LoadPackage("gbnp");
SetInfoLevel(InfoGBNP, 1);
SetInfoLevel(InfoGBNPTime,1);
SetRecursionTrapInterval(50000);

# coefficient ring (edit pStr; p is derived from it so the two stay in sync)
pStr := "2^61-1";
p := EvalString(pStr);
R := GF(p);
q := 3*One(R);
t := 5*One(R);

# strands
n := 4;

# logfile name encodes (n, p, q, t)
LogTo(Concatenation("../logs_and_traces/logfile_bmw","-", String(n), "-(", pStr, ")-",
                    String(Int(q)), "-", String(Int(t)), ".txt"));


# define free algebra
# xs are generators, ys their inverses
generators := Concatenation(
    List([1..n-1], i -> Concatenation("x", String(i))),
    List([1..n-1], i -> Concatenation("y", String(i)))
);
F := FreeAssociativeAlgebraWithOne(R, generators);
generators := GeneratorsOfAlgebra(F);
one := generators[1];
xs := generators{[2..n]};;
ys := generators{[n+1..2*n-1]};;


# define relations
relations := [];


# add invertibility relation for generators
for i in [1..n-1] do
  Add(relations, xs[i]*ys[i] - one);
  Add(relations, ys[i]*xs[i] - one);
od;


# add far commutativity and braid relations
# include the y-side and mixed versions explicitly: all derivable from the
# x-side relations + invertibility, but giving them upfront saves SGrobner
# from rediscovering them via S-polynomial reductions
for i in [1..n-2] do
  for j in [i+1..n-1] do
    if j - i >= 2 then
      Add(relations, xs[i]*xs[j] - xs[j]*xs[i]);
      Add(relations, ys[i]*ys[j] - ys[j]*ys[i]);
      Add(relations, ys[i]*xs[j] - xs[j]*ys[i]);
      Add(relations, xs[i]*ys[j] - ys[j]*xs[i]);
    else  # j = i+1
      Add(relations, xs[i]*xs[j]*xs[i] - xs[j]*xs[i]*xs[j]);
      Add(relations, ys[i]*ys[j]*ys[i] - ys[j]*ys[i]*ys[j]);
    fi;
  od;
od;


# define sliders S[i][j] = i-strand slider at position j
#   S[2][j] = q*y_j + (1-q) - x_j
#   S[i][j] = (q^(i-1) * y_j*y_{j+1}*...*y_{j+i-2}
#                       - x_j*x_{j+1}*...*x_{j+i-2}) * S[i-1][j]
# valid range: i in [2..n], j in [1..n-i+1]
S := List([1..n], i -> []);
for j in [1..n-1] do
  S[2][j] := q*ys[j] + (1-q)*one - xs[j];
od;
for i in [3..n] do
  for j in [1..n-i+1] do
    yProd := ys[j];
    for k in [j+1..j+i-2] do yProd := yProd * ys[k]; od;
    xProd := xs[j];
    for k in [j+1..j+i-2] do xProd := xProd * xs[k]; od;
    S[i][j] := (q^(i-1)*yProd - xProd) * S[i-1][j];
  od;
od;


# zipper relations for every number of strands and position
# 2-strand at position j (j in [1..n-2]):
#   (S[2][j+1] - q*y_j*y_{j+1} + x_j*x_{j+1}) * S[2][j] = 0
for j in [1..n-2] do
  Add(relations,
      (S[2][j+1] - q*ys[j]*ys[j+1] + xs[j]*xs[j+1]) * S[2][j]);
od;

# level i >= 3 at position j (j in [1..n-i]):
#   ((q^(i-1)*y_{j+1}*...*y_{j+i-1} - x_{j+1}*...*x_{j+i-1})
#  - (q^(i-1)*y_j  *...*y_{j+i-1} - x_j  *...*x_{j+i-1})) * S[i][j] = 0
for i in [3..n-1] do
  for j in [1..n-i] do
    yProd_short := ys[j+1];
    for k in [j+2..j+i-1] do yProd_short := yProd_short * ys[k]; od;
    yProd_long  := ys[j] * yProd_short;
    xProd_short := xs[j+1];
    for k in [j+2..j+i-1] do xProd_short := xProd_short * xs[k]; od;
    xProd_long  := xs[j] * xProd_short;
    Add(relations, (q^(i-1)*yProd_short - xProd_short
                  - q^(i-1)*yProd_long  + xProd_long) * S[i][j]);
  od;
od;


# BMW quotient part I: S[3][i] = 0.
for i in [1..n-2] do
  Add(relations, S[3][i]);
od;


# BMW quotient part II: untwisting at every j in [1..n-1]: (x_j - t) * S[2][j] = 0
for j in [1..n-1] do
  Add(relations, (xs[j] - t*one) * S[2][j]);
od;


# compute and display from here
Print("Relations (GAP):\n");
for r in relations do Print(r, "\n"); od;
I := GP2NPList(relations);
Print("Beginning SGrobner calculation.\n");
B := SGrobner(I);
Print("Groebner basis size: ", Length(B), "\n");

# Only leading monomials are required for determining dimension
L := LMonsNP(B);   # leading monomials
nGen := 2*(n-1);   # number of generators of the free algebra (xs and ys)
growth := DetermineGrowthQA(L, nGen, true);
if growth=0 then
  Print("The quotient algebra is finite-dimensional.\n",
  "The Gel'fand-Kirillov dimension is: ", growth, "\n");
elif not IsString(var) then
  Print("The quotient algebra is infinite-dimensional of polynomial growth.\n",
  "The Gel'fand-Kirillov dimension is: ", growth, "\n");
else 
  Print("The quotient algebra is infinite-dimensional of exponential growth.\n",
  "The Gel'fand-Kirillov dimension is infinite.\n");
fi;

# HilbertSeriesQA(Lm, t, d): values of the Hilbert series up to degree d
dMax := n*(n-1);
hilb := HilbertSeriesQA(L, nGen, dMax);
hilb_deg := Length(hilb);
dims := List([1..hilb_deg], i -> Sum(hilb{[1..i]}));
Print("Hilbert series (degree 0,...,", hilb_deg-1, "): ", hilb, "\n");
Print("Cumulative dims: ", dims, "\n");
Print("Quotient algebra dimension DimQA(B, ", nGen, ") = ", DimQA(B, nGen), "\n");
Print("Expected: dim BMW_", n, " = (2n-1)!! = ",
      Product([1, 3..2*n-1]), "\n");