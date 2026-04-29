LoadPackage("gbnp");
SetInfoLevel(InfoGBNP, 2);
SetInfoLevel(InfoGBNPTime,2);
SetRecursionTrapInterval(50000);

# Homogenized version of bmw_example.txt for use with SGrobnerTrunc.
# We introduce a central degree-1 generator h and replace each constant c
# in the relations by c*h^k where k is chosen so that every monomial in
# every relation has the same total degree (with each x_i, y_i, h of weight 1).
# Then the homogenized algebra A^h satisfies dim (A^h)_d = dim A_{<=d},
# i.e., HilbertSeriesQA on A^h gives the cumulative Hilbert function of A.

# coefficient ring (edit pStr; p is derived from it so the two stay in sync)
pStr := "2^61-1";
p := EvalString(pStr);
R := GF(p);
q := 3*One(R);
t := 5*One(R);

# strands
n := 4;

# logfile name encodes (n, p, q, t)
LogTo(Concatenation("../logs_and_traces/logfile_bmw_trunc","-", String(n), "-(", pStr, ")-",
                    String(Int(q)), "-", String(Int(t)), ".txt"));


# define free algebra: x1..x_{n-1}, y1..y_{n-1}, h
generators := Concatenation(
    List([1..n-1], i -> Concatenation("x", String(i))),
    List([1..n-1], i -> Concatenation("y", String(i))),
    ["h"]
);
F := FreeAssociativeAlgebraWithOne(R, generators);
gen_list := GeneratorsOfAlgebra(F);
one := gen_list[1];
xs := gen_list{[2..n]};;
ys := gen_list{[n+1..2*n-1]};;
h  := gen_list[2*n];


# define relations
relations := [];


# h is central
for i in [1..n-1] do
  Add(relations, xs[i]*h - h*xs[i]);
  Add(relations, ys[i]*h - h*ys[i]);
od;


# invertibility (homogeneous of degree 2 in x,y,h)
for i in [1..n-1] do
  Add(relations, xs[i]*ys[i] - h^2);
  Add(relations, ys[i]*xs[i] - h^2);
od;


# braid + far-commutativity primers (already homogeneous)
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


# sliders (homogenized).
#   S[2][j] = q*y_j + (1-q)*h - x_j           (degree 1)
#   S[i][j] = (q^(i-1)*y_j*...*y_{j+i-2}
#             - x_j*...*x_{j+i-2}) * S[i-1][j]
# The leading factor at level i has i-1 letters; recursively the slider has
# degree 1 + 2 + ... + (i-1) = i(i-1)/2. The leading factor is already
# homogeneous in x,y so no h-padding is needed inside it.
S := List([1..n], i -> []);
for j in [1..n-1] do
  S[2][j] := q*ys[j] + (1-q)*h - xs[j];
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


# zipper relations (homogenized).
# Level 2 at anchor j: original coefficient mixes the deg-1 slider S[2][j+1]
# with deg-2 strip terms. Pad S[2][j+1] by h to lift to deg 2:
#   (h*S[2][j+1] - q*y_j*y_{j+1} + x_j*x_{j+1}) * S[2][j]    (deg 3)
for j in [1..n-2] do
  Add(relations,
      (h*S[2][j+1] - q*ys[j]*ys[j+1] + xs[j]*xs[j+1]) * S[2][j]);
od;

# Level i >= 3 at anchor j: short term has i-1 letters, long term has i.
# Pad short term by h to lift to deg i:
#   (h*(q^(i-1)*y_{j+1}*...*y_{j+i-1} - x_{j+1}*...*x_{j+i-1})
#  -    q^(i-1)*y_j  *...*y_{j+i-1} + x_j  *...*x_{j+i-1}) * S[i][j]
for i in [3..n-1] do
  for j in [1..n-i] do
    yProd_short := ys[j+1];
    for k in [j+2..j+i-1] do yProd_short := yProd_short * ys[k]; od;
    yProd_long  := ys[j] * yProd_short;
    xProd_short := xs[j+1];
    for k in [j+2..j+i-1] do xProd_short := xProd_short * xs[k]; od;
    xProd_long  := xs[j] * xProd_short;
    Add(relations, (h*(q^(i-1)*yProd_short - xProd_short)
                  -    q^(i-1)*yProd_long  + xProd_long) * S[i][j]);
  od;
od;


# BMW quotient: S[n][1] = 0 (already homogeneous of degree n(n-1)/2)
Add(relations, S[n][1]);


# untwisting (homogenized): (x_j - t*h) * S[2][j]   (deg 2)
for j in [1..n-1] do
  Add(relations, (xs[j] - t*h) * S[2][j]);
od;


# compute
Print("Relations (GAP):\n");
for r in relations do Print(r, "\n"); od;
I := GP2NPList(relations);
Print("NP relations count: ", Length(I), "\n");

# weight vector: every generator has weight 1
nGen := 2*n - 1;             # x1..x_{n-1}, y1..y_{n-1}, h
wtv  := List([1..nGen], i -> 1);

# truncation degree: any word in the original (non-homogenized) algebra of
# length <= dMax corresponds to a homogeneous word of degree dMax in A^h.
dMax := n*(n-1);

# sanity check: confirm input is homogeneous wrt wtv
Print("CheckHomogeneousNPs: ", CheckHomogeneousNPs(I, wtv), "\n");

B := SGrobnerTrunc(I, dMax, wtv);
if B = false then
  Print("Relations are NOT homogeneous wrt the chosen weight vector.\n");
else
  Print("Truncated Groebner basis size: ", Length(B), "\n");
  dims := DimsQATrunc(B, dMax, wtv);
  Print("Graded dims of A^h, degree 0..", dMax, ": ", dims, "\n");
  Print("(These equal the cumulative dim of the original algebra A.)\n");
  Print("Final cumulative dim A_{<=", dMax, "} = ", dims[Length(dims)], "\n");
  Print("Expected dim BMW_", n, " = (2n-1)!! = ",
        Product([1, 3..2*n-1]), "\n");
fi;
