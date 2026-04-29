LoadPackage("gbnp");
SetInfoLevel(InfoGBNP, 2);
SetInfoLevel(InfoGBNPTime,2);
SetRecursionTrapInterval(50000);

# In principle we want the coefficient ring to be
# R = Q(q,t)
# R := FunctionField(Rationals, ["q","t"]);
# indeterminates := IndeterminatesOfFunctionField(R);
# q := indeterminates[1];
# t := indeterminates[2];

# However, rational field coefficients are too expensive.
# Our computational coefficient ring is 
# (edit pStr; p is derived from it so the two stay in sync)
pStr := "2^31-1";
p := EvalString(pStr);
R := GF(p);
q := 5*One(R);
t := 7*One(R);

# Number of strands
n := 3;

# logfile name encodes (n, p, q, t)
LogTo(Concatenation("../logs_and_traces/logfile_zipper","-", String(n), "-(", pStr, ")-",
                    String(Int(q)), "-", String(Int(t)), ".txt"));


# Define free associative algebra
# xs are generators, ys their inverses
# Generator order: x1, x2, ..., x_{n-1}, y1, y2, ..., y_{n-1}.
generators := Concatenation(
    List([1..n-1], i -> Concatenation("x", String(i))),
    List([1..n-1], i -> Concatenation("y", String(i)))
);
F := FreeAssociativeAlgebraWithOne(R, generators);
generators := GeneratorsOfAlgebra(F);
one := generators[1];
xs := generators{[2..n]};;
ys := generators{[n+1..2*n-1]};;


# Define relations
# Three groups, kept separate so that we can reduce the high-degree
# zipper/untwist relations modulo the cheap invertibility ones before
# handing them to SGrobnerTrace.
inv_relations := [];          # x_i*y_i = 1, y_i*x_i = 1
basic_relations := [];        # braid + far-commutativity (no x*y pairs)
complex_relations := [];      # zipper + untwisting (contain x*y pairs)


# Add invertibility relations
for i in [1..n-1] do
  Add(inv_relations, xs[i]*ys[i] - one);
  Add(inv_relations, ys[i]*xs[i] - one);
od;


# Add far commutativity and braid relations
# Include the y-braid and mixed versions explicitly: all derivable from the
# x-braid relations + invertibility, but giving them upfront saves SGrobner
# from rediscovering them via S-polynomial reductions.
for i in [1..n-2] do
  for j in [i+1..n-1] do
    if j - i >= 2 then
      Add(basic_relations, xs[i]*xs[j] - xs[j]*xs[i]);
      Add(basic_relations, ys[i]*ys[j] - ys[j]*ys[i]);
      Add(basic_relations, ys[i]*xs[j] - xs[j]*ys[i]);
      Add(basic_relations, xs[i]*ys[j] - ys[j]*xs[i]);
    else  # j = i+1
      Add(basic_relations, xs[i]*xs[j]*xs[i] - xs[j]*xs[i]*xs[j]);
      Add(basic_relations, ys[i]*ys[j]*ys[i] - ys[j]*ys[i]*ys[j]);
    fi;
  od;
od;


# Mixed-sign length-3 braid consequences for adjacent strands.
# These are derivable from the x-braid + y-braid + invertibility relations
# above, but without including them they show up as Grobner basis elements
# via long S-polynomial chains.
for i in [1..n-2] do
  Add(basic_relations, xs[i]*xs[i+1]*ys[i]   - ys[i+1]*xs[i]*xs[i+1]);
  Add(basic_relations, ys[i]*ys[i+1]*xs[i]   - xs[i+1]*ys[i]*ys[i+1]);
  Add(basic_relations, xs[i]*ys[i+1]*ys[i]   - ys[i+1]*ys[i]*xs[i+1]);
  Add(basic_relations, ys[i]*xs[i+1]*xs[i]   - xs[i+1]*xs[i]*ys[i+1]);
od;


# Define sliders
S := EmptyPlist(n);
S[2] := q*ys[1] + (1-q)*one - xs[1];

for i in [3..n] do
  yProd := ys[1];
  for k in [2..i-1] do
    yProd := yProd * ys[k];
  od;
  xProd := xs[1];
  for k in [2..i-1] do
    xProd := xProd * xs[k];
  od;
  S[i] := (q^(i-1)*yProd - xProd)*S[i-1];
od;


# Add zipper relations
Add(complex_relations, (q*ys[2] + (1-q)*one - xs[2]
             - q*ys[1]*ys[2] + xs[1]*xs[2])*S[2]);

for i in [3..n-1] do
  yProd_from2 := ys[2];
  for k in [3..i] do
    yProd_from2 := yProd_from2 * ys[k];
  od;
  yProd_from1 := ys[1] * yProd_from2;
  xProd_from2 := xs[2];
  for k in [3..i] do
    xProd_from2 := xProd_from2 * xs[k];
  od;
  xProd_from1 := xs[1] * xProd_from2;
  Add(complex_relations, (q^(i-1)*yProd_from2 - xProd_from2
               - q^(i-1)*yProd_from1 + xProd_from1)*S[i]);
od;


# Add untwisting relations
Add(complex_relations, (xs[1] - t*one)*S[2]);

for i in [3..n] do
  xProd_reverse := xs[i-1];
  for k in [2..i-1] do
     xProd_reverse := xProd_reverse * xs[i-k];
  od;
  yProd_reverse := ys[i-1];
  for k in [2..i-1] do
    yProd_reverse := yProd_reverse * ys[i-k];
  od;
  # Bigelow's conjectured untwisting relations
  Add(complex_relations, (xProd_reverse - q^(i-1)*yProd_reverse)*S[i]);

  # indeterminate untwisting
#  Add(complex_relations, (xProd_reverse - s*yProd_reverse)*S[i]);
od;


# Pre-reduce complex relations modulo invertibility.
# The four invertibility relations already form a Grobner basis on their own
# (their leading monomials don't overlap; all S-polys reduce to zero), so we can
# use them directly in StrongNormalFormNP without an SGrobner call. Reducing
# kills internal x_i*y_i and y_i*x_i adjacencies. The ideal is unchanged: each
# simplified poly equals the original plus a multiple of an invertibility
# relation.
inv_GB := GP2NPList(inv_relations);
complex_np := GP2NPList(complex_relations);
complex_simplified := List(complex_np, p -> StrongNormalFormNP(p, inv_GB));
# Drop any that reduced to zero (would mean the relation was already implied
# by invertibility alone — shouldn't happen here, but we do it conservatively).
complex_simplified := Filtered(complex_simplified, p -> p <> []);

# Display the input we're about to feed SGrobner.
relations := Concatenation(inv_relations, basic_relations, complex_relations);
Print("Original relations (GAP):\n");
for r in relations do Print(r, "\n"); od;
Print("Simplified complex relations (post-reduction mod invertibility):\n");
for p in complex_simplified do Print(NP2GP(p, F), "\n"); od;

I := Concatenation(inv_GB,
                   GP2NPList(basic_relations),
                   complex_simplified);
Print("Total input relations: ", Length(I), "\n");
Print("Beginning SGrobnerTrace calculation.\n");
GBT := SGrobnerTrace(I);
B := List(GBT, r -> r.pol);   # plain Grobner basis for downstream calls
Print("Groebner basis size: ", Length(B), "\n");
outFile := Concatenation("../logs_and_traces/grobner_basis_zipper","-", String(n), "-(", pStr, ")-",
                    String(Int(q)), "-", String(Int(t)), ".gap");
PrintTo(outFile,
  "# Saved traced Grobner basis and parameters from zipper.gap\n",
  "# GBT is the traced basis (list of rec(pol, trace)); trace tuples\n",
  "# [left, inputIdx, right, coeff] reference positions in I.\n",
  "n := ", n, ";\n",
  "pStr := \"", pStr, "\";\n",
  "p := EvalString(pStr);\n",
  "R := GF(p);\n",
  "q := ", Int(q), "*One(R);\n",
  "t := ", Int(t), "*One(R);\n",
  "I := ", I, ";\n",
  "GBT := ", GBT, ";\n");

# Only leading monomials are required for determining dimension
L := LMonsNP(B);   # leading monomials
nGen := 2*(n-1);   # number of generators of the free algebra (xs and ys)
growth := DetermineGrowthQA(L, nGen, true);
if growth=0 then
  Print("The quotient algebra is finite-dimensional.\n",
  "The Gel'fand-Kirillov dimension is: ", growth, "\n");
elif not IsString(growth) then
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
Print("Compare: dim BMW_", n, " = (2n-1)!! = ",
      Product([1, 3..2*n-1]), "\n");