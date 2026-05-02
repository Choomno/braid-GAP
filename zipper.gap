LoadPackage("gbnp");
SetInfoLevel(InfoGBNP, 2);
SetInfoLevel(InfoGBNPTime, 2);
SetRecursionTrapInterval(50000);


###############################################################################
# USER PARAMETERS
###############################################################################
#
# Edit the values in this block, then run
#   gap -o <workspace> -K <workspace> zipper.gap
# from the braid-GAP/ directory.
#
# Number of strands.
n := 4;

# The "true" coefficient ring is the function field Q(q,t), but rational
# arithmetic is too expensive; specializing to GF(p) at chosen integer values is
# the computational substitute.
#
# The coefficient ring is GF(p) for the prime p below; q and t are the residue
# classes of q_int and t_int. Run at multiple primes/parameters to validate, or
# for lifting to Q(q,t) via Chinese remainder theorem, rational reconstruction,
# and and Pade interpolation.
pStr := "2^31-1";
q_int := 5;
t_int := 7;

# Below is a parameter that determines whether to compute the full trace
# (for instance, for the purpose of expressing each basis element as a
# combination of the input relations) or just a bare Grobner basis.
# Tracing is dramatically heavier in time, RAM, and disk. Set either
#   traced := true
#   traced := false
traced := false;

###############################################################################
# END USER PARAMETERS
###############################################################################

# Field parameters
p := EvalString(pStr);
R := GF(p);
q := q_int * One(R);
t := t_int * One(R);
if traced then
  mode_str := "traced";
  out_str := "trace";
else
  mode_str := "untraced";
  out_str := "untraced";
fi;

# logfile name encodes (mode, n, p, q, t)
LogTo(Concatenation("logs_and_traces/logfile_zipper-", mode_str, "-",
                    String(n), "-(", pStr, ")-",
                    String(Int(q)), "-", String(Int(t)), ".txt"));


# Define free associative algebra on 2*(n-1) variables
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
# We include the y-braid and mixed versions explicitly: all derivable from the
# x-braid relations + invertibility, but giving them upfront saves SGrobner from
# rediscovering them via S-polynomial reductions.
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


# Additional length-3 braid identities for adjacent strands.
# These are derivable from the x-braid + invertibility relations above, but
# without including them they show up as Grobner basis elements via long
# S-polynomial chains.
for i in [1..n-2] do
  Add(basic_relations, xs[i]*xs[i+1]*ys[i]   - ys[i+1]*xs[i]*xs[i+1]);
  Add(basic_relations, ys[i]*ys[i+1]*xs[i]   - xs[i+1]*ys[i]*ys[i+1]);
  Add(basic_relations, xs[i]*ys[i+1]*ys[i]   - ys[i+1]*ys[i]*xs[i+1]);
  Add(basic_relations, ys[i]*xs[i+1]*xs[i]   - xs[i+1]*xs[i]*ys[i+1]);
od;


# Define sliders S[number of strands][anchor]
# The i-strand sliders have anchor index j ranging over [1..n-i+1].
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


# Add zipper relations
# Zipper relations for 2-strand sliders
for j in [1..n-2] do
  Add(complex_relations,
      (q*ys[j+1] + (1-q)*one - xs[j+1]
       - q*ys[j]*ys[j+1] + xs[j]*xs[j+1]) * S[2][j]);
od;

# Zipper relations for 3 or more strand sliders
# Since the zipper relation only applies if there is free strand to the right of
# a slider, j ranges in [1..n-i]
for i in [3..n-1] do
  for j in [1..n-i] do
    yProd_after := ys[j+1];
    for k in [j+2..j+i-1] do yProd_after := yProd_after * ys[k]; od;
    yProd_full := ys[j] * yProd_after;
    xProd_after := xs[j+1];
    for k in [j+2..j+i-1] do xProd_after := xProd_after * xs[k]; od;
    xProd_full := xs[j] * xProd_after;
    Add(complex_relations,
        (q^(i-1)*yProd_after - xProd_after
         - q^(i-1)*yProd_full + xProd_full) * S[i][j]);
  od;
od;


# Add untwisting relations
# Unzipping relations for 2-strand sliders
for j in [1..n-1] do
  Add(complex_relations, (xs[j] - t*one) * S[2][j]);
od;

# Unzipping relations for 3 or more strand sliders
# An i-strand slider anchored at strand index j requires strands
# j, j+1, ..., j+i-2, so j ranges [1..n-i+1].
for i in [3..n] do
  for j in [1..n-i+1] do
    xProd_reverse := xs[j+i-2];
    yProd_reverse := ys[j+i-2];
    for k in [2..i-1] do
      xProd_reverse := xProd_reverse * xs[j+i-1-k];
      yProd_reverse := yProd_reverse * ys[j+i-1-k];
    od;
    # Bigelow's conjectured untwisting relations
    Add(complex_relations,
        (xProd_reverse - q^(i-1)*yProd_reverse) * S[i][j]);

    # indeterminate untwisting
#   Add(complex_relations, (xProd_reverse - s*yProd_reverse) * S[i][j]);
  od;
od;


# Pre-reduce complex relations modulo invertibility.
# The four invertibility relations already form a Grobner basis on their own
# (their leading monomials don't overlap; all S-polys reduce to zero), so we can
# use them directly in StrongNormalFormNP without an SGrobner call. Reducing
# kills x_i*y_i and y_i*x_i instances.
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

# Run SGrobnerTrace or SGrobner depending on the user parameter `traced`.
if traced then
  Print("Traced option selected.\n",
        "Beginning SGrobnerTrace calculation.\n");
  GBT := SGrobnerTrace(I);
  B := List(GBT, r -> r.pol);   # plain basis for downstream calls
else
  Print("Untraced option selected.\n",
        "Beginning SGrobner calculation (no trace).\n");
  B := SGrobner(I);
fi;
Print("Groebner basis size: ", Length(B), "\n");

# Save the result to a parameter-tagged file.
outFile := Concatenation("logs_and_traces/grobner_", out_str,
                          "_zipper-", String(n), "-(", pStr, ")-",
                          String(Int(q)), "-", String(Int(t)), ".gap");
if traced then
  PrintTo(outFile,
    "# Saved traced Grobner basis and parameters from zipper.gap.\n",
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
else
  PrintTo(outFile,
    "# Saved (untraced) Grobner basis and parameters from zipper.gap.\n",
    "# B is the basis as a list of NP polynomials.\n",
    "n := ", n, ";\n",
    "pStr := \"", pStr, "\";\n",
    "p := EvalString(pStr);\n",
    "R := GF(p);\n",
    "q := ", Int(q), "*One(R);\n",
    "t := ", Int(t), "*One(R);\n",
    "I := ", I, ";\n",
    "B := ", B, ";\n");
fi;

# Determination of dimension of quotient algebra
# Only leading monomials are required for determining dimension.
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
# This is a sanity check for comparison to BMW, and is also just kind of neat.
dMax := n*(n-1);
hilb := HilbertSeriesQA(L, nGen, dMax);
hilb_deg := Length(hilb);
dims := List([1..hilb_deg], i -> Sum(hilb{[1..i]}));
Print("Hilbert series (degree 0,...,", hilb_deg-1, "): ", hilb, "\n");
Print("Cumulative dims: ", dims, "\n");
Print("Quotient algebra dimension DimQA(B, ",nGen,") = ", DimQA(B, nGen), "\n");
Print("Compare: dim BMW_", n, " = (2n-1)!! = ",
      Product([1, 3..2*n-1]), "\n");