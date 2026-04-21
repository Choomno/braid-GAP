LogTo("logfile.txt");
LoadPackage("gbnp");
SetInfoLevel(InfoGBNP, 2);
SetInfoLevel(InfoGBNPTime,2);
SetRecursionTrapInterval(50000);

# coefficient ring
R := FunctionField(Rationals, ["q"]);
indeterminates := IndeterminatesOfFunctionField(R);
q := indeterminates[1];


# strands
n := 6;


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
for i in [1..n-2] do
  for j in [i+1..n-1] do
    if j - i >= 2 then
      Add(relations, xs[i]*xs[j] - xs[j]*xs[i]);
    else  # j = i+1
      Add(relations, xs[i]*xs[j]*xs[i] - xs[j]*xs[i]*xs[j]);
    fi;
  od;
od;


# define slider
S := q*ys[1] + (1-q)*one - xs[1];

# to get Hecke, S = 0
Add(relations,S);

# compute
Print("Relations (GAP):\n");
for r in relations do Print(r, "\n"); od;
I := GP2NPList(relations);
Print("NP relations count: ", Length(I), "\n");
Print("NP relations:\n");
PrintNPList(I);
B := SGrobner(I);
Print("Groebner basis size: ", Length(B), "\n");

L := LMonsNP(B);
Display(DetermineGrowthQA(L,2*(n-1),true));
Display(DimQA(B,2*(n-1)));