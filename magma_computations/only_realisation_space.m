//parallel --shuf --timeout 259200 --eta -j17 magma -b  k:=4 n:=9 seq:={}  realizationspacerank_kon_n.m  ::: {1..128675} >> rk4on9_sep11.out
// inputfile for the nonbases of the matroids needs to be saved in the run directory by name "nonbases48" for rank 4 matroids on 8 elements


n := StringToInteger(n);
filename:="rank" cat k cat "/nonbases" cat k cat IntegerToString(n);
k := StringToInteger(k);

//bases of uniform matroid of rank k on n elements
U :=[Sort(SetToSequence(b)) : b in Subsets({1..n},k)];

function constructMinors(M, indices, R, b)
	//we need to let the indices in b be the first indices, and then it doesn't matter
	bcomp := {1..n} diff Set(b);
	bcomp := SetToSequence(bcomp);
	reorder := pmap<[i : i in {1..n}]->[i : i in {1..n}] | [ <b[i],i> : i in {1..k} ] cat [<bcomp[i-k],i> : i in {(k+1)..n}]>;
    return [ R!Determinant(Transpose(Matrix([ColumnSubmatrixRange(M, reorder(i), reorder(i)): i in ind]))) : ind in indices]; 
end function;

//if the matroid is not simple (see rank 2) then we cannot always normalize columns because some might just be all zero. but then the output is just empty and it does not influence the remaining code
function normalizeCols(M, minors, R)
	xs := Matrix(k, n-k, [R.i : i in [1..k*(n-k)]]);
    firstnotzer := [];
    for i in [1 .. n-k] do
        for j in [1 .. k] do
                if xs[j][i] notin minors and -xs[j][i] notin minors then
                    Append(~firstnotzer, xs[j][i] - R!1);
                break;
            end if;
        end for;
    end for;
    return firstnotzer;
end function;

function normalizeRows(M, minors, R)
	xs := Matrix(k, n-k, [R.i : i in [1..k*(n-k)]]);
    firstnotzer := [];
    for i in [1 .. k] do
        for j in [1 .. n-k] do
                if xs[i][j] notin minors and -xs[i][j] notin minors then
                    Append(~firstnotzer, xs[i][j] - R!1);
                break;
            end if;
        end for;
    end for;
    return firstnotzer;
end function;


function saturateIdeal(I, basisminors)
    for f in basisminors do
        I := Saturation(I, f);
    end for;
    return I;
end function;


function strip(s) return Join(Split(Join(Split(s," "),""),"\n"),""); end function;

function doline(nonbases)
	R<[x]> := PolynomialRing(Rationals(), k*(n-k));
	xs := Matrix(k, n-k, [R.i : i in [1..k*(n-k)]]);
	Id := ScalarMatrix(k,R!1);
	M := HorizontalJoin(Id, xs);
    bases :=  SetToSequence(Set(U) diff Set(nonbases)); 
    b := bases[1]; //pick a basis to relabel by so that we can create the left identity matrix
	nonbasisminors :=constructMinors(M, nonbases, R, b);
	//force the first nonzero entry of each column to be one
	nonzer := normalizeCols(M, nonbasisminors, R);
	//add in all the equations for each non-basis
	nonzercol := normalizeRows(M, nonbasisminors, R);
	//also add in xs = 1 for each first element in the row that is nonzero 
	eqns := nonbasisminors cat nonzer cat nonzercol;
	//now saturate for each basis element
	basisminors := constructMinors(M, bases, R, b);
	I := ideal<R| eqns >;
	Isat := saturateIdeal(I, basisminors);
	gb := GroebnerBasis(Isat);
	d := Dimension(Isat);
	//d := d- n ; //check this!
	Q := quo<R | Isat>;
	Mspec := ChangeRing(M, Q); 
	output := [* bases, gb, d,"Nothing", "Nothing", "Nothing", [Eltseq(r) : r in Rows(Mspec)] *];
	return output;
end function;

if assigned seq then
	SetColumns(0);
	SetAutoColumns(false);
	seq := eval seq;
	inputs := Split(Read(filename), "\n");
	input := eval inputs[seq];
	output := doline(input);
	output := [* seq *] cat output;
	print strip(Join([Sprint(elt) : elt in output], ":"));
	exit;
end if;






