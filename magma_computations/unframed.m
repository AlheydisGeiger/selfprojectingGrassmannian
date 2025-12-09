


//SPECIAL CASE: no possible choice of frame (c, and basis element) exists. true for two of rank 4 on 9


filename:="rank" cat k cat "/unframed_nonbases" cat k cat n;
n := StringToInteger(n);
k := StringToInteger(k);
U := [Sort(SetToSequence(b)) : b in Subsets({1..n},k)];

function constructMinorsUnframed(M, indices, R, b)
	//this function works whether or not the matroid is framed
	bcomp := {1..n} diff Set(b);
	bcomp := SetToSequence(bcomp);
	reorder := pmap<[i : i in {1..n}]->[i : i in {1..n}] | [ <b[i],i> : i in {1..k} ] cat [<bcomp[i-k],i> : i in {(k+1)..n}]>;
    return [ R!Determinant(Transpose(Matrix([ColumnSubmatrixRange(M, reorder(i), reorder(i)): i in ind]))) : ind in indices]; 
end function;

function normalizeCols(M, minors, R)
    xs := Matrix(k, n-k, [R.i : i in [1..(k*(n-k))]]);
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
    xs := Matrix(k, n-k, [R.i : i in [1..(k*(n-k))]]);
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

function saturateIdeal(eqns, basisminors, R)
    Isat := ideal<R| eqns >;
    for f in basisminors do
        Isat := Saturation(Isat, f);
    end for;
    return Isat;
end function;

function constructLambdaEqns(M, R)
    l := [R.i : i in [(k*(n-k)+1) .. (k*(n-k)+n)]];
    prod := M* DiagonalMatrix(l) * Transpose(M);
    leqns := [Vector(prod)[i] : i in [1 .. (k*k)]];
    return leqns;
end function;

function strip(s) return Join(Split(Join(Split(s," "),""),"\n"),""); end function;


function doline(nonbases)
    R<[x]> := PolynomialRing(Rationals(), (k*(n-k)+n));
    xs := Matrix(k, n-k, [R.i : i in [1..(k*(n-k))]]);
    Id := ScalarMatrix(k,R!1);
    M := HorizontalJoin(Id, xs);
    bases :=  SetToSequence(Set(U) diff Set(nonbases)); 
    b := bases[1]; // pick a random basis;
    nonbasisminors :=constructMinorsUnframed(M, nonbases, R, b);
    //force the first nonzero entry of each column to be one
    nonzer := normalizeCols(M, nonbasisminors, R);
    //add in all the equations for each non-basis
    nonzercol := normalizeRows(M, nonbasisminors, R);

    eqns := nonbasisminors cat nonzer cat nonzercol;
    basisminors := constructMinorsUnframed(M, bases, R, b);

    I := Ideal(eqns);
    Isat := saturateIdeal(eqns, basisminors, R);
    l := [R.i : i in [(k*(n-k)+1) .. (k*(n-k)+n)]];
    prod := M* DiagonalMatrix(l) * Transpose(M); 

    gb := GroebnerBasis(Isat);
    d := Dimension(Isat);
    d := d - n;
    leqns := constructLambdaEqns(M,R);
    selfdualeqns := gb cat leqns;
    selfdualI := ideal<R|selfdualeqns>;
    //sdIsat := Saturation(selfdualI, ideal<R| [x[i]: i in [26 .. 35]]>);

    sdIsat := Saturation(selfdualI, &*[x[i]: i in [(k*(n-k)+1) .. (k*(n-k)+n)]]);
    sdIsatelim := EliminationIdeal(sdIsat, {x[i] : i in [1 .. (k*(n-k))]});
    sdequalsreal := sdIsatelim eq Isat;
    if sdequalsreal then
        selfdualdim := Dimension(sdIsatelim) - n;
        Q := quo<R | sdIsatelim>;
        Mspec := ChangeRing(M, Q);
    else
        Isdsat := sdIsatelim;
        for f in basisminors do
            Isdsat := Saturation(Isdsat, f);
        end for;
        sdIsatelim := Isdsat;
        selfdualdim := Dimension(sdIsatelim) - n;
        Q := quo<R | sdIsatelim>;
        Mspec := ChangeRing(M, Q);
        sdequalsreal := sdIsatelim eq Isat;
    end if;

    output := [* bases, gb, d, Basis(sdIsatelim), selfdualdim, sdequalsreal, [Eltseq(r) : r in Rows(Mspec)] *];
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
