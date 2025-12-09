//parallel --shuf --timeout 36000 --eta -j40 magma -b k:=5 n:=9  seq:={} rk5optimize.m ::: {1..100} >> combosep22try2.out

// the only two self-projecting matroids of rank 4 on 9 elements have labels [6778, 184598] in the full database of all (4,9) matroids. I need to find out which are the numbers in our nonbases49 set. see comment at the end of file



filename:="rank" cat k cat "/nonbases" cat k cat n;
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

//difference to normalizeCols: We collect the all(!) nonzero entries, we do not yet add the x-1 polynomial
function nonzeroEntries(M, minors, R)
    xs := Matrix(k, n-k, [R.i : i in [1..k*(n-k)]]);
    nonzeroentries := [];
    for i in [1 .. n-k] do
        for j in [1 .. k] do
                if xs[j][i] notin minors and -xs[j][i] notin minors then
                    Append(~nonzeroentries, <j,i>);
            end if;
        end for;
    end for;
    return nonzeroentries;
end function;

function saturateIdeal(eqns, basisminors, R)
    Isat := ideal<R| eqns >;
    for f in basisminors do
        Isat := Saturation(Isat, f);
    end for;
    return Isat;
end function;

function constructLambdaEqns(M, R)
    h:=k*(n-k)+1;
    l := [R.i : i in [h..h+n-1]];
    prod := M* DiagonalMatrix(l) * Transpose(M);
    leqns := [Vector(prod)[i] : i in [1..(k*k)]];
    return leqns;
end function;

function strip(s) return Join(Split(Join(Split(s," "),""),"\n"),""); end function;

//this should find all possible columns that can complement to a frame of the matroid, i.e. a column where all entries are nonzero.
function findpossiblecols(nonzer)
    goodcols := [];
    for i in [1 .. n-k] do
        fullcol := true;
        for j in [ 1..k] do
            if <j, i> notin nonzer then
                fullcol := false;
                break;
            end if;
        end for;
        if fullcol then
            Append(~goodcols, i);
        end if;
    end for;
    return goodcols;
end function;

//below funciton does not work as intended
//k ist die Tiefe, idx gibt die aktuelle Tiefe an (du startest mit 1)
//args ist eine Liste, die die aktuell gewählten Werte auf jeder Schleifenebene enthält
//function NestedLoop(firstindex, k, idx, args,c)
//    res :=[];
//    if idx gt k then
//        row := [elt : i->elt in args | i ne c];
//        Append(~res, row);
//    else
//        for x in firstindex[idx] do
//            Append(~args,x);
//            NestedLoop(firstindex, k, idx + 1, args,c);
//        end for;
//    end if;
//    return res;
//end function;

function findpossiblerows(nonzer, c)
    //remains to pick one element <j_1,1> , <j_2,1>, ..., <j_5,5> excluding <j_c,c> 
    firstindex := AssociativeArray(); //create dictionary of second indices 1: all second indices ... etc.
    for pair in nonzer do
        if IsDefined(firstindex,pair[2]) then
            Append(~firstindex[pair[2]], pair[1]);
        else 
            firstindex[pair[2]] := [pair[1]];
        end if;
    end for;
    //firstindex[i] contains the row-indices of its nonzero entries for a column i
    //return all possibilities 
    res := [];
 //   res := NestedLoop(firstindex, k, 1, [], c);
    if n-k eq 3 then 
    for i1 in firstindex[1] do
        for i2 in firstindex[2] do
            for i3 in firstindex[3] do
                row := [i1, i2, i3];
                row := [elt : i->elt in row | i ne c];
                Append(~res, row);
            end for;
        end for;
    end for;
    end if;
    if n-k eq 4 then 
    for i1 in firstindex[1] do
        for i2 in firstindex[2] do
            for i3 in firstindex[3] do
                for i4 in firstindex[4] do
                    row := [i1, i2,  i3,  i4];
                    row := [elt : i->elt in row | i ne c];
                    Append(~res, row);
                end for;
            end for;
        end for;
    end for;
    end if;
    if n-k eq 5 then 
    for i1 in firstindex[1] do
        for i2 in firstindex[2] do
            for i3 in firstindex[3] do
                for i4 in firstindex[4] do
                    for i5 in firstindex[5] do
                        row := [i1, i2,  i3,  i4, i5];
                        row := [elt : i->elt in row | i ne c];
                        Append(~res, row);
                    end for;
                end for;
            end for;
        end for;
    end for;
    end if;
    return res;

end function;
//this function returns a vector of vectors, where each vector is of length n-k -1 and contains a possible choice of row indices for the columns not equal to c of nonzero elements.


//r is an element of the output of findpossiblerows and c is an element of the output of findpossiblecolumns
//xs is the k by n-k matrix filled with the variables
function evaluatexs(r, c, xs)
    evalxs := xs;
    //we set all entries in c to 1
    for i in [1 .. k] do
        evalxs[i, c] := 1;
    end for;
    for i->x in r do
        if i lt c then
            evalxs[x, i] := 1; //we skipped the one in column c
        else 
            evalxs[x, i+1] := 1;
        end if;
    end for;
    return evalxs;
end function;


function chooseOptimalOnes(xs, b, M, R, nonbases)
    nonbasisminors := constructMinorsUnframed(M, nonbases, R, b);
    nonzer := nonzeroEntries(M, nonbasisminors, R); //possible placement of ones, given the above
    //you need to choose one element in each column and row, and iterate over each choice for each b
    possiblecols := findpossiblecols(nonzer); 
    if #possiblecols eq 0 then
        return [* -1, []*];
    end if;
    for c in possiblecols do
        //now have to iterate over all possible row choices, find the best degree, then compare across all columns...
        rowchoices := findpossiblerows(nonzer, c);
        if #rowchoices eq 0 then
            return [* -1, []*];
        end if;
        for r in rowchoices do 
            evalxs := evaluatexs(r,c, xs);
            evalvector := Eltseq(evalxs); //evaluate the column and row choices to be 1
            for i in [1 .. n] do Append(~evalvector, 0); end for; //lambda are dumb
            deg :=  &*[Degree(Evaluate(poly, evalvector)) : poly in nonbasisminors | poly ne 0];
            if not assigned(bestdeg) then
                bestdeg := deg;
                bestr := r;
            else
                if deg lt bestdeg then
                    bestdeg := deg;
                    bestr := r;
                end if;
            end if;
        end for;
        //the for loop above finds the smallest degree over all the row choices: bestr is the best rowchoice and bestdeg the smallest degree. 
        if not assigned(bestr) then
            //to test if we need this:
            print("This was needed!");
            return [* -1, []*];  //no good options -> this should only happen if we have no rowchoices, and then the function already terminated. We might(!) not need this if clause. 
        end if;
        //now we have to compare over all choices of columns
        if not assigned(bestpair) then
            winningcdeg := bestdeg;
            bestpair := [* c, bestr *];
        else 
            if bestdeg lt winningcdeg then
                winningcdeg := bestdeg;
                bestpair := [* c, bestr *]; //choose best [c, r] after optimizing r
            end if;
        end if;
    end for;
    return bestpair;
end function;

//now we have to find the optimal choice of basis to assign to the identity matrix, so we go over all choices and find the best (c,r) for these and then compare the bestdeg for all these tuples (b, bestpair) to find the optimal basis b
function chooseOptimalBasis(nonbases, bases, M, R, xs)
    //returns a frame for M which gives the smallest product of degrees for the minors of the nonbases
    firsttime := true; //work-around to check if we have assigned bestdeg
    done := false;

    for i->b in bases do
        c, r := Explode(chooseOptimalOnes(xs, b, M, R, nonbases));
        if c ne -1 then
           // print c;
            t := Cputime();
            evalxs:= evaluatexs(r, c, xs);
            t:= Cputime();
            Id := ScalarMatrix(k,R!1);
            Meval := HorizontalJoin(Id, evalxs);
            nonbasisminors := constructMinorsUnframed(Meval, nonbases, R, b);
            t := Cputime();
            deg := &*[Degree(poly) : poly in nonbasisminors | poly ne 0];
            t := Cputime(t);
            if firsttime then
                bestdeg := deg;
                bestb := b;
                bestminors := nonbasisminors;
                bestpair := [* c, r *];
                firsttime := false;
            end if;
            t := Cputime(t);
            if deg lt bestdeg then
                bestdeg := deg;
                bestb := b;
                bestminors := nonbasisminors;
                bestpair := [* c, r *];
            end if;
            // if bestdeg lt 2^(#nonbases - 5) then
            //     // good enough?
            //     return bestb, bestdeg, bestpair, bestminors;
            // end if;
        end if;
    end for;
    return bestb, bestdeg, bestpair, bestminors;
end function;

function doline(nonbases)
    h:=k*(n-k)+1;
	R<[x]> := PolynomialRing(Rationals(), h+n-1);
    xs := Matrix(k, n-k, [R.i : i in [1..k*(n-k)]]);
	Id := ScalarMatrix(k,R!1);
    M := HorizontalJoin(Id, xs);
    bases :=  SetToSequence(Set(U) diff Set(nonbases)); 
    b, deg, pair, nonbasisminors := chooseOptimalBasis(nonbases, bases, M, R, xs);
    //print "done with optimal basis";
    c, r := Explode(pair);
    //construct equations forced by setting elements in c and r to 1
    nonzereqns := [];
    for i in [1 .. k] do
        Append(~nonzereqns, xs[i, c]-  1);
    end for;
    for i->x in r do
        if i lt c then
            Append(~nonzereqns, xs[x, i] - 1);
        else
            Append(~nonzereqns, xs[x, i+1] - 1);
        end if;
    end for;

    eqns := nonbasisminors cat nonzereqns; // construct equations of the ideal I
    I := Ideal(eqns);
    Q := quo<R|I>;    

    //construct basisminors
    basisminors := constructMinorsUnframed(M, bases, R, b);
    
    Isat := saturateIdeal(eqns, basisminors, R);
    //print "Done: saturation with basisminors"; 
    gb := GroebnerBasis(Isat);
    //print "Done: GB for saturation with basisminors";
    d := Dimension(Isat);
    d := d - n;
    leqns := constructLambdaEqns(M,R);
    selfdualeqns := gb cat leqns;
    selfdualI := ideal<R|selfdualeqns>;
    sdIsat := Saturation(selfdualI, ideal<R| &*[x[i]: i in [h .. h+n-1]]>);
    //print "Done: saturation with product of lambdas";
    sdIsatelim := EliminationIdeal(sdIsat, {x[i] : i in [1 .. k*(n-k)]});
    //print "Done: Elimination of lambdas";
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
       // print "Done: resaturation with basisminors";
        sdIsatelim := Isdsat;
        selfdualdim := Dimension(sdIsatelim) - n;
        Q := quo<R | sdIsatelim>;
        Mspec := ChangeRing(M, Q);
        sdequalsreal := sdIsatelim eq Isat;
    end if;

    output := [* bases, gb, d, Basis(sdIsatelim), selfdualdim, sdequalsreal, [Eltseq(r) : r in Rows(Mspec)] *];
    return output;

end function;

//figure out how to take out the unframed ones in rank 4 on 9 elements

if assigned seq then
    SetColumns(0);
    SetAutoColumns(false);
    seq := eval seq;
    inputs := Split(Read(filename), "\n");
    input := eval inputs[seq];
    if seq notin [] then //take the non-framed matroids out
        output := doline(input);
        output := [* seq *] cat output;
        print strip(Join([Sprint(elt) : elt in output], ":"));
    end if;
    exit;
end if;

//Unframed for (4,8) sind 9 und 12
//julia> println(nonbases(L[unframed_selfproj[1]]))
//[[1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 3, 6], [1, 2, 3, 7], [1, 2, 3, 8], [1, 2, 3, 9], [1, 2, 4, 5], [1, 2, 4, 6], [1, 2, 4, 7], [1, 2, 4, 8], [1, 2, 4, 9], [1, 2, 5, 6], [1, 2, 5, 7], [1, 2, 5, 8], [1, 2, 5, 9], [1, 3, 4, 5], [1, 3, 4, 6], [1, 3, 4, 7], [1, 3, 4, 8], [1, 3, 4, 9], [1, 3, 5, 6], [1, 3, 5, 7], [1, 3, 5, 8], [1, 3, 5, 9], [1, 4, 5, 6], [1, 4, 5, 7], [1, 4, 5, 8], [1, 4, 5, 9], [1, 6, 7, 8], [1, 6, 7, 9], [1, 6, 8, 9], [1, 7, 8, 9], [2, 3, 4, 5], [2, 3, 4, 6], [2, 3, 4, 7], [2, 3, 4, 8], [2, 3, 4, 9], [2, 3, 5, 6], [2, 3, 5, 7], [2, 3, 5, 8], [2, 3, 5, 9], [2, 4, 5, 6], [2, 4, 5, 7], [2, 4, 5, 8], [2, 4, 5, 9], [2, 6, 7, 8], [2, 6, 7, 9], [2, 6, 8, 9], [2, 7, 8, 9], [3, 4, 5, 6], [3, 4, 5, 7], [3, 4, 5, 8], [3, 4, 5, 9], [3, 6, 7, 8], [3, 6, 7, 9], [3, 6, 8, 9], [3, 7, 8, 9], [4, 6, 7, 8], [4, 6, 7, 9], [4, 6, 8, 9], [4, 7, 8, 9], [5, 6, 7, 8], [5, 6, 7, 9], [5, 6, 8, 9], [5, 7, 8, 9], [6, 7, 8, 9]]

//julia> println(nonbases(L[unframed_selfproj[2]]))
//[[1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 3, 6], [1, 2, 3, 7], [1, 2, 3, 8], [1, 2, 3, 9], [1, 2, 4, 5], [1, 2, 4, 6], [1, 2, 5, 6], [1, 2, 7, 8], [1, 2, 7, 9], [1, 2, 8, 9], [1, 3, 4, 5], [1, 3, 4, 6], [1, 3, 5, 6], [1, 3, 7, 8], [1, 3, 7, 9], [1, 3, 8, 9], [1, 4, 5, 6], [1, 7, 8, 9], [2, 3, 4, 5], [2, 3, 4, 6], [2, 3, 5, 6], [2, 3, 7, 8], [2, 3, 7, 9], [2, 3, 8, 9], [2, 4, 5, 6], [2, 7, 8, 9], [3, 4, 5, 6], [3, 7, 8, 9], [4, 5, 6, 7], [4, 5, 6, 8], [4, 5, 6, 9], [4, 5, 7, 8], [4, 5, 7, 9], [4, 5, 8, 9], [4, 6, 7, 8], [4, 6, 7, 9], [4, 6, 8, 9], [4, 7, 8, 9], [5, 6, 7, 8], [5, 6, 7, 9], [5, 6, 8, 9], [5, 7, 8, 9], [6, 7, 8, 9]]

