using Oscar
function extract_entry(line::String,n::Int)::String
    # Regex: match digits at the start of the line, followed by a colon
    #(id:bases:gb:dim:gb:dim:bool:template)
    pattern = r"^(\d+):(.*):(.*):(-?\d*):(.*):(-?\d*):(\w*):(.*)"
    m = match(pattern, line)
    if m !== nothing
        result = m.captures[n]
    else 
        error("Input did not match the pattern")
    end
    return result
end

function extract_entry_onlyR(line::String,n::Int)::String
    # Regex: match digits at the start of the line, followed by a colon
    #(id:bases:gb:dim:gb:dim:bool:template)
    pattern = r"^(\d+):(.*):(.*):(-?\d*):(\w*):(\w*):(\w*):(.*)"
    m = match(pattern, line)
    if m !== nothing
        result = m.captures[n]
    else 
        error("Input did not match the pattern")
    end
    return result
end



function build_matroid(M::MatElem,k::Int,n::Int)::Matroid
    nonba = Vector{Vector{Int}}([])
    for b in bases(uniform_matroid(k,n))
        if iszero(det(M[:,b]))
            push!(nonba,b)
        end
    end
    return matroid_from_nonbases(nonba,n)
end
function extract_first_ints(filename::String)::Set{Int}
    result = Set()
    # Regex: match digits at the start of the line, followed by a colon
    pattern = r"^(\d+):(.*):(.*):(-?\d*):(.*):(.*):(.*):(.*)"
    open(filename, "r") do file
        for line in eachline(file)
            m = match(pattern, line)
            if m !== nothing
                push!(result, parse(Int, m.captures[1]))
            end
        end
    end
    return result
end
function find_not_terminated(filename::String,N::Int)::Set{Int}
    S = Set{Int}(i for i in 1:N)
    t = extract_first_ints(filename)
    return setdiff!(S,t)
end

#if the kwarg notallterminated is set to true the cases when we do not have a computation of the self-projecting space are included. These are the cases where  the id does not appear in inputfile, but only in inputfile2
function create_mrdi(inputfile::String,inputfile2::String,k::Int,n::Int;notallterminated::Bool = true)
    i = 0;
    global R, x = polynomial_ring(QQ, :x=>1:k*(n-k));
    open(inputfile, "r") do file
        for line in eachline(file) 
            i = i+1
            id = eval(Meta.parse(extract_entry(line,1)))
            println(id)
            gb1 = eval(Meta.parse(extract_entry(line,3)))
            gb2 = eval(Meta.parse(extract_entry(line,5)))
            S, p = quo(R, ideal(R,gb1));
            T, q = quo(R, ideal(R,gb2));
            M = matrix(R,eval(Meta.parse(extract_entry(line,8))))
            dimR = eval(Meta.parse(extract_entry(line,4)))
            dimS = eval(Meta.parse(extract_entry(line,6)))
            println(dimR,",",dimS)
            if iszero(M) && dimR <0 # not realizable at all, in this case gb1 && gb2 should both be one
                if !isone(gb1[1]) || !isone(gb2[1]) #sanity check
                    error("not realizable matroid has Groebner basis not equal to 1.")
                end
                m = matroid_from_bases(eval(Meta.parse(extract_entry(line,2))),n)
                #In this case I cannot compute tbe Oscar.basis_minors as we do it usually, but there should still be inequations. Therefore, we use the oscar function to compute the realization_space and hope that it is not too slow!
                #MRS = realization_space(m,char = 0, ground_ring = QQ)
                #MRSSP=Oscar.MatroidRealizationSpaceSelfProjecting(defining_ideal(MRS),inequations(MRS),R,nothing,0,nothing,QQ);
                MRS = Oscar.MatroidRealizationSpace(ideal(R,gb1),#Oscar.basis_minors(M,bases(m)),
                Vector{RingElem}(),R,nothing,0,nothing,QQ);
                MRSSP=Oscar.MatroidRealizationSpaceSelfProjecting(ideal(R,gb2),#Oscar.basis_minors(M,bases(m)),
                Vector{RingElem}(),R,nothing,0,nothing,QQ);
            elseif iszero(M) && dimR >= 0 #realizable without selfprojecting realization
                open(inputfile2,"r") do file2
                    for line2 in eachline(file2) 
                        id2 = eval(Meta.parse(extract_entry_onlyR(line2,1)))
                        if id == id2
                            #sanity check
                            dimR2 = eval(Meta.parse(extract_entry_onlyR(line2,4)))
                            if !(dimR == dimR2)
                                error("the dimensions of the realization spaces in the two computations does not agree!")
                            end
                            gb1_r = eval(Meta.parse(extract_entry_onlyR(line2,3)))
                            S, p = quo(R, ideal(R,gb1_r));
                            M_r = matrix(R,eval(Meta.parse(extract_entry_onlyR(line2,8))))
                            m_r = build_matroid(p.(M_r),k,n)
                            MRS = Oscar.MatroidRealizationSpace(ideal(R,gb1_r),Oscar.basis_minors(M_r,bases(m_r)),R,M_r,0,nothing,QQ);
                            MRSSP=Oscar.MatroidRealizationSpaceSelfProjecting(ideal(R,gb2),inequations(MRS),R,nothing,0,nothing,QQ);
                            if !is_isomorphic(m_r,matroid_from_bases(eval(Meta.parse(extract_entry_onlyR(line2,2))),n))
                                error("the two matroids are not isomorphic!")
                            end
                            m = m_r
                        end
                    end
                end
            elseif dimS < dimR && dimS>=0 # S is a proper nonempty subset of R
                m = build_matroid(q.(M),k,n)
                MRSSP=Oscar.MatroidRealizationSpaceSelfProjecting(ideal(R,gb2),Oscar.basis_minors(M,bases(m)),R,M,0,nothing,QQ)
                open(inputfile2,"r") do file2
                    for line2 in eachline(file2) 
                        id2 = eval(Meta.parse(extract_entry_onlyR(line2,1)))
                        if id == id2
                            gb1 = eval(Meta.parse(extract_entry_onlyR(line2,3)))
                            S, p = quo(R, ideal(R,gb1));
                            M_r = matrix(R,eval(Meta.parse(extract_entry_onlyR(line2,8))))
                            m_r = build_matroid(p.(M_r),k,n)
                            MRS = Oscar.MatroidRealizationSpace(ideal(R,gb1),Oscar.basis_minors(M_r,bases(m_r)),R,M_r,0,nothing,QQ);
                            dimR2 = eval(Meta.parse(extract_entry_onlyR(line2,4)))
                            #sanity check
                            if !(dimR == dimR2)
                                error("the dimensions of the realization spaces in the two computations does not agree!")
                            end
                            if !(Set(bases(m)[i] for i in 1:length(bases(m))) == Set(bases(m_r)[i] for i in 1:length(bases(m_r))) )
                                error("the two matroids are not the same!")
                            end
                        end
                    end
                end
            else 
                if !(dimR == dimS) #just a sanity check
                    error("The dimesion of R and S are not the same, but none of the other elseif's applied! Something is wrong!")
                end
                m = build_matroid(p.(M),k,n)
                MRS = Oscar.MatroidRealizationSpace(ideal(R,gb1),Oscar.basis_minors(M,bases(m)),R,M,0,nothing,QQ);
                MRSSP=Oscar.MatroidRealizationSpaceSelfProjecting(ideal(R,gb2),Oscar.basis_minors(M,bases(m)),R,M,0,nothing,QQ)
            end
            # I need to make dimS and dimR = -1 in the case that they are negative
            if dimS <0
                dimS = -1;
            end
            if dimR <0
                dimR=-1;
            end
            boo = eval(Meta.parse(extract_entry(line,7)))
           # if dimR>=0 && dimS>=0
            save("r_$(k)_n_$(n)_index_$id.mrdi",MatroidRealizations("r_$(k)_n_$(n)_index_$id",m,k,n,MRS,dimR, MRSSP ,dimS,boo));
            #end
            println(i)
        end
    end
    if notallterminated
    L = find_not_terminated(inputfile,countlines(inputfile2));
    open(inputfile2, "r") do File
        for line in eachline(inputfile2)
            id = eval(Meta.parse(extract_entry_onlyR(line,1)))
            println(id)
            if id in L
                dimR = eval(Meta.parse(extract_entry_onlyR(line,4)))
                gb1_r = eval(Meta.parse(extract_entry_onlyR(line,3)))
                S, p = quo(R, ideal(R,gb1_r));
                if dimR >=0
                    M_r = matrix(R,eval(Meta.parse(extract_entry_onlyR(line,8))))
                    m = build_matroid(p.(M_r),k,n)
                    MRS = Oscar.MatroidRealizationSpace(ideal(R,gb1_r),Oscar.basis_minors(M_r,bases(m)),R,M_r,0,nothing,QQ);
                else 
                    m = matroid_from_bases(eval(Meta.parse(extract_entry_onlyR(line,2))),n)
                    MRS = Oscar.MatroidRealizationSpace(ideal(R,gb1_r),Vector{RingElem}(),R,nothing,0,nothing,QQ);
                end
                save("r_$(k)_n_$(n)_index_$id.mrdi",MatroidRealizations("r_$(k)_n_$(n)_index_$id",m,k,n,MRS,dimR, nothing ,nothing,nothing));
                println(id);
            end
        end
    end
    end
end


