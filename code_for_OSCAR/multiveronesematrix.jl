using Oscar

function veronese2(M::MatElem)
    R = base_ring(M)
    newCols = Vector{Vector{elem_type(R)}}()
    for j in 1:ncols(M)
        v = M[:, j]
        col = elem_type(R)[]
        for i in 1:nrows(M)
            for k in i:nrows(M)
                push!(col, v[i] * v[k])
            end
        end
        push!(newCols, col)
    end
    return transpose(matrix(R, hcat(newCols...)))
end
