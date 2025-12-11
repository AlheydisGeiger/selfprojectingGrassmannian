## Additional Code to verify Tables and Examples

The following explains how to use the code in this directory to obtain the tables and examples from the paper.

**Tables 2 and 3**

These tables show the distribution of the dimension of the (self-projecting) realization spaces for matroids of rank k on n elements, for which the realization spaces were computed.
The code is included in the file ``generating_tables.jl``. There are two functions, one for the dimensions of the realization spaces, in the article denoted by $\mathcal{R}$, and one for the dimensions of the self-projeting realization spaces $\mathcal{S}$; see Definition 4.8.

The functions need to access the magma output files, stored in the magma directory of this gitHub repository. These files need to be downloaded in order to reproduce the tables.
```julia-repl
julia> using Oscar
julia> include("your/path/to/generating_tables.jl")
julia> generate_table_content_dimR("your/path/to/rk3on8.out",3,8)
The dimensions of the realization spaces for self-projecting rank 3 matroids on 8 elements are distributed as follows (without the uniform matroid)
[-1   0   1    2    3   4   5   6   7   8]
[ 2   2   5   11   12   9   3   3   1   0]

julia> generate_table_content_dimS("your/path/to/rk3on8.out",3,8)
The dimensions of the self-projecting realization spaces for self-projecting rank 3 matroids on 8 elements are distributed as follows (without the uniform matroid)
[-1   0   1    2    3   4   5   6   7   8]
[ 2   2   5   11   12   9   3   3   1   0]
```

```julia-repl
julia> include("your/path/to/generating_tables.jl")
julia> generate_table_content_dimR("your/path/to/rk3on8.out",3,8)
The dimensions of the realization spaces for self-projecting rank 3 matroids on 8 elements are distributed as follows (without the uniform matroid)
[-1   0   1    2    3   4   5   6   7   8]
[ 2   2   5   11   12   9   3   3   1   0]

julia> generate_table_content_dimS("your/path/to/rk3on8.out",3,8)
The dimensions of the self-projecting realization spaces for self-projecting rank 3 matroids on 8 elements are distributed as follows (without the uniform matroid)
[-1   0   1    2    3   4   5   6   7   8]
[ 2   2   5   11   12   9   3   3   1   0]
```
When using as inputfiles the magma output files containing only the computations of realization spaces $\mathcal{R}$, the functions need to be endowed with an additional ``_onlyR`` at the end of their names. The inputfiles are similary marked.
```julia-repl
julia> include("your/path/to/generating_tables.jl")
julia> generate_table_content_dimR_onlyR("your/path/to/opt_3_8_onlyR.out",3,8)
The dimensions of the realization spaces for self-projecting rank 3 matroids on 8 elements are distributed as follows (without the uniform matroid)
[-1   0   1    2    3    4   5   6   7   8]
[ 2   2   5   11   12   11   5   3   1   0]
```


**Table 4**
This table shows the dimensions of realization spaces $\mathcal{R}(M)$ of self-projecting matroids of rank 4 on 9 elements with $\mathcal{S}= \emptyset$. The functions demonstrated below show how to access the identifiers for given $\dim(\mathcal{R})$ and to how to fill the row entries of Table 4.
```julia-repl
julia> include("your/path/to/generating_tables.jl")
julia> find_all_realizable_not_sp_realizable("realisation_output/rank4/rk4on9_all.out",0)
4-element Vector{Any}:
 5985
 2788
 6265
 7274
julia> length(find_all_realizable_not_sp_realizable("realisation_output/rank4/rk4on9_all.out",5))
124
```


**Example 4.12**

In order to work with the database and/or compute self-projecting realization spaces of matroids in OSCAR, you need to use the developers version of OSCAR on the branch ag/selfprojecting_matroids on <https://github.com/AlheydisGeiger/Oscar.jl/tree/ag/selfprojecting_matroids>.
To reproduce example 4.12 you can access the relevant file from the database.
```julia-repl
julia> using Oscar
julia> db = Oscar.OscarDB.get_db();
julia> find_one(db["Combinatorics.SelfProjectingMatroids"], Dict(["name"=>"r_4_n_9_index_5985"]))
The matroid is of rank 4 on 9 elements.
The realization space is
  [1   0   0   0   2//3   0      1   1   1//2]
  [0   1   0   0      0   2   1//2   1   1//2]
  [0   0   1   0      1   1      1   1      1]
  [0   0   0   1      2   2      2   1      1]
in the multivariate polynomial ring in 20 variables over QQ
within the vanishing set of the ideal
Ideal with 20 generators
avoiding the zero loci of the polynomials
RingElem[2]
The matroid does not have a self-projecting realization over characteristic zero.
The closures of the realization space and the self-projecting realization space are not equal.
```
