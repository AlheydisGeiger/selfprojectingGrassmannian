# selfprojectingGrassmannian
This GitHub page accompanies the paper "The Self-Projecting Grassmannian" by Alheydis Geiger and Francesca Zaffalon.
arXiv: <https://arxiv.org/abs/2511.21442)>

 It contains output files and code from the computations in Section 4 and 5, as well as the database of (self-projecting) realization spaces of self-projecting matroids of rank k on n elments over characteristic zero for (k,n) in {(2,4),...,(2,12),(3,6),(3,7),(3,8),(4,8),(4,9),(5,10)}.

This repository is still under construction. If you have any questions, contact the authors.


**Abstract:**  We introduce the self-projecting Grassmannian, an irreducible subvariety of the Grassmannian parametrizing linear subspaces that satisfy a generalized self-duality condition. We study its relation to classical moduli spaces, such as the moduli spaces of pointed curves of genus $g$, as well as to other natural subvarieties of the Grassmannian. We further translate the self-projectivity condition into the combinatorial language of matroids, introducing self-projecting matroids, and we computationally investigate their realization spaces inside the self-projecting Grassmannian.

For the cases {(2,4),(3,6),(4,8),(5,10)} the database stores material from the  article:
Alheydis Geiger, Sachi Hashimoto, Bernd Sturmfels, Raluca Vlad: Self-dual matroids from canonical curves
In: Experimental mathematics, 33 (2024) 4, p. 701-722
DOI: `10.1080/10586458.2023.2239282 <https://dx.doi.org/10.1080/10586458.2023.2239282>`_ ARXIV: https://arxiv.org/abs/2212.05910 CODE: https://github.com/sachihashimoto/self-dual

## Code for Oscar.jl 
The handling of the magma output was done using the open source computeralgebra research system Oscar, a package for the programming language julia.
The following explains how to use the code in the directory code_for_OSCAR to obtain the tables and examples from the paper.


**Tables 2 and 3**

These tables show the distribution of the dimension of the (self-projecting) realization spaces for matroids of rank k on n elements, for which the realization spaces were computed.
The code is included in the file ``generating_tables.jl``. There are two functions, one for the dimensions of the realization spaces, in the article denoted by $\mathcal{R}$, and one for the dimensions of the self-projeting realization spaces $\mathcal{S}$; see Definition 4.8.

The functions need to access the magma output files, stored in the magma directory of this gitHub repository. These files need to be downloaded in order to reproduce the tables.

```
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
When using as inputfiles the magma output files containing only the computations of realization spaces $\mathcal{R}$, the functions need to be endowed with an additional ``_onlyR`` at the end of their names. The inputfiles are similary marked.
```
julia> using Oscar
julia> include("your/path/to/generating_tables.jl")
julia> generate_table_content_dimR_onlyR("your/path/to/opt_3_8_onlyR.out",3,8)
The dimensions of the realization spaces for self-projecting rank 3 matroids on 8 elements are distributed as follows (without the uniform matroid)
[-1   0   1    2    3    4   5   6   7   8]
[ 2   2   5   11   12   11   5   3   1   0]
```


**Table 4**
This table shows the dimensions of realization spaces $\mathcal{R}(M)$ of self-projecting matroids of rank 4 on 9 elements with $\mathcal{S}= \emptyset$. The functions demonstrated below show how to access the identifiers for given $\dim(\mathcal{R})$ and to how to fill the row entries of Table 4.
```
julia> using Oscar
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
To reproduce example 4.12 you need to download the relevant file from the database directory of this gitHub repository. Then you can run the following code:
```
julia> using Oscar
julia> load("your/path/to/r_4_n_9_index_5985.jl")
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


Project contributors: Alheydis Geiger, Francesca Zaffalon.

Corresponding author of this page: Alheydis Geiger, 
<a href="mailto:geiger\@mis.mpg.com">geiger\@mis.mpg.de</a>

 
Software used: Magma (V2.27), Julia (Version 1.12.1), OSCAR (version 1.6.0-DEV), 
GNU parallel 20221122, Macaulay2 (version 1.24.11)

Project page created 18/11/2025.
Last updated 26/11/2025.
