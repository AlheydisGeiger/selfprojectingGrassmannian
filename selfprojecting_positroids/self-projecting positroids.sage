###########################################################################
# Positroids objects constructions and translations
###########################################################################

#Imports
from sage.matroids.advanced import *
from itertools import combinations
from random import randint
from itertools import product

# Translating from permutation to bounded affine permutation
# Since selfproj matroids do not have coloops, we transform the permutation by assuming fixed points are loops
def bounded_affine_permutation_nocoloop(f):
    n = len(f)
    g = []
    for i in range(n):
        if f[i]>i:
            g.append(f[i])
        else:
            g.append(f[i]+n)
    return g

# Translating from permutation to bounded affine permutation
# Assuming the fixed points are coloops (okay if only considering simple positroids)
def bounded_affine_permutation(f):
    n = len(f)
    g = []
    for i in range(n):
        if f[i]>i+1:
            g.append(f[i])
        else:
            g.append(f[i]+n)
    return g

# Computes the rank of the positroid, given its bounded affine permutation
def rank_bap(p):
    n = len(p)
    r = 1/n*sum(p[i]-i-1 for i in range(n))
    return r

# Computes the codimension of the positroid, given its bounded affine permutation
def codimension_bap(f):
    n = len(f)
    g = f + [f[i] +n for i in range(n)]
    l = 0
    for i in range(n):
        for j in range(i+1,2*n):
            if g[i]>g[j]:
                l +=1
    return l

# Computes the dimension of the positroid, given its bounded affine permutation
def dimension_bap(p):
    n = len(p)
    r = rank_bap(p)
    codimp = codimension_bap(p)
    dimp = k*(n-k) - codimp
    return dimp

# Computes the Grassmann necklace from a bounded affine permutation
def grassmann_necklace_from_bap(p):
    n = len(p)
    k = rank_bap(p)
    necklace = []
    doublep = [p[i] for i in range(n)] + [p[i]+n for i in range(n)]
    for i in range(n):
        I = []
        for j in range(i+n):
            if doublep[j]> i+n:
                I.append(doublep[j]%n)
        if 0 in I:
            I.remove(0)
            I.append(n)
        I = sorted(I)
        necklace.append(I)
    return necklace

def get_value_in_map(x, my_zero, n):
    return x + n if x < my_zero else x

# Compare two sets s1 and s2 coordinate-wise in cyclic order starting from my_zero.
# Return True if all elements in s1 >= corresponding elements in s2 after sorting by cyclic order.
def bigger(s1, s2, my_zero, n):
    s11 = sorted(s1, key=lambda x: get_value_in_map(x, my_zero, n))
    s22 = sorted(s2, key=lambda x: get_value_in_map(x, my_zero, n))
    return all(get_value_in_map(s11[i], my_zero, n) >= get_value_in_map(s22[i], my_zero, n) for i in range(len(s1)))

# Constructs the matroid from a Grassmann necklace
def matroid_from_Grassmann_necklace(necklace):
    n = len(necklace)
    k = len(necklace[0])
    bases_envelope = list(Subsets(range(1, n+1), k))  # 1-based
    for i in range(1, n+1):
        Ii = necklace[i-1]
        bases_envelope = [b for b in bases_envelope if bigger(b, Ii, i, n)]
    return Matroid(bases=bases_envelope, groundset=list(range(1, n+1)))

# Constructs the matroid from a bounded affine permutation
def matroid_from_bap(p):
    necklace = grassmann_necklace_from_bap(p)
    return matroid_from_Grassmann_necklace(necklace)

# Check if all the k-dim subsets of the ground set are independent
# Returns True if all k-subsets are independent, False otherwise
def check_matroid_k(M,k):
    sets = list(Subsets(M.groundset(), k))
    for s in sets:
        if not M.is_independent(s):
            return False
    return True

def check_bap_k(p,k):
    M = matroid_from_bap(p)
    return check_matroid_k(M,k)

# Returns all rank k positroids on n elements without coloops
def all_rank_k(k,n):
    positroids = []
    for f in Permutations(n):
        p = bounded_affine_permutation(f)
        if rank_bap(p) == k:
            positroids.append(p)
    return positroids

# Computes the sign of the permutation that sends S + {i} to sorted(S + {i})
def sign_Si(S,i):
    Si = sorted(set(S).union({i}))
    S = sorted(list(S))
    new_order = S+[i]
    perm = [Si.index(x) + 1 for x in new_order]  
    return Permutation(perm).signature()


###########################################################################
# Self-projecting functions
###########################################################################

# Checks if a matroid is self-projecting
# Returns True if M is self-projecting,i.e. if M has no half-coloop, False otherwise
def is_selfprojecting(M):
    k = M.rank()
    n = len(M.groundset())
    boo = True
    for f in M.flats(k-1):
        boo = True
        for g in M.flats(k-1):
            if len(f.union(g)) == n-1:
                boo = False
                break
        if not boo:
            return False
    return boo

# Check if a matroid is an orthopositroid with respect to a given lambda vector
def is_orthopositroid(lam,M):
    n = len(M.groundset())
    bases = M.bases()
    kmin1subsets = [set(S) for S in M.independent_sets(M.rank()-1)]
    for S in kmin1subsets:
        for T in kmin1subsets:
            Aplus = []
            Amin = []
            for i in range(1,n+2):
                if S.union({i}) in bases and T.union({i}) in bases:
                    if lam[i-1]*sign_Si(S,i)*sign_Si(T,i)>0:
                        Aplus.append(i)
                    else: 
                        Amin.append(i)
            if (len(Aplus)==0 and len(Amin)>0) or (len(Aplus)>0 and len(Amin)==0):
                return False
    return True

# Creates all admissible lambdas for orthogonal Grassmannian OGr(k,n)
def create_real_lambda(k,n):
    vectors = []
    for v in product([1, -1], repeat=n):
        if v[0] != 1:
            continue  # fix sign
        if v.count(1) >= k and v.count(-1) >= k:
            vectors.append(vector(v))
    return vectors

###########################################################################
# Generation of positroids and selfprojecting positroids
###########################################################################

parameters = [(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,6),(3,7),(3,8),(3,9),(3,10),(4,8),(4,9),(4,10),(5,10)]

# Generation of all loopless positroids divided by rank and size of ground set
data = {}
for k,n in parameters:
    data[(k,n)] = all_rank_k(k,n)
    print((k,n), len(data[(k,n)]))

save(data, "data_positroids.sobj")
## Can be loaded from data = load("data_positroids.sobj")

# Generation of all isomorphism classes of positroids, simple whenever k>2
data_iso = {}
for k,n in parhigh:
    data_iso[(k,n)] = []
    i=0
    for p in data[(k,n)]:
        if i % 10000 == 0:
            print(f"Processed {i} items...")
        i+=1
        # Skip positroids with adjacent parallel elements
        for j in range(n):
            iplusone = False
            if p[j]==j+2:
                iplusone = True
                break
        if iplusone and k>2:
            continue
        M = matroid_from_bap(p)
        # Skip non-simple positroids when k>2
        if k>2 and not M.is_simple():
            continue
        nbases = M.bases_count()
        is_new = True
        for iso_class in data_iso[(k,n)]:
            if nbases == iso_class[0]:
                q = iso_class[1]
                Mq = matroid_from_bap(q)
                if M.is_isomorphic(Mq):
                    iso_class.append(p)
                    is_new = False
                    break
        if is_new:
            data_iso[(k,n)].append([nbases,p])
    for iso in data_iso[(k,n)]:
        iso.pop(0)
    print("Finished: ", (k,n) , len(data_iso[(k,n)]) ,"isomorphism classes.")

save(data_iso, "data_iso_positroids.sobj")
## Can be loaded from data_iso = load("data_iso_positroids.sobj")

# Construction of self-projecting (isomorphism classes of simple) positroids
data_selfprojecting = {}
for k,n in parameters:
    data_selfprojecting[(k,n)] = []
    for i, p in enumerate(data_iso[(k,n)]):
        M = matroid_from_bap(p[0])
        if is_selfprojecting(M):
            data_selfprojecting[(k,n)].append(p[0])
        if i % 1000 == 0:
            print(f"Processed {i} items...")
    print("Finished: ", (k,n) , len(data_selfprojecting[(k,n)]) ,"self-projecting isomorphism classes.")

save(data_selfprojecting, "data_selfprojecting_positroids.sobj")
## Can be loaded from data_selfprojecting = load("data_selfprojecting_positroids.sobj")

data_orthopositroids = {}
for k,n in parameters:
    data_orthopositroids[(k,n)] = []
    lambda_vectors = create_real_lambda(k,n)
    for j, p in enumerate(data_selfprojecting[(k,n)]):
        M = matroid_from_bap(p)
        for lam in lambda_vectors:
            if is_orthopositroid(lam,M):
                data_orthopositroids[(k,n)].append((p,lam))
                break
        if j % 100 == 0:
            print(f"Processed {j} items...")
    print("Finished: ", (k,n) , len(data_orthopositroids[(k,n)]) ,"orthopositroids.")

save(data_orthopositroids, "data_orthopositroids.sobj")
## Can be loaded from data_orthopositroids = load("data_orthopositroids.sobj")


###########################################################################
# Example of self-projecting positroid which is not an orthopositroid
###########################################################################

nonorthopositroid = data_selfprojecting[(4,9)].copy()
for (f,lam) in data_orthopositroids[(4,9)]:
    if f in nonorthopositroid:
        nonorthopositroid.remove(f)

nonorthopositroid
f = [4, 6, 8, 7, 9, 11, 10, 12, 14] # = nonorthopositroid[0]
M = matroid_from_bap(f)
list(M.nonbases())
