from sympy.combinatorics.perm_groups import PermutationGroup
from sympy.combinatorics.permutations import Permutation
from Program8_1 import theta
from Program8_1 import surfaces_fixes

def div (L,T):
    G=PermutationGroup(L)
    M=G._elements
    n=len(M)
    F=surfaces_fixes(L,T)
    N=[]
    while F!=[]:
        b=F[0]
        N=N+[b]                                 #We consider b as a representative
        for i in range(0,n):
            a=theta(M[i],T)*b*(M[i]**-1)        #We compute the orbit of b
            if a in F:                          #We remove all the elements of 
                F.remove(a)                     #the orbit of b from F
    return len(N)                        
