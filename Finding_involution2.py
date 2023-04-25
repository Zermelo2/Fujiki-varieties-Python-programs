from sympy.combinatorics.perm_groups import PermutationGroup
from sympy.combinatorics.permutations import Permutation
from itertools import combinations
from Finding_involution1 import The_Automorphisms
import copy
import math

#Given B a family of generators, the next function is a recursive construction of all the
#elements of the group G by product of elements of B. To obtained the involution
#theta which sends each element of B to its inverse, we need to know how every elements
#of G is written as a product of elements of B. E will be the list of elements of G 
#already constructed; we start the program with E=[\id] and at each steps we produce 
#elements obtained from products of elements of E and elements of B.

def tab(B,E):
    G=PermutationGroup(B)
    M=G._elements
    b=len(B)                #To keep the elements that we already have constructed,
    B2=[G.identity]+B       #we also need to multiply by $\id$. We will multiply  
    if set(E)==set(M):      #the elements of E by the elements in B2.
        return E            #If we have all the elements of G, we stop the program.
    else:                   
       e=len(E)
       PP=[]
       for i in range(0,e):
           for j in range(0,b+1):       #We obtain a new list of elements PP by multiplying 
               PP=PP+[E[i]*B2[j]]       #all elements of E by all elements of B2.
       return tab(B,PP)

#The involution theta defined previously sends all elements of B to their inverse. 
#To know the image of an element x of G by theta, we use the previous function tab
#which decomposes x in a product of elements of B. The argument R of the function 
#will be taken equal to tab(B,[\id]). We need this argument to avoid recomputing 
#tab(B,[\id]) each time that we need to use theta. The program is constructed as follows. 
#Let x be an element of G. We search x in R. Then i the index of x in R will tell how x 
#decomposes as a product of elements of B. It is obtained by writing i in base len(B)+1.
#The Python function "%" provides the rest of the Euclidian division and the function "//"
#provides the quotient.


def theta(R,B):
    G=PermutationGroup(B)
    B=[G.identity]+B
    b=len(B)
    a=int(math.log(len(R),b))      #a corresponds to the number of multiplications that we 
    def f(x):                      #need to obtain all elements of G.
        i=R.index(x)               #We find the element x in the list R and knowing its
        T=G.identity               #index i, we can deduce it decomposition in elements of B.
        for j in range(0,a):
            T=(B[i%(len(B))])**-1*T     #We take the inverses of the elements that compose x.
            i=i//(len(B))  
        return T
    return f

#The group G is given by a family of generators L. The next function returns all possible
#basis of G, it is based on the Tarski Theorem (see Definition C.1 and Theorem C.2).

def generators(L):
    G=PermutationGroup(L)
    M=G._elements
    M.remove(G.identity)
    m=len(M)
    N=[]                        #N will contain the basis that we have already found.
    a=True                      #a will be the test that tell to the program when to stop.
    k=2                         #k will be the number of elements of a basis.
    while a:
       A=list(combinations(M,k))
       r=len(A)             #If N is not empty, the program stops apart if we find a
       if N!=[]:            #larger basis (see below).
           a=False              
       O=copy.copy(N)       #O will contain the basis that we already got of length smaller
       for i in range(0,r): #or equal to k-1.
           b=True
           for j in range(0,len(O)):
               b=b*(not (O[j].issubset(set(A[i]))))     #We verify that A[i] does not strictly
           if b:                                        #contain a basis.
               H=PermutationGroup(list(A[i]))
               if G.order()==H.order():             #If moreover A[i] generates G, then it
                   N=N+[set(A[i])]                  #is a basis.
                   a=True                           #If b has been True at least once, we 
       k=k+1                                        #need to continue the program, so a 
    N2=[]                                           #becomes True, else, a stay False and 
    n=len(N)                                        #the program will stop, according to  
    for i in range(0,n):                            #Theorem C.2 (there is no larger basis).
        N2=N2+[list(N[i])]                              
    return N2                           #Here for practical reasons, we just write the basis
                                        #as list instead of set.


#The next function keeps only the basis that define a bijection from G to G. To verify
#that we have a bijection, we only need to check that the image of theta has the same
#cardinal as G. We also eliminate redundancy; if two basis give the same bijection, we
#keep only one of them.

def bijections(L):
    A=generators(L)
    G=PermutationGroup(L)
    M=G._elements
    m=len(M)
    A2=[]                                       #A2 will be the list of bijections
    AA2=[]                                      #AA2 is the list of the images of 
    while A!=[]:                                #the bijections in A2.
        I=A[0]
        RI=tab(I,[H.identity])
        A.remove(A[0])
        M3=[]
        for i in range(0,m):
            M3=M3+[theta(RI,I)(M[i])]           #We construct the list M3 of the image of
        if set(M3)==set(M):                     #theta_I. If theta_I is a bijection,
           a=True                               #we keep it.
           j=0
           while a==True and j<len(AA2):        #Here we avoid the redundancy.
               a=a*(M3!=AA2[j])                 #M3 is the image of I
               j=j+1                            #If this image corresponds to 
           if a:                                #an image already found we do not take I.
               A2=A2+[I]
               AA2=AA2+[M3]
    return A2

#The next function keeps the morphisms among the bijections. They are put in the list A2.

def involutions(L):
    A=bijections(L)
    G=PermutationGroup(L)
    M=G._elements
    M.remove(H.identity)
    C=list(combinations(M,2))               #We consider C the set of all combinations of 2
    A2=[]                                   #elements (x,y). We will verify that
    while A!=[]:                            #theta(x.y)=theta(x).theta(y).
        I=A[0]
        RI=tab(I,[H.identity])
        A.remove(A[0])
        a=True
        j=0                                 #We verify that the bijection verifies the 
        while a==True and j<len(C):         #morphism condition below:         
            a=a*(theta(RI,I)(C[j][0]*C[j][1])==theta(RI,I)(C[j][0])*theta(RI,I)(C[j][1]))
            j=j+1
        if a:
            A2=A2+[I]
    return A2

#The next function is identical to "class_valid_involution" of Program 8.1.
#However, since theta has been modified, we need to rewrite the function accordingly.

def classes_valid_involution2(P,L,N):
    G=PermutationGroup(L)
    H=PermutationGroup(N)
    M=H._elements
    P2=[]
    k=len(L)
    if L!=N:
        M=The_Automorphisms(L,M)
    while P!=[]:
        I=P[0]
        RI=tab(I,[G.identity])
        P.remove(P[0])
        a=True
        j=0
        while a==True and j<len(P2):
            RP2=tab(P2[j],[G.identity])
            LL=[]
            for i in range(0,k):
               LL=LL+[theta(RP2,P2[j])(L[i])]
            m1=0
            while a==True and m1<len(M):
                m2=0
                while a==True and m2<len(M):
                    LP=[]
                    Q=M[m1]*M[m2]**-1
                    if (Q in G):
                        if theta(RI,I)(Q)==Q**-1:
                            for l in range(0,k):
                                LP=LP+[M[m2]**-1*theta(RI,I)(M[m1]*L[l]*M[m1]**-1)*M[m2]]
                            a=a*(LP!=LL)
                    m2=m2+1
                m1=m1+1
            j=j+1
        if a:
            P2=P2+[I]
    return P2

#L is a family of generators of G, N a family of generators of H,
#A and B are the two valid involutions that we want to compare
#(they are given by a basis of G). The variable r is the cardinal
#that we want for the group G tilde. The next program will construct the list P.
#Let P[i] be an element of the list P; the group G tilde will be generated by G and P[i].

def finding_G_tilde (L,N,A,B,r):
    l=len(L)
    H=PermutationGroup(N)
    G=PermutationGroup(L)
    N=G._elements
    n=len(N)
    h2=H._elements
    m=len(h2)
    P=[]
    Ra=tab(A,[H.identity])
    Rb=tab(B,[H.identity])
    HH=[]
    for k in range(0,n):                        #We construct the list HH
        if theta(Rb,B)(N[k])==N[k]**-1:         #of the elements h_1*h_2**-1 
            HH=HH+[N[k]]                        #as in Proposition 3.24.
    f=len(HH)
    for i in range(0,m):
        for j in range(0,f):
            h1=HH[j]*h2[i]
            b=True
            for x in range(0,l):                    #we search for h1 and h2 that
                left=theta(Rb,B)(h1*L[x]*h1**-1)    #verified Proposition 3.24.
                right=h2[i]*theta(Ra,A)(L[x])*h2[i]**-1
                b=b*(left==right)
            if b:
                K=PermutationGroup(L+[h2[i]])        #We construct G tilde.
                if (K.order()==r):
                    P=P+[h2[i]]
    return P

#The next function is a realization in Python of the group F tilde from [30, Section 2, n°5].

def F():
    u=Permutation(63)
    v=Permutation(63)
    w=Permutation(63)
    t1=Permutation(63)
    t2=Permutation(63)
    t3=Permutation(63)
    for i in range(0,61,4):
        u=u*Permutation(i,i+1,i+2,i+3)
    for j in range(0,4):
        for k in range(0,4):
            v=v*Permutation(k+16*j,k+16*j+4,k+16*j+8,k+16*j+12)
    for r in range(0,4):
        for s in range(0,4):
            w=w*Permutation(r+4*s,r+4*s+16,r+4*s+32,r+4*s+48)
    for x in range(0,4):
        for y in range(0,4):
            for z in range(y+1,4):
                t1=t1*Permutation(y+4*z+16*x,z+4*y+16*x)
                t2=t2*Permutation(x+4*z+16*y,x+4*y+16*z)
    L=list(range(16,64))
    while L!=[]:
        e=L[0]//16
        p=(L[0]%16)//4
        q=((L[0]%16)%4)
        t3=t3*Permutation(q+4*p+16*e,((q-e)%4)+((p-e)%4)*4+16*(4-e))
        L.remove(L[0])
        L.remove(((q-e)%4)+((p-e)%4)*4+16*(4-e))
    return [u,v,w,t1,t2,t3]
