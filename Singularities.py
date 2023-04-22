from sympy.combinatorics.perm_groups import PermutationGroup
from sympy.combinatorics.permutations import Permutation
from Program8_1 import surfaces_fixes
from Program8_1 import theta

#The next function will be use to compute the numbers k_6 and k_4 from Lemmas 4.11
#and 4.12. The arguments of the function are n which can be 6 or 4, L a list of generators
#of G and g an element of G. The list K will contain all elements g_i (modulo inverse)
#of order n such that g is in <g_i>.


def k(n,L,g):
    G=PermutationGroup(L)
    M=G._elements
    K=[]
    m=len(M)
    for i in range(0,m):
        if M[i].order()==n and not(M[i]**-1 in K):   #We consider only the elements modulo
            H=PermutationGroup([M[i],g])                #inverse.
            if H.is_cyclic:                             #We test if g is in <g_i>.
                K=K+[M[i]]
    return K


#The next function computes the set of orbits S_{g1,g2}/<g1> defined in Reamrk 4.17.
#It is denoted Sg in the program. The list L is a family of generators of G.
#T is a permutation which induces theta by conjugation; g1 and g2 are two elements in G.


def S(L,T,g1,g2):
    G=PermutationGroup(L)
    M=G._elements           #We search in M the elements that go in Sg
    Sg=[]
    o=g1.order()
    while M!=[]:            
        s=M[0]
        if s**-1*theta(g2,T)*s==g1 or s**-1*theta(g2,T)*s==g1**-1:
            Sg=Sg+[s]               #We test the condition to be in Sg (see Reamrk 4.17).
        for i in range(0,o):
            if s*g1**i in M:                #We only consider a representative for each
                M.remove(s*g1**i)           #orbits under the action of <g1>.
    return Sg

#For convenient reason, we set the function t for the cardinal of Sg as in Lemma 4.18.


def t(L,T,g1,g2):
    return len(S(L,T,g1,g2))


#The next function returns the number of specific fixed points on S^2 which are not
#of the form (x,s(x)) as explained in Lemma 4.18. We just follow the fomulas given 
#in Lemma 4.18.


def N(L,g,T):
    tl=t(L,T,g,g)           #tl is t(g) in Lemma 4.18.
    o=g.order()
    G=PermutationGroup(L)
    M=G._elements
    if o==6:                
        return 2*(2-tl)
    if o==4:
        return 4*(4-tl)
    if o==3:
        K=k(6,L,g)
        k6=len(K)
        R=0
        for i in range(0,k6):
            for j in range(i+1,k6):
                R=R+2*(2-t(L,T,K[i],K[j]))+2*(2-t(L,T,K[j],K[i]))
        I=(6-2*k6)*(6+2*k6-tl)+R
        return I
    if o==2:
        K6=k(6,L,g)
        K4=k(4,L,g)
        k6=len(K6)
        k4=len(K4)
        R6=0
        R4=0
        for i in range(0,k6):
            for j in range(i+1,k6):
                R6=R6+2*(2-t(L,T,K6[i],K6[j]))+2*(2-t(L,T,K6[j],K6[i]))
        for i in range(0,k4):
            for j in range(i+1,k4):
                R4=R4+4*(4-t(L,T,K4[i],K4[j]))+4*(4-t(L,T,K4[j],K4[i]))
        I=(8-2*k6-4*k4)*(8+2*k6+4*k4-tl)+R6+R4+16*k6*k4
        return I


#Now the idea is to provide all the sets given in (24) to compute the formulas of 
#Proposition 4.33, 4.35 and 4.36. The list S in argument of the function will be   
#S_{g1,g2}; it is an argument to avoid to recompute S_{g1,g2} at each uses. The next 
#function computes the lists S_{g1,g2}^+ and S_{g1,g2}^- from Notation 4.30. The argument   
#"plus" can be True or False. The function returns S_{g1,g2}^+ if plus==True and returns
#S_{g1,g2}^- if plus==False.   


def S_PlusMinus(T,g1,g,S,plus):
    o=g1.order()
    Splus=[]
    Sminus=[]
    H=PermutationGroup([g])
    for i in range(0,len(S)):
        a=True
        j=0
        s=S[i]
        while j<o and a==True:
            v=s*g1**j
            if theta(v,T)*v in H:       #We test the condition to be in S_{g1,g2}^+
                a=False                 #a=False if S[i] is in S_{g1,g2}^+
                Splus=Splus+[S[i]]
            j=j+1
        if a==True:                     #If S[i] is not in S_{g1,g2}^+, S[i] goes in 
            Sminus=Sminus+[S[i]]        #S_{g1,g2}^-.
    if plus==True:
        return Splus
    else:
        return Sminus


#The list S in argument of the next function will be S_{g1,g2}^+.        
#The next function computes the lists S_{g1,g2}^{+,c} and S_{g1,g2}^{+,nc} 
#from Notation 4.30. The argument "c" can be True or False. The function  
#returns S_{g1,g2}^{+,c} if c==True and return S_{g1,g2}^{+,nc} if c==False.

            
def S_c(T,S,g,c):
    Sc=[]
    Snc=[]
    for i in range(0,len(S)):
        if theta(g,T)*S[i]==S[i]*g:  #We check the condition to be in S_{g1,g2}^{+,c}.
            Sc=Sc+[S[i]]
        else:
            Snc=Snc+[S[i]]
    if c==True:
        return Sc
    else:
        return Snc


#As usual, the argument F of the function will be the list of elements sent to their
#inverses by theta. The argument S of the next function will be S_{g1,g2}^{+,c} or
#S_{g1,g2}^{+,nc}. Then the function will return S intersected with Fg or S setminus Fg.
#Fg is defined in Notation 4.30. The argument "f" can be True or False. The function  
#returns S intersected with Fg if f==True and returns S minus Fg if f==False.
    

def SF(T,S,F,g1,f):
  Sf=[]
  Snf=[]
  o=g1.order()
  for i in range(0,len(S)):
      a=True
      j=0
      s=S[i]
      while j<o and a==True:
          v=s*(g1**j)
          if v in F:            #We test the condition to be in Fg.
              a=False
              Sf=Sf+[S[i]]
          j=j+1
      if a==True:
          Snf=Snf+[S[i]]
  if f==True:
      return Sf
  else:
      return Snf
        
#The argument Sp of the next functions a8, B4 and B6 will be Sg^+.
#The argument n is the cardinal of G.
#We just follows the formulas form Proposition 4.33. The next functions provide 
#the contribution to the singularities of one element g.


def a8(L,T,g,Sp,F,n):
    if g.order()==4:
        return 16*len(SF(T,S_c(T,Sp,g,True),F,g,False))/n
    else:
        return 0

def B4(L,T,g,Sp,F,n):
    if g.order()==4:
        return 16*len(SF(T,S_c(T,Sp,g,False),F,g,False))/n
    else:
        return 0

def B6(L,T,g,Sp,F,n):
    if g.order()==6:
        return 12*len(SF(T,S_c(T,Sp,g,False),F,g,False))/n
    else:
        return 0


#The argument St of the next functions will be Sg and the argument Sp will be Sg^+.
#We follow the formulas from Propositions 4.34 and 4.35.

def a6(L,T,g,St,Sp,F,n):
    I=0
    if g.order()==6:
       I=I+6*len(S_PlusMinus(T,g,g,St,False))/n
       I=I+3*N(L,g,T)/n
       return I
    elif g.order()==3:
        K=k(6,L,g)
        k6=len(K)
        I=3*(6-2*k6)*len(SF(T,S_c(T,Sp,g,True),F,g,False))/n
        for i in range(0,k6):
            for j in range(i+1,k6):
                Sij=S_PlusMinus(T,K[i],g,S(L,T,K[i],K[j]),True)     #We compute S_{K[i],K[j]}^+
                Sji=S_PlusMinus(T,K[j],g,S(L,T,K[j],K[i]),True)
                I=I+6*len(SF(T,S_c(T,Sij,g,True),F,K[i],False))/n
                I=I+6*len(SF(T,S_c(T,Sji,g,True),F,K[j],False))/n
        return I
    else:
        return 0
    
def a4(L,T,g,St,Sp,F,n):
    I=0
    if g.order()==4:
       I=I+8*len(S_PlusMinus(T,g,g,St,False))/n
       I=I+2*N(L,g,T)/n
       return I
    elif g.order()==2:
        K6=k(6,L,g)
        K4=k(4,L,g)
        k6=len(K6)
        k4=len(K4)
        I=2*(8-2*k6-4*k4)*len(SF(T,S_c(T,Sp,g,True),F,g,False))/n
        for i in range(0,k6):
            for j in range(i+1,k6):
                Sij=S_PlusMinus(T,K6[i],g,S(L,T,K6[i],K6[j]),True)
                Sji=S_PlusMinus(T,K6[j],g,S(L,T,K6[j],K6[i]),True)
                I=I+4*len(SF(T,S_c(T,Sij,g,True),F,K6[i],False))/n
                I=I+4*len(SF(T,S_c(T,Sji,g,True),F,K6[j],False))/n
        for i in range(0,k4):
            for j in range(i+1,k4):
                Sij=S_PlusMinus(T,K4[i],g,S(L,T,K4[i],K4[j]),True)
                Sji=S_PlusMinus(T,K4[j],g,S(L,T,K4[j],K4[i]),True)
                I=I+8*len(SF(T,S_c(T,Sij,g,True),F,K4[i],False))/n
                I=I+8*len(SF(T,S_c(T,Sji,g,True),F,K4[j],False))/n
        return I
    else:
        return 0

def a3(L,T,g,St,Sp,F,n):
    I=0
    if g.order()==6:
       I=48*len(SF(T,S_c(T,Sp,g,True),F,g,True))/n
       return I
    elif g.order()==3:
        K=k(6,L,g)
        k6=len(K)
        I=3*N(L,g,T)/(2*n)
        I=I+3*(6-2*k6)*len(S_PlusMinus(T,g,g,St,False))/(2*n)
        I=I+6*(6-2*k6)*len(SF(T,S_c(T,Sp,g,True),F,g,True))/n
        for i in range(0,k6):
            for j in range(i+1,k6):
                Sij=S(L,T,K[i],K[j])
                Sji=S(L,T,K[j],K[i])
                Splusij=S_PlusMinus(T,K[i],g,Sij,True)
                Splusji=S_PlusMinus(T,K[j],g,Sji,True)
                I=I+12*len(SF(T,S_c(T,Splusij,g,True),F,K[i],True))/n
                I=I+12*len(SF(T,S_c(T,Splusji,g,True),F,K[j],True))/n
                I=I+3*len(S_PlusMinus(T,K[i],g,Sij,False))/n
                I=I+3*len(S_PlusMinus(T,K[j],g,Sji,False))/n        
        return I
    else:
        return 0
    
def a2(L,T,g,St,Sp,F,n):
    I=0
    if g.order()==6:
        I=12*len(SF(T,S_c(T,Sp,g,False),F,g,True))/n
        return I
    elif g.order()==4:
       I=64*len(SF(T,S_c(T,Sp,g,True),F,g,True))/n
       return I
    elif g.order()==2:
        K6=k(6,L,g)
        K4=k(4,L,g)
        k6=len(K6)
        k4=len(K4)
        I=N(L,g,T)/n
        I=I+(8-2*k6-4*k4)*len(S_PlusMinus(T,g,g,St,False))/n
        for i in range(0,k6):
            for j in range(i+1,k6):
                Sij=S(L,T,K6[i],K6[j])
                Sji=S(L,T,K6[j],K6[i])
                I=I+2*len(S_PlusMinus(T,K6[i],g,Sij,False))/n
                I=I+2*len(S_PlusMinus(T,K6[j],g,Sji,False))/n
        for i in range(0,k4):
            for j in range(i+1,k4):
                Sij=S(L,T,K4[i],K4[j])
                Sji=S(L,T,K4[j],K4[i])
                I=I+4*len(S_PlusMinus(T,K4[i],g,Sij,False))/n
                I=I+4*len(S_PlusMinus(T,K4[j],g,Sji,False))/n        
        return I
    else:
        return 0

#We compine all our previous computations in a global function
#which provides all the singularities. It retruns the list
#a=[a2,a3,a4,a6,a8,b4,b6] (see Notation 4.27).
    

def singularities(L,T):
    G=PermutationGroup(L)
    n=G.order()
    M=G._elements
    a=[0,0,0,0,0,0,0]                   
    M.remove(G.identity)
    F=surfaces_fixes(L,T)
    while M!=[]:                            #We are going to compute the contribution 
        g=M[0]                              #to the singularities of each g in G.
        St=S(L,T,g,g)                       #St is the list Sg
        Sp=S_PlusMinus(T,g,g,St,True)       #Sp is the list Sg^+
        a[0]=a[0]+a2(L,T,g,St,Sp,F,n)
        a[1]=a[1]+a3(L,T,g,St,Sp,F,n)
        a[2]=a[2]+a4(L,T,g,St,Sp,F,n)
        a[3]=a[3]+a6(L,T,g,St,Sp,F,n)
        a[4]=a[4]+a8(L,T,g,Sp,F,n)
        a[5]=a[5]+B4(L,T,g,Sp,F,n)
        a[6]=a[6]+B6(L,T,g,Sp,F,n)
        M.remove(g)
        if g.order()!=2:                    #g and g**-1 have the same specific fixed points;
            M.remove(g**-1)                 #we remove g**-1 to avoid counting the 
    return a                                #singularities twice.
