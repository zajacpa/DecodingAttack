#####################################################################
#
# Demonstration of the decoding attack on SIMON-32, 
# see 
# P. Zajac: Upper bounds on the complexity of algebraic 
#    cryptanalysis of ciphers with a low multiplicative complexity
#
# (C) 2016, Pavol Zajac
#
# Can be used for research and education, 
# with attribution and citation of the article if applicable.
#
#####################################################################

## Simon left-hand side matrix
def getSimonMatrix4r():
    M=matrix(GF(2),32,3*32)
    
    #F1 part
    for j in range(16):
       #in1: 
       M[(j-8)%16,3*j+0] = 1  #S8 k0
       #in2: 
       M[(j-1)%16,3*j+1] = 1  #S1 k0
       #out 
       M[(j-2)%16,3*j+2] = 1  #S2 k0
       M[(j+3)%16,3*j+2] = 1  #S-3 k0
       M[(j+4)%16,3*j+2] = 1  #S-4 k0
       M[16+(j+6)%16,3*j+2] = 1  #S-6 k1
       M[16+(j+8)%16,3*j+2] = 1  #S-8 k1
     
    #F2 part
    for j in range(16):
       #in1: 
       M[(j-5)%16,3*16+3*j+0] = 1  #S8 S-3 k0
       M[(j-4)%16,3*16+3*j+0] = 1  #S8 S-4 k0
       M[16+(j-2)%16,3*16+3*j+0] = 1  #S8 S-6 k1
       M[16+(j+0)%16,3*16+3*j+0] = 1  #S8 S-8 k1
       #in2: 
       M[(j+2)%16,3*16+3*j+1] = 1  #S1 S-3 k0
       M[(j+3)%16,3*16+3*j+1] = 1  #S1 S-4 k0
       M[16+(j+5)%16,3*16+3*j+1] = 1  #S1 S-6 k1
       M[16+(j+7)%16,3*16+3*j+1] = 1  #S1 S-8 k1

       #out 
       M[(j+1)%16,3*16+3*j+2] = 1  #S-1 k0
       M[(j+2)%16,3*16+3*j+2] = 1  #S-2 k0
       M[16+(j+3)%16,3*16+3*j+2] = 1  #S-3 k1
       M[16+(j+6)%16,3*16+3*j+2] = 1  #S-6 k1
       
    return M
##########################################

## Simon right-hand side sets
def getSimonConstant(j):
    if j < 16:  #for first part
        #if (j == 1) or (j == 13) or (j == 14):
        #0 is index in y1, y2 = 0
        if j in [1, 13, 14, 0]:
            return [0,0,0]
        else:
            return [0,0,1]
    else:        
        j -= 16
        c1 = 0 if (j-8)%16 in [1,13,14,0] else 1 
        c2 = 0 if (j-1)%16 in [1,13,14,0] else 1 
        c3 = 1 if j in [0,1,3,15,2] else 0
        return [c1,c2,c3]

#S is a set of rhs, c is a hex constant
def addBitConstant(S, c):
    S2 = copy(S)
    for i in range(S2.nrows()):
        for j in range(S2.ncols()):
            S2[i,j] = S2[i,j]+c[j]
    return S2

def rot(x, i=1):
    return ((x << i) & 0xffff ) | (x >> (16 - i))

def bit(x, i):
    return ((x >> i) & 1 )

def get_y_const(y1, y2):
    #print y1, y2
    
    y1_F_y2 = (y1.__xor__(rot(y2,8)&rot(y2,1))).__xor__(rot(y2,2))
    consts = []
    #F1 - constant y1+F(y2) is added to result of AND
    for i in range(16):
        consts += [ [0,0,bit(y1_F_y2,i)] ]
    #F2 - y1+F(y2) is added to input 1 rotated by 8
    #   - y1+F(y2) is added to input 2 rotated by 1
    #   - y1+F(y2) is added to output rotated by 2
    #   - y2 is added to output
    in1 = rot(y1_F_y2,8)
    in2 = rot(y1_F_y2,1)
    out = y2.__xor__(rot(y1_F_y2,2))
    for i in range(16):
        consts += [ [bit(in1,i),bit(in2,i),bit(out,i)] ]
    return consts

def getSimonConstants4r(y1, y2):
    SxAND=matrix(GF(2),[[0,0,0],[0,1,0],[1,0,0],[1,1,1]])
    without_y = [addBitConstant(SxAND,getSimonConstant(i)) for i in range(0,32)]
    y_const = get_y_const(y1, y2)
    with_y = [addBitConstant(without_y[i],y_const[i]) for i in range(0,32)]
    return block_diagonal_matrix(with_y,subdivide=False)
##########################################

## MRHS transformation to decoding

#M - LHS matrix
#S - RHS (block) matrix
#n - variables, m - blocks, k - block size
def getMatrixU( M, S, n, m, k ):
    #get systematic matrix + PCM
    C=LinearCode(M)
    G=C.generator_matrix_systematic()
    H=C.parity_check_matrix()

    #compute V
    R = S*H.transpose()

    #construct T to transform V to U
    T0 = matrix(GF(2), k-1, k)
    for i in range(k-1):
        T0[i,0] = 1
        T0[i,i+1] = 1
    
    T1 = matrix(GF(2), 1, k)
    T1[0,0] = 1
    
    # m blocks T0
    T2 = block_diagonal_matrix([T0 for i in range(0,m)],subdivide=False)
    
    # m blocks T1
    T3 = block_matrix(1,m,[T1 for i in range(0,m)],subdivide=False)

    T = block_matrix(2,1,[T3,T2])

    #final parity check matrix, first row is syndrome
    Q=(T*R)
    
    return Q
##########################################

## Final check of solution
def extract_solution(sols, up, S):
    #sols := [ sol ]
    # sol := (ix1, ix2, count, syndrome)
    #up   := [rev]
    #rev  := (block, solnum, row)
    posx = [0] * 32
    s = up[3*32][2]
    for sol in sols:
        if (sol[0] != '.'):
            posx[ up[sol[0]][0] ] = up[sol[0]][1]
            s += up[sol[0]][2]          
        if (sol[1] != '.'):
            posx[ up[sol[1]][0] ] = up[sol[1]][1]          
            s += up[sol[1]][2]
        for ix, val in enumerate(sol[3]):
            if val == 1:
                posx[ up[ix][0] ] = up[ix][1] 
                s += up[ix][2]

        print sol
        print s
        print posx
        rhs = [] 
        for i in range(32):
            rhs += list(S[4*i+posx[i]][3*i:3*i+3])
        print rhs
##########################################


## Decoding algorithm      
def hw(vec):
    return sum(1 for x in vec if x==1)

def final_check_conflicts(lst):
    syndrome = lst[3] 
    pos1 = lst[0] 
    pos2 = lst[1]
    
    #syndrome cannot have 1 in positions x[0] and x[1]
    if pos1 != '.' and (syndrome[pos1%32] == 1 or syndrome[pos1%32+32] == 1): return False
    if pos2 != '.' and (syndrome[pos2%32] == 1 or syndrome[pos2%32+32] == 1): return False
    return True   
              
#adapted version of Lee-Brickel decoding
def decoding(y1 = 0, y2 = 0, max_try = 10000):
    M=getSimonMatrix4r()
    S=getSimonConstants4r(y1,y2)        
    U=getMatrixU(M, S, 32, 32, 4)

    u=U.rows()[0]

    count = 0
    while count < max_try:
        
        count += 1
        
        #apply random permutation to blocks, and separate columns 
        P=Permutations(32).random_element()
        
        up = [None] * (3*32+1)
        for i in range(32):
            R = Permutations(3).random_element()
            for j in range(3):
                up[32*j + i] = (P[i]-1, R[j], U.rows()[1+(P[i]-1)*3+R[j]-1])
        up[3*32] = ('.', '.', u)
           
        #create echelon form, last block has each vector from a different block
        UP = matrix(GF(2),map(lambda x: x[2], up)).transpose().echelon_form().transpose()
        if UP[0:64,0:64] != identity_matrix(64):
            #print count
            continue
    
        #create a list of potential solutions including at most 2 vectors from the last block
        l1 = [[i,UP.rows()[i]] for i in range(64,96)]
        uhat = UP.rows()[96]
        
        lst = [('.','.',0,uhat)]+[(x[0],'.',1,uhat+x[1]) for x in l1]+[(x[0],y[0],2,uhat+x[1]+y[1]) for x in l1 for y in l1 if y[0] > x[0]]

        #check special position 64 
        special   = filter(lambda x: x[3][64] == 0, lst)   
         
        #filter by weight, 
        weight_ok = filter(lambda x: hw(x[3])+x[2] <= 32, special)
        # then by conflicts within the first two blocks, 
        no_conflicts12 = filter(lambda x: sum(1 if x[3][i]==1 and x[3][32+i]==1 else 0 for i in range(32)) < 1, weight_ok)
        # and finally conflicts with the chosen vectors from the last block
        no_conflicts = filter(final_check_conflicts, no_conflicts12)
              
        if len(no_conflicts) > 0: 
            #print UP.str()
            #print no_conflicts
            extract_solution(no_conflicts, up, S)
            
            return count
        
    return count
##########################################
    
#time results = [decoding(1,1) for i in range(100)]
#import random;
#time results = [decoding(Integer(random.randint(0,0x10000)),Integer(random.randint(0,0x10000)),1500) for i in range(100)]