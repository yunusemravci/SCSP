︠da0cf32a-a34c-4287-bfa6-2f3f1a3e1a92︠
# Laurent polynomial rings create value with L_ and y_
# Laurent matrix normalized to y_ variables

def createLPR(d):
    LPR = LaurentPolynomialRing(QQ, [ "L_"+str(i) for i in range(d)])
    return LPR

def createYPR(d):
    return LaurentPolynomialRing(QQ,[ "y_"+str(i) for i in range(d)])

#with getSubs function substituted variables in y variables using;
#x1 = y1 , x2 = y2y1^l .. xm=ymy1^(l^(m-1)) rule
def getSubs(XPR,YPR, d, l):
    subsdict = {}
    subsdict[XPR.gen(0)] = YPR.gen(0)
    for i in range(1,d):
        subsdict[XPR.gen(i)] = YPR.gen(i)*YPR.gen(0)^(l^(i))
    
    return subsdict
#----------------------
def listToMatrix(list):
    MM = []
    for i in range(len(list[0])):
        MM.append(list[0][i])
        
    MM = matrix(list[1],MM)
    return MM
#---------------------------
def normalize(M,sub,YPR):
    MM = []
    for row in M.rows():
        tmp = []
        for e in row:
            
            tmp.append(e.subs(sub))
        MM.append(tmp)
    
    MM = matrix(YPR,MM)
    return MM

#each element of matrix is normalized with choosing a sufficiently large l
def LaurentNormalization(M, LPR, YPR, l):
    sub = getSubs(LPR,YPR,len(LPR.gens()), l)
    
    M = normalize(M,sub,YPR)
    return M
#----------------------------------------------------

# Creation of D matrix
# leading:
# p : output number, row number
def createMatrix_D(leading, p, YPR):
    D = [[0 for x in range(p)] for y in range(p)]
    D[0][0] = 1/leading
    D[1][1] = leading

    for i in range(2,p):
        for j in range(2,p):
            if(i==j):
                D[i][j] = 1

    return Matrix(YPR, D)
#-----------
# term:
# V: vector that multiply with left matrix E(term)
def elementaryMatrix(term,n, YPR):

    E = [[0 for x in range(n)] for y in range(n)]

    E[n-1][0] =  term
    for i in range(n):
        for j in range(n):
            if(i==j):
                E[i][j] = 1
    EM = Matrix(YPR, E)
    return EM

# To find parameter of elemantary matrix according degree rule
# pp: pth input vector
# YPR: Symbols over polynomial rings
# degree: current degree of components which will be assumed as parameter
def ElementaryParameter(pp,YPR,degree):
    ep = (-1) * pp.coefficient(YPR.gen(0)^degree)* YPR.gen(0)^degree
    return ep

#------------------
# find of the rows least degree variable of YPR.gen(0)
# monomialList: Second components monomial list
# YPR: Symbols over polynomial rings
def LeastDegree(monomialList, YPR):

    minDegree = monomialList[0].degree(YPR.gen(0))

    for i in range(len(monomialList)):
        if(monomialList[i].degree(YPR.gen(0)) < minDegree):
            minDegree = monomialList[i].degree(YPR.gen(0))

    return minDegree
#--------------------
# Elementary reduction algorithm to find polynomial variable vector
# from the headings that is 9.3 description of causal conversion algorithm
# elemenetary reduction using elementary matrix with laurent polynomial entries,
# product of elementary matrices and production with D matrix give transfer matrix T
# M: Input Matrix
# YPR: Symbols over polynomial rings
# n: system input output number p
def ElementaryReduction(M,YPR,n,startRow):

    D = createMatrix_D(M[0][0].monomials()[0],n, YPR)
    print "\n D: \n", D
    
    M = D * M 
    
    for j in range(1,M.nrows()):
        leastDegree = LeastDegree(M[j][0].monomials(),YPR)
        if leastDegree >= 0:
            continue
        tempLeastDegree = -(leastDegree)

        for i in range(tempLeastDegree+1):
        #print "Current M:\n", M
        #print "\n Elementary parameter: \n", ElementaryParameter(M[1][0],YPR,leastDegree)

            E = elementaryMatrix(ElementaryParameter(M[j][0],YPR,leastDegree),n, YPR)
            M = E * M
            D = D * E
            leastDegree = leastDegree + 1


    return D,M
#-----------------------
# Mtrx: 
def GaussElimination(Mtrx,YPR):

    rowNumber = Mtrx.nrows()
    colNumber = Mtrx.ncols()

    for i in range(rowNumber):
        for k in range(rowNumber):
            if(k>i):
                factor = Mtrx[i][k] / Mtrx[k][k]
                for j in range(colNumber):
                    print "mlt: ",factor * Mtrx[k][j]
                    a = Mtrx[k,j]
                    b = Mtrx[i,j]

                    print a - b * factor
                    #print temp

    return Mtrx
#-----------------------
# M:
# YPR:
def CausalConversion(M,YPR):

    leastDegree = LeastDegree(M[1][0].monomials(),YPR)

    NewRing = FractionField(PolynomialRing(QQ, [ str(i) for i in YPR.gens()] + [ "w" ]))

    l =  (-1)* min(flatten([[ v[1] for v in p.exponents() ] for p in M.list()]))
    subsdict = {}
    subsdict[NewRing.gen(0)] = NewRing.gen(YPR.ngens()) * ( prod([ NewRing.gen(i) for i in range(1,YPR.ngens())]))^l

    print subsdict

    L = M.list()
    L = [ NewRing(str(e)).subs(subsdict) for e in L]

    return [L, NewRing]
#------------------------------------------------------------------
#
# L:
# NR:
def UnimodularityCheck(L, NR):
    R = PolynomialRing(QQ, [ str(i) for i in NR.gens()] )
    
    I = R * [ R(str(i)) for i in L ]
    #print "Groebner Result: ",I.groebner_basis()
    if (I.groebner_basis() == 1):
        return True
    else:
        return False
#-----------------------------------------------------------------------------
#
# causalCol:
# n:
# WPR:
def ElementaryReductionPolynomial(causalCol,n,WPR):
    #causalColMatrix = [[0 for x in range(1)] for y in range(n)]
    causalColMatrix =  matrix(n,causalCol)
    
    E = ElementaryMatrixPolynomial(causalColMatrix,n, 0,WPR)
    causalColMatrix = E * causalColMatrix
    for i in range(1,n):
        NewE = ElementaryMatrixPolynomial(causalColMatrix,n,i,WPR)
        causalColMatrix = NewE * causalColMatrix
        E = E * NewE

    print "\n Polynomail elementary matrix production -> U: \n",E
    print "\n Applied ERA to A column vector: \n", causalColMatrix
    return E
#------------------------------------------------------------
#
# causalCol:
# n:
# index:
# WPR:
def ElementaryMatrixPolynomial(causalCol,n, index,WPR):
    E = [[0 for x in range(n)] for y in range(n)]
    if(index == 0):
        E[0][0] =  1/causalCol[0][0]
    else:
        E[index][0] = -causalCol[index][0]
    for i in range(n):
        for j in range(n):
            if(i==j):
                if(i == 0 and j == 0):
                    if(E[i][j] == 0):
                        E[i][j] = 1
                else:
                    E[i][j] = 1
    EM = Matrix(WPR, E)
    return EM
#--------------------------------------------------------------------
#
#
#
def createInverse_S(UT, startCoord,n):
    S = [[0 for x in range(n)] for y in range(n)]
    
    for i in range(n):
        for j in range(n):
            if(i == j):
                S[i][j] = 1
    
    for i in range(startCoord,n):
        for j in range(startCoord,n):
            S[i][j] = UT[i-startCoord][j-startCoord]

    return matrix(n,S)
#---------------------------------------------------------------------

#---------------------------------------------------------------------
#
# M:
# LPR,YPR:
# l
def GeneralSystemsQP(M,LPR,YPR,l):
    Mtranspose = M.transpose()

    for i in range(M.ncols()):
        Mcol = Mtranspose[i]
        temp = matrix(LPR, [[0 for x in range(1)] for y in range(M.nrows()-i)])

        for j in range(i,M.nrows()):
            temp[j-i,0] = Mcol[j]
        print "\n--------------------------------\n Column vector of A: \n", temp
        MtempLN = LaurentNormalization(temp, LPR,YPR,-2)
        print  "\nLaurent Normalization result: \n", MtempLN

        T,MtempERA_LP =ElementaryReduction(MtempLN,YPR,M.nrows()-i,0)
        print "\nElementary Reduction to obtain polynomial and T matrix: \n", MtempERA_LP
        print "\nTransformation matrix T: \n", T
        print "\nv^ = Tv: \n", T*MtempLN
        MlistRing = CausalConversion(MtempERA_LP, YPR)

        print "\nCausal Conversion Result for current column: \n", MlistRing[0]

        U = ElementaryReductionPolynomial(MlistRing[0],M.nrows()-i, MlistRing[1])
        UT = U*T
        print "\nU^ = UT -> Inverse laurent polynomail matrix: \n",UT
        print "\nSi with expanded UT matrix: \n",createInverse_S(UT,i,M.nrows())

        

    #return Mtemp
#------------------------------
LPR = createLPR(2)
y_0,y_1 = LPR.gens()

YPR =  createYPR(2)
y_0,y_1 = LPR.gens()


M = matrix(YPR, [[y_1^(-1),y_0*y_1^(-1)+y_0],[y_0*y_1^(-2)+1,y_1+y_0*y_1],[y_0^-3*y_1^(-2),y_1^-1 + y_0]])
if(M.nrows() < 2):
    print "Input size should be greater than or equals to 2!\n"
else:
    print "* Input of the system: \n", M
    x = GeneralSystemsQP(M,LPR,YPR,1)

︡90b60aa7-51e0-4d7a-aebc-290fee1b639d︡{"stdout":"* Input of the system: \n[          y_1^-1 y_0 + y_0*y_1^-1]\n[  1 + y_0*y_1^-2    y_0*y_1 + y_1]\n[   y_0^-3*y_1^-2     y_0 + y_1^-1]\n\n--------------------------------\n Column vector of A: \n[        L_1^-1]\n[1 + L_0*L_1^-2]\n[ L_0^-3*L_1^-2]\n\nLaurent Normalization result: \n[    y_0^2*y_1^-1]\n[y_0^5*y_1^-2 + 1]\n[      y_0*y_1^-2]\n\n D: \n[  y_0^-2*y_1            0            0]\n[           0 y_0^2*y_1^-1            0]\n[           0            0            1]\n\nElementary Reduction to obtain polynomial and T matrix: \n[                          1]\n[y_0^7*y_1^-3 + y_0^2*y_1^-1]\n[                 y_0*y_1^-2]\n\nTransformation matrix T: \n[  y_0^-2*y_1            0            0]\n[           0 y_0^2*y_1^-1            0]\n[           0            0            1]\n\nv^ = Tv: \n[                          1]\n[y_0^7*y_1^-3 + y_0^2*y_1^-1]\n[                 y_0*y_1^-2]\n{y_0: y_1^3*w}\n\nCausal Conversion Result for current column: \n[1, y_1^18*w^7 + y_1^5*w^2, y_1*w]\n\n Polynomail elementary matrix production -> U: \n[                      1                       0                       0]\n[-y_1^18*w^7 - y_1^5*w^2                       1                       0]\n[                 -y_1*w                       0                       1]\n\n Applied ERA to A column vector: \n[1]\n[0]\n[0]\n\nU^ = UT -> Inverse laurent polynomail matrix: \n[                      y_1/y_0^2                               0                               0]\n[(-y_1^19*w^7 - y_1^6*w^2)/y_0^2                       y_0^2/y_1                               0]\n[               (-y_1^2*w)/y_0^2                               0                               1]\n\nSi with expanded UT matrix: \n[                      y_1/y_0^2                               0                               0]\n[(-y_1^19*w^7 - y_1^6*w^2)/y_0^2                       y_0^2/y_1                               0]\n[               (-y_1^2*w)/y_0^2                               0                               1]\n\n--------------------------------\n Column vector of A: \n[L_0*L_1 + L_1]\n[ L_0 + L_1^-1]\n\nLaurent Normalization result: \n[y_0^-1*y_1 + y_0^-2*y_1]\n[     y_0^2*y_1^-1 + y_0]\n\n D: \n[y_0^2*y_1^-1            0]\n[           0   y_0^-2*y_1]\n\nElementary Reduction to obtain polynomial and T matrix: \n[      y_0 + 1]\n[y_0*y_1 - y_0]\n\nTransformation matrix T: \n[                            y_0^2*y_1^-1                                        0]\n[y_0^-2*y_1^2 - y_0^-2*y_1 - y_0^-3*y_1^2                               y_0^-2*y_1]\n\nv^ = Tv: \n[                                                                   y_0 + 1]\n[1 + y_0^-1*y_1 + y_0^-3*y_1^3 - y_0^-3*y_1^2 - y_0^-4*y_1^2 - y_0^-5*y_1^3]\n{y_0: w}\n\nCausal Conversion Result for current column: \n[w + 1, y_1*w - w]\n\n Polynomail elementary matrix production -> U: \n[ 1/(w + 1)          0]\n[-y_1*w + w          1]\n\n Applied ERA to A column vector: \n[1]\n[0]\n\nU^ = UT -> Inverse laurent polynomail matrix: \n[                                                 y_0^2/(y_1*w + y_1)                                                                    0]\n[(-y_0^5*y_1*w + y_0^5*w + y_0*y_1^3 - y_0*y_1^2 - y_1^3)/(y_0^3*y_1)                                                            y_1/y_0^2]\n\nSi with expanded UT matrix: \n[                                                                   1                                                                    0                                                                    0]\n[                                                                   0                                                  y_0^2/(y_1*w + y_1)                                                                    0]\n[                                                                   0 (-y_0^5*y_1*w + y_0^5*w + y_0*y_1^3 - y_0*y_1^2 - y_1^3)/(y_0^3*y_1)                                                            y_1/y_0^2]\n"}︡{"done":true}︡
︠f9cf9301-44c4-471e-adc5-1a6668a9fbces︠

LPR = createLPR(3)
y_0,y_1,y_2 = LPR.gens()

YPR =  createYPR(3)
y_0,y_1,y_2 = LPR.gens()

T = matrix(YPR, [[1-y_0*y_1 - 2*y_2 - 4*y_0*y_2 - y_0^2*y_2 - 2*y_0*y_1*y_2 + 2*y_0^2*y_1^2*y_2 - 2*y_0*y_2^2 - 2*y_0^2*y_2^2 + 2*y_0^2*y_1*y_2^2],[2+4*y_0 + y_0^2 + 2*y_0*y_1 - 2*y_0^2*y_1^2 + 2*y_0*y_2+2*y_0^2*y_2 - 2*y_0^2*y_1*y_2],[1+2*y_0 + y_0*y_1 - y_0^2*y_1^2 + y_0*y_2 + y_0^2*y_2 - y_0^2*y_1*y_2],[2 + y_0 + y_1 - y_0*y_1^2 + y_2 - y_0*y_1*y_2]])

print "input: \n",T
︡7777b305-4f04-4b11-b077-e6028898b34b︡{"stdout":"input: \n[2*y_0^2*y_1^2*y_2 + 2*y_0^2*y_1*y_2^2 - 2*y_0^2*y_2^2 - y_0^2*y_2 - 2*y_0*y_1*y_2 - 2*y_0*y_2^2 - y_0*y_1 - 4*y_0*y_2 - 2*y_2 + 1]\n[                                       -2*y_0^2*y_1^2 - 2*y_0^2*y_1*y_2 + 2*y_0^2*y_2 + y_0^2 + 2*y_0*y_1 + 2*y_0*y_2 + 4*y_0 + 2]\n[                                                         -y_0^2*y_1^2 - y_0^2*y_1*y_2 + y_0^2*y_2 + y_0*y_1 + y_0*y_2 + 2*y_0 + 1]\n[                                                                                   -y_0*y_1^2 - y_0*y_1*y_2 + y_0 + y_1 + y_2 + 2]\n"}︡{"done":true}︡
︠3e21cc8f-ff56-45a5-acf7-8e9f0bdf1c7as︠
Mtranspose = T.transpose()

for i in range(T.ncols()):
    Mcol = Mtranspose[i]
    temp = matrix(LPR, [[0 for x in range(1)] for y in range(T.nrows()-i)])

    for j in range(i,T.nrows()):
        
        temp[j-i,0] = Mcol[j]

    MtempLN = LaurentNormalization(temp, LPR,YPR,2)
    print  "\nLaurent result: \n", MtempLN
        
    T,MtempERA_LP =ElementaryReduction(MtempLN,YPR,T.nrows()-i,0)
    print "M ERA to N.LP: \n", MtempERA_LP
    MlistRing = CausalConversion(MtempERA_LP, YPR)
    
    print "\nCausal Result for current column: \n", MlistRing[0]

    ElementaryReductionPolynomial(MlistRing[0],T.nrows()-i, MlistRing[1])
︡66c0959b-ad46-4730-a77b-84ad2aa623c5︡{"stdout":"\nLaurent result: \n[2*y_0^12*y_1*y_2^2 + 2*y_0^10*y_1^2*y_2 - 2*y_0^10*y_2^2 - 2*y_0^9*y_2^2 - 2*y_0^7*y_1*y_2 - y_0^6*y_2 - 4*y_0^5*y_2 - 2*y_0^4*y_2 - y_0^3*y_1 + 1]\n[                                                    -2*y_0^8*y_1*y_2 - 2*y_0^6*y_1^2 + 2*y_0^6*y_2 + 2*y_0^5*y_2 + 2*y_0^3*y_1 + y_0^2 + 4*y_0 + 2]\n[                                                                      -y_0^8*y_1*y_2 - y_0^6*y_1^2 + y_0^6*y_2 + y_0^5*y_2 + y_0^3*y_1 + 2*y_0 + 1]\n[                                                                                    -y_0^7*y_1*y_2 - y_0^5*y_1^2 + y_0^4*y_2 + y_0^2*y_1 + y_0 + 2]\n\n D: \n[y_0^-12*y_1^-1*y_2^-2                     0                     0                     0]\n[                    0      y_0^12*y_1*y_2^2                     0                     0]\n[                    0                     0                     1                     0]\n[                    0                     0                     0                     1]\nM ERA to N.LP: \n[2 + 2*y_0^-2*y_1*y_2^-1 - 2*y_0^-2*y_1^-1 - 2*y_0^-3*y_1^-1 - 2*y_0^-5*y_2^-1 - y_0^-6*y_1^-1*y_2^-1 - 4*y_0^-7*y_1^-1*y_2^-1 - 2*y_0^-8*y_1^-1*y_2^-1 - y_0^-9*y_2^-2 + y_0^-12*y_1^-1*y_2^-2]\n[                    -2*y_0^20*y_1^2*y_2^3 - 2*y_0^18*y_1^3*y_2^2 + 2*y_0^18*y_1*y_2^3 + 2*y_0^17*y_1*y_2^3 + 2*y_0^15*y_1^2*y_2^2 + y_0^14*y_1*y_2^2 + 4*y_0^13*y_1*y_2^2 + 2*y_0^12*y_1*y_2^2]\n[                                                                                                                  -y_0^8*y_1*y_2 - y_0^6*y_1^2 + y_0^6*y_2 + y_0^5*y_2 + y_0^3*y_1 + 2*y_0 + 1]\n[                                                                                                                                -y_0^7*y_1*y_2 - y_0^5*y_1^2 + y_0^4*y_2 + y_0^2*y_1 + y_0 + 2]\n{y_0: y_1*y_2*w}\n\nCausal Result for current column: \n[(2*y_1^13*y_2^14*w^12 + 2*y_1^12*y_2^11*w^10 - 2*y_1^10*y_2^12*w^10 - 2*y_1^9*y_2^11*w^9 - 2*y_1^8*y_2^8*w^7 - y_1^6*y_2^7*w^6 - 4*y_1^5*y_2^6*w^5 - 2*y_1^4*y_2^5*w^4 - y_1^4*y_2^3*w^3 + 1)/(y_1^13*y_2^14*w^12), -2*y_1^22*y_2^23*w^20 - 2*y_1^21*y_2^20*w^18 + 2*y_1^19*y_2^21*w^18 + 2*y_1^18*y_2^20*w^17 + 2*y_1^17*y_2^17*w^15 + y_1^15*y_2^16*w^14 + 4*y_1^14*y_2^15*w^13 + 2*y_1^13*y_2^14*w^12, -y_1^9*y_2^9*w^8 - y_1^8*y_2^6*w^6 + y_1^6*y_2^7*w^6 + y_1^5*y_2^6*w^5 + y_1^4*y_2^3*w^3 + 2*y_1*y_2*w + 1, -y_1^8*y_2^8*w^7 - y_1^7*y_2^5*w^5 + y_1^4*y_2^5*w^4 + y_1^3*y_2^2*w^2 + y_1*y_2*w + 2]\n\n Polynomail elementary matrix production -> U: \n[y_1^13*y_2^14*w^12/(2*y_1^13*y_2^14*w^12 + 2*y_1^12*y_2^11*w^10 - 2*y_1^10*y_2^12*w^10 - 2*y_1^9*y_2^11*w^9 - 2*y_1^8*y_2^8*w^7 - y_1^6*y_2^7*w^6 - 4*y_1^5*y_2^6*w^5 - 2*y_1^4*y_2^5*w^4 - y_1^4*y_2^3*w^3 + 1)                                                                                                                                                                                                                0                                                                                                                                                                                                                0                                                                                                                                                                                                                0]\n[                             2*y_1^22*y_2^23*w^20 + 2*y_1^21*y_2^20*w^18 - 2*y_1^19*y_2^21*w^18 - 2*y_1^18*y_2^20*w^17 - 2*y_1^17*y_2^17*w^15 - y_1^15*y_2^16*w^14 - 4*y_1^14*y_2^15*w^13 - 2*y_1^13*y_2^14*w^12                                                                                                                                                                                                                1                                                                                                                                                                                                                0                                                                                                                                                                                                                0]\n[                                                                                                       y_1^9*y_2^9*w^8 + y_1^8*y_2^6*w^6 - y_1^6*y_2^7*w^6 - y_1^5*y_2^6*w^5 - y_1^4*y_2^3*w^3 - 2*y_1*y_2*w - 1                                                                                                                                                                                                                0                                                                                                                                                                                                                1                                                                                                                                                                                                                0]\n[                                                                                                                           y_1^8*y_2^8*w^7 + y_1^7*y_2^5*w^5 - y_1^4*y_2^5*w^4 - y_1^3*y_2^2*w^2 - y_1*y_2*w - 2                                                                                                                                                                                                                0                                                                                                                                                                                                                0                                                                                                                                                                                                                1]"}︡{"stdout":"\n\n Applied ERA to A column vector: \n[1]\n[0]\n[0]\n[0]\n[y_1^13*y_2^14*w^12/(2*y_1^13*y_2^14*w^12 + 2*y_1^12*y_2^11*w^10 - 2*y_1^10*y_2^12*w^10 - 2*y_1^9*y_2^11*w^9 - 2*y_1^8*y_2^8*w^7 - y_1^6*y_2^7*w^6 - 4*y_1^5*y_2^6*w^5 - 2*y_1^4*y_2^5*w^4 - y_1^4*y_2^3*w^3 + 1)                                                                                                                                                                                                                0                                                                                                                                                                                                                0                                                                                                                                                                                                                0]\n[                             2*y_1^22*y_2^23*w^20 + 2*y_1^21*y_2^20*w^18 - 2*y_1^19*y_2^21*w^18 - 2*y_1^18*y_2^20*w^17 - 2*y_1^17*y_2^17*w^15 - y_1^15*y_2^16*w^14 - 4*y_1^14*y_2^15*w^13 - 2*y_1^13*y_2^14*w^12                                                                                                                                                                                                                1                                                                                                                                                                                                                0                                                                                                                                                                                                                0]\n[                                                                                                       y_1^9*y_2^9*w^8 + y_1^8*y_2^6*w^6 - y_1^6*y_2^7*w^6 - y_1^5*y_2^6*w^5 - y_1^4*y_2^3*w^3 - 2*y_1*y_2*w - 1                                                                                                                                                                                                                0                                                                                                                                                                                                                1                                                                                                                                                                                                                0]\n[                                                                                                                           y_1^8*y_2^8*w^7 + y_1^7*y_2^5*w^5 - y_1^4*y_2^5*w^4 - y_1^3*y_2^2*w^2 - y_1*y_2*w - 2                                                                                                                                                                                                                0                                                                                                                                                                                                                0                                                                                                                                                                                                                1]\n"}︡{"done":true}︡
︠2b3bd1ea-7229-48bc-af1f-2baa3661a93fs︠

︡050f6fc4-dc83-4ecd-b4d9-9a9dd43405f9︡{"done":true}︡









