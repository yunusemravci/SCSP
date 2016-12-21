︠20dbc151-e23d-4b0c-9d6b-c7e4ee4edda5s︠
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
#--------------------------Elementary Reduction --------------------------

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
# M: Input Matrix
# YPR: Symbols over polynomial rings
# n: system input output number p
def ElementaryReduction(M,YPR,n):

    D = createMatrix_D(M[0][0].monomials()[0],n, YPR)

    print "\n D: \n", D

    M = D * M 

    leastDegree = LeastDegree(M[1][0].monomials(),YPR)

    tempLeastDegree = -(leastDegree)

    for i in range(tempLeastDegree+1):
        print "Current M:\n", M
        print "\n Elementary parameter: \n", ElementaryParameter(M[1][0],YPR,leastDegree)

        E = elementaryMatrix(ElementaryParameter(M[1][0],YPR,leastDegree),n, YPR)
        M = E * M

        leastDegree = leastDegree + 1


    return M
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

#------------------------------
def UnimodularityCheck(L, NR):
    R = PolynomialRing(QQ, [ str(i) for i in NR.gens()] )
    I = R * [ R(str(i)) for i in L ]
    if (I.groebner_basis() == 1):
        return True
    else:
        return False

#---------------------------- Main -------------------------------------
LPR = createLPR(2)
y_0,y_1 = LPR.gens()

YPR =  createYPR(2)
y_0,y_1 = LPR.gens()


M = matrix(LPR, [[y_1^(-1)+y_0*y_1^(-1)+y_0],[y_0*y_1^(-2)+1+y_1+y_0*y_1]])

print M
M = LaurentNormalization(M,LPR,YPR,1)

print "\nNormalize M:\n", M

M = ElementaryReduction(M,YPR,2)
print "\n Elementary reduction result:\n", M

R=  CausalConversion(M, YPR)
L=R[0]
NR=R[1]
print "\n Causal Conversion:\n", L

print "\n Unimodular:",  UnimodularityCheck(L,NR)

︡d356f4b6-3f68-43ba-8bef-246965c515d2︡{"stdout":"[     L_0 + L_0*L_1^-1 + L_1^-1]\n[L_0*L_1 + L_1 + 1 + L_0*L_1^-2]\n"}︡{"stdout":"\nNormalize M:\n[           y_0 + y_1^-1 + y_0^-1*y_1^-1]\n[y_0^2*y_1 + y_0*y_1 + 1 + y_0^-1*y_1^-2]\n"}︡{"stdout":"\n D: \n[      y_0*y_1             0]\n[            0 y_0^-1*y_1^-1]\nCurrent M:\n[                    y_0^2*y_1 + y_0 + 1]\n[y_0 + 1 + y_0^-1*y_1^-1 + y_0^-2*y_1^-3]\n\n Elementary parameter: \n-y_0^-2*y_1^-3\nCurrent M:\n[                             y_0^2*y_1 + y_0 + 1]\n[y_0 + 1 - y_1^-2 + y_0^-1*y_1^-1 - y_0^-1*y_1^-3]\n\n Elementary parameter: \n-y_0^-1*y_1^-1 + y_0^-1*y_1^-3\nCurrent M:\n[                      y_0^2*y_1 + y_0 + 1]\n[1 + y_0*y_1^-2 - y_1^-1 - y_1^-2 + y_1^-3]\n\n Elementary parameter: \n-1 - y_0*y_1^-2 + y_1^-1 + y_1^-2 - y_1^-3\n"}︡{"stdout":"\n Elementary reduction result:\n[                                                                                           y_0^2*y_1 + y_0 + 1]\n[-y_0^2*y_1 - y_0^3*y_1^-1 + y_0^2 + y_0^2*y_1^-1 - y_0 - 2*y_0^2*y_1^-2 + y_0*y_1^-1 + y_0*y_1^-2 - y_0*y_1^-3]\n"}︡{"stdout":"{y_0: y_1^3*w}\n"}︡{"stdout":"\n Causal Conversion:\n[y_1^7*w^2 + y_1^3*w + 1, -y_1^8*w^3 - y_1^7*w^2 + y_1^6*w^2 + y_1^5*w^2 - 2*y_1^4*w^2 - y_1^3*w + y_1^2*w + y_1*w - w]\n"}︡{"stdout":"\n Unimodular: False\n"}︡{"done":true}︡









