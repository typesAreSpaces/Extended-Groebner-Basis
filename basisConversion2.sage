from sage.rings.polynomial.toy_buchberger              import spol, LCM, LM, LT
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field                         import QQ
from copy                                              import deepcopy
from itertools                                         import combinations
from collections                                       import deque, OrderedDict
from StringIO                                          import StringIO

def push_row(M, row):
    return matrix(M.rows() + [row])

def insert_row(M, k, row):
    return matrix(M.rows()[:k] + [row] + M.rows()[k:])

def delete_row(M, k):
    return matrix(M.rows()[:k] + M.rows()[(k+1):])

class FamilyEntry:
    def __init__(self, initial_map, basis):
        self.basis = basis
        self.map = deepcopy(initial_map)
        if(not bool(self.map)):
            for element in basis:
                self.map[element] = 0

    def __getitem__(self, key):
        return self.map[key]

    def __setitem__(self, key, value):
        self.map[key] = value

    def __add__(self, other):
        new = FamilyEntry(OrderedDict({}), self.basis)
        for key in self.map:
            new[key] = self[key] + other[key]
        return new

    def __mul__(self, polynomial):
        new = FamilyEntry(OrderedDict({}), self.basis)
        for key in self.map:
            new[key] = polynomial * self.map[key]
        return new

    def __str__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Basis Element: {}\nMultiplier: {}\n"\
                    .format(repr(key), repr(value)))
        ans = output.getvalue()
        output.close()
        return ans

    def __repr__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Basis Element: {}\nMultiplier: {}\n"\
                    .format(repr(key), repr(value)))
        ans = output.getvalue()
        output.close()
        return ans

    def __len__(self):
        return len(self.map)

    def getPolynomial(self):
        result = 0
        for indexing_polynomial in self.map:
            result += indexing_polynomial * self.map[indexing_polynomial]
        return result

    def pop(self, key):
        return self.map.pop(key)

class FamilyIndexedPolynomials: 
    def __init__(self, original_basis):
        self.original_basis = original_basis
        self.map = OrderedDict({})
        for element in original_basis:
            new_entry = OrderedDict({})
            for element_ in original_basis:
                if(element == element_):
                    new_entry[element_] = 1
                else:
                    new_entry[element_] = 0
            self.map[element] = FamilyEntry(new_entry, original_basis)

    def keyInit(self, key):
        self.map[key] = FamilyEntry(OrderedDict({}), self.original_basis)

    def __getitem__(self, key):
        return self.map[key]

    def __setitem__(self, key, value):
        self.map[key] = value

    def __delitem__(self, key):
        del self.map[key]

    def __str__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Polynomial: {}\nCoefficients:\n{}"\
                    .format(repr(key), repr(value)))
        ans = output.getvalue()
        output.close()
        return ans 

    def __repr__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Polynomial: {}\nCoefficients:\n{}"\
                    .format(repr(key), repr(value)))
        ans = output.getvalue()
        output.close()
        return ans 

    def pop(self, key):
        return self.map.pop(key)

    def toMatrix(self):
        rows = []
        for row in self.map.values():
            rows.append(row.map.values())
        return Matrix(rows)

def spolCoeffs(poly1, poly2, R):
    poly1 = R(poly1)
    poly2 = R(poly2)
    leading_monomial1 = LM(poly1)
    leading_monomial2 = LM(poly2)
    lcm_poly_1_2 = LCM(poly1, poly2)
    leading_coefficient1 = poly1.lc()
    leading_coefficient2 = poly2.lc()
    s1 = R.monomial_quotient(lcm_poly_1_2, leading_monomial1, coeff=True)
    s2 = R.monomial_quotient(lcm_poly_1_2, leading_monomial2, coeff=True)
    return (leading_coefficient2*s1, leading_coefficient1*s2)

def redPol(polynomial, basis, R):
    coefficients = { element : 0 for element in basis } 
    residue = 0

    num_elements = len(basis) 
    p = R(polynomial)
    while(p != 0):
        index = 0
        division_ocurred = False 
        current_leading_term = LT(p)
        while(index < num_elements and not(division_ocurred)):
            current_divisor = R(basis[index])
            leading_divisor = LT(current_divisor)
            (q, r) = current_leading_term.quo_rem(leading_divisor)
            if(r == 0):
                coefficients[current_divisor] += q
                p -= q*current_divisor
                division_ocurred = True
            else:
                index += 1
        if not(division_ocurred):
            residue += current_leading_term 
            p -= current_leading_term 

    return (coefficients, residue)

def extGroebnerBasis(original_polys, polys, R):
    G = polys
    family_coeffs = FamilyIndexedPolynomials(original_polys)
    B = list(combinations(polys, 2))
    while B:
        (g1, g2) = B.pop()
        (m1, m2) = spolCoeffs(g1, g2, R)
        g = m1*g1 - m2*g2
        (coeffs, residue) = redPol(g, G, R)
        if(residue != 0):
            print "Included S-polynomial of {} and {}: {}\nIts residue (i.e. mod GB of F_t): {}"\
                    "\nCoefficients of {} and {} respectively: {}, {}"\
                    .format(g1, g2, g, residue, g1, g2, m1, -m2)
            family_coeffs.keyInit(residue)
            for indexing_polynomial, coeff in coeffs.items():
                family_coeffs[residue] += family_coeffs[indexing_polynomial] * (-coeff)
            family_coeffs[residue] += family_coeffs[g1] * m1 + family_coeffs[g2] * (-m2)
            print "Coefficients from F_t for the residue:\n{}".format(family_coeffs[residue])
            for element in G:
                B.append((element, residue))
            G.append(residue)
    return (G, family_coeffs)

def checkRedundantPolyGroebner(poly, polys, R):
    poly = R(poly)
    lead_monomial = LM(poly)
    for elem in polys:
        elem = R(elem)
        curr_lead_monomial = LM(elem)
        if(R.monomial_divides(curr_lead_monomial, lead_monomial)):
            return False
    return True

def existsReduciblePoly(polys, family_coeffs, R):
    num_elements = len(polys)
    while(num_elements):
        poly = polys.pop() 
        poly_entry = family_coeffs[poly]
        del family_coeffs[poly]
        (coeffs, r) = redPol(poly, polys, R)
        # If the r and poly are different
        # then return poly, r, and 
        # the FamilyIndexedPolynomials data structure 
        # without poly
        if (r != poly):
            return (True, coeffs, poly_entry, poly, r)
        # Otherwise, reinsert poly back 
        # to the FamilyIndexedPolynomials
        # data structure
        polys.appendleft(poly)
        family_coeffs[poly] = poly_entry
        num_elements -= 1
    return (False, None, None, None, None)

def reduceBasis(original_basis, basis, family_coeffs, R):
    basis_ = deque(basis)
    print "\nCurrent gb of F_t after elimination of redundant terms: {}\n".format(basis_)
    while(True):
        (termination_condition, coeffs_poly, \
                poly_entry, poly, residue) = existsReduciblePoly(basis_, family_coeffs, R)
        if(not termination_condition):
            break
        print "Reduce Basis: This poly {} reduces to {}".format(poly, residue)
        if(residue != 0):
            family_coeffs.keyInit(residue)
            for indexing_polynomial, coeff in coeffs_poly.items():
                family_coeffs[residue] += family_coeffs[indexing_polynomial] * (-coeff)
            family_coeffs[residue] += poly_entry 
            print "Coefficients:\n{}".format(family_coeffs[residue])
            basis_.appendleft(residue)

    num_elements = len(basis_)
    index = 0
    while (index < num_elements):
        current_poly = R(basis_[index])
        leading_coeff = current_poly.lc()
        if(leading_coeff != 1):
            basis_[index] = (1 / leading_coeff) * current_poly 
            family_coeffs[basis_[index]] = family_coeffs[current_poly] * (1 / leading_coeff)
            del family_coeffs[current_poly]
        index += 1
    return basis_

def redExtGroebnerBasis(original_polys, polys, R):
    (gbasis, family_coeffs) = extGroebnerBasis(original_polys, polys, R)

    print "Current gb of F_t after completion: {}\n".format(gbasis)

    gbasis_ = []
    while (gbasis):
        poly = gbasis.pop()
        if checkRedundantPolyGroebner(poly, gbasis, R) \
                and checkRedundantPolyGroebner(poly, gbasis_, R):
            gbasis_.append(poly)
        else:
            print "Redundant polynomial in extended Groebner basis computation: {}".format(poly)
            del family_coeffs[poly]

    reduced_gb = reduceBasis(original_polys, gbasis_, family_coeffs, R)
    return (reduced_gb, family_coeffs) 

# ---------------------------------------------------------------------------------------
# TESTS
def testRedExtGroebner():
    R1 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    R2 = PolynomialRing(QQ, 3, 'xyz')
    (x, y, z) = R2.gens()
    # basis = [y^2-x,x^2-y*z-1,z^2-x]
    basis = [y^2-x,x^2-y*z-1, z^3 -2*y^3 + 3*x^2]
    
    original_basis = deepcopy(basis)
    (groebner_basis, coeffs) = redExtGroebnerBasis(original_basis, basis, R2)

    print(groebner_basis)
    for key in coeffs.map:
        value = coeffs.map[key].getPolynomial()
        print("Expected: {}\nReality : {}\nCorrect?: {}"\
                .format(key, value, key == value))
    M = coeffs.toMatrix()
    vec_gb1 = [R2(x) for x in M*vector(original_basis)]
    vec_gb2 = [R2(x) for x in vector(groebner_basis)]
    vec_gb1.sort()
    vec_gb2.sort()
    print "Test equivalence between groebner basis and matrix multiplication: {}"\
            .format(vec_gb1 == vec_gb2)

def composeGBTransformationsTest():
    R1 = PolynomialRing(QQ, 3, 'xyz', order='deglex')
    R2 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    R3 = PolynomialRing(QQ, 3, 'xyz', order='degrevlex')
    (x, y, z) = R1.gens()
    basis1 = [y^2-x,x^2-y*z-1,z^2-x]
    original_elements = deepcopy(basis1)
    (gb, coeffs) = redExtGroebnerBasis(original_elements, basis1, R2)
    M1 = coeffs.toMatrix()
    basis2 = list(gb)
    original_elements2 = deepcopy(basis2)
    (gb2, coeffs2) = redExtGroebnerBasis(original_elements2, basis2, R3)
    M2 = coeffs2.toMatrix()
    test1 = [R1(x) for x in gb2]
    test2 = [R1(x) for x in M2*M1*vector(original_elements)]
    test1.sort()
    test2.sort()
    print test1 == test2
# ---------------------------------------------------------------------------------------

# ---------------------------------------------------------------------------------------
# Prof Kapur Basis Conversion Algorithm 

def truncatePolynomial(poly, R1, R2):
    poly = R1(poly)
    leading_monomial = poly.lm()
    result = leading_monomial * poly.monomial_coefficient(leading_monomial)
    poly = R2(poly)
    for monomial in poly.monomials():
        if(monomial == leading_monomial):
            break
        result += monomial * poly.monomial_coefficient(monomial)
    return result

def reduceAndTruncateBasis(original_basis, basis, family_coeffs, R):
    basis_ = deque(basis)
    while(True):
        (termination_condition, coeffs_poly, \
                poly_entry, poly, residue) = existsReduciblePoly(basis_, family_coeffs, R)
        if(not termination_condition):
            break
        print "reduceBasis: Poly: {} residue: {}".format(poly, residue)
        if(residue != 0):
            family_coeffs.keyInit(residue)
            for indexing_polynomial, coeff in coeffs_poly.items():
                family_coeffs[residue] += family_coeffs[indexing_polynomial] * (-coeff)
            family_coeffs[residue] += poly_entry 
            basis_.appendleft(residue)

    num_elements = len(basis_)
    index = 0
    while (index < num_elements):
        current_poly = R(basis_[index])
        leading_coeff = current_poly.lc()
        if(leading_coeff != 1):
            basis_[index] = (1 / leading_coeff) * current_poly 
            family_coeffs[basis_[index]] = family_coeffs[current_poly] * (1 / leading_coeff)
            del family_coeffs[current_poly]
        index += 1
    return basis_

def basisConversion(basis, R1, R2):
    print "Step 1"
    basis_1 = [R1(x) for x in basis]
    I = ideal(basis_1)
    F = [poly for poly in I.groebner_basis()]
    num_elements = len(F)
    M = matrix.identity(num_elements)
    M_ = matrix.identity(num_elements)
    print "Groebner basis wrt R1: {}".format(F)
    F_t = [truncatePolynomial(poly, R1, R2) for poly in F]

    num_iter = 1

    while(True):
        print "\nIteration {}".format(num_iter)
        num_iter += 1
        
        # ---------------------------------------------------------------------------------------
        # TODO
        # Fix step 2

        # 2. $F_t = Tru(F) = [tru(f_1), \cdots, tru(f_{|G_{\grt_1}|})]^T$ be 
        # the
        # truncated vector for $F$. Interreduce $F_t$ by appropriately 
        # modifying
        # $M'$ and $M$, and recomputing the truncation of
        # $f$'s in $F^T$ as they get interreduced (this is very important) as
        # initial ideals \wrt \grt_2 and \grt_2 are appropriately kept track of

        print "\nStep 2" 

        original_elements = deepcopy(F_t)
        print "F_t before interreduce: {}".format(F_t)
        family_coeffs = FamilyIndexedPolynomials(original_elements)
        reduceAndTruncateBasis(original_elements, F_t, family_coeffs, R2)
        M_ = family_coeffs.toMatrix()
        print "F_t after interreduce: {}".format([poly for poly in M_*vector(original_elements)])
        print "Associated Interreduction Matrix:\n{}".format(M_)
        M = M_ * M

        print "F before update: {}".format(F)
        F = [poly for poly in M_ * vector(F)]
        print "F after update: {}".format(F)

        F_t = [truncatePolynomial(poly, R1, R2) for poly in F]
        print "F_t after truncate F: {}".format(F_t)
        # ---------------------------------------------------------------------------------------

        print "\nStep 3"
        original_F_t = deepcopy(F_t)
        (H, family_coeffs2) = redExtGroebnerBasis(original_F_t, F_t, R2)
        print "H: {}".format(list(H))

        print "\nStep 4"
        M_ = family_coeffs2.toMatrix()
        print "Matrix of multipliers:\n{}".format(M_)

        print "\nStep 5"
        G = [poly for poly in M_ * vector(F)]
        M = M_ * M
        print "G: {}".format(G)

        print "\nStep 6 and 7"
        h = M_*vector(original_F_t)
        assert len(h) == len(G)
        num_elements = len(h)
        index = 0
        repeat = False
        print "The h_j's: {}".format([poly for poly in h])
        print "The g_j's: {}".format(G)
        while(index < num_elements):
            g_j = R2(G[index])
            h_j = R2(h[index])
            if(g_j.lm() != h_j.lm()):
                print "These are the witness polynomials that "\
                        "prove G_s is not empty: g_j = {}, h_j = {}"\
                        .format(g_j, h_j)
                repeat = True
                break
            index += 1
        if(not repeat):
            print "Done"
            original_G = deepcopy(G)
            new_family_coeffs = FamilyIndexedPolynomials(original_G)
            gb = reduceBasis(original_G, G, new_family_coeffs, R2)
            return (list(gb), M)
        else:
            F = G
            F_t = [truncatePolynomial(poly, R1, R2) for poly in F]

def basisConversion2(basis, R1, R2):
    print "Step 1"
    basis_1 = [R1(x) for x in basis]
    I = ideal(basis_1)
    F = [poly for poly in I.groebner_basis()]
    F_original = deepcopy(F)
    num_elements = len(F)
    M = matrix.identity(num_elements)
    M_ = matrix.identity(num_elements)
    print "Groebner basis wrt R1: {}".format(F)
    F_t = [truncatePolynomial(poly, R1, R2) for poly in F]
    print "\nCurrent F: {}".format(F)
    print "Current F_t: {}".format(F_t)

    num_iter = 1

    while(True):
        print "\nIteration {}".format(num_iter)
        num_iter += 1
        
        print "\nStep 3 & 4"
        original_F_t = deepcopy(F_t)
        (H, family_coeffs2) = redExtGroebnerBasis(original_F_t, F_t, R2)
        M_ = family_coeffs2.toMatrix()
        print "Matrix of multipliers M':\n{}".format(M_)
        print "H (= M' * F_t): {}".format([poly for poly in M_ * vector(original_F_t)])

        print "\nStep 5"
        G = [poly for poly in M_ * vector(F)]
        M = M_ * M
        print "Matrix of multipliers M after update (i.e. M := M' * M):\n{}".format(M)
        print "G (= M' * F): {}".format(G)
        print "G_full (= M * F_original) {}".format([poly for poly in M * vector(F_original)])

        print "\nStep 6 and 7"
        h = M_*vector(original_F_t)
        assert len(h) == len(G)
        num_elements = len(h)
        index = 0
        repeat = False
        print "The h_j's: {}".format([poly for poly in h])
        print "The g_j's: {}".format(G)
        while(index < num_elements):
            g_j = R2(G[index])
            h_j = R2(h[index])
            if(g_j.lm() != h_j.lm()):
                print "These are the witness polynomials that "\
                        "prove G_s is not empty: g_j = {}, h_j = {}"\
                        .format(g_j, h_j)
                repeat = True
                break
            index += 1
        if(not repeat):
            print "Done"
            original_G = deepcopy(G)
            new_family_coeffs = FamilyIndexedPolynomials(original_G)
            gb = reduceBasis(original_G, G, new_family_coeffs, R2)
            return (list(gb), M)
        else:
            F = G
            F_t = [truncatePolynomial(poly, R1, R2) for poly in F]
            print "\nCurrent F: {}".format(F)
            print "Current F_t: {}".format(F_t)

def testBasisConversion():
    R1 = PolynomialRing(QQ, 3, 'xyz', order='deglex')
    R2 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    (x, y, z) = R2.gens()
    basis1 = [y^2-x,x^2-y*z-1,z^2-x]
    print("Basis: {} From {} {} to {} {}".\
            format(basis1, R1, R1.term_order(), R2, R2.term_order()))
    gb, M = basisConversion(basis1, R1, R2)
    print "Results:" 
    print "Groebner basis: {}".format(gb)
    print "Associated matrix:\n{}".format(M)
    print "Check if basis is Groebner basis: {}".format(Ideal(gb).basis_is_groebner())
    # print "Groebner basis computed by SageMath: {}".format(Ideal(basis1).groebner_basis())

def testBasisConversion2(R1, R2, basis1):
    print("Basis: {} From {} {} to {} {}".\
            format(basis1, R1, R1.term_order(), R2, R2.term_order()))
    gb, M = basisConversion2(basis1, R1, R2)
    print "Results:" 
    gb.sort()
    print "Groebner basis produced: {}".format(gb)
    print "Associated matrix:\n{}".format(M)
    print "Check if basis is Groebner basis: {}".format(Ideal(gb).basis_is_groebner())
    gb_sage = [poly for poly in Ideal(basis1).groebner_basis()]
    gb_sage.sort()
    print "Groebner basis computed by Sage: {}".format(gb_sage)
    print "Check if the produced gb is the same as the gb produced by Sage: {}".format(gb == gb_sage)
    # print "Groebner basis computed by SageMath: {}".format(Ideal(basis1).groebner_basis())

if __name__ == "__main__":

    R1 = PolynomialRing(QQ, 3, 'xyz', order='deglex')
    R2 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    (x, y, z) = R2.gens()

    # testRedExtGroebner()
    # composeGBTransformationsTest()
    # testBasisConversion()
    testBasisConversion2(R1, R2, [y^2-x,x^2-y*z-1,z^2-x])
