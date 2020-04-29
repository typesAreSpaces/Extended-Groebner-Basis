from sage.rings.polynomial.toy_buchberger              import spol, LCM, LM, LT
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field                         import QQ
from copy                                              import deepcopy
from itertools                                         import combinations
from collections                                       import deque, OrderedDict
from StringIO                                          import StringIO

class FamilyEntry:
    def __init__(self, initial_map, basis):
        self.basis = basis
        self.map = deepcopy(initial_map)
        if(self.map == {}):
            for element in basis:
                self.map[element] = 0

    def __getitem__(self, key):
        return self.map[key]

    def __setitem__(self, key, value):
        self.map[key] = value

    def __add__(self, other):
        new = FamilyEntry({}, self.basis)
        for key in self.map:
            new[key] = self[key] + other[key]
        return new

    def __mul__(self, polynomial):
        new = FamilyEntry({}, self.basis)
        for key in self.map:
            new[key] = polynomial * self.map[key]
        return new

    def __str__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Basis Element: {}\nMultiplier: {}\n".format(repr(key), repr(value)))
        ans = output.getvalue()
        output.close()
        return ans

    def __repr__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Basis Element: {}\nMultiplier: {}\n".format(repr(key), repr(value)))
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
    def __init__(self, basis):
        self.map = {}
        for element in basis:
            new_entry = {}
            for element_ in basis:
                if(element == element_):
                    new_entry[element_] = 1
                else:
                    new_entry[element_] = 0
            self.map[element] = FamilyEntry(new_entry, basis)
            self.original_basis = new_entry.keys()

    def __getitem__(self, key):
        return self.map[key]

    def __setitem__(self, key, value):
        self.map[key] = value

    def __delitem__(self, key):
        del self.map[key]

    def __str__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Polynomial: {}\nCoefficients:\n{}".format(repr(key), repr(value)))
        ans = output.getvalue()
        output.close()
        return ans 

    def __repr__(self):
        output = StringIO()
        for key, value in self.map.items():
            output.write("Polynomial: {}\nCoefficients:\n{}".format(repr(key), repr(value)))
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

    def originalBasis(self):
        return self.original_basis

def push_row(M, row):
    return matrix(M.rows() + [row])

def insert_row(M, k, row):
    return matrix(M.rows()[:k] + [row] + M.rows()[k:])

def delete_row(M, k):
    return matrix(M.rows()[:k] + M.rows()[(k+1):])

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
    G_ = FamilyIndexedPolynomials(original_polys)
    B = list(combinations(polys, 2))
    while B:
        (g1, g2) = B.pop()
        (m1, m2) = spolCoeffs(g1, g2, R)
        g = m1*g1 - m2*g2
        (coeffs, residue) = redPol(g, G, R)
        if(residue != 0):
            # -----------------------------------------------------------------------
            G_[residue]= FamilyEntry({}, original_polys)  
            for indexing_polynomial in coeffs:
                G_[residue] += G_[indexing_polynomial] * (-coeffs[indexing_polynomial])
            G_[residue] += G_[g1] * m1 + G_[g2] * (-m2)
            # -----------------------------------------------------------------------
            for element in G:
                B.append((element, residue))
            G.append(residue)
    return (G, G_)

def checkRedundantPolyGroebner(poly, polys, R):
    poly = R(poly)
    lead_monomial = LM(poly)
    for elem in polys:
        elem = R(elem)
        curr_lead_monomial = LM(elem)
        if(R.monomial_divides(curr_lead_monomial, lead_monomial)):
            return False
    return True

def existsReduciblePoly(polys, familyCoeffs, R):
    num_elements = len(polys)
    while(num_elements):
        poly = polys.pop() 
        poly_entry = familyCoeffs[poly]
        del familyCoeffs[poly]
        (coeffs, r) = redPol(poly, polys, R)
        if (r != poly):
            # print( "This was reducible modulo polys. poly: {} and r: {}".format(poly, r))
            return (True, coeffs, poly_entry, poly, r)
        polys.appendleft(poly)
        familyCoeffs[poly] = poly_entry
        num_elements -= 1
    return (False, None, None, None, None)

def reduceBasis(original_basis, basis, familyCoeffs, R):
    basis_ = deque(basis)
    # print( "Before\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs))
    (termination_condition, coeffs_poly, poly_entry, poly, residue) = existsReduciblePoly(basis_, familyCoeffs, R)
    while(termination_condition):
        if(residue != 0):
            new_entry = FamilyEntry({}, original_basis)
            for indexing_polynomial in coeffs_poly:
                new_entry += familyCoeffs[indexing_polynomial] * (-coeffs_poly[indexing_polynomial])
            new_entry += poly_entry 
            familyCoeffs[residue] = new_entry
            basis_.appendleft(residue)
        (termination_condition, coeffs_poly, poly_entry, poly, residue) = existsReduciblePoly(basis_, familyCoeffs, R)

    num_elements = len(basis_)
    index = 0
    while (index < num_elements):
        current_poly = R(basis_[index])
        leading_coeff = current_poly.lc()
        if(leading_coeff != 1):
            basis_[index] = (1 / leading_coeff) * current_poly 
            familyCoeffs[basis_[index]] = familyCoeffs[current_poly] * (1 / leading_coeff)
            del familyCoeffs[current_poly]
        index += 1
    # print( "After\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs))
    return (basis_, familyCoeffs)

def redExtGroebnerBasis(original_polys, polys, R):
    (gbasis, familyCoeffs) = extGroebnerBasis(original_polys, polys, R)
    print "Gbasis: {}".format(gbasis)
    M1 = familyCoeffs.toMatrix()
    # print "Family Coeffs:\n{}\n".format(familyCoeffs)
    # KEEP: working here
    print "Original basis elements: {}".format(familyCoeffs.originalBasis())
    hmm1 = [R(x) for x in M1*vector(familyCoeffs.originalBasis())]
    hmm2 = [R(x) for x in vector(gbasis)]
    hmm1.sort()
    hmm2.sort()
    print hmm1
    print hmm2 

    gbasis_ = []
    while (gbasis):
        poly = gbasis.pop()
        if checkRedundantPolyGroebner(poly, gbasis, R) and checkRedundantPolyGroebner(poly, gbasis_, R):
            gbasis_.append(poly)
        else:
            del familyCoeffs[poly]

    (a, b) = reduceBasis(original_polys, gbasis_, familyCoeffs, R)

    M2 = b.toMatrix()

    return (a, b)

# ---------------------------------------------------------------------------------------
# TESTS
def testReduce():
    R = PolynomialRing(QQ, 3, 'xyz', order='lex')
    (x, y, z) = R.gens()
    original_basis = [y^2-z,x^2+y^5+y*z-1,z^2-x]
    G_ = FamilyIndexedPolynomials(original_basis)
    basis = deque(original_basis)
    reduceBasis(original_basis, basis, G_, R)

def testRedExtGroebner():
    R1 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    R2 = PolynomialRing(QQ, 3, 'xyz')
    (x, y, z) = R2.gens()
    # basis = [y^2-x,x^2-y*z-1,z^2-x]
    basis = [y^2-x,x^2-y*z-1, z^3 -2*y^3 + 3*x^2]
    (groebner_basis, coeffs) = redExtGroebnerBasis(basis, R2)
    print( groebner_basis)
    for key in coeffs.map:
        value = coeffs.map[key].getPolynomial()
        print( "Expected: {}\nReality : {}\nCorrect?: {}".format(key, value, key == value))

# ---------------------------------------------------------------------------------------



# ---------------------------------------------------------------------------------------

def existsReducible(polys, R):
    num_elements = len(polys)
    while(num_elements):
        poly = polys.pop() 
        (coeffs, r) = redPol(poly, polys, R)
        if (r != poly):
            # print( "This was reducible modulo polys. poly: {} and r: {}".format(poly, r))
            return (True, poly, r)
        polys.appendleft(poly)
        num_elements -= 1
    return (False, None, None)

def interReduce(original_basis, R):
    original_basis_ = deepcopy(original_basis)
    basis_ = deque(original_basis)
    inverse_lift_map = {}
    # print( "Before\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs))
    (termination_condition, poly, residue) = existsReducible(basis_, R)
    while(termination_condition):
        if(residue != 0):
            while(not(poly in original_basis_)):
                poly = inverse_lift_map[poly]
            inverse_lift_map[residue] = poly
            basis_.appendleft(residue)
        (termination_condition, poly, residue) = existsReducible(basis_, R)

    num_elements = len(basis_)
    index = 0
    while (index < num_elements):
        current_poly = R(basis_[index])
        leading_coeff = current_poly.lc()
        if(leading_coeff != 1):
            basis_[index] = (1 / leading_coeff) * current_poly 
            if(current_poly in inverse_lift_map):
                inverse_lift_map[basis_[index]] = inverse_lift_map.pop(current_poly)
        index += 1
    # print( "After\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs))
    return (basis_, inverse_lift_map)

def liftFamilyCoeffs(familyCoeffs, truncation_map):
    inverse_lift_map = {}
    for key, value in truncation_map.items():
        if (key != value):
            for poly, family_entry in familyCoeffs.map.items():
                family_entry[value] = family_entry.pop(key)
                familyCoeffs[poly] = family_entry
                if(family_entry[value] != 0):
                    lift_poly = poly + family_entry[value] * (value - key)
                    familyCoeffs[lift_poly] = familyCoeffs.pop(poly)
                    inverse_lift_map[lift_poly] = poly
                else:
                    inverse_lift_map[poly] = poly
    return inverse_lift_map

def truncatePolynomial(poly, R1, R2):
    leading_monomial = R1(poly).lm()
    result = leading_monomial * poly.monomial_coefficient(leading_monomial)
    poly = R2(poly)
    for monomial in poly.monomials():
        if(monomial == leading_monomial):
            break
        result += monomial * poly.monomial_coefficient(monomial)
    return result

def basisConversion(basis, R1, R2):
    print "Step 1:"
    basis_1 = [R1(x) for x in basis]
    I = ideal(basis_1)
    F = I.groebner_basis()
    num_elements = len(F)
    M = matrix.identity(num_elements)
    M_ = matrix.identity(num_elements)
    print "Groebner basis wrt R1: {}".format(F)

    print "Step 2:"
    F_t = [truncatePolynomial(poly, R1, R2) for poly in F]
    print "F_t: {}".format(F_t)
    (F_, inverse_lift_map) = interReduce(F_t, R2)
    print "F_: {}".format(F_)
    print "Inverse Lift Map: {}".format(inverse_lift_map)
    pass

def testBasisConversion():
    R1 = PolynomialRing(QQ, 3, 'xyz', order='deglex')
    R2 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    (x, y, z) = R1.gens()
    basis1 = [y^2-x,x^2-y*z-1,z^2-x]
    print( "--- Basis: {} From deglex x > y > z to lex x > y > z".format(basis1))
    # basisConversion(basis1, R1, R2)
    original_basis = deepcopy(basis1)
    gb, M = redExtGroebnerBasis(original_basis, basis1, R2)

    # print "Input basis: {}\nGroebner basis: {}\n".format(original_basis, gb)
    # print "Original basis: {}".format(M.toMatrix()\vector(M.originalBasis()))
    # print "Original basis: {}".format(vector(M.originalBasis())*M.toMatrix())
    # gb2 = [R2(x) for x in gb] 
    # print Ideal(gb2).basis_is_groebner()

if __name__ == "__main__":

    # testProfKapurAlgorithm()
    # test1ProfKapurAlgorithm()
    # test2ProfKapurAlgorithm()
    # test3ProfKapurAlgorithm()
    # testHandExampleProfKapurAlgorithm()
    testBasisConversion()
    
