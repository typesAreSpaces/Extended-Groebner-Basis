from sage.rings.polynomial.toy_buchberger              import spol, LCM, LM, LT
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field                         import QQ
from copy                                              import deepcopy
from itertools                                         import combinations
from collections                                       import deque

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
        return "{}".format(self.map)

    def __repr__(self):
        return "{}".format(self.map)

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

    def __getitem__(self, key):
        return self.map[key]

    def __setitem__(self, key, value):
        self.map[key] = value

    def __delitem__(self, key):
        del self.map[key]

    def __str__(self):
        return "{}".format(self.map)

    def __repr__(self):
        return "{}".format(self.map)

    def pop(self, key):
        return self.map.pop(key)

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
    _map = {}
    for element in basis:
        _map[element] = 0
    _residue = 0

    num_elements = len(basis) 
    p = R(polynomial)
    while(p != 0):
        index = 0
        division_ocurred = False 
        leading_poly = LT(p)
        while(index < num_elements and not(division_ocurred)):
            current_divisor = R(basis[index])
            leading_divisor = LT(current_divisor)
            (q, r) = leading_poly.quo_rem(leading_divisor)
            if(r == 0):
                _map[current_divisor] += q
                p -= q*current_divisor
                division_ocurred = True
            else:
                index += 1
        if not(division_ocurred):
            _residue += leading_poly 
            p -= leading_poly 
    return (_map, _residue)

def extGroebnerBasis(polys, R):
    original_polys = deepcopy(polys)
    G = polys
    G_ = FamilyIndexedPolynomials(original_polys)
    B = list(combinations(polys, 2))
    while B:
        (g1, g2) = B.pop()
        # print "Processing {} and {}".format(g1, g2)
        (m1, m2) = spolCoeffs(g1, g2, R)
        g = m1*g1 - m2*g2
        (coeffs, residue) = redPol(g, G, R)
        if(residue != 0):
            # print "We need to add {}. Original: {} Coeffs: {}".format(residue, g, coeffs)
            for element in G:
                B.append((element, residue))
            new_entry = FamilyEntry({}, original_polys)  
            for indexing_polynomial in coeffs:
                new_entry += G_[indexing_polynomial] * (-coeffs[indexing_polynomial])
            new_entry += G_[g1] * m1 + G_[g2] * (-m2)
            G_[residue] = new_entry
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
            # print "This was reducible modulo polys. poly: {} and r: {}".format(poly, r)
            return (True, coeffs, poly_entry, poly, r)
        polys.appendleft(poly)
        familyCoeffs[poly] = poly_entry
        num_elements -= 1
    return (False, None, None, None, None)

def reduceBasis(original_basis, basis, familyCoeffs, R):
    basis_ = deque(basis)
    # print "Before\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs)
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
    # print "After\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs)
    return (basis_, familyCoeffs)

def redExtGroebnerBasis(polys, R):
    original_polys = deepcopy(polys)
    (gbasis, familyCoeffs) = extGroebnerBasis(polys, R)

    gbasis_ = []
    while (gbasis):
        poly = gbasis.pop()
        if checkRedundantPolyGroebner(poly, gbasis, R) and checkRedundantPolyGroebner(poly, gbasis_, R):
            gbasis_.append(poly)
        else:
            del familyCoeffs[poly]

    return reduceBasis(original_polys, gbasis_, familyCoeffs, R)

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
    print groebner_basis
    for key in coeffs.map:
        value = coeffs.map[key].getPolynomial()
        print "Expected: {}\nReality : {}\nCorrect?: {}".format(key, value, key == value)

# ---------------------------------------------------------------------------------------

if __name__ == "__main__":

    # testReduce()
    # testRedExtGroebner()
    pass
