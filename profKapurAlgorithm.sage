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

def existsReducible(polys, R):
    num_elements = len(polys)
    while(num_elements):
        poly = polys.pop() 
        (coeffs, r) = redPol(poly, polys, R)
        if (r != poly):
            # print "This was reducible modulo polys. poly: {} and r: {}".format(poly, r)
            return (True, poly, r)
        polys.appendleft(poly)
        num_elements -= 1
    return (False, None, None)

def interReduce(original_basis, R):
    original_basis_ = deepcopy(original_basis)
    basis_ = deque(original_basis)
    inverse_lift_map = {}
    # print "Before\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs)
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
    # print "After\nbasis: {}\nfamilyCoeffs: {}".format(basis_, familyCoeffs)
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

def truncatePolynomial(poly, leading_monomial, R):
    poly = R(poly)
    leading_monomial = R(leading_monomial)
    result = leading_monomial * poly.monomial_coefficient(leading_monomial)
    for monomial in poly.monomials():
        if(monomial == leading_monomial):
            break
        result += monomial * poly.monomial_coefficient(monomial)
    return result

def profKapurAlgorithm(basis, R1, R2):
    # Step 1:
    print "Step 1:"
    I = ideal(basis)
    gb = I.groebner_basis()
    print "Groebner basis wrt R1: {}\n".format(gb)

    # Step 2:
    print "Step 2"
    truncated_basis = []
    truncation_map = {}
    for poly in gb:
        poly = R2(poly) 
        truncated_poly = truncatePolynomial(poly, R1(poly).lm(), R2)
        truncated_basis.append(truncated_poly)
        truncation_map[truncated_poly] = poly

    num_iter = 1
    repeat = True
    while(repeat):
        print "Truncated basis {}".format(truncated_basis)
        print "Truncation map: {}\n".format(truncation_map)

        # Step 3:
        print "Step 3"
        (g2h, familyCoeffs) = redExtGroebnerBasis(truncated_basis, R2)
        print "G2h: {}\n".format(g2h)

        # Step 4:
        print "Step 4"
        print "FamilyCoeffs Before Lifting: {}".format(familyCoeffs)
        inverse_lift_map = liftFamilyCoeffs(familyCoeffs, truncation_map)
        print "FamilyCoeffs After Lifting: {}\n".format(familyCoeffs)

        g2c = familyCoeffs.map.keys()
        print "G2c Before interreduce: {}".format(g2c)
        print "Inverse Lift Map Before interreduce: {}\n".format(inverse_lift_map)
        
        (inter_reduced_basis, inter_reduce_lift_map) = interReduce(g2c, R2)
        print "Interreduce Lift Map {}\n".format(inter_reduce_lift_map)
        g2c = list(inter_reduced_basis)
        print "G2c After interreduce: {}".format(g2c)

        aux_inverse_lift_map = {}
        for poly in g2c:
            if(poly in inter_reduce_lift_map):
                value = inter_reduce_lift_map[poly]
                if(value in inverse_lift_map):
                    aux_inverse_lift_map[poly] = inverse_lift_map[value]
                else:
                    aux_inverse_lift_map[poly] = -inverse_lift_map[-value]
            elif(-poly in inter_reduce_lift_map):
                value = -inter_reduce_lift_map[-poly]
                if(value in inverse_lift_map):
                    aux_inverse_lift_map[poly] = inverse_lift_map[value]
                else:
                    aux_inverse_lift_map[poly] = -inverse_lift_map[-value]
            elif(poly in inverse_lift_map):
                aux_inverse_lift_map[poly] = inverse_lift_map[poly]
            else:
                aux_inverse_lift_map[poly] = -inverse_lift_map[-poly]

        print "Inverse Lift Map After interreduce: {}\n".format(aux_inverse_lift_map)
        inverse_lift_map = aux_inverse_lift_map

        # poss 2
        print "poss 2"
        print "Num iterations of poss 2: {}\n".format(num_iter)
        num_iter += 1
        repeat = False
        truncated_basis = []
        truncation_map = {}
        for lift_poly, poly in inverse_lift_map.items():
            lift_poly = R2(lift_poly)
            poly = R2(poly)
            leading_monomial = poly.lm()
            if(lift_poly.lm() > leading_monomial):
                repeat = True
                truncated_poly = truncatePolynomial(lift_poly, leading_monomial, R2)
                truncation_map[truncated_poly] = lift_poly
                truncated_basis.append(truncated_poly)
            else:
                truncation_map[lift_poly] = lift_poly
                truncated_basis.append(lift_poly)

    print "Done"

def testProfKapurAlgorithm():
    
    R1 = PolynomialRing(QQ, 3, 'xyz', order='deglex')
    R2 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    (x, y, z) = R1.gens()
    basis1 = [y^2-x,x^2-y*z-1,z^2-x]
    print "--- Basis: {} From deglex x > y > z to lex x > y > z".format(basis1)
    profKapurAlgorithm(basis1, R1, R2)

    R3 = PolynomialRing(QQ, 3, 'xyz', order='degrevlex')
    R4 = PolynomialRing(QQ, 3, 'zyx', order='lex')
    basis2 = [x*y+z-x*z, x^2-z, 2*x^3-x^2*y*z-1]
    print "--- Basis: {} From degrevlex x > y > z to lex z > y > x".format(basis2)
    profKapurAlgorithm(basis2, R3, R4)

    basis3 = [x + y + z, x*y + y*z + z*y, x*y*z - 1]
    print "--- Basis: {} From deglex x > y > z to lex x > y > z".format(basis3)
    profKapurAlgorithm(basis3, R1, R2)

    R5 = PolynomialRing(QQ, 4, 'xyzu', order='deglex')
    R6 = PolynomialRing(QQ, 4, 'xyzu', order='lex')
    (x, y, z, u) = R5.gens()
    basis4 = [x + y + z + u, x*y + y*z + z*u + u*x, x*y*z + y*z*u + z*u*x + u*x*y, x*y*z*u - 1]
    print "--- Basis: {} From deglex x > y > z > u to lex x > y > z > u".format(basis4)
    profKapurAlgorithm(basis4, R5, R6)

def test2ProfKapurAlgorithm():
    R1 = PolynomialRing(QQ, 4, 'xyzu', order='deglex')
    R2 = PolynomialRing(QQ, 4, 'xyzu', order='lex')
    (x, y, z, u) = R1.gens()
    basis1 = [x^2-x+2*y^2+2*z^2+2*u^2, 2*x*y+2*y*z+2*z*u-y, 2*x*z+y^2+2*y*u-z, x+2*y+2*z+2*u-1]
    print "--- Basis: {} From deglex x > y > z > u to lex x > y > z > u".format(basis1)
    profKapurAlgorithm(basis1, R1, R2)
    
    
def test3ProfKapurAlgorithm():
    R1 = PolynomialRing(QQ, 3, 'abc', order=TermOrder('wdeglex',(5,6,13)))
    R2 = PolynomialRing(QQ, 3, 'abc', order=TermOrder('wdeglex',(13,5,4)))
    (a, b, c) = R1.gens()
    # (a, b, c) = R2.gens()
    basis1 = [a^5-2*b^2+b^3+b^4-2*a^2+2*a^2*b^2+a^4, c-1+b^2+a^2, b^6+3*b^2-3*b^4-b^5+3*a^2-6*a^2*b^2+3*a^2*b^4-3*a^4+3*a^4*b^2]
    print "--- Basis: {} From wdeglex 5, 6, 13 a > b > c to wdeglex 13, 5, 4 a > b > c".format(basis1)
    profKapurAlgorithm(basis1, R1, R2)
    # I = ideal(basis1)
    # print I.groebner_basis()


def testHandExampleProfKapurAlgorithm():
    
    R1 = PolynomialRing(QQ, 3, 'xyz', order='deglex')
    R2 = PolynomialRing(QQ, 3, 'xyz', order='lex')
    (x, y, z) = R1.gens()
    basis1 = [y^2-x,x^2-y*z-1,z^2-x]
    print "--- Basis: {} From deglex x > y > z to lex x > y > z".format(basis1)
    profKapurAlgorithm(basis1, R1, R2)

if __name__ == "__main__":

    # testProfKapurAlgorithm()
    # test2ProfKapurAlgorithm()
    test3ProfKapurAlgorithm()
    # testHandExampleProfKapurAlgorithm()
