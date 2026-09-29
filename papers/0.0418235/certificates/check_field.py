#!/usr/bin/env python3
"""Exact checks of the printed retained-field data, with no archived helper imports."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
import re

RAD = (-1, 2, 3, 5, 7, 11, 13)
PAIRS = tuple(combinations(range(7), 2))
CATALOG = (
    (-1,65,4,7,1), (-55,91,6,1,1), (-2,33,1,4,1),
    (-55,14,1,1,2), (-55,26,7,1,2), (-7,2,1,1,2),
    (-10,1001,1,10,1), (22,273,19,2,1), (-39,55,4,1,1),
    (-35,429,1,7,2), (-143,42,5,1,2), (-3,13,1,2,1),
    (-26,105,1,2,1), (-6,385,1,8,1), (-14,65,3,2,1),
    (-11,5,3,1,2), (-1,13,-2,3,1),
)
A_WORDS = (17,27184,6220,2,32768,39508,132)
B_WORDS = (2,256,512,4096,9,65,132,2052,24576,37,32768,65536)
A_HEX = '9014280 af24500 6830680 b401400 800200 acf0980 a138900'.split()
B_HEX = 'b401400 9140a00 78c1900 520e700 2415680 1c38e00 a138900 213900 45f9c00 1bb80 800200 1000'.split()
RELATIONS = [int(x,16) for x in
    '1 142104 1444000 4480410 a010820 d020000 4 8 10 20 40 2 1a080 2c080 814aab 42aa056'.split()]


def squareclass(n):
    result = int(n < 0)
    n = abs(n)
    for i,p in enumerate(RAD[1:],1):
        while n % p == 0:
            n //= p
            result ^= 1 << i
    assert n == 1
    return result


def cup(a,b):
    result = a & b
    for k,(i,j) in enumerate(PAIRS,7):
        if ((a >> i & 1)*(b >> j & 1)) ^ ((a >> j & 1)*(b >> i & 1)):
            result ^= 1 << k
    return result


def rank(vectors):
    basis = {}
    for v in vectors:
        while v:
            k = v.bit_length()-1
            if k in basis:
                v ^= basis[k]
            else:
                basis[k] = v
                break
    return len(basis)


def vector_span(vectors):
    result = {0}
    for v in vectors:
        result |= {x ^ v for x in tuple(result)}
    return result


def evaluate(q,v):
    result = (q & v).bit_count() % 2
    for k,(i,j) in enumerate(PAIRS,7):
        if q >> k & 1:
            result ^= (v >> i & 1)*(v >> j & 1)
    return result


def polar(q,v):
    return sum((evaluate(q,v ^ (1 << i)) ^ evaluate(q,v) ^ evaluate(q,1 << i)) << i
               for i in range(7))


# Rational multiplication and trace in a quartic quotient Q[X]/(f).
def quartic_mul(a,b,p):
    result = [F(0)]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            result[i+j] += x*y
    for i in range(6,3,-1):
        for j in range(4):
            result[i-4+j] -= result[i]*p[j]
    return result[:4]


def quartic_trace(a,p):
    return sum(quartic_mul(a,[F(int(i == j)) for i in range(4)],p)[j]
               for j in range(4))


def determinant(matrix):
    a = [row[:] for row in matrix]
    result = F(1)
    for k in range(len(a)):
        j = next(j for j in range(k,len(a)) if a[j][k])
        if j != k:
            a[j],a[k] = a[k],a[j]
            result = -result
        value = a[k][k]
        result *= value
        for j in range(k+1,len(a)):
            ratio = a[j][k]/value
            for i in range(k+1,len(a)):
                a[j][i] -= ratio*a[k][i]
    return result


def quartic_bases():
    output = {}
    for prime,p,basis in (
        (5, [80,0,20,0], [[1,0,0,0], [F(3,2),F(-1,4),F(1,8),0],
                         [F(-3,2),F(-1,4),F(-1,8),0], [-1,F(3,4),F(-1,8),F(1,16)]]),
        (13,[208,0,52,0],[[1,0,0,0], [F(5,6),F(-1,4),F(1,24),0],
                         [F(-5,6),F(-1,4),F(-1,24),0], [F(-4,3),F(11,12),F(-1,24),F(1,48)]]),
    ):
        basis = [[F(x) for x in b] for b in basis]
        characteristic_polynomials = []
        for b in basis:
            value = [F(1),F(0),F(0),F(0)]
            power_traces = [F(4)]
            for k in range(1,5):
                value = quartic_mul(value,b,p)
                power_traces.append(quartic_trace(value,p))
            coefficients = [F(1)]
            for k in range(1,5):
                coefficients.append(-sum(coefficients[k-i]*power_traces[i]
                                         for i in range(1,k+1))/k)
            assert all(c.denominator == 1 for c in coefficients)
            characteristic_polynomials.append([int(c) for c in coefficients])
        gram = [[quartic_trace(quartic_mul(a,b,p),p) for a in basis] for b in basis]
        disc = determinant(gram)
        assert disc == prime**3
        output[str(prime)] = {
            'integral_element_characteristic_polynomials':characteristic_polynomials,
            'trace_discriminant':int(disc),
        }
    return output


FACTORS = []
for mask in range(128):
    value = 1
    for i,p in enumerate(RAD):
        if mask >> i & 1:
            value *= p
    FACTORS.append(value)


class Element:
    """Sparse rational coordinates on product(sqrt(RAD[i]))."""
    def __init__(self,terms):
        self.terms = {i:F(v) for i,v in terms.items() if v}
    def __add__(self,other):
        result = self.terms.copy()
        for i,v in other.terms.items():
            result[i] = result.get(i,F(0))+v
        return Element(result)
    def __mul__(self,other):
        result = {}
        for i,a in self.terms.items():
            for j,b in other.terms.items():
                k = i ^ j
                result[k] = result.get(k,F(0))+a*b*FACTORS[i & j]
        return Element(result)
    def scale(self,value):
        return Element({i:v*value for i,v in self.terms.items()})
    def conjugate(self,v):
        return Element({i:(-a if (i & v).bit_count()%2 else a)
                        for i,a in self.terms.items()})
    def __eq__(self,other):
        return self.terms == other.terms
    def __bool__(self):
        return bool(self.terms)


def pure_projector():
    word = (4,6,9,10,11)
    beta = Element({0:1})
    for i in word:
        A,B,x,y,z = CATALOG[i]
        beta = beta*Element({0:x,squareclass(A):y})
    projector = Element({0:1})
    for v,sign in zip((1,16,32,6,74),(1,1,1,-1,-1)):
        lift = Element({0:1})
        for i in word:
            A,B,x,y,z = CATALOG[i]
            if (squareclass(A) & v).bit_count()%2:
                lift = (lift*Element({0:x,squareclass(A):-y})
                        *Element({squareclass(B):F(1,B*z)}))
        assert beta*lift*lift == beta.conjugate(v)
        projector = projector+(lift*projector.conjugate(v)).scale(sign)
        assert projector
    eta = Element({0:393911,squareclass(30):-10360,
                   squareclass(65):23013,squareclass(78):-12000})
    assert (beta*projector*projector).scale(F(1,256)) == eta
    assert 393911-10360*6-23013*9-2400*45 == 16634 > 0
    return {'status':'PASS eta0 = beta * P5^2 / 256',
            'projector_vectors':[1,16,32,6,74],
            'projector_signs':[1,1,1,-1,-1],
            'positive_embedding_lower_bound':16634}


def verify():
    if not __debug__:
        raise RuntimeError('Run without -O: assertions implement arithmetic checks')
    text = (Path(__file__).resolve().parents[1]/'sections/retained-field.tex').read_text()
    rows = []
    for line in text.splitlines():
        line = line.rstrip('\\')
        if re.fullmatch(r'\d+&-?\d+&\d+&-?\d+&-?\d+&\d+',line):
            rows.append(tuple(map(int,line.split('&'))))
    assert rows == [(i,*row) for i,row in enumerate(CATALOG)]
    assert re.findall(r'\\texttt\{([0-9a-f]+)\}',text) == A_HEX+B_HEX
    for letter,words in [('A',A_WORDS),('B',B_WORDS)]:
        match = re.search(r'\\mathcal '+letter+r'&=\(([^)]*)\)',text)
        assert tuple(map(int,match.group(1).split(','))) == words
    catalog_forms = []
    for A,B,x,y,z in CATALOG:
        assert x*x-A*y*y == B*z*z
        catalog_forms.append(cup(squareclass(A),squareclass(B)))
    def form(word):
        result = 0
        for i,q in enumerate(catalog_forms):
            if word >> i & 1:
                result ^= q
        return result
    completed = [form(a) for a in A_WORDS]
    full = [form(b) for b in B_WORDS]
    assert completed == [int(x,16) for x in A_HEX]
    assert full == [int(x,16) for x in B_HEX]
    assert rank(completed) == 7 and rank(full) == 12 and rank(RELATIONS) == 16
    assert all(not (q & r).bit_count()%2 for q in full for r in RELATIONS)
    full_space = vector_span(full)
    assert set(completed) <= full_space
    inventory = Counter()
    parity_kernel = []
    choice_counts = Counter()
    for q in sorted(vector_span(completed)-{0}):
        polar_rank = rank(polar(q,1 << i) for i in range(7))
        gauss = sum(1-2*evaluate(q,v) for v in range(128))
        assert polar_rank in (2,4,6) and gauss in (0,2**(7-polar_rank//2))
        inventory[(polar_rank,gauss > 0)] += 1
        assert evaluate(q,1) == 0
        if polar(q,1) == 0:
            parity_kernel.append(q)
        if gauss == 0:
            choices = tuple(p for p in (5,13)
                            if sum(1-2*evaluate(q ^ squareclass(p),v) for v in range(128)) > 0)
            assert choices
            choice_counts[choices] += 1
    assert inventory == {(2,True):5,(2,False):3,(4,True):34,(4,False):23,(6,True):48,(6,False):14}
    assert parity_kernel == [form(sum(1 << i for i in (4,6,9,10,11)))]
    assert choice_counts == {(5,13):26,(5,):9,(13,):5}
    result = {
        'status':'PASS independent exact printed retained-field arithmetic',
        'catalog_norm_identities':17,
        'completed_rank':7,'full_rank':12,'quadratic_relation_rank':16,
        'quadratic_relation_annihilation':True,
        'completed_field_degree':16384,'full_field_degree':524288,
        'polar_rank_counts':{'2':8,'4':57,'6':62},
        'positive_gauss_counts':{'2':5,'4':34,'6':48},
        'zero_gauss_counts':{'2':3,'4':23,'6':14},
        'pure_sector_count':1,
        'quartic_twist_choices':{','.join(map(str,k)):v for k,v in choice_counts.items()},
        'quartic_integral_bases':quartic_bases(),
        'pure_projector':pure_projector(),
    }
    print(json.dumps(result,indent=2))
    return result


if __name__ == '__main__':
    verify()
