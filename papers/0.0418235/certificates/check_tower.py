#!/usr/bin/env python3
"""Exact finite calculations printed in the tower section, independent of old helpers."""
from fractions import Fraction
from itertools import combinations
import json

if not __debug__:
    raise RuntimeError("Run without -O: assertions implement arithmetic checks")


def reduce(v, basis):
    for p in sorted(basis, reverse=True):
        if v >> p & 1:
            v ^= basis[p]
    return v


def span(vectors):
    basis = {}
    for v in vectors:
        v = reduce(v, basis)
        if v:
            basis[v.bit_length() - 1] = v
    return basis


def verify():
    pairs = list(combinations(range(7), 2))
    rows = [int(x, 16) for x in
            '1 142104 1444000 4480410 a010820 d020000 4 8 10 20 40 2 1a080 2c080 814aab 42aa056'.split()]
    quadratic = span(rows)
    assert len(quadratic) == 16

    def square(v):
        out = v
        for k, (i, j) in enumerate(pairs, 7):
            if v >> i & v >> j & 1:
                out ^= 1 << k
        return out

    def bracket(v, w):
        return square(v ^ w) ^ square(v) ^ square(w)

    def tensor(q):
        out = [(i, i) for i in range(7) if q >> i & 1]
        for k, (i, j) in enumerate(pairs, 7):
            if q >> k & 1:
                out += [(i, j), (j, i)]
        return out

    def cubic(q, v):
        out = 0
        for i, j in tensor(q):
            for k in range(7):
                if v >> k & 1:
                    out ^= (1 << (49*i + 7*j + k)) ^ (1 << (49*k + 7*i + j))
        return out

    cubic_relations = span(cubic(q, 1 << k) for q in rows for k in range(7))
    assert len(cubic_relations) == 92
    cubic_relations = span([*cubic_relations.values(), cubic(bracket(53, 89), 89)])
    assert len(cubic_relations) == 93
    free_cubic = span(cubic(1 << i, 1 << k) for i in range(28) for k in range(7))
    assert len(free_cubic) == 112
    class_rank_one = len(span(reduce(bracket(1, 1 << k), quadratic) for k in range(7)))
    class_rank_two = len(span(reduce(cubic(1 << i, 1), cubic_relations) for i in range(28)))
    assert class_rank_one == class_rank_two == 6
    assert len(span([*quadratic.values(), square(89), bracket(53, 89)])) == 18

    def multiply(g, h):
        a,b,c,d = g & 1, g >> 1 & 1, g >> 2 & 3, g >> 4 & 1
        A,B,C,D = h & 1, h >> 1 & 1, h >> 2 & 3, h >> 4 & 1
        return (a ^ A) + 2*(b ^ B) + 4*((c+C) % 4) + 16*(d ^ D ^ ((c & 1)*B))

    def right_difference(v, h):
        out = v
        for g in range(32):
            if v >> g & 1:
                out ^= 1 << multiply(g, h)
        return out

    ideals = [span(1 << g for g in range(32))]
    for n in range(8):
        ideals.append(span(right_difference(v, h) for v in ideals[-1].values() for h in (1,2,4)))
    dimensions = list(map(len, ideals))
    assert dimensions == [32,31,28,23,16,9,4,1,0]
    kernels = []
    for n in range(8):
        graded = span(reduce(v, ideals[n+1]) for v in ideals[n].values())
        denominator = ideals[n+2] if n+2 < len(ideals) else {}
        images = []
        for v in graded.values():
            image = 0
            for j,h in enumerate((1,2,4)):
                image |= reduce(right_difference(v,h), denominator) << (32*j)
            images.append(image)
        kernels.append(len(graded)-len(span(images)))
    assert kernels == [0,0,0,0,0,0,0,1]
    assert list(ideals[7].values()) == [(1 << 32)-1]
    t = Fraction(11,34)
    pd = (1+t)**3 * (1+t*t)**2
    c1=t*t/(1+t)
    c2=2*t-1+1/(1+t)**2
    c24=2*t-1+1/((1+t)**2*(1+t*t))
    c4=t**4/((1+t)*(1+t*t))
    value=1-7*t+2*c2+3*c24+(3*t-1+1/pd)+c1-t*t*(1-t**7/pd)+5*c4
    assert value == Fraction(-160218343,112275691650)
    result={'status':'PASS independent exact manuscript tower calculations',
            'quadratic_rank':16,'cubic_ranks':[92,93,112],
            'quotient_order_exponent':7+(28-16)+(112-93),
            'conjugacy_class_exponent':class_rank_one+class_rank_two,
            'local_augmentation_dimensions':dimensions,'graded_row_kernel_dimensions':kernels,
            'GS_value':str(value)}
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    verify()
