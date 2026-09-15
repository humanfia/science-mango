#!/usr/bin/env python3
"""Exact finite polynomial optimizer; local validation is separate from proof review."""
import itertools
import json
from pathlib import Path

def rem(a, b):
    if b <= 0:
        raise ValueError("positive divisor required")
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a

def quotient(a, b):
    q = 0
    while a and a.bit_length() >= b.bit_length():
        s = a.bit_length() - b.bit_length()
        q ^= 1 << s
        a ^= b << s
    if a:
        raise ValueError("inexact division")
    return q

def gcd(a, b):
    while b:
        a, b = b, rem(a, b)
    return a

def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
    return result

def optimize(a0, b0, F, K):
    if min(a0, b0) < 1 or F < 1 or not F & 1 or K < 0:
        raise ValueError("invalid optimizer input")
    if F == 1:
        return None
    r = max(a0.bit_length(), b0.bit_length()) - 1
    mask = (1 << r) - 1
    # Values carry the witness to avoid any dependence on backpointer mutation.
    states = {(0, 0): (0, 0)}
    power = 1
    for i in range(K + r + 1):
        next_states = {}
        for (memory, residue), (cost, c) in states.items():
            for bit in ((0, 1) if i <= K else (0,)):
                window = (memory << 1) | bit
                new_cost = cost + ((window & a0).bit_count() & 1) + ((window & b0).bit_count() & 1)
                key = (window & mask, residue ^ (power if bit else 0))
                value = (new_cost, c | (bit << i))
                if key not in next_states or value < next_states[key]:
                    next_states[key] = value
        states = next_states
        power = rem(power << 1, F)
    distance, witness = min(value for (memory, residue), value in states.items() if memory == 0 and residue)
    u, v = multiply(a0, witness), multiply(b0, witness)
    assert rem(witness, F) and u.bit_count() + v.bit_count() == distance
    return dict(distance=distance, c=witness, u=u, v=v)

def parameters(a, b, F):
    G = gcd(a, b)
    if F <= 1 or rem(G, F):
        raise ValueError("nonconstant F must divide G")
    a0, b0 = quotient(a, G), quotient(b, G)
    R = max(a.bit_length(), b.bit_length()) - 1
    r = max(a0.bit_length(), b0.bit_length()) - 1
    D = a0.bit_count() + b0.bit_count()
    return dict(a0=a0, b0=b0, threshold=R*D, K=R*(D-1)-r)

# Independent set arithmetic for the exhaustive reference.
def support(poly):
    return {i for i in range(poly.bit_length()) if poly >> i & 1}

def set_product(a, b):
    output = set()
    for i in a:
        for j in b:
            output.symmetric_difference_update({i+j})
    return output

def set_remainder(a, b):
    a = set(a)
    while a and max(a) >= max(b):
        offset = max(a) - max(b)
        a.symmetric_difference_update({i+offset for i in b})
    return a

def brute_optimizer(a0, b0, F, K):
    values = []
    for c in range(1 << (K+1)):
        cs = support(c)
        if set_remainder(cs, support(F)):
            values.append(len(set_product(support(a0), cs)) + len(set_product(support(b0), cs)))
    return min(values)

def row_basis(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length()-1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return basis

def in_span(v, basis):
    while v:
        pivot = v.bit_length()-1
        if pivot not in basis:
            return False
        v ^= basis[pivot]
    return True

def matrix_distance(N, a, b, upper):
    A, B = support(a), support(b)
    hx = [sum(1 << ((i+j)%N) for j in A) | sum(1 << (N+(i+j)%N) for j in B) for i in range(N)]
    hz = [sum(1 << ((i-j)%N) for j in B) | sum(1 << (N+(i-j)%N) for j in A) for i in range(N)]
    basis = row_basis(hx)
    assert all((x & z).bit_count()%2 == 0 for x in hx for z in hz)
    if len(basis) + len(row_basis(hz)) == 2*N:
        return None
    for weight in range(1, upper+1):
        for positions in itertools.combinations(range(2*N), weight):
            vector = sum(1 << i for i in positions)
            if all((vector & check).bit_count()%2 == 0 for check in hz) and not in_span(vector, basis):
                return weight
    raise AssertionError("upper bound not attained")

def validate():
    count = 0
    for a0, b0, F, K in itertools.product((1,3,5,7), (1,3,5,7), (3,5,7,9), range(5)):
        result = optimize(a0,b0,F,K)
        assert result['distance'] == brute_optimizer(a0,b0,F,K)
        count += 1
    assert optimize(1,1,1,0) is None
    assert set_remainder(support(3), support(5)) == support(3)
    assert not set_remainder(support(3), support(3))
    cases = []
    for a,b,orders in [(3,3,range(3,9)), (5,3,range(7,12)), (9,3,range(13,17)), (15,15,(8,12,16))]:
        for N in orders:
            F = gcd(gcd(a,b),(1<<N)|1)
            params = parameters(a,b,F)
            result = optimize(params['a0'],params['b0'],F,params['K'])
            exact = matrix_distance(N,a,b,result['distance'])
            assert N > params['threshold'] and exact == result['distance']
            cases.append(dict(N=N,a=a,b=b,F=F,d=exact,**params))
    # Below-threshold behavior is deliberately different and must not be masked.
    assert matrix_distance(6,9,3,4) == 2
    assert optimize(7,1,3,7)['distance'] == 4
    assert matrix_distance(5,7,11,4) is None
    return dict(status='passed',optimizer_exhaustive_cases=count,cyclic_matrix_cases=cases,
                controls=['F=1 has no logical distance','repeated F must not be replaced by radical','N=6 below threshold differs'],
                evidence='finite checks, not proof premises; implementation not included in prior harness reviews')

if __name__ == '__main__':
    result = validate()
    path = Path(__file__).with_name('verification.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status=result['status'],optimizer_cases=result['optimizer_exhaustive_cases'],matrix_cases=len(result['cyclic_matrix_cases']))))
