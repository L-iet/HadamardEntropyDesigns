"""Exact parity-saturation and repair checks, newly written; stdlib only."""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
MASKS16 = [0,16773120,16519104,10359454,7684730,5820908,9389414,1547504,
           6736278,11838780,3701846,13790378,10646512,2963882,12892774,5974836]
MASKS12 = [0,16773120,16519104,9656012,13838682,14783914,
           1944718,11409518,15230494,5921970,3487346,13018356]


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def dependency(rows):
    pivots = {}
    for i, row in enumerate(rows):
        bits = sum((x & 1) << j for j, x in enumerate(row))
        combination = 1 << i
        while bits:
            pivot = bits.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = (bits, combination)
                break
            other, mask = pivots[pivot]
            bits ^= other
            combination ^= mask
        if not bits:
            return combination
    return None


def saturate2(rows):
    basis = [list(row) for row in rows]
    steps = 0
    while (mask := dependency(basis)) is not None:
        chosen = [i for i in range(len(basis)) if mask >> i & 1]
        value = [sum(basis[i][j] for i in chosen) for j in range(len(basis[0]))]
        assert all(x % 2 == 0 for x in value)
        basis[chosen[0]] = [x//2 for x in value]
        steps += 1
        assert steps < 1000
    return basis, steps


def rref(rows):
    a = [list(map(F, row)) for row in rows]
    pivots = []
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        d = a[rank][col]
        a[rank] = [x/d for x in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][col]:
                scale = a[i][col]
                a[i] = [x-scale*y for x, y in zip(a[i], a[rank])]
        pivots.append(col)
        rank += 1
        if rank == len(a):
            break
    return a, pivots


def odd_kernel(basis):
    # Select pivot columns with an odd determinant using F2 elimination.
    columns = list(map(list, zip(*basis)))
    selected = []
    for j, col in enumerate(columns):
        if dependency([columns[k] for k in selected]+[col]) is None:
            selected.append(j)
        if len(selected) == len(basis):
            break
    assert len(selected) == len(basis)
    free = [j for j in range(len(columns)) if j not in selected]
    augmented = [[row[j] for j in selected]+[-sum(row[j] for j in free)] for row in basis]
    solved, pivots = rref(augmented)
    assert pivots == list(range(len(basis)))
    values = [F(1) for _ in columns]
    for i, j in enumerate(selected):
        values[j] = solved[i][-1]
    denominator = lcm(*(x.denominator for x in values))
    answer = [int(x*denominator) for x in values]
    assert all(x % 2 for x in answer)
    assert all(dot(row, answer) == 0 for row in basis)
    return answer


def classify(rows, label):
    basis, steps = saturate2(rows)
    assert len(rref(basis)[1]) == len(rows)
    # Verify the computed integer basis stays in the exact original row span.
    original_rref, pivots = rref(rows)
    for row in basis:
        reconstructed = [sum(row[pivots[i]]*original_rref[i][j] for i in range(len(rows)))
                         for j in range(len(row))]
        assert reconstructed == row
    witness = next((row for row in basis if sum(row) % 2), None)
    if witness is not None:
        return {'label': label, 'rows': len(rows), 'order': len(rows[0]),
                'halving_steps': steps, 'certificate': 'odd-sum integer row-span vector',
                'witness': witness, 'witness_squared_norm': dot(witness, witness)}
    kernel = odd_kernel(basis)
    assert all(dot(row, kernel) == 0 for row in rows)
    return {'label': label, 'rows': len(rows), 'order': len(rows[0]),
            'halving_steps': steps, 'certificate': 'all-odd integer kernel vector',
            'odd_kernel': kernel, 'kernel_squared_norm': dot(kernel, kernel)}


def had(t):
    return [[1-2*((i & j).bit_count() % 2) for j in range(t)] for i in range(t)]


def row_tensor(a, b):
    return [x*y for x in a for y in b]


def enumerate_sign_kernel(rows):
    reduced, pivots = rref(rows)
    free = [j for j in range(len(rows[0])) if j not in pivots]
    count = 0
    shortest_odd = None
    for tail in product((-1, 1), repeat=len(free)-1):
        values = (1,)+tail
        v = [F(0) for _ in rows[0]]
        for j, value in zip(free, values):
            v[j] = F(value)
        for i, j in enumerate(pivots):
            v[j] = -sum(reduced[i][col]*value for col, value in zip(free, values))
        if all(abs(x) == 1 for x in v):
            count += 1
        if all(x.denominator == 1 and x.numerator % 2 for x in v):
            iv = [int(x) for x in v]
            if shortest_odd is None or dot(iv, iv) < dot(shortest_odd, shortest_odd):
                shortest_odd = iv
    return count, shortest_odd, 2**(len(free)-1)


def norm32_free_exceptions(rows):
    reduced, pivots = rref(rows)
    free = [j for j in range(len(rows[0])) if j not in pivots]
    denominator = lcm(*(reduced[i][j].denominator for i in range(len(rows)) for j in free))
    coefficients = [[int(reduced[i][j]*denominator) for j in free] for i in range(len(rows))]
    tested = solutions = 0
    for exceptional in range(len(free)):
        for tail in product((-1, 1), repeat=len(free)-1):
            values = [1]+list(tail)
            values[exceptional] *= 3
            numerators = [-sum(x*y for x, y in zip(row, values)) for row in coefficients]
            tested += 1
            if all(x % denominator == 0 and (x//denominator) % 2 for x in numerators):
                norm = sum(x*x for x in values)+sum((x//denominator)**2 for x in numerators)
                solutions += int(norm == 32)
    return tested, solutions


def masks_to_rows(masks):
    rows = [[1-2*((mask >> j) & 1) for j in range(24)] for mask in masks]
    assert all(dot(a, b) == 0 for a, b in combinations(rows, 2))
    return rows


if __name__ == '__main__':
    base = [row_tensor(row, [1, 1, 1]) for row in had(4)]
    cases = [classify(base, 'classical repeated4by12'),
             classify(base[1:], 'three rows admitting affine-plane repair')]
    rows24 = masks_to_rows(MASKS16)
    cases.append(classify(rows24, 'earlier order24 terminal16rows'))
    rows12 = masks_to_rows(MASKS12)
    cases.append(classify(rows12, 'earlier order24 terminal12rows'))
    count, shorter, assignments = enumerate_sign_kernel(rows12)
    assert count == 0 and dot(shorter, shorter) == 40
    assert all(dot(row, shorter) == 0 for row in rows12)
    extra_assignments, norm32_solutions = norm32_free_exceptions(rows12)
    assert assignments == 2048 and extra_assignments == 24576 and norm32_solutions == 0

    sparse = []
    for indices, signs, heavy in (((2,8,19),(1,1,1),[0,4,5,6,7,11,15]),
                                  ((9,10,22),(1,-1,1),[4,6,7,9,10,14,15])):
        witness = [0]*24
        for j, sign in zip(indices, signs):
            witness[j] = sign
        weights = [dot(row, witness)**2 for row in rows24]
        assert sum(witness) % 2 and sum(weights) == 24*dot(witness, witness) == 72
        assert [i for i, weight in enumerate(weights) if weight == 9] == heavy
        assert all(weight in (1,9) for weight in weights)
        sparse.append({'witness': witness, 'weights': weights, 'heavy_rows': heavy, 'budget': 0})

    words = [(x,y,(x+y)%3,(x-y)%3) for x in range(3) for y in range(3)]
    installed = [[1-2*(position == word[j]) for j in range(4) for position in range(3)]
                 for word in words]
    completed = base[1:]+installed
    assert all(dot(a,b) == 0 for a,b in combinations(completed,2))
    weighted_cases = []
    for t in (1,2,4):
        ht = had(t)
        original = [row_tensor(row,tau) for row in base for tau in ht]
        n = 12*t
        # A consecutive triple after permuting tensor coordinates.
        witness = [int(j in (0,t,2*t)) for j in range(n)]
        for repaired in range(t+1):
            old = [row for i,row in enumerate(original) if i not in range(repaired)]
            new = [row_tensor(row,ht[fiber]) for fiber in range(repaired) for row in installed]
            assert all(dot(row,witness)**2 == 9 for row in old)
            assert all(dot(row,witness)**2 == 1 for row in new)
            assert n*dot(witness,witness)-sum(dot(row,witness)**2 for row in old+new) == 0
            weighted_cases.append({'t':t,'repaired':repaired,'remaining_original_deletions':t-repaired})

    # Arbitrary unequal disjoint odd blocks: the same general budget applies.
    unequal_blocks = []
    offset = 0
    for size in (1,3,3,5):
        witness = [int(offset <= j < offset+size) for j in range(12)]
        offset += size
        budget = 12*size-sum(dot(row,witness)**2 for row in base[1:])
        assert budget >= 9 and budget % 8 == 1
        assert sum(dot(row,witness)**2 for row in installed) == budget
        unequal_blocks.append({'size':size,'budget_for_nine_missing_rows':budget})

    output = {'status':'passed','arithmetic':'exact rational/integer',
              'saturated_lattice_alternatives':cases,'sparse_order24_witnesses':sparse,
              'weighted_fiber_cases':weighted_cases,'unequal_odd_blocks':unequal_blocks,
              'odd_coset_minimum_example':{'row_masks':MASKS12,'minimum_squared_norm':40,
                'minimizing_vector':shorter,'free_sign_assignments':assignments,
                'free_single_three_assignments':extra_assignments,'sign_solutions':0,'norm32_solutions':0},
              'scope':'Finite certificates supplement the general proofs; no conjecture proof is claimed.'}
    (HERE/'checks.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','lattice_alternatives':len(cases),
                      'sparse_witnesses':len(sparse),'weighted_fiber_cases':len(weighted_cases),
                      'odd_coset_minimum_squared_norm':40,'information_assignments':assignments+extra_assignments}))
