"""Exact finite checks of balancing/capacity obstructions; stdlib only."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random

HERE = Path(__file__).resolve().parent
RNG = random.Random(20261120)


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def det(a):
    a = [list(map(F, row)) for row in a]
    result = F(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        d = a[i][i]
        result *= d
        for k in range(i+1, len(a)):
            scale = a[k][i]/d
            for j in range(i+1, len(a)):
                a[k][j] -= scale*a[i][j]
    return result


def prod(xs):
    result = F(1)
    for x in xs:
        result *= x
    return result


def reflection(v):
    norm = sum(x*x for x in v)
    return [[F(i == j)-F(2*v[i]*v[j], norm)
             for j in range(len(v))] for i in range(len(v))]


def bistochastic(b):
    return all(sum(row) == 1 for row in b+transpose(b)) and all(
        x >= 0 for row in b for x in row)


capacity_cases = 0
for n in range(2, 8):
    u = reflection(list(range(1, n+1)))
    assert mm(u, transpose(u)) == eye(n)
    candidates = [eye(n), [[F(1, n) for _ in range(n)] for _ in range(n)],
                  [[x*x for x in row] for row in u]]
    for b in candidates:
        assert bistochastic(b)
        for _ in range(8):
            x = [F(RNG.randrange(1, 10), RNG.randrange(1, 10)) for _ in range(n)]
            output = [sum(b[i][j]*x[j] for j in range(n)) for i in range(n)]
            assert prod(output) >= prod(x)
            # Positive definite X = LL^T with rational lower-triangular L.
            lower = [[F(RNG.randrange(-3, 4)) if j < i else F(i == j)
                      for j in range(n)] for i in range(n)]
            matrix = mm(lower, transpose(lower))
            out_diag = [sum(b[i][j]*matrix[j][j] for j in range(n)) for i in range(n)]
            assert prod(out_diag) >= prod(matrix[i][i] for i in range(n)) >= det(matrix)
            capacity_cases += 1
        # Exact equality witnesses for the two infima.
        assert prod(sum(row) for row in b) == 1

# Exhaust all positive diagonal multiplier choices from a finite alphabet.
scaling_cases = orthogonal_scalings = 0
for n in (2, 3, 4):
    u = reflection([1]*n)
    for values in product((F(1, 2), F(1), F(2)), repeat=2*n):
        d, e = values[:n], values[n:]
        changed = [[d[i]*u[i][j]*e[j] for j in range(n)] for i in range(n)]
        scaling_cases += 1
        if mm(changed, transpose(changed)) == eye(n):
            assert changed == u
            orthogonal_scalings += 1

# Parity defect of arbitrary sign matrices and rational-orthogonal F4 gap.
parity_cases = energy_cases = 0
for n in (6, 10, 14):
    for _ in range(30):
        h = [[RNG.choice((-1, 1)) for _ in range(n)] for _ in range(n)]
        gram = mm(h, transpose(h))
        defect = sum((gram[i][j]-n*int(i == j))**2 for i in range(n) for j in range(n))
        assert defect >= 2*n*(n-2)
        parity_cases += 1
    for _ in range(6):
        u = eye(n)
        for _ in range(3):
            vector = [RNG.randrange(-2, 3) for _ in range(n)]
            if not any(vector):
                vector[0] = 1
            u = mm(u, reflection(vector))
        assert mm(u, transpose(u)) == eye(n)
        q = sum(x**4 for row in u for x in row)
        distance = sum((x*x-F(1, n))**2 for row in u for x in row)
        assert distance == q-1 >= F(2*(n-2), 9*n*n)
        energy_cases += 1

report = {'status': 'passed', 'arithmetic': 'exact rational/integer',
          'capacity_inequality_cases': capacity_cases,
          'positive_diagonal_scalings_examined': scaling_cases,
          'orthogonal_scalings_all_identical_to_base': orthogonal_scalings,
          'sign_matrix_parity_cases': parity_cases,
          'rational_orthogonal_energy_gap_cases': energy_cases,
          'order6_rational_gap': str(F(2*(6-2), 9*6*6)),
          'scope': 'Finite checks support the general proofs; they do not prove the conjecture.'}
(HERE/'checks.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(json.dumps(report, indent=2))
