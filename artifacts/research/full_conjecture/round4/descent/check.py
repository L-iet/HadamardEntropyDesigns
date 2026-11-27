"""Exact checks, newly written; Python standard library only."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def tensor(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def plus(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def data(u, p):
    n = len(u)
    assert mm(transpose(u), u) == eye(n)
    w = [[abs(x)**(p-2)*x for x in row] for row in u]
    m = mm(transpose(u), w)
    assert m == transpose(m)
    q = sum(abs(x)**p for row in u for x in row)
    r = sum(abs(x)**(p-2) for row in u for x in row)
    return m, q, r


def ts(u, m, p, x):
    ux = mm(u, x)
    t = sum(abs(u[i][j])**(p-2)*ux[i][j]**2
            for i in range(len(u)) for j in range(len(u)))
    s = trace(mm(m, mm(transpose(x), x)))
    return t, s


def hessian(u, m, p, x):
    t, s = ts(u, m, p, x)
    return p*((p-1)*t-s)


def basis(n, skew=False):
    for i, j in combinations(range(n), 2):
        x = [[F(0) for _ in range(n)] for _ in range(n)]
        x[i][j] = F(1)
        x[j][i] = F(-1 if skew else 1)
        yield x, F(1, 2)
    if not skew:
        for ell in range(1, n):
            x = [[F(0) for _ in range(n)] for _ in range(n)]
            for i in range(ell):
                x[i][i] = F(1)
            x[ell][ell] = -F(ell)
            yield x, F(1, ell*(ell+1))


def partials2(x, n):
    a = [[sum(x[i*n+t][j*n+t] for t in range(n))
          for j in range(n)] for i in range(n)]
    b = [[sum(x[t*n+i][t*n+j] for t in range(n))
          for j in range(n)] for i in range(n)]
    return a, b


records = []
for n in range(2, 9):
    u = [[F(2, n)-int(i == j) for j in range(n)] for i in range(n)]
    for p in (4, 6, 8):
        m, q, r = data(u, p)
        # n=4 is flat and has no strict trace-ratio inequality.
        t_sum = s_sum = F(0)
        choices = []
        for z, norm in basis(n):
            assert trace(z) == 0 and z == transpose(z)
            t, s = ts(u, m, p, z)
            t_sum += norm*t
            s_sum += norm*s
            if s > 0:
                choices.append((t/s, z))
        assert t_sum == (r+q)/2-q/n
        assert s_sum == (n+1)*q/2-q/n
        if r < n*q:
            b0 = (n*r+(n-2)*q)/((n+2)*(n-1)*q)
            b = (r+q)/((n+1)*q)
            assert 0 < b0 < b < 1
            beta, z = min(choices, key=lambda a: a[0])
            assert beta <= b0
            ys = [(ts(u, m, p, y), y) for y, _ in basis(n, skew=True)]
            alpha, y = min(((t/s, y) for (t, s), y in ys if s > 0),
                           key=lambda a: a[0])
            assert alpha <= (r-q)/((n-1)*q) < 1
            k = 2
            while (p-1)*alpha*beta**(k-1) >= 1:
                k += 1
                assert k < 200
            zero = [[F(0) for _ in range(n)] for _ in range(n)]
            assert partials2(tensor(y, z), n) == (zero, zero)
            records.append({'n': n, 'p': p, 'alpha': str(alpha),
                            'beta': str(beta), 'b0': str(b0), 'k': k})

# Direct full Hessian checks of product-tangent splitting.
for n in range(2, 6):
    u = [[F(2, n)-int(i == j) for j in range(n)] for i in range(n)]
    m, q, _ = data(u, 4)
    u2, m2 = tensor(u, u), tensor(m, m)
    skew = [y for y, _ in basis(n, skew=True)]
    a, b = skew[0], skew[-1]
    local = plus(tensor(a, eye(n)), tensor(eye(n), b))
    assert hessian(u2, m2, 4, local) == q*(hessian(u, m, 4, a)+hessian(u, m, 4, b))

# Concrete interaction-only descent from the strict order-5 trap.
n = 5
u = [[F(2, n)-int(i == j) for j in range(n)] for i in range(n)]
m, q, _ = data(u, 4)
assert m == [[F(7, 25)*int(i == j)-F(6, 125)
              for j in range(n)] for i in range(n)]
y = [[F(0) for _ in range(n)] for _ in range(n)]
z = [[F(0) for _ in range(n)] for _ in range(n)]
for i, j in ((0, 1), (1, 2), (2, 0)):
    y[i][j], y[j][i] = F(1), F(-1)
for i, j, value in ((0, 1, 1), (1, 2, -1), (2, 3, 1), (3, 0, -1)):
    z[i][j] = z[j][i] = F(value)
x = tensor(y, z)
curvature = hessian(tensor(u, u), tensor(m, m), 4, x)
assert curvature == -F(192, 625)
zero = [[F(0) for _ in range(n)] for _ in range(n)]
assert partials2(x, n) == (zero, zero)
d = [[F((1, -1, 1, -1, 1)[i] if i == j else 0)
      for j in range(n)] for i in range(n)]
assert mm(mm(d, z), d) == [[-v for v in row] for row in z]
# All exact power-series coefficients through degree eight have symmetric
# one-factor partial traces; the proof establishes this for every degree.
power = eye(n*n)
for degree in range(9):
    for marginal in partials2(power, n):
        assert marginal == transpose(marginal)
    if degree != 8:
        power = mm(power, x)

# Explicit Paley-type conference construction and its order-36 Hadamard.
prime = 17
quadratic = {x*x % prime for x in range(1, prime)}
c = [[0 for _ in range(18)] for _ in range(18)]
for a in range(1, 18):
    c[0][a] = c[a][0] = 1
for a in range(prime):
    for b in range(prime):
        if a != b:
            c[a+1][b+1] = 1 if (a-b) % prime in quadratic else -1
assert c == transpose(c)
assert mm(c, c) == [[17*int(i == j) for j in range(18)] for i in range(18)]
h = []
for i in range(18):
    h.append([c[i][j]+int(i == j) for j in range(18)]
             + [c[i][j]-int(i == j) for j in range(18)])
for i in range(18):
    h.append([c[i][j]-int(i == j) for j in range(18)]
             + [-c[i][j]-int(i == j) for j in range(18)])
assert all(abs(x) == 1 for row in h for x in row)
assert mm(h, transpose(h)) == [[36*int(i == j) for j in range(36)] for i in range(36)]

output = {'status': 'passed', 'arithmetic': 'exact rational/integer',
          'tracefree_activation_cases': records,
          'product_hessian_cases': 4,
          'explicit_interaction_curvature': str(curvature),
          'symmetric_partial_trace_coefficients_checked_through_degree': 8,
          'conference_order': 18, 'hadamard_order': 36,
          'scope': 'Finite checks support, but do not replace, the general proofs.'}
(HERE/'checks.json').write_text(json.dumps(output, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'status': 'passed', 'activation_cases': len(records),
                  'product_hessian_cases': 4, 'interaction_curvature': str(curvature),
                  'hadamard_order': 36}))
