"""Exact verification of the odd-block exchange construction; stdlib only."""
from itertools import combinations, product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def gram_check(rows, n):
    assert all(len(row) == n and all(x in (-1, 1) for x in row) for row in rows)
    assert all(dot(a, b) == 0 for a, b in combinations(rows, 2))


def sylvester(t):
    assert t > 0 and t & (t-1) == 0
    return [[1-2*((i & j).bit_count() % 2) for j in range(t)] for i in range(t)]


def kronrow(a, b):
    return [x*y for x in a for y in b]


def tensor(a, b):
    return [kronrow(ar, br) for ar in a for br in b]


def transpose(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[dot(ar, col) for col in zip(*b)] for ar in a]


def blocksums(row, s=3):
    return [sum(row[j:j+s]) for j in range(0, len(row), s)]


k = sylvester(4)
p = [kronrow(row, [1, 1, 1]) for row in k]
gram_check(p, 12)
all_signs = list(product((-1, 1), repeat=12))
assert not [v for v in all_signs if all(dot(v, row) == 0 for row in p)]

words = [(x, y, (x+y) % 3, (x-y) % 3) for x in range(3) for y in range(3)]
assert all(sum(a == b for a, b in zip(x, y)) == 1 for x, y in combinations(words, 2))
for i, j in combinations(range(4), 2):
    assert len({(w[i], w[j]) for w in words}) == 9

counts = []
for deleted in range(4):
    retained = [row for i, row in enumerate(p) if i != deleted]
    candidates = [v for v in all_signs if all(dot(v, row) == 0 for row in retained)]
    assert len(candidates) == 164
    normed = []
    for row in candidates:
        b = blocksums(row)
        lam = b[0]*k[deleted][0]
        assert all(b[j] == lam*k[deleted][j] for j in range(4))
        if lam > 0:
            normed.append((lam, row))
    assert len(normed) == 82
    assert sorted(lam for lam, _ in normed).count(1) == 81
    assert sorted(lam for lam, _ in normed).count(3) == 1
    inserted = [[k[deleted][j]*(1-2*(position == word[j]))
                 for j in range(4) for position in range(3)] for word in words]
    assert all(tuple(row) in candidates for row in inserted)
    gram_check(retained+inserted, 12)
    counts.append({'deleted_row': deleted, 'candidates_including_both_signs': len(candidates),
                   'antipodal_classes': len(normed), 'completion_rows': 12})

# Use the deleted-first-row completion for the tensor family.
r = [[1-2*(position == word[j]) for j in range(4) for position in range(3)] for word in words]
b = p[1:]+r
gram_check(b, 12)

# Integer rank-eight residual factor: four scaled A2 triangle blocks.
conference = [[0, 1, 1, 1], [-1, 0, 1, -1],
              [-1, -1, 0, 1], [-1, 1, -1, 0]]
assert mm(transpose(conference), conference) == [[3*int(i == j) for j in range(4)] for i in range(4)]
columns = []
for j in range(4):
    ej = [int(i == j) for i in range(4)]
    cj = [conference[i][j] for i in range(4)]
    alpha = [2*x for x in ej]*2
    beta = [-x+y for x, y in zip(ej, cj)]+[-x-y for x, y in zip(ej, cj)]
    gamma = [-x-y for x, y in zip(alpha, beta)]
    columns.extend((alpha, beta, gamma))
yfactor = transpose(columns)
g = [[4*int(i//3 == j//3)*(3*int(i == j)-1) for j in range(12)] for i in range(12)]
assert mm(transpose(yfactor), yfactor) == g
assert mm(yfactor, transpose(yfactor)) == [[12*int(i == j) for j in range(8)] for i in range(8)]
assert mm(p, transpose(yfactor)) == [[0]*8 for _ in range(4)]
assert any(abs(x) != 1 for row in yfactor for x in row)

tensor_cases = []
for t in (1, 2, 4, 8):
    ht = sylvester(t)
    original = tensor(p, ht)
    n, m = 12*t, 4*t
    # Put the common repetition into consecutive triples.
    permutation = [(j*3+c)*t+z for j in range(4) for z in range(t) for c in range(3)]
    grouped = [[row[idx] for idx in permutation] for row in original]
    assert all(all(abs(v) == 3 for v in blocksums(row)) for row in grouped)
    for deleted in range(t+1):
        retained = [row for i, row in enumerate(original) if i not in range(deleted)]
        inserted = [kronrow(row, ht[fiber]) for fiber in range(deleted) for row in r]
        partial = retained+inserted
        assert len(partial) == m+8*deleted
        gram_check(partial, n)
        energy = 0
        for row in partial:
            sums = blocksums([row[idx] for idx in permutation])
            energy += sum(v*v for v in sums)
        assert energy == m*m*9
        assert len(inserted) == deleted*9
        tensor_cases.append({'t': t, 'deleted': deleted, 'inserted': len(inserted),
                             'row_count': len(partial), 'missing': n-len(partial),
                             'block_bessel_budget': energy, 'saturated': True})
    full = tensor(b, ht)
    gram_check(full, n)
    # Count shared projective rows without presuming exact tensor uniqueness.
    full_set = {tuple(row) for row in full} | {tuple(-x for x in row) for row in full}
    overlap = sum(tuple(row) in full_set for row in original)
    assert overlap == 3*t
    # Near-complete unextendible frame: just one fiber is unrepaired.
    missing = t-1
    near = [row for i, row in enumerate(original) if i not in range(missing)]
    near += [kronrow(row, ht[fiber]) for fiber in range(missing) for row in r]
    assert len(near) == n-8
    tau = ht[-1]
    integral = [kronrow(row, tau) for row in yfactor]
    assert mm(integral, transpose(integral)) == [[n*int(i == j) for j in range(8)] for i in range(8)]
    assert mm(near, transpose(integral)) == [[0]*8 for _ in near]
    near_gram = mm(transpose(near), near)
    residual = [[n*int(i == j)-near_gram[i][j] for j in range(n)] for i in range(n)]
    assert residual == tensor(g, [[x*z for z in tau] for x in tau])
    assert residual == mm(transpose(integral), integral)

report = {'status': 'passed', 'arithmetic': 'exact integer',
          'base_sign_rows_enumerated': 4096,
          'base_deletions': counts,
          'affine_plane_code_words': words,
          'tensor_exchange_cases': tensor_cases,
          'full_completion_deletion_costs': [{'t': t, 'cost': t} for t in (1, 2, 4, 8)],
          'integer_rank8_completion_orders': [12, 24, 48, 96],
          'residual_gram_model': 'Four scaled A2 triangle blocks; exact integer factor verified.',
          'scope': 'Exact finite checks supplement the general Bessel-budget proofs.'}
(HERE/'checks.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'status': 'passed', 'base_sign_rows_enumerated': 4096,
                  'all_four_deletions_complete': True, 'tensor_exchange_cases': len(tensor_cases),
                  'full_completion_costs': [1, 2, 4, 8]}))
