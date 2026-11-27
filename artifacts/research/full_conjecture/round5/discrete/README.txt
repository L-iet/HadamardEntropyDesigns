ROUND 5: DISCRETE FIXED-DIMENSION BRIDGE

Files
  rounding.tex     TeX fragment with proofs; include in a document defining
                   theorem, proposition, corollary and loading amsmath,
                   amssymb, amsthm, hyperref.
  check.py         Original Python standard-library exact arithmetic checks.
  checks.json      Output of: python research/full_conjecture/round5/discrete/check.py

Results
1. Constructive collision/moment certificate. For a probability measure on
   n-1 sign bits, let C=sum(weights squared) and E=the squared Frobenius norm
   of its augmented degree-one moment matrix minus identity. If n is even
   and (n^2-4)C > n+E-4/(n-1), the existing support contains n mutually
   orthogonal sign vectors, which are extracted by weighted clique merging.
   For exact pairwise independence this permits a collision deficit below
   1/n of 4/[n(n-1)(n^2-4)]. Single-parity support improves 4 to 16.
   No optimality or novelty claim is made.
2. Sharp forbidden-parity collision bound: for n>=6, n=2 mod4, balanced
   pairwise independent n-1 bits satisfy C<=1/(n+2). It is attained when
   H(n+2) exists. In particular the exact five-bit maximum is 1/8, stronger
   than 1/6 obtained from the general maximum-atom estimate. This supplies
   a sharp benchmark for the relaxation and an independent calibration.
3. Fixed-residue finite-field lifting fails, even for full-rank modular
   seeds at admissible orders. J_n-2I_n is orthogonal mod p when n=4+4pt,
   but its unique sign lift has nonzero Gram correlations 4pt. If p does
   not divide t, it already fails mod p^2. This standard modular construction
   is explicitly attributed; no claim of new modular-Hadamard results.

What remains missing
The certificate does not produce concentrated measures in unknown orders.
The uniform cube satisfies every degree-two equation and all moment-matrix
positivity constraints, but its collision is exponentially too small.
Finite-field solutions likewise require a global sign repair, not ordinary
entrywise Hensel lifting. None of these statements proves the conjecture.

Checks
Exact rational examples n=4,8 perturbing a Hadamard measure with cube mass;
weight merging extracts an n-clique. All five-bit cube orthogonality triangles
are checked absent. Uniform six-column restriction of H8 attains C=1/8.
A second exact five-bit distribution has maximum atom 1/6 and C=7/72,
showing that a stronger collision bound is not a stronger maximum-atom bound.
Six modular seeds for primes 3,5,7 verify admissibility, modular
orthogonality, real failure, and immediate mod-p^2 obstruction.

Primary sources consulted online
- Gavinsky and Pudlak (2016), On the joint entropy of d-wise-independent
  variables. Theorem 3.2 (atom bound) and Section 4 (Hadamard equality).
  https://users.math.cas.cz/~pudlak/pairwise.pdf
- Motzkin and Straus (1965), Maxima for graphs and a new proof of a theorem
  of Turan. Weighted clique merging is classical and reproved in the note.
  https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/maxima-for-graphs-and-a-new-proof-of-a-theorem-of-turan/AC3CC45896B053B75C856F25829CA95C
- Vivian Kuperberg (2015 version), Hadamard matrices modulo p and small
  modular Hadamard matrices. Lemma 2.3 contains J-2I construction.
  https://arxiv.org/abs/1409.0148v4

Only papers were read; no external source code was downloaded or reused.
No Lean code, commits, outside messages or submissions were made.

Equality strengthening (independently checked after the initial delivery)
For n=2 mod4, equality C=1/(n+2) forces uniform mass on exactly n+2
atoms, with a complete bipartite orthogonality graph whose parity classes
have mass 1/2. The pointwise identity v_x^T M v_x=n forces each weight
1/(n+2). A self-contained rank-two residual argument reconstructs two
missing sign columns, yielding H(n+2). Thus equality in the sharp
collision bound is equivalent to existence at the adjacent admissible
order; it is not a weaker existence assertion. No external completion
theorem is used for this two-column case. Checker reconstructs H8 from
all 21 deleted nonconstant column pairs, H16 from all 105 pairs, and
H32 from 12 pairs. All reconstructions use only the retained matrix.
