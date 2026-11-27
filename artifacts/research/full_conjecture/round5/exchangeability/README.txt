Exchangeability research, round 5

exchangeability.tex proves an exact obstruction and characterization:
1. Uniform signed-permutation matrices give a fully consistent symmetric
   hierarchy of vectorized pure orthogonal states with maximally mixed
   one-copy state. Every displayed factor is sparse and nonflat.
2. The two-copy coincidence observable measures F4/n^2 and hence exactly
   the average nonnegative flatness defect. It vanishes only on flat
   factors; one-copy entropy cannot substitute for this witness.
3. Infinite exchangeability plus full-swap purity, minimal row-swap
   purity, realness-square constraints, and minimal coincidence is
   equivalent to real Hadamard existence. This is a reformulation, not
   a feasibility or existence proof. Finite symmetry is not substituted
   for infinite extendibility.

Run python check_exact.py (standard library, Fraction arithmetic).
It constructs exact one- and two-copy moments of all 48 signed
permutations in O(3), verifies rho1=I/9, swap=1, row-swap=1/3,
coincidence=1/3 > 1/9, and compares with the genuine flat order-4
Sylvester matrix, whose coincidence is 1/16.

No downloaded external code was used. New code Apache-2.0 under the
research parent LICENSE. Primary quantum de Finetti reference is Caves,
Fuchs and Schack, arXiv quant-ph/0104088; its consistency-definition
erratum is explicitly acknowledged. Priority of these elementary
reformulations has not been established. No Lean or git commits.
