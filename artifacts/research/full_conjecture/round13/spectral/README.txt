ROUND 13: DISCRETE SPECTRAL QUANTIZATION AND CERTIFIED REPAIR

Files
  rank_two.tex   TeX fragment with complete proofs.
  check.py       Original standard-library exact checker.
  checks.json    Exact matrices/ranks/energies/determinants summary.

Main results
1. For signH of order n divisible4 and E=HH^T-nI of nonzero REALrank2,
   the complete possible defect-energy list is
     ||E||F^2=8A(n-A),  integer1<=A<=n/2.
   Eigenvalues are +/-2sqrt(A(n-A)); determinant magnitude is
     n^((n-2)/2)(n-2A).
   Proof: rank2+trace0, determinant integer-square, rational square root
   of an integer is integer, and sign-inner-product parity. Every energy
   is realized by flipping A entries in one row of an existingHad_n.
2. Stronger energy-only rounding: ||E||F^2=8(n-1) forces a UNIQUE
   one-entry Hadamard repair, even WITHOUT rank assumption. Row parity
   forces the defect graph to be a star with correlations+/-2; the other
   n-1 rows have an integer rank-one complement giving the missing sign
   row, which differs in one entry. This is an explicit repair algorithm.
3. Thus rank(E)<=2 plus energy<=8(n-1) certifies Hadamardness or exact
   one-entry repair. This is a genuine sufficient completion criterion.
4. Rank2 alone is insufficient for one-row or one-column repair. Flipping
   a2x2 all-positive rectangle in WalshH8 or PaleyH12 gives rank2defect
   K2,2 orK2,4. Both require exactly4 entry changes and at least2rows and
   2columns changed; the order12 counterexample is nonsingular.
5. A general weighted-defect-graph lower bound certifies entryrepairbudget:
   sum_edges(w_ij|E_ij|)/(2 max_weighted_degree).
6. A rectangular rank-one flip of Hadamard has areaA<=n and energy
   8A(n-A), or preserves Hadamardness atA=n. This explains the examples
   but is NOT asserted to classify every rank-two-defect sign matrix.

Reproduce
  python research/full_conjecture/round13/spectral/check.py
All512 normalized4x4 sign matrices checked; row/column sign operations
cover every4x4 matrix up to the invariants used. There are168rank2 cases
and96 unique one-entry repairs atenergy24. Checks every possibleA for
orders8,12; exact rational ranks; Bareiss integer determinants; integer
missing-row repair; uniqueness over all single-entry flips; both row and
column defect graphs; sharp4-entry lower bounds and inverseflip repairs.

Scope
The threshold criterion begins with a sign matrix meeting its rank/energy
hypotheses. No method constructing one at everyadmissible order is proved.
Real polar orthogonalization alone does not preserve signentries. No new
Hadamard order, novelty assertion, Lean formalization, or gitcommit.

Primary background consulted
WilliamP.Orrick, Switching operations for Hadamard matrices.
https://arxiv.org/abs/math/0507515
Classical Walsh/Paley matrices supply only known benchmark instances.
No external source code downloaded or reused. Priorroundfiles untouched.
