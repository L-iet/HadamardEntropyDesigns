Round11 exact self-dual-neighbor landscape

Run python census.py. Input is the original round10/code_traps/search.json
certificate. Only standard library and original adjacent project code
are used. Graycode enumerates all524288 normalized signs, grouped by
projective syndrome. MacWilliams transform of a 25-word evaluation-dual
code completes all2441406 neighbors without a full5^10 syndrome scan.
All42 improving neighbors are separately rebuilt and their Hadamard
Gram and complete sign counts checked. census.json has all profiles.

Result: exactly42 improving neighbors, allwith20 signs;10 retain10old
rows,32 retain9. Exactly2678 tiesat12. This one terminal12-frame is
not a local signcount maximum, but improving requires >=2 rowloss.
No universal landscape or unknown-order existence claim is made.

landscape.tex/PDF present the identity, exact counts, scope and primary
MacWilliams reference. No Lean or commits. New code Apache-2.0 under
research parent LICENSE; no external code imported. Priority unknown.

Additional retention.tex fragment and check_retention.py give the exact
generalized-Hamming-weight profile of the old-row evaluation code.
All4096 column subsets checked: d_h=[2,3,4,6,7,8,9,10,11,12], maximum
oldrows retained=[10,9,8,6,5,4,3,2,1,0]. retention.json stores paritycheck
matrix and minimum-support witnesses. This is classical weight-hierarchy
theory interpreted as exact resource geometry, not an improvement guarantee.
