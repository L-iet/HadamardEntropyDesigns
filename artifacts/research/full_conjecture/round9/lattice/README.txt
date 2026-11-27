Modular sign lifting with an exact column-pair correction
20 November 2026, bounded research pass

lattice.tex proves the main reusable result:
If N=4(q+1), q>=3 odd, and P has r>4(q+1)^2/q^2 orthogonal sign rows,
then exact sign-extension classes equal modular-q sign classes minus
the number of column pairs whose absolute correlation is r-2.
Each spurious modular class is exactly two flips away from one old row.
Hence a finite group-algebra/Fourier coefficient plus an O(rN^2)
column statistic counts the actual real extensions exactly.

Checks include a NONZERO correction example at N16,q3,r8:
group-algebra constant coefficient88; modular classes44; correction8;
exact classes36. Constant coefficient is independently computed by
integer group-algebra multiplication and modular Gaussian enumeration.

For the N24 benchmark frames, modulo5 candidate counts are exactly
0,0,2,16, and all column-pair corrections vanish. Modulo3 instead
gives72,76,72,182 classes, showing the importance of the modulus.
The terminal12-row frame passes odd-integer parity feasibility yet
fails sign-residue feasibility modulo5.

A general modular population/energy first-moment bound is also proved.
No automatic positivity or universal Hadamard construction is claimed.

Primary source for classical code enumerator/Fourier context:
Jessie MacWilliams (1963), A Theorem on the Distribution of Weights
in a Systematic Code, DOI10.1002/j.1538-7305.1963.tb04003.x
https://www.terpconnect.umd.edu/~abarg/ECC/macwilliams1963.pdf
The specific lifting proof is independently derived; novelty has not
been established. No external code was downloaded or imported.

check.py is standalone Python standard-library code, exact integer
arithmetic throughout. Run python check.py to regenerate checks.json.
No Lean or git commits.
