FOUR-PHASE APPROACH AND A QUANTITATIVE FOURIER OBSTRUCTION

quaternary.tex proves the needed classical realification, a signed
complex-structure criterion, and an exact phase-alphabet invariant:
rho4(F)=||F entrywise-fourth||op/n is1 exactly when row/column phases
can turn complexHadF into a quaternary Hadamard matrix.
Normalized squared Frobenius distance from any quaternary unit matrix
is >=(1-rho4)/8, even after all row/column phases and permutations.

For Fourier_m, rho4=sqrt(gcd(m,4)/m). More generally a Dita-type
deformation retaining a Fourier_m block factor has no larger rho4.
This gives a quantitative family-level obstruction to phase
quantization; it does not exclude paths outside that family.

Positive known examples use symmetric conference C: I+iC isquaternary.
Exact Gaussian-integer checks produce BH6/BH14/BH18 and H12/H28/H36.
An arbitrary transported real complex structure is also checked to
need not be monomial, so abstract realification cannot bypass flatness.

check.py uses original standard-library arithmetic, including exact
cyclotomic polynomial remainders for Fourier fourth-power Gram checks.
No external source code or floating point is used for certificates.
All-even-order BH existence is an unresolved sufficient stronger
target; no equivalence with the full Hadamard conjecture is assumed.
Classical morphisms, phase invariants and block families are credited.
No novelty or unknown-order claim, no Lean edits or commits.
