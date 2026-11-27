Round6 quantitative residue-one stability

stability.tex proves the exact nonnegative deficit decomposition for
n=1 mod4 and a concrete extraction theorem: if an exactly isotropic
distribution has collision within 1/(1024(n+3)^4) of 1/(n+3), select
the atoms whose weights are within relative 1/(4(n+3)) of uniform.
There are exactly n+3 of them; integer rounding forces their uniform
distribution to remain exactly isotropic, and the rank3 tetrahedral
completion gives a Hadamard matrix. No near-optimal distribution is
assumed to exist unconditionally. Constants are conservative.

python check_exact.py uses standard-library Fraction arithmetic on
a small mixture of H8-derived and uniform 4-cube distributions. It
checks the defect decomposition, pointwise identity, extraction and
exact isotropy, and shows naive deletion/renormalization breaks balance.

No external code, no Lean, no commits. New code Apache-2.0 under the
research parent LICENSE. Priority unestablished. This is an additional
stability theorem for the round5 residue bound, not an HC proof.
