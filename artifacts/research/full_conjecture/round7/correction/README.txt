Round7 exact moment correction

correction.tex supplies an explicit nonnegative Fourier buffer repair
of any finite sign law to unbiased pairwise independence, with exact
collision identity and TV bound. A computable tiny-error sufficient
condition enters the round6 Hadamard extraction window. A separate
quantization theorem shows why the universal buffer does not rescue a
nonisotropic uniform nearest-order sign-row candidate.

The exact smallest buffer in the affine ansatz is also given; the
universal-buffer obstruction is deliberately NOT asserted for that
smaller buffer or for arbitrary correction methods. Input near-optimal
collision and tiny moments are hypotheses, not proved constructions.

python check_exact.py uses only standard library Fraction arithmetic.
Checks cover weighted perturbation of a known H8 distribution, exact
Fourier cancellation, positivity, normalization, TV, exact collision,
minimal-buffer positivity, extraction window, and a quantized-error
uniform-row counterexample to this universal repair strategy.

No external code or Lean, no commits. New code Apache-2.0 under research
parent LICENSE. Elementary derivation; priority not established.
