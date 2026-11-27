CONSTRUCTIVE PHASE ROUNDING

For a complex Hadamard F of order n put M=F entrywise-fourth and
D=n^4-||MM*||F^2. This gauge-invariant nonnegative deficit controls
an explicit finite dephasing/rounding algorithm.

If D<2n for even n (or D<n in general), one of the n^2 row-column
pivot dephasings rounds to an exact quaternary Hadamard matrix.
It suffices to have 1-rho4(F)^4<2/n^3 at even n.
All pivot errors can be computed in O(n^3) exact scalar operations.

Proof: mean fourth-power error is exactly 2D/n^2; nearest-fourth-root
squared error is at most one quarter of that error. For the selected
pivot eta<=D/(2n^2). Off-diagonal rounded Gram entries have magnitude
at most sqrt(2n eta). At even n a nonzero Gaussian-integer Gram entry
has magnitude at least sqrt2, so eta<1/n forces exact orthogonality.

This improves the initial more conservative operator-norm threshold
using the parity observation independently supplied by the phase agent.
It is a sufficient rounding theorem, not an all-order input construction.
The n^-3 normalized deficit is dimension dependent and is not guaranteed
by ordinary small average error or the previously excluded Fourier blocks.

check.py verifies Gaussian-rational nontrivial 4x4 complex Hadamard
deformations, all pivot identities, rounding bounds and successful
threshold certificates. Original standard-library Python, Apache-2.0.
Paper proof covers general complex inputs. No priority claim.
