CONTINUOUS PHASE ESCAPE FROM EVERY REAL NON-HADAMARD SIGN MATRIX

main.tex proves that the Gram-energy Hessian on the complex phase torus
is positive semidefinite at a real sign matrix iff that matrix is Hadamard.
Every real non-Hadamard sign input therefore has a negative phase direction.
The proof provides an exact algorithm yielding an integer phase direction.

Constant-energy unitary mixing of two real sign columns or rows provides
zero-curvature directions. Unless their Hessian images vanish, an explicit
linear combination has negative curvature. If all vanish, H is a scaled
partial isometry. A left-kernel/right-kernel outer product then gives a
negative direction unless H is already a full Hadamard matrix.
An exact Cayley phase step with dyadic backtracking converts the
direction into a finite Gaussian-rational strictly decreasing matrix.

check.py independently constructs the integer Hessian by rectangle sums.
It checks all 512 normalized order-four sign matrices (6 Hadamards and
506 strict saddles), the certified trap8 and its order16 tensor lift,
and two singular tight examples exercising the nullspace case.
The four saved cases also have exact accepted finite-step energies.
No floating point or numerical eigensolver is used.

This removes the earlier one/two-entry traps only by allowing continuous
complex phases. No convergence, four-phase limit, or all-order real
Hadamard construction follows. The phase-flow literature is credited
in the proof; priority for this statement remains unverified.
Original standard-library Python under ../../LICENSE, Apache-2.0.
