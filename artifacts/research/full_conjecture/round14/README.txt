FOURTEENTH PASS: CONSTRUCTIVE CERTIFICATES AND ESCAPE OBSTRUCTIONS

python build.py reruns the four branch checkers, assembles two papers,
compiles them three times with strict checks, and hashes the artifacts.
Windows uses the existing WSL TeX installation.

phase_rounding.tex/pdf:
For any even-order unit-modulus matrix F, let
 D=n^4-||(F entrywise-fourth)(F entrywise-fourth)*||F^2
and beta=max off-diagonal Gram magnitude.
If beta+sqrt(D/n)<sqrt2, an explicit pivot dephasing and nearest-root
rounding produces a quaternary Hadamard matrix. In particular exact
complex Hadamard F suffices when D<2n, or 1-rho4^4<2/n^3.
All pivot scores and an exact Gram certificate take O(n^3) scalar
operations. No all-order input satisfying this criterion is constructed.

research.tex/pdf:
Combines phase rounding with weighing-support completion, exact local
energy traps, and two-column completion via residual qubit geometry.
Each branch directory contains its own proof, checker and limitations.
The weighing result proves real completion iff sign completion on the
prescribed two-zero support, and a sharp six-fill bound beyond order four.
The two-column result proves automatic quaternary completion using the
classical real codimension-four theorem. Neither provides the initial
large partial matrix at an unknown order.

The full conjecture and novelty remain unresolved. No unknown Hadamard
order is claimed, no Lean is edited, and no commits are made.
Code is original standard-library Python under ../LICENSE (Apache-2.0).
No third-party proof implementation is imported.
