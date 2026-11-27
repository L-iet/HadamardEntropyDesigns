TENTH RESEARCH PASS

research.tex/pdf: combined proofs and exact known-order experiments.
code_pivots.tex/pdf: short account of the global code model and pivot.
build.py: reruns exact branch checks, builds papers, validates typesetting
and records source/PDF hashes in verification.json.

RESULTS
codes/: for N=4q, q odd, modularly orthogonal sign classes are exactly
orthogonal within each sign-product parity. If both parities occur,
each has at most four classes. A self-orthogonal module with five
orthogonal sign rows thus has a completely compatible set of sign words.
An exact extension outside a prime-field self-dual code gives a
self-dual neighbor preserving every old sign row. An exact known H20
benchmark raises the sign count8 to20 in one code pivot.
This does not prove large counts at unknown orders, nor allow a
terminal real partial frame to be extended without row replacement.
An exact restricted-neighbor incidence identity gives an explicit
surplus condition for some sign-count-improving neighbor. With a
codimension-one retained span, the entire modular sign pool splits
between exactly two codes; its exact count predicts the other code.

code_traps/: a second self-dual code has twelve orthogonal sign classes
spanning the full code and admits no new sign row, even after deleting
one old row. Two specified row deletions unlock ten new rows and a full
H20 through one code pivot. Exhaustive enumeration of 524288 normalized
signs proves two deletions are minimal. Its retained-rank-nine space has
modular pool22, shared classes10, and the two code counts are12 and20.
This is a known-order benchmark, not an all-order escape theorem.

modular/: the correction E=M_q-r is exact at N=4q, q odd, r>=5.
At four rows a closed quadruple adds exactly four false classes.
Together with the ninth pass this handles both residue classes mod8,
but a count surplus remains unproved.

exchanges/: elementary exact nullspace endpoint moves concentrate a
law until a vertex with no collision loss. This can stop at a bad
vertex. A sharp selected-target straight-bridge barrier is derived;
an exact counterexample prevents interpreting it as a global barrier.
The convex endpoint principle is classical, with provenance credited.

nonlinear/: exactly balanced uniform low-degree candidates have
squared Frobenius moment error >=32*max(0,2a-3)/N^2, where a is the
affine codimension of the omitted labels. Minimum support relabeling
cost and exact small Fourier tradeoffs are also established.
These are restricted-model bounds, not universal impossibility results.

SCOPE AND PROVENANCE
Original checkers use standard-library exact arithmetic. Mathematical
primary sources are credited; no third-party proof code was imported.
No full conjecture proof, unknown-order matrix, priority clearance,
Lean changes, publication, or Git commits were produced.
Earlier research artifacts are unchanged.
