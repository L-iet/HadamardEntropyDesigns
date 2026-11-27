Subquadratic extension, 20 November 2026

Main result: for every real 1<p<2, tensor-stable local maxima of the
entrywise p-energy on O(n) are exactly scaled real Hadamard matrices.
For a nonflat critical matrix with no zero entries, some finite tensor
power has a strictly positive tangent-Hessian direction. Negative or
singular critical matrices already destabilize at tensor square.

The proof independently treats zero entries, the indefinite spectrum,
and singular positive semidefinite critical matrices. No positivity
assumption is hidden in the ratio averaging step.

The endpoint p=1 fails: U=2J/n-I, n>4, is nonflat and every tensor power
is a strict local maximum. At p=2 all matrices have constant energy.
The factored proof here covers real matrices and their phase/permutation
equivalents. A separate companion tensor_trace.tex supplies the full
complex unitary tensor-stability characterization by tangent traces.
No prescribed-dimension existence conclusion follows. Priority unknown.

Run: python check_exact.py
This uses only Python's standard library and exact rational arithmetic.
For p=3/2, n=10, it obtains alpha=beta=49/34 and a positive tensor-square
Hessian bracket 89/2312. For p=4/3, n=18, it obtains alpha=beta=107/44
and bracket 5641/5808. The code checks all symmetric/skew trace sums,
orthogonality, criticality, positivity of M, and the selected ratios.
These finite checks support but do not replace the general proof.

Run: python check_complex.py
Independent Gaussian rational arithmetic checks the complete complex
tangent Hessian trace at p=4,n=3 with nonreal phases, and p=1,n=5 for
a real Householder seed. The p1 seed has rho=35/33 and acquires positive
complex tangent trace at tensor exponent 12, consistent with stability
in the smaller real orthogonal group but not the unitary group.

No external code was used. New code is Apache-2.0; see the parent research
LICENSE. Existing mathematical literature is cited in the TeX.
