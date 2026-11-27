RESEARCH EXTENSIONS — 4 NOVEMBER 2026

Read paper/extensions.pdf; edit paper/extensions.tex.
The existing manuscript and Lean proof repository have not been changed.
No Git commits were made, and nothing was published or submitted.

WHAT WAS FOUND

1. Quantitative flatness:
   u(n) <= 1 / (sqrt(n) - exp(D log(n)/loglog(n))) eventually, with a
   positive denominator. This keeps the original quantitative gap rate,
   instead of replacing it by an arbitrary fixed power n^epsilon.

2. A stronger quantitative form of the conditioning consequence:
   kappa(n) <= 1 + n^(-1/4) exp(E log(n)/loglog(n)) eventually.
   Its correction is specified as a function of n, strengthening the earlier
   family of fixed-delta statements. The power endpoint is still 1/4.

3. Second-order covering upper bound for r independent bases:
   log ell_m <= (r-1)m log m + r m loglog m + (beta+eta)m eventually,
   for every eta>0, where
   beta = 1 + r log(r-1) - log(r! product_i log(b_i)).
   For 2,10,26 the constant is approximately -0.360981.

4. Maximal determinant:
   D(n)/n^(n/2) >= exp(-exp(E log(n)/loglog(n))) eventually.
   The note gives a route through a published determinant theorem and a
   separate elementary Cauchy--Binet argument.

5. Exact finite experiments, plus a finite radix construction theorem.
   For S(2,10,26), ell_6 = 637399 was verified. This gives an explicit
   logarithmic exponent coefficient 12/19, which is worse than Du--Jiang's
   3/20. No competitive new uniform numerical Hadamard bound is claimed.

The principal exponent tau(p) = O(log(p)/loglog(p)) is NOT improved here.
These are additions and quantitative refinements of consequences. Nothing
here establishes bibliographic priority. A better principal growth rate needs
another ingredient beyond optimizing fixed-monoid sums with the same transfer.

FORMAL STATUS

lean/QuantitativeFlatness.lean proves the quantitative flatness endpoint and
a finite conditioning theorem that preserves the actual gap/error parameters.
It imports the existing project and its permissively licensed dependencies.
There are no new third-party proof-code dependencies or downloads.
The printed axiom audits contain only propext, Classical.choice and Quot.sound.
The conditioning ASYMPTOTIC refinement, second-order entropy theorem and
determinant corollary have paper proofs; complete Lean proofs of those three
asymptotic conclusions are not claimed.

REPRODUCE

From D:\Papers\Hadamard:
  python improvement/experiments/test_covering.py
  python improvement/experiments/covering.py
  python improvement/experiments/entropy.py
  python improvement/lean/check.py
  python improvement/build.py

The Lean check uses the existing local Lean 4.35.0 compiler and the original
project's compiled dependency files, without editing that project or fetching
code. The PDF builder uses the installed TeX Live through WSL on Windows;
pdftotext is also needed. Compile paper/extensions.tex directly with pdfLaTeX
three times if building the standalone mathematical note elsewhere.

DATA AND LIMITATIONS

data/covering.json records exact subset-bitset computations up to 2^22.
When firstMissing is null, the only conclusion is ell_m > cutoff. These
computations are checked against an independent unbounded-coin dynamic
program on smaller ranges. Repetition and distinctness have the same minimum
weight for these monoids because equal terms can be carried to their double.

data/entropy.json contains integer-only multiset-count certificates proving
upper bounds ell_m <= 2^k even for very large N. They do not certify that all
numbers below N are covered. Decimal beta constants are illustrative only.

data/lean-check.json records the kernel check. verification.json records the
paper/data integrity checks and artifact hashes. Intermediate build files and
visual previews are in .build/.

All newly authored code is Apache-2.0. The proof dependency packages retain
their Apache-2.0 or MIT licenses as inventoried in lean/DEPENDENCIES.md and
lean/submission/mathlib-licenses.json in the ORIGINAL repository. Mathematical
sources were read as literature; no research-supplement code was imported.
