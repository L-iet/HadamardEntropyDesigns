FOURTH RESEARCH PASS -- 20 November 2026
Human author and responsible maintainer: Joshua Mark
ORCID: https://orcid.org/0009-0003-5905-2382
Original code and notes use the Apache-2.0 license in ../LICENSE.
No external proof source code was imported. Literature supplies
mathematical context; derivations and exact checkers are project work.

The prior tensor theorem is preserved at ../round3/geometry/ and
recorded in ../MILESTONES.txt. New results in this directory:

1. tensor_trace.tex/pdf: a simpler tangent-trace proof, complex unitary
   extension for every p>0 except p=2, real subquadratic extension for
   1<p<2, and finite-power quantitative stability estimates.
   In particular the real normalized quartic energy is <3^(1/k) if
   its kth tensor power is locally minimizing. Flatness error in
   normalized squared Frobenius distance is O(1/k).
2. sharpen/activation.tex/pdf: exact least Hessian eigenvalue for all
   powers of the five-dimensional reflection, and examples needing
   three or five copies before instability. Flat factors give seeds
   of admissible initial order 20. Universal two-copy activation fails.
3. exponents/subquadratic_tensor.tex/pdf: complementary factored-direction
   proof in the real subquadratic range, including spectral edge cases.
4. descent/descent.tex: trace-free interaction directions, projection
   obstructions, and exact failure of partial-trace/polar extraction.
5. research.tex/pdf: consolidated report including the trace theorem,
   quantitative corollaries, exact activation and descent limitations.

Build and checks: python research/full_conjecture/round4/build.py
The five checkers use only Python's standard library and exact rational
or integer arithmetic. The build reuses ../round3/build.py's compiler
without changing any prior artifacts. WSL TeX Live is used on Windows;
pdftotext must be available. verification.json records checked hashes.

The proof, not the finite checks, establishes each uniform theorem.
No all-order real Hadamard existence result follows. The complex
one-copy almost-Hadamard conjecture is not settled. Novelty/priority
have not been established. No Lean changes or Git commits were made.
