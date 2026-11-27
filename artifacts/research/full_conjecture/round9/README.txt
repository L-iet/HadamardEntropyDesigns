NINTH RESEARCH PASS -- 20 November 2026
Human author/responsible maintainer: Joshua Mark
ORCID: https://orcid.org/0009-0003-5905-2382
Original code and notes: Apache-2.0, see ../LICENSE.

PRIMARY ARTIFACTS
rank_rounding.tex/pdf: binary support-rigidity theorem. At N=4mod8,
an exact N-atom target on N-4 bits has binary rank N-4. Its support
intersects any rank-r binary linear code in at mostr+4 atoms. Thus
low-moment-error Walsh candidates can require replacing almost all
atoms. An infinite Paley subsequence makes the claim nonvacuous:
candidate moments tend to zero and feasible-law distance tends to
zero, but every minimal-support/extremal-law distance tends to one.
This is not a failure of moment correction to arbitrary feasible laws.
research.tex/pdf: full report with all branch proofs and scope.

OTHER BRANCHES
nonlinear/: fixed support permits degree<=r-2 full Hadamard encodings
iff its complement affinely spans, ASSUMING a Hadamard matrix exists.
Punctured N-4-bit equal-weight inputs retain a stronger degree barrier.
Near N=2^r-4 their required maximum degree is r-1. The r=4 case is an
explicit exhaustive finite quadratic-clique certificate.
exchanges/: all80 four-bit moves from bad vertices to matching optima
are exact moment-preserving circuits. Collision gain is1/36; the
optimal barrier among ALL continuous feasible paths is1/288.
lattice/: exact modular extension count E=M_q-A under the stated
N=4(q+1), oddq row-count hypotheses. A counts simple exceptional
column pairs. This covers an eight-divisible class, not4mod8.

CHECKS AND PROVENANCE
Run: python research/full_conjecture/round9/build.py
Four final checkers use Python's standard library with exact binary,
rational, modular or integer arithmetic. They check known-order rank
benchmarks, all-support affine orbits, exhaustive finite clique bounds,
circuit moves, and modular counting/correction profiles.
The infinite sequence in rank_rounding uses Paley's published theorem
and the written elementary irrational-rotation proof, not finite tests.
The build reuses ../round3/build.py without changing prior artifacts.
verification.json records hashes, pages and completed checks.
No unlicensed proof code was imported. Mathematical sources and known
construction ingredients are credited. No full conjecture proof,
distribution at an unknown order, novelty clearance, Lean changes,
or Git commits were produced.
