EIGHTH RESEARCH PASS -- 20 November 2026
Human author/responsible maintainer: Joshua Mark
ORCID: https://orcid.org/0009-0003-5905-2382
Original notes and code: Apache-2.0, see ../LICENSE.

PRIMARY BENCHMARKS
nonlinear_encodings.tex/pdf and nonlinear/: exact minimal-seed encodings
of classical Paley H12/H20. Minimum maximum Boolean ANF degree is three
in both cases; maximum affine observable counts are respectively3and5.
For full normalized H(N), N=4mod8, minimal seed lengthr forces maximum
degree at leastceil(r/2). This is a statement about allN-1observables of
the full matrix; the sharp cubic benchmark should not silently be
transferred to a smaller punctured observation set.
encodings.json stores actual labels and Boolean extension polynomials.
Paley existence and the binary-code viewpoint are explicitly credited.

ADAPTIVE CORRECTION
weights/: right-inverse moment correction with explicit rank and
positivity margin. No reweighting on a failed uniformN-point support
can restore exact moments in the N-4-bit target. The sufficient
conditioning/concentration assumptions do not construct their input.

OTHER DIRECTIONS
renyi_transition.tex/pdf: complete analytic26-vertex hull description
of the four-bit moment polytope and exact entropy-order diagram.
Global minimizers switch at unique alpha* in(6,7), while both families
remain strict local minima for every finite alpha>1. This does not
justify entropy-order continuation as a global solver.
lattice/: exact one-row deletion/five-row insertion repair; odd-kernel
minimum changes40toinfinity under successful augmentation. A general
sign-rounding bound is proved and its limitations calibrated.
research.tex/pdf consolidates all branches.

VALIDATION
Run: python research/full_conjecture/round8/build.py
Four final checkers use Python's standard library and exact integer,
binary or rational arithmetic. They check the nonlinear encodings,
Reed-Muller restriction certificates, adaptive correction, all4368
candidate active sets of the small polytope, exact gradient exposure,
and the finite lattice/augmentation certificates.
The real-parameter entropy theorem rests on the analytic proof.
The build reuses ../round3/build.py's compiler without editing it.
verification.json records successful checks, pages and file hashes.

No external proof code was copied; mathematical sources are cited.
No distribution at an unknown Hadamard order, full-conjecture proof,
priority clearance, Lean changes or Git commits were produced.
