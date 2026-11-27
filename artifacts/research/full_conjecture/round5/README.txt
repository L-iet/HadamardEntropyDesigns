FIFTH RESEARCH PASS -- 20 November 2026
Human author and responsible maintainer: Joshua Mark
ORCID: https://orcid.org/0009-0003-5905-2382
Original notes and code use ../LICENSE (Apache-2.0).

PRIMARY RESULT
For d>=2 unbiased pairwise-independent sign bits, let
N=4*ceil((d+1)/4). Collision probability is at most 1/N.
Consequently collision entropy and Shannon entropy are at least log N.
Equality forces a uniform law on N atoms, and its augmented matrix
can be explicitly completed in at most three columns to a Hadamard
matrix of order N. Conversely a Hadamard matrix of order N attains
both entropy bounds. The proof uses second moments, parity and Bessel
inequality; no external completion classification is needed for it.

Main short paper: collision_entropy.tex/pdf.
Broader extraction/entropy paper: rounding_entropy.tex/pdf.
Full report: research.tex/pdf.
Working source for the main theorem: residue.tex.
Independent proof audit: exchangeability/residue_review.txt.

ADDITIONAL RESULTS
discrete/rounding.tex: constructive approximate-moment/collision
certificate extracting a Hadamard matrix within the original support;
sharp forbidden-parity bound and rank-two equality completion;
nonsingular modular seeds that do not admit entrywise sign lifts.
entropy.tex: positive Shannon-entropy windows for exact rounding,
a saturated-min-entropy counterexample, elementary rank-one completion,
and a larger existence window using Verheiden's seven-row theorem.
completion.tex: a classical unextendible 4x12 partial matrix shows that
the seven-missing-row completion boundary is sharp in general.
invariant/: diagonal rigidity, capacity blindness, and a forbidden-order
quartic energy gap.
exchangeability/: a signed-permutation averaging counterexample and
an exact quantum moment formulation retaining the flatness defect.

VALIDATION
Run: python research/full_conjecture/round5/build.py
Six standard-library checkers use exact rational or integer arithmetic.
They check all residue classes, explicit two/three-column completions,
the rounding extraction, modular counterexamples, diagonal balancing,
capacity inequalities, and quantum expectation values.
The compiler reuses the project's ../round3/build.py without editing it.
verification.json records hashes, scopes, successful checks and pages.
The mathematical proofs establish the universal theorems. The finite
checks provide supporting evidence and do not replace the proofs.

PROVENANCE AND LIMITS
No external proof code was copied. Primary mathematical papers are
cited where used. Verheiden1978 Theorem4.5 was read in its original scan;
its computational classification has not been independently rerun.
The quantum moment reformulation uses complex quantum de Finetti
(Caves--Fuchs--Schack2002), followed by explicit reality constraints.
Downloaded reading material and exploratory files are confined to
.build/ and are not part of the original-code provenance claim.

This pass does not prove existence of a bound-attaining distribution
in every admissible dimension. Such attainment is equivalent to the
Hadamard conjecture. Targeted prior-art searches are not a novelty
clearance; comparison with weighted orthogonal arrays and Delsarte
bounds is still required. No Lean work or Git commits were made.
