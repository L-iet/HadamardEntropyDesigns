MOMENT-SEMIGROUP RESEARCH PASS

All files are confined to this new moments/ directory.
No Lean work, commits, external messages or external proof-code imports.

Read progress.tex for complete elementary proofs. It is a TeX fragment
using the main research notebook's proposition/proof environments and
macros; it can be included as a section in that notebook.

MAIN ACTIONABLE RESULT

Every saturated Hadamard orthogonal array OA(N,N-1,2,2), N>=8, is
isolated under every individual translated coordinate-subcube parity
move of dimension >=3, including any integer multiple of such a move.
Its rows have Hamming distance N/2>=4; either side of a cube parity move
contains a pair at Hamming distance two. Consequently no orientation
can subtract only from supported patterns.

This closes a specific tempting algorithmic approach: the integer-kernel
cube basis cannot be used as a positivity-preserving Markov basis at the
target. The obstruction persists even if all translations and all cube
dimensions are allowed.

There is nevertheless a non-coordinate degree-four trade at OA(8,7):
  remove masks [0,85,102,51], add [119,34,17,68].
Both endpoints satisfy all moments and are cube-isolated. The trade is
derived from a classical closed-quadruple row transformation, not claimed
as a new construction. It identifies the richer sort of move needed.

OTHER PROVED RESULTS

1. Positive unbiased pairwise-independent designs supported in weights
   <=K require K>=ceil((d+1)/2), sharply. Catalan-shell constructions
   attain this maximum-weight bound at N=2*binom(2 floor(d/2),floor(d/2)).

2. Thus using only the existing ORIGIN-ANCHORED cube basis through order
   K requires K linear in d for positivity conversion. This latter claim
   does NOT exclude translated small-dimensional cubes at high weights.

3. Exact monotone triple-only conversion of the canonical signed design:
   d=4 feasible iff L=N/4>=2; d=5 feasible iff 3 divides L; d>=6 impossible.
   These are restrictions on a move strategy, not existence obstructions.

4. Full coordinate-permutation symmetry forces N=Theta(2^d/sqrt d).
   The lower bound follows from a central Hamming-weight orbit selected
   by the exact variance d/4; the Catalan-shell upper bound matches order.
   Thus averaging over all coordinates cannot retain saturated N=d+1
   for sufficiently large d (the small case OA(4,3) is symmetric).

5. For fixed d, all central-ray holes disappear by an explicit threshold
   C_d<3(d+1)^2. This follows by concatenating arrays from one Sylvester
   and one 3-power Paley order, then applying the two-generator Frobenius
   theorem. No use of the current multibase asymptotic result is needed.
   The bound remains far from the diagonal N=d+1.

CHECKS

  python research/full_conjecture/moments/check.py

No external Python dependencies. All arithmetic is exact. The report
certificates.json contains endpoint counts, the non-cube trade, all 939
face checks, shell identities through d=40, low-dimensional explicit
array checks, triple witnesses, and conductor examples through d=999.

LITERATURE / NOVELTY

The derivations in this pass are not claimed novel. A related recent
primary paper was located: Ruwan C. Karunanayaka, "Catalan Bounds for
Symmetric Strength-Two Orthogonal Arrays", Journal of Combinatorial
Designs, DOI 10.1002/jcd.70039. It studies symmetric shell constructions
and an exact minimum-run conjecture. Our maximum-weight objective is
different, and our symmetry theorem establishes growth order only.
No external research code from that paper was copied.

OPEN NEXT STEP

Study a positivity-preserving move family containing general closed-
quadruple/non-coordinate trades. A proof of integer-kernel generation
or connectivity of already nonempty fibers will not establish existence
at N=d+1. A useful theorem must give a positive construction or a
monotone repair argument that survives the cube-isolated endpoints.
