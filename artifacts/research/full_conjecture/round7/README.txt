SEVENTH RESEARCH PASS -- 20 November 2026
Human author/responsible maintainer: Joshua Mark
ORCID: https://orcid.org/0009-0003-5905-2382
Original notes/code: Apache-2.0, see ../LICENSE.

The missing distribution is still the objective. This pass constructs
an escape in a special family, derives exact corrections, and tests
which proposed models can reach the earlier extraction window.

ARTIFACTS
research.tex/pdf: full report with all branch proofs and limitations.
code_escape.tex/pdf: explicit nonlocal escape from every trap in the
round6 infinite character family. The endpoint is an optimal2h-atom
law; support overlap h is maximal and the direct straight bridge has
optimal collision loss1/(2h^3). Character rewiring preserves moments
and never decreases collision at jump endpoints. This is a special
power-of-two family, not all-order Hadamard existence.

correction/: exact nonnegative Fourier correction of arbitrary input
laws, with collision identity and total-variation bounds. Tiny moment
error plus sufficiently high input collision gives exact extraction.
buffer_obstruction.tex: even the MINIMAL feasible buffer in the same
affine family cannot repair a nonisotropic uniformN-point candidate
into the required window for multiples N>=20. This strengthens the
universal-buffer limitation and leaves other correction ansatzes open.

character_rigidity.tex: A+A coverage forces uniformity of an arbitrary
seed law with fixed linear observed characters. Missing directions
give exact hyperplane compression. The smallest binary seed cannot
yield the desired non-power-of-two support, even with arbitrary weights.

repair/: odd-integer witness budgets, arithmetic feasibility criterion,
and explicit separation between an odd kernel vector and a sign row.

REPRODUCE AND PROVENANCE
Run: python research/full_conjecture/round7/build.py
Five final checkers use exact rational/integer arithmetic and Python's
standard library. The build reuses ../round3/build.py's compiler without
changing earlier artifacts. verification.json records checked hashes.
Mathematical proofs establish the uniform results; finite checks support
them. No unlicensed source code was imported. Classical character and
lattice mechanisms are cited and distinguished from present deductions.
No bibliographic novelty clearance, universal attainment proof, Lean
formalization, or Git commit is claimed.
