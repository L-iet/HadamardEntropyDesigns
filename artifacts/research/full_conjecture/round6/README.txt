SIXTH RESEARCH PASS -- 20 November 2026
Human author/responsible maintainer: Joshua Mark
ORCID: https://orcid.org/0009-0003-5905-2382
Original code and notes: Apache-2.0, see ../LICENSE.

The fifth-pass entropy theorem is explicitly preserved in
../MILESTONES.txt and ../round5/collision_entropy.tex/pdf.

THIS PASS
collision_stability.tex/pdf: near-equality extraction for n=1 mod4.
If an exactly isotropic law on n-1 bits has collision deficit at most
1/[1024(n+3)^4], select exactly n+3 heavy atoms and uniformize them.
Integer moment rounding preserves exact isotropy and gives H(n+3).
This is conditional on the near-extremal input, not its construction.

attainment/: explicit strict local collision maxima at four/five bits;
an infinite family at admissible orders with arbitrarily poor ratio to
the known global optimum, explicit local radii and escape barriers.

symmetry.tex: full coordinate permutation symmetry prevents equality
for every d>=5; symmetric collision maxima are Theta(d^-2) and
Shannon entropy is at least (d-1)log2-log(d+1). No infinite deFinetti
assumption is used. check_symmetry.py exactly optimizes finite slice
moment polytopes and checks the algebra supporting the bounds.

completion/: sharp L<=k*s^2 exchange budget for odd repeated blocks;
explicit affine-plane repair and a family with one-row augmentation
but full-completion deletion cost growing linearly. Classical Scarpis
construction is credited, and an explicit rank-eight residual Gram
example separates integral and sign completions.

research.tex/pdf consolidates all four branches with scope statements.

REPRODUCE
python research/full_conjecture/round6/build.py
Four final checkers use exact integer/rational arithmetic and only
Python's standard library. The build reuses ../round3/build.py's
warning-checking compiler without changing prior files.
verification.json records all covered hashes and completed checks.
The universal statements rest on written proofs; the finite tests
are supporting checks. Independent adversarial reviews checked the
stability and symmetry arguments.

No unlicensed proof source code was imported, no Lean was written,
and no Git commit was made. Existing special-family constructions
are distinguished from independently derived bounds. Novelty remains
unestablished. No full Hadamard-conjecture proof or universal
near-extremal distribution construction is claimed.
