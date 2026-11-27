ROUND 10: QUANTITATIVE NONLINEAR ENCODING BARRIERS

Files
  quantitative.tex  TeX fragment with proofs.
  check.py          Original exact Python standard-library checks.
  checks.json       Full certificates and explicit approximate candidates.

Results
1. Quantitative moment-error floor. For uniform N seed labels, N=4mod8,
   exactly balanced N-4 Boolean outputs of degree<=r-2, and complement
   affine codimension a, at least max(0,2a-3) pairs have nonzero real
   correlation. Augmented squared Frobenius moment error is therefore
   at least32*max(0,2a-3)/N^2. The proof uses binary Gram rank plus the
   graph nullity bound nullity(I+J+Adj(H))<=edges(H)+1.
   For four omitted labels,r>=5, E>=32(2r-9)/N^2.
   This strengthens the exact obstruction to an explicit approximate
   exclusion neighborhood while keeping all assumptions visible.
2. The edge-count bound is sharp at binary-Gram level: odd matchings give
   equality. We do NOT assert actual low-degree laws attain the moment
   bound or matching pattern.
3. Exact minimum support-edit distance to affine-spanning complement is
   r-affdim(T), provided complement size>=r+1. Transfer truth rows along
   these exchanges and repair off-support syndromes: the entire observed
   law and collision remain unchanged, intermediate degree<=r-1 and
   final degree<=r-2. This operation works for arbitrary given truth laws
   and does not require N=4mod8. Benchmarks preserve known Paley laws
   with one exchange atN20 and two atN48.
4. Four-omission Fourier/capacity tradeoff. Plane complement has exactly
   2^(r-2)-1 nonconstant seed Fourier modes; tetrahedral complement has
   5*2^(r-3)-1. The sparser plane case loses two binary bilinear-rank units.
   AtN12 these correspond to3vs9 modes and5vs7 quadratic independentbits.

Reproduce
  python research/full_conjecture/round10/nonlinear/check.py
Checks all32834 labeled graphs at sizes2,4,6 against the nullity bound;
odd-matching equality examples; full exact spectra atseed sizes4,5,6;
explicit balanced low-degree nonisotropic test laws atN28,60
(these are not near-isotropic examples); and minimal support
edits plus exact output-row preservation and Boolean syndrome repair at
known Paley orders20,48. Integer and Fraction arithmetic only.

Scope
The approximate exclusion requires exact balance, equal seed weights,
and the stated degree bound. It does not extend automatically to biased,
nonuniform, or larger-seed candidates. The support exchange improves an
encoding, not the law: it neither produces a missing distribution nor
increases concentration. No new Hadamard order or novelty claim is made.

Primary background
Claude Carlet, Boolean Functions for Cryptography and Coding Theory,
Reed-Muller duality and Boolean degree (facts used here are reproved).
https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf
Paley's quadratic-character matrices supply only known benchmark laws.
No external source code, Lean work, commits, or submissions.
