ROUND 9: FIXED-SUPPORT NONLINEAR CRITERIA

Files
  support.tex   TeX fragment with algebraic proofs and finite classification.
  check.py      Exact original Python standard-library checker.
  checks.json   Rank, graph, witness, and syndrome-repair certificates.
  search*.py    Exploratory exhaustive clique searches.

Main new results
1. Exact criterion, conditional only on an existing H_N:
   N=4mod8, seedbits r>=4. A fixed N-label support S permits a full
   degree<=r-2 Hadamard observable basis iff its omitted labels T affinely
   span F2^r. This is necessary, not merely sufficient interpolation.
2. Binary restriction-code radical formula. Put a=r-affdim(T), C=the
   restriction of RM(r-2,r) toS. Its even subcode has dimension N-a-1,
   radical dimension a+1, and binary bilinear rank N-2a-2. Real moment
   orthogonality implies a prescribed nonsingular or corank-one binary
   Gram, giving the criterion and punctured variants.
3. Constructive nonlinear support switching: arbitrarily relabel existing
   Hadamard rows onto a support with affine-spanning complement; then repair
   each truth table only at an affine basis of omitted labels to cancel
   its affine syndromes. Degree becomes<=r-2 without changing any observed
   row or moment. A single omitted-point parity repair gives degree<=r-1
   on ANY proper support. Verified at orders12,20,60.
4. Sharp degree saturation: for minimal seedlength r, an encoding of a
   given H_N with maxdegree<=r-2 exists iff 2^r-N>=r+1. If the deficit
   is<=r, optimal maximum degree is exactlyr-1. In particular any H_(2^r-4)
   requires degree exactlyr-1, r>=4.
5. Extraction input audit: N equal-weight atoms carrying only N-4 unbiased
   pairwise-independent bits still require sum_{j<=d}binom(r,j)>=N-3,
   hence degree>=ceil(r/2) on minimal seeds. In the degree<=r-2 model,
   the omitted labels must have affine codimension<=1. Thus N=2^r-4,
   r>=5 already requires degree r-1 WITHOUT any completion assumption.
6. Sharp finite real-orthogonality obstruction at12 labels in4bits:
   maximum quadratic bits is5 when complement is an affineplane, and7
   when complement is an affine-independent tetrahedron. This rules out
   the8-bit extraction target for EVERY labeling, completing the r4
   boundary case of the preceding degree-saturation family.

Reproduce
  python research/full_conjecture/round9/nonlinear/check.py
All ranks, codewords, weights, and graph searches are exact. Clique graphs
have126 or238 vertices; search excludes6 or8 cliques, respectively, and
verifies matching5 or7 witnesses, including explicit quadratic monomials.
No heuristic pruning or floating-point optimization is used. The theorem
reduces all12-label supports to two affine orbits, so these finite searches
exhaust the model. checks.json records graph hashes and search-state counts.

Scope
These are rigorous narrow-model criteria, obstructions, and explicit label
repair operations. Upper constructions still start with known Hadamard
matrices; no missing distribution or new Hadamard order is asserted.
The lower bounds assume equal N-atom weights and minimal binary seed,
so they do not automatically constrain nonuniform near-extremal inputs,
larger seeds, or approximate moments. Novelty has not been established.

Primary background read
Claude Carlet, Boolean Functions for Cryptography and Coding Theory:
Reed-Muller spaces, duality, and Boolean degree. Required facts reproved.
https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf
Classical Paley quadratic-character construction is used only to provide
known benchmark matrices at orders12,20,60 (primes11,19,59).
No external source code, Lean work, commits, or submissions.
