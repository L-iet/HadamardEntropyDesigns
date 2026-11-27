ROUND 8: NONLINEAR MINIMAL-SEED ENCODINGS

Files
  encoding.tex     TeX fragment, all main statements proved.
  check.py         Original standard-library exact checker.
  encodings.json   Explicit seed labels and Boolean polynomial monomials.
  checks.json      Exact verification summary.
  explore*.py and *_explore.py / quadratic_search.py are exploratory scripts.

Concrete results
1. Exact Paley12 and Paley20 extremal distributions on minimal binary seeds:
   twelve labels out of16 with eleven sign outputs, and twenty labels
   out of32 with nineteen outputs. Collision exactly1/12 and1/20.
   Explicit polynomial outputs are degree<=3, with no numerical fitting.
2. For ANY twelve-atom Hadamard encoding in4bits, at least one output
   requires Boolean algebraic degree>=3. Proof is label-independent:
   binary Hadamard span has dimension11; an all-quadratic encoding would
   force all RM(2,4) restrictions to have even weight. The four excluded
   labels then XORtozero, making an affineplane whose quadratic indicator
   contradicts the required restriction rank. Cubics always suffice.
3. At order20 on5bits, quadratics fail by dimension16<19; displayed
   labels have complement affinely spanning the cube, proving all outputs
   extend cubically. Thus minimum maximum degree is exactly3 at12,20.
4. Sharp affine budgets: H12 on4bits has at most3affine outputs, attained;
   H20 on5bits has at most5, attained. At least8 and14 outputs respectively
   must be nonlinear. The bounds combine binary rank and complement
   orthogonality; they do not depend on a particular row labeling.
5. General narrow-model obstruction: at N=4mod8, an r-bit encoding with
   outputs of degree<=d requires sum_{j<=d}binom(r,j)>=N-1. At minimal
   r=ceil(log2N), degree>=ceil(r/2). Every proper-support injection admits
   degree<=r-1. Fixed algebraic degree cannot represent all such orders.
6. Reusable interpolation criterion: restriction RM(d,r)->functions(S)
   is onto iff no nonzero RM(r-d-1,r) polynomial is supported in S.
   Coupling this with Paley character matrices gives exact nonlinear
   binary-seed laws for classical Paley prime-power orders.

Reproduce
  python research/full_conjecture/round8/nonlinear/check.py
Checks exact Paley Gram matrices; binary rank; all moments of every output;
minimal per-column degrees by exact F2 elimination; explicit labels and
complement affine basis; all140 four-point affineplane indicators.
Polynomial masks in encodings.json: bit i means factor z_i, mask0 is the
constant monomial. Sum selected monomials modulo2, output sign(-1)^f.
Use uniform seed mass1/N on the listed labels, zero elsewhere.

Scope and attribution
The Hadamard orders and quadratic-character formula are classical Paley,
not new existence results. The labeling/degree results are research
lemmas with novelty unestablished. In particular the procedure cannot
supply missing distributions at unknown orders: it still starts from
an existing Hadamard construction.
Primary sources read online:
- R.E.A.C.Paley (1933), On Orthogonal Matrices.
  https://doi.org/10.1002/sapm1933121311
- William P.Orrick, Switching operations for Hadamard matrices.
  https://arxiv.org/abs/math/0507515
No source code downloaded or reused. No Lean code, commits, submissions.
