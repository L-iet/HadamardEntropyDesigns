CONCENTRATION AND RELATIVE-STABILITY EXTENSIONS

All earlier round11 files are unchanged.

concentration.tex / check_concentration.py / concentration_checks.json
- The exact collision maximum over all isotropic laws supported on the
  full k-block source S is1/h^2, not1/h^k. Pair-block marginals must be
  uniform, giving atom<=1/h^2. Classical finite-field slopes A+t_jB attain
  the bound with h^2 uniform atoms. Equality requires an index-one OA.
- Two observed block-character spaces span every2s-seed character via
  products, so this uniform law is a vertex and strict local collision
  maximum of the FULL feasible polytope. A quantitative barrier is proved.
- Under h>2(k-1),k,h powers2, exact TVtoHadmixtures is1-1/k, and sharp
  h^2(1-1/k) row replacement still attains a union of Hadamard blocks.
- h2k: support2n, C1/(2n), TV1-sqrt(2/n). hk^2: supportn^(4/3),
  relativecollisionn^(-1/3), TV1-n^(-1/3). Exact GF4/GF8 checks pass.

relative_stability.tex / check_relative.py / relative_checks.json
- General Plotkin bound removes h>2(k-1): full source orthogonal subsets
  have size<=h floor[h/(h-k+1)] for2<=k<=h.
- Stronger construction: take slopes P containing0, h/2<|P|=k<h, and
  require omitted slopes R to LINEARLY SPAN the additive field space.
  The compressed h^2 support orthogonality graph is exactly h disjoint
  Kh, regardless how close k is to h. Thus if H_k exists, its exact
  distance from all order-kh Hadamard mixtures is1-1/k, while its
  collision is k/h times the global optimum. It remains a strict local
  maximum. R can be chosen when log2h<=h-k<h/2.
- Benchmark h16,k12: omitR{1,2,4,8}, implement GF16modx4+x+1.
  A256-atom exactlyisotropic strict localmaximum on191bits hasC1/256
  versus optimum1/192, and TVdistance EXACT11/12. Upper witness uses
  classical PaleyH12 blockmixing to complete16cliques; all3072 rows and
  every completed Gram are checked exactly. No repair-with-preserved-C
  claim is made because12 does not divide16.
- h8,k5 gives another exact64-atom law and TVlowerbound4/5; noH5-based
  completion is claimed.
- If knownHadk andpowers2h satisfy k/h->1 and log2h<=h-k<h/2, these
  laws have relativecollision->1 yetTV->1. Root supplies the independent
  Paley/irrational-rotation sequence argument; our file states the clean
  conditional regime and exact deficit(h-k)/(k h^2).

Reproduce both newcheckers with Python standardlibrary. Only exact integer
and Fraction arithmetic; finite-field multiplication implemented originally.
Classical finitefieldindex-oneOA and Plotkin bounds are credited:
K.A.Bush(1952), https://doi.org/10.1214/aoms/1177729387
M.Plotkin(1960), https://doi.org/10.1109/TIT.1960.1057584
No external code, oldfile edits, Lean changes, commits or submissions.
Novelty is unestablished; these are obstruction/stability theorems, not
new Hadamard orders or a proof of the conjecture.
