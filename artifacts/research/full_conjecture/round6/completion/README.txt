Odd-block exchange budgets and an explicit completion route
20 November 2026, bounded research pass

completion.tex is a TeX section fragment with three main ingredients:
* If P=K_m tensor 1_s (s odd), retaining m-k original rows allows
  at most k*s^2 inserted orthogonal sign rows. Full completion needs
  k >= ceil(m/(s+1)). This is proved by blockwise Bessel and parity.
* The classical 4x12 seed is repaired by deleting any one row and
  inserting the nine affine-plane F3 words. All 82 antipodal candidate
  classes are classified exactly; any completion gives OA(9,4,3,2).
* For P_t=(H4 tensor 1_3) tensor H_t, one-step augmentation cost is1,
  but full-completion deletion cost is exactly t. For each k<=t the
  full exchange frontier L=9k is attained by independent fiber repair.
  Every intermediate is unextendible. In particular k=t-1 gives
  unextendible (12t-8)x12t partial matrices at unbounded orders.
* The rank-eight residual Gram is four scaled A2 triangle blocks and
  has an explicit INTEGER 8-row orthogonal completion, despite not
  allowing even one sign completion row. The same integral-versus-sign
  distinction persists at every tensor order12t with exactly8 missing.

The Hadamard construction is classical Scarpis/Djokovic machinery.
Primary source inspected, including construction and proof:
https://arxiv.org/pdf/1601.00635
Published version: DOI 10.1080/03081087.2016.1265062
No novelty claim is made for the exchange-budget interpretation.

No code was imported from this source or elsewhere. check.py is newly
written standard-library Python using exact integer arithmetic. It
checks all 4096 length-12 sign rows, candidate classification, the
9-word code and full completion, and tensor repairs at t=1,2,4,8.
Run python check.py to regenerate checks.json.
No Lean or git commits.
