ROUND 11: SHARP GLOBAL TRADE BUDGETS FOR HADAMARD-MIXTURE REPAIR

Files
  repair.tex    TeX fragment with complete proofs.
  check.py      Original Python standard-library exact checker.
  checks.json   Exact benchmark certificates.

Strongest result
For k,h powers of two with h>2(k-1), construct an explicit uniform
D=h^k-atom exact pairwise-independent law on n-1 bits, n=kh. Its total
variation distance from the convex hull of ALL order-n Hadamard laws
is exactly1-1/k. This tends to one, although these n are known Sylvester
orders. Thus arbitrary isotropic laws cannot generally be repaired into
Hadamard mixtures by changing only a small fraction of their mass.

Construction and sharpness
Use k independent s-bit seeds, h=2^s. Observe all nonzero characters in
each seed block plus k-1 mixed characters chi_e(x1+xj). Augmented row
inner products show an orthogonal source subset has at most h rows;
offset-diagonal cliques attain h. Each such clique explicitly completes
by Walsh block mixing, and different offset completions are disjoint.
Averaging their Hadamard laws attains TV distance1-1/k exactly.

Global observation trades
Converting the D distinct source observations into D/n Hadamard blocks
requires exactly D(1-1/k) replacements. A construction attains this
minimum and keeps all rows distinct, so collision probability stays1/D.
Both endpoints have identical first and second moments and identical
collision, but the endpoint is explicitly a union of Hadamard blocks.
This is a sharp large trade, not a small-move guarantee or a new order.
No local-optimality claim is made for the k>2 source laws.

Scope and arithmetic caution
The theorem concerns n-1 output bits. An auxiliary denominator bound
C<=floor(D/n)/D and nonuniformity threshold D>=2n use the corresponding
atom bound1/n. They must not be applied as1/N atom bounds to the
N-4-bit extraction target, whose elementary bound is only1/(N-3).
No missing distribution, Hadamard conjecture proof, or novelty claim.

Reproduce
  python research/full_conjecture/round11/designs/check.py
Exact cases(k,h)=(2,4),(2,8),(4,8), including source supports up to4096
and completed supports up to16384. Every source/repair first and second
moment, every completion-block orthogonality, every support intersection,
disjointness, TV value, collision equality, and replacement count is
checked with integers and Fraction. The row-kernel identity is checked
on all pairs in small cases and deterministic sampled pairs in the largest
case; its general validity and upper bound are proved algebraically.

Primary background consulted
Claude Carlet, Rebeka Kiss, Gabor P. Nagy, Simplicity conditions for binary
orthogonal arrays (2022), Rao bounds, simplicity, repeated rows.
https://arxiv.org/abs/2204.00835
No external source code downloaded or reused. No Lean, commits, submissions.
