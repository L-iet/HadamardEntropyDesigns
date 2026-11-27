Invariant-theory / balancing bridge: bounded research pass
20 November 2026

invariant.tex contains independently derived proofs of three obstructions:
1. Positive diagonal left-right scaling of an orthogonal matrix cannot
   change it while keeping it orthogonal.
2. Natural polynomial and completely-positive operator capacities of its
   squared-entry bistochastic matrix are identically 1, flat or nonflat.
3. At n = 2 mod 4 there is an explicit positive quartic-energy gap despite
   the perfect balancing/capacity value. Constants are not claimed sharp.

Primary sources consulted online:
https://arxiv.org/abs/1511.03730
https://www.math.ias.edu/~avi/PUBLICATIONS/GargGOW20.pdf
https://arxiv.org/abs/1801.01412
https://sites.math.rutgers.edu/~wcf17/images/site_OSWSM_arxiv_ver3.pdf
https://doi.org/10.1016/j.disopt.2018.10.001

These sources motivate the attempted bridge; the arguments above are
self-contained. No novelty claim and no proof of the Hadamard conjecture.
No downloaded source code, external mathematical implementation, Lean,
or git commits are included. The checker uses only Python's standard
library and exact rational/integer arithmetic.

Run python check.py to regenerate checks.json.
