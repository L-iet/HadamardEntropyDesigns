THIRD RESEARCH PASS — 20 NOVEMBER 2026

Main candidate result: geometry/tensor_stability.pdf
Combined proofs: research.pdf
Scope and reproducibility: this file and verification.json.

TENSOR STABILITY: A UNIFORM OPTIMIZATION THEOREM

For every finite real p>2, every nonflat critical point U of the entrywise
p-energy on O(n) has a negative tangent-Hessian direction at some finite
self-tensor power U^(tensor k). An explicit k bound and a factored direction
Y tensor Z^(tensor(k-1)) are proved. Only scaled Hadamard matrices remain
local minima at EVERY tensor power.

The proof uses trace averages over symmetric/skew-symmetric matrices and
strict Chebyshev inequality. It handles zero entries and does not assume
the critical-point matrix is positive semidefinite. A separate mathematical
review checked these points and the tensor factorization. Exact rational
checks cover 39 examples at integer exponents and a direct two-copy example.
The theorem also extends to rectangular row-orthonormal Stiefel frames,
where flatness corresponds to a rectangular partial Hadamard matrix.

This is not a Hadamard existence proof: lifting changes the dimension, and
neither a stable point nor descent back to the original order is supplied.
The statement is a potential standalone research result. Targeted searches
did not locate it, but comprehensive novelty clearance is still outstanding.

ARITHMETIC: THE FULL CHARACTER TEMPLATE IS NOW RULED OUT

In the family Ai=z^ri(ui L+vi+wi J), with all coefficients odd, the exact
minimum energies are (m^2+6m+21)/16 for a skew quadratic character and
(m^2+2m+5)/8 for a symmetric character. Shifts and arbitrary integer
rescaling cannot lower these minima. Only prime lengths3,5,7 reach the
binary boundary in this entire family. This excludes a construction class,
not unrestricted Hadamard existence.

TRADES: ARITHMETIC RIGIDITY ON THE SATURATED BALANCED FIBER

At order n=4m, m odd, let P be the least prime factor of m. A genuinely
new sign row in the span of r<n old Hadamard rows forces
P <= r^(r/2)/2^(r-1). This yields a lower bound on every nontrivial reduced
observation trade. For example at known order212, no trade of volume<=8
can leave any saturated array. CRT, Dirichlet and Linnik produce infinitely
many known orders with unbounded trade volume, quantitatively at least
(2-o(1)) loglog(n)/logloglog(n) along a subsequence.

General unbounded Markov width is already known with stronger global
bounds. This result is specifically about the balanced minimum-run fiber.
It does not rule out global symmetry operations or bounded augmentation of
incomplete matrices. No claim of bibliographic priority is made.

EXCHANGES: AN INFINITE EXACT THREE-ROW BARRIER

The order24 example keeps exact augmenting exchange cost3 after tensoring
with ANY Hadamard matrix. A proved half-overlap criterion excludes cheaper
non-product exchanges. On the other hand rho(P tensor H)<=rho(P) always,
so this tensor operation cannot amplify a finite cost into an unbounded one.

REPRODUCE FROM D:\Papers\Hadamard

  python research/full_conjecture/round3/geometry/check.py
  python research/full_conjecture/round3/arithmetic/check.py
  python research/full_conjecture/round3/trades/check_rigidity.py
  python research/full_conjecture/round3/exchanges/check.py
  python research/full_conjecture/round3/build.py

All research checkers use Python's standard library and exact arithmetic.
The infinite assertions have mathematical paper proofs, not Lean proofs.
The builder assembles research.tex from reviewed branch sources and builds
the standalone tensor paper and combined note. It uses installed TeX Live
through WSL on Windows and native pdftotext. Intermediates are in .build/.
The combined TeX is standalone; edit branch sources before regenerating it.

No external research code, Git commits, submissions or publications.
New authored code is Apache-2.0 under ../LICENSE. The previous research
notes, existing Lean repository and asymptotic manuscript are unchanged.
