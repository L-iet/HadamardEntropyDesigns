FULL HADAMARD CONJECTURE — SEPARATE RESEARCH PROJECT
20 November 2026

Start with paper/parallel_progress.pdf (source: paper/parallel_progress.tex).
It records the second, parallel research pass and complete reviewed proofs.
The earlier starting notebook is paper/research.pdf (source: research.tex).

LATEST PROVED PROGRESS

- The norm equation is solvable for every odd m and every odd
  t >= (m^2+3)/4, by the three-square theorem. This threshold is sharp
  within the constant-perturbation family, not globally optimal.
- For primes p=3 mod4, a skew-character family improves the sufficient
  threshold to t >= (p^2+6p+21)/16. It remains quadratic, above the
  required boundary t=p in general. Odd multiplier closure also holds.
- Every saturated OA(N,N-1,2,2), N>=8, is isolated under all translated
  coordinate-cube parity moves. Non-coordinate trades are necessary.
  Fixed-dimension central-ray existence has an explicit quadratic bound.
- An exact 16x24 partial matrix needs at least THREE row deletions for
  an augmenting exchange; three-for-four succeeds. All 137 deletion sets
  of sizes zero, one and two were checked using an independent traversal
  of the entire 2^23 normalized sign cube.
- Quartic flattening also has strict nonglobal local minima at every
  order 20*2^a. The proof gives an analytic positive Hessian lower bound.
  A separate order-28 saddle has positive curvature along every single
  coordinate rotation, showing why those tests miss joint directions.

Read the individual arithmetic/, moments/, exchanges/ and geometry/
directories for proofs and exact certificates. No novelty is claimed.

This project explores connections beyond the existing asymptotic proof.
The full conjecture is NOT proved. No new universal construction, novelty
claim, submission, publication, Git commit or Lean formalization is made.
The old Lean repository, manuscripts and website were not edited.

PRIORITY 1: INTEGRAL HERMITIAN NORMS WITH PARITY

For odd m, let R = Z[z]/(z^m-1), let * reverse powers of z, and let
J = 1+z+...+z^(m-1). Ask for four A_i congruent to J modulo 2 with
  sum_i A_i A_i* = 4t.
The paper proves t>=m and t odd are necessary. At t=m the energy identity
forces all 4m coefficients to be signs. Goethals--Seidel then supplies a
Hadamard matrix of order 4m; Sylvester doubling covers all multiples of 4.
The broader question asks about all odd t>=m. It remains OPEN HERE in
the lower-energy range and could have further obstructions. The latest
uniform high-energy theorems are summarized above.
The boundary itself is a stronger four-circulant existence problem;
rewriting it in ring language is not progress on existence by itself.

IMPORTANT NEGATIVE RESULT FROM LITERATURE

Full quaternionic perfection would add conditions that are not needed
for Goethals--Seidel. Published nonexistence results at lengths
35,47,53,59 rule out that stronger all-length route for the relevant
alphabet. The weaker real-part cancellation remains the intended target.
Sources and the exact distinction are explained in the paper.

PRIORITY 2: INTEGER MOMENT SEMIGROUPS

Pairwise-independent unbiased binary observations correspond to positive
integer solutions of quadratic moment equations. At N observations and
d=N-1 coordinates, this is equivalent to Hadamard existence.
We give an explicit signed integer solution at every admissible N and a
complete integer-kernel basis of cube moves. The missing step is to remove
negative coefficients. Generic semigroup normality is false: a small hole
is certified. No positive-conversion theorem is claimed.

PRIORITY 3: LOW-RANK GRAM COMPLETION AND EXCHANGES

For P with n-r orthogonal sign rows, C=nI-P^T P is a rank-r integral
projection Gram matrix. Completing P requires a sign factor B^T B=C.
The paper proves a finite-type anchor reduction for fixed r and an
elementary defect-two completion theorem. It also proves that dead ends
persist under tensoring with a full Hadamard matrix.

A certified 12x20 partial matrix has NO orthogonal sign extension. Each
of its twelve rows is frozen under a single-row replacement. Two-for-three
exchange repairs it, and a full order-20 completion is checked exactly.
The minimal number of deleted rows for any augmenting exchange is two
for THIS example. There is no universal bounded-exchange theorem here.

OTHER PROVED OBSTRUCTIONS

- The known orthogonal Householder family has non-Hadamard strict local
  maxima for the entrywise l1 objective, even at valid orders. Tensoring
  preserves the traps. Local optimization alone cannot justify existence.
- Condition number 1+o(1/n) for even-order sign matrices would force eventual
  exactness; a bound merely tending to one is insufficient.
- If a Hadamard matrix of order n+s preserves a k x (n-c) rectangle from
  one of order n, with s>0, then k<=c+s. Additive-order induction cannot
  preserve a large untouched rectangle.

REPRODUCE FROM D:\Papers\Hadamard

  python research/full_conjecture/experiments/investigate.py
  python research/full_conjecture/experiments/exchange.py
  python research/full_conjecture/experiments/moments.py
  python research/full_conjecture/experiments/norm_lifting.py
  python research/full_conjecture/experiments/verify.py
  python research/full_conjecture/build.py

To reproduce the parallel-pass checks and latest PDF:
  python research/full_conjecture/arithmetic/verify_large_energy.py
  python research/full_conjecture/moments/check.py
  python research/full_conjecture/exchanges/test_cube.py
  python research/full_conjecture/exchanges/verify.py
  python research/full_conjecture/geometry/verify.py
  python research/full_conjecture/build_progress.py

The latest standalone TeX is assembled from the branch sources by
build_progress.py; edit those source files rather than the generated TeX.
The generated TeX itself contains the complete note and compiles directly.
progress-verification.json records branch check status and artifact hashes.

All experiment code uses Python's standard library. Searches are seeded
and bounded. The verifier does not perform the random search; it checks
the stored certificates by independent enumeration and exact arithmetic.
The builder checks that the displayed partial matrix matches the JSON,
then compiles the PDF and records hashes and scope in verification.json.
On Windows it uses installed TeX Live through WSL and native pdftotext.
Temporary files are in .build/.

No externally authored research code was downloaded or copied. Papers
were read as mathematical literature. New project-authored code is
Apache-2.0; see LICENSE. No external Python dependencies are required.

LITERATURE AND PRIORITY

The paper cites primary sources for known results. Public-web searches
included quaternionic perfect sequences, integral Gram completion,
Hadamard trades, orthogonal arrays, rare-object counting, absorption and
cut-polytope normality. This is not an exhaustive novelty audit, and the
elementary reductions are not claimed as new results. The bibliography
is a reading trail, not a list of code dependencies.
