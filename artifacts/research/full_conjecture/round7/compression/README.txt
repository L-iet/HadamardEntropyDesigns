ROUND 7: EXPLICIT NONLOCAL ESCAPE OF THE CHARACTER TRAPS

Files
  escape.tex      TeX fragment with self-contained proofs.
  check.py        Original standard-library exact checker.
  checks.json     Exact output for s=2,3,4 (Hadamard orders8,16,32).

Main findings
Let h=2^s,s>=2. The initial trap has h^2 atoms on2h-1 bits, observed
as all nonzero A characters, all nonzero B characters, and one mixed
character e(A+B).

1. Constructed compressed endpoint, rather than merely invoking existence:
   sample uniform a in F2^s and fair t; output A characters(a), all
   B-labeled characters(a) multiplied by(-1)^t, and mixed bit(-1)^t.
   This has2h atoms and exact unbiased pairwise independence.
2. Maximum possible overlap with any globally optimal2h-atom law is h.
   The augmented trap-row inner product formula proves any orthogonal
   subset has at most h rows; the endpoint meets this upper bound.
3. Direct feasible mixture has exact collision
     (1-lambda+(h/2)lambda^2)/h^2.
   Its minimum is (1-1/(2h))/h^2 at lambda1/h, a loss of1/(2h^3).
   This minimum is optimal among all straight mixture bridges to any
   global maximizer. No optimality over curved paths is claimed.
4. Every maximumh-row orthogonal subset of the trap explicitly completes:
   split it as[H1 H2] and append[H1 -H2]. This attains maximum overlap
   without restricting the selected subset to a linear graph.
5. Explicit finite rewiring changes observed masks via one column swap
   and h-2 single-character substitutions. Every endpoint is pairwise
   independent; endpoint collision never falls. Exactly s-1 substitutions
   halve support and double collision. Straight interpolation of all
   individual jumps has minimum3/(4h^2), worse than the direct bridge.
6. A quotient retaining the original observed characters cannot compress
   this trap: observed masks and pairwise sums cover the entire dual.
   The successful method changes the observed characters instead.

Scope
This is a complete constructive escape of one special family of bad local
maxima at already-known orders. It neither gives the missing distributions
in arbitrary dimensions nor supplies a general collision-ascent algorithm.
The endpoint ingredients are Walsh characters and block doubling, both
classical; novelty of the quantitative landscape statements is unverified.

Reproduce
  python research/full_conjecture/round7/compression/check.py
Checks all means and pairs; all trap-pair kernel identities; exact overlap;
all jump endpoint collisions and intersections; direct and piecewise bridge
minima; completions of parity-compatible nonlinear maximal cliques.
Only integers and fractions are used. No external source code, Lean files,
commits or submissions were made.

Primary background read
Luby and Wigderson, Pairwise Independence and Derandomization,
Sections1.1-1.2, finite-field constructions and pairwise independence.
https://www.math.ias.edu/~avi/PUBLICATIONS/LubyWig2005.pdf
