ROUND 6: COLLISION ATTAINMENT LANDSCAPE

Results in traps.tex (TeX fragment)
1. Exact criterion: a point of a finite polytope locally maximizes squared
   norm iff it uniquely maximizes its own gradient linear functional.
   Every uniform vertex of the pairwise-independent law polytope is a
   strict local collision maximum.
2. Explicit d4,d5 nonglobal strict local maxima, each with collision7/72
   versus feasible1/8. Rational quadratic dual certificates expose both.
3. Direct admissible-order8 trap: a uniform16-atom linear code on7bits,
   collision1/16 versus global1/8. Full-cube perturbations are included.
4. Infinite admissible family: h=2^s,s>=2, d=2h-1 bits, m=h^2 atoms,
   strict local collision maximum1/h^2 versus global1/(2h). Ratio2/h->0.
   The selected observed bits are all nonzero characters in each of two
   complementary seed subspaces plus one mixed character. Restricted
   degree-two monomials span every seed character, proving vertex status.
5. Explicit strict-local infinity-norm radius2/[m(m+1)]. This is indeed
   an infinity-norm bound: if t is outside mass, Fourier interpolation
   gives ||delta||1<=(m+1)t, then ||delta||2^2<=||delta||infty||delta||1.
   Any continuous path to a global optimum loses collision at least
   1/[m^2(m+1)] somewhere.

Interpretation
These are bad traps for the full feasible polytope, not just coordinate
moves. They disprove a universal local-ascent attainment principle even
at orders with known Hadamard matrices. Nonlocal jumps or objectives
with different geometry remain possible. No Hadamard conjecture proof
or novelty assertion is made. No product-closure claim is made: large
independent products have supported feasible escape directions.

Exact reproducibility
Run python research/full_conjecture/round6/attainment/check.py
- All calculations use original Python standard-library code and Fraction.
- explore_d4.py enumerates all4368 candidate5-active-facet intersections
  in the free five-dimensional Walsh representation, filtering feasible
  vertices. It finds26: ten withC1/8, sixteen withC7/72. Every vertex is
  strictly exposed by its own gradient. d3 is a one-dimensional interval
  whose two endpoint maxima are global.
- d4,d5 support moment rank11 and exact quadratic exposure are checked.
- d7 Fourier interpolation is checked on all128 atoms for all16 kernels.
- Infinite family checked at s2,3,4: orders8,16,32; supports16,64,256.
- d4_vertices.json is the exact vertex list; checks.json summarizes.

Primary sources read online
Luby and Wigderson, Pairwise Independence and Derandomization,
Sections1.1-1.2 (classical finite-field character background).
https://www.math.ias.edu/~avi/PUBLICATIONS/LubyWig2005.pdf
Gavinsky and Pudlak, On the joint entropy of d-wise-independent variables,
Theorem3.2 and Section4 (standard atom bound and Hadamard equality).
https://users.math.cas.cz/~pudlak/pairwise.pdf
No external code was downloaded. No Lean files, commits or submissions.
