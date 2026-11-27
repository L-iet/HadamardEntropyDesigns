ROUND THREE: TENSOR PRESERVATION OF EXCHANGE RIGIDITY

Read tensor_barrier.tex, a section fragment using theorem, proposition,
corollary and proof environments, amsmath/amssymb, hyperref, and \R.
Run:
  python research/full_conjecture/round3/exchanges/check.py

PROVED

1. If rho(P) is the smallest number of row deletions needed for an
   augmenting exchange, rho(P tensor H) <= rho(P) for any full Hadamard H.
   Thus tensoring cannot amplify a finite repair cost into an unbounded one.

2. A general span-rigidity criterion preserves c-row exchange barriers
   under arbitrary Hadamard tensor factors.

3. A weaker half-overlap pair criterion still preserves the two-row barrier.
   The preceding 16x24 example satisfies this criterion exactly.
   Therefore rho(P tensor H)=3 for EVERY full Hadamard tensor factor H.
   In particular exact cost-three maximal examples exist at all orders
   24*2^a. This is an infinite-family theorem, not a sample extrapolation.

4. Performing the base three-for-four exchange separately in all s fibers
   gives Q tensor H, which has an explicitly constructed full completion.
   A single lifted exchange is only asserted to augment the partial matrix.

CHECKS

check.py re-enumerates the entire 2^23 normalized base sign cube. All
16 singleton caps and all 120 pair caps are checked. The 20 nontrivial
pair caps have two extra orthogonal lines with cross-correlations +/-12
and parallel projection vectors. Tensor exchanges and completions are
checked at factor orders 1,2,4,8. An independent exact nullspace enumerator
checks the three deletion cases at order48: 2,2,6 candidate lines,
respectively, after testing 131072 free-coordinate assignments per case.

checks.json records the passed checks. The scripts use only Python's
standard library and existing project-authored Apache-2.0 code from
../../exchanges/cube_kernel.py. No external research code is imported.

No unbounded-exchange lower bound, new Hadamard orders, full-conjecture
proof, Lean formalization, or bibliographic novelty is claimed. The
general upper bound explains why a naive tensor amplification direction
cannot produce the hoped-for unbounded repair barrier. Public primary
literature searches on maximal row-Hadamard matrices, tensor products
and augmentation did not establish priority for the preservation theorem;
no novelty conclusion is drawn from those searches.
