# Further results

The [README](README.md) highlights three leading theorems. The main results are “No dimension-independent stability, even for exact moments,” “Residue-sensitive collision bound and equality,” and “Uniform bounded-degree moves cannot suffice.”

## A family with an exactly attained distance

Let $`h=2^s`$, and let $`k`$ be a known Hadamard order with $`s\le h-k<h/2`$. A finite-field construction produces an unbiased pairwise-independent law on $`kh-1`$ signs, uniform on $`h^2`$ atoms, that is a strict local collision maximum and satisfies

$$
C(\mu)=h^{-2},\qquad \inf_{\nu\in\mathcal H_{kh}}\|\mu-\nu\|_{\rm TV}=1-\frac1k.
$$

Here $`\mathcal H_{kh}`$ denotes convex mixtures of laws obtained from order-$`kh`$ Hadamard matrices. Choosing $`k/h\to1`$ while $`k\to\infty`$ yields the instability theorem in the README.

## Additional proved results

- Exact finite-field families with an attained distance of $`1-1/k`$ from all Hadamard mixtures.
- Quantitative collision-defect identities, weight stability, and extraction of nearly orthogonal configurations.
- Moment-correction constructions with explicit positivity and error bounds.
- A finite support-reduction algorithm that preserves feasibility and does not decrease collision probability.
- Explicit feasible repair paths, exact collision barriers, support-reduction schedules, and symmetric-design bounds.

The [paper](paper/main.pdf) supplies the definitions, hypotheses, proofs, and prior-work references. The following list names the additional principal results covered by the public Lean proofs; the [technical guide](TECHNICAL.md) explains the correspondence and separately identifies unfinished formalizations.

- Denominator obstruction to a new sign row.
- A prime-factor lower bound for positive trade volume.
- Uniform bounded-degree moves cannot suffice.
- A quantitative infinite subsequence.
- A universal half-row trade.
- Exponential multiplicity of isolated states.
- Residue-sensitive collision bound and equality.
- A positive entropy window suffices.
- One saturated atom in every even dimension.
- Exact false positive for one-copy uniformity.
- Rigidity of positive diagonal balancing.
- The natural classical and operator capacities are blind.
- Elementary parity gap.
- Collision--moment rounding certificate.
- Explicit collision gap.
- Nonsingular modular seeds need not lift.
- Sharp weighted collision bound.
- Equality rigidity and two-column reconstruction.
- Nonnegative defect decomposition.
- Explicit extraction from a sufficiently small deficit.
- Collision cost of full coordinate symmetry.
- Shannon entropy is almost maximal.
- Local maximum criterion.
- Explicit four- and five-bit traps.
- A trap at admissible Hadamard order eight.
- Arbitrarily poor traps at admissible orders.
- A certified collision barrier.
- Complete rigidity from additive coverage.
- The smallest binary seed forces a power-of-two law.
- Approximate moment version.
- Maximum overlap and optimal straight bridge.
- Complete any maximum overlap subset.
- Finite nonlocal rewiring.
- Nonnegative exact correction.
- A sufficient input window for exact extraction.
- Quantization obstruction for a uniform row candidate.
- Affine observable budget.
- Complement criterion for low-degree extensions.
- Sharp cubic benchmarks at orders twelve and twenty.
- Fixed algebraic degree cannot suffice asymptotically.
- Actual positive correction with an explicit margin.
- No adaptive reweighting on a minimal-size support.
- Binary rank of a minimal-support target.
- Support-overlap rigidity.
- An explicit near-moment candidate.
- A nonvacuous asymptotic obstruction to dimension-free rounding.
- Even restriction code and its radical.
- Exact fixed-support criterion for a full basis.
- Degree saturation near a power of two.
- Punctured-observable bounds, without completion.
- Exact finite obstruction.
- A finite exact escape rule.
- The unavoidable barrier is exactly $`1/288`$.
- A quantitative moment-error floor.
- Minimum support edits to unlock degree repair.
- An exact monotone support-reduction algorithm.
- Sharp barrier for a specified straight bridge.
- A support witness against all Hadamard mixtures.
- Sharp distance and global repair family.
- Exact fixed-support collision optimum.
- Simultaneous face optimum, strict trap, and sharp distance.
- A certified local barrier.
- Moderate-support regimes.
- General support bound without a small-$`k`$ restriction.
- Spanning omitted slopes give the sharp distance.
- A near-optimal relative regime.
- No dimension-independent stability, even for exact moments.
- No residue-class restriction is needed.
- An ordinary-prime-gap transfer.
- Uniform Hadamard-gap transfer.
- Unconditional near-square instability from the multiplier bound.
- Exact projective and commuting criteria.
- Uniform tight frames are uniformly almost commuting.
- Simplex count.
- Second-order entropy bound.
- Finite radix certificate.
- Isolation under all coordinate-cube moves.
- Sharp maximum-weight constraint.
- Exact limitation of monotone triple conversion.
- Exponential cost of full permutation symmetry.
- An explicit cofinite central ray.
- Sparse uniform candidates cannot enter the extraction window.
- Complete four-bit entropy diagram.
- Spanning-slope summary input.
