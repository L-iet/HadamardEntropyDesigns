GLOBAL COMPLETION MOMENTS

moments.tex proves first and second moments of the sign count in
uniformly chosen self-dual completions of a retained isotropic space.
The data are weights on isotropic quotient projective points and their
orthogonal pairs. A second-moment lower bound can certify a large
orthogonal sign frame without selecting a specific target code.

Known order20 benchmark: retained rank8, b9, W42, S2=96, T=588 gives
mean total16 but maximum>=19, enough for Hadamard completion.
Retaining only five rows gives maximum>=9, insufficient.
No unknown-order count inequality is established.

Also proves exact expected sign-count drift under uniform code-neighbor
steps, using the tenth-pass incidence identity. Above the global mean,
uniform steps lower expected sign count, with contraction factor<1/p
for quotient half-dimension>=3. This is a diagnostic for search, not an
impossibility theorem for guided moves.

check.py uses only standard-library exact arithmetic. It checks small
hyperbolic point counts, exhausts all eight ternary completions in the
rank-four H12 example, and computes the two H20 moment benchmarks.
All previous project files are read only. No external code is imported.
Finite polar geometry is established background; novelty is unverified.
