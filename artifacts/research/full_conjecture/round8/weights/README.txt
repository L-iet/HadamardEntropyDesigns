Round8 adaptive weights

weights.tex gives an explicit right-inverse correction on a support
whose degree<=2 feature matrix has full row rank. It checks positivity
through p_min >= gamma*moment_error, and bounds TV and collision loss.
This is a constructive finite distribution correction with all support
geometry and positivity assumptions exposed.

The sharp complementary obstruction: for d=N-4, N multiple4>=8, any
exact unbiased pairwise-independent law supported on <=N points is
already uniform on exactly N points and completes to Hadamard N.
Thus no adaptive same-support reweighting can repair a failed uniform
N-row candidate. More support or different sign rows are necessary.

No enriched support with the required concentration/error window is
constructed in unknown Hadamard orders. The sufficient extraction
criterion remains conditional. No HC proof or priority claim.

Run python check_exact.py: standard-library exact Fraction checks of
full feature rank, right inverse, positivity margin, moment correction
and collision bound on a 16-point support. No external code, Lean or
commits. New code Apache-2.0 under research parent LICENSE.
