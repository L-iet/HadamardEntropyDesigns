CONDITIONAL quantitative half-frame transfer
20 November2026

arithmetic.tex proves, assuming Dirichlet GRH for power-of-two
conductors (including conductor1), that the established unconditional
tau(u)=O(logu/loglogu) gives
 r(n)>=n/2 - B*sqrt(n)*exp(K*logn/loglogn)
for every sufficiently large multiple of4.

Key details explicitly handled:
* Uniform T(n) controls ALL odd parts<=n before choosing any prime or k.
* Q=2^T=n^o(1); no circular dependence on an unknown selected k.
* Correct progression residue is n-1modQ, not always -1modQ.
* Prime POWERS3mod4 suffice for Paley; positive psi interval is enough.
* Both endpoint errors are dominated by H=D Q sqrt(x) log^2(x).
* Truncated blocks concatenate with exactly n columns and Gram nI.
* The result remains conditional. No claim GRH is proved or verified.

Primary sources inspected:
de Launey-Gordon, A Comment on the Hadamard Conjecture,
DOI10.1006/jcta.2000.3155, Lemma2.1 and originalproof,
indexed PDF9738d44bd69b58dd37f232adad586d99b6aa82b7.
Montgomery-Vaughan, Multiplicative Number Theory I, Theorem13.7
and Corollary13.8:
https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/17.0_pp_419_451_Conditional_estimates.pdf

The concatenation strategy is historical; the quantified transfer is
independently derived using this project's newer tau bound. No novelty
claim is made. No external code was imported, and no Lean or commits.

check.py uses standard-library exact arithmetic and actual finite
Hadamard constructions. Finite checks DO NOT verify GRH, asymptotic
prime estimates, or the unknown numerical tau constant.
