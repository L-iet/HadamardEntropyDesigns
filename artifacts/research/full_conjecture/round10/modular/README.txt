Exact modular lifting at orders4mod8
20 November2026, bounded research pass

modular.tex proves for any odd integer q>=3, N=4q, and r>=5
orthogonal sign rows:
  exact extension classes = modular-q sign classes - r.
Every spurious modular class is an existing row. The proof is pure
parity plus Bessel and does not require q prime.

Sharp boundary: at r4 an additional4-class correction appears exactly
for a closed quadruple. These are the half-sums of the four old rows.
H4 tensor1_q supplies M8,E0, so omitting this term gives a falsepositive.
Closed-quadruple terminology and the4mod8 prohibition are classical:
Orrick, Switching Operations for Hadamard Matrices, Sec3.1/Prop3.1,
https://arxiv.org/abs/math/0507515 (primary PDF inspected).

The finite group-algebra coefficient Cq gives E=Cq/2-r. Positivity
beyond the installed r rows remains the substantial missing step.
No novelty or full Hadamard-conjecture proof is claimed.

check.py is standalone, newly written Python standard-library code.
Exact integer checks construct H12,H20,H28; verify modular/exact
profiles, full matrices, closed/nonclosed four-row boundaries, and
independently compute the small group-algebra coefficient36.
Gaussian enumeration uses prime moduli3,5,7; the proof covers alloddq.
Run python check.py to regenerate checks.json. No external sourcecode,
Lean, or git commits. No earlier-round files were modified.
