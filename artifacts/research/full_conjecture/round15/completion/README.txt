Round15 three-column quaternary completion

main.tex input-ready fragment; paper.tex/PDF standalone. The exact
one-column gate is simple: a sign column in the realified kernel gives
a fourth-root complex column by dividing its paired complex entries
by1+i. CLASSICAL real codimension<=7 completion supplies one such sign
column when complex defect<=3. Append one and repeat, without assuming
an arbitrary full real completion preserves a complex structure.

An exact Gaussian-rational systematic-kernel search tests at most16+4+1
=21 normalized candidate columns and constructs the full completion.
At complex defect4, at most64 candidate tests decide the first-column
gate; if it succeeds, defect3 completion finishes. No automatic first
column at defect4, no novel classicalcompletion theorem, and no source
of the large partialframe at unknown Hadamard orders is claimed.

Run python check.py (standard library Fraction pairs). Exact test cases
at orders4,6,8,14 and a known defect4 gate verify positivity-of-alphabet,
kernel equations, final Gaussian Gram, and candidate bounds. No external
code, Lean or commits. New code Apache-2.0 under parent research LICENSE.
