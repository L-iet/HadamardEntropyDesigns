Round9 nonlocal atom exchanges

exchanges.tex proves an exact twelve-atom edge/circuit move from each
of the 16 suboptimal four-bit collision vertices to any of five matching
uniform optima, with endpoint gain1/36. The entire interpolation is an
actual nonnegative pairwise-independent law.

Its collision barrier1/288 is globally optimal over ALL continuous
feasible paths to any uniform vertex, not only straight paths. A simple
Hadamard4 frame bounds every coordinate-half section by ||a||^2<=1/2;
every path must cross one. This makes the need for nonlocal moves exact.

python check_exact.py uses standard-library Fraction arithmetic. Checks
all80 circuit moves, support-union size12, kernel dimension1, all pairwise
moments, collision polynomial, and an independent exact chord certificate
for all10 half-coordinate sections. No external code, Lean or commits.
New code Apache-2.0 under research parent LICENSE. No novelty claim or
claim of a corresponding rule in unknown higher Hadamard orders.
