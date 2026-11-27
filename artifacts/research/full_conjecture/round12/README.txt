TWELFTH RESEARCH PASS

research.tex/pdf: combined report.
conditional_partial.tex/pdf: conditional quantitative half-frame theorem.
stability_rates.tex/pdf: independent prime-gap rates and stronger
unconditional rates from the existing multiplier theorem.
Run python research/full_conjecture/round12/build.py to reproduce.

RESULTS AND ASSUMPTIONS
arithmetic/: assuming only Dirichlet GRH for power-of-two conductors,
r(n)>=n/2-B*sqrt(n)*exp(Klogn/loglogn) for all sufficiently large4|n.
The uniform multiplier buffer and progression residue are handled
before any prime power is selected. No GRH proof is imported or verified.

stability/: published ordinary prime gaps already give unconditional
quantitative stability counterexamples at all large dyadic seed orders.
Ordinary RH improves that independent prime route.
More strongly, the existing unconditional multiplier theorem explicitly
supplies H_k just below every large dyadic h. The resulting exact
isotropic strict local maxima have n+n^(1/2+o(1)) atoms, relative
collision deficit n^(-1/2+o(1)), absolute deficit n^(-3/2+o(1)),
and distance1-(1+o(1))/sqrt(n) from ALL Hadamard mixtures.
These are known orders and full n-1-bit laws, not the punctured input.

moments/: exact cubic completion moments include dependent collinear
triples. One retained-space H20 example certifies20 rather than19
classes; the weak example improves9 to11 and still fails the threshold.
No uniform useful moment order or all-order positivity is established.

dilations/: explicit real/rational scaled-orthogonal completions of
concatenated Hadamard frames have a residual O(b-a) parameterization.
A quaternion construction always supplies rational points, while signs
remain constrained. The structured [H8|first8H12] frame can retain at
most12 orthogonal rows in any extension, despite known H20 existence.
Deleting exactly one prescribed row permits a full H20; witness stored.
An exact rounding threshold gives a positive quartic gap for every
real completion of an uncompletable prescribed sign frame.

CHECKS AND PROVENANCE
Four exact standard-library branch checkers and independent mathematical
audits support the written results. Finite tests do not validate GRH,
asymptotic constants, or unknown orders. No external proof code imported.
Earlier project files, proof hashes and Lean sources remain unchanged.
The full conjecture and bibliographic novelty remain unresolved.
No commits, publication or external submission.
