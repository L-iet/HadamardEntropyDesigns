Near-full weighing completion: forcedblocks,8-state algorithm,realcounterexample
20 November2026

weighing.tex proves for W(n,n-2),4|n:
1. Zero support is a union ofK2,2, not arbitrarylongcycles.
2. Every off-diagonal2x2block is automaticallyHad2. Proof uses
   A=W(I tensorH2)/2 and its mod2 inverse on pairconstant vectors.
3. Every zero-preservingHadfill is determined by ONE of8 signed
   permutation rootstates. Allfills listed inO(n^2) integeroperations.
4. An explicitW12,10 has incompatible triangleconstraints. It cannot
   be completed by modifying onlyzeros EVEN WITH REAL fillentries.
   Two triangleequations force the rootorthogonal matrix tobezero.

check.py embeds the explicit counterexample; verifiesGram10I and
all8 failurecertificates; checks positive completioncounts8,6,2 at
orders4,8,12; verifies conference diagonalcyclecriteria and signing
invariance. It is standalone newly written Python stdlib/exactintegers.
Run python check.py to regenerate checks.json.

search.py is the exploratory own-code search, defaulting to the
exhaustive256 normalizedW8,6 cases (allfillable). The counterexample
insearch.json was found in an order12 pass after9 fullweighing cases.
This exploratory search is not needed toverify the fixed certificate.

Primary literature inspected:
Geramita-Verner, Orthogonal Designs with Zero Diagonal (1976),
https://doi.org/10.4153/CJM-1976-028-3
Theorems1-2 state the classical orthogonal-design decomposition and
Delsarte-Goethals-Seidel conference normalization used for d1.
Gysin-Seberry, On the Weighing Matrices of Order4n and Weight4n-2
and2n-1 (1995), https://ajc.maths.uq.edu.au/pdf/12/ocr-ajc-v12-p157.pdf
for context on constructing near-full weighing matrices.

No externalcode or text copied; no novelty/all-orderexistence claim,
Lean, commits, or earlier-file edits. The counterexample forbids only
zero-supportpreserving completion, not modifying some fixednonzeros.
