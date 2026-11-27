Exactness of real two-zero weighing completion
20 November2026

weighing.tex proves:
* Real zero-supported orthogonal completion exists iff signHadamard
  completion exists for W(n,n-2),4|n.
* The rootconditions form a linearspaceK inM2. Its rotation/reflection
  sections can onlybe0,coordinateaxis,orfullplane.
* A potential diagonal section gives W+sqrt2T; C=WT^T isskew,
  U=C+I isconference, and classicalconferencefills +/-Y yield
  Hadamards(U+/-Y)T preserving alloldnonzeroentries. Their independent
  roots force the wholecomponentplane, excludingisolated diagonal lines.
* Allisolatedrealcompletions alreadyhave signentries. Nonsign solutions
  lieon circles containing4 signfillings each.
* At n>=8 thereare atmost6 signfills (possiblecounts0,2,4,6), sharpat8.
  At n4 thereare8. No claimallcountsrealizedateveryorder.

check.py is standalone stdlib exactarithmetic. It verifies converter
outputs, kernelclassifications, a nonsign rationalcircle point, the
real-inconsistentW12,10, andall256 normalizedW8,6 cases (eachhas6fills).
Run python check.py to regenerate checks.json.

Classical dependency, explicitly invoked ratherthan claimednew:
Delsarte-Goethals-Seidel conference normalization, restated in
Geramita-Verner, Orthogonal Designs with Zero Diagonal, Theorem2,
https://doi.org/10.4153/CJM-1976-028-3
Primary source was inspected in the precedingpass. Proofs/code here
are independently derived. No externalcode copied, noLean, no commits,
no old-file edits, no all-orderexistence or novelty claim.
