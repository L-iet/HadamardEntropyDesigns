Support-moving four-row weighing repair
20 November2026

main.tex proves an exact admissibility criterion for mixing two whole
zero-row pairs by normalizedSylvesterH4/2. The operation preserves
the weighingGram and alphabet iff everyoutside-column fourfoldsign
product is-1. Zero positions maymove within the selected4x4 corner.

It repairs the explicit unfillableW12,10: first4rows switched, then
2 signfillings exist. FullintegerGram certificates are embedded.
Costs:26entrieschanged inW,22oldnonzeros changed/erased,8supportstatus
changes. EachresultingHad12 violates20of120oldnonzero prescriptions,
allinfirst4rows. NO GLOBAL MINIMALITY CLAIM is made.

A separate theorem shows same-zero-support changes confinedto1or2
zero-rowpairblocks are signedrowpermutationequivalences, so cannot
changecompletionfeasibility. The positive switch escapes by movingzeros.

check.py is standalone exactstdlib Python and includes the old8-root
obstruction, every15rowpairchoice for thisQorientation, bothnewHad
Gramchecks, and boundedfailedHouseholderselector search(3200cases).
Run python check.py to regenerate checks.json.

Classical orthogonal-design context (primary source previously read):
Geramita-Verner, Orthogonal Designs with Zero Diagonal,
https://doi.org/10.4153/CJM-1976-028-3
No sourcecode imported. No novelty/all-orderguarantee, Lean, commits,
or older-file edits.
