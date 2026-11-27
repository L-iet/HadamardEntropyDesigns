ROUND 15: STRUCTURED ESCAPES OF THE DISCRETE TENSOR TRAPS

Main fragment: main.tex
Original exact checker: check.py
Output: checks.json

Results
1. General heterogeneous Hadamard-layer identity. For Hadamard B orderm
   and arbitrary base matrices A_p orderN, define
     H_(i,p),(j,q)=(A_p)_ij B_pq.
   Exact Gram decomposition gives F(H)=m^2 sum_p F(A_p).
   This embeds independent base landscapes into structured rowlayers.
2. A base entry flip becomes an m-entry strip flip in one actual row,
   with exact costm^2 times the base cost. For the order8 trapA,
   stripescape requires exactly3 strips and has optimal strip-path energy
   barrier8m^2. Explicitcells(2,4),(2,2),(2,3) affect only one actual
   expanded row and3m entries, ending at energy152m^3-24m^2.
   These optimality claims concern stripmoves, NOT arbitrary entrymoves.
3. Four explicit base row updates repairA toHad8, with energy
     152->120->96->56->0.
   They lift to4 improving block-row replacements repairingA tensorB
   completely, or4m strictly improving ordinary-row replacements.
   The construction changes7m^2 entries. No global minimalrepair claim.
4. The layerfamily is Hadamard iff every base layer is Hadamard, making
   explicit why this special repair does not establish an unknown order.

Reproduce
  python research/full_conjecture/round15/exchanges/check.py
Checks all base singles/pairs, the explicit stripbarrier path, each base
rowrepair, heterogeneous layers, direct expanded Grams/energies atHadfactor
orders2,4,8, every ordinaryrow improvement, total changedrows/entries,
and final Hadamardness. Exact integers, Python standardlibrary only.

Scope
This constructively escapes the preceding one-/two-entry traps when the
factor structure is known. It is not a universal rowrepair algorithm or
new all-order Hadamard result. Classical Hadamard tensor/block operations
are the background; priority for these particular exact repair and barrier
certificates is unestablished. No external code, oldroundedits, Lean work,
commits or submissions.
