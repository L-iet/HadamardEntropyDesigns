ROUND 14: DISCRETE GRAM-ENERGY FLIP TRAPS

Main assembler fragment: spectral.tex
flips.tex is the same branch source for convenience; include only one.
Original exact certificates: check.py and checks.json.
The trap8/12/16 JSON files and explore.py record exploratory searches;
only the order8 certificate is used for the infinite theorem.

Results
1. Exact flip calculus for F(H)=||HH^T-nI||F^2:
   delta_ia=8[(2n-1)-h_ia(HH^TH)_ia]. Exact two-cell interactions are
   given for shared-row, shared-column, and distinct-row/column pairs.
   Even-order single flips are always8mod16, so never neutral.
2. Explicit order8 nonglobal strict single-entry trap, energy152.
   Its64 single flips increase energy by8,40,72; every one of2016
   two-entry changes is nonnegative. There are110 neutral pairs.
   All41664 triples checked; minimum change-24. Cells0,5,60 give
   path152->160->152->128, proving optimal escape barrier8 and minimum
   direct Hamming escape distance3.
3. Tensoring this matrix with ANY Hadamard factor of orderm>=2 gives
   positive energy152m^3 and STRICT local minima for both one- and
   two-entry moves. Exact minima: delta1=16m-8, delta2=32(m-1).
   This provides infinite examples at known Sylvester orders8*2^r.
4. Exact enumeration of all512 normalized order4 sign matrices gives
   only six Hadamard local minima. Thus8 is the first admissible traporder.

Reproduce
  python research/full_conjecture/round14/spectral/check.py
Every base one/pair/triple energy is computed directly. Pair interactions
are independently compared with the formula. All32640 pairs atorder16
are directly recomputed; all523776 pair formulas atorder32 are evaluated,
with2039 direct Gram recomputations. The uniform theorem is algebraic,
not inferred from those finite tests. All arithmetic integer, standardlib.

Scope and priority
Local energy traps and simulated/quantum annealing are established topics;
no novelty claim is made for the phenomenon. Priority for this particular
exact trap/tensor certificate is unverified. This rules out universal
improving one- or two-entry descent as a Hadamard existence proof, but does
not rule out nonlocal search or prove nonexistence at any admissibleorder.
The base has an explicit three-entry escape. No all-order construction.

Primary background
Finding a Hadamard Matrix by Simulated Quantum Annealing(2018)
https://www.mdpi.com/1099-4300/20/2/141
Quantum computing formulation of some classical Hadamard matrix searching
methods and its implementation on a quantum computer(2021)
https://doi.org/10.1038/s41598-021-03586-0
No downloaded sourcecode, oldroundedits, Lean work, or gitcommits.
