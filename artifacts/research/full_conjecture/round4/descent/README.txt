Interaction-only tensor descent: research result, 20 November 2026

descent.tex is a self-contained section extending round3 tensor stability.
It assumes the round3 definitions T,S,q,r and its trace-sum identities.
No novelty claim is made. No Lean or external code is included.

Main rigorous additions:
1. A smaller activation bound from symmetric trace-zero basis averages.
2. The activating generator has all one-factor partial traces zero.
3. Independent tensor-factor optimization preserves any base local minimum.
4. Local nearest-product projection erases the full quadratic energy gain.
5. An explicit exact order-36 construction illustrates why dimension descent
   cannot be a universal rule (order 6 has no Hadamard matrix).
6. For paired-spectrum symmetric interaction factors, normalized relative
   partial traces are positive definite near zero, so polar-factor extraction
   returns every original factor exactly, even along a strictly decreasing
   order-25 curve from the strict order-5 local minimum.

Run: python check.py
The standard-library exact-rational checker writes checks.json. Finite
checks support the derivations; the proofs in descent.tex establish the
general statements. The source is newly written for this project.
