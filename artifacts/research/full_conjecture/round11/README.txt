ELEVENTH RESEARCH PASS

research.tex/pdf: combined report.
global_repair.tex/pdf: collision-stability and global-repair proofs.
Reproduce: python research/full_conjecture/round11/build.py

BRANCHES
designs/relative_sequence.tex: at infinitely many KNOWN Hadamard orders,
exactly isotropic laws have collision/global-optimum ratio tending to
one, and additive entropy excess tending to zero for EVERY Renyi order
(including Shannon/min-entropy), while distance from the convex hull
of ALL Hadamard laws tends to one. These laws are strict local maxima.
This disproves a dimension-independent small-repair guarantee from
relative collision or entropy excess. It does not prove a new order.
Paley prime-power orders plus an elementary irrational-rotation
subsequence give nonvacuous comparisons without prime-pattern assumptions.

designs/: explicit uniform exactly isotropic laws at known power-of-two
orders have TV distance exactly1-1/k from the convex hull of ALL
Hadamard laws. Minimum observation replacements into Hadamard blocks
is exactly D(1-1/k), attained constructively with unchanged collision.
No small-change repair theorem can apply to all such laws.

quotients/: in a four-dimensional isotropic quotient the compatible
modular sign pool is a weighted (p+1)-square rook grid. All maximal
completion codes are its rows and columns. Maximum real frame size,
and losses relative to the old code, follow from weights without a
clique search. Two exact H20 retained-space experiments have full
completions; no favorable grid is guaranteed at unknown orders.

moments/: exact first and second sign-count moments over every
self-dual completion of a retained space yield an existence certificate.
One H20 seed has mean count16 but second moment certifies count>=19,
enough for completion. A smaller retained space certifies only9.
Uniform neighbor walks contract expected sign count to the global
mean by a factor<1/p when quotient half-dimension>=3.

landscape/: census of ALL2441406 neighbors of the previous H20 terminal
code. Exactly42 improve count12, all reaching20;10 retain10old rows
and32 retain9. All42 codes are rebuilt and their real Gram checked.
Gray enumeration plus a MacWilliams transform accounts for every
neighbor, including those with no new sign word.
The exact minimum old-row losses for retained codimensions1 through10
are2,3,4,6,7,8,9,10,11,12. They are the generalized Hamming weights of
the evaluation code, checked over all4096 coordinate subsets.

VERIFICATION AND SCOPE
Eight checkers use exact standard-library arithmetic across four branches.
The written general proofs and independent audits establish the stated
uniform claims; finite checks validate their explicit benchmarks.
Classical sources are credited; no imported external code.
No full conjecture proof, unknown-order matrix, priority clearance,
Lean changes, commits or external submissions.
