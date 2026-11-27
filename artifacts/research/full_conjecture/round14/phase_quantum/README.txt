Round14 positive quaternary completion bridge

completion.tex input-readyfragment; paper.tex/PDF standalone. A rank-two
residual K has BlochGram B_ij=|Kij|^2/2-1. Complex flat completion iff
rankB<=2. For even quaternary input, B entries are -1,0,1 and an exact
phase-graph algorithm produces quaternary completing columns whenever
rank<=2. Using CLASSICAL real codimension-four completion, rank3 is
impossible: its six complex lines would supply12 real antipodal row
directions while a four-sign residual permits only8. Thus every such
quaternary codim2 partial frame completes. Classical input is explicitly
named/cited and not claimed proved from scratch or new.

Run python check.py: exact Fraction-pair Gaussian arithmetic at orders
4,6,8, phase-graph reconstruction, Gram checks, codim1 check, abstract
rank3 residual. search.py records only a bounded small-frame search;
it is not needed by the proof and makes no nonexistence inference.

No external code, Lean or commits. New code Apache-2.0 under research
parent LICENSE. Does not supply the large partialframe at unknownorders.
