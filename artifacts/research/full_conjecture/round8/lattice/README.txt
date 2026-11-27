Odd-coset benchmark: explicit repair and nonmonotone arithmetic potential
20 November 2026

lattice.tex contains a fully explicit one-row augmentation of the
12x24 terminal norm40 benchmark. Deleting old row1 permits exactly
five mutually orthogonal insertions; all16 candidate classes are
enumerated, and their graph has clique number5. The new16x24 frame
is terminal and has an odd-sum row-span witness e0+e9-e11, so no
all-odd integer kernel vector exists after the augmentation.

Thus row growth12->16 can make the odd-coset minimum worsen40->infinity.
Every individual deletion trivially closes the minimum to24 by putting
the deleted old row into the kernel, so norm-gap closure alone does not
identify which deletion will allow augmentation.

A general rounding-defect lemma identifies exactly the bad retained
rows for a +/-1,+/-3 odd kernel vector. Odd exception count makes sign
rounding orthogonal to none of the old rows. No universal bounded
augmenting-exchange theorem in exception count is claimed.

check.py is newly written standard-library Python using exact integer
and rational arithmetic. It imports no outside code or project modules.
Run python check.py to regenerate checks.json. No Lean or git commits.

Primary context source:
Verheiden, Integral and rational completions of Hadamard matrices,
https://doi.org/10.1016/0097-3165(80)90028-X
The actual finite frame was recorded in this project's earlier searches;
the repair and certificates are independently checked here. No novelty
claim or proof of the full Hadamard conjecture is asserted.
