Parity-witness repair budgets and a calibrated Euclidean obstruction
20 November 2026, bounded research pass

repair.tex is a self-contained TeX section fragment.

General results:
* Any odd-sum integer vector f gives a Bessel repair budget. Arbitrary
  signed indicators of unequal or overlapping odd blocks are included.
* Simultaneous witnesses give weighted constraints on which rows must
  be deleted. Installed affine-plane rows can be rigorously preferred
  over repeated old rows in the constructive tensor family.
* Witness budget is congruent to the missing-row count mod8. A parity
  deficit cannot first appear before8 missing rows.
* An odd-sum vector in the saturated row lattice exists exactly when
  no all-odd integer kernel vector exists. Proof uses primitive-lattice
  reduction modulo2. An elementary halving algorithm finds a certificate.

New finite certificates on previously recorded local examples:
* The earlier16x24 terminal frame has two norm3 signed-indicator
  witnesses, giving a small direct unextendibility proof and row filters.
* The earlier12x24 terminal frame has all-odd integer kernel minimum
  squared norm EXACTLY40, so it passes parity feasibility but admits
  no sign row (which would have norm24). It also has no norm32 vector.
  Exact information-coordinate enumeration uses2048+24576 assignments.

All masks are embedded in the checker, so no other project files or
external packages are required. Python standard library only; newly
written code; exact integer/rational calculations. Run python check.py
to regenerate checks.json. No Lean or git commits.

Primary arithmetic-completion sources consulted online:
https://thesis.caltech.edu/2899/
https://doi.org/10.1016/0097-3165(80)90028-X
The proofs are self-contained. No external code was imported, and no
novelty or full Hadamard-conjecture proof is claimed.
