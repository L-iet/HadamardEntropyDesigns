ROUND THREE: SHARP CHARACTER-SPAN ENERGY FLOORS

Read sharp_character_span.tex. Run python check.py to reproduce checks.json.
Only Python standard library is used. No Lean, commits, or external code.

MAIN PROVED INSIGHT

The previous skew-character sufficient threshold (m^2+6m+21)/16 is
not merely sharp in the three-character-plus-one-J construction. It is
the global minimum energy in the ENTIRE integer family
  A_i = z^(r_i) (u_i L + v_i + w_i J),
subject to coefficientwise oddness and scalar sum of Hermitian norms.
This permits arbitrary integer coefficients and independent shifts.

For symmetric quadratic characters, the exact minimum is instead
(m^2+2m+5)/8, attained by two L+/-1 channels and two J corrections.

Consequently this entire affine quadratic-character template reaches
the binary boundary at prime lengths exactly 3,5,7, and no prime>=11.
Any improvement toward all-order existence must leave this template.
There is no nonexistence claim for unrestricted Hadamard matrices.

A second obstruction permits arbitrary last two binary channels:
fixing two skew Legendre channels cannot be completed at any prime
p=11 mod36. This follows from the row-sum sum-of-two-squares condition;
there are infinitely many such primes by Dirichlet's theorem.

These are elementary deductions; no bibliographic novelty is claimed.
The uniform proof establishes the statements. Finite certificates are
checks of construction minima and selected arbitrary templates only.
