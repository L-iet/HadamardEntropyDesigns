RESTRICTED-ALPHABET CODES AND AN EXACT CODE PIVOT

codes.tex contains the mathematical proofs; check.py uses original
Python standard-library code and exact arithmetic. checks.json stores
the finite-field bases and sign-row witnesses.

For N=4q with q odd, pairwise modularly orthogonal sign classes are
orthogonal within each sign-product parity. If both parities occur,
each has at most four classes. A self-orthogonal module containing
five real orthogonal rows therefore has mutually compatible sign
words: counting them suffices, without a further clique search.
Nine modular classes already force real orthogonality.

For a prime modulus, an exact sign extension outside a self-dual code
gives a self-dual neighbor that preserves every old sign class.
This removes an artificial code restriction but cannot escape a
terminal real frame while preserving all its rows.

Checks:
- Exhaust all self-dual ternary extensions of one prescribed five-row
  H12 seed: two codes, twelve sign classes each.
- Exact sharp mixed-parity examples for q=3,5,9.
- A self-dual ternary length12 code with zero sign words.
- One deterministic F5 self-dual extension of a prescribed H20 seed
  has eight sign classes, so five initial rows do not force a count20.
  Its eight-row frame has forty modular classes, of which thirty-two
  are exact extensions. One self-dual neighbor gives twenty mutually
  orthogonal sign classes while preserving all eight original classes.

No unknown-order matrix was constructed. The code-count criterion is
an equivalent research target, not a proved lower bound. Novelty has
not been established. Classical modular Hadamard context is credited
in the paper. No external proof code, Lean changes or Git commits.
