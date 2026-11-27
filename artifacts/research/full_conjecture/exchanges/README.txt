ROW-EXCHANGE RESEARCH PASS — 20 NOVEMBER 2026

MAIN RESULT (EXACT FINITE COUNTEREXAMPLE)

There is a 16x24 partial Hadamard matrix for which no augmenting
exchange can delete 0, 1 or 2 rows. A 3-for-4 exchange succeeds and
the 17 resulting rows have a full order-24 completion.
Therefore universal bounded-exchange augmentation, if true, needs a
deletion constant at least 3. No universal upper bound is proved here.

results.tex contains the mathematical statements, proofs, and all
row masks needed for the finite positive certificate. It is a section
fragment for the parent research note. No novelty priority is claimed.

NEW ELEMENTARY REDUCTIONS

- A q-dimensional rational subspace meets the sign cube in at most
  2^q vectors. Information coordinates permit exact enumeration using
  2^q assignments, or 2^(q-1) up to global negation.
- Equality occurs exactly for signed coordinate-duplication spaces.
- For a partial Hadamard residual space, equal cube count forces equal
  duplication block sizes n/q. Completion then reduces to H(q).

REPRODUCE FROM D:\Papers\Hadamard

  python research/full_conjecture/exchanges/sample.py
  python research/full_conjecture/exchanges/augment.py
  python research/full_conjecture/exchanges/verify.py

sample.py reproduces the seeded 30-run experiment and partial24.json.
augment.py exhausts all deletion sets of sizes 0, 1, and 2, finds the
three-row deletion witness, and stores augmentation24.json. It uses the
new exact cube_kernel.py implementation, not floating-point nullspaces.
verify.py independently traverses all 8,388,608 normalized sign vectors,
checks the 137 deletion sets, and verifies the positive exchange and
full completion. It does not call cube_kernel.py.

verification.json records success. independent24.json records all 56
vectors whose nonorthogonality support has size at most two, and all
small deletion-set candidate counts. All arithmetic is exact and all
code is newly authored using only Python's standard library.

STATUS

No full conjecture proof, no Lean code, no commits, no edits outside
this subdirectory. The original two-row possibility is refuted by this
certificate, but this does not refute a larger fixed exchange bound.

LITERATURE CONTEXT

Known near-completion results go to seven missing rows. This pass does
not rely on them for its finite completion: the full Gram matrix is
checked directly. The source trail checked during this pass includes
Verheiden's thesis https://thesis.caltech.edu/2899/ and Banica--Skalski's
partial-matrix discussion https://arxiv.org/abs/1310.3855. The latter
explicitly records the seven-row completion range. Neither source was
copied as code, and the new elementary lemmas are not claimed as novel.
