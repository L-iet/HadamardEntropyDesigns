# Build, provenance, and formalization guide

This document contains the reproducibility and submission details for the mathematics introduced in the [README](README.md) and [further results](RESULTS.md).

## What the formalization covers

The public Lean development covers **84 of 89 principal manuscript results**. A principal result is one of the statements tracked in the paper-to-code correspondence, rather than a count of all supporting lemmas. The complete correspondence is in [paper/ALIGNMENT.json](paper/ALIGNMENT.json); [submission/SCOPE.json](submission/SCOPE.json) specifies which results are included in the prepared submission.

The labels in those files are bookkeeping identifiers. The prefixes refer to the projects: TS means tensor stability, PG phase geometry, CT completion theory, and E entropy designs. RH means the Riemann hypothesis; GRH means its generalized version. These hypotheses occur only in statements explicitly identified as conditional. They distinguish statements and their proof status; they are not additional mathematical hypotheses. The final table below explains each label by its theorem title. Proof development is currently paused.

### Results outside the public formalization

- **Completion-assisted rounding** (`E07.03`): A checked private proof exists, but source integration and public-project verification are unfinished. It is not included in the submitted formalization.
- **Where the hierarchy becomes equivalent to existence** (`E08.02`): The complete principal statement has not been formalized. Supporting lemmas or computational certificates do not establish the whole claim.
- **Unconditional polynomial rates** (`E26.03`): The complete principal statement has not been formalized. Supporting lemmas or computational certificates do not establish the whole claim.
- **Conditional RH rates** (`E26.04`): The complete principal statement has not been formalized. Supporting lemmas or computational certificates do not establish the whole claim.
- **Only sublinearly many extra atoms** (`E26.05`): The complete principal statement has not been formalized. Supporting lemmas or computational certificates do not establish the whole claim.

## Build the proofs

Install Lean through elan, then run from this repository:

```sh
lake exe cache get
lake build
```

The toolchain is Lean **4.35.0**, with mathlib and its dependencies pinned in `lean-toolchain` and `lake-manifest.json`. Lake is Lean's build tool; mathlib is the community mathematics library. Downloading its cache avoids recompiling the library.

For a complete build and recorded axiom audit:

```sh
python scripts/record_verified_sources.py
python scripts/audit_mathlib_licenses.py
python -m pip install -r scripts/requirements-submission.txt
python scripts/validate_metadata.py
python scripts/check_submission.py
python scripts/check_submission_preparation.py
```

The recorder checks all configured proof and independent specification entry points. It records source hashes only after the ordinary builds and declaration audits succeed without input changes. An axiom audit checks every logical assumption on which a theorem depends. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed; they express propositional extensionality, classical choice, and soundness of quotients. No additional mathematical axioms or unfinished proofs are permitted in solution code.

The structure/scanner tests run before Lean setup in CI. Tests that use `.lake/` create their fixture parent themselves; they do not assume a downloaded cache or a previous build. No README, technical-guide, paper-disclosure wording, or abstract prefix is enforced by the theorem-coverage check. The guide above lists unfinished results for readers.

### Independent statements and proof checking

Comparator is Lean's tool for comparing a submitted proof against an independently written statement. A `Challenge` module specifies statements using mathlib and core Lean; a `Solution` module supplies their proofs. Intentional placeholders occur only in the independent specification, which the solution must not import. They are not accepted proof dependencies.

The configurations below select groups of theorem statements and definitions. One configuration corresponds to one proposed Palomar entry, not automatically to every result in this paper. NanoDa is an independent proof checker; both it and Lean's own kernel must accept each group.

| Group | Configuration |
|---|---|
| Affine | [comparator-affine.json](comparator-affine.json) |
| Barrier | [comparator-barrier.json](comparator-barrier.json) |
| Boolean | [comparator-boolean.json](comparator-boolean.json) |
| Buffer | [comparator-buffer.json](comparator-buffer.json) |
| Cofinite | [comparator-cofinite.json](comparator-cofinite.json) |
| Collision | [comparator-collision.json](comparator-collision.json) |
| Complete sequence | [comparator-complete-sequence.json](comparator-complete-sequence.json) |
| Cubic | [comparator-cubic.json](comparator-cubic.json) |
| Denominator | [comparator-denominator.json](comparator-denominator.json) |
| Distance | [comparator-distance.json](comparator-distance.json) |
| Face | [comparator-face.json](comparator-face.json) |
| Family | [comparator-family.json](comparator-family.json) |
| Gap | [comparator-gap.json](comparator-gap.json) |
| Hierarchy | [comparator-hierarchy.json](comparator-hierarchy.json) |
| Moderate | [comparator-moderate.json](comparator-moderate.json) |
| Moments | [comparator-moments.json](comparator-moments.json) |
| Permutation cost | [comparator-permutation-cost.json](comparator-permutation-cost.json) |
| Plotkin | [comparator-plotkin.json](comparator-plotkin.json) |
| Prime exponent | [comparator-prime-exponent.json](comparator-prime-exponent.json) |
| Prime | [comparator-prime.json](comparator-prime.json) |
| Project | [comparator-project.json](comparator-project.json) |
| Quadratic classification | [comparator-quadratic-classification.json](comparator-quadratic-classification.json) |
| Quantum bounds | [comparator-quantum-bounds.json](comparator-quantum-bounds.json) |
| Quantum | [comparator-quantum.json](comparator-quantum.json) |
| Radix | [comparator-radix.json](comparator-radix.json) |
| Relative | [comparator-relative.json](comparator-relative.json) |
| Seed repair | [comparator-seed-repair.json](comparator-seed-repair.json) |
| Simplex entropy | [comparator-simplex-entropy.json](comparator-simplex-entropy.json) |
| Spanning | [comparator-spanning.json](comparator-spanning.json) |
| Support | [comparator-support.json](comparator-support.json) |
| Symmetric | [comparator-symmetric.json](comparator-symmetric.json) |
| Trade | [comparator-trade.json](comparator-trade.json) |
| Translation orbits | [comparator-translation-orbits.json](comparator-translation-orbits.json) |
| Witness | [comparator-witness.json](comparator-witness.json) |
| Main statements | [comparator.json](comparator.json) |

For local diagnostics of a selected group:

```sh
python scripts/run_local_comparator.py --config comparator.json
```

Local reports are in `submission/local-comparator*-result.json`. A documentation-only rebinding may update the source inventory after a disclosure-check script changes; it records the previous published report, checks that all Lean sources, build inputs, and exported proof bytes are unchanged, and does not claim another kernel run. They record actual kernel acceptance, or explicitly identified reuse of earlier acceptance for byte-identical exports. Such reports do not establish sandboxed registry verification. Earlier tensor-stability and phase-geometry receipts do not record original checker-binary digests; that limitation remains disclosed in their evidence.

For sandboxed checks on a compatible Linux host with bubblewrap installed:

```sh
python scripts/run_comparator.py
python scripts/check_submission_preparation.py --require-sandbox
```

Bubblewrap isolates the source build. The preparation check also validates source bindings, complete target audits, paper/PDF bindings, licenses, and metadata. `python scripts/check_submission.py --ready` is the stricter whole-paper gate: it additionally requires complete principal-result coverage, so it fails while any principal manuscript result remains unformalized.

## Paper and publication

The [current paper](paper/main.pdf), [LaTeX source](paper/main.tex), and [standalone source bundle](paper/source.tar.gz) accompany the proofs. Rebuild them with:

```sh
python scripts/build_paper.py
python scripts/refresh_paper_bundle.py
```

On Windows, set `HADAMARD_NATIVE_TEX=1` to use the installed native TeX engine. Paper and proof-source hashes are recorded separately. Text files use LF line endings; `.gitattributes` keeps Git's text representation consistent. Historical artifacts retain their original bytes.

The repository is published on GitHub on `main`. Use the full immutable commit hash when requesting verification. The manual **Official Palomar mechanical preflight** GitHub workflow invokes a pinned official verifier for a chosen configuration; it does not register or submit the project. [submission/PALOMAR_ENTRIES.txt](submission/PALOMAR_ENTRIES.txt) lists the available entries. Local preparation, official mechanical verification, editorial review, and registry acceptance are distinct steps. The prepared CI does not globally disable AppArmor restrictions.

## Dependencies, licenses, and historical material

The nine pinned dependency revisions and their permissive license evidence are recorded in [submission/mathlib-licenses.json](submission/mathlib-licenses.json). See [DEPENDENCIES.txt](DEPENDENCIES.txt) and [LICENSE](LICENSE). Public papers are cited as mathematical sources; access to a paper is not treated as permission to redistribute its code.

Original project code is Apache-2.0.

The `artifacts/` directory preserves earlier research proofs, experiments, data, and PDFs. It overlaps companion projects and is historical reference material, not an expansion of the current formalized claims. Its notice and snapshot describe that distinction. Generated `.lake/` files are disposable local build state and are excluded from Git.

## Theorem labels and public coverage

Each identifier below refers to a principal manuscript result. “Public proof” means its named Lean declarations are included in the configured public proof set; “Excluded” means the whole result is outside that set. Supporting lemmas do not change an excluded result’s status.

| Identifier | Mathematical statement | Coverage |
|---|---|---|
| `E04.01` | Denominator obstruction to a new sign row | Public proof |
| `E04.02` | A prime-factor lower bound for positive trade volume | Public proof |
| `E04.03` | Uniform bounded-degree moves cannot suffice | Public proof |
| `E04.04` | A quantitative infinite subsequence | Public proof |
| `E04.05` | A universal half-row trade | Public proof |
| `E04.06` | Exponential multiplicity of isolated states | Public proof |
| `E06.01` | Residue-sensitive collision bound and equality | Public proof |
| `E07.01` | A positive entropy window suffices | Public proof |
| `E07.02` | One saturated atom in every even dimension | Public proof |
| `E08.01` | Exact false positive for one-copy uniformity | Public proof |
| `E09.01` | Rigidity of positive diagonal balancing | Public proof |
| `E09.02` | The natural classical and operator capacities are blind | Public proof |
| `E09.03` | Elementary parity gap | Public proof |
| `E10.01` | Collision--moment rounding certificate | Public proof |
| `E10.02` | Explicit collision gap | Public proof |
| `E10.03` | Nonsingular modular seeds need not lift | Public proof |
| `E10.04` | Sharp weighted collision bound | Public proof |
| `E10.05` | Equality rigidity and two-column reconstruction | Public proof |
| `E11.01` | Nonnegative defect decomposition | Public proof |
| `E11.02` | Explicit extraction from a sufficiently small deficit | Public proof |
| `E12.01` | Collision cost of full coordinate symmetry | Public proof |
| `E12.02` | Shannon entropy is almost maximal | Public proof |
| `E13.01` | Local maximum criterion | Public proof |
| `E13.02` | Explicit four- and five-bit traps | Public proof |
| `E13.03` | A trap at admissible Hadamard order eight | Public proof |
| `E13.04` | Arbitrarily poor traps at admissible orders | Public proof |
| `E13.05` | A certified collision barrier | Public proof |
| `E14.01` | Complete rigidity from additive coverage | Public proof |
| `E14.02` | The smallest binary seed forces a power-of-two law | Public proof |
| `E14.03` | Approximate moment version | Public proof |
| `E15.01` | Maximum overlap and optimal straight bridge | Public proof |
| `E15.02` | Complete any maximum overlap subset | Public proof |
| `E15.03` | Finite nonlocal rewiring | Public proof |
| `E16.01` | Nonnegative exact correction | Public proof |
| `E16.02` | A sufficient input window for exact extraction | Public proof |
| `E16.03` | Quantization obstruction for a uniform row candidate | Public proof |
| `E18.01` | Affine observable budget | Public proof |
| `E18.02` | Complement criterion for low-degree extensions | Public proof |
| `E18.03` | Sharp cubic benchmarks at orders twelve and twenty | Public proof |
| `E18.04` | Fixed algebraic degree cannot suffice asymptotically | Public proof |
| `E19.01` | Actual positive correction with an explicit margin | Public proof |
| `E19.02` | No adaptive reweighting on a minimal-size support | Public proof |
| `E20.01` | Binary rank of a minimal-support target | Public proof |
| `E20.02` | Support-overlap rigidity | Public proof |
| `E20.03` | An explicit near-moment candidate | Public proof |
| `E20.04` | A nonvacuous asymptotic obstruction to dimension-free rounding | Public proof |
| `E21.01` | Even restriction code and its radical | Public proof |
| `E21.02` | Exact fixed-support criterion for a full basis | Public proof |
| `E21.03` | Degree saturation near a power of two | Public proof |
| `E21.04` | Punctured-observable bounds, without completion | Public proof |
| `E21.05` | Exact finite obstruction | Public proof |
| `E22.01` | A finite exact escape rule | Public proof |
| `E22.02` | The unavoidable barrier is exactly $1/288$ | Public proof |
| `E23.01` | A quantitative moment-error floor | Public proof |
| `E23.02` | Minimum support edits to unlock degree repair | Public proof |
| `E24.01` | An exact monotone support-reduction algorithm | Public proof |
| `E24.02` | Sharp barrier for a specified straight bridge | Public proof |
| `E25.01` | A support witness against all Hadamard mixtures | Public proof |
| `E25.02` | Sharp distance and global repair family | Public proof |
| `E25.03` | Exact fixed-support collision optimum | Public proof |
| `E25.04` | Simultaneous face optimum, strict trap, and sharp distance | Public proof |
| `E25.05` | A certified local barrier | Public proof |
| `E25.06` | Moderate-support regimes | Public proof |
| `E25.07` | General support bound without a small-$k$ restriction | Public proof |
| `E25.08` | Spanning omitted slopes give the sharp distance | Public proof |
| `E25.09` | A near-optimal relative regime | Public proof |
| `E25.10` | No dimension-independent stability, even for exact moments | Public proof |
| `E26.01` | No residue-class restriction is needed | Public proof |
| `E26.02` | An ordinary-prime-gap transfer | Public proof |
| `E27.01` | Uniform Hadamard-gap transfer | Public proof |
| `E28.01` | Unconditional near-square instability from the multiplier bound | Public proof |
| `E29.01` | Exact projective and commuting criteria | Public proof |
| `E29.02` | Uniform tight frames are uniformly almost commuting | Public proof |
| `E30.01` | Simplex count | Public proof |
| `E30.02` | Second-order entropy bound | Public proof |
| `E30.03` | Finite radix certificate | Public proof |
| `E31.01` | Isolation under all coordinate-cube moves | Public proof |
| `E31.02` | Sharp maximum-weight constraint | Public proof |
| `E31.03` | Exact limitation of monotone triple conversion | Public proof |
| `E31.04` | Exponential cost of full permutation symmetry | Public proof |
| `E31.05` | An explicit cofinite central ray | Public proof |
| `E32.01` | Sparse uniform candidates cannot enter the extraction window | Public proof |
| `E33.01` | Complete four-bit entropy diagram | Public proof |
| `E34.01` | Spanning-slope summary input | Public proof |
| `E07.03` | Completion-assisted rounding | Excluded; see explanation above |
| `E08.02` | Where the hierarchy becomes equivalent to existence | Excluded; see explanation above |
| `E26.03` | Unconditional polynomial rates | Excluded; see explanation above |
| `E26.04` | Conditional RH rates | Excluded; see explanation above |
| `E26.05` | Only sublinearly many extra atoms | Excluded; see explanation above |
