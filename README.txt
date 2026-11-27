ENTROPY DESIGNS

Responsible author and maintainer: Joshua Mark.
ORCID: https://orcid.org/0009-0003-5905-2382

VERIFIED SCOPE: 84/89 principal paper claim records.
Proof development is paused. This release submits only configured proved
declarations. The paper identifies every result outside that scope.
Unsubmitted records: E07.03, E08.02, E26.03, E26.04, E26.05.
E07.03 has a checked private proof, but public integration and verification
are unfinished; it is not included in the submitted formalization.
Read paper/main.pdf, paper/ALIGNMENT.json and submission/SCOPE.json.
No full Hadamard-conjecture proof, novelty or registry acceptance is claimed.

BUILD AND SOURCE-BOUND AUDIT
lake exe cache get
python scripts/record_verified_sources.py
python scripts/audit_mathlib_licenses.py
python -m pip install -r scripts/requirements-submission.txt
python scripts/validate_metadata.py
python scripts/build_paper.py
python scripts/refresh_paper_bundle.py

The source recorder performs real ordinary builds of every configured proof
and independent Challenge entry point and audits every compared declaration.
It binds source/config hashes only after those checks succeed unchanged.
Only propext, Classical.choice and Quot.sound are allowed. Intentional proof
placeholders belong only to independent Challenge specifications.
On Windows, HADAMARD_NATIVE_TEX=1 selects the installed native TeX engine.

LOCAL SUBMISSION PREPARATION
python scripts/check_submission.py
python scripts/check_submission_preparation.py

The preparation check covers the explicitly declared verified scope, every
comparison group, current builds/axiom audits, paper/PDF bindings, metadata,
licenses and local dual-kernel evidence. Historical kernel acceptance may be
reused only for byte-identical fresh exports and is labelled in its report.
It is not a fresh registry verification. See submission/PALOMAR_ENTRIES.txt.

SANDBOXED COMPARISON AND REGISTRY PREFLIGHT
python scripts/run_comparator.py
python scripts/check_submission_preparation.py --require-sandbox

Run these on a compatible Linux host with bubblewrap available. Both Lean
and NanoDa acceptance are required for every configured group. The existing
check_submission.py --ready command remains the stronger whole-paper gate;
it intentionally fails if any principal paper claim remains unformalized.

After publishing an immutable commit, the manual "Official Palomar mechanical
preflight" GitHub workflow can check one chosen Comparator configuration
using the pinned official verifier. This workflow is advisory: it performs no
registry submission or registration. One configuration corresponds to one
Palomar entry; multiple configurations must be submitted separately.
No global AppArmor namespace restriction is disabled by this repository's CI.

PUBLICATION STATUS
No commit, push, external workflow dispatch or registry submission was made
as part of this preparation. A public immutable commit and Palomar's actual
mechanical/editorial checks remain external steps. Local preparation reports
must not be described as registry verification or acceptance.

DEPENDENCIES AND LICENSING
Lean 4.35.0, exactly matching pinned mathlib. All nine package revisions
and Apache-2.0/MIT license evidence are recorded in submission/mathlib-licenses.json.
New proof code is original. Public papers are mathematical sources, not
unlicensed code dependencies. Project license: Apache-2.0.
Source hashes use canonical LF bytes, avoiding LF/CRLF verification drift.
Local .lake state is a disposable cache and is excluded from Git.

The artifacts directory preserves the earlier author's research proofs,
experiments, data and PDFs for reference. It overlaps companion projects
and does not enlarge this project's formalized claims. Its notice and
snapshot distinguish historical evidence from current verification.

Public repository: https://github.com/L-iet/HadamardEntropyDesigns
Use an immutable commit for the declared verified submission scope. Registry
verification and editorial review remain separate submission requirements.

VERIFIED CONFIGURED-TARGET SNAPSHOT
All configured theorem targets passed local exported-proof Comparator,
Lean kernel and NanoDa checks. This diagnostic disabled source sandboxing
and is NOT a Palomar run. See submission/local-comparator-result.json.
The standard sandboxed comparison and full principal proof coverage remain
required by --ready. No supporting pass certifies the whole paper.
