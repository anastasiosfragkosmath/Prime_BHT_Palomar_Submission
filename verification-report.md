# Verification boundary and reproducible checks

This file intentionally does not claim a successful registry verification for an earlier or different revision. Verification evidence applies to the exact commit that was checked, and the checks below were run on the files of this repository, which include the sources of the earlier project described next.

The statement of the main theorem is in [`PrimeBHT/Frozen/MainTheorem.lean`](PrimeBHT/Frozen/MainTheorem.lean) and, as the statement-only text, in [`Challenge.lean`](Challenge.lean). The [semantic audit](semantic-audit.md) records its correspondence with the paper and the corrected forms of the intermediate statements.

## Included earlier project

The proof imports the author's formalization of *A Variation Norm Carleson Theorem Along the Primes* for the input X3. Its relevant part is included in this repository, not required as a Lake dependency:

- source: <https://github.com/anastasiosfragkosmath/Variational-Carleson-Along-the-Primes-Palomar-Submission>, commit `f0f9299287feeaea25f6b9cedd3e078b4a98f3c7`; the files are the import closure of the modules imported by `PrimeBHT/` (1,519 Lean files: 241 under `PrimeCarleson/`, 1,245 under `vendor/openai-math/` and 33 under `vendor/carleson/`), copied unchanged together with that project's provenance records in `vendor/provenance/`; they are built here as the libraries `PrimeCarleson`, `OAI` and `Carleson` of this package, with the library options of that project's lakefile;
- it uses the same Lean toolchain (v4.35.0) and Mathlib revision as this repository, which is the only Lake dependency;
- the three frozen definitions of that project on which the proof depends (`PrimeCarleson.e`, `PrimeCarleson.ramanujanSum`, `PrimeCarleson.blockWeight`) are bound by file hash in [`scripts/data/frozen-manifest.json`](scripts/data/frozen-manifest.json), and `scripts/frozen_abi.py` prints their ABI hashes, which equal the manifest's. The files differ from the revision used for the earlier verification of this project (`5ef339eed4950426cdd3f6016e225de506423d8b`) only in comment text (two lines of the module docstring of each file, and one cited line range of the manuscript in the docstring of `RamanujanSum.lean`); the elaborated definitions, and hence their ABI hashes, are unchanged, and the manifest records the new file hashes. The sealed theorem used for X3, `PrimeCarleson.vonMangoldt_sub_heathBrown_U3`, is imported through `PrimeBHT/Inputs/X3.lean`.

`scripts/check_dependency.py` checks that the included sources are closed under imports, the three file hashes, and, when a checkout of that project is available at `../variational-carleson-lean`, that every included file is byte-identical to the pinned revision.

## Local Lean checks

All checks below were run on 2026-11-13 with Lean 4.35.0 and Mathlib v4.35.0.

- **Build.** `lake build PrimeBHT Challenge Solution` (the default targets) passed 10,983 jobs with no error; this includes compiling the included sources of the earlier project. The only `sorry` warning is `Challenge.lean:51`, the single statement-only placeholder for the main theorem; no other file of this repository contains `sorry` in code (checked by `scripts/check_layout.py`, which strips nested comments).
- **Axioms.** `#print axioms PrimeBHT.Statements.t_maintheorem`, run through `Solution`, reports exactly `propext`, `Classical.choice`, `Quot.sound`. `scripts/interface_check.sh` reports the same three axioms for the six frozen declarations (`tri_restricted_eps`, `bht_real_smooth`, `x1_bht_smooth`, `t_finiteBV`, `p_key0`, `t_maintheorem`) and for their six providers. `scripts/axiom_audit_x2.sh` reports standard axioms for the headline declarations of the X2 chain, including `x2Statement_final`, `oSelectable_proved`, `pint_nonHilbert_O` and `overlap_O2`, and finds no `sorry`, `axiom`, `native_decide` or `unsafe` in the X2 tree.
- **Frozen anchors.** The frozen-anchor guard passes: all 30 anchors are `SEALED` (the three bound definitions of the earlier project are checked by file hash); every sealed body is exactly `by exact <provider>`; no `sorry` or custom axiom lies outside the manifest. `scripts/frozen_abi.py` reports that the elaborated declarations of the groups T0, Key0, X2, X1, M2 and M1 match the author-approved texts in [`scripts/data/approved`](scripts/data/approved). The guard is the frozen-anchor checker `check_frozen_anchors.py` of the `lean-orchestrator` skill in *LeanAutoformalizationSkills* by Scott Armstrong (https://github.com/scottnarmstrong/LeanAutoformalizationSkills, CC BY 4.0), used unmodified at commit `1837b95b3d5a9fd8d311367603902ad7fe261adf`; it is not part of this repository; the manifest it reads is [`scripts/data/frozen-manifest.json`](scripts/data/frozen-manifest.json).
- **Statement text.** `Challenge.lean` is the approved text of the main-theorem group (`primeBHT` and `t_maintheorem`), with the placeholder `sorry`. In the frozen layout the same two declarations live in two files (`PrimeBHT/Frozen/PrimeBHT.lean` and `PrimeBHT/Frozen/MainTheorem.lean`, one declaration per file, plus the frozen-anchor comments); `scripts/frozen_abi.py` is the check that they are the approved text.
- **Layout.** `scripts/check_layout.py` passes: every Lean file starts with `module` and has at most 10,000 lines; `Challenge.lean` has 60 lines and imports only Mathlib; no compiled artifacts, symbolic links or submodules; the only Markdown files are `README.md`, `semantic-audit.md`, `verification-report.md` and the two provenance notes of the included third-party code (`vendor/README.md`, `vendor/provenance/THIRD-PARTY.md`); one `LICENSE` (Apache-2.0) matching `formalization.yaml`.

## Kernel replay

`lake env leanchecker --verbose` replays each of `Solution`, `PrimeBHT.Frozen.{FiniteBV,Key0,MainTheorem}` and `PrimeBHT.Proof.{X2,Key0,MainTheorem}` in the Lean kernel and exited with status 0 for all seven. A full-closure replay in the `--fresh` mode was started during the audit of the last three seals and was **not completed**; it is not part of the evidence.

## Independent audits

Two audits of the seals were made by separate AI agents that had not written the audited material: one for `tri_restricted_eps`, `bht_real_smooth` and `x1_bht_smooth`, one for `t_finiteBV`, `p_key0` and `t_maintheorem`. Both concluded that the seals are accepted. They checked, for each declaration: byte fidelity of the frozen file (only the proof body changed, to `by exact <provider>`); equality of the statement with the approved text; that each provider has exactly the frozen type, with no added hypothesis, and consumes the intended predecessors; kernel and axiom evidence; and absence of hypothesis smuggling or vacuity (for the selection lemma `OSelectable`, now a theorem). The second audit also traversed the 151,422 constants reachable from `t_maintheorem` in a non-module environment (only the three standard axioms; no unsafe or partial definition) and token-scanned the project part of the 1,926-module import closure (no code hit for `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque` and similar). These audits were made on the layout in which the earlier project's sources are copied into the repository, as they are now; the files under `PrimeBHT/Frozen` and `PrimeBHT/Proof` are byte-identical to the audited ones. Non-blocking notes of the audits: docstrings of some internal modules still describe results that are now proved as open; intermediate definitions use junk-value constructs (Bochner integrals, `choose`, `tsum`) that cannot weaken the sealed statement; the frozen files keep their draft-era docstrings. The audit reports are the author's working notes and are not part of this repository. These audits are automated reviews, not peer review.

## Comparator and NanoDa preflight

Comparator (the Challenge/Solution comparison configured in [`comparator.json`](comparator.json), with NanoDa enabled) has **not** been run on the current files. The manual workflow [`.github/workflows/run-comparator.yml`](.github/workflows/run-comparator.yml) builds the pair and runs Comparator with NanoDa using a pinned verifier toolchain; it has not been executed yet, and a successful `lake build` is distinct from Comparator verification. The official Palomar registry performs the final, independent verification of the public repository and the selected immutable commit, so a local or private CI run is not described here as a registry acceptance.

## Reproduce the local checks

```sh
lake exe cache get
lake build
python3 -I scripts/frozen_abi.py --compare T0=scripts/data/approved/T0-approved.lean.txt \
  --compare Key0=scripts/data/approved/Key0-approved.lean.txt --compare X2=scripts/data/approved/X2-approved.lean.txt \
  --compare X1=scripts/data/approved/X1-approved.lean.txt --compare M2=scripts/data/approved/M2-approved.lean.txt \
  --compare M1=scripts/data/approved/M1-approved.lean.txt
bash scripts/interface_check.sh
bash scripts/axiom_audit_x2.sh
python3 -I scripts/check_dependency.py
python3 -I scripts/check_layout.py
for m in Solution PrimeBHT.Frozen.MainTheorem PrimeBHT.Proof.MainTheorem; do lake env leanchecker --verbose "$m"; done
```

The first `lake build` also compiles the included sources of the earlier project; the checks need a Linux or macOS machine with enough memory for Mathlib-scale builds. Do not run `lake update` to verify this checkout.

## History of the layout

On 2026-11-10 the project was put into the layout of a Palomar submission, with the part of the earlier project that the proof imports copied into the repository. On 2026-11-11 the library was cleaned up (598 unreferenced declarations and 6 emptied modules removed from `PrimeBHT/`, lint warnings 357 → 71, 13 umbrella imports of `Mathlib` narrowed, 15 proofs rewritten for speed; no declaration statement changed). On 2026-11-13 the copied sources were briefly replaced by a pinned Git dependency on the earlier project's submission repository, and then included again, unchanged, from its current commit (`f0f9299287feeaea25f6b9cedd3e078b4a98f3c7`, same 1,519-file import closure as before) so that the repository is self-contained; no file under `PrimeBHT/Frozen`, `PrimeBHT/Proof`, `Challenge.lean` or `Solution.lean` changed in these steps, and the changes under `PrimeBHT/` are docstrings and comments that named paths which no longer exist.
