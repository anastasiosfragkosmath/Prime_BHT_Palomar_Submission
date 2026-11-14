# Lean verification of "The Bilinear Hilbert Transform Along the Primes"

A Lean 4 + Mathlib formalization of the main theorem of *The Bilinear Hilbert Transform Along the Primes* by Anastasios Fragkos, Ben Krause, Michael Lacey, Nazar Miheisi and Yu-Chen Sun.

- [Paper](source-paper/Prime_BHT_final.tex)
- [Bibliography](source-paper/primeBHTbib.bib)

## Main result

Let $\Lambda$ be the von Mangoldt function. For finitely supported $f,g:\mathbb Z\to\mathbb C$ write

```math
\mathcal H_{\mathbb P}(f,g)(x)=\sum_{n\neq 0}\frac{\Lambda(|n|)}{n}\,f(x-n)\,g(x+n),\qquad x\in\mathbb Z .
```

**Theorem** (`t:maintheorem`). Let $p,q\in(1,\infty)$ and $\frac1r=\frac1p+\frac1q$ with

```math
\frac2p+\frac3q<3,\qquad \frac3p+\frac2q<3 .
```

Then there is a constant $C=C_{p,q,r}$ such that for all finitely supported $f,g:\mathbb Z\to\mathbb C$

```math
\bigl\|\mathcal H_{\mathbb P}(f,g)\bigr\|_{\ell^r(\mathbb Z)}\le C\,\|f\|_{\ell^p(\mathbb Z)}\,\|g\|_{\ell^q(\mathbb Z)} .
```

This region contains the Banach range $r\ge 1$ and a portion of the quasi-Banach range $r\in(\frac23,1)$; on the diagonal it reaches up to, and excludes, the endpoint $(\frac53,\frac53,\frac56)$. The Lean statement uses the estimate on finitely supported functions, which is the dense subspace on which the operator is defined; see the [semantic audit](semantic-audit.md).

## Main Lean declarations

- [`PrimeBHT.Statements.t_maintheorem`](PrimeBHT/Frozen/MainTheorem.lean): the main theorem, with `PrimeBHT.Statements.primeBHT` the operator $\mathcal H_{\mathbb P}$. Its body is `by exact PrimeBHT.Proof.t_maintheorem`.
- [`Challenge.lean`](Challenge.lean): the statement alone (Mathlib imports only; one author-approved `sorry` for the theorem). It is the text approved by the author, [`scripts/data/approved/T0-approved.lean.txt`](scripts/data/approved/T0-approved.lean.txt).
- [`Solution.lean`](Solution.lean): re-exports the proved declarations. [`comparator.json`](comparator.json) compares `PrimeBHT.Statements.t_maintheorem` between the two; the manual [Comparator workflow](.github/workflows/run-comparator.yml) runs that comparison with NanoDa.

The [semantic audit](semantic-audit.md) describes the correspondence with the paper.

## Structure of the proof

The statements below are frozen, author-approved Lean declarations (one declaration per file under [`PrimeBHT/Frozen`](PrimeBHT/Frozen)); each is proved in a separate provider module under [`PrimeBHT/Proof`](PrimeBHT/Proof), and the frozen file's body is only `by exact <provider>`.

| Frozen declaration | Content | Provider |
| --- | --- | --- |
| `tri_restricted_eps` (M1) | restricted-type estimate for the tri-tile form, with an $\varepsilon$-loss | `Proof/M1.lean` |
| `bht_real_smooth` (M2) | smooth truncated bilinear Hilbert transform on $\mathbb R$, uniform in both scales | `Proof/M2.lean` |
| `x1_bht_smooth` (X1) | the same on $\mathbb Z$, smooth truncations uniform in both radii | `Proof/X1.lean` |
| `t_finiteBV` (X2) | vector-valued bilinear form on $\mathbb R\times\mathbb Z/P$ (`t:finiteBV`) | `Proof/X2.lean` |
| `p_key0` | key proposition `p:key0` for a cutoff $\chi$ (corrected form) | `Proof/Key0.lean` |
| `t_maintheorem` | the main theorem | `Proof/MainTheorem.lean` |

`t_maintheorem` is assembled (`PrimeBHT.MainConditional.t_maintheorem_of_inputs`) from X1, `p_key0` and X3, where X3 is the $U^3$ approximation of the von Mangoldt function from the author's formalization of *A Variation Norm Carleson Theorem Along the Primes*. The part of that project that the proof imports is included in this repository: the 241 modules of [`PrimeCarleson`](PrimeCarleson), [`vendor/openai-math`](vendor/openai-math) (the ported openai/math files) and [`vendor/carleson`](vendor/carleson) (the ported Carleson-project files) form the import closure of the single sealed theorem used, copied unchanged from commit `f0f9299287feeaea25f6b9cedd3e078b4a98f3c7` of the [Variational-Carleson-Along-the-Primes-Palomar-Submission](https://github.com/anastasiosfragkosmath/Variational-Carleson-Along-the-Primes-Palomar-Submission) repository (see [`vendor/provenance/THIRD-PARTY.md`](vendor/provenance/THIRD-PARTY.md)). They are built from here as the libraries `PrimeCarleson`, `OAI` and `Carleson` of this package, so there is no Lake dependency other than Mathlib. `p_key0` is derived from `t_finiteBV`, whose proof follows the vector-valued route with lattice Calderón–Zygmund/Mikhlin tools; X1 is derived from M2, which is derived from M1.

The project has 413 Lean modules (about 98,000 lines) under [`PrimeBHT`](PrimeBHT) and uses the toolchain in [`lean-toolchain`](lean-toolchain) (Lean 4.35.0, Mathlib v4.35.0).

## Build and verify

Install the Lean toolchain selected by `lean-toolchain` (via [elan](https://github.com/leanprover/elan)). Dependencies are pinned in the committed `lake-manifest.json`; obtain the cache and then build:

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
```

The cache command is optional but makes the initial build substantially faster. The initial build compiles the library and the included sources of the earlier project, so it is long and can require roughly 15 GB of free disk space, depending on the platform and cache state. Do not run `lake update` merely to verify this checkout: it is a maintainer operation that changes the dependency lockfile.

`lake build` builds the library, `Challenge` and `Solution`. `scripts/frozen_abi.py` compares the elaborated frozen statements with the author-approved texts in [`scripts/data/approved`](scripts/data/approved). `scripts/interface_check.sh` checks the type equalities between the frozen statements and the internal interfaces and the standard axioms of the main declarations; `scripts/axiom_audit_x2.sh` audits the X2 chain; `scripts/check_dependency.py` checks that the included sources are closed under imports, the manifest hashes of the three frozen definitions among them, and (when a checkout of the earlier project is available at `../variational-carleson-lean`) that every included file is byte-identical to the pinned revision. `scripts/check_layout.py` checks the repository layout (module headers, file sizes, the Challenge's imports, licence, no stray `sorry`). The frozen-anchor manifest is [`scripts/data/frozen-manifest.json`](scripts/data/frozen-manifest.json).

The [verification report](verification-report.md) records the checks that were run and their exact scope. Comparator has **not** been run on the current statement files, and no human referee has reviewed the Lean development.

## Navigation

- [Main theorem statement](PrimeBHT/Frozen/MainTheorem.lean)
- [Verification report](verification-report.md)
- [Semantic comparison with the paper](semantic-audit.md)

## License

The project's own Lean source code and repository documentation are licensed under [Apache-2.0](LICENSE). The included third-party code (everything under [`vendor`](vendor), and the files of the author's earlier project under [`PrimeCarleson`](PrimeCarleson) that were ported from it) retains its original credits and Apache-2.0 licenses; see [`vendor/provenance/THIRD-PARTY.md`](vendor/provenance/THIRD-PARTY.md), [`vendor/openai-math/LICENSE`](vendor/openai-math/LICENSE) and [`vendor/provenance/third-party-licenses`](vendor/provenance/third-party-licenses). The file counts in that record describe the full ports in the earlier project; this repository contains the subset in the import closure of the main theorem (1,043 Progressions files, 201 SiegelZeros files, 1 DirichletL file and 33 of the 40 Carleson modules).

## Acknowledgement

The Lean development was produced by AI agents (Anthropic's Claude models, run through Claude Code with an orchestrator that assigns bounded proof tasks to worker agents) under the author's direction. The author selected and approved the exact Lean statements of the frozen declarations; every formal result is checked by Lean, and independent AI auditors reviewed the seals. See the [verification report](verification-report.md) and [`formalization.yaml`](formalization.yaml).

The proof includes the part of the author's formalization of *A Variation Norm Carleson Theorem Along the Primes* ([Variational-Carleson-Along-the-Primes-Palomar-Submission](https://github.com/anastasiosfragkosmath/Variational-Carleson-Along-the-Primes-Palomar-Submission)) described above, together with the code that project adapts from openai/math and from the Carleson project; those contributions retain their original attribution, and the maintainer does not claim authorship of the bundled third-party code.

The workflow followed here (frozen, author-approved statements, one declaration per file; a frozen-anchor checker; independent statement and seal audits; bounded proof tasks for worker agents) is that of the Lean agent skills in *LeanAutoformalizationSkills* by Scott Armstrong, <https://github.com/scottnarmstrong/LeanAutoformalizationSkills>, licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The skills were used unmodified at commit `1837b95b3d5a9fd8d311367603902ad7fe261adf`; in particular the frozen-anchor checker `check_frozen_anchors.py` was run on this repository's manifest. The skills' files are not included in this repository, and no endorsement by their author is implied.
