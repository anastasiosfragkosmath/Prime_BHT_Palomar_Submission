# Semantic comparison with the paper

This report compares the Lean statement of the main theorem, [`PrimeBHT.Statements.t_maintheorem`](PrimeBHT/Frozen/MainTheorem.lean) (also in [`Challenge.lean`](Challenge.lean)), with Theorem `t:maintheorem` of [*The Bilinear Hilbert Transform Along the Primes*](source-paper/Prime_BHT_final.tex). The manuscript and its [bibliography](source-paper/primeBHTbib.bib) are included. It also records where the intermediate frozen statements deviate from the printed proof outline.

## The main theorem

The paper's theorem (lines 175-179 of the included TeX) asserts that $\mathcal H_{\mathbb P}$ extends to a bounded operator $\ell^p\times\ell^q\to\ell^r$ for $(p,q,r)$ in the region $\mathcal R=\{(p,q,r)\in(0,\infty)^3:\ \tfrac2p+\tfrac3q<3,\ \tfrac3p+\tfrac2q<3,\ \tfrac1r=\tfrac1p+\tfrac1q,\ p,q>1\}$.

The Lean statement reads:

```lean
theorem t_maintheorem :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / p + 3 / q < 3 → 3 / p + 2 / q < 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
        eLpNorm (primeBHT f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count
```

Points of correspondence and of reading:

- **Region.** The hypotheses are exactly those of $\mathcal R$. The conditions $p,q,r>0$ of $(0,\infty)^3$ follow from $1<p$, $1<q$ and $1/r=1/p+1/q$. The inequalities are strict, so the endpoint $(\frac53,\frac53,\frac56)$ is excluded.
- **Operator.** `primeBHT f g x` is $\sum_{n\ne0}\frac{\Lambda(|n|)}{n}f(x-n)g(x+n)$ with $\Lambda=$ Mathlib's `ArithmeticFunction.vonMangoldt` applied to `n.natAbs`. The guard `n = 0 → 0` is explicit, so the statement does not rely on Lean's junk values `Λ 0 = 0` and `a / 0 = 0`. For finitely supported $f$ the family has finitely many nonzero terms (a term is nonzero only if $x-n\in\mathrm{supp}\,f$), so the unconditional sum `∑'` is the genuine finite sum and not the junk value of a non-summable family.
- **Norms.** $\ell^s$ norms are `eLpNorm` for counting measure, with values in $[0,\infty]$; for $s<1$ this is $(\sum|F|^s)^{1/s}$.
- **Boundedness.** "Extends to a bounded operator" is read as the a priori estimate on finitely supported $f,g:\mathbb Z\to\mathbb C$ (`ℤ →₀ ℂ`), the dense subspace on which the operator is defined; the extension by density (paper lines 1437-1440) is not part of the statement.
- **Constant.** The constant is quantified after $(p,q,r)$ and before $(f,g)$, so $C=C_{p,q,r}$ depends only on the exponents; `0 ≤ C` is recorded.

## Intermediate frozen statements and corrections

The proof is organized through frozen, author-approved intermediate statements (see the table in the [README](README.md)). Their Lean text is in [`scripts/data/approved`](scripts/data/approved), checked against the elaborated declarations by `scripts/frozen_abi.py`. Where the Lean statement is not a literal transcription of the printed proof outline, the docstring of the declaration says so:

- **`p_key0`** (paper lines 705-720) is stated in a corrected form: the half `e:long-unsmoothed` of the printed proposition is stated with the decay $Q^{-\tau/2+\eta}$ in $\ell^2\times\ell^2\to\ell^1$; the smoothed half `e:longgoal` is not stated, because it cannot be read literally for a fixed smoothing parameter and no part of the proof consumes it.
- **`t_finiteBV`** (paper lines 974-1020) is stated in the all-multi-index form: the constant depends on $u$ and on the full sequence $(A_j)$ of symbol bounds, and the integrability of the form's integrand is part of the conclusion.
- **`tri_restricted_eps`** (M1) is the restricted-type estimate for the unshifted tri-tile form with an $\varepsilon$-loss; it is not the corner bound printed in the source it follows.
- **`bht_real_smooth`** (M2) and **`x1_bht_smooth`** (X1) are the smooth truncated bilinear Hilbert transform estimates on $\mathbb R$ and on $\mathbb Z$, uniform in both truncation scales, for $1<p,q$, $\frac1r=\frac1p+\frac1q$, $\frac23<r$.


## Proof correspondence

The paper reduces the discrete operator, after a $U^3$-based approximation of $\Lambda$, to smooth truncated bilinear Hilbert transforms and a transference estimate for a vector-valued form. The Lean proof follows that architecture: `t_maintheorem` is assembled from X1 (smooth truncations on $\mathbb Z$), `p_key0` and the $U^3$ approximation X3. X3 is not proved by the files under `PrimeBHT/`: it is the sealed theorem `PrimeCarleson.vonMangoldt_sub_heathBrown_U3` of the author's formalization of *A Variation Norm Carleson Theorem Along the Primes*, whose import closure is included in [`PrimeCarleson`](PrimeCarleson) and [`vendor`](vendor) (copied unchanged from commit `f0f9299287feeaea25f6b9cedd3e078b4a98f3c7` of [that project](https://github.com/anastasiosfragkosmath/Variational-Carleson-Along-the-Primes-Palomar-Submission)). Its statement was frozen and audited there and is not among the frozen declarations of this repository; the three frozen definitions of that project that the proof depends on are bound here by file hash (see the [verification report](verification-report.md)). The proof of `t_finiteBV` does not use UMD-space machinery; it uses lattice Calderón–Zygmund and Mikhlin-type tools, a different route to the same estimate. The proofs of the intermediate statements were developed by automated agents under author direction and are checked only by Lean (see the acknowledgement in the [README](README.md)); the [verification report](verification-report.md) records what was checked.
