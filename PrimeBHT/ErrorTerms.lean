module

public import PrimeBHT.ErrorTerms.Moment
public import PrimeBHT.ErrorTerms.Rough
public import PrimeBHT.ErrorTerms.L2
public import PrimeBHT.ErrorTerms.Summable

/-!
# N20: the error terms `e:errL2`, `e:errrough`, `e:error-summable`

`S_k^err(f,g)(x) = ∑_n ψ_k(n) E_k(n) f(x-n) g(x+n)` (`PrimeBHT.Decomposition.Serr`),
`E_k = Λ - Λ_{≤ M_k}`, `M_k = exp ((log 2^k)^{1/10})`.

* `PrimeBHT.ErrorTerms.eLpNorm_Serr_rough` (b, **unconditional**): for `1 < p, q`, `1/r = 1/p + 1/q`
  there are `b, C ≥ 0` with `‖S_k^err(f,g)‖_{ℓ^r} ≤ C k^b ‖f‖_p ‖g‖_q`, `k ≥ 1`
  (KMTT moment bound for the cumulative Heath-Brown model, `Moment`; Hölder/N11 route, `Rough`).
* `PrimeBHT.ErrorTerms.X3Statement`: the sealed `[F+, Prop 3.1]` as an explicit `Prop`.
* `PrimeBHT.ErrorTerms.eLpNorm_Serr_le_of_X3` (a, conditional on X3): `e:errL2`,
  `‖S_k^err(f,g)‖_{ℓ²} ≤ C_A k^{-A} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}` for `A ≥ 1` (`L2`).
* `PrimeBHT.ErrorTerms.eLpNorm_Serr_le_k_rpow_of_X3` / `eLpNorm_Serr_le_k_pow_of_X3` (c, conditional
  on X3): `e:error-summable`, `‖S_k^err(f,g)‖_{ℓ^r} ≤ C k^{-100} ‖f‖_p ‖g‖_q` (`Summable`).
-/
