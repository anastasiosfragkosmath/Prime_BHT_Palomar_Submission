module

public import PrimeBHT.PeriodicBlock.Basic
public import PrimeBHT.PeriodicBlock.L2Norm
public import PrimeBHT.PeriodicBlock.Divisor
public import PrimeBHT.PeriodicBlock.Envelope

/-!
# The arithmetic side of the periodic block (blueprint N30, N31 identities, N33)

* `PeriodicBlock/Basic.lean`: `Y_N = ZMod N`, `lam` (`Λ_B`), `bilinAvg`, `trilinForm`, `l2`, and the
  Cauchy-Schwarz bound `norm_trilinForm_le` (N30).
* `PeriodicBlock/L2Norm.lean`: `lam_intCast` (periodicity), `l2_lam_sq`
  (`‖Λ_B‖² = ∑_{q ∈ B} 1/φ(q)`), the explicit-`ε` bounds and `exists_l2_bilinAvg_le` (N30).
* `PeriodicBlock/Divisor.lean`: `lam_eq_sum_divisors` (N31(a)), `sum_beta_eq`,
  `exists_sum_beta_le` (N31(d)).
* `PeriodicBlock/Envelope.lean`: the fibre envelope (N33).

N31(c) (`A_B = ∑_d μ(d) β_d A_d`) is postponed (it needs `A_d`).
-/
