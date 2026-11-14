module

public import PrimeBHT.PeriodicAssembly.Decomp
public import PrimeBHT.PeriodicAssembly.Structured
public import PrimeBHT.PeriodicAssembly.D4
public import PrimeBHT.PeriodicAssembly.Interp

/-!
# Assembly of the periodic block (blueprint N31(c), N34, N36, N37)

Setting (`blueprint.md` §5.0): `B` a finite nonempty set of squarefree naturals in `(Q/2, Q]`,
`N = lcmQ B`, `Y_N = ZMod N` with the normalized counting measure, `Λ_B = lam B N`,
`A_B = bilinAvg (lam B N)`, and for `d ∣ N` the splitting `Split.ofDvd` with `A_d = Split.A`.

* `PeriodicAssembly/Decomp.lean`: `bilinAvg_lam_eq_sum_divisors` (N31(c)), `beta_pos_iff`, the
  bridge `l2_eq : PeriodicBlock.l2 = Periodic.l2`.
* `PeriodicAssembly/Structured.lean`: `l1_bilinAvg_atom_le`, `exists_l1_bilinAvg_atom_le_ofDvd`
  (N34 `l:structured-bound`).
* `PeriodicAssembly/D4.lean`: `exists_l1_bilinAvg_le` (N36 `l:d4`).
* `PeriodicAssembly/Interp.lean`: `lpNorm_le` (Lyapunov interpolation) and
  `exists_lpNorm_bilinAvg_le` (N37 `p:interpsetup`).
-/
