module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.Tile.Gram.Bessel
public import PrimeBHT.TimeFrequency.Tile.Gram.Bernstein

/-!
# Packet inner products and same-interval Bessel inequalities (blueprint node C2, `TT.gram`)

Statements (namespace `PrimeBHT.TimeFrequency.Tile`, packets adapted in the sense of the frozen
`PrimeBHT.Statements.IsAdapted`; constants depend on `N` only):

* (G0) `fourier_demod_eq_zero`, `contDiff_demod`, `iteratedDeriv_demod_eq`,
  `exists_norm_iteratedDeriv_demod_le` (`Gram/Bernstein.lean`);
* (G1) `norm_pairing_le_of_isAdapted` (`N ≥ 2`, constant `gramConst N`), (G2) `pairing_eq_zero_of_disjoint`,
  (G3) `sum_norm_pairing_sameScale_le` (`N ≥ 3`, constant `sameScaleConst N`) (`Gram/Pair.lean`);
* (G4) `sum_norm_sq_pairing_le_weighted`, `sum_norm_sq_pairing_sameInterval_le_weighted`, (G5)
  `sum_norm_sq_pairing_le`, `sum_norm_sq_pairing_sameInterval_le` (`N ≥ 3`, constant `besselConst N`)
  (`Gram/Bessel.lean`).
-/
