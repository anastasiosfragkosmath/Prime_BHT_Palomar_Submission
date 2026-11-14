module

public import PrimeBHT.TimeFrequency.Interp.Hull.Exponents
public import PrimeBHT.TimeFrequency.Interp.Hull.Glue
public import PrimeBHT.TimeFrequency.Interp.Hull.ModelForm
public import PrimeBHT.TimeFrequency.Interp.Hull.Bilinear
public import PrimeBHT.TimeFrequency.Interp.Hull.Chain
public import PrimeBHT.TimeFrequency.Interp.Hull.ChainR6b
public import PrimeBHT.TimeFrequency.Interp.Hull.ModelBound

/-!
# C11, the hull step, and its connection to the abstract chain R6a/R6b/R6c

Umbrella module for `PrimeBHT.TimeFrequency.Interp.Hull.*` (blueprint `docs/x1-blueprint.md`, node C11).

* `Exponents`: C11(b) (`corner_le_rpow_mul`) and C11(c)'s exponent choice (`epsOf`, hexagons,
  compactness).
* `Glue`: `M1Prop` (the type of the frozen `tri_restricted_eps`) and `M1Prop ⇒ HullBound`
  (`hullBound_triForm_of_m1`, and the local-boundedness forms).
* `ModelForm`: `IsSubadditive`, `IsSmall`, `IsDominatedConj`/`IsDominated`, `hmeas` for
  `Λ_P = triForm P φ` and `Π_P = modelOp P φ`.
* `Bilinear`: homogeneity of `Λ_P` and bilinearity of `Π_P` (the `hhom`, `hadd`, `hsmul` of R6c).
* `Chain`: `M1Prop ⇒` R6a for `Λ_P` (`restrictedType_triForm_of_m1`) and the `hRT` of R6c-II.
* `ModelBound`: the model bound `modelBound_of_m1 : M1Prop → ModelBound p q r N C` for `1<p,q`, `1/r = 1/p+1/q`,
  `2/3<r` (blueprint (MB): R6c applied to `Π_P`), conditional only on `M1Prop`.
* `ChainR6b`: the `hRS` of R6c-I from M1 (`hRS_modelOp_of_m1`), using the `InReg` version of the R6b hypothesis
  (the hull bound is only needed on a compact part of `U_*`: patch applied by the orchestrator, see
  `Restricted/Operator.lean`, correction 7).
-/
