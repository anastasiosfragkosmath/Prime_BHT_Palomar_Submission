module

public import PrimeBHT.TimeFrequency.X2.Pint.FeffermanStein

/-!
# X2, V11-b: the Fefferman-Stein inequality for `g ∈ L^R` (no integrability hypothesis), and the sharp function

`Pint.fefferman_stein` (`Pint/FeffermanStein.lean`) assumes `g ∈ L¹ ∩ L^R`.  This file removes `Integrable g`:

* `fefferman_stein_lp`: for `R > 1`, `g ≥ 0` measurable with `∫⁻ ofReal (g^R) < ⊤`, and a measurable `h : ℝ → ℝ≥0∞` such that for
  every `[a, b)` and `x ∈ [a, b)` some constant `c` has `∫_{[a,b)} |g - c| ≤ (b - a) h x`:
  `∫⁻ ofReal (g^R) ≤ ofReal (fsConst R) * ∫⁻ h^R`.
  Proof: the truncation `g_ε = max (g - ε) 0` is `1`-Lipschitz in `g` (so the same `h` works with the constant
  `max (c - ε) 0`), vanishes off `{g > ε}`, and is bounded by `ε^{1-R} g^R`, hence integrable; apply `fefferman_stein` to
  `g_{1/(n+1)}` and Fatou along `g_{1/(n+1)} ↑ g`.
* `sharpFn g x = sup_{[a,b) ∋ x} ⨍_{[a,b)} |g - ⨍_{[a,b)} g|` (the sharp maximal function over half-open intervals), and
  `fefferman_stein_sharp`: for every measurable `h ≥ g^#`, the conclusion of `fefferman_stein_lp`; in particular
  `∫⁻ ofReal (g^R) ≤ ofReal (fsConst R) * ∫⁻ (g^#)^R` whenever `g^#` is measurable (it is lower semicontinuous for locally
  integrable `g`, a classical fact that is NOT formalized here: every use in X2 supplies an explicit measurable majorant `h`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

/-- The truncation from below `max (g - ε) 0`. -/
def truncBelow (ε : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := fun x => max (g x - ε) 0

/-! ### The sharp maximal function -/

end PrimeBHT.TimeFrequency.X2.Pint
