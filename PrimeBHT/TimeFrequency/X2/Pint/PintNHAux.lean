module

public import PrimeBHT.TimeFrequency.X2.Pint.TreeKernel
public import PrimeBHT.TimeFrequency.X2.Ortho.PintNested

/-!
# X2, V11: auxiliary lemmas for the assembly of `pint_nonHilbert_O`

* `finsetSum_iSup_le`: a finite sum of suprema is bounded by `X` if every selection sum is;
* `eps_opt`: the `ε`-optimisation `X ≤ K (ε L + (1 + ε^{-(1-α)/α}) M)` for all `ε > 0` ⟹ `X ≤ 2K (M + L^{1-α} M^α)`;
* `young_split'`, `val_rpow_eq'` (copies of the TB-4 helpers);
* `selKer`: the kernel of an optional choice of tree-operator data (`0` for `none`), with its value identity
  `∫ ‖selKer F‖^q = selVal` and `selVal ≤ |I_T| topNorm^q ≤ ⨆ selVal`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- A finite sum of suprema is at most `X` if every selection sum is. -/
theorem finsetSum_iSup_le {ι : Type*} [DecidableEq ι] {J : ι → Type*} [∀ i, Nonempty (J i)] (s : Finset ι)
    (h : ∀ i, J i → ℝ≥0∞) {X : ℝ≥0∞} (hX : ∀ g : ∀ i, J i, ∑ i ∈ s, h i (g i) ≤ X) :
    ∑ i ∈ s, ⨆ j, h i j ≤ X := by
  suffices H : ∀ c : ℝ≥0∞, (∀ g : ∀ i, J i, c + ∑ i ∈ s, h i (g i) ≤ X) → c + ∑ i ∈ s, ⨆ j, h i j ≤ X by
    simpa using H 0 (by simpa using hX)
  clear hX
  induction s using Finset.induction_on with
  | empty => intro c hc; simpa using hc (fun i => Classical.choice inferInstance)
  | insert a s ha ih =>
    intro c hc
    rw [Finset.sum_insert ha, ← add_assoc, ENNReal.add_iSup, ENNReal.iSup_add]
    refine iSup_le fun j => ih (c + h a j) fun g => ?_
    have := hc (Function.update g a j)
    rw [Finset.sum_insert ha, Function.update_self, ← add_assoc] at this
    rwa [Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]] at this

/-- Young's inequality in the form used for the HLC intersection form (copy of `young_split`). -/
theorem young_split' {x y ε α : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1) :
    x ^ (1 - α) * y ^ α ≤ ε * x + ε ^ (-((1 - α) / α)) * y := by
  have hβ : 0 ≤ ε ^ (-((1 - α) / α)) := (Real.rpow_pos_of_pos hε _).le
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - α) (w₂ := α) (p₁ := ε * x)
    (p₂ := ε ^ (-((1 - α) / α)) * y) (by linarith) hα0.le (by positivity) (by positivity) (by ring)
  have e : (ε * x) ^ (1 - α) * (ε ^ (-((1 - α) / α)) * y) ^ α = x ^ (1 - α) * y ^ α := by
    rw [Real.mul_rpow hε.le hx, Real.mul_rpow hβ hy, ← Real.rpow_mul hε.le]
    have : ε ^ (1 - α) * ε ^ (-((1 - α) / α) * α) = 1 := by
      rw [← Real.rpow_add hε, show 1 - α + -((1 - α) / α) * α = 0 by field_simp; ring, Real.rpow_zero]
    calc ε ^ (1 - α) * x ^ (1 - α) * (ε ^ (-((1 - α) / α) * α) * y ^ α) =
        (ε ^ (1 - α) * ε ^ (-((1 - α) / α) * α)) * (x ^ (1 - α) * y ^ α) := by ring
      _ = _ := by rw [this, one_mul]
  rw [e] at h
  have h1 : (1 - α) * (ε * x) ≤ ε * x := by nlinarith [mul_nonneg hε.le hx]
  have h2 : α * (ε ^ (-((1 - α) / α)) * y) ≤ ε ^ (-((1 - α) / α)) * y := by
    nlinarith [mul_nonneg hβ hy]
  linarith

/-- **The `ε`-optimisation.** -/
theorem eps_opt {X K L M α : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ K * (ε * L + (1 + ε ^ (-((1 - α) / α))) * M)) :
    X ≤ 2 * K * (M + L ^ (1 - α) * M ^ α) := by
  have h1α : 0 < 1 - α := by linarith
  rcases hM.eq_or_lt with hM0 | hMp
  · subst hM0
    rw [Real.zero_rpow hα0.ne', mul_zero, add_zero, mul_zero]
    by_contra hX
    push Not at hX
    have hε : 0 < X / (2 * (K * L + 1)) := by positivity
    have := h _ hε
    rw [mul_zero, add_zero] at this
    have h3 : K * (X / (2 * (K * L + 1)) * L) < X := by
      have : K * (X / (2 * (K * L + 1)) * L) = X * (K * L / (2 * (K * L + 1))) := by ring
      rw [this]
      have : K * L / (2 * (K * L + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith [mul_nonneg hK hL]
      nlinarith
    linarith
  rcases hL.eq_or_lt with hL0 | hLp
  · subst hL0
    have := h 1 one_pos
    norm_num at this
    rw [Real.zero_rpow h1α.ne', zero_mul, add_zero]
    nlinarith [mul_nonneg hK hM]
  · set ε := (M / L) ^ α with hεdef
    have hε : 0 < ε := Real.rpow_pos_of_pos (div_pos hMp hLp) _
    have e1 : ε * L = L ^ (1 - α) * M ^ α := by
      rw [hεdef, Real.div_rpow hM hLp.le, Real.rpow_sub hLp, Real.rpow_one]
      field_simp
    have e2 : ε ^ (-((1 - α) / α)) * M = L ^ (1 - α) * M ^ α := by
      rw [hεdef, ← Real.rpow_mul (div_nonneg hM hLp.le), show α * -((1 - α) / α) = -(1 - α) by field_simp,
        Real.rpow_neg (div_nonneg hM hLp.le), Real.div_rpow hM hLp.le, inv_div]
      have hMa : M ^ α = M / M ^ (1 - α) := by
        rw [Real.rpow_sub hMp, Real.rpow_one]; field_simp
      rw [hMa]
      have : 0 < M ^ (1 - α) := Real.rpow_pos_of_pos hMp _
      field_simp
    have := h ε hε
    have h4 : K * (ε * L + (1 + ε ^ (-((1 - α) / α))) * M) = K * (M + 2 * (L ^ (1 - α) * M ^ α)) := by
      rw [add_mul, one_mul, e1, e2]; ring
    rw [h4] at this
    have h5 : 0 ≤ L ^ (1 - α) * M ^ α := by positivity
    nlinarith [mul_nonneg hK h5, mul_nonneg hK hM]

/-- `(L^{-1/q} ‖f‖_q)^q = L⁻¹ ∫ f^q` (copy of `val_rpow_eq`). -/
theorem val_rpow_eq' {q : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {L : ℝ}
    (hL : 0 < L) :
    (ENNReal.ofReal (L ^ (-1 / q)) * eLpNorm f (ENNReal.ofReal q) volume) ^ q =
      ENNReal.ofReal L⁻¹ * ∫⁻ x, ENNReal.ofReal (f x ^ q) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hL.le _) hq.le,
    ← Real.rpow_mul hL.le, show -1 / q * q = -1 by field_simp, Real.rpow_neg_one,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hfm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, show 1 / q * q = 1 by field_simp, ENNReal.rpow_one]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x), ENNReal.ofReal_rpow_of_nonneg (hf0 x) hq.le]

/-! ## Optional tree-operator data -/

/-- Tree-operator data of slot `k` for the tile set `Tr`. -/
abbrev TD (𝔭 : Params) (k : Fin 3) (Tr : Finset TriTile) : Type :=
  {d : (TriTile → ℝ → ℂ) × (TriTile → ℝ → ℂ) // IsTreeOpData 𝔭 k Tr d.1 d.2}

/-- The kernel of an optional choice of data (`0` for `none`). -/
def selKer (𝔭 : Params) (k : Fin 3) (T : Finset TriTile × Top) : Option (TD 𝔭 k T.1) → ℝ → ℝ → ℂ
  | none => fun _ _ => 0
  | some d => treeKer T.1 d.1.1 d.1.2 (T.2.2 * freqDir k)

/-- The value of an optional choice of data (`0` for `none`). -/
def selVal {P : ℕ} [NeZero P] (𝔭 : Params) (s q : ℝ) (k : Fin 3) (T : Finset TriTile × Top)
    (F : ℝ → ZMod P → ℂ) : Option (TD 𝔭 k T.1) → ℝ≥0∞
  | none => 0
  | some d => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * treeOpNorm s q T.1 T.2 d.1.1 d.1.2 F ^ q

section Sel

variable {P : ℕ} [NeZero P] {𝔭 : Params} {k : Fin 3} {T : Finset TriTile × Top} {Cφ Cκ : ℝ}
  (hN : (0 : ℝ) ≤ 𝔭.N)
  (hTBd : ∀ d : TD 𝔭 k T.1, ∀ R ∈ T.1,
    TileBound (𝔭.N : ℝ) 3 Cφ Cκ R.box.scale R.pos (d.1.1 R) (kernelDemod (T.2.2 * freqDir k) (d.1.2 R)))
include hTBd

theorem stronglyMeasurable_selKer (o : Option (TD 𝔭 k T.1)) :
    StronglyMeasurable (Function.uncurry (selKer 𝔭 k T o)) := by
  cases o with
  | none => exact stronglyMeasurable_const
  | some d =>
    have hc := continuous_tileKernel T.1 d.1.1 (fun R => kernelDemod (T.2.2 * freqDir k) (d.1.2 R))
      (fun R hR => (hTBd d R hR).φ_diff.continuous) (fun R hR => (hTBd d R hR).κ_diff.continuous)
    refine Continuous.stronglyMeasurable ?_
    exact hc.mul (by fun_prop)

include hN in
theorem selKer_rowcol (o : Option (TD 𝔭 k T.1)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∫⁻ w, ‖selKer 𝔭 k T o x w‖ₑ ≤ ENNReal.ofReal C) ∧
      ∀ w, ∫⁻ x, ‖selKer 𝔭 k T o x w‖ₑ ≤ ENNReal.ofReal C := by
  cases o with
  | none => refine ⟨0, le_rfl, fun x => ?_, fun w => ?_⟩ <;> simp [selKer]
  | some d =>
    obtain ⟨C, hC, h1, h2⟩ := tileKernel_row_col hN (hTBd d)
    have e : ∀ x w, ‖selKer 𝔭 k T (some d) x w‖ₑ =
        ‖tileKernel T.1 d.1.1 (fun R => kernelDemod (T.2.2 * freqDir k) (d.1.2 R)) x w‖ₑ := fun x w => by
      simp only [selKer]; rw [← ofReal_norm, norm_treeKer, ofReal_norm]
    refine ⟨C, hC, fun x => ?_, fun w => ?_⟩
    · simp_rw [e]; exact h1 x
    · simp_rw [e]; exact h2 w

/-- The value identity. -/
theorem lintegral_selKer {s q : ℝ} (hs : 0 < s) (hq : 0 < q) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {b : ℝ}
    (hb : ∀ z y, ‖F z y‖ ≤ b) (o : Option (TD 𝔭 k T.1)) :
    ∫⁻ x, ENNReal.ofReal (yNorm s (Pint.kernelOp (selKer 𝔭 k T o) F x) ^ q) = selVal 𝔭 s q k T F o := by
  cases o with
  | none =>
    simp only [selKer, selVal]
    have h0 : ∀ x, Pint.kernelOp (fun _ _ => (0 : ℂ)) F x = 0 := fun x => by
      funext y; simp [Pint.kernelOp]
    simp [h0, yNorm_zero_of_pos hs, Real.zero_rpow hq.ne']
  | some d =>
    simp only [selKer, selVal]
    have hL : (0 : ℝ) < (2 : ℝ) ^ T.2.1.1 := zpow_pos (by norm_num) _
    have hid : ∀ x, yNorm s (Pint.kernelOp (treeKer T.1 d.1.1 d.1.2 (T.2.2 * freqDir k)) F x) =
        yNorm s (treeOp T.1 d.1.1 d.1.2 F x) := fun x => yNorm_kernelOp_treeKer (hTBd d) hF hb hs x
    have hm : Measurable fun x => yNorm s (treeOp T.1 d.1.1 d.1.2 F x) := by
      have := (measurable_yNorm_fun s).comp
        (Pint.measurable_kernelOp (stronglyMeasurable_selKer hTBd (some d)) hF)
      have e : (fun x => yNorm s (treeOp T.1 d.1.1 d.1.2 F x)) =
          fun x => yNorm s (Pint.kernelOp (treeKer T.1 d.1.1 d.1.2 (T.2.2 * freqDir k)) F x) :=
        funext fun x => (hid x).symm
      rw [e]; exact this
    rw [treeOpNorm, val_rpow_eq' hq hm (fun x => Pint.yNorm_nonneg _ _) hL, ← mul_assoc,
      ← ENNReal.ofReal_mul hL.le, mul_inv_cancel₀ hL.ne', ENNReal.ofReal_one, one_mul]
    exact lintegral_congr fun x => by rw [hid]

end Sel

theorem selVal_le {P : ℕ} [NeZero P] {𝔭 : Params} {s q : ℝ} {k : Fin 3} {T : Finset TriTile × Top}
    {F : ℝ → ZMod P → ℂ} (hq : 0 ≤ q) (o : Option (TD 𝔭 k T.1)) :
    selVal 𝔭 s q k T F o ≤ ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * topNorm 𝔭 s k F T.1 T.2 q ^ q := by
  cases o with
  | none => exact zero_le
  | some d =>
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (le_topNorm d.2) hq) _

theorem iSup_rpow_eq' {ι : Sort*} (f : ι → ℝ≥0∞) {q : ℝ} (hq : 0 < q) : (⨆ i, f i) ^ q = ⨆ i, f i ^ q := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hq.le)
  have h1 : (⨆ i, f i) ≤ (⨆ i, f i ^ q) ^ (1 / q) := iSup_le fun i => by
    calc f i = (f i ^ q) ^ (1 / q) := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow (le_iSup (fun i => f i ^ q) i) (by positivity)
  calc (⨆ i, f i) ^ q ≤ ((⨆ i, f i ^ q) ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow h1 hq.le
    _ = _ := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

theorem le_iSup_selVal {P : ℕ} [NeZero P] {𝔭 : Params} {s q : ℝ} {k : Fin 3} {T : Finset TriTile × Top}
    {F : ℝ → ZMod P → ℂ} (hq : 0 < q) :
    ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * topNorm 𝔭 s k F T.1 T.2 q ^ q ≤ ⨆ o, selVal 𝔭 s q k T F o := by
  have e : topNorm 𝔭 s k F T.1 T.2 q ^ q = ⨆ (ψ : TriTile → ℝ → ℂ) (m : TriTile → ℝ → ℂ)
      (_ : IsTreeOpData 𝔭 k T.1 ψ m), treeOpNorm s q T.1 T.2 ψ m F ^ q := by
    simp only [topNorm]
    exact (iSup_rpow_eq' _ hq).trans (iSup_congr fun ψ => (iSup_rpow_eq' _ hq).trans
      (iSup_congr fun m => iSup_rpow_eq' _ hq))
  rw [e, ENNReal.mul_iSup]
  refine iSup_le fun ψ => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hd => le_iSup_of_le (some ⟨(ψ, m), hd⟩) le_rfl

end PrimeBHT.TimeFrequency.X2
