module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Close
public import PrimeBHT.TimeFrequency.X2.Psp.O2bFar
public import PrimeBHT.TimeFrequency.X2.Psp.O2LayerDecay

/-!
# X2, V13 O2 (b-out): the OUTSIDE bound `OutBound 𝔭 Cout` (MTT2 (d1)-(d4)) of `O2Close.lean`

Owner: V13 (`docs/audits/X2-O2-coordination.md` §0b, §0c).  Single application of `outside_conv_bound` (`O2bFar.lean`) to `Φ = D_out`:

* `dout_eq_zero_of_mem`: `D_out = 0` on `Ẽ_σ` (the coarse bumps are supported outside `Ẽ_τ ⊇ Ẽ_σ`);
* `yNorm_overlapBumps_le`: the bump part is bounded by `16 B` (all bumps are disjoint);
* `dout_norm_le`: for `z ∉ Ẽ_σ`, `x' ∈ Ẽ_σ`: `‖D_out(z)‖_{L²(Y)} ≤ Ab · e · ⟨(z - x')/2^σ⟩^{N'}` (`growth_around`, `overlapPi_bound`, `ovCoef_bound_end`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real FourierTransform
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Out
variable {P : ℕ} [NeZero P]

theorem yNorm_overlapBumps_le (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) (cL cR : ℤ → ℝ → ZMod P → ℂ)
    {s : ℝ} (hs : 1 ≤ s) {B : ℝ} (hB : 0 ≤ B) (hcL : ∀ σ ∈ L, ∀ x ∈ leftEnds TA W σ, yNorm s (cL σ x) ≤ B)
    (hcR : ∀ σ ∈ L, ∀ x ∈ rightEnds TA W σ, yNorm s (cR σ x) ≤ B) (y : ℝ) :
    yNorm s (overlapBumps TA W L θ cL cR y) ≤ 16 * B := by
  unfold overlapBumps
  refine (CZ.yNorm_add_le hs _ _).trans ?_
  linarith [yNorm_leftBumps_le (TA := TA) (W := W) (L := L) hs hB hcL θ y,
    yNorm_rightBumps_le (TA := TA) (W := W) (L := L) hs hB hcR θ y]

omit [NeZero P] in
/-- `D_out` vanishes on `Ẽ_σ`. -/
theorem dout_eq_zero_of_mem {J : ℕ} {s₀ lo : ℤ} {TA : Finset TriTile} {W : ℤ × ℤ} {θ : ℝ} {F : ℝ → ZMod P → ℂ}
    {cL cR : ℤ → ℝ → ZMod P → ℂ} {σ : ℤ} {z : ℝ} (hz : z ∈ eTil TA W σ) :
    Dout J s₀ lo TA W θ F cL cR σ z = 0 := by
  unfold Dout
  rw [Set.indicator_of_notMem (by simpa using hz), zero_add]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  obtain ⟨hτL, hστ⟩ := Finset.mem_filter.1 hτ
  have hτW : τ ≤ W.1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hτL).1).2
  have hzτ : z ∈ eTil TA W τ := eTil_mono hστ hτW hz
  unfold bumpAt
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro x hx
    have : rightPhi τ x z = 0 := rightPhi_eq_zero fun h => (Set.disjoint_left.1 (rightBump_disjoint_eTil hx)) h hzτ
    simp [this]
  · intro x hx
    have : leftPhi τ x z = 0 := leftPhi_eq_zero fun h => (Set.disjoint_left.1 (leftBump_disjoint_eTil hx)) h hzτ
    simp [this]


theorem real_of_enn_mul {a C g e : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g) (he : 0 ≤ e)
    (h : ENNReal.ofReal a ≤ ENNReal.ofReal C * ENNReal.ofReal g * ENNReal.ofReal e) : a ≤ C * g * e := by
  rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (mul_nonneg hC hg)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- The constant of the pointwise bound of `D_out`. -/
def Ab (𝔮 : Params) : ℝ := |polyC 𝔮 2| + |oaConst 𝔮 2| + 16 * (coefConst 𝔮 2 + 1)

theorem Ab_nonneg (𝔮 : Params) : 0 ≤ Ab 𝔮 := by
  unfold Ab; have := coefConst_nonneg 𝔮 2; positivity

/-- **Pointwise bound of `D_out` off `Ẽ_σ`**: for `z ∉ Ẽ_σ`, any `x' ∈ Ẽ_σ`:
`‖D_out(z)‖_{L²(Y)} ≤ Ab · e · ⟨(z - x')/2^σ⟩^{N'}`, `e = engTop`, `N' = 𝔮.N` (`𝔮 = 𝔭.tree`). -/
theorem dout_norm_le {𝔮 : Params} (h𝔮 : 𝔮.Admissible) (hJ2 : 2 ≤ 𝔮.J) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔮 η')
    {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile}
    (hsub : TA ⊆ Cs) {t : Top} (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {s₀ lo σ : ℤ}
    (hσL : σ ∈ ovScales 𝔮.J s₀ lo t.1.1) (hlat : ∀ R ∈ TA, (𝔮.J : ℤ) ∣ R.box.scale - s₀) {e : ℝ}
    (hE : engTop 𝔮 2 k F Cs 2 = ENNReal.ofReal e) (he : 0 ≤ e) {x' : ℝ} (hx' : x' ∈ eTil TA t.1 σ) {z : ℝ}
    (hz : z ∉ eTil TA t.1 σ) :
    yNorm 2 (Dout 𝔮.J s₀ lo TA t.1 (t.2 * freqDir k) F (fun τ x => ovCoef 𝔮.J (t.2 * freqDir k) F τ x)
        (fun τ x => -ovCoef 𝔮.J (t.2 * freqDir k) F τ x) σ z) ≤
      Ab 𝔮 * e * jb ((z - x') / (2 : ℝ) ^ σ) ^ 𝔮.N := by
  set θ : ℝ := t.2 * freqDir k with hθ
  set L : Finset ℤ := ovScales 𝔮.J s₀ lo t.1.1 with hL
  have hlatL : ∀ τ ∈ L, ∀ R ∈ TA, (𝔮.J : ℤ) ∣ R.box.scale - τ := by
    intro τ hτ R hR
    have h1 := (mem_ovScales.1 hτ).2
    have : R.box.scale - τ = (R.box.scale - s₀) - (τ - s₀) := by ring
    rw [this]; exact dvd_sub (hlat R hR) h1
  have hjb1 : 1 ≤ jb ((z - x') / (2 : ℝ) ^ σ) ^ 𝔮.N := one_le_pow₀ (one_le_jb _)
  -- (1) the low-pass at scale σ
  have hT : yNorm 2 (tmult (lowSym θ σ) F z) ≤ |polyC 𝔮 2| * jb ((z - x') / (2 : ℝ) ^ σ) ^ 𝔮.N * e := by
    have h := growth_around h𝔮 hJ2 hη' (s := 2) (q := 2) (by norm_num) (by norm_num) hF hFb hsub hov
      (hlatL σ hσL) hx' z
    rw [hE] at h
    refine real_of_enn_mul (abs_nonneg _) (by positivity) he (h.trans ?_)
    gcongr
    exact le_abs_self _
  -- (2) `Π̃F`
  have hPi : yNorm 2 (overlapPi TA t.1 L θ F z) ≤ |oaConst 𝔮 2| * e := by
    have h := overlapPi_bound h𝔮 hJ2 hη' (s := 2) (q := 2) (by norm_num) (by norm_num) hF hFb hsub hov hlatL z
    rw [hE] at h
    have h' : ENNReal.ofReal (yNorm 2 (overlapPi TA t.1 L θ F z)) ≤
        ENNReal.ofReal |oaConst 𝔮 2| * ENNReal.ofReal 1 * ENNReal.ofReal e := by
      refine h.trans ?_
      simp only [ENNReal.ofReal_one, mul_one]
      gcongr
      exact le_abs_self _
    have := real_of_enn_mul (abs_nonneg _) zero_le_one he h'
    simpa using this
  -- (3) the coarse bumps
  set L' : Finset ℤ := L.filter (fun τ => σ ≤ τ) with hL'
  have hcL : ∀ τ ∈ L', ∀ x ∈ leftEnds TA t.1 τ, yNorm 2 (ovCoef 𝔮.J θ F τ x) ≤ (coefConst 𝔮 2 + 1) * e := by
    intro τ hτ x hx
    obtain ⟨v, hv, -, rfl⟩ := mem_leftEndsOf.1 hx
    have h := ovCoef_bound_end h𝔮 hJ2 hη' (s := 2) (q := 2) (by norm_num) (by norm_num) hF hFb hsub hov
      (hlatL τ (Finset.mem_filter.1 hτ).1) (mem_eTilKeysF.1 hv) (Or.inl rfl)
    rw [hE] at h
    have h' : ENNReal.ofReal (yNorm 2 (ovCoef 𝔮.J θ F τ ((2 : ℝ) ^ τ * (v : ℝ)))) ≤
        ENNReal.ofReal (coefConst 𝔮 2 + 1) * ENNReal.ofReal 1 * ENNReal.ofReal e := by
      simpa using h
    have := real_of_enn_mul (by have := coefConst_nonneg 𝔮 2; linarith) zero_le_one he h'
    simpa using this
  have hcR : ∀ τ ∈ L', ∀ x ∈ rightEnds TA t.1 τ, yNorm 2 (-ovCoef 𝔮.J θ F τ x) ≤ (coefConst 𝔮 2 + 1) * e := by
    intro τ hτ x hx
    obtain ⟨v, hv, -, rfl⟩ := mem_rightEndsOf.1 hx
    have h := ovCoef_bound_end h𝔮 hJ2 hη' (s := 2) (q := 2) (by norm_num) (by norm_num) hF hFb hsub hov
      (hlatL τ (Finset.mem_filter.1 hτ).1) (mem_eTilKeysF.1 hv) (Or.inr rfl)
    rw [hE] at h
    have h' : ENNReal.ofReal (yNorm 2 (ovCoef 𝔮.J θ F τ ((2 : ℝ) ^ τ * ((v : ℝ) + 1)))) ≤
        ENNReal.ofReal (coefConst 𝔮 2 + 1) * ENNReal.ofReal 1 * ENNReal.ofReal e := by
      simpa using h
    have := real_of_enn_mul (by have := coefConst_nonneg 𝔮 2; linarith) zero_le_one he h'
    rw [yNorm_neg_ov (by norm_num)]
    simpa using this
  have hB0 : 0 ≤ (coefConst 𝔮 2 + 1) * e := by have := coefConst_nonneg 𝔮 2; positivity
  have hbump : yNorm 2 (∑ τ ∈ L', bumpAt TA t.1 θ (fun τ x => ovCoef 𝔮.J θ F τ x) (fun τ x => -ovCoef 𝔮.J θ F τ x) τ z) ≤
      16 * ((coefConst 𝔮 2 + 1) * e) := by
    rw [← overlapBumps_eq_sum]
    exact yNorm_overlapBumps_le TA t.1 L' θ _ _ (by norm_num) hB0 hcL hcR z
  -- assemble
  unfold Dout
  rw [Set.indicator_of_mem (by simpa using hz)]
  refine (CZ.yNorm_add_le (by norm_num) _ _).trans ?_
  have hsubn := yNorm_sub_ov (s := 2) (by norm_num) (tmult (lowSym θ σ) F z) (overlapPi TA t.1 (ovScales 𝔮.J s₀ lo t.1.1) θ F z)
  have : Ab 𝔮 * e * jb ((z - x') / (2 : ℝ) ^ σ) ^ 𝔮.N ≥ |polyC 𝔮 2| * jb ((z - x') / (2 : ℝ) ^ σ) ^ 𝔮.N * e +
      |oaConst 𝔮 2| * e + 16 * ((coefConst 𝔮 2 + 1) * e) := by
    unfold Ab
    have hc := coefConst_nonneg 𝔮 2
    nlinarith [mul_nonneg (abs_nonneg (oaConst 𝔮 2)) he, mul_nonneg (mul_nonneg (abs_nonneg (oaConst 𝔮 2)) he) (sub_nonneg.2 hjb1),
      mul_nonneg hB0 (sub_nonneg.2 hjb1), mul_nonneg (abs_nonneg (polyC 𝔮 2)) he]
  linarith

end Out

end PrimeBHT.TimeFrequency.X2
