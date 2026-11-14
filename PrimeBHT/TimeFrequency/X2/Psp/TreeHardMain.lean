module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardSym

/-!
# X2, V15 (assembly), step 11: the paraproduct main term — data and norms

* `treeOp_data`: the tree operator `G_k = Σ_R χ_R T_{m_R} F` of a part is measurable, bounded and `L¹` in `yNorm s` (V14's data class);
* `eLpNorm_treeOp_le`: `‖G_k‖_{L^q(L^s)} ≤ |I_t|^{1/q} eng` (L1, general `(s, q)`);
* `eLpNorm_bdd_supp_le`: a sup bound and support in `A` give `‖f‖_{L^p} ≤ M |A|^{1/p}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem freqDir_of_ne_two {k : Fin 3} (hk : k ≠ 2) : freqDir k = 1 := by
  fin_cases k <;> simp [freqDir] at hk ⊢

theorem freqDir_two : freqDir 2 = 2 := by simp [freqDir]

section Data

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

theorem treeOp_data (pd : PartData 𝔭 η η' Tr TA t χ m) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : IsBddC F) {s : ℝ}
    (hs : 1 ≤ s) :
    Measurable (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F) ∧
      (∃ B, ∀ x, yNorm s (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F x) ≤ B) ∧
      Integrable (fun x => yNorm s (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F x)) := by
  have hs0 : 0 < s := by linarith
  have hgm := pd.goodModel
  have hbd : ∀ Q ∈ TA, ∃ A : ℝ, 0 ≤ A ∧ ∀ x y, ‖tmult (m Q k) F x y‖ ≤ A := fun Q hQ =>
    exists_bound_tmult pd hF hQ
  choose! A hA0 hA using hbd
  have hχb : ∀ Q ∈ TA, ∃ Cχ : ℝ, ∀ x, |χ Q x| ≤ Cχ := fun Q hQ => hgm.bdd Q hQ
  choose! Cχ hCχ using hχb
  have hmeas : Measurable (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F) := by
    unfold treeOp
    refine Finset.measurable_sum _ fun Q hQ => ?_
    exact measurable_psi_smul_tmult_psp (pd.cls Q hQ).1.1 ((pd.cls Q hQ).2 k) hF.measurable
  have hpt : ∀ x, yNorm s (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F x) ≤
      ∑ Q ∈ TA, |χ Q x| * A Q := by
    intro x
    unfold treeOp
    refine (CZ.yNorm_sum_le hs _ _).trans (Finset.sum_le_sum fun Q hQ => ?_)
    rw [yNorm_csmul hs0, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (yNorm_le_of_forall_le hs0 (hA0 Q hQ) (hA Q hQ x)) (abs_nonneg _)
  refine ⟨hmeas, ⟨∑ Q ∈ TA, Cχ Q * A Q, fun x => (hpt x).trans (Finset.sum_le_sum fun Q hQ =>
    mul_le_mul_of_nonneg_right (hCχ Q hQ x) (hA0 Q hQ))⟩, ?_⟩
  refine (integrable_finsetSum TA fun Q hQ => ((hgm.integrable Q hQ).norm.mul_const (A Q))).mono'
    ((measurable_yNorm_fun s).comp hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
  refine (hpt x).trans (le_of_eq (Finset.sum_congr rfl fun Q _ => ?_))
  simp [Complex.norm_real]

/-- **L1** for general `(s, q)`: `‖G_k‖_{L^q(L^s)} ≤ |I_t|^{1/q} eng`. -/
theorem eLpNorm_treeOp_le (pd : PartData 𝔭 η η' Tr TA t χ m) {k : Fin 3} (hIL : IsLacunary k TA) {s q : ℝ}
    (_hq : 0 < q) (F : ℝ → ZMod P → ℂ) :
    eLpNorm (fun x => yNorm s (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F x)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / q)) * eng 𝔭.tree s k F Tr q := by
  have hL1 := lacunary_L1 (s := s) (q := q) (F := F) (Cs := Tr) pd.sub pd.good.1 hIL (pd.lacData k).tree
  unfold treeOpNorm at hL1
  have hp2 := zpow_two_pos t.1.1
  have hcc : ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / q)) * ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp2.le _), ← Real.rpow_add hp2]
    have : 1 / q + -1 / q = 0 := by ring
    rw [this, Real.rpow_zero, ENNReal.ofReal_one]
  calc _ = ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / q)) * (ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F x)) (ENNReal.ofReal q) volume) := by
        rw [← mul_assoc, hcc, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hL1

end Data

theorem eLpNorm_bdd_supp_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) {M : ℝ≥0∞} (hM : ∀ x, f x ≤ M) {A : Set ℝ}
    (hAm : MeasurableSet A) (hA : ∀ x, x ∉ A → f x = 0) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ M * volume A ^ (1 / p) := by
  rw [eLpNorm_ofReal_eq_lintegral hp hf]
  have hI : ∫⁻ x, f x ^ p ≤ ∫⁻ x, A.indicator (fun _ => M ^ p) x := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]; exact ENNReal.rpow_le_rpow (hM x) hp.le
    · rw [Set.indicator_of_notMem hx, hA x hx, ENNReal.zero_rpow_of_pos hp]
  rw [lintegral_indicator_const hAm] at hI
  have hp1 : (0 : ℝ) ≤ 1 / p := by positivity
  calc (∫⁻ x, f x ^ p) ^ (1 / p) ≤ (M ^ p * volume A) ^ (1 / p) := ENNReal.rpow_le_rpow hI hp1
    _ = M * volume A ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp1, ← ENNReal.rpow_mul]
        rw [mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem volume_dilate_three (s v : ℤ) : volume (dilate 3 (dyadicInt s v)) = ENNReal.ofReal (3 * (2 : ℝ) ^ s) := by
  rw [dilate_dyadicInt, Real.volume_Ico]
  congr 1; ring

theorem measurableSet_dilate_three (s v : ℤ) : MeasurableSet (dilate 3 (dyadicInt s v)) := by
  rw [dilate_dyadicInt]
  exact measurableSet_Ico

section Key

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

/-- The modulated symbols and functions of the paraproduct main term. -/
theorem main_key (pd : PartData 𝔭 η η' Tr TA t χ m) {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) {i j : Fin 3} (hi : i ≠ 2) (hj : j ≠ 2) {Tq : Form P}
    (hlacj : ∀ R ∈ TA, ¬ IsOvSlot t j R.box) (hlac2 : ∀ R ∈ TA, ¬ IsOvSlot t 2 R.box)
    {Fh Fw G : ℝ → ZMod P → ℂ} (hFh : Measurable Fh) (hFhb : ∃ B, ∀ x, yNorm 2 (Fh x) ≤ B) (hFw : Measurable Fw)
    (hFwb : ∃ B, ∀ x, yNorm 2 (Fw x) ≤ B) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    ((layerCut η TA σ x ^ 2 : ℝ) : ℂ) * Tq (tmult (m R₀ i) G x) (tmult (m R₀ j) Fh x) (tmult (m R₀ 2) Fw x) =
      ((𝔭.C * lacLam ^ 2 : ℝ) : ℂ) *
        Tq (tmult (fun ξ => ((𝔭.C⁻¹ : ℝ) : ℂ) * m R₀ i (ξ + t.2 * freqDir i))
              (fun z => ovPhase (-(t.2 * freqDir i)) z • G z) x)
          (tmult (fun ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 σ ξ)
              (fun z => ovPhase (-(t.2 * freqDir j)) z • treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R j) Fh z) x)
          (tmult (fun ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 σ ξ)
              (fun z => ovPhase (-(t.2 * freqDir 2)) z • treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R 2) Fw z) x) := by
  obtain ⟨hN, -, -, hC⟩ := pd.h𝔭.bounds
  have hC0 : 0 < 𝔭.C := by linarith
  have hL0 : 0 < lacLam := by linarith [lacLam_spec.1]
  set θi := t.2 * freqDir i with hθi
  set θj := t.2 * freqDir j with hθj
  set θ2 := t.2 * freqDir 2 with hθ2
  have hθ : -θi + -θj = -θ2 := by
    rw [hθi, hθj, hθ2, freqDir_of_ne_two hi, freqDir_of_ne_two hj, freqDir_two]; ring
  -- slot `o`
  have e1 : tmult (fun ξ => ((𝔭.C⁻¹ : ℝ) : ℂ) * m R₀ i (ξ + θi)) (fun z => ovPhase (-θi) z • G z) x =
      (((𝔭.C⁻¹ : ℝ) : ℂ) * ovPhase (-θi) x) • tmult (m R₀ i) G x := by
    rw [tmult_const_mul, tmult_shift_hm (m R₀ i) θi, smul_smul]
    congr 2
    funext z
    rw [smul_smul, ovPhase_add_hm, add_neg_cancel, ovPhase_zero, one_smul]
  -- lacunary slots
  have lacSlot : ∀ (k : Fin 3) (F : ℝ → ZMod P → ℂ), k ≠ 2 ∨ k = 2 → (∀ R ∈ TA, ¬ IsOvSlot t k R.box) →
      Measurable F → (∃ B, ∀ x, yNorm 2 (F x) ≤ B) →
      tmult (fun ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 σ ξ)
        (fun z => ovPhase (-(t.2 * freqDir k)) z • treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F z) x =
      (((lacLam⁻¹ : ℝ) : ℂ) * ovPhase (-(t.2 * freqDir k)) x) • ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x) := by
    intro k F _ hlk hF hFb
    have hL2 := lacunary_layer_proj (k := k) pd.h𝔭 pd.h𝔭.1 hQ hbox pd.good hlk (pd.lacData k) hF hFb hR₀ x
    rw [tmult_const_mul]
    have hsh : tmult (lacSym (t.2 * freqDir k) σ) (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F) x =
        ovPhase (t.2 * freqDir k) x • tmult (lacSym 0 σ) (fun z => ovPhase (-(t.2 * freqDir k)) z •
          treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F z) x := by
      have e : lacSym (t.2 * freqDir k) σ = fun ξ => lacSym 0 σ (ξ + -(t.2 * freqDir k)) := by
        funext ξ; unfold lacSym; congr 3; ring
      rw [e, tmult_shift_hm (lacSym 0 σ) (-(t.2 * freqDir k)), neg_neg]
    have hinv : tmult (lacSym 0 σ) (fun z => ovPhase (-(t.2 * freqDir k)) z •
          treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F z) x =
        ovPhase (-(t.2 * freqDir k)) x • ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x) := by
      rw [← hL2, hsh, smul_smul, ovPhase_add_hm, neg_add_cancel, ovPhase_zero, one_smul]
    rw [hinv, smul_smul]
  have e2 := lacSlot j Fh (Or.inl hj) hlacj hFh hFhb
  have e3 := lacSlot 2 Fw (Or.inr rfl) hlac2 hFw hFwb
  rw [e1, e2, e3]
  rw [Form_phase3 Tq (𝔭.C⁻¹) (lacLam⁻¹) (lacLam⁻¹) hθ, ← Form_smul2, ← mul_assoc, ← Complex.ofReal_mul]
  have h1 : 𝔭.C * lacLam ^ 2 * (𝔭.C⁻¹ * lacLam⁻¹ * lacLam⁻¹) = 1 := by field_simp
  rw [h1]; simp

end Key

/-- **The paraproduct main term** (V14, `paraproduct_draft` with the overlapping Hilbert slot first):
`‖Σ_σ ∫ χ̃² Π(T_{m_σ i} G, a_h, a_w)‖ ≤ C CT |I_t| M_G E_h E_w`, `G` bounded by `M_G`, supported in `3 I_t`. -/
theorem main_term_exists {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {u R : ℝ} (hu : 1 < u) (hR : 2 < R) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ (P : ℕ) [NeZero P] (η η' : ℝ → ℝ) (Tr TA : Finset TriTile) (t : Top)
      (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), PartData 𝔭 η η' Tr TA t χ m →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → (∀ R ∈ TA, R.box ∈ Qs) → ∀ (i j : Fin 3), i ≠ 2 → j ≠ 2 →
      (∀ R ∈ TA, IsOvSlot t i R.box) → (∀ R ∈ TA, ¬ IsOvSlot t j R.box) → (∀ R ∈ TA, ¬ IsOvSlot t 2 R.box) →
      IsLacunary j TA → IsLacunary 2 TA → ∀ (Tq : Form P) (CT : ℝ), FormBound u Tq CT →
      ∀ (Fh Fw G : ℝ → ZMod P → ℂ), Measurable Fh → (∃ B, ∀ x, yNorm 2 (Fh x) ≤ B) → Measurable Fw →
      (∃ B, ∀ x, yNorm 2 (Fw x) ≤ B) → Measurable G → (∃ B, ∀ x, yNorm 2 (G x) ≤ B) →
      (∀ x, x ∉ dilate 3 (dyadicInt t.1.1 t.1.2) → G x = 0) → ∀ MG : ℝ≥0∞,
      (∀ x, ENNReal.ofReal (yNorm 2 (G x)) ≤ MG) → ∀ (R₀ : ℤ → TriTile), (∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) →
      ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 2 : ℝ) : ℂ) *
          Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ ≤
        ENNReal.ofReal (Cm * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
          (MG * (eng 𝔭.tree 2 j Fh Tr 2 * eng 𝔭.tree u 2 Fw Tr R)) := by
  have hJ16 : 16 ≤ 𝔭.J := h𝔭.1
  set p : Fin 3 → ℝ := ![2 * R / (R - 2), 2, R] with hp
  have hRm : 0 < R - 2 := by linarith
  have hp0 : 0 < 2 * R / (R - 2) := div_pos (by linarith) hRm
  have hp1 : ∀ k, 1 < p k := by
    intro k; fin_cases k
    · simp only [hp]
      show 1 < 2 * R / (R - 2)
      rw [lt_div_iff₀ hRm]; linarith
    · simp [hp]
    · simp [hp]; linarith
  have hpsum : ∑ k, 1 / p k = 1 := by
    simp only [Fin.sum_univ_three, hp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp; ring
  obtain ⟨Cp, hCp0, hCp⟩ := paraproduct_draft 𝔭.J 3 (by omega) (le_refl 3) hu ![2, 2, u] (by simp) (by simp) (by simp)
    hp1 hpsum
  obtain ⟨-, -, -, hC⟩ := h𝔭.bounds
  refine ⟨𝔭.C * lacLam ^ 2 * Cp * (3 : ℝ) ^ (1 / (2 * R / (R - 2))), ?_, ?_⟩
  · have := lacLam_spec.1
    positivity
  intro P _ η η' Tr TA t χ m pd Qs hQ hbox i j hi hj hov hlacj hlac2 hILj hIL2 Tq CT hT Fh Fw G hFh hFhb hFw hFwb hG hGb hGs
    MG hMG R₀ hR₀
  by_cases hne : TA.Nonempty
  swap
  · have : TA = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    subst this
    simp [treeScales]
  obtain ⟨R₂, hR₂⟩ := hne
  set J : ℕ := 𝔭.J with hJ
  set s₀ : ℤ := R₂.box.scale with hs₀
  set ts := treeScales TA with hts
  have hdvd : ∀ σ ∈ ts, (J : ℤ) ∣ s₀ - σ := by
    intro σ hσ
    obtain ⟨R', hR', hRs⟩ := mem_treeScales_iff.1 hσ
    have := hQ.1 R₂.box (hbox R₂ hR₂) R'.box (hbox R' hR')
    rw [← hRs]; exact this
  set jidx : ℤ → ℤ := fun σ => (s₀ - σ) / (J : ℤ) with hjidx_def
  have hjidx : ∀ σ ∈ ts, s₀ - (J : ℤ) * jidx σ = σ := by
    intro σ hσ
    have := Int.mul_ediv_cancel' (hdvd σ hσ)
    simp only [hjidx_def]; omega
  have hinj : Set.InjOn jidx (↑ts : Set ℤ) := by
    intro σ hσ σ' hσ' h
    have h1 := hjidx σ hσ
    have h2 := hjidx σ' hσ'
    rw [h] at h1
    omega
  set A : ℝ := (2 : ℝ) ^ (-s₀) / 8 with hA
  have hA0 : 0 < A := by have := zpow_two_pos (-s₀); positivity
  have hθ2 : t.2 * freqDir i + t.2 * freqDir j = t.2 * freqDir 2 := by
    rw [freqDir_of_ne_two hi, freqDir_of_ne_two hj, freqDir_two]; ring
  -- the symbol families
  set σ₁ : ℤ → ℝ → ℂ := fun jj ξ => if (s₀ - (J : ℤ) * jj) ∈ ts then
      ((𝔭.C⁻¹ : ℝ) : ℂ) * m (R₀ (s₀ - (J : ℤ) * jj)) i (ξ + t.2 * freqDir i) else 0 with hσ₁def
  set σ₂ : ℤ → ℝ → ℂ := fun jj ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 (s₀ - (J : ℤ) * jj) ξ with hσ₂def
  have hσ₁ : ∀ jj, IsLowSymbol A J 3 jj (σ₁ jj) := by
    intro jj
    by_cases h : (s₀ - (J : ℤ) * jj) ∈ ts
    · have e : σ₁ jj = fun ξ => ((𝔭.C⁻¹ : ℝ) : ℂ) * m (R₀ (s₀ - (J : ℤ) * jj)) i (ξ + t.2 * freqDir i) := by
        funext ξ; simp only [hσ₁def, ite_eq_left h]
      rw [e]
      obtain ⟨hRT, hsc⟩ := mem_layer'_iff.1 (hR₀ _ h)
      have hm := (pd.cls _ hRT).2 i
      rw [hsc] at hm
      have hθ := abs_theta_sub_centre_le_of_ov (hov _ hRT)
      rw [hsc, abs_sub_comm] at hθ
      exact isLowSymbol_mult pd.h𝔭 hJ16 (σ := s₀ - (J : ℤ) * jj) rfl hm hθ
    · have e : σ₁ jj = fun _ => 0 := by funext ξ; simp only [hσ₁def, ite_eq_right h]
      rw [e]; exact isLowSymbol_zero _ _ _ _
  have hσ₂ : ∀ jj, IsLPSymbol A J 3 jj (σ₂ jj) := fun jj => isLPSymbol_lac hJ16 (σ := s₀ - (J : ℤ) * jj) rfl
  -- the modulated functions
  set Gh : ℝ → ZMod P → ℂ := treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R j) Fh with hGh
  set Gw : ℝ → ZMod P → ℂ := treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R 2) Fw with hGw
  set θi := t.2 * freqDir i with hθi
  set θj := t.2 * freqDir j with hθj
  set θ2 := t.2 * freqDir 2 with hθ2'
  set g : Fin 3 → ℝ → ZMod P → ℂ := ![fun z => ovPhase (-θi) z • G z, fun z => ovPhase (-θj) z • Gh z,
    fun z => ovPhase (-θ2) z • Gw z] with hg
  have hdata_h := treeOp_data pd (k := j) (isBddC_of_hFb hFh hFhb) (s := 2) (by norm_num)
  have hdata_w := treeOp_data pd (k := 2) (isBddC_of_hFb hFw hFwb) (s := 2) (by norm_num)
  have hnorm : ∀ (θ : ℝ) (v : ℝ → ZMod P → ℂ) (s' : ℝ) (z : ℝ), 1 ≤ s' →
      yNorm s' (ovPhase θ z • v z) = yNorm s' (v z) := by
    intro θ v s' z hs'
    rw [yNorm_csmul (by linarith), norm_ovPhase, one_mul]
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    fin_cases k
    · exact (continuous_ovPhase _).measurable.smul hG
    · exact (continuous_ovPhase _).measurable.smul hdata_h.1
    · exact (continuous_ovPhase _).measurable.smul hdata_w.1
  have hgb : ∀ k, ∃ B, ∀ x, yNorm 2 (g k x) ≤ B := by
    intro k
    fin_cases k
    · obtain ⟨B, hB⟩ := hGb
      exact ⟨B, fun x => by simp only [hg]; show yNorm 2 (ovPhase (-θi) x • G x) ≤ B; rw [hnorm _ _ _ _ (by norm_num)]; exact hB x⟩
    · obtain ⟨B, hB⟩ := hdata_h.2.1
      exact ⟨B, fun x => by show yNorm 2 (ovPhase (-θj) x • Gh x) ≤ B; rw [hnorm _ _ _ _ (by norm_num)]; exact hB x⟩
    · obtain ⟨B, hB⟩ := hdata_w.2.1
      exact ⟨B, fun x => by show yNorm 2 (ovPhase (-θ2) x • Gw x) ≤ B; rw [hnorm _ _ _ _ (by norm_num)]; exact hB x⟩
  have hgi : ∀ k, Integrable (fun x => yNorm 2 (g k x)) := by
    intro k
    fin_cases k
    · obtain ⟨B, hB⟩ := hGb
      have hAm := measurableSet_dilate_three t.1.1 t.1.2
      have hfin : volume (dilate 3 (dyadicInt t.1.1 t.1.2)) ≠ ⊤ := by
        rw [volume_dilate_three]; exact ENNReal.ofReal_ne_top
      have hint : Integrable ((dilate 3 (dyadicInt t.1.1 t.1.2)).indicator (fun _ : ℝ => B)) :=
        (integrable_indicator_iff hAm).2 (integrableOn_const hfin)
      refine hint.mono' (((measurable_yNorm_fun 2).comp (hgm 0)).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
      show yNorm 2 (ovPhase (-θi) x • G x) ≤ _
      rw [hnorm _ _ _ _ (by norm_num)]
      by_cases hx : x ∈ dilate 3 (dyadicInt t.1.1 t.1.2)
      · rw [Set.indicator_of_mem hx]; exact hB x
      · rw [Set.indicator_of_notMem hx, hGs x hx]; simp [yNorm_zero_ov]
    · refine hdata_h.2.2.congr (Filter.Eventually.of_forall fun x => ?_)
      show _ = yNorm 2 (ovPhase (-θj) x • Gh x)
      rw [hnorm _ _ _ _ (by norm_num)]
    · refine hdata_w.2.2.congr (Filter.Eventually.of_forall fun x => ?_)
      show _ = yNorm 2 (ovPhase (-θ2) x • Gw x)
      rw [hnorm _ _ _ _ (by norm_num)]
  have hmain := hCp A hA0 P Tq CT hT (ts.image jidx) (fun _ => 1) (fun _ => by simp) σ₁ σ₂ σ₂ hσ₁ hσ₂ hσ₂ g hgm hgb hgi
  have hg0 : g 0 = fun z => ovPhase (-θi) z • G z := rfl
  have hg1 : g 1 = fun z => ovPhase (-θj) z • Gh z := rfl
  have hg2 : g 2 = fun z => ovPhase (-θ2) z • Gw z := rfl
  have hK1 : 0 ≤ 𝔭.C * lacLam ^ 2 := by have := lacLam_spec.1; positivity
  have hrel : (∑ σ ∈ ts, ∫ x, ((layerCut η TA σ x ^ 2 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)) =
      ((𝔭.C * lacLam ^ 2 : ℝ) : ℂ) * ∑ jj ∈ ts.image jidx, (1 : ℂ) * ∫ x,
        Tq (tmult (σ₁ jj) (g 0) x) (tmult (σ₂ jj) (g 1) x) (tmult (σ₂ jj) (g 2) x) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have e1 : σ₁ (jidx σ) = fun ξ => ((𝔭.C⁻¹ : ℝ) : ℂ) * m (R₀ σ) i (ξ + t.2 * freqDir i) := by
      funext ξ; simp only [hσ₁def]; rw [hjidx σ hσ, ite_eq_left hσ]
    have e2 : σ₂ (jidx σ) = fun ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 σ ξ := by
      funext ξ; simp only [hσ₂def]; rw [hjidx σ hσ]
    rw [e1, e2, hg0, hg1, hg2, one_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact main_key pd hQ hbox hi hj hlacj hlac2 hFh hFhb hFw hFwb (hR₀ σ hσ) x
  have hnE : ∀ (K : ℝ) (S : ℂ), 0 ≤ K → ‖(K : ℂ) * S‖ₑ = ENNReal.ofReal K * ‖S‖ₑ := by
    intro K S hK
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hK]
  rw [hrel, hnE _ _ hK1]
  refine (mul_le_mul' le_rfl hmain).trans ?_
  rw [Fin.prod_univ_three]
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hH := zpow_two_pos t.1.1
  have hpe : 1 / (2 * R / (R - 2)) + 1 / 2 + 1 / R = 1 := by field_simp; ring
  -- slot 0 (the overlapping function `G`)
  have E0 : eLpNorm (fun x => yNorm (![2, 2, u] 0) (g 0 x)) (ENNReal.ofReal (p 0)) volume ≤
      MG * ENNReal.ofReal ((3 * (2 : ℝ) ^ t.1.1) ^ (1 / (2 * R / (R - 2)))) := by
    have e : (fun x => yNorm (![2, 2, u] 0) (g 0 x)) = fun x => yNorm 2 (G x) :=
      funext fun x => by rw [hg0]; exact hnorm _ _ _ _ (by norm_num)
    rw [e]
    have hmeasG : Measurable fun x => yNorm 2 (G x) := (measurable_yNorm_fun 2).comp hG
    rw [← eLpNorm_ofReal_fun hmeasG (fun x => yNorm_nonneg' _ _)]
    have := eLpNorm_bdd_supp_le (f := fun x => ENNReal.ofReal (yNorm 2 (G x))) (ENNReal.measurable_ofReal.comp hmeasG)
      hMG (measurableSet_dilate_three t.1.1 t.1.2) (fun x hx => by rw [hGs x hx]; simp [yNorm_zero_ov]) hp0
    refine this.trans ?_
    rw [volume_dilate_three, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  have E1 : eLpNorm (fun x => yNorm (![2, 2, u] 1) (g 1 x)) (ENNReal.ofReal (p 1)) volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / (2 : ℝ))) * eng 𝔭.tree 2 j Fh Tr 2 := by
    have e : (fun x => yNorm (![2, 2, u] 1) (g 1 x)) = fun x => yNorm 2 (Gh x) :=
      funext fun x => by rw [hg1]; exact hnorm _ _ _ _ (by norm_num)
    rw [e]
    exact eLpNorm_treeOp_le pd hILj (s := 2) (q := 2) (by norm_num) Fh
  have E2 : eLpNorm (fun x => yNorm (![2, 2, u] 2) (g 2 x)) (ENNReal.ofReal (p 2)) volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / R)) * eng 𝔭.tree u 2 Fw Tr R := by
    have e : (fun x => yNorm (![2, 2, u] 2) (g 2 x)) = fun x => yNorm u (Gw x) :=
      funext fun x => by rw [hg2]; exact hnorm _ _ _ _ hu.le
    rw [e]
    exact eLpNorm_treeOp_le pd hIL2 (s := u) (q := R) (by linarith) Fw
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' E0 E1) E2))).trans (le_of_eq ?_)
  have h3 : ENNReal.ofReal ((3 * (2 : ℝ) ^ t.1.1) ^ (1 / (2 * R / (R - 2)))) =
      ENNReal.ofReal ((3 : ℝ) ^ (1 / (2 * R / (R - 2)))) * ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / (2 * R / (R - 2)))) := by
    rw [Real.mul_rpow (by norm_num) hH.le, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  have h2 : ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / (2 * R / (R - 2)))) * ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / (2 : ℝ))) *
      ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / R)) = ENNReal.ofReal ((2 : ℝ) ^ t.1.1) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hH.le _), ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hH.le _)
      (Real.rpow_nonneg hH.le _)), ← Real.rpow_add hH, ← Real.rpow_add hH, hpe, Real.rpow_one]
  have h4 : ENNReal.ofReal (𝔭.C * lacLam ^ 2 * Cp * (3 : ℝ) ^ (1 / (2 * R / (R - 2))) * CT) =
      ENNReal.ofReal (𝔭.C * lacLam ^ 2) * ENNReal.ofReal Cp * ENNReal.ofReal ((3 : ℝ) ^ (1 / (2 * R / (R - 2)))) *
        ENNReal.ofReal CT := by
    have := lacLam_spec.1
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [h4, h3, ← h2, ENNReal.ofReal_mul hCp0]
  ring


end PrimeBHT.TimeFrequency.X2
