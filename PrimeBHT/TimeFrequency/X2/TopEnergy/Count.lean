module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Finite
public import PrimeBHT.TimeFrequency.X2.TopEnergy.Value

/-!
# X2, node V12-top (TB-5): one round of the selection and its count

For one side `σ = ±1`: the greedy selection of the data with `valS σ > e/4` (maximal `ξ` first in the reflected
coordinate `ξ' = σ ξ`), its termination (TB-0), and the Bessel count
`Σ_{V selected} |W_V| ≤ 1024 C₁² ‖F‖₂² / e²` (TB-1, TB-2, TB-5: dual vectors of the one-sided top operators, the top
separation `top_separation_pair_H`, and the abstract Bessel inequality `bessel_of_sep`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- The constant of the duals of one-sided top multipliers (`β = 12`). -/
def topC₁ (𝔭 : Params) : ℝ := 2 ^ 13 * 12 * 𝔭.C * 𝔭.C

theorem topC₁_nonneg {𝔭 : Params} (h : 0 ≤ 𝔭.C) : 0 ≤ topC₁ 𝔭 := by unfold topC₁; positivity

/-- The normalized amplitude `ĉ = |W|^{-1/2} ‖ψ T_m F‖₂`. -/
def chatTop (W : ℤ × ℤ) (ψ m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : ℝ :=
  ((2 : ℝ) ^ W.1) ^ (-(1 : ℝ) / 2) * va ψ m F

/-- The classes of a one-sided top datum for the duals. -/
theorem topData_classes {𝔭 : Params} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3}
    {ψ m : ℝ → ℂ} (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMultS 𝔭 σ W ξ k m) :
    InPsi 𝔭.shellCls W.1 W.2 ψ ∧ InMult 𝔭.shellCls W.1 (shellC σ k W ξ) m ∧
      ∀ ζ, ζ ∉ Icc (shellLo σ k W ξ) (shellUp σ k W ξ) → m ζ = 0 :=
  ⟨hψ, hm.inMult hσ, fun _ζ hζ => hm.zero_off_shell hσ hζ⟩

/-- **Bounds for one operator**: `|W| ĉ² ≤ 64 C₁² ‖F‖₂²` and `ĉ ≤ (2/5) C₁ B`. -/
theorem single_val_bounds {𝔭 : Params} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {ψ m : ℝ → ℂ} (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMultS 𝔭 σ W ξ k m)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B)
    (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2)) (hC : 0 ≤ 𝔭.C) :
    (2 : ℝ) ^ W.1 * chatTop W ψ m F ^ 2 ≤ 64 * topC₁ 𝔭 ^ 2 * ∫ x, yNorm 2 (F x) ^ 2 ∧
      chatTop W ψ m F ≤ 2 / 5 * topC₁ 𝔭 * B := by
  obtain ⟨h1, h2, h3⟩ := topData_classes hσ hψ hm
  have hfam := topDualFam (ι := Unit) (F := F) {()} (fun _ => W) (fun _ => shellC σ k W ξ)
    (fun _ => shellLo σ k W ξ) (fun _ => shellUp σ k W ξ) (fun _ => ψ) (fun _ => m)
    (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num)
    (fun _ _ => h1) (fun _ _ => h2) (fun _ _ => h3) hF hB
  have hC₀ : 0 ≤ 2 ^ 13 * 𝔭.shellCls.β * 𝔭.shellCls.C * 𝔭.shellCls.C := by
    simp only [Params.shellCls_β, Params.shellCls_C]; positivity
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self _
  have e : 2 ^ 13 * 𝔭.shellCls.β * 𝔭.shellCls.C * 𝔭.shellCls.C = topC₁ 𝔭 := by
    simp only [Params.shellCls_β, Params.shellCls_C, topC₁]
  rw [e] at hC₀ hfam
  have hs := single_L2 hfam hC₀ hF hB hFint hmem
  have hc := chat_le_of_bdd hfam hC₀ hF hB hmem
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ W.1 := zpow_pos (by norm_num) _
  have hsq := ell_mul_chatF_sq (ℓ := fun _ : Unit => (2 : ℝ) ^ W.1) (i := ()) hℓ (fun _ => va ψ m F)
  refine ⟨?_, ?_⟩
  · show (2 : ℝ) ^ W.1 * chatF (fun _ : Unit => (2 : ℝ) ^ W.1) (fun _ => va ψ m F) () ^ 2 ≤ _
    rw [hsq]; exact hs
  · exact hc


/-- The candidate predicate (reflected coordinate `ξ' = σ ξ`): the `σ`-side value exceeds `e/4`. -/
def candS (𝔭 : Params) (σ : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (e : ℝ≥0∞) : ℤ × ℤ → ℝ → Prop :=
  fun W ξ' => e / 4 < valS 𝔭 σ k F W (σ * ξ')

/-- A candidate has a near-maximizing operator. -/
theorem candS_data {𝔭 : Params} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {k : Fin 3}
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) {e : ℝ≥0∞} (heT : e ≠ ⊤)
    {W : ℤ × ℤ} {ξ' : ℝ} (h : candS 𝔭 σ k F e W ξ') :
    ∃ ψ m : ℝ → ℂ, InPsi 𝔭 W.1 W.2 ψ ∧ InTopMultS 𝔭 σ W (σ * ξ') k m ∧
      e.toReal / 4 < chatTop W ψ m F := by
  unfold candS valS at h
  obtain ⟨ψ, h1⟩ := lt_iSup_iff.1 h
  obtain ⟨m, h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨hψ, h3⟩ := lt_iSup_iff.1 h2
  obtain ⟨hm, h4⟩ := lt_iSup_iff.1 h3
  refine ⟨ψ, m, hψ, hm, ?_⟩
  obtain ⟨c1, c2, -⟩ := topData_classes hσ hψ hm
  have heq := ofReal_val_eq (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num) c1 c2 hF hB
  rw [heq] at h4
  have h5 : e / 4 < ENNReal.ofReal (chatTop W ψ m F) := h4
  have heT4 : e / 4 ≠ ⊤ := by
    intro h; rw [ENNReal.div_eq_top] at h; rcases h with ⟨_, h⟩ | ⟨h, _⟩ <;> simp_all
  rw [ENNReal.lt_ofReal_iff_toReal_lt heT4] at h5
  have : (e / 4).toReal = e.toReal / 4 := by
    rw [ENNReal.toReal_div]; norm_num
  rwa [this] at h5

/-- A point is in the shell of the `σ`-side iff `σ x` is in the `plusShell` of the reflected datum. -/
theorem mem_Icc_shell_iff {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin 3) (W : ℤ × ℤ) (ξ' x : ℝ) :
    x ∈ Icc (shellLo σ k W (σ * ξ')) (shellUp σ k W (σ * ξ')) ↔ σ * x ∈ plusShell (freqDir k) W ξ' := by
  rcases hσ with rfl | rfl
  · rw [one_mul, shellLo_one, shellUp_one, one_mul]; rfl
  · rw [shellLo_neg, shellUp_neg]
    unfold plusShell
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem Ico_dyCentre (s v : ℤ) :
    Ico (dyCentre s v - (2 : ℝ) ^ s / 2) (dyCentre s v + (2 : ℝ) ^ s / 2) = dyadicInt s v := by
  unfold dyCentre dyadicInt
  congr 1 <;> ring


theorem one_le_freqDir (k : Fin 3) : 1 ≤ freqDir k := by fin_cases k <;> simp [freqDir]

theorem ofReal_chatTop_le_valS {𝔭 : Params} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B)
    {W : ℤ × ℤ} {ξ : ℝ} {ψ m : ℝ → ℂ} (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMultS 𝔭 σ W ξ k m) :
    ENNReal.ofReal (chatTop W ψ m F) ≤ valS 𝔭 σ k F W ξ := by
  obtain ⟨c1, c2, -⟩ := topData_classes hσ hψ hm
  have heq := ofReal_val_eq (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num) c1 c2 hF hB
  refine le_iSup₂_of_le ψ m (le_iSup₂_of_le hψ hm ?_)
  rw [heq]; exact le_rfl

/-- **One round** (side `σ`): the greedy selection of the data with `valS σ > e/4`, maximal `ξ' = σ ξ` first, runs until
no admissible candidate is left (TB-0), and `Σ |W_V| ≤ 1024 C₁² ‖F‖₂² / e²` (TB-1, TB-2, TB-5). -/
theorem round_selection (𝔭 : Params) (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hjf : jFloor ≤ 𝔭.J) (hC : 0 ≤ 𝔭.C)
    {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin 3)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hB : ∀ x, yNorm 2 (F x) ≤ 1)
    (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2)) (C₀ : Finset TriTile) (hbox : ∀ R ∈ C₀, R.box ∈ Qs)
    {e : ℝ≥0∞} (he0 : e ≠ 0) (heT : e ≠ ⊤)
    (hE : ∀ W ξ, IsTopDatum 𝔭.J C₀ W ξ → topOpNorm 𝔭 2 2 k F W ξ ≤ e) :
    ∃ ts : List TopSel,
      (∀ W ξ', candS 𝔭 σ k F e W ξ' → ¬ IsTopDatumH (Hσ σ) fatRad 𝔭.J (resH (Hσ σ) C₀ ts) W ξ') ∧
      (ts.map fun V => ENNReal.ofReal ((2 : ℝ) ^ V.W.1)).sum ≤
        ENNReal.ofReal (1024 * topC₁ 𝔭 ^ 2 * (∫ x, yNorm 2 (F x) ^ 2) / e.toReal ^ 2) := by
  have he_r : 0 < e.toReal := ENNReal.toReal_pos he0 heT
  set e_r := e.toReal with he_r_def
  set Ifs := ∫ x, yNorm 2 (F x) ^ 2 with hIfs
  have hIfs0 : 0 ≤ Ifs := integral_nonneg fun x => by unfold yNorm; positivity
  have hρ : (0 : ℝ) ≤ fatRad := by unfold fatRad; norm_num
  have hC₁ : 0 ≤ topC₁ 𝔭 := topC₁_nonneg hC
  -- the scale bound for candidates
  set L₀ := 1024 * topC₁ 𝔭 ^ 2 * Ifs / e_r ^ 2 with hL₀
  have hL : ∀ W ξ', candS 𝔭 σ k F e W ξ' → (2 : ℝ) ^ W.1 ≤ L₀ := by
    intro W ξ' h
    obtain ⟨ψ, m, hψ, hm, hgt⟩ := candS_data hN hD hσ hF hB heT h
    obtain ⟨h1, -⟩ := single_val_bounds hN hD hσ hψ hm hF hB hFint hC
    have hℓ : 0 < (2 : ℝ) ^ W.1 := zpow_pos (by norm_num) _
    have h2 : (2 : ℝ) ^ W.1 * (e_r / 4) ^ 2 ≤ (2 : ℝ) ^ W.1 * chatTop W ψ m F ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hgt.le 2) hℓ.le
    rw [hL₀, le_div_iff₀ (by positivity)]
    nlinarith
  -- the bounded hulls
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ R ∈ C₀, ∀ x ∈ Hσ σ R.box, |x| ≤ M := by
    have hb : Bornology.IsBounded (⋃ R ∈ C₀, Box.hull R.box) :=
      (Bornology.isBounded_biUnion_finset C₀).2 fun R _ => by unfold Box.hull; exact Metric.isBounded_Icc _ _
    obtain ⟨M', hM'⟩ := isBounded_iff_forall_norm_le.1 hb
    refine ⟨max M' 0, le_max_right _ _, fun R hR x hx => ?_⟩
    have h1 : σ * x ∈ Box.hull R.box := hx
    have h2 := hM' (σ * x) (Set.mem_biUnion hR h1)
    have h3 : |σ * x| = |x| := by rcases hσ with rfl | rfl <;> simp
    rw [Real.norm_eq_abs, h3] at h2
    exact h2.trans (le_max_left _ _)
  have hfin : {p : (ℤ × ℤ) × ℝ | candS 𝔭 σ k F e p.1 p.2 ∧ IsTopDatumH (Hσ σ) fatRad 𝔭.J C₀ p.1 p.2}.Finite :=
    (finite_topData hρ 𝔭.J C₀ hM0 hM L₀).subset fun p hp => ⟨hp.2, hL p.1 p.2 hp.1⟩
  obtain ⟨ts, hsel, hres⟩ := exists_greedy (Hσ σ) hρ 𝔭.J (candS 𝔭 σ k F e) C₀.card C₀ le_rfl hfin
  refine ⟨ts, hres, ?_⟩
  -- the selected data
  have hmono : ∀ C C' W ξ ζ, C ⊆ C' → AdmH (Hσ σ) fatRad 𝔭.J C W ξ ζ → AdmH (Hσ σ) fatRad 𝔭.J C' W ξ ζ :=
    fun C C' W ξ ζ h hd => hd.mono h
  have hadm := hsel.adm_cand hmono
  have hnodup := hsel.nodup hρ
  have hdata : ∀ V ∈ ts, ∃ ψ m : ℝ → ℂ, InPsi 𝔭 V.W.1 V.W.2 ψ ∧ InTopMultS 𝔭 σ V.W (σ * V.ξ) k m ∧
      e_r / 4 < chatTop V.W ψ m F := fun V hV => candS_data hN hD hσ hF hB heT (hadm V hV).2
  choose! ψ m hψ hm hgt using hdata
  set 𝒮 : Finset TopSel := ts.toFinset with h𝒮
  have hmem : ∀ V ∈ 𝒮, V ∈ ts := fun V hV => List.mem_toFinset.1 hV
  have hcls := fun V (hV : V ∈ 𝒮) => topData_classes hσ (hψ V (hmem V hV)) (hm V (hmem V hV))
  have hfam := topDualFam (ι := TopSel) (F := F) 𝒮 (fun V => V.W) (fun V => shellC σ k V.W (σ * V.ξ))
    (fun V => shellLo σ k V.W (σ * V.ξ)) (fun V => shellUp σ k V.W (σ * V.ξ)) ψ m
    (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num)
    (fun V hV => (hcls V hV).1) (fun V hV => (hcls V hV).2.1) (fun V hV => (hcls V hV).2.2) hF hB
  have e' : 2 ^ 13 * 𝔭.shellCls.β * 𝔭.shellCls.C * 𝔭.shellCls.C = topC₁ 𝔭 := by
    simp only [Params.shellCls_β, Params.shellCls_C, topC₁]
  rw [e'] at hfam
  -- the shells and the separation
  have hsym : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, (Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ)) ∩
      Icc (shellLo σ k j.W (σ * j.ξ)) (shellUp σ k j.W (σ * j.ξ))).Nonempty →
      (Icc (shellLo σ k j.W (σ * j.ξ)) (shellUp σ k j.W (σ * j.ξ)) ∩
        Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ))).Nonempty :=
    fun i _ j _ ⟨x, hx1, hx2⟩ => ⟨x, hx2, hx1⟩
  have hsep : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ∀ j' ∈ 𝒮, j ≠ j' →
      (Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ)) ∩
        Icc (shellLo σ k j.W (σ * j.ξ)) (shellUp σ k j.W (σ * j.ξ))).Nonempty →
      (Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ)) ∩
        Icc (shellLo σ k j'.W (σ * j'.ξ)) (shellUp σ k j'.W (σ * j'.ξ))).Nonempty →
      (2 : ℝ) ^ j.W.1 ≤ (2 : ℝ) ^ i.W.1 → (2 : ℝ) ^ j'.W.1 ≤ (2 : ℝ) ^ i.W.1 →
      Disjoint (Ico (dyCentre j.W.1 j.W.2 - (2 : ℝ) ^ j.W.1 / 2) (dyCentre j.W.1 j.W.2 + (2 : ℝ) ^ j.W.1 / 2))
        (Ico (dyCentre j'.W.1 j'.W.2 - (2 : ℝ) ^ j'.W.1 / 2) (dyCentre j'.W.1 j'.W.2 + (2 : ℝ) ^ j'.W.1 / 2)) := by
    intro i hi j hj j' hj' hne ⟨x, hx1, hx2⟩ ⟨x', hx1', hx2'⟩ hlj hlj'
    rw [Ico_dyCentre, Ico_dyCentre]
    have h0 : j.W.1 ≤ i.W.1 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlj
    have h0' : j'.W.1 ≤ i.W.1 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlj'
    exact top_separation_pair_H (H := Hσ σ) (ρ := fatRad) (by unfold fatRad; norm_num) hjf hQ hbox hsel
      (one_le_freqDir k) i (hmem j hj) (hmem j' hj') hne h0 h0'
      ⟨σ * x, (mem_Icc_shell_iff hσ k i.W i.ξ x).1 hx1, (mem_Icc_shell_iff hσ k j.W j.ξ x).1 hx2⟩
      ⟨σ * x', (mem_Icc_shell_iff hσ k i.W i.ξ x').1 hx1', (mem_Icc_shell_iff hσ k j'.W j'.ξ x').1 hx2'⟩
  -- the comparability of the amplitudes
  have hupper : ∀ V ∈ 𝒮, chatTop V.W (ψ V) (m V) F ≤ e_r := by
    intro V hV
    have h1 := ofReal_chatTop_le_valS hN hD hσ hF hB (hψ V (hmem V hV)) (hm V (hmem V hV))
    have h2 := valS_le_topOpNorm 𝔭 σ k F V.W (σ * V.ξ)
    have hdat : IsTopDatum 𝔭.J C₀ V.W (σ * V.ξ) :=
      (isTopDatumH_Hσ hσ).1 (hadm V (hmem V hV)).1.2
    have h3 := hE _ _ hdat
    exact (ENNReal.ofReal_le_iff_le_toReal heT).1 (h1.trans (h2.trans h3))
  have hbes := bessel_of_sep hfam (by have := hC₁; exact this.trans' (by positivity) |> fun h => h)
    hF hB hFint hsym hsep (μ := e_r) (K := 1) zero_le_one
    (fun V hV => ⟨by simpa [chatF, chatTop] using (hupper V hV).trans (le_of_eq (one_mul _).symm),
      by have := hgt V (hmem V hV); simp only [chatF, chatTop] at this ⊢; linarith⟩)
  have hsum : ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1 ≤ L₀ := by
    have h1 : ∀ V ∈ 𝒮, (2 : ℝ) ^ V.W.1 * (e_r / 4) ^ 2 ≤ va (ψ V) (m V) F ^ 2 := by
      intro V hV
      have hℓ : 0 < (2 : ℝ) ^ V.W.1 := zpow_pos (by norm_num) _
      have h2 := ell_mul_chatF_sq (ℓ := fun V : TopSel => (2 : ℝ) ^ V.W.1) (i := V) hℓ
        (fun V => va (ψ V) (m V) F)
      have h3 : chatF (fun V : TopSel => (2 : ℝ) ^ V.W.1) (fun V => va (ψ V) (m V) F) V =
          chatTop V.W (ψ V) (m V) F := rfl
      rw [h3] at h2
      have h4 : (e_r / 4) ^ 2 ≤ chatTop V.W (ψ V) (m V) F ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hgt V (hmem V hV)).le 2
      calc (2 : ℝ) ^ V.W.1 * (e_r / 4) ^ 2 ≤ (2 : ℝ) ^ V.W.1 * chatTop V.W (ψ V) (m V) F ^ 2 :=
            mul_le_mul_of_nonneg_left h4 hℓ.le
        _ = va (ψ V) (m V) F ^ 2 := h2
    have h5 : ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1 * (e_r / 4) ^ 2 ≤ 64 * topC₁ 𝔭 ^ 2 * Ifs := by
      refine (Finset.sum_le_sum h1).trans ?_
      simpa using hbes
    rw [← Finset.sum_mul] at h5
    rw [hL₀, le_div_iff₀ (by positivity)]
    nlinarith
  rw [← List.sum_toFinset (fun V : TopSel => ENNReal.ofReal ((2 : ℝ) ^ V.W.1)) hnodup,
    ← ENNReal.ofReal_sum_of_nonneg (fun V _ => (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le)]
  exact ENNReal.ofReal_le_ofReal hsum

end PrimeBHT.TimeFrequency.X2
