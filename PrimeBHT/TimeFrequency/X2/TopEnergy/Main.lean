module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Count
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Geom
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs

/-!
# X2, node V12-top: the energy lemma for top operators at the Hilbert slots (global count)

`EnergyLemmaTopGStatementFor E`: the GLOBAL part (halving and global count) of `EnergyLemmaTopStatement` for the exponents
`E`.  **The localized conjunct of `EnergyLemmaTopStatement` is FALSE** (see the report: top data with `W ⊋` the localizing
interval see far-away mass); it is not used by B10 (`Outside.lean` discards it), only by `EnergyStep`'s statement.

* `energyLemmaTopG_two : EnergyLemmaTopGStatementFor HilbertExp`: PROVED (no hypothesis on the analysis; uses
  `top_separation_pair_H`, the dual-vector Bessel inequality, TB-0 finiteness).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The GLOBAL part of `EnergyLemmaTopStatement` (halving and global count) for the exponents `E`. -/
def EnergyLemmaTopGStatementFor (E : ℝ → ℝ → Prop) : Prop :=
  ∀ (𝔭 : Params), 𝔭.loc.Admissible → ∀ {s qX q : ℝ}, E s qX → qX < q →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (Cs₀ Cs : Finset TriTile), (∀ R ∈ Cs₀, R.box ∈ Qs) → HasTC Cs₀ → IsResidual Cs₀ Cs →
        ∀ (k : Fin 3) (F : ℝ → ZMod P → ℂ), Measurable F → (∀ x, yNorm s (F x) ≤ 1) →
          ∃ ts : List Top,
            engTop 𝔭 s k F (removeTrees Cs ts) qX ≤ engTop 𝔭 s k F Cs qX / 2 ∧
            topSum (removedTrees Cs ts) * engTop 𝔭 s k F Cs qX ^ q ≤ ENNReal.ofReal C * mixedPow qX s F

variable {P : ℕ} [NeZero P]

/-! ## Bounds -/

theorem chatTop_le {𝔭 : Params} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {ψ m : ℝ → ℂ} (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMultS 𝔭 σ W ξ k m)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) (hC : 0 ≤ 𝔭.C) :
    chatTop W ψ m F ≤ 2 / 5 * topC₁ 𝔭 * B := by
  obtain ⟨h1, h2, h3⟩ := topData_classes hσ hψ hm
  have hfam := topDualFam (ι := Unit) (F := F) {()} (fun _ => W) (fun _ => shellC σ k W ξ)
    (fun _ => shellLo σ k W ξ) (fun _ => shellUp σ k W ξ) (fun _ => ψ) (fun _ => m)
    (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num)
    (fun _ _ => h1) (fun _ _ => h2) (fun _ _ => h3) hF hB
  have hC₀ : 0 ≤ 2 ^ 13 * 𝔭.shellCls.β * 𝔭.shellCls.C * 𝔭.shellCls.C := by
    simp only [Params.shellCls_β, Params.shellCls_C]; positivity
  have e : 2 ^ 13 * 𝔭.shellCls.β * 𝔭.shellCls.C * 𝔭.shellCls.C = topC₁ 𝔭 := by
    simp only [Params.shellCls_β, Params.shellCls_C, topC₁]
  rw [e] at hC₀ hfam
  exact chat_le_of_bdd hfam hC₀ hF hB (Finset.mem_singleton_self _)

theorem valS_le_const {𝔭 : Params} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin 3)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) (hC : 0 ≤ 𝔭.C)
    (W : ℤ × ℤ) (ξ : ℝ) : valS 𝔭 σ k F W ξ ≤ ENNReal.ofReal (2 / 5 * topC₁ 𝔭 * B) := by
  refine iSup₂_le fun ψ m => iSup₂_le fun hψ hm => ?_
  obtain ⟨c1, c2, -⟩ := topData_classes hσ hψ hm
  have heq := ofReal_val_eq (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num) c1 c2 hF hB
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (chatTop_le hN hD hσ hψ hm hF hB hC)

theorem engTop_le_const {𝔭 : Params} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hC : 0 ≤ 𝔭.C) (k : Fin 3)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, yNorm 2 (F x) ≤ B)
    (Cs : Finset TriTile) : engTop 𝔭 2 k F Cs 2 ≤ ENNReal.ofReal (4 / 5 * topC₁ 𝔭 * B) := by
  refine iSup₂_le fun W ξ => iSup_le fun _ => ?_
  refine (topOpNorm_le_valS_add 𝔭 k hF hB W ξ).trans ?_
  have h1 := valS_le_const hN hD (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) k hF hB hC W ξ
  have h2 := valS_le_const hN hD (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) k hF hB hC W ξ
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  have hC₁ := topC₁_nonneg hC
  have h0 : 0 ≤ 2 / 5 * topC₁ 𝔭 * B := by positivity
  rw [← ENNReal.ofReal_add h0 h0]
  congr 1; ring


theorem ennreal_div_four_add (e : ℝ≥0∞) : e / 4 + e / 4 = e / 2 := by
  rw [ENNReal.div_add_div_same]
  rw [show e + e = e * 2 by ring]
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  ring

/-- The empty collection has no top data. -/
theorem engTop_empty (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (q : ℝ) :
    engTop 𝔭 s k F ∅ q = 0 := by
  refine le_antisymm (iSup₂_le fun W ξ => iSup_le fun hd => ?_) zero_le
  obtain ⟨-, R, hR, -⟩ := hd
  simp at hR

/-- Finitely many removal tops remove every tile. -/
theorem removeTrees_all (Cs : Finset TriTile) : ∃ ts : List Top, removeTrees Cs ts = ∅ := by
  set t : TriTile → Top := fun R => ((R.box.scale, R.pos), R.box.centre 0 / freqDir 0) with ht
  have key : ∀ (l : List TriTile) (S : Finset TriTile), ∀ R ∈ l, R ∉ removeTrees S (l.map t) := by
    intro l
    induction l with
    | nil => intro S R hR; simp at hR
    | cons R₀ l ih =>
      intro S R hR
      have hsub : removeTrees (S \ maxTree S (t R₀).1 (t R₀).2) (l.map t) ⊆ S \ maxTree S (t R₀).1 (t R₀).2 :=
        removeTrees_subset _ _
      rcases List.mem_cons.1 hR with rfl | hR
      · intro hmem
        have h1 := Finset.mem_sdiff.1 (hsub hmem)
        refine h1.2 (mem_maxTree.2 ⟨h1.1, ?_, ?_⟩)
        · exact subset_rfl
        · exact centre_mem_hull _ 0
      · exact ih _ R hR
  refine ⟨Cs.toList.map t, ?_⟩
  refine Finset.eq_empty_of_forall_notMem fun R hR => ?_
  exact key Cs.toList Cs R (Finset.mem_toList.2 (removeTrees_subset _ _ hR)) hR


/-- **V12-top at the Hilbert slots, global part**: halving and the global count. -/
theorem energyLemmaTopG_two : EnergyLemmaTopGStatementFor HilbertExp := by
  intro 𝔭 h𝔭 s qX q hE hq
  obtain ⟨rfl, rfl⟩ := hE
  obtain ⟨hJ, hNf, hDf, -, -, -, -, hC1⟩ := h𝔭
  have hN : 12 ≤ 𝔭.N := by
    have : classFloor = 400 := rfl
    have h2 : locLoss = 100 := rfl
    simp only [Params.loc_N] at hNf; omega
  have hD : 12 ≤ 𝔭.D := by
    have : classFloor = 400 := rfl
    have h2 : locLoss = 100 := rfl
    simp only [Params.loc_D] at hDf; omega
  have hjf : jFloor ≤ 𝔭.J := by simpa using hJ
  have hC : 0 ≤ 𝔭.C := by simp only [Params.loc_C] at hC1; linarith
  have hC₁ : 0 ≤ topC₁ 𝔭 := topC₁_nonneg hC
  set B₁ : ℝ := 4 / 5 * topC₁ 𝔭 * 1 with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  refine ⟨2048 * topC₁ 𝔭 ^ 2 * B₁ ^ (q - 2) + 1, by positivity, ?_⟩
  intro P _ Qs hQ Cs₀ Cs hbox hTC hres k F hF hB
  have hbox' : ∀ R ∈ Cs, R.box ∈ Qs := fun R hR => hbox R (by
    obtain ⟨ts, rfl⟩ := hres
    exact removeTrees_subset _ _ hR)
  set e := engTop 𝔭 2 k F Cs 2 with he
  have heB : e ≤ ENNReal.ofReal B₁ := engTop_le_const hN hD hC k hF zero_le_one hB Cs
  have heT : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heB
  by_cases he0 : e = 0
  · refine ⟨[], ?_, ?_⟩
    · show engTop 𝔭 2 k F Cs 2 ≤ engTop 𝔭 2 k F Cs 2 / 2
      have h0 : engTop 𝔭 2 k F Cs 2 = 0 := he0
      rw [h0]; simp
    · show topSum [] * _ ≤ _
      rw [topSum_nil, zero_mul]; exact zero_le
  by_cases hmp : mixedPow 2 2 F = ⊤
  · -- degenerate case: remove everything, the right side is `⊤`
    obtain ⟨ts, hts⟩ := removeTrees_all Cs
    refine ⟨ts, ?_, ?_⟩
    · rw [hts, engTop_empty]; exact zero_le
    · rw [hmp, ENNReal.mul_top]
      · exact le_top
      · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  -- the main case
  have hFint := integrable_of_mixedPow_ne_top hF hmp
  have hmpeq := mixedPow_eq_ofReal hFint
  set Ifs := ∫ x, yNorm 2 (F x) ^ 2 with hIfs
  have hIfs0 : 0 ≤ Ifs := integral_nonneg fun x => by unfold yNorm; positivity
  have hEdat : ∀ C : Finset TriTile, C ⊆ Cs → ∀ W ξ, IsTopDatum 𝔭.J C W ξ → topOpNorm 𝔭 2 2 k F W ξ ≤ e :=
    fun C hC W ξ hd => le_iSup₂_of_le W ξ (le_iSup (fun _ : IsTopDatum 𝔭.J Cs W ξ => topOpNorm 𝔭 2 2 k F W ξ)
      (IsTopDatumH.mono (H := Box.hull) (ρ := fatRad) hC hd : IsTopDatum 𝔭.J Cs W ξ))
  -- round 1: the `+` side
  obtain ⟨ts₁, hres₁, hcnt₁⟩ := round_selection 𝔭 hN hD hjf hC hQ (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) k hF hB
    hFint Cs hbox' he0 heT (hEdat Cs subset_rfl)
  set Cs₁ := resH (Hσ 1) Cs ts₁ with hCs₁
  have hCs₁sub : Cs₁ ⊆ Cs := resH_subset _ _ _
  -- round 2: the `-` side on the residual
  obtain ⟨ts₂, hres₂, hcnt₂⟩ := round_selection 𝔭 hN hD hjf hC hQ (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) k hF hB
    hFint Cs₁ (fun R hR => hbox' R (hCs₁sub hR)) he0 heT (hEdat Cs₁ hCs₁sub)
  set Cs₂ := resH (Hσ (-1)) Cs₁ ts₂ with hCs₂
  have hCs₂sub : Cs₂ ⊆ Cs₁ := resH_subset _ _ _
  have h1 : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have h2 : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  refine ⟨ts₁.map (toTop 1) ++ ts₂.map (toTop (-1)), ?_, ?_⟩
  · -- halving
    have hrem : removeTrees Cs (ts₁.map (toTop 1) ++ ts₂.map (toTop (-1))) = Cs₂ := by
      rw [← removeTrees_removeTrees, removeTrees_map_toTop h1, removeTrees_map_toTop h2]
    rw [hrem]
    refine iSup₂_le fun W ξ => iSup_le fun hd => ?_
    refine (topOpNorm_le_valS_add 𝔭 k hF hB W ξ).trans ?_
    have hv1 : valS 𝔭 1 k F W ξ ≤ e / 4 := by
      by_contra hcon
      rw [not_le] at hcon
      have hc : candS 𝔭 1 k F e W ξ := by unfold candS; simpa using hcon
      have hdat : IsTopDatumH (Hσ 1) fatRad 𝔭.J Cs₁ W ξ := by
        rw [isTopDatumH_Hσ h1]
        have hd' : IsTopDatumH Box.hull fatRad 𝔭.J Cs₁ W ξ := IsTopDatumH.mono hCs₂sub hd
        simpa using hd'
      exact hres₁ W ξ hc hdat
    have hv2 : valS 𝔭 (-1) k F W ξ ≤ e / 4 := by
      by_contra hcon
      rw [not_le] at hcon
      have hc : candS 𝔭 (-1) k F e W (-ξ) := by unfold candS; simpa using hcon
      have hdat : IsTopDatumH (Hσ (-1)) fatRad 𝔭.J Cs₂ W (-ξ) := by
        rw [isTopDatumH_Hσ h2]
        have hd' : IsTopDatumH Box.hull fatRad 𝔭.J Cs₂ W ξ := hd
        simpa using hd'
      exact hres₂ W (-ξ) hc hdat
    exact (add_le_add hv1 hv2).trans (le_of_eq (ennreal_div_four_add e))
  · -- the count
    have hsum : topSum (removedTrees Cs (ts₁.map (toTop 1) ++ ts₂.map (toTop (-1)))) ≤
        ENNReal.ofReal (2048 * topC₁ 𝔭 ^ 2 * Ifs / e.toReal ^ 2) := by
      rw [removedTrees_append, topSum_append, removeTrees_map_toTop h1, removedTrees_map_toTop h1,
        removedTrees_map_toTop h2]
      refine (add_le_add hcnt₁ hcnt₂).trans (le_of_eq ?_)
      have hpos : 0 ≤ 1024 * topC₁ 𝔭 ^ 2 * Ifs / e.toReal ^ 2 := by positivity
      rw [← ENNReal.ofReal_add hpos hpos]
      congr 1; ring
    have he_r : 0 < e.toReal := ENNReal.toReal_pos he0 heT
    have he_le : e.toReal ≤ B₁ := by
      have := (ENNReal.toReal_le_toReal heT ENNReal.ofReal_ne_top).2 heB
      rwa [ENNReal.toReal_ofReal hB₁0] at this
    have hq2 : (0 : ℝ) ≤ q - 2 := by linarith
    have heq : e ^ q = ENNReal.ofReal (e.toReal ^ q) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg he_r.le (by linarith), ENNReal.ofReal_toReal heT]
    calc topSum (removedTrees Cs (ts₁.map (toTop 1) ++ ts₂.map (toTop (-1)))) * engTop 𝔭 2 k F Cs 2 ^ q
        ≤ ENNReal.ofReal (2048 * topC₁ 𝔭 ^ 2 * Ifs / e.toReal ^ 2) * e ^ q := by
          exact mul_le_mul' hsum le_rfl
      _ = ENNReal.ofReal (2048 * topC₁ 𝔭 ^ 2 * Ifs / e.toReal ^ 2 * e.toReal ^ q) := by
          rw [heq, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((2048 * topC₁ 𝔭 ^ 2 * B₁ ^ (q - 2) + 1) * Ifs) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 : e.toReal ^ q = e.toReal ^ (2 : ℝ) * e.toReal ^ (q - 2) := by
            rw [← Real.rpow_add he_r]; congr 1; ring
          have h4 : e.toReal ^ (q - 2) ≤ B₁ ^ (q - 2) := Real.rpow_le_rpow he_r.le he_le hq2
          have h5 : e.toReal ^ (2 : ℝ) = e.toReal ^ 2 := Real.rpow_two _
          rw [h3, h5]
          have h6 : 2048 * topC₁ 𝔭 ^ 2 * Ifs / e.toReal ^ 2 * (e.toReal ^ 2 * e.toReal ^ (q - 2)) =
              2048 * topC₁ 𝔭 ^ 2 * Ifs * e.toReal ^ (q - 2) := by field_simp
          rw [h6]
          have h7 : 0 ≤ 2048 * topC₁ 𝔭 ^ 2 * Ifs := by positivity
          calc 2048 * topC₁ 𝔭 ^ 2 * Ifs * e.toReal ^ (q - 2) ≤ 2048 * topC₁ 𝔭 ^ 2 * Ifs * B₁ ^ (q - 2) :=
                mul_le_mul_of_nonneg_left h4 h7
            _ = 2048 * topC₁ 𝔭 ^ 2 * B₁ ^ (q - 2) * Ifs := by ring
            _ ≤ (2048 * topC₁ 𝔭 ^ 2 * B₁ ^ (q - 2) + 1) * Ifs := by nlinarith
      _ = ENNReal.ofReal (2048 * topC₁ 𝔭 ^ 2 * B₁ ^ (q - 2) + 1) * mixedPow 2 2 F := by
          rw [hmpeq, ← ENNReal.ofReal_mul (by positivity)]

end PrimeBHT.TimeFrequency.X2
