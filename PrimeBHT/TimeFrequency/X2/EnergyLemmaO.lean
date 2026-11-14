module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.SelectO
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Count
public import PrimeBHT.TimeFrequency.X2.EnergyLemma
public import PrimeBHT.TimeFrequency.X2.Ortho.PintNested

/-!
# X2, node V12 (redesign): the energy lemma from `PintStatementO`

`energyLemmaO (hpint : PintStatementOFor IsEnergyExponent) (hB5 : EngBoundStatement) (hsel : OSelectable) :
EnergyLemmaStatementR`, and the Hilbert endpoint `energyLemmaO_two` whose `pint` input is the UNCONDITIONAL
`pint_two_O_statement`.

`PintStatementOFor` is the TRUE form of `pint` (`IsStronglyDisjointO`); the old `PintStatement`
(`IsStronglyDisjointN`) is FALSE (shell chains).  The remaining open inputs of the energy lemma are therefore:
V11 for `s ≠ 2` in the `O` form, B5 (`eng ≲ 1`), and the selection lemma `OSelectable` (combinatorial, no analysis:
a complete greedy selection satisfying the clause `O1` of `IsStronglyDisjointO`; the clause `O2` and tile-disjointness are
proved, `SelSeq.pairwise_O2`).  With `OSelectable`, one removed maximal tree has ONE lacunary sub-tree in the family, with
`topNorm > λ/2`; the counts are `(λ/2)^q Σ|I_t| ≲ ‖F‖^{qX}` by `count_family` (no three-phase splitting is needed).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **V12 (energy lemma), `O` form**, for the exponent pairs `E`. -/
theorem energyLemmaOFor {E : ℝ → ℝ → Prop} (hE : ∀ s qX, E s qX → 1 ≤ s ∧ 1 ≤ qX)
    (hpint : PintStatementOFor E) (hB5 : EngBoundStatementFor E) (hsel : OSelectable) :
    EnergyLemmaStatementFor E := by
  intro 𝔭 h𝔭 s qX q hX hq
  obtain ⟨hloc, h𝔭dec, h𝔭a, h𝔭locdec⟩ := Params.Admissible.of_loc_decN h𝔭
  have hs1 : 1 ≤ s := (hE s qX hX).1
  have hqX1 : 1 ≤ qX := (hE s qX hX).2
  have hq0 : 0 < q := by linarith
  have hqX0 : 0 < qX := by linarith
  have hα0 : 0 < qX / q := div_pos hqX0 hq0
  have hα1 : qX / q < 1 := (div_lt_one hq0).2 hq
  have hJ : 16 ≤ 𝔭.J := h𝔭a.1
  obtain ⟨Cp, hCp0, hCp⟩ := hpint 𝔭 h𝔭dec hX hα0 hα1
  obtain ⟨Cl, hCl0, hCl⟩ := hpint 𝔭.loc h𝔭locdec hX hα0 hα1
  obtain ⟨C₀, hC₀0, hC₀⟩ := hB5 𝔭 h𝔭a hX
  obtain ⟨K, hK1, hK⟩ := topNorm_le_loc 𝔭 hloc hs1 hqX1
  have hK0 : 0 < K := by linarith
  set K₁ : ℝ := 2 * Cp * C₀ ^ (q - qX) + (2 * Cp) ^ (1 / (qX / q)) + 1 with hK₁
  set K₂ : ℝ := 2 * Cl * C₀ ^ (q - qX) + (2 * Cl) ^ (1 / (qX / q)) + 1 with hK₂
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨max (2 ^ q * K₁) ((2 * K) ^ q * K₂), ?_, ?_⟩
  · exact le_max_of_le_left (by positivity)
  intro P _ Qs hQ Cs₀ Cs hbox hTC hres k F hFm hbd
  have hbCs : ∀ R ∈ Cs, R.box ∈ Qs := by
    obtain ⟨ts₀, rfl⟩ := hres
    exact fun R hR => hbox R (removeTrees_subset _ _ hR)
  set lam := eng 𝔭 s k F Cs qX with hlam
  have hlam_le : lam ≤ ENNReal.ofReal C₀ := hC₀ P Qs hQ Cs hbCs k F hFm hbd
  by_cases hlam0 : lam = 0
  · refine ⟨[], ?_, ?_, fun W _ => ?_⟩
    · show eng 𝔭 s k F Cs qX ≤ lam / 2
      rw [← hlam, hlam0]; simp
    · show topSum [] * lam ^ q ≤ _
      simp
    · show topSum [] * lam ^ q ≤ _
      simp
  have hlamtop : lam ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlam_le
  set lr := lam.toReal with hlr
  have hlr0 : 0 < lr := ENNReal.toReal_pos hlam0 hlamtop
  have hlamr : lam = ENNReal.ofReal lr := (ENNReal.ofReal_toReal hlamtop).symm
  have hlrC : lr ≤ C₀ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlam_le
    rwa [ENNReal.toReal_ofReal hC₀0] at this
  set θ : ℝ≥0∞ := ENNReal.ofReal (lr / 2) with hθ
  obtain ⟨𝒯, hSD, hmem, hhalf⟩ := selectionO hsel hQ hJ hbCs 𝔭 hs1 hqX0 k F θ
  refine ⟨𝒯.map Prod.snd, ?_, ?_, ?_⟩
  · -- halving
    refine hhalf.trans (le_of_eq ?_)
    rw [hlamr, hθ]
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  · -- global count
    have hε0 : 0 < lr / 2 := by positivity
    have hεC : lr / 2 ≤ C₀ := by linarith
    have fam : topSum 𝒯 * ENNReal.ofReal ((lr / 2) ^ q) ≤ ENNReal.ofReal K₁ * mixedPow qX s F := by
      refine count_family hqX0 hq rfl hCp0 hε0 hεC 𝒯 (fun Tr t => topNorm 𝔭 s k F Tr t qX) _
        (fun T hT => (hmem T hT).2.le) ?_
      exact hCp P Qs hQ k 𝒯 hSD (fun T hT R hR => hbCs R ((hmem T hT).1 hR)) F 1 hFm hbd
    rw [topSum_removedTrees, hlamr, ENNReal.ofReal_rpow_of_nonneg hlr0.le hq0.le]
    have h2 : lr ^ q = 2 ^ q * (lr / 2) ^ q := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
    rw [h2, ENNReal.ofReal_mul (by positivity)]
    calc topSum 𝒯 * (ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((lr / 2) ^ q))
        = ENNReal.ofReal (2 ^ q) * (topSum 𝒯 * ENNReal.ofReal ((lr / 2) ^ q)) := by ring
      _ ≤ ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal K₁ * mixedPow qX s F) := by gcongr
      _ = ENNReal.ofReal (2 ^ q * K₁) * mixedPow qX s F := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring
      _ ≤ ENNReal.ofReal (max (2 ^ q * K₁) ((2 * K) ^ q * K₂)) * mixedPow qX s F := by
          gcongr
          exact le_max_left _ _
  · -- localized count
    intro W hW
    have hε0 : 0 < lr / (2 * K) := by positivity
    have hεC : lr / (2 * K) ≤ C₀ := by
      refine (div_le_self hlr0.le (by linarith)).trans hlrC
    have hg := locDiv_measurable W hFm
    have hgb : ∀ x, yNorm s (locDiv W F x) ≤ 1 := fun x =>
      (yNorm_locDiv_le (by linarith) W F x).trans (hbd x)
    have hB : ∃ B, ∀ x, yNorm 2 (locDiv W F x) ≤ B :=
      ⟨(P : ℝ) ^ s⁻¹ * 1, fun x => (yNorm_two_le_rpow_mul (by linarith) _).trans
        (mul_le_mul_of_nonneg_left (hgb x) (by positivity))⟩
    have fam : topSum 𝒯 * ENNReal.ofReal ((lr / (2 * K)) ^ q) ≤
        ENNReal.ofReal K₂ * mixedPow qX s (locDiv W F) := by
      refine count_family hqX0 hq rfl hCl0 hε0 hεC 𝒯
        (fun Tr t => topNorm 𝔭.loc s k (locDiv W F) Tr t qX) _ ?_ ?_
      · intro T hT
        have h1 := hK P k W (locDiv W F) hg hB T.1 T.2 (fun Q hQ' => hW Q ((hmem T hT).1 hQ'))
        rw [locDiv_smul] at h1
        have h2 := (hmem T hT).2
        have h3 : ENNReal.ofReal K * ENNReal.ofReal (lr / (2 * K)) ≤
            ENNReal.ofReal K * topNorm 𝔭.loc s k (locDiv W F) T.1 T.2 qX := by
          rw [← ENNReal.ofReal_mul hK0.le]
          have : K * (lr / (2 * K)) = lr / 2 := by field_simp
          rw [this]
          exact h2.le.trans h1
        exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hK0).ne'
          ENNReal.ofReal_ne_top).1 h3
      · exact hCl P Qs hQ k 𝒯 hSD (fun T hT R hR => hbCs R ((hmem T hT).1 hR)) (locDiv W F) 1 hg hgb
    have e : (fun x => ((locPoly W x)⁻¹ : ℂ) • F x) = locDiv W F := rfl
    rw [e, topSum_removedTrees, hlamr, ENNReal.ofReal_rpow_of_nonneg hlr0.le hq0.le]
    have h2 : lr ^ q = (2 * K) ^ q * (lr / (2 * K)) ^ q := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
    rw [h2, ENNReal.ofReal_mul (by positivity)]
    calc topSum 𝒯 * (ENNReal.ofReal ((2 * K) ^ q) * ENNReal.ofReal ((lr / (2 * K)) ^ q))
        = ENNReal.ofReal ((2 * K) ^ q) * (topSum 𝒯 * ENNReal.ofReal ((lr / (2 * K)) ^ q)) := by ring
      _ ≤ ENNReal.ofReal ((2 * K) ^ q) * (ENNReal.ofReal K₂ * mixedPow qX s (locDiv W F)) := by gcongr
      _ = ENNReal.ofReal ((2 * K) ^ q * K₂) * mixedPow qX s (locDiv W F) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring
      _ ≤ ENNReal.ofReal (max (2 ^ q * K₁) ((2 * K) ^ q * K₂)) * mixedPow qX s (locDiv W F) := by
          gcongr
          exact le_max_right _ _

/-- **V12 (all energy exponents)**: from the TRUE `pint` (V11, `O` form), B5 and the selection lemma. -/
theorem energyLemmaO (hpint : PintStatementOFor IsEnergyExponent) (hB5 : EngBoundStatement)
    (hsel : OSelectable) : EnergyLemmaStatementR :=
  energyLemmaOFor (fun _ _ h => ⟨h.one_le_s, h.one_le_qX⟩) hpint hB5 hsel

end PrimeBHT.TimeFrequency.X2
