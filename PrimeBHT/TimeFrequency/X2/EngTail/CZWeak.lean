module

public import PrimeBHT.TimeFrequency.X2.CZ.Addendum

/-!
# X2, node B5: the strong-type half of `vectorCZStatement` with the scalar `L²` hypothesis for bounded integrable `g` only

`vectorCZStatement` assumes the scalar `L²` bound for every `g ∈ L²`; its proof only uses it for bounded integrable `g`
(`czPack_normalize`).  This file copies `czPack_normalize` and the strong-type half of `vectorCZStatement` with the weaker
hypothesis (`vectorCZ_strong_bdd`), so that tree operators only need the bound for bounded integrable `g`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-- Normalization: a CZ kernel with scalar `L²` bound `A > 0` gives a `CZPack` for `K / A`. -/
theorem czPack_normalize_bdd {A : ℝ} (hA : 0 < A) {K : ℝ → ℝ → ℂ} (hCZ : IsCZKernel A K)
    (hKm : Measurable (Function.uncurry K)) (hMb : ∃ M : ℝ, ∀ x z, ‖K x z‖ ≤ M)
    (hL2 : ∀ g : ℝ → ℂ, Measurable g → Integrable g volume → (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) →
      eLpNorm (fun x => ∫ z, K x z * g z) 2 volume ≤ ENNReal.ofReal A * eLpNorm g 2 volume) :
    CZPack (fun x z => (A : ℂ)⁻¹ * K x z) 13 1 := by
  obtain ⟨hb1, hb2⟩ := czBounds_normalize hA hCZ
  obtain ⟨M, hM⟩ := hMb
  have hmeas : Measurable (Function.uncurry fun x z => (A : ℂ)⁻¹ * K x z) :=
    measurable_const.mul hKm
  have hbdd : ∀ x z, ‖(A : ℂ)⁻¹ * K x z‖ ≤ A⁻¹ * M := by
    intro x z
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left (hM x z) (by positivity)
  refine ⟨hmeas, ⟨A⁻¹ * M, hbdd⟩, fun c u ℓ hu => hH_of_czBounds hb1 c u ℓ hu,
    fun c u ℓ hu => hH_of_czBounds hb2 c u ℓ hu, ?_⟩
  intro g hg
  refine hGood_of_scalar (P := 1) (s := 2) (by norm_num) (K := fun x z => (A : ℂ)⁻¹ * K x z)
    hmeas hbdd ?_ g hg.1 hg.2.1 hg.2.2
  intro h hm hi hb
  have h1 := hL2 h hm hi hb
  have e2 : ENNReal.ofReal 2 = 2 := by norm_num
  rw [kop_normalize, eLpNorm_const_smul, enorm_inv_ofReal hA, e2]
  calc ENNReal.ofReal A⁻¹ * eLpNorm (fun x => ∫ z, K x z * h z) 2 volume
      ≤ ENNReal.ofReal A⁻¹ * (ENNReal.ofReal A * eLpNorm h 2 volume) := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal 1 * eLpNorm h 2 volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; field_simp


/-- The strong-type half of `vectorCZStatement` with the scalar `L²` hypothesis for bounded integrable `g`. -/
theorem vectorCZ_strong_bdd {q s : ℝ} (hq : 1 < q) (hs : 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (A : ℝ) (K : ℝ → ℝ → ℂ), IsCZKernel A K →
      Measurable (Function.uncurry K) → (∃ M : ℝ, ∀ x z, ‖K x z‖ ≤ M) →
      (∀ g : ℝ → ℂ, Measurable g → Integrable g volume → (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) →
        eLpNorm (fun x => ∫ z, K x z * g z) 2 volume ≤ ENNReal.ofReal A * eLpNorm g 2 volume) →
      ∀ F : ℝ → ZMod P → ℂ, Measurable F → (∃ B, ∀ x, yNorm s (F x) ≤ B) →
        eLpNorm (fun x => yNorm s (kernelOp K F x)) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal (C * A) * eLpNorm (fun x => yNorm s (F x)) (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨Aqs, hAqs, hKS⟩ := exists_kStrong_czPack hq hs 13 1 (by norm_num) (by norm_num)
  set C : ℝ := max Aqs 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCA : Aqs ≤ C := le_max_left _ _
  refine ⟨C, by linarith, fun P _ A K hCZ hKm hMb hL2 F hFm hFb => ?_⟩
  obtain ⟨B, hB⟩ := hFb
  have hA0 := hCZ.nonneg
  have hFmy : ∀ y, Measurable fun u => F u y := fun y => (measurable_pi_apply y).comp hFm
  rcases hA0.eq_or_lt with hA | hA
  · -- `A = 0`
    subst hA
    have h0 := kernelOp_eq_zero_of_zero hCZ F
    have hy0 : ∀ x, yNorm s (kernelOp K F x) = 0 := by
      intro x; rw [h0]; exact yNorm_zero' hs0
    have : (fun x => yNorm s (kernelOp K F x)) = fun _ => (0 : ℝ) := funext hy0
    rw [this]; simp
  · -- `A > 0`
    have hpack := czPack_normalize_bdd hA hCZ hKm hMb hL2
    obtain ⟨M, hM⟩ := hpack.bdd
    obtain ⟨hb1, -⟩ := czBounds_normalize hA hCZ
    have hsz : ∀ x u : ℝ, x ≠ u → ‖(A : ℂ)⁻¹ * K x u‖ ≤ 1 / |x - u| := hb1.size
    set Kt : ℝ → ℝ → ℂ := fun x z => (A : ℂ)⁻¹ * K x z with hKt
    -- the relation between `kernelOp K F` and `kop Kt`
    have hkern : ∀ x y, kernelOp K F x y = (A : ℂ) * kop Kt (fun u => F u y) x := by
      intro x y
      have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
      simp only [kernelOp, kop, hKt]
      rw [← integral_const_mul]
      congr 1; ext u; field_simp
    have hyN : ∀ x, yNorm s (kernelOp K F x) = A * yNorm s (fun y => kop Kt (fun u => F u y) x) := by
      intro x
      have : kernelOp K F x = fun y => (A : ℂ) * kop Kt (fun u => F u y) x := funext (hkern x)
      rw [this, yNorm_const_mul (P := P) hs0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    have hGtm : ∀ y, Measurable fun x => kop Kt (fun u => F u y) x := fun y =>
      measurable_kop hpack.meas (hFmy y)
    have hCApos : 0 < C * A := by positivity
    show mixedENorm q s (kernelOp K F) ≤ ENNReal.ofReal (C * A) * mixedENorm q s F
    have hFAE : ∀ y, AEStronglyMeasurable (fun u => F u y) volume := fun y => (hFmy y).aestronglyMeasurable
    by_cases htop : ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q = ⊤
    · have : mixedENorm q s F = ⊤ := by
        have h1 := mixedENorm_rpow hq0 s hFAE
        rw [htop] at h1
        by_contra hne
        exact absurd h1 (ENNReal.rpow_ne_top_of_nonneg hq0.le hne)
      rw [this, ENNReal.mul_top (by simpa using hCApos)]
      exact le_top
    · have hFq : ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q < ⊤ := lt_top_iff_ne_top.2 htop
      have h1 := kStrong_extend hpack.meas hM hsz hq hs (hKS P Kt hpack) hFmy hB hFq
      have hGAE : ∀ y, AEStronglyMeasurable (fun x => kop Kt (fun u => F u y) x) volume :=
        fun y => (hGtm y).aestronglyMeasurable
      set G : ℝ → ZMod P → ℂ := fun x y => kop Kt (fun u => F u y) x with hG
      have hmG : mixedENorm q s G ≤ ENNReal.ofReal Aqs * mixedENorm q s F := by
        have e1 := mixedENorm_rpow hq0 s hGAE
        have e2 := mixedENorm_rpow hq0 s hFAE
        rw [← e1, ← e2, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le] at h1
        exact (ENNReal.rpow_le_rpow_iff hq0).1 h1
      have hscale : mixedENorm q s (kernelOp K F) = ENNReal.ofReal A * mixedENorm q s G := by
        unfold mixedENorm
        have : (fun x => yNorm s (kernelOp K F x)) = (A : ℝ) • fun x => yNorm s (G x) := by
          ext x; rw [hyN x]; rfl
        rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hA.le]
      rw [hscale]
      calc ENNReal.ofReal A * mixedENorm q s G
          ≤ ENNReal.ofReal A * (ENNReal.ofReal Aqs * mixedENorm q s F) := mul_le_mul' le_rfl hmG
        _ = ENNReal.ofReal (Aqs * A) * mixedENorm q s F := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le, mul_comm A]
        _ ≤ ENNReal.ofReal (C * A) * mixedENorm q s F := by
            gcongr

end PrimeBHT.TimeFrequency.X2.CZ
