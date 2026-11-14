module

public import PrimeBHT.U3MaxMod.Plain
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `l:U3maxmod`, part 5: from real sums to `eLpNorm` with the counting measure
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson

lemma eLpNorm_count_eq' (f : ℤ → ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm f (ENNReal.ofReal r) Measure.count = (∑' x, ‖f x‖ₑ ^ r) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top
    (measurable_of_countable f).aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hr.le]

/-- `ℓ^r` norm of a finitely supported function as an `ENNReal.ofReal` of a real sum. -/
lemma eLpNorm_count_eq_ofReal (F : ℤ → ℂ) (hF : (Function.support F).Finite) {r : ℝ}
    (hr : 0 < r) :
    eLpNorm F (ENNReal.ofReal r) Measure.count =
      ENNReal.ofReal ((∑' x, ‖F x‖ ^ r) ^ (1 / r)) := by
  rw [eLpNorm_count_eq' F hr]
  have hs : Summable (fun x => ‖F x‖ ^ r) :=
    summable_of_hasFiniteSupport (fin_supp_of_imp' (F := fun x => ‖F x‖ ^ r) hF
      (fun x hx h0 => hx (by simp [h0, hr.ne'])))
  have : ∑' x, ‖F x‖ₑ ^ r = ENNReal.ofReal (∑' x, ‖F x‖ ^ r) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => by positivity) hs]
    refine tsum_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
  rw [this, ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun x => by positivity) (by positivity)]

lemma eLpNorm_count_two (F : ℤ → ℂ) (hF : (Function.support F).Finite) :
    eLpNorm F 2 Measure.count = ENNReal.ofReal (Real.sqrt (∑' x, ‖F x‖ ^ 2)) := by
  have h := eLpNorm_count_eq_ofReal F hF (r := 2) (by norm_num)
  rw [ENNReal.ofReal_ofNat] at h
  rw [h, Real.sqrt_eq_rpow]
  congr 2
  refine tsum_congr fun x => ?_
  exact Real.rpow_two _

lemma eLpNorm_count_four (F : ℤ → ℂ) (hF : (Function.support F).Finite) :
    eLpNorm F 4 Measure.count = ENNReal.ofReal ((∑' x, ‖F x‖ ^ 4) ^ (1 / 4 : ℝ)) := by
  have h := eLpNorm_count_eq_ofReal F hF (r := 4) (by norm_num)
  rw [ENNReal.ofReal_ofNat] at h
  rw [h]
  congr 2
  refine tsum_congr fun x => ?_
  exact_mod_cast Real.rpow_natCast ‖F x‖ 4

/-- The support of `x ↦ ∑_{n ∈ I} c n f(x-n) g(x+n)` is finite. -/
lemma fs_bilin (I : Finset ℤ) (c f g : ℤ → ℂ) (hf : (Function.support f).Finite) :
    (Function.support fun x => ∑ n ∈ I, c n * f (x - n) * g (x + n)).Finite := by
  have : (Function.support fun x => ∑ n ∈ I, c n * f (x - n) * g (x + n)) ⊆
      ⋃ n ∈ I, Function.support (fun x => f (x + -n)) := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    simp only [Set.mem_iUnion, Function.mem_support, ne_eq]
    refine ⟨n, hn, ?_⟩
    have := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    simpa [sub_eq_add_neg] using this
  exact (Set.Finite.biUnion I.finite_toSet fun n _ =>
    fin_supp_of_imp (-n) hf fun x hx => hx).subset this


end PrimeBHT.U3MaxMod
