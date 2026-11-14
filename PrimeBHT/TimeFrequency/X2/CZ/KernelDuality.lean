module

public import PrimeBHT.TimeFrequency.X2.CZ.Duality
public import PrimeBHT.TimeFrequency.X2.CZ.WeakType

/-!
# V08 phase 3: Fubini pairing for kernel operators and the transfer of strong bounds to the adjoint

For a bounded measurable kernel `K`, `kopVec K F (x, y) = ∫ K(x, u) F(u, y) du`, the adjoint kernel
`K^*(u, x) = conj K(x, u)`.  For `g` in the class `𝒞` (measurable, integrable, bounded fibres) and a test
function `G` (bounded, compactly supported)
`⟨K g, G⟩ = ⟨g, K^* G⟩` (`mixedPairing_kop_eq`), and consequently a strong `(q', s')` bound for `K^*`
on `𝒞` gives the strong `(q, s)` bound for `K` on `𝒞`, with the same constant (`kStrong_of_adjoint`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

theorem integrable_conj' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => (starRingEnd ℂ) (f x)) μ :=
  Integrable.mono' hf.norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.1)
    (ae_of_all _ fun x => by simp)

/-- The adjoint kernel `K^*(u, x) = conj K(x, u)`. -/
def adjKernel (K : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := fun u x => (starRingEnd ℂ) (K x u)

theorem measurable_adjKernel {K : ℝ → ℝ → ℂ} (hKm : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (adjKernel K)) :=
  Complex.continuous_conj.measurable.comp (hKm.comp measurable_swap)

theorem norm_adjKernel {K : ℝ → ℝ → ℂ} (u x : ℝ) : ‖adjKernel K u x‖ = ‖K x u‖ := by
  simp [adjKernel]

/-- The class `𝒞`: measurable, integrable, bounded fibres. -/
def IsClassC {P : ℕ} [NeZero P] (g : ℝ → ZMod P → ℂ) : Prop :=
  (∀ y, Measurable fun u => g u y) ∧ (∀ y, Integrable fun u => g u y) ∧ (∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C)

/-- The strong `(q, s)` bound of the kernel `K` on the class `𝒞`, constant `A`. -/
def KStrong (P : ℕ) [NeZero P] (K : ℝ → ℝ → ℂ) (q s A : ℝ) : Prop :=
  ∀ g : ℝ → ZMod P → ℂ, IsClassC g →
    ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => g u y) x)) ^ q ≤
      ENNReal.ofReal A ^ q * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ q

section Fubini

variable {P : ℕ} [NeZero P]

theorem integrable_of_testFun {G : ℝ → ZMod P → ℂ} (hG : IsTestFun G) (y : ZMod P) :
    Integrable fun x => G x y := by
  obtain ⟨hGm, ⟨Mb, hMb⟩, ⟨R, hR⟩⟩ := hG
  have h1 : IntegrableOn (fun x => G x y) (Icc (-|R|) |R|) volume :=
    Measure.integrableOn_of_bounded (M := Mb) measure_Icc_lt_top.ne
      (hGm y).aestronglyMeasurable (ae_of_all _ fun x => hMb x y)
  have hsupp : Function.support (fun x => G x y) ⊆ Icc (-|R|) |R| := by
    intro x hx
    by_contra hxn
    apply hx
    apply hR x _ y
    simp only [mem_Icc, not_and_or, not_le] at hxn
    rcases hxn with h | h
    · rw [abs_of_neg (by have := abs_nonneg R; linarith)]; linarith [le_abs_self R]
    · rw [abs_of_pos (by have := abs_nonneg R; linarith)]; linarith [le_abs_self R]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 h1

theorem isClassC_of_testFun {G : ℝ → ZMod P → ℂ} (hG : IsTestFun G) : IsClassC G :=
  ⟨hG.1, integrable_of_testFun hG, fun y => by
    obtain ⟨Mb, hMb⟩ := hG.2.1
    exact ⟨Mb, fun u => hMb u y⟩⟩

/-- Scalar Fubini: `∫ (K g)(x) conj(G x) dx = ∫ g(u) conj((K^* G)(u)) du`. -/
theorem integral_kop_mul_conj {K : ℝ → ℝ → ℂ} {M : ℝ} (hKm : Measurable (Function.uncurry K))
    (hKb : ∀ x z, ‖K x z‖ ≤ M) {g G : ℝ → ℂ} (hgi : Integrable g volume) (_hGm : Measurable G)
    (hGi : Integrable G volume) :
    ∫ x, kop K g x * (starRingEnd ℂ) (G x) =
      ∫ u, g u * (starRingEnd ℂ) (kop (adjKernel K) G u) := by
  have hInt : Integrable (Function.uncurry fun x u => K x u * g u * (starRingEnd ℂ) (G x))
      (volume.prod volume) := by
    have h1 : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (G p.1) * g p.2) (volume.prod volume) :=
      (integrable_conj' hGi).mul_prod hgi
    have h2 := h1.bdd_mul (c := M) hKm.aestronglyMeasurable
      (ae_of_all _ fun p => hKb p.1 p.2)
    refine h2.congr (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry]; ring
  have e1 : ∀ x, kop K g x * (starRingEnd ℂ) (G x) = ∫ u, K x u * g u * (starRingEnd ℂ) (G x) := by
    intro x; unfold kop; rw [integral_mul_const]
  have e2 : ∀ u, g u * (starRingEnd ℂ) (kop (adjKernel K) G u) =
      ∫ x, K x u * g u * (starRingEnd ℂ) (G x) := by
    intro u
    unfold kop
    rw [← integral_conj, ← integral_const_mul]
    congr 1; ext x
    simp [adjKernel]; ring
  simp_rw [e1, e2]
  exact integral_integral_swap hInt

theorem norm_kop_le {K : ℝ → ℝ → ℂ} {M : ℝ} (_hKm : Measurable (Function.uncurry K))
    (hKb : ∀ x z, ‖K x z‖ ≤ M) {h : ℝ → ℂ} (hh : Integrable h volume) (x : ℝ) :
    ‖kop K h x‖ ≤ M * ∫ u, ‖h u‖ := by
  unfold kop
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun u => norm_nonneg _) (hh.norm.const_mul M)
    (ae_of_all _ fun u => ?_)
  show ‖K x u * h u‖ ≤ M * ‖h u‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hKb x u) (norm_nonneg _)

theorem mixedPairing_eq_sum {F G : ℝ → ZMod P → ℂ}
    (h : ∀ y, Integrable fun x => F x y * (starRingEnd ℂ) (G x y)) :
    mixedPairing F G = (P : ℂ)⁻¹ * ∑ y, ∫ x, F x y * (starRingEnd ℂ) (G x y) := by
  unfold mixedPairing pairingY
  rw [integral_const_mul, integral_finsetSum]
  intro y _; exact h y

/-- **Fubini pairing**: `⟨K g, G⟩ = ⟨g, K^* G⟩` for `g ∈ 𝒞` and test functions `G`. -/
theorem mixedPairing_kop_eq {K : ℝ → ℝ → ℂ} {M : ℝ} (hKm : Measurable (Function.uncurry K))
    (hKb : ∀ x z, ‖K x z‖ ≤ M) {g G : ℝ → ZMod P → ℂ} (hg : IsClassC g) (hG : IsTestFun G) :
    mixedPairing (fun x y => kop K (fun u => g u y) x) G =
      mixedPairing g (fun u y => kop (adjKernel K) (fun x => G x y) u) := by
  obtain ⟨hgm, hgi, hgb⟩ := hg
  have hGm := hG.1
  have hGi := integrable_of_testFun hG
  obtain ⟨Mb, hMb⟩ := hG.2.1
  have hKa : Measurable (Function.uncurry (adjKernel K)) := measurable_adjKernel hKm
  have hKab : ∀ u x, ‖adjKernel K u x‖ ≤ M := fun u x => by rw [norm_adjKernel]; exact hKb x u
  -- integrability of the two families of integrands
  have hI1 : ∀ y, Integrable fun x => kop K (fun u => g u y) x * (starRingEnd ℂ) (G x y) := by
    intro y
    refine Integrable.bdd_mul (c := M * ∫ u, ‖g u y‖) (integrable_conj' (hGi y))
      ((measurable_kop hKm (hgm y)).aestronglyMeasurable) (ae_of_all _ fun x => norm_kop_le hKm hKb (hgi y) x)
  have hI2 : ∀ y, Integrable fun u => g u y *
      (starRingEnd ℂ) (kop (adjKernel K) (fun x => G x y) u) := by
    intro y
    refine Integrable.mul_bdd (c := M * ∫ x, ‖G x y‖) (hgi y)
      (Complex.continuous_conj.measurable.comp (measurable_kop hKa (hGm y))).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Complex.norm_conj]
    exact norm_kop_le hKa hKab (hGi y) u
  rw [mixedPairing_eq_sum hI1, mixedPairing_eq_sum hI2]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  exact integral_kop_mul_conj hKm hKb (hgi y) (hGm y) (hGi y)

end Fubini

section Transfer

variable {P : ℕ} [NeZero P]

/-- **Duality transfer**: a strong `(q', s')` bound of the adjoint kernel on `𝒞` (hence on test functions)
gives the strong `(q, s)` bound of `K` on `𝒞`, with the same constant. -/
theorem kStrong_of_adjoint {K : ℝ → ℝ → ℂ} {M : ℝ} (hKm : Measurable (Function.uncurry K))
    (hKb : ∀ x z, ‖K x z‖ ≤ M) {q s A : ℝ} (hq : 1 < q) (hs : 1 < s) (_hA : 0 ≤ A)
    (hadj : KStrong P (adjKernel K) (Real.conjExponent q) (Real.conjExponent s) A) :
    KStrong P K q s A := by
  intro g hg
  have hq0 : 0 < q := by linarith
  have hq' := Real.HolderConjugate.conjExponent hq
  have hs' := Real.HolderConjugate.conjExponent hs
  have hq'0 : 0 < Real.conjExponent q := hq'.symm.pos
  have hKa : Measurable (Function.uncurry (adjKernel K)) := measurable_adjKernel hKm
  obtain ⟨hgm, hgi, hgb⟩ := hg
  have hHm : ∀ y, Measurable fun x => kop K (fun u => g u y) x := fun y => measurable_kop hKm (hgm y)
  have hgAE : ∀ y, AEStronglyMeasurable (fun u => g u y) volume := fun y => (hgm y).aestronglyMeasurable
  have hHAE : ∀ y, AEStronglyMeasurable (fun x => kop K (fun u => g u y) x) volume :=
    fun y => (hHm y).aestronglyMeasurable
  set H : ℝ → ZMod P → ℂ := fun x y => kop K (fun u => g u y) x with hH
  have hmain : mixedENorm q s H ≤ ENNReal.ofReal A * mixedENorm q s g := by
    refine mixedENorm_le_of_dual hq hs hHm fun G hGt hGn => ?_
    have hGC := isClassC_of_testFun hGt
    set KG : ℝ → ZMod P → ℂ := fun u y => kop (adjKernel K) (fun x => G x y) u with hKG
    have hKGm : ∀ y, Measurable fun u => KG u y := fun y => measurable_kop hKa (hGt.1 y)
    rw [mixedPairing_kop_eq hKm hKb ⟨hgm, hgi, hgb⟩ hGt]
    refine (ofReal_norm_mixedPairing_le hq' hs' hgAE (fun y => (hKGm y).aestronglyMeasurable)).trans ?_
    have h1 : mixedENorm (Real.conjExponent q) (Real.conjExponent s) KG ≤
        ENNReal.ofReal A * mixedENorm (Real.conjExponent q) (Real.conjExponent s) G := by
      have e1 := mixedENorm_rpow hq'0 (Real.conjExponent s) (fun y => (hKGm y).aestronglyMeasurable)
      have e2 := mixedENorm_rpow hq'0 (Real.conjExponent s) (fun y => (hGt.1 y).aestronglyMeasurable)
      have := hadj G hGC
      rw [← e1, ← e2, ← ENNReal.mul_rpow_of_nonneg _ _ hq'0.le] at this
      exact (ENNReal.rpow_le_rpow_iff hq'0).1 this
    calc mixedENorm q s g * mixedENorm (Real.conjExponent q) (Real.conjExponent s) KG
        ≤ mixedENorm q s g * (ENNReal.ofReal A * mixedENorm (Real.conjExponent q) (Real.conjExponent s) G) :=
          mul_le_mul' le_rfl h1
      _ ≤ mixedENorm q s g * (ENNReal.ofReal A * 1) := by gcongr
      _ = ENNReal.ofReal A * mixedENorm q s g := by rw [mul_one, mul_comm]
  have e1 := mixedENorm_rpow hq0 s hHAE
  have e2 := mixedENorm_rpow hq0 s hgAE
  rw [← e2, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← e1]
  exact ENNReal.rpow_le_rpow hmain hq0.le

end Transfer

end PrimeBHT.TimeFrequency.X2.CZ
