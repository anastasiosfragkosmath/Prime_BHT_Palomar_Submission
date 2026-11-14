module

public import PrimeBHT.TimeFrequency.X2.CZ.MikhlinAll
public import PrimeBHT.TimeFrequency.X2.CZ.CZHormander

/-!
# V08 addendum: strong `(q, s)` and weak `(1, 1)` bounds for general kernels (`CZPack`)

A `CZPack K cH a2` collects what the proof uses of a kernel `K(x, u)`: measurable and bounded, the two
(integral) Hörmander conditions (for `K` in `u`, and for the adjoint `K^*` in `u`; constant `cH`) and the
scalar `L²` bound with constant `a2` (`KStrong 1 K 2 2 a2`).  The package is symmetric
(`CZPack.adj`: duality in `L²`).  From it:

* scalar `L^r` bounds, all `1 < r < ∞` (`exists_kStrong_one`): Marcinkiewicz for `r < 2`, duality for `r > 2`;
* `KStrong P K s s A` for all `P` (`exists_kStrong_diag`; the scalar bound acts fibrewise in `y`);
* `KStrong P K q s A`, all `1 < q, s < ∞`, uniformly in `P` (`exists_kStrong_czPack`);
* the weak `(1,1)` bound on `𝒞` (`exists_weak_czPack`).

Constants depend only on `(q, s, cH, a2)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

theorem adjKernel_adjKernel (K : ℝ → ℝ → ℂ) : adjKernel (adjKernel K) = K := by
  ext x z; simp [adjKernel]

theorem conjExponent_two : Real.conjExponent 2 = 2 := by
  unfold Real.conjExponent; norm_num

/-- The hypotheses of the general Calderón-Zygmund theory (see the module docstring). -/
structure CZPack (K : ℝ → ℝ → ℂ) (cH a2 : ℝ) : Prop where
  meas : Measurable (Function.uncurry K)
  bdd : ∃ M : ℝ, ∀ x z, ‖K x z‖ ≤ M
  hH : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
    ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖K x u - K x c‖ₑ ≤ ENNReal.ofReal cH
  hHadj : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
    ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖adjKernel K x u - adjKernel K x c‖ₑ ≤ ENNReal.ofReal cH
  L2 : KStrong 1 K 2 2 a2

theorem CZPack.adj {K : ℝ → ℝ → ℂ} {cH a2 : ℝ} (h : CZPack K cH a2) (ha2 : 0 ≤ a2) :
    CZPack (adjKernel K) cH a2 where
  meas := measurable_adjKernel h.meas
  bdd := by
    obtain ⟨M, hM⟩ := h.bdd
    exact ⟨M, fun x z => by rw [norm_adjKernel]; exact hM z x⟩
  hH := h.hHadj
  hHadj := by rw [adjKernel_adjKernel]; exact h.hH
  L2 := by
    obtain ⟨M, hM⟩ := h.bdd
    refine kStrong_of_adjoint (K := adjKernel K) (M := M) (measurable_adjKernel h.meas)
      (fun x z => by rw [norm_adjKernel]; exact hM z x)
      (by norm_num) (by norm_num) ha2 ?_
    rw [adjKernel_adjKernel, conjExponent_two]
    exact h.L2

/-- The explicit Marcinkiewicz constant. -/
def czMarc (q s A cH : ℝ) : ℝ :=
  q * 2 ^ q * ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) / (q - 1) + A ^ s / (s - q))

theorem czMarc_nonneg {q s A cH : ℝ} (hq : 1 < q) (hqs : q < s) (hA : 0 ≤ A) (hcH : 0 ≤ cH) :
    0 ≤ czMarc q s A cH := by
  have h1 : 0 < q - 1 := by linarith
  have h2 : 0 < s - q := by linarith
  unfold czMarc
  positivity

/-- For `P = 1` the exponent `s` of `L^s(Y_1)` is immaterial. -/
theorem kStrong_one_congr {K : ℝ → ℝ → ℂ} {q s s' A : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    KStrong 1 K q s A ↔ KStrong 1 K q s' A := by
  unfold KStrong
  simp only [yNorm_zmod_one hs, yNorm_zmod_one hs']

section Strong

variable {K : ℝ → ℝ → ℂ} {cH a2 : ℝ}

/-- Marcinkiewicz for a pack: from `KStrong P K s s A` to `KStrong P K q s` for `1 < q < s`. -/
theorem kStrong_lt_of_pack {P : ℕ} [NeZero P] (hK : CZPack K cH a2) {q s A : ℝ} (hq : 1 < q)
    (hqs : q < s) (hA : 0 ≤ A) (hcH : 0 ≤ cH) (hS : KStrong P K s s A) :
    KStrong P K q s (czMarc q s A cH ^ q⁻¹) := by
  intro g hg
  have hs : 1 < s := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨M, hM⟩ := hK.bdd
  have hMq := czMarc_nonneg hq hqs hA hcH
  have h1 := marcinkiewicz_kernel hs hK.meas hM hA hcH hK.hH
    (fun g hgm hgi hgb => hS g ⟨hgm, hgi, hgb⟩) hq hqs g hg.1 hg.2.1 hg.2.2
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hMq _) hq0.le, ← Real.rpow_mul hMq,
    inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  exact h1

/-- Scalar `L^r` bounds, `1 < r < 2`. -/
theorem kStrong_one_lt_two_pack (hK : CZPack K cH a2) {r : ℝ} (hr : 1 < r) (hr2 : r < 2)
    (ha2 : 0 ≤ a2) (hcH : 0 ≤ cH) : KStrong 1 K r r (czMarc r 2 a2 cH ^ r⁻¹) :=
  (kStrong_one_congr (K := K) (q := r) (A := czMarc r 2 a2 cH ^ r⁻¹) (by norm_num : (0 : ℝ) < 2)
    (by linarith : 0 < r)).1 (kStrong_lt_of_pack (P := 1) (s := 2) (A := a2) hK hr hr2 ha2 hcH hK.L2)

/-- Scalar `L^r` bounds for all `1 < r < ∞`, uniformly over packs. -/
theorem exists_kStrong_one {r : ℝ} (hr : 1 < r) (cH a2 : ℝ) (hcH : 0 ≤ cH) (ha2 : 0 ≤ a2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ K : ℝ → ℝ → ℂ, CZPack K cH a2 → KStrong 1 K r r A := by
  rcases lt_trichotomy r 2 with h | h | h
  · exact ⟨czMarc r 2 a2 cH ^ r⁻¹, Real.rpow_nonneg (czMarc_nonneg hr h ha2 hcH) _,
      fun K hK => kStrong_one_lt_two_pack hK hr h ha2 hcH⟩
  · subst h; exact ⟨a2, ha2, fun K hK => hK.L2⟩
  · obtain ⟨h1, h2⟩ := conjExponent_mem_Ioo h
    refine ⟨czMarc (Real.conjExponent r) 2 a2 cH ^ (Real.conjExponent r)⁻¹,
      Real.rpow_nonneg (czMarc_nonneg h1 h2 ha2 hcH) _, fun K hK => ?_⟩
    obtain ⟨M, hM⟩ := hK.bdd
    refine kStrong_of_adjoint hK.meas hM hr hr (Real.rpow_nonneg (czMarc_nonneg h1 h2 ha2 hcH) _) ?_
    exact kStrong_one_lt_two_pack (hK.adj ha2) h1 h2 ha2 hcH

/-- `KStrong P K s s A` for every `P` (the scalar bound acts fibrewise). -/
theorem exists_kStrong_diag {s : ℝ} (hs : 1 < s) (cH a2 : ℝ) (hcH : 0 ≤ cH) (ha2 : 0 ≤ a2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : ℕ) [NeZero P] (K : ℝ → ℝ → ℂ), CZPack K cH a2 → KStrong P K s s A := by
  obtain ⟨A, hA, hK⟩ := exists_kStrong_one hs cH a2 hcH ha2
  refine ⟨A, hA, fun P _ K hKp g hg => ?_⟩
  obtain ⟨M, hM⟩ := hKp.bdd
  exact hGood_of_scalar hs hKp.meas hM
    (fun h hm hi hb => eLpNorm_kop_le_of_kStrong_one (by linarith) hA (hK K hKp) hm hi hb hKp.meas)
    g hg.1 hg.2.1 hg.2.2

/-- Strong `(q, s)`, `1 < q ≤ s`. -/
theorem exists_kStrong_czPack_le {q s : ℝ} (hq : 1 < q) (hqs : q ≤ s) (cH a2 : ℝ) (hcH : 0 ≤ cH)
    (ha2 : 0 ≤ a2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : ℕ) [NeZero P] (K : ℝ → ℝ → ℂ), CZPack K cH a2 → KStrong P K q s A := by
  have hs : 1 < s := by linarith
  obtain ⟨A₀, hA₀, hdiag⟩ := exists_kStrong_diag hs cH a2 hcH ha2
  rcases hqs.eq_or_lt with h | h
  · subst h; exact ⟨A₀, hA₀, hdiag⟩
  · exact ⟨czMarc q s A₀ cH ^ q⁻¹, Real.rpow_nonneg (czMarc_nonneg hq h hA₀ hcH) _,
      fun P _ K hK => kStrong_lt_of_pack hK hq h hA₀ hcH (hdiag P K hK)⟩

/-- **Strong `(q, s)` for packs, all `1 < q, s < ∞`**, uniformly in `P` and in the pack. -/
theorem exists_kStrong_czPack {q s : ℝ} (hq : 1 < q) (hs : 1 < s) (cH a2 : ℝ) (hcH : 0 ≤ cH)
    (ha2 : 0 ≤ a2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : ℕ) [NeZero P] (K : ℝ → ℝ → ℂ), CZPack K cH a2 → KStrong P K q s A := by
  rcases le_or_gt q s with h | h
  · exact exists_kStrong_czPack_le hq h cH a2 hcH ha2
  · have hq' : 1 < Real.conjExponent q := one_lt_conjExponent' hq
    have hs' : Real.conjExponent q ≤ Real.conjExponent s := by
      unfold Real.conjExponent
      have h1 : 0 < q - 1 := by linarith
      have h2 : 0 < s - 1 := by linarith
      rw [div_le_div_iff₀ h1 h2]; nlinarith
    obtain ⟨A, hA, hK⟩ := exists_kStrong_czPack_le hq' hs' cH a2 hcH ha2
    refine ⟨A, hA, fun P _ K hKp => ?_⟩
    obtain ⟨M, hM⟩ := hKp.bdd
    exact kStrong_of_adjoint hKp.meas hM hq hs hA (hK P _ (hKp.adj ha2))

end Strong

end PrimeBHT.TimeFrequency.X2.CZ
