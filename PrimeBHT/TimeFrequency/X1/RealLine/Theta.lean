module

public import PrimeBHT.TimeFrequency.X1.RealLine.ModelSum
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley
public import PrimeBHT.TimeFrequency.Interp.Hull.ModelBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem Θ from the model bound (blueprint node R5, `docs/x1-blueprint.md`)

The model bound is `PrimeBHT.TimeFrequency.Interp.Hull.ModelBound p q r N C` (R6c; proved from M1(ε) in
`Interp/Hull/ModelBound.lean`, `modelBound_of_m1`): for valid `ν = (a, b, s', α)`, finite `P ⊆ triIdx s' α`, packets
`φ` adapted with exponent `N` (frozen `IsAdapted`) and Schwartz `f₁ f₂`, `‖Π_P(f₁,f₂)‖_{L^r} ≤ C ‖f₁‖_p ‖f₂‖_q`,
`Π_P = modelOp P φ`.

* `theta_of_modelBound`: if `0 < r`, `(M - 2 - 2N) min(r,1) > 2` and `ModelBound p q r N C`, then
  `TheoremTheta p q r M C'` with `C' = (3000 · c^{r_*} · ∑_{n ∈ ℤ²} w_n^{r_*})^{1/r_*}`, where
  `r_* = min r 1`, `w_n = (1+|n|)^{-(M-2-2N)}` and `c = C_pk³ · max C 0`, `C_pk = C_pk(ρ, M, N)` the normalisation constant
  of `exists_isAdapted_modelPacket` (the frozen `IsAdapted` has constant exactly `1`, so the blueprint's packets
  are divided by `C_pk`; the factor `3000` of the blueprint is `3000^{1/r_*}` after taking `r_*`-th roots).
* `exists_theta_of_m1` / `theoremB_of_m1`: the consumers, conditional on `M1Prop` (via `modelBound_of_m1`): Theorem Θ for
  all `M ≥ M₀ = 2N + 3 + ⌈2/r_*⌉`, and Theorem B (via `theoremB_of_theta_at`, R3, at the single exponent `M₀`).

Proof of `theta_of_modelBound`: `hasSum_modelFamily` (R4 (d)) gives the pointwise absolutely convergent expansion over
`(ν, n, t)`; along the exhaustion `modelIdx S K` (`|n_i|, |v|, |ℓ| ≤ K`) the partial sums are
`∑_{ν,n} w_n Π_{P_K(ν)}`, bounded in `L^r` by the `r_*`-triangle inequality, `ModelBound` and the normalisation
`C_pk`, and a single Fatou (`eLpNorm_rpow_le_of_tendsto`) passes to the limit.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Finset
open scoped FourierTransform Real SchwartzMap ENNReal

namespace PrimeBHT.TimeFrequency.RealLine

open PrimeBHT.Statements (TriValid triIdx timeInt freqInt IsAdapted IsCutoff)
open PrimeBHT.TimeFrequency.Interp.Hull (modelOp ModelBound M1Prop modelBound_of_m1)

/-! ## Generic tools -/

/-- Partial sums along an exhaustion converge to the sum of a summable family (`F = 0` off the exhaustion). -/
theorem tendsto_sum_finset_of_hasSum {ι E : Type*} [NormedAddCommGroup E] {F : ι → E} {a : E}
    (h : HasSum F a) (Λ : ℕ → Finset ι) (hmono : Monotone Λ) (hcov : ∀ i, F i ≠ 0 → ∃ K, i ∈ Λ K) :
    Tendsto (fun K => ∑ i ∈ Λ K, F i) atTop (𝓝 a) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h' : Tendsto (fun s : Finset ι => ∑ i ∈ s, F i) atTop (𝓝 a) := h
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1 (Metric.tendsto_nhds.1 h' ε hε)
  have hsub : ∀ s : Finset ι, (∀ i ∈ s, ∃ K, i ∈ Λ K) → ∃ K, s ⊆ Λ K := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨K1, h1⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      obtain ⟨K2, h2⟩ := hs a (Finset.mem_insert_self a s)
      exact ⟨max K1 K2, Finset.insert_subset (hmono (le_max_right _ _) h2)
        (h1.trans (hmono (le_max_left _ _)))⟩
  obtain ⟨K₀, hK₀⟩ := hsub (s₀.filter fun i => F i ≠ 0) (fun i hi => hcov i (Finset.mem_filter.1 hi).2)
  refine ⟨K₀, fun K hK => ?_⟩
  have hsK : s₀.filter (fun i => F i ≠ 0) ⊆ Λ K := hK₀.trans (hmono hK)
  have heq : ∑ i ∈ Λ K ∪ s₀, F i = ∑ i ∈ Λ K, F i := by
    refine (Finset.sum_subset Finset.subset_union_left fun i hi hni => ?_).symm
    by_contra hne
    rcases Finset.mem_union.1 hi with h1 | h1
    · exact hni h1
    · exact hni (hsK (Finset.mem_filter.2 ⟨h1, hne⟩))
  rw [← heq]
  exact hs₀ _ Finset.subset_union_right

/-- The `r_*`-th power of the `L^r` norm is lower semicontinuous along pointwise convergence (Fatou). -/
theorem eLpNorm_rpow_le_of_tendsto {Φ : ℕ → ℝ → ℂ} {Θ : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ K, AEStronglyMeasurable (Φ K) volume) (hlim : ∀ x, Tendsto (fun K => Φ K x) atTop (𝓝 (Θ x)))
    {B : ℝ≥0∞} (hB : ∀ K, eLpNorm (Φ K) (ENNReal.ofReal r) volume ^ min r 1 ≤ B) :
    eLpNorm Θ (ENNReal.ofReal r) volume ^ min r 1 ≤ B := by
  have hs : 0 < min r 1 := lt_min hr one_pos
  have hSm : AEStronglyMeasurable Θ volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hΦ (Eventually.of_forall hlim)
  have hle : eLpNorm Θ (ENNReal.ofReal r) volume ≤ B ^ (1 / min r 1) := by
    refine Lp.eLpNorm_le_of_ae_tendsto (ι := ℕ) (u := atTop) (f := Φ)
      (Eventually.of_forall fun K => ?_) hΦ hSm (Eventually.of_forall hlim)
    rw [← ENNReal.rpow_le_rpow_iff hs, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs.ne',
      ENNReal.rpow_one]
    exact hB K
  rw [← ENNReal.rpow_le_rpow_iff (z := min r 1) hs] at hle
  rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs.ne', ENNReal.rpow_one] at hle

/-! ## The model operator: homogeneity and continuity -/

theorem modelOp_const_mul (c : ℝ) (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (f₁ f₂ : ℝ → ℂ) (x : ℝ) :
    modelOp P (fun t k y => (c : ℂ) * φ t k y) f₁ f₂ x = ((c ^ 3 : ℝ) : ℂ) * modelOp P φ f₁ f₂ x := by
  simp only [modelOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [← pairing_eq_frozen, pairing_const_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem continuous_modelOp (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (hφ : ∀ t ∈ P, Continuous (φ t 2)) (f₁ f₂ : ℝ → ℂ) : Continuous (modelOp P φ f₁ f₂) := by
  unfold modelOp
  exact continuous_finsetSum _ fun t ht => continuous_const.mul (hφ t ht)

/-- One weighted finite model sum: from `ModelBound` and the normalisation `C_pk` of the packets. -/
theorem eLpNorm_weighted_modelOp_le {p q r : ℝ} {N : ℕ} {C : ℝ} (hMB : ModelBound p q r N C)
    {Cpk : ℝ} (hCpk : 0 < Cpk) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {a b s' α : ℤ}
    (hν : TriValid a b s' α) {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t)
      (fun x => ((Cpk⁻¹ : ℝ) : ℂ) * φ t k x))
    {w : ℝ} (hw : 0 ≤ w) (f₁ f₂ : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (fun x => (w : ℂ) * modelOp P φ f₁ f₂ x) volume ∧
      eLpNorm (fun x => (w : ℂ) * modelOp P φ f₁ f₂ x) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal (w * Cpk ^ 3 * C) *
          (eLpNorm f₁ (ENNReal.ofReal p) volume * eLpNorm f₂ (ENNReal.ofReal q) volume) := by
  set φ' : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ := fun t k y => ((Cpk⁻¹ : ℝ) : ℂ) * φ t k y with hφ'
  have hpt : ∀ x, (w : ℂ) * modelOp P φ f₁ f₂ x = ((w * Cpk ^ 3 : ℝ) : ℂ) * modelOp P φ' f₁ f₂ x := by
    intro x
    rw [hφ', modelOp_const_mul]
    have : (w : ℂ) = ((w * Cpk ^ 3 : ℝ) : ℂ) * ((Cpk⁻¹ ^ 3 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    conv_lhs => rw [this]
    ring
  have hcont : Continuous (modelOp P φ' f₁ f₂) :=
    continuous_modelOp P φ' (fun t ht => (hφ t ht 2).1.continuous) _ _
  have hfun : (fun x => (w : ℂ) * modelOp P φ f₁ f₂ x) =
      ((w * Cpk ^ 3 : ℝ) : ℂ) • modelOp P φ' f₁ f₂ := by
    funext x
    rw [hpt x]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hcont.const_smul _).aestronglyMeasurable
  · rw [hfun, eLpNorm_const_smul]
    have hen : ‖((w * Cpk ^ 3 : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (w * Cpk ^ 3) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hen]
    have hmb := hMB a b s' α hν P hP φ' hφ f₁ f₂
    calc ENNReal.ofReal (w * Cpk ^ 3) * eLpNorm (modelOp P φ' f₁ f₂) (ENNReal.ofReal r) volume
        ≤ ENNReal.ofReal (w * Cpk ^ 3) * (ENNReal.ofReal C * eLpNorm (⇑f₁) (ENNReal.ofReal p) volume *
            eLpNorm (⇑f₂) (ENNReal.ofReal q) volume) := by gcongr
      _ = ENNReal.ofReal (w * Cpk ^ 3 * C) *
          (eLpNorm f₁ (ENNReal.ofReal p) volume * eLpNorm f₂ (ENNReal.ofReal q) volume) := by
        have h3 : ENNReal.ofReal (w * Cpk ^ 3 * C) =
            ENNReal.ofReal (w * Cpk ^ 3) * ENNReal.ofReal C := ENNReal.ofReal_mul (by positivity)
        rw [h3]
        ring

/-! ## Summability of the weights -/

theorem summable_nrm_rpow {e : ℝ} (he : 2 < e) : Summable (fun n : ℤ × ℤ => nrm n ^ (-e)) := by
  have h1 : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(e / 2))) :=
    summable_one_add_abs_rpow (by linarith)
  have h2 := Summable.mul_of_nonneg h1 h1 (fun n => Real.rpow_nonneg (by positivity) _)
    (fun n => Real.rpow_nonneg (by positivity) _)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (nrm_pos n).le _) (fun n => ?_) h2
  have e1 : nrm n ^ (-e) = nrm n ^ (-(e / 2)) * nrm n ^ (-(e / 2)) := by
    rw [← Real.rpow_add (nrm_pos n)]; congr 1; ring
  rw [e1]
  have hn1 := rpow_neg_anti (by positivity : (0 : ℝ) < 1 + |(n.1 : ℝ)|) (nrm_ge_one_add_abs_fst n)
    (by linarith : (0 : ℝ) ≤ e / 2)
  have hn2 := rpow_neg_anti (by positivity : (0 : ℝ) < 1 + |(n.2 : ℝ)|) (nrm_ge_one_add_abs_snd n)
    (by linarith : (0 : ℝ) ≤ e / 2)
  exact mul_le_mul hn1 hn2 (Real.rpow_nonneg (nrm_pos n).le _) (Real.rpow_nonneg (by positivity) _)

/-! ## Finite partial sums -/

/-- `[-K, K]`. -/
def boxZ (K : ℕ) : Finset ℤ := Finset.Icc (-(K : ℤ)) K

/-- `[-K, K]²`. -/
def boxN (K : ℕ) : Finset (ℤ × ℤ) := boxZ K ×ˢ boxZ K

/-- The tiles with scale in `S` and `|v|, |ℓ| ≤ K`. -/
def tileBox (S : Finset ℤ) (K : ℕ) : Finset (ℤ × ℤ × ℤ) := S ×ˢ (boxZ K ×ˢ boxZ K)

/-- The exhaustion of the index of `modelFamily`. -/
def modelIdx (S : Finset ℤ) (K : ℕ) : Finset ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  nuSet ×ˢ (boxN K ×ˢ tileBox S K)

open Classical in
/-- The finite set `P_K ∩ tileBox` of tiles of `P_ν`. -/
def tilesAt (S : Finset ℤ) (K : ℕ) (ν : ℤ × ℤ × ℤ × ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (tileBox S K).filter (fun t => t ∈ triIdx ν.2.2.1 ν.2.2.2)

theorem boxZ_mono {K K' : ℕ} (h : K ≤ K') : boxZ K ⊆ boxZ K' := by
  intro z hz
  simp only [boxZ, Finset.mem_Icc] at hz ⊢
  omega

theorem modelIdx_mono (S : Finset ℤ) : Monotone (modelIdx S) := by
  intro K K' h
  unfold modelIdx boxN tileBox
  exact Finset.product_subset_product Finset.Subset.rfl
    (Finset.product_subset_product (Finset.product_subset_product (boxZ_mono h) (boxZ_mono h))
      (Finset.product_subset_product Finset.Subset.rfl
        (Finset.product_subset_product (boxZ_mono h) (boxZ_mono h))))

theorem sum_modelIdx (ρ : 𝓢(ℝ, ℂ)) (M N : ℕ) (g : ℤ → ℝ → ℂ) (S : Finset ℤ) (f₁ f₂ : ℝ → ℂ)
    (x : ℝ) (K : ℕ) :
    ∑ q ∈ modelIdx S K, modelFamily ρ M N g S f₁ f₂ x q =
      ∑ ν ∈ nuSet, ∑ n ∈ boxN K, (modelWeight M N n : ℂ) *
        modelOp (tilesAt S K ν) (modelPacket ρ M N g ν n) f₁ f₂ x := by
  classical
  unfold modelIdx
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [modelOp_apply, Finset.mul_sum, tilesAt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hS : t.1 ∈ S := (Finset.mem_product.1 ht).1
  unfold modelFamily
  by_cases hT : t ∈ triIdx ν.2.2.1 ν.2.2.2
  · rw [ite_eq_left hT, ite_eq_left ⟨hν, hT, hS⟩]
  · rw [ite_eq_right hT, ite_eq_right]
    rintro ⟨-, h, -⟩
    exact hT h

theorem eLpNorm_partial_le {p q r : ℝ} (hr : 0 < r) {N : ℕ} {C : ℝ} (hMB : ModelBound p q r N C)
    {Cpk : ℝ} (hCpk : 0 < Cpk) (ρ : 𝓢(ℝ, ℂ)) (M : ℕ) (g : ℤ → ℝ → ℂ) (S : Finset ℤ)
    (hAd : ∀ (ν : ℤ × ℤ × ℤ × ℤ) (n : ℤ × ℤ) (t : ℤ × ℤ × ℤ), t.1 ∈ S → ∀ k : Fin 3,
      IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 k t)
        (fun x => ((Cpk⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t k x))
    (f₁ f₂ : SchwartzMap ℝ ℂ) (K : ℕ) :
    AEStronglyMeasurable (fun x => ∑ q ∈ modelIdx S K, modelFamily ρ M N g S f₁ f₂ x q) volume ∧
    eLpNorm (fun x => ∑ q ∈ modelIdx S K, modelFamily ρ M N g S f₁ f₂ x q) (ENNReal.ofReal r)
        volume ^ min r 1 ≤
      ∑ _ν ∈ nuSet, ∑ n ∈ boxN K, (ENNReal.ofReal (modelWeight M N n * Cpk ^ 3 * C) *
        (eLpNorm f₁ (ENNReal.ofReal p) volume * eLpNorm f₂ (ENNReal.ofReal q) volume)) ^ min r 1 := by
  classical
  set A : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ → ℝ → ℂ := fun ν n x => (modelWeight M N n : ℂ) *
    modelOp (tilesAt S K ν) (modelPacket ρ M N g ν n) f₁ f₂ x with hA
  have hw : ∀ n, 0 ≤ modelWeight M N n := fun n => Real.rpow_nonneg (nrm_pos n).le _
  have hterm : ∀ ν ∈ nuSet, ∀ n, AEStronglyMeasurable (A ν n) volume ∧
      eLpNorm (A ν n) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal (modelWeight M N n * Cpk ^ 3 * C) *
          (eLpNorm f₁ (ENNReal.ofReal p) volume * eLpNorm f₂ (ENNReal.ofReal q) volume) := by
    intro ν hν n
    refine eLpNorm_weighted_modelOp_le hMB hCpk (triValid_of_mem_nuSet hν) ?_ ?_ (hw n) f₁ f₂
    · intro t ht
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
    · intro t ht k
      exact hAd ν n t (Finset.mem_product.1 (Finset.mem_filter.1 ht).1).1 k
  have hfun : (fun x => ∑ q ∈ modelIdx S K, modelFamily ρ M N g S f₁ f₂ x q) =
      ∑ q ∈ nuSet ×ˢ boxN K, A q.1 q.2 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_product, sum_modelIdx]
  have hmeas : ∀ q ∈ nuSet ×ˢ boxN K, AEStronglyMeasurable (A q.1 q.2) volume := fun q hq =>
    (hterm q.1 (Finset.mem_product.1 hq).1 q.2).1
  rw [hfun]
  refine ⟨Finset.aestronglyMeasurable_sum _ hmeas, ?_⟩
  refine (eLpNorm_sum_rpow_le (nuSet ×ˢ boxN K) hr hmeas).trans ?_
  rw [Finset.sum_product]
  refine Finset.sum_le_sum fun ν hν => Finset.sum_le_sum fun n hn => ?_
  exact ENNReal.rpow_le_rpow (hterm ν hν n).2 (lt_min hr one_pos).le

/-- The `ℝ≥0∞` bookkeeping of the `r_*`-triangle inequality over `ν ∈ 𝒩` (`3000` values) and `n ∈ [-K,K]²`. -/
theorem sum_box_le {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 ≤ c) (X : ℝ≥0∞) {w : ℤ × ℤ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hsum : Summable (fun n => w n ^ s)) (K : ℕ) :
    ∑ _ν ∈ nuSet, ∑ n ∈ boxN K, (ENNReal.ofReal (w n * c) * X) ^ s ≤
      ENNReal.ofReal (3000 * (c ^ s * ∑' n, w n ^ s)) * X ^ s := by
  have hterm : ∀ n, (ENNReal.ofReal (w n * c) * X) ^ s = ENNReal.ofReal (w n ^ s * c ^ s) * X ^ s := by
    intro n
    rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (hw0 n) hc) hs.le,
      Real.mul_rpow (hw0 n) hc]
  simp only [hterm]
  rw [Finset.sum_const, card_nuSet, nsmul_eq_mul, ← Finset.sum_mul]
  have h1 : ∑ n ∈ boxN K, ENNReal.ofReal (w n ^ s * c ^ s) ≤
      ENNReal.ofReal (c ^ s * ∑' n, w n ^ s) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Real.rpow_nonneg (hw0 n) _)
      (Real.rpow_nonneg hc _))]
    apply ENNReal.ofReal_le_ofReal
    have := (hsum.mul_right (c ^ s)).sum_le_tsum (boxN K)
      (fun n _ => mul_nonneg (Real.rpow_nonneg (hw0 n) _) (Real.rpow_nonneg hc _))
    rw [tsum_mul_right] at this
    linarith
  calc ((3000 : ℕ) : ℝ≥0∞) * ((∑ n ∈ boxN K, ENNReal.ofReal (w n ^ s * c ^ s)) * X ^ s)
      ≤ ((3000 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (c ^ s * ∑' n, w n ^ s) * X ^ s) := by gcongr
    _ = ENNReal.ofReal (3000 * (c ^ s * ∑' n, w n ^ s)) * X ^ s := by
        have h2 : ENNReal.ofReal (3000 * (c ^ s * ∑' n, w n ^ s)) =
            (3000 : ℝ≥0∞) * ENNReal.ofReal (c ^ s * ∑' n, w n ^ s) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [h2]
        push_cast
        ring

theorem summable_modelWeight_rpow {M N : ℕ} {s : ℝ} (_hs : 0 < s)
    (h : 2 < ((M : ℝ) - 2 - 2 * N) * s) : Summable (fun n : ℤ × ℤ => modelWeight M N n ^ s) := by
  have := summable_nrm_rpow h
  refine this.congr fun n => ?_
  unfold modelWeight
  rw [← Real.rpow_mul (nrm_pos n).le]
  congr 1
  ring

theorem three_lt_of_two_lt_mul {M N : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (h : 2 < ((M : ℝ) - 2 - 2 * N) * s) : 3 < M := by
  have hu : 2 < (M : ℝ) - 2 - 2 * N := by
    by_contra hcon
    push Not at hcon
    rcases le_or_gt 0 ((M : ℝ) - 2 - 2 * N) with h0 | h0
    · nlinarith
    · nlinarith
  have : (3 : ℝ) < M := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  exact_mod_cast this

/-- **R5, with explicit constants.** Given a frame window `ρ`, the normalisation `C_pk` of the packets (so that
`C_pk⁻¹ φ^n_{t,k}` is `IsAdapted N`) and the model bound, Theorem Θ holds with the constant
`(3000 · (C_pk³ max C 0)^{r_*} · ∑_n w_n^{r_*})^{1/r_*}`. -/
theorem theta_of_modelBound_explicit {p q r : ℝ} (hr : 0 < r) {N M : ℕ}
    (hMN : 2 < ((M : ℝ) - 2 - 2 * N) * min r 1) {C : ℝ} (hMB : ModelBound p q r N C)
    {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) {Cpk : ℝ} (hCpk : 0 < Cpk)
    (hAd : ∀ (g : ℤ → ℝ → ℂ) (ν : ℤ × ℤ × ℤ × ℤ) (n : ℤ × ℤ) (t : ℤ × ℤ × ℤ),
      IsBandProfile (M : ℝ) (g t.1) → ∀ k : Fin 3,
        IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 k t)
          (fun x => ((Cpk⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t k x)) :
    TheoremTheta p q r M
      ((3000 * ((Cpk ^ 3 * max C 0) ^ min r 1 * ∑' n : ℤ × ℤ, modelWeight M N n ^ min r 1)) ^
        (1 / min r 1)) := by
  classical
  have hs : 0 < min r 1 := lt_min hr one_pos
  have hM3 : 3 < M := three_lt_of_two_lt_mul hs (min_le_right _ _) hMN
  have hsum := summable_modelWeight_rpow hs hMN
  have hc : 0 ≤ Cpk ^ 3 * max C 0 := by positivity
  set c := Cpk ^ 3 * max C 0 with hcdef
  set W := ∑' n : ℤ × ℤ, modelWeight M N n ^ min r 1 with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun n => Real.rpow_nonneg (Real.rpow_nonneg (nrm_pos n).le _) _
  have hBc : 0 ≤ 3000 * (c ^ min r 1 * W) := by positivity
  intro S g hgi hgF hgD f₁ f₂
  have hband : ∀ s ∈ S, IsBandProfile (M : ℝ) (g s) := fun s hs' =>
    isBandProfile_of_decay (hgi s hs') (hgF s hs') (hgD s hs')
  set X : ℝ≥0∞ := eLpNorm f₁ (ENNReal.ofReal p) volume * eLpNorm f₂ (ENNReal.ofReal q) volume with hX
  have hpart := fun K => eLpNorm_partial_le hr hMB hCpk ρ M g S
    (fun ν n t ht k => hAd g ν n t (hband _ ht) k) f₁ f₂ K
  have hB : ∀ K : ℕ, eLpNorm (fun x => ∑ q ∈ modelIdx S K, modelFamily ρ M N g S f₁ f₂ x q)
      (ENNReal.ofReal r) volume ^ min r 1 ≤
      ENNReal.ofReal (3000 * (c ^ min r 1 * W)) * X ^ min r 1 := by
    intro K
    refine (hpart K).2.trans ?_
    refine le_trans ?_ (sum_box_le hs hc X (fun n => Real.rpow_nonneg (nrm_pos n).le _) hsum K)
    refine Finset.sum_le_sum fun ν hν => Finset.sum_le_sum fun n hn => ?_
    refine ENNReal.rpow_le_rpow ?_ hs.le
    have hw := (Real.rpow_nonneg (nrm_pos n).le (-((M : ℝ) - 2 - 2 * N)))
    have key : modelWeight M N n * Cpk ^ 3 * C ≤ modelWeight M N n * (Cpk ^ 3 * max C 0) := by
      have := le_max_left C 0
      have h3 : 0 ≤ modelWeight M N n * Cpk ^ 3 := mul_nonneg hw (by positivity)
      nlinarith
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal key) le_rfl
  have hlim : ∀ x, Tendsto (fun K : ℕ => ∑ q ∈ modelIdx S K, modelFamily ρ M N g S f₁ f₂ x q) atTop
      (𝓝 (∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x)) := by
    intro x
    refine tendsto_sum_finset_of_hasSum
      (hasSum_modelFamily hρ hM3 N S g hgi hgF hgD f₁ f₂ x) (modelIdx S) (modelIdx_mono S) ?_
    intro q hq
    have hcond : q.1 ∈ nuSet ∧ q.2.2 ∈ tileSet S q.1.2.2.1 q.1.2.2.2 := by
      by_contra hcon
      apply hq
      unfold modelFamily
      exact ite_eq_right hcon
    obtain ⟨ν, ⟨n₁, n₂⟩, ⟨s₀, v, ℓ⟩⟩ := q
    have hν := hcond.1
    have hS : s₀ ∈ S := hcond.2.2
    refine ⟨n₁.natAbs + n₂.natAbs + v.natAbs + ℓ.natAbs, ?_⟩
    simp only [modelIdx, boxN, tileBox, boxZ, Finset.mem_product, Finset.mem_Icc]
    refine ⟨hν, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hS, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
  have hfin := eLpNorm_rpow_le_of_tendsto hr (fun K => (hpart K).1)
    (Θ := fun x => ∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x) hlim hB
  have hSeq : (∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂) =
      fun x => ∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x := by
    funext x
    rw [Finset.sum_apply]
  rw [hSeq]
  have h3 := ENNReal.rpow_le_rpow hfin (one_div_pos.2 hs).le
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hs.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hs).le, ← ENNReal.rpow_mul,
    mul_one_div_cancel hs.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hBc (one_div_pos.2 hs).le] at h3
  rw [mul_assoc]
  exact h3

/-- **R5: Theorem Θ from the model bound.** If `0 < r`, `(M - 2 - 2N) min(r,1) > 2` and `ModelBound p q r N C`
(the model bound of R6c, `Interp/Hull/ModelBound.lean`), then Theorem Θ holds at the decay exponent `M` with some constant
(`theta_of_modelBound_explicit` gives it). -/
theorem theta_of_modelBound {p q r : ℝ} (hr : 0 < r) {N M : ℕ}
    (hMN : 2 < ((M : ℝ) - 2 - 2 * N) * min r 1) {C : ℝ} (hMB : ModelBound p q r N C) :
    ∃ C' : ℝ, TheoremTheta p q r M C' := by
  obtain ⟨ρ, hρ⟩ := exists_isFrameWindow
  have hs : 0 < min r 1 := lt_min hr one_pos
  have hM3 := three_lt_of_two_lt_mul hs (min_le_right _ _) hMN
  obtain ⟨Cpk, hCpk, hAd⟩ := exists_isAdapted_modelPacket hρ hM3 N
  exact ⟨_, theta_of_modelBound_explicit hr hMN hMB hρ hCpk hAd⟩

/-- **Θ from M1(ε)** (consumer shape): conditional on `M1Prop` (the type of the frozen M1(ε)), for
`1 < p, q`, `1/r = 1/p + 1/q`, `2/3 < r` there is `M₀` such that Theorem Θ holds for every `M ≥ M₀` (with some
constant). `M₀ = 2N + 3 + ⌈2/min(r,1)⌉` where `N` is the adaptation exponent of the model bound (`modelBound_of_m1`). -/
theorem exists_theta_of_m1 (hM1 : M1Prop) {p q r : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 / r = 1 / p + 1 / q) (hr' : 2 / 3 < r) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ C : ℝ, TheoremTheta p q r M C := by
  obtain ⟨N, C, hMB⟩ := modelBound_of_m1 hM1 hp hq hr hr'
  have hr0 : 0 < r := by linarith
  have hs : 0 < min r 1 := lt_min hr0 one_pos
  refine ⟨2 * N + 3 + ⌈2 / min r 1⌉₊, fun M hM => ?_⟩
  refine theta_of_modelBound hr0 ?_ hMB
  have h1 : 2 / min r 1 ≤ (⌈2 / min r 1⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((2 * N + 3 + ⌈2 / min r 1⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  push_cast at h2
  have h3 : 1 + 2 / min r 1 ≤ (M : ℝ) - 2 - 2 * N := by linarith
  calc (2 : ℝ) < (1 + 2 / min r 1) * min r 1 := by
        rw [add_mul, div_mul_cancel₀ _ hs.ne']; linarith
    _ ≤ ((M : ℝ) - 2 - 2 * N) * min r 1 := mul_le_mul_of_nonneg_right h3 hs.le

/-- **Theorem B from M1(ε)**: `exists_theta_of_m1` composed with `theoremB_of_theta_at` (R3). -/
theorem theoremB_of_m1 (hM1 : M1Prop) {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (hp : 1 < p)
    (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) (hr' : 2 / 3 < r) :
    ∃ C' : ℝ, TheoremB χ p q r C' := by
  obtain ⟨M₀, h⟩ := exists_theta_of_m1 hM1 hp hq hr hr'
  obtain ⟨C, hC⟩ := h M₀ le_rfl
  exact theoremB_of_theta_at hχ hp hq hr hr' hC

end PrimeBHT.TimeFrequency.RealLine

end
