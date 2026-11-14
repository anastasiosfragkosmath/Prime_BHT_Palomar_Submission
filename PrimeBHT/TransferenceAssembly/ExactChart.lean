module

public import PrimeBHT.TransferenceAssembly.ChartExpansion
public import PrimeBHT.TransferenceAssembly.TwistedForm

/-!
# N42 steps 2-5, summed over the chart triples (`e:exact-chart-integral`)

`T = ∑_x ∑_n K(n) w(n) f̃(x-n) g̃(x+n) conj(h̃(x))` with `f̃ = P_{ι₁,N} f` etc. (`chartProj`).
By `chartProj_eq_sum`, `f̃ = ∑_a f_a e(a·/N)`; the finite sum over `(a,b,c)` is moved out of the
double series (absolute summability: `summable_chartTerm_n`, `summable_chartTerm_x`) and each triple
is evaluated by `tsum_tsum_chartPiece_eq_exact`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate ContDiff

namespace PrimeBHT.TransferenceAssembly

open PrimeCarleson PrimeBHT.Transference

variable {N : ℕ} [NeZero N]

/-- One term of the triple-expanded double series. -/
def chartTerm (N : ℕ) (K : 𝓢(ℝ, ℂ)) (w : ℤ → ℂ) (φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ)) (a b c : ℤ)
    (x n : ℤ) : ℂ :=
  K n * w n * (φ₁ (x - n) * e (a * (x - n) / N)) *
    (φ₂ (x + n) * e (b * (x + n) / N)) * conj (φ₃ x * e (c * x / N))

omit [NeZero N] in
theorem norm_chartTerm_le (K : 𝓢(ℝ, ℂ)) {w : ℤ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C)
    (φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ)) (a b c x n : ℤ) :
    ‖chartTerm N K w φ₁ φ₂ φ₃ a b c x n‖ ≤
      ‖K n‖ * (C * (SchwartzMap.seminorm ℝ 0 0 φ₁ * SchwartzMap.seminorm ℝ 0 0 φ₂) * ‖φ₃ x‖) := by
  unfold chartTerm
  simp only [norm_mul, Complex.norm_conj, PrimeCarleson.Proof.Goal0.norm_e, mul_one]
  have h1 := SchwartzMap.norm_le_seminorm ℝ φ₁ (x - n)
  have h2 := SchwartzMap.norm_le_seminorm ℝ φ₂ (x + n)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  have := hw n
  calc ‖K n‖ * ‖w n‖ * ‖φ₁ (x - n)‖ * ‖φ₂ (x + n)‖ * ‖φ₃ x‖
      ≤ ‖K n‖ * C * SchwartzMap.seminorm ℝ 0 0 φ₁ * SchwartzMap.seminorm ℝ 0 0 φ₂ * ‖φ₃ x‖ := by
        gcongr
    _ = _ := by ring

omit [NeZero N] in
theorem summable_chartTerm_n (K : 𝓢(ℝ, ℂ)) {w : ℤ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C)
    (φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ)) (a b c x : ℤ) :
    Summable (chartTerm N K w φ₁ φ₂ φ₃ a b c x) :=
  Summable.of_norm_bounded ((summable_norm_schwartz_int K).mul_right _)
    (norm_chartTerm_le K hw φ₁ φ₂ φ₃ a b c x)

omit [NeZero N] in
theorem summable_chartTerm_x (K : 𝓢(ℝ, ℂ)) {w : ℤ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C)
    (φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ)) (a b c : ℤ) :
    Summable fun x : ℤ => ∑' n : ℤ, chartTerm N K w φ₁ φ₂ φ₃ a b c x n := by
  set D := C * (SchwartzMap.seminorm ℝ 0 0 φ₁ * SchwartzMap.seminorm ℝ 0 0 φ₂)
  refine Summable.of_norm_bounded
    (((summable_norm_schwartz_int φ₃).mul_left (D * ∑' n : ℤ, ‖K n‖))) fun x => ?_
  have hs : Summable fun n => ‖chartTerm N K w φ₁ φ₂ φ₃ a b c x n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_chartTerm_le K hw φ₁ φ₂ φ₃ a b c x)
      ((summable_norm_schwartz_int K).mul_right _)
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  refine (Summable.tsum_le_tsum (norm_chartTerm_le K hw φ₁ φ₂ φ₃ a b c x) hs
    ((summable_norm_schwartz_int K).mul_right _)).trans_eq ?_
  rw [tsum_mul_right]
  ring

/-- **`e:exact-chart-integral` (blueprint N42 steps 1-5).** For the chart projections
`f̃ = P_{ι₁,N} f`, `g̃ = P_{ι₂,N} g`, `h̃ = P_{ι₃,N} h` (`chartProj`), with
`supp χᵢ ⊆ Iᵢ = [aᵢ, bᵢ]`, `supp K̂ ⊆ [-δ, δ]`, `N δ ≤ 10⁻³`, `d` the only integer within `10⁻³`
of `I₁ - I₂`, and `v` the only integer in `I₁ + I₂ - I₃`:
`∑_x ∑_n K(n) w(n) f̃(x-n) g̃(x+n) conj(h̃(x))
  = ∑_{a,b,c ∈ Y_N} 1_{a+b-c+v ≡ 0} F_N(w)(a-b+d) ∫∫ K̂(α-β-d/N) f̂_a(α) ĝ_b(β) conj(ĥ_c(α+β-v/N))`. -/
theorem tsum_tsum_chartProj_eq_exact {χ₁ χ₂ χ₃ : ℝ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hχ₂c : HasCompactSupport χ₂)
    (hχ₃ : ContDiff ℝ ∞ χ₃) (hχ₃c : HasCompactSupport χ₃)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hI₁ : ∀ t, χ₁ t ≠ 0 → t ∈ Set.Icc a₁ b₁)
    (hI₂ : ∀ t, χ₂ t ≠ 0 → t ∈ Set.Icc a₂ b₂) (hI₃ : ∀ t, χ₃ t ≠ 0 → t ∈ Set.Icc a₃ b₃)
    {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
    (hNδ : N * δ ≤ 1 / 1000) {d v : ℤ}
    (hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
    (hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
      (v' : ℝ) = s₁ + s₂ - s₃ → v' = v)
    (f g h : ℤ →₀ ℂ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
        conj (chartProj χ₃ N h x) =
      ∑ a : ZMod N, ∑ b : ZMod N, ∑ c : ZMod N,
        if (((a.val : ℤ) + b.val - c.val + v : ℤ) : ZMod N) = 0 then
          finFourier N w (((a.val : ℤ) - b.val + d : ℤ) : ZMod N) *
            ∫ α : ℝ, ∫ β : ℝ, 𝓕 (K : ℝ → ℂ) (α - β - d / N) *
              𝓕 (⇑(chartPiece hχ₁ hχ₁c f a)) α * 𝓕 (⇑(chartPiece hχ₂ hχ₂c g b)) β *
                conj (𝓕 (⇑(chartPiece hχ₃ hχ₃c h c)) (α + β - v / N))
        else 0 := by
  have hw' := norm_le_sum_of_periodic hw
  set t : ZMod N → ZMod N → ZMod N → ℤ → ℤ → ℂ := fun a b c x n =>
    chartTerm N K w (chartPiece hχ₁ hχ₁c f a) (chartPiece hχ₂ hχ₂c g b)
      (chartPiece hχ₃ hχ₃c h c) a.val b.val c.val x n with ht
  have hsn : ∀ a b c x, Summable (t a b c x) := fun a b c x =>
    summable_chartTerm_n K hw' _ _ _ _ _ _ x
  have hsx : ∀ a b c, Summable fun x => ∑' n, t a b c x n := fun a b c =>
    summable_chartTerm_x K hw' _ _ _ _ _ _
  have hpt : ∀ x n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
      conj (chartProj χ₃ N h x) = ∑ a, ∑ b, ∑ c, t a b c x n := by
    intro x n
    rw [chartProj_eq_sum hχ₁ hχ₁c, chartProj_eq_sum hχ₂ hχ₂c, chartProj_eq_sum hχ₃ hχ₃c,
      map_sum]
    rw [show ∀ (P Q R S : ℂ), P * Q * R * S = P * (Q * R * S) from fun _ _ _ _ => by ring,
      Finset.sum_mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [ht, chartTerm]
    push_cast
    ring
  have hn : ∀ x : ℤ, ∑' n, ∑ a, ∑ b, ∑ c, t a b c x n = ∑ a, ∑ b, ∑ c, ∑' n, t a b c x n := by
    intro x
    rw [Summable.tsum_finsetSum fun a _ => summable_sum fun b _ => summable_sum fun c _ =>
      hsn a b c x]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Summable.tsum_finsetSum fun b _ => summable_sum fun c _ => hsn a b c x]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Summable.tsum_finsetSum fun c _ => hsn a b c x]
  simp_rw [hpt, hn]
  rw [Summable.tsum_finsetSum fun a _ => summable_sum fun b _ => summable_sum fun c _ =>
    hsx a b c]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Summable.tsum_finsetSum fun b _ => summable_sum fun c _ => hsx a b c]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Summable.tsum_finsetSum fun c _ => hsx a b c]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact tsum_tsum_chartPiece_eq_exact hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c hI₁ hI₂ hI₃ hw K hK hNδ hd hv
    f g h a b c

omit [NeZero N] in
theorem integrable_mul_mul_of_hasCompactSupport {F₁ F₂ : ℝ → ℂ} (h1 : HasCompactSupport F₁)
    (h2 : HasCompactSupport F₂) {G : ℝ × ℝ → ℂ}
    (hc : Continuous fun p : ℝ × ℝ => F₁ p.1 * F₂ p.2 * G p) :
    Integrable (fun p : ℝ × ℝ => F₁ p.1 * F₂ p.2 * G p) (volume.prod volume) := by
  rw [← Measure.volume_eq_prod]
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (h1.isCompact.prod h2.isCompact) fun p hp => ?_)
  by_cases hp1 : p.1 ∈ tsupport F₁
  · have hp2 : p.2 ∉ tsupport F₂ := fun hp2 => hp ⟨hp1, hp2⟩
    simp [image_eq_zero_of_notMem_tsupport hp2]
  · simp [image_eq_zero_of_notMem_tsupport hp1]

omit [NeZero N] in
theorem integral_integral_finsetSum {ι : Type*} (s : Finset ι) (P : ι → ℝ → ℝ → ℂ)
    (hP : ∀ i ∈ s, Integrable (fun p : ℝ × ℝ => P i p.1 p.2) (volume.prod volume)) :
    ∫ α, ∫ β, ∑ i ∈ s, P i α β = ∑ i ∈ s, ∫ α, ∫ β, P i α β := by
  have h1 := integral_prod (fun p : ℝ × ℝ => ∑ i ∈ s, P i p.1 p.2) (integrable_finsetSum s hP)
  simp only at h1
  rw [← h1, integral_finsetSum s hP]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact integral_prod _ (hP i hi)

theorem sum_sum_sum_comm (X : ZMod N → ZMod N → ZMod N → ℂ) :
    ∑ a, ∑ b, ∑ c, X a b c = ∑ c, ∑ b, ∑ a, X a b c := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

/-- **`e:chart-identification`, unmodulated form (N42 steps 6-7).** `T` is the double integral of
`K̂(α - β - d/N)` against the twisted form `Π_{B,d,v}` evaluated on the frequency vectors
`F̂(α;·) = ∑_a f̂_a(α) e_a`, `Ĝ(β;·) = ∑_b ĝ_b(β) e_b`, `Ĥ(α+β-v/N;·) = ∑_c ĥ_c(α+β-v/N) e_c`.
(The substitution `ξ₁ = α - d/N` turning this into `Λ_m^{Π_{B,d,v}}(F_{d,N}, G, H_{d,v,N})` is not
done here.) -/
theorem tsum_tsum_chartProj_eq_integral_twistedForm {χ₁ χ₂ χ₃ : ℝ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hχ₂c : HasCompactSupport χ₂)
    (hχ₃ : ContDiff ℝ ∞ χ₃) (hχ₃c : HasCompactSupport χ₃)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hI₁ : ∀ t, χ₁ t ≠ 0 → t ∈ Set.Icc a₁ b₁)
    (hI₂ : ∀ t, χ₂ t ≠ 0 → t ∈ Set.Icc a₂ b₂) (hI₃ : ∀ t, χ₃ t ≠ 0 → t ∈ Set.Icc a₃ b₃)
    {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
    (hNδ : N * δ ≤ 1 / 1000) {d v : ℤ}
    (hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
    (hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
      (v' : ℝ) = s₁ + s₂ - s₃ → v' = v)
    (f g h : ℤ →₀ ℂ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
        conj (chartProj χ₃ N h x) =
      ∫ α : ℝ, ∫ β : ℝ, 𝓕 (K : ℝ → ℂ) (α - β - d / N) *
        twistedForm (fun r : ZMod N => w (r.val : ℤ)) (d : ZMod N) (v : ZMod N)
          (fun y => ∑ a, 𝓕 (⇑(chartPiece hχ₁ hχ₁c f a)) α * charN a y)
          (fun y => ∑ b, 𝓕 (⇑(chartPiece hχ₂ hχ₂c g b)) β * charN b y)
          (fun y => ∑ c, 𝓕 (⇑(chartPiece hχ₃ hχ₃c h c)) (α + β - v / N) * charN c y) := by
  rw [tsum_tsum_chartProj_eq_exact hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c hI₁ hI₂ hI₃ hw K hK hNδ hd hv,
    sum_sum_sum_comm]
  simp_rw [twistedForm_sum_charN, fourierN_eq_finFourier, Finset.mul_sum]
  have hint : ∀ a b c : ZMod N, Integrable (fun p : ℝ × ℝ =>
      𝓕 (K : ℝ → ℂ) (p.1 - p.2 - d / N) * (𝓕 (⇑(chartPiece hχ₁ hχ₁c f a)) p.1 *
        𝓕 (⇑(chartPiece hχ₂ hχ₂c g b)) p.2 *
        conj (𝓕 (⇑(chartPiece hχ₃ hχ₃c h c)) (p.1 + p.2 - v / N)) *
        if a + b - c + (v : ZMod N) = 0 then finFourier N w (a - b + (d : ZMod N)) else 0))
      (volume.prod volume) := by
    intro a b c
    have := integrable_mul_mul_of_hasCompactSupport
      (hasCompactSupport_fourier_chartPiece hχ₁ hχ₁c f a)
      (hasCompactSupport_fourier_chartPiece hχ₂ hχ₂c g b)
      (G := fun p : ℝ × ℝ => 𝓕 (K : ℝ → ℂ) (p.1 - p.2 - d / N) *
        conj (𝓕 (⇑(chartPiece hχ₃ hχ₃c h c)) (p.1 + p.2 - v / N)) *
        if a + b - c + (v : ZMod N) = 0 then finFourier N w (a - b + (d : ZMod N)) else 0)
      (by
        refine Continuous.mul (Continuous.mul ((𝓕 (chartPiece hχ₁ hχ₁c f a)).continuous.comp
          continuous_fst) ((𝓕 (chartPiece hχ₂ hχ₂c g b)).continuous.comp continuous_snd))
          (Continuous.mul (Continuous.mul ((𝓕 K).continuous.comp (by fun_prop))
            (Complex.continuous_conj.comp ((𝓕 (chartPiece hχ₃ hχ₃c h c)).continuous.comp
              (by fun_prop)))) continuous_const))
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only
    ring
  rw [integral_integral_finsetSum _ _ fun c _ => integrable_finsetSum _ fun b _ =>
    integrable_finsetSum _ fun a _ => hint a b c]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_integral_finsetSum _ _ fun b _ => integrable_finsetSum _ fun a _ => hint a b c]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_integral_finsetSum _ _ fun a _ => hint a b c]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hc1 : (((a.val : ℤ) + b.val - c.val + v : ℤ) : ZMod N) = a + b - c + (v : ZMod N) := by
    push_cast; simp
  have hc2 : (((a.val : ℤ) - b.val + d : ℤ) : ZMod N) = a - b + (d : ZMod N) := by
    push_cast; simp
  rw [hc1, hc2]
  split_ifs
  · rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    simp only
    ring
  · simp

/-- **`e:chart-identification` (N42 step 7, after the substitution `ξ₁ = α - d/N`).** With
`m(t) = K̂(-t)`, `F̂_{d,N}(ξ;·) = ∑_a f̂_a(ξ + d/N) e_a`, `Ĝ(ξ;·) = ∑_b ĝ_b(ξ) e_b` and
`Ĥ_{d,v,N}(ζ;·) = ∑_c ĥ_c(ζ + (d-v)/N) e_c`:
`T = ∫∫ m(ξ₂ - ξ₁) Π_{B,d,v}(F̂_{d,N}(ξ₁), Ĝ(ξ₂), Ĥ_{d,v,N}(ξ₁ + ξ₂)) dξ₁ dξ₂`. -/
theorem tsum_tsum_chartProj_eq_integral_multiplier {χ₁ χ₂ χ₃ : ℝ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hχ₂c : HasCompactSupport χ₂)
    (hχ₃ : ContDiff ℝ ∞ χ₃) (hχ₃c : HasCompactSupport χ₃)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hI₁ : ∀ t, χ₁ t ≠ 0 → t ∈ Set.Icc a₁ b₁)
    (hI₂ : ∀ t, χ₂ t ≠ 0 → t ∈ Set.Icc a₂ b₂) (hI₃ : ∀ t, χ₃ t ≠ 0 → t ∈ Set.Icc a₃ b₃)
    {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
    (hNδ : N * δ ≤ 1 / 1000) {d v : ℤ}
    (hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
    (hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
      (v' : ℝ) = s₁ + s₂ - s₃ → v' = v)
    (f g h : ℤ →₀ ℂ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
        conj (chartProj χ₃ N h x) =
      ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ, 𝓕 (K : ℝ → ℂ) (-(ξ₂ - ξ₁)) *
        twistedForm (fun r : ZMod N => w (r.val : ℤ)) (d : ZMod N) (v : ZMod N)
          (fun y => ∑ a, 𝓕 (⇑(chartPiece hχ₁ hχ₁c f a)) (ξ₁ + d / N) * charN a y)
          (fun y => ∑ b, 𝓕 (⇑(chartPiece hχ₂ hχ₂c g b)) ξ₂ * charN b y)
          (fun y => ∑ c, 𝓕 (⇑(chartPiece hχ₃ hχ₃c h c)) (ξ₁ + ξ₂ + (d - v) / N) *
            charN c y) := by
  rw [tsum_tsum_chartProj_eq_integral_twistedForm hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c hI₁ hI₂ hI₃ hw K hK
    hNδ hd hv]
  rw [← integral_add_right_eq_self _ ((d : ℝ) / N)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
  simp only
  have h1 : ξ₁ + d / N - ξ₂ - d / N = -(ξ₂ - ξ₁) := by ring
  have h2 : ξ₁ + d / N + ξ₂ - v / N = ξ₁ + ξ₂ + (d - v) / N := by ring
  rw [h1, h2]

end PrimeBHT.TransferenceAssembly
