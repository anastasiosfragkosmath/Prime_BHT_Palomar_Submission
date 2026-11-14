module

public import PrimeBHT.TransferenceAssembly.Chart
public import PrimeBHT.Transference

/-!
# N43(a): `ℓ¹` duality and the chart expansion of `⟨H(f,g), h⟩`

* `summable_and_tsum_norm_le_of_forall_tsum_mul_conj_le`: for a finitely supported `u : ℤ → ℂ`, if
  `‖∑ₓ u x conj (h x)‖ ≤ C` for all finitely supported `h` with `‖h‖_∞ ≤ 1`, then
  `∑ₓ ‖u x‖ ≤ C`.
* `finite_support_tsum_mul`: `x ↦ ∑ₙ K n w n f(x-n) g(x+n)` is finitely supported.
* `tsum_mul_conj_eq_sum_chartTriple_of_partition`: the chart expansion
  `∑ₓ H(f,g)(x) conj h(x) = ∑_{ι₁ι₂ι₃} T_{ι₁ι₂ι₃}`, given the partition identity `hpart`.
* `summable_and_tsum_norm_le_of_chart_bounds`: the reduction `‖H(f,g)‖_{ℓ¹} ≤ n_ch³ C₀`.
-/

public section

namespace PrimeBHT.TransferenceAssembly

open scoped ComplexConjugate ContDiff SchwartzMap

open PrimeBHT.Transference PrimeCarleson

/-! ## `ℓ¹` duality -/

/-- **`ℓ¹` duality for finitely supported sequences** (test sequences `h x = u x / ‖u x‖`). -/
theorem summable_and_tsum_norm_le_of_forall_tsum_mul_conj_le {u : ℤ → ℂ}
    (hu : (Function.support u).Finite) {C : ℝ}
    (hC : ∀ h : ℤ →₀ ℂ, (∀ x, ‖h x‖ ≤ 1) → ‖∑' x, u x * conj (h x)‖ ≤ C) :
    Summable (fun x => ‖u x‖) ∧ ∑' x, ‖u x‖ ≤ C := by
  have hs : Summable (fun x => ‖u x‖) :=
    summable_of_ne_finset_zero (s := hu.toFinset) fun x hx => by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
      simp [hx]
  refine ⟨hs, ?_⟩
  let v : ℤ → ℂ := fun x => u x / ((‖u x‖ : ℝ) : ℂ)
  have hv : (Function.support v).Finite :=
    hu.subset fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [v, h0])
  let h : ℤ →₀ ℂ := Finsupp.ofSupportFinite v hv
  have hh : ∀ x, h x = v x := fun x => rfl
  have hnorm : ∀ x, ‖h x‖ ≤ 1 := by
    intro x
    rw [hh]
    by_cases hx : u x = 0
    · simp [v, hx]
    · have hpos : 0 < ‖u x‖ := norm_pos_iff.2 hx
      simp only [v, norm_div, Complex.norm_real, norm_norm]
      rw [div_self hpos.ne']
  have hpt : ∀ x, u x * conj (h x) = ((‖u x‖ : ℝ) : ℂ) := by
    intro x
    rw [hh]
    by_cases hx : u x = 0
    · simp [v, hx]
    · have hne : ((‖u x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hx).ne'
      simp only [v, map_div₀, Complex.conj_ofReal]
      rw [← mul_div_assoc, Complex.mul_conj', div_eq_iff hne]
      ring
  have := hC h hnorm
  simp_rw [hpt] at this
  rw [← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)] at this
  exact this

/-! ## Finite support -/

/-- If `f` and `g` are finitely supported then so is `x ↦ ∑ₙ K n w n f(x-n) g(x+n)`: a nonzero
term forces `2x = (x - n) + (x + n) ∈ supp f + supp g`. -/
theorem finite_support_tsum_mul {K w f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) :
    (Function.support fun x : ℤ => ∑' n : ℤ, K n * w n * f (x - n) * g (x + n)).Finite := by
  have hfin : (Set.image2 (· + ·) (Function.support f) (Function.support g)).Finite :=
    hf.image2 _ hg
  have hinj : Function.Injective fun x : ℤ => 2 * x := fun a b h => by simpa using h
  refine (hfin.preimage hinj.injOn).subset fun x hx => ?_
  rw [Function.mem_support] at hx
  by_contra hmem
  apply hx
  have hz : ∀ n : ℤ, K n * w n * f (x - n) * g (x + n) = 0 := by
    intro n
    by_contra hn
    apply hmem
    have h1 : f (x - n) ≠ 0 := fun h0 => hn (by simp [h0])
    have h2 : g (x + n) ≠ 0 := fun h0 => hn (by simp [h0])
    exact Set.mem_image2.2 ⟨x - n, h1, x + n, h2, by simp only; ring⟩
  simp only [hz, tsum_zero]

/-! ## Absolute summability -/

/-- `chartProj χ N h` is absolutely summable over `ℤ` (a finite sum of translates of Schwartz
functions, `chartProj_eq_sum`). -/
theorem summable_norm_chartProj {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {N : ℕ} [NeZero N] (h : ℤ →₀ ℂ) : Summable fun m : ℤ => ‖chartProj χ N h m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_sum (s := (Finset.univ : Finset (ZMod N))) fun A _ =>
      summable_norm_schwartz_int (chartPiece hχ hχc h A))
  rw [chartProj_eq_sum (N := N) hχ hχc h m]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)
  rw [norm_mul, PrimeCarleson.Proof.Goal0.norm_e, mul_one]

theorem norm_le_tsum_norm_of_summable {F : ℤ → ℂ} (hF : Summable fun m => ‖F m‖) (m : ℤ) :
    ‖F m‖ ≤ ∑' k, ‖F k‖ :=
  hF.le_tsum m fun _ _ => norm_nonneg _

/-- Summability of the `n`-series and of the `x`-series of `∑ₙ K n w n F(x-n) G(x+n) conj H(x)`,
for bounded `F, G` and `ℓ¹` `H`. -/
theorem summable_tsum_mul_mul_conj {K w F G H : ℤ → ℂ} {W M₁ M₂ : ℝ}
    (hK : Summable fun n => ‖K n‖) (hw : ∀ n, ‖w n‖ ≤ W)
    (hF : ∀ x, ‖F x‖ ≤ M₁) (hG : ∀ x, ‖G x‖ ≤ M₂) (hH : Summable fun x => ‖H x‖) :
    (∀ x, Summable fun n => K n * w n * F (x - n) * G (x + n) * conj (H x)) ∧
      Summable fun x => ∑' n, K n * w n * F (x - n) * G (x + n) * conj (H x) := by
  have hbd : ∀ x n, ‖K n * w n * F (x - n) * G (x + n) * conj (H x)‖ ≤
      ‖K n‖ * (W * M₁ * M₂ * ‖H x‖) := by
    intro x n
    simp only [norm_mul, Complex.norm_conj]
    have h0 : 0 ≤ ‖w n‖ := norm_nonneg _
    have h1 := hw n
    have h2 := hF (x - n)
    have h3 := hG (x + n)
    have hW : 0 ≤ W := h0.trans h1
    have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans h2
    calc ‖K n‖ * ‖w n‖ * ‖F (x - n)‖ * ‖G (x + n)‖ * ‖H x‖
        ≤ ‖K n‖ * W * M₁ * M₂ * ‖H x‖ := by gcongr
      _ = _ := by ring
  have hsn : ∀ x, Summable fun n => ‖K n * w n * F (x - n) * G (x + n) * conj (H x)‖ := fun x =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbd x) (hK.mul_right _)
  refine ⟨fun x => (hsn x).of_norm, ?_⟩
  refine Summable.of_norm_bounded (hH.mul_left ((∑' n, ‖K n‖) * (W * M₁ * M₂))) fun x => ?_
  refine (norm_tsum_le_tsum_norm (hsn x)).trans ?_
  refine ((hsn x).tsum_le_tsum (hbd x) (hK.mul_right _)).trans_eq ?_
  rw [tsum_mul_right]
  ring

/-! ## Chart expansion -/

/-- Exchange of the finite triple sum with the `tsum`. -/
theorem tsum_sum_sum_sum {ι β : Type*} [Fintype ι] {a : ι → ι → ι → β → ℂ}
    (ha : ∀ i j k, Summable (a i j k)) :
    ∑' b, ∑ i, ∑ j, ∑ k, a i j k b = ∑ i, ∑ j, ∑ k, ∑' b, a i j k b := by
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => summable_sum fun k _ => ha i j k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ => summable_sum fun k _ => ha i j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum fun k _ => ha i j k]

theorem mul_sum_mul_sum_mul_conj_sum {ι : Type*} [Fintype ι] (c : ℂ) (F G H : ι → ℂ) :
    c * (∑ i, F i) * (∑ j, G j) * conj (∑ k, H k) =
      ∑ i, ∑ j, ∑ k, c * F i * G j * conj (H k) := by
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

/-- The chart expansion in an abstract form: finite decompositions `F = ∑ᵢ Fᵢ`, `G = ∑ⱼ Gⱼ`,
`H = ∑ₖ Hₖ` into bounded (resp. `ℓ¹`) pieces. -/
theorem tsum_tsum_sum_eq_sum_sum_sum {ι : Type*} [Fintype ι] {K w : ℤ → ℂ} {W M₁ M₂ : ℝ}
    (hK : Summable fun n => ‖K n‖) (hw : ∀ n, ‖w n‖ ≤ W) (F G H : ι → ℤ → ℂ)
    (hF : ∀ i x, ‖F i x‖ ≤ M₁) (hG : ∀ i x, ‖G i x‖ ≤ M₂)
    (hH : ∀ i, Summable fun x => ‖H i x‖) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * (∑ i, F i (x - n)) * (∑ j, G j (x + n)) *
        conj (∑ k, H k x) =
      ∑ i, ∑ j, ∑ k, ∑' x : ℤ, ∑' n : ℤ,
        K n * w n * F i (x - n) * G j (x + n) * conj (H k x) := by
  have hs := fun i j k => summable_tsum_mul_mul_conj hK hw (hF i) (hG j) (hH k)
  simp_rw [mul_sum_mul_sum_mul_conj_sum]
  have hn : ∀ x : ℤ, ∑' n : ℤ, ∑ i, ∑ j, ∑ k,
      K n * w n * F i (x - n) * G j (x + n) * conj (H k x) =
      ∑ i, ∑ j, ∑ k, ∑' n : ℤ, K n * w n * F i (x - n) * G j (x + n) * conj (H k x) :=
    fun x => tsum_sum_sum_sum fun i j k => (hs i j k).1 x
  simp_rw [hn]
  exact tsum_sum_sum_sum fun i j k => (hs i j k).2

/-- **Chart expansion of `⟨H(f,g), h⟩` (N43(a), step 1), conditional on the partition identity.**
For a partition identity `hpart` (`∑_ι P_{ι,N} h = h` for every finitely supported `h`),
`∑ₓ H(f,g)(x) conj h(x) = ∑_{ι₁ι₂ι₃} T_{ι₁ι₂ι₃}`, with
`T_{ι₁ι₂ι₃} = ∑ₓ ∑ₙ K(n) w(n) f̃(x-n) g̃(x+n) conj h̃(x)`, `f̃ = P_{ι₁,N} f` etc.
All the double series are absolutely summable (`chartProj` is `ℓ¹`, in particular bounded). -/
theorem tsum_mul_conj_eq_sum_chartTriple_of_partition {nch : ℕ} {χ : Fin nch → ℝ → ℂ}
    (hχ : ∀ ι, ContDiff ℝ ∞ (χ ι)) (hχc : ∀ ι, HasCompactSupport (χ ι))
    (hpart : ∀ (N : ℕ) [NeZero N] (h : ℤ →₀ ℂ) (m : ℤ), ∑ ι, chartProj (χ ι) N h m = h m)
    (N : ℕ) [NeZero N] (K : 𝓢(ℝ, ℂ)) {w : ℤ → ℂ} {W : ℝ} (hw : ∀ n, ‖w n‖ ≤ W)
    (f g h : ℤ →₀ ℂ) :
    ∑' x : ℤ, (∑' n : ℤ, K n * w n * f (x - n) * g (x + n)) * conj (h x) =
      ∑ ι₁, ∑ ι₂, ∑ ι₃, ∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj (χ ι₁) N f (x - n) *
        chartProj (χ ι₂) N g (x + n) * conj (chartProj (χ ι₃) N h x) := by
  have hbd : ∀ (u : ℤ →₀ ℂ) (i : Fin nch) (x : ℤ),
      ‖chartProj (χ i) N u x‖ ≤ ∑ j, ∑' m : ℤ, ‖chartProj (χ j) N u m‖ := by
    intro u i x
    refine (norm_le_tsum_norm_of_summable (summable_norm_chartProj (hχ i) (hχc i) u) x).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑' m : ℤ, ‖chartProj (χ j) N u m‖)
      (fun j _ => tsum_nonneg fun _ => norm_nonneg _) (Finset.mem_univ i)
  have key := tsum_tsum_sum_eq_sum_sum_sum (K := fun n : ℤ => K n) (w := w)
    (summable_norm_schwartz_int K) hw (fun ι => chartProj (χ ι) N f)
    (fun ι => chartProj (χ ι) N g) (fun ι => chartProj (χ ι) N h) (hbd f) (hbd g)
    (fun i => summable_norm_chartProj (hχ i) (hχc i) h)
  rw [← key]
  refine tsum_congr fun x => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [hpart N f, hpart N g, hpart N h]

/-- **Reduction to the chart triples (N43(a), step 1).** If each chart-triple quantity
`T_{ι₁ι₂ι₃}(f,g,h)` is bounded by `C₀` for all finitely supported `h` with `‖h‖_∞ ≤ 1`, then
`H(f,g) = (x ↦ ∑ₙ K(n) w(n) f(x-n) g(x+n))` satisfies `‖H(f,g)‖_{ℓ¹} ≤ n_ch³ C₀`. -/
theorem summable_and_tsum_norm_le_of_chart_bounds {nch : ℕ} {χ : Fin nch → ℝ → ℂ}
    (hχ : ∀ ι, ContDiff ℝ ∞ (χ ι)) (hχc : ∀ ι, HasCompactSupport (χ ι))
    (hpart : ∀ (N : ℕ) [NeZero N] (h : ℤ →₀ ℂ) (m : ℤ), ∑ ι, chartProj (χ ι) N h m = h m)
    (N : ℕ) [NeZero N] (K : 𝓢(ℝ, ℂ)) {w : ℤ → ℂ} {W : ℝ} (hw : ∀ n, ‖w n‖ ≤ W)
    (f g : ℤ →₀ ℂ) {C₀ : ℝ}
    (hT : ∀ h : ℤ →₀ ℂ, (∀ x, ‖h x‖ ≤ 1) → ∀ ι₁ ι₂ ι₃ : Fin nch,
      ‖∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj (χ ι₁) N f (x - n) *
        chartProj (χ ι₂) N g (x + n) * conj (chartProj (χ ι₃) N h x)‖ ≤ C₀) :
    Summable (fun x : ℤ => ‖∑' n : ℤ, K n * w n * f (x - n) * g (x + n)‖) ∧
      ∑' x : ℤ, ‖∑' n : ℤ, K n * w n * f (x - n) * g (x + n)‖ ≤ (nch : ℝ) ^ 3 * C₀ := by
  refine summable_and_tsum_norm_le_of_forall_tsum_mul_conj_le
    (finite_support_tsum_mul (K := fun n : ℤ => K n) (w := w) (f := ⇑f) (g := ⇑g)
      (by rw [Finsupp.fun_support_eq]; exact f.support.finite_toSet)
      (by rw [Finsupp.fun_support_eq]; exact g.support.finite_toSet)) ?_
  intro h hh
  rw [tsum_mul_conj_eq_sum_chartTriple_of_partition hχ hχc hpart N K hw f g h]
  calc _ ≤ ∑ ι₁ : Fin nch, ∑ ι₂ : Fin nch, ∑ ι₃ : Fin nch,
        ‖∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj (χ ι₁) N f (x - n) *
          chartProj (χ ι₂) N g (x + n) * conj (chartProj (χ ι₃) N h x)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ ι₁ : Fin nch, ∑ ι₂ : Fin nch, ∑ ι₃ : Fin nch, C₀ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => hT h hh i j k
    _ = (nch : ℝ) ^ 3 * C₀ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `summable_and_tsum_norm_le_of_chart_bounds` for finitely supported functions `f g : ℤ → ℂ`
(as in `hOp`), via `Finsupp.ofSupportFinite`. -/
theorem summable_and_tsum_norm_le_of_chart_bounds_of_finite_support {nch : ℕ}
    {χ : Fin nch → ℝ → ℂ}
    (hχ : ∀ ι, ContDiff ℝ ∞ (χ ι)) (hχc : ∀ ι, HasCompactSupport (χ ι))
    (hpart : ∀ (N : ℕ) [NeZero N] (h : ℤ →₀ ℂ) (m : ℤ), ∑ ι, chartProj (χ ι) N h m = h m)
    (N : ℕ) [NeZero N] (K : 𝓢(ℝ, ℂ)) {w : ℤ → ℂ} {W : ℝ} (hw : ∀ n, ‖w n‖ ≤ W)
    {f g : ℤ → ℂ} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) {C₀ : ℝ}
    (hT : ∀ h : ℤ →₀ ℂ, (∀ x, ‖h x‖ ≤ 1) → ∀ ι₁ ι₂ ι₃ : Fin nch,
      ‖∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj (χ ι₁) N (Finsupp.ofSupportFinite f hf) (x - n) *
        chartProj (χ ι₂) N (Finsupp.ofSupportFinite g hg) (x + n) *
          conj (chartProj (χ ι₃) N h x)‖ ≤ C₀) :
    Summable (fun x : ℤ => ‖∑' n : ℤ, K n * w n * f (x - n) * g (x + n)‖) ∧
      ∑' x : ℤ, ‖∑' n : ℤ, K n * w n * f (x - n) * g (x + n)‖ ≤ (nch : ℝ) ^ 3 * C₀ :=
  summable_and_tsum_norm_le_of_chart_bounds hχ hχc hpart N K hw
    (Finsupp.ofSupportFinite f hf) (Finsupp.ofSupportFinite g hg) hT

end PrimeBHT.TransferenceAssembly
