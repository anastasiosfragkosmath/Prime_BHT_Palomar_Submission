module

public import PrimeBHT.Transference
public import PrimeBHT.TransferenceAssembly.Chart

/-!
# N42 step 2 for one chart triple (`e:chart-expanded`, termwise in `(a, b, c)`)

For Schwartz `φ₁, φ₂, φ₃` with compactly supported Fourier transforms (e.g. the chart pieces
`f_a, g_b, h_c`), an `N`-periodic weight `w` (e.g. `Λ_B`), a Schwartz kernel `K` and integers
`a, b, c`:
`∑_x ∑_n K(n) w(n) [φ₁(x-n) e(a(x-n)/N)] [φ₂(x+n) e(b(x+n)/N)] conj(φ₃(x) e(cx/N))
  = ∑_k ∫∫ φ̂₁(α) φ̂₂(β) conj(φ̂₃(α + β + (a+b-c)/N - k)) M_w((a-b)/N + α - β) dα dβ`,
with `M_w(θ) = ∑_n K(n) w(n) e(-nθ)` (`Transference.multiplier`). This is blueprint N42 step 2
before the sum over `(a, b, c)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace PrimeBHT.TransferenceAssembly

open PrimeCarleson PrimeBHT.Transference

theorem conj_e (t : ℝ) : conj (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem e_add' (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem e_intCast' (k : ℤ) : e k = 1 := by
  unfold e
  have : (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) = k * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

variable {N : ℕ} [NeZero N]

/-- The modulated weight `w(n) e(n(b-a)/N)` is again `N`-periodic. -/
theorem periodic_mul_e {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ)) (a b : ℤ) :
    Function.Periodic (fun n : ℤ => w n * e (n * (b - a) / N)) (N : ℤ) := by
  intro n
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  simp only [hw n]
  have : ((n + N : ℤ) : ℝ) * (b - a) / N = n * (b - a) / N + ((b - a : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [this, e_add', e_intCast', mul_one]

omit [NeZero N] in
/-- `M_{w e((b-a)·/N)}(θ) = M_w(θ + (a-b)/N)`. -/
theorem multiplier_mul_e (K : 𝓢(ℝ, ℂ)) (w : ℤ → ℂ) (a b : ℤ) (θ : ℝ) :
    multiplier K (fun n : ℤ => w n * e (n * (b - a) / N)) θ =
      multiplier K w ((a - b) / N + θ) := by
  unfold multiplier
  refine tsum_congr fun n => ?_
  have : -((n : ℝ) * ((a - b) / N + θ)) = n * (b - a) / N + -((n : ℝ) * θ) := by ring
  rw [this, e_add']
  ring

/-- **N42 step 2 (`e:chart-expanded`) for one chart triple `(a, b, c)`.** -/
theorem tsum_tsum_chart_eq {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (K φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ))
    (h₁ : HasCompactSupport (𝓕 (φ₁ : ℝ → ℂ))) (h₂ : HasCompactSupport (𝓕 (φ₂ : ℝ → ℂ)))
    (h₃ : HasCompactSupport (𝓕 (φ₃ : ℝ → ℂ))) (a b c : ℤ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * (φ₁ (x - n) * e (a * (x - n) / N)) *
        (φ₂ (x + n) * e (b * (x + n) / N)) * conj (φ₃ x * e (c * x / N)) =
      ∑' k : ℤ, ∫ α : ℝ, ∫ β : ℝ, 𝓕 (φ₁ : ℝ → ℂ) α * 𝓕 (φ₂ : ℝ → ℂ) β *
        conj (𝓕 (φ₃ : ℝ → ℂ) (α + β + (a + b - c) / N - k)) *
          multiplier K w ((a - b) / N + (α - β)) := by
  have hmain := tsum_tsum_eq_tsum_integral_integral_periodic (periodic_mul_e hw a b) K φ₁ φ₂ φ₃
    h₁ h₂ h₃ ((a + b - c) / N)
  simp only [multiplier_mul_e] at hmain
  rw [← hmain]
  refine tsum_congr fun x => tsum_congr fun n => ?_
  rw [map_mul, conj_e]
  have hexp : e (a * (x - n) / N) * e (b * (x + n) / N) * e (-(c * x / N)) =
      e (n * (b - a) / N) * e (x * ((a + b - c) / N)) := by
    rw [← e_add', ← e_add', ← e_add']
    congr 1
    ring
  calc _ = K n * w n * φ₁ (x - n) * φ₂ (x + n) * conj (φ₃ x) *
        (e (a * (x - n) / N) * e (b * (x + n) / N) * e (-(c * x / N))) := by ring
    _ = _ := by rw [hexp]; ring

/-- Integer identity behind the alias: if `ℓ.val + j N = m` then `ℓ = m mod N` and `j = m / N`. -/
theorem alias_int_eq {ℓ : ZMod N} {j m : ℤ} (h : (ℓ.val : ℤ) + j * N = m) :
    ℓ = (m : ZMod N) ∧ j = m / N := by
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (NeZero.ne N)
  constructor
  · rw [← h]; push_cast; simp
  · rw [← h, mul_comm, Int.add_mul_ediv_left _ _ hN, Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _)
      (Int.ofNat_lt.2 (ZMod.val_lt ℓ)), zero_add]

/-- **N42 steps 3-4 (`e:one-alias`), pointwise form.** If `supp K̂ ⊆ [-δ, δ]`, `N δ ≤ 10⁻³`, and
`d` is the only integer within `10⁻³` of `N(α - β)`, then
`M_w((a-b)/N + α - β) = F_N(w)(a - b + d) K̂(α - β - d/N)`. -/
theorem multiplier_eq_one_alias {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ)) (K : 𝓢(ℝ, ℂ))
    {δ : ℝ} (hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0) (hNδ : N * δ ≤ 1 / 1000)
    {a b d : ℤ} {α β : ℝ} (hd : ∀ d' : ℤ, |N * (α - β) - d'| ≤ 1 / 1000 → d' = d) :
    multiplier K w ((a - b) / N + (α - β)) =
      finFourier N w ((a - b + d : ℤ) : ZMod N) * 𝓕 (K : ℝ → ℂ) (α - β - d / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold multiplier
  rw [tsum_kernel_mul_weight_mul_e_eq hw K]
  -- a nonzero term forces the alias equation
  have key : ∀ (ℓ : ZMod N) (j : ℤ),
      𝓕 (K : ℝ → ℂ) ((a - b) / N + (α - β) - (ℓ.val : ℝ) / N - j) ≠ 0 →
        (ℓ.val : ℤ) + j * N = a - b + d := by
    intro ℓ j hne
    have hle : |(a - b) / N + (α - β) - (ℓ.val : ℝ) / N - j| ≤ δ := by
      by_contra hlt; exact hne (hK _ (not_le.1 hlt))
    have hd' := hd ((ℓ.val : ℤ) - a + b + j * N) ?_
    · linarith
    · have hrw : (N : ℝ) * (α - β) - (((ℓ.val : ℤ) - a + b + j * N : ℤ) : ℝ) =
          N * ((a - b) / N + (α - β) - (ℓ.val : ℝ) / N - j) := by
        push_cast; field_simp; ring
      rw [hrw, abs_mul, abs_of_pos hNpos]
      nlinarith [abs_nonneg ((a - b) / N + (α - β) - (ℓ.val : ℝ) / N - j)]
  rw [Finset.sum_eq_single ((a - b + d : ℤ) : ZMod N)]
  · congr 1
    set ℓ₀ : ZMod N := ((a - b + d : ℤ) : ZMod N)
    rw [tsum_eq_single ((a - b + d) / N)]
    · have h0 : (ℓ₀.val : ℤ) + (a - b + d) / N * N = a - b + d := by
        simp only [ℓ₀, ZMod.val_intCast]
        exact Int.emod_add_ediv_mul _ _
      have h0' : (ℓ₀.val : ℝ) = a - b + d - (((a - b + d) / N : ℤ) : ℝ) * N := by
        have := congrArg (fun z : ℤ => (z : ℝ)) h0
        push_cast at this ⊢; linarith
      rw [h0']
      have hN : (N : ℝ) ≠ 0 := hNpos.ne'
      exact congrArg (𝓕 (K : ℝ → ℂ)) (by field_simp; ring)
    · intro j hj
      by_contra hne
      exact hj (alias_int_eq (key ℓ₀ j hne)).2
  · intro ℓ _ hℓ
    have hz : (fun j : ℤ => 𝓕 (K : ℝ → ℂ) ((a - b) / N + (α - β) - (ℓ.val : ℝ) / N - j)) =
        fun _ => 0 := by
      funext j
      by_contra hne
      exact hℓ (alias_int_eq (key ℓ j hne)).1
    rw [hz, tsum_zero, mul_zero]
  · simp

/-- **N42 step 5 (output alias).** Let `F₁, F₂, F₃` vanish unless `N·(argument)` lies in
`I₁ = [a₁,b₁]`, `I₂`, `I₃` respectively, and let `v` be the only integer of the form
`s₁ + s₂ - s₃` with `sᵢ ∈ Iᵢ`. Then the `k`-sum collapses:
`∑_k ∫∫ F₁(α) F₂(β) conj(F₃(α+β+(a+b-c)/N - k)) G(α,β)
  = 1_{a+b-c+v ≡ 0 (N)} ∫∫ F₁(α) F₂(β) conj(F₃(α+β-v/N)) G(α,β)`. -/
theorem tsum_integral_output_alias {F₁ F₂ F₃ : ℝ → ℂ} (G : ℝ → ℝ → ℂ)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hF₁ : ∀ α, F₁ α ≠ 0 → (N : ℝ) * α ∈ Set.Icc a₁ b₁)
    (hF₂ : ∀ β, F₂ β ≠ 0 → (N : ℝ) * β ∈ Set.Icc a₂ b₂)
    (hF₃ : ∀ ζ, F₃ ζ ≠ 0 → (N : ℝ) * ζ ∈ Set.Icc a₃ b₃)
    {v : ℤ} (hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
      (v' : ℝ) = s₁ + s₂ - s₃ → v' = v) (a b c : ℤ) :
    ∑' k : ℤ, ∫ α : ℝ, ∫ β : ℝ, F₁ α * F₂ β * conj (F₃ (α + β + (a + b - c) / N - k)) * G α β =
      if ((a + b - c + v : ℤ) : ZMod N) = 0 then
        ∫ α : ℝ, ∫ β : ℝ, F₁ α * F₂ β * conj (F₃ (α + β - v / N)) * G α β
      else 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (N : ℝ) ≠ 0 := hNpos.ne'
  -- a nonzero integrand forces `k N = a + b - c + v`
  have key : ∀ (k : ℤ) (α β : ℝ),
      F₁ α * F₂ β * conj (F₃ (α + β + (a + b - c) / N - k)) * G α β ≠ 0 →
        k * (N : ℤ) = a + b - c + v := by
    intro k α β hne
    have h1 : F₁ α ≠ 0 := fun h => hne (by simp [h])
    have h2 : F₂ β ≠ 0 := fun h => hne (by simp [h])
    have h3 : F₃ (α + β + (a + b - c) / N - k) ≠ 0 := fun h => hne (by simp [h])
    have := hv (k * N - a - b + c) _ (hF₁ α h1) _ (hF₂ β h2) _ (hF₃ _ h3) (by
      push_cast; field_simp; ring)
    linarith
  have hzero : ∀ k : ℤ, k * (N : ℤ) ≠ a + b - c + v →
      (∫ α : ℝ, ∫ β : ℝ, F₁ α * F₂ β * conj (F₃ (α + β + (a + b - c) / N - k)) * G α β) = 0 := by
    intro k hk
    have : (fun α : ℝ => ∫ β : ℝ, F₁ α * F₂ β * conj (F₃ (α + β + (a + b - c) / N - k)) * G α β)
        = fun _ => 0 := by
      funext α
      have : (fun β : ℝ => F₁ α * F₂ β * conj (F₃ (α + β + (a + b - c) / N - k)) * G α β)
          = fun _ => 0 := by
        funext β
        by_contra hne
        exact hk (key k α β hne)
      rw [this, integral_zero]
    rw [this, integral_zero]
  split_ifs with hdiv
  · obtain ⟨k₀, hk₀⟩ : (N : ℤ) ∣ a + b - c + v :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hdiv
    rw [tsum_eq_single k₀]
    · have harg : ∀ α β : ℝ, α + β + (a + b - c) / N - k₀ = α + β - v / N := by
        intro α β
        have : ((a + b - c + v : ℤ) : ℝ) = N * k₀ := by exact_mod_cast hk₀
        push_cast at this
        field_simp
        linarith
      simp only [harg]
    · intro k hk
      apply hzero k
      intro h
      apply hk
      have : (N : ℤ) * k = N * k₀ := by linarith
      exact mul_left_cancel₀ (Int.natCast_ne_zero.2 (NeZero.ne N)) this
  · have : (fun k : ℤ => ∫ α : ℝ, ∫ β : ℝ,
        F₁ α * F₂ β * conj (F₃ (α + β + (a + b - c) / N - k)) * G α β) = fun _ => 0 := by
      funext k
      apply hzero k
      intro h
      apply hdiv
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨k, by linarith⟩
    rw [this, tsum_zero]

/-- **N42 steps 2-5 for one chart triple (`e:exact-chart-integral`, termwise).** With
`supp K̂ ⊆ [-δ, δ]`, `N δ ≤ 10⁻³`, `N·supp φ̂ᵢ ⊆ Iᵢ`, `d` the only integer within `10⁻³` of
`I₁ - I₂` and `v` the only integer in `I₁ + I₂ - I₃`:
`∑_x ∑_n K(n) w(n) [φ₁(x-n) e(a(x-n)/N)] [φ₂(x+n) e(b(x+n)/N)] conj(φ₃(x) e(cx/N))
  = 1_{a+b-c+v ≡ 0 (N)} F_N(w)(a-b+d) ∫∫ K̂(α-β-d/N) φ̂₁(α) φ̂₂(β) conj(φ̂₃(α+β-v/N))`. -/
theorem tsum_tsum_chart_eq_exact {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (K φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ)) {δ : ℝ} (hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
    (hNδ : N * δ ≤ 1 / 1000)
    (h₁ : HasCompactSupport (𝓕 (φ₁ : ℝ → ℂ))) (h₂ : HasCompactSupport (𝓕 (φ₂ : ℝ → ℂ)))
    (h₃ : HasCompactSupport (𝓕 (φ₃ : ℝ → ℂ)))
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ}
    (hF₁ : ∀ α, 𝓕 (φ₁ : ℝ → ℂ) α ≠ 0 → (N : ℝ) * α ∈ Set.Icc a₁ b₁)
    (hF₂ : ∀ β, 𝓕 (φ₂ : ℝ → ℂ) β ≠ 0 → (N : ℝ) * β ∈ Set.Icc a₂ b₂)
    (hF₃ : ∀ ζ, 𝓕 (φ₃ : ℝ → ℂ) ζ ≠ 0 → (N : ℝ) * ζ ∈ Set.Icc a₃ b₃)
    {d v : ℤ}
    (hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
    (hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
      (v' : ℝ) = s₁ + s₂ - s₃ → v' = v) (a b c : ℤ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * (φ₁ (x - n) * e (a * (x - n) / N)) *
        (φ₂ (x + n) * e (b * (x + n) / N)) * conj (φ₃ x * e (c * x / N)) =
      if ((a + b - c + v : ℤ) : ZMod N) = 0 then
        finFourier N w ((a - b + d : ℤ) : ZMod N) *
          ∫ α : ℝ, ∫ β : ℝ, 𝓕 (K : ℝ → ℂ) (α - β - d / N) * 𝓕 (φ₁ : ℝ → ℂ) α *
            𝓕 (φ₂ : ℝ → ℂ) β * conj (𝓕 (φ₃ : ℝ → ℂ) (α + β - v / N))
      else 0 := by
  rw [tsum_tsum_chart_eq hw K φ₁ φ₂ φ₃ h₁ h₂ h₃ a b c,
    tsum_integral_output_alias (fun α β => multiplier K w ((a - b) / N + (α - β))) hF₁ hF₂ hF₃ hv]
  split_ifs
  · rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    simp only
    by_cases h0 : 𝓕 (φ₁ : ℝ → ℂ) α = 0 ∨ 𝓕 (φ₂ : ℝ → ℂ) β = 0
    · rcases h0 with h0 | h0 <;> simp [h0]
    · push Not at h0
      have hd' : ∀ d' : ℤ, |(N : ℝ) * (α - β) - d'| ≤ 1 / 1000 → d' = d := by
        intro d' hd'
        refine hd d' _ (hF₁ α h0.1) _ (hF₂ β h0.2) ?_
        rwa [mul_sub] at hd'
      rw [multiplier_eq_one_alias hw K hK hNδ hd']
      ring
  · rfl

section ChartPieces

open scoped ContDiff

variable {χ : ℝ → ℂ}

/-- The chart pieces have `N · supp ĥ_A ⊆ I` when `supp χ ⊆ I`. -/
theorem mem_Icc_of_fourier_chartPiece_ne_zero (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {a₀ b₀ : ℝ} (hI : ∀ t, χ t ≠ 0 → t ∈ Set.Icc a₀ b₀) (h : ℤ →₀ ℂ) (A : ZMod N) (α : ℝ)
    (hne : 𝓕 (⇑(chartPiece hχ hχc h A)) α ≠ 0) : (N : ℝ) * α ∈ Set.Icc a₀ b₀ := by
  rw [fourier_chartPiece] at hne
  refine hI _ fun h0 => hne ?_
  simp [chartCoeffHat, h0]

theorem hasCompactSupport_fourier_chartPiece (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (h : ℤ →₀ ℂ) (A : ZMod N) : HasCompactSupport (𝓕 (⇑(chartPiece hχ hχc h A))) := by
  rw [fourier_chartPiece]
  exact hasCompactSupport_chartCoeffHat hχc h A

/-- **N42 steps 2-5 for the chart pieces `f_a, g_b, h_c` (one triple `(a,b,c) ∈ Y_N³`).** -/
theorem tsum_tsum_chartPiece_eq_exact {χ₁ χ₂ χ₃ : ℝ → ℂ}
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
    (f g h : ℤ →₀ ℂ) (a b c : ZMod N) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n *
        (chartPiece hχ₁ hχ₁c f a (x - n) * e ((a.val : ℤ) * (x - n) / N)) *
        (chartPiece hχ₂ hχ₂c g b (x + n) * e ((b.val : ℤ) * (x + n) / N)) *
        conj (chartPiece hχ₃ hχ₃c h c x * e ((c.val : ℤ) * x / N)) =
      if (((a.val : ℤ) + b.val - c.val + v : ℤ) : ZMod N) = 0 then
        finFourier N w (((a.val : ℤ) - b.val + d : ℤ) : ZMod N) *
          ∫ α : ℝ, ∫ β : ℝ, 𝓕 (K : ℝ → ℂ) (α - β - d / N) *
            𝓕 (⇑(chartPiece hχ₁ hχ₁c f a)) α * 𝓕 (⇑(chartPiece hχ₂ hχ₂c g b)) β *
              conj (𝓕 (⇑(chartPiece hχ₃ hχ₃c h c)) (α + β - v / N))
      else 0 :=
  tsum_tsum_chart_eq_exact hw K _ _ _ hK hNδ
    (hasCompactSupport_fourier_chartPiece hχ₁ hχ₁c f a)
    (hasCompactSupport_fourier_chartPiece hχ₂ hχ₂c g b)
    (hasCompactSupport_fourier_chartPiece hχ₃ hχ₃c h c)
    (mem_Icc_of_fourier_chartPiece_ne_zero hχ₁ hχ₁c hI₁ f a)
    (mem_Icc_of_fourier_chartPiece_ne_zero hχ₂ hχ₂c hI₂ g b)
    (mem_Icc_of_fourier_chartPiece_ne_zero hχ₃ hχ₃c hI₃ h c) hd hv _ _ _

end ChartPieces

end PrimeBHT.TransferenceAssembly
