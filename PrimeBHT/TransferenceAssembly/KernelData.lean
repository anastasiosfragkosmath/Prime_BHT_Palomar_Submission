module

public import PrimeBHT.BlockSum.Basic
public import PrimeBHT.KernelFourier.Uniform

/-!
# Packaging facts for the block transference (blueprint N43(a))

* `KernelData`, `kernelData`: the kernel `K^J_{Q;τ} = φ_{N(Q)} * ∑_{a_Q ≤ k ≤ J} ψ_k` is (the real
  part of) a Schwartz function `K : 𝓢(ℝ, ℂ)` with `K̂ = 0` for `|t| > c / N(Q)`, and `m(t) = K̂(-t)`
  smooth on `ℝ \ {0}` satisfying the all-order bounds `|t|^j ‖m^{(j)}(t)‖ ≤ A_j` with `A_j`
  independent of `Q` and `J`.
* `exists_Q0_alias_arith`: for blocks `B` with `|B| ≤ 24 Q^{τ-ε}` and `N = lcm B`, one has
  `N · c / N(Q) ≤ 10⁻³` for `Q ≥ Q₀` (from `log N ≤ 100 Q^{τ-ε} log Q` and
  `log N(Q) = Q^{τ-ε/10}`).
-/

@[expose] public section

open scoped FourierTransform SchwartzMap ContDiff

namespace PrimeBHT.TransferenceAssembly

open PrimeCarleson.Proof.Paper (sqfreeSet lcmQ lcmQ_le_exp)

/-- The kernel `K^J_{Q;τ}` is a Schwartz function `K` with `K̂` supported in `|t| ≤ c / N(Q)`, and
`m(t) = K̂(-t)` is smooth off `0` with the all-order bounds `A`. -/
def KernelData (φ : 𝓢(ℝ, ℝ)) (c : ℝ) (χ : ℝ → ℝ) (τ ε : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ (Q J : ℕ), ∃ K : 𝓢(ℝ, ℂ),
    (∀ x : ℝ, K x = ((PrimeBHT.BlockSum.KQ φ χ Q τ ε J x : ℝ) : ℂ)) ∧
    (∀ t : ℝ, c / PrimeBHT.BlockSum.NQ Q τ ε < |t| → 𝓕 (K : ℝ → ℂ) t = 0) ∧
    ContDiffOn ℝ ∞ (fun t => 𝓕 (K : ℝ → ℂ) (-t)) {0}ᶜ ∧
    (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 →
      |t| ^ j * ‖iteratedDeriv j (fun t => 𝓕 (K : ℝ → ℂ) (-t)) t‖ ≤ A j)

theorem kernelData {φ : 𝓢(ℝ, ℝ)} {χ : ℝ → ℝ} (hχ : PrimeBHT.Kernel.IsCutoff χ) {c : ℝ}
    (hφc : ∀ ξ : ℝ, c < |ξ| → 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) ξ = 0) (τ ε : ℝ) :
    KernelData φ c χ τ ε (PrimeBHT.KernelFourier.symbolConst hχ φ) := by
  intro Q J
  have hN : 0 < PrimeBHT.BlockSum.NQ Q τ ε := Real.exp_pos _
  obtain ⟨S, hS⟩ := PrimeBHT.KernelFourier.exists_schwartz_smooth_kernelI hχ φ hN
    (PrimeBHT.BlockSum.aQ Q τ) J
  have hK : ((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM S : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      fun x => ((PrimeBHT.Kernel.smooth φ (PrimeBHT.BlockSum.NQ Q τ ε)
        (PrimeBHT.Kernel.kernelI χ (PrimeBHT.BlockSum.aQ Q τ) J) x : ℝ) : ℂ) := by
    funext x
    rw [← hS]
    rfl
  refine ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM S, fun x => ?_, ?_, ?_, ?_⟩
  · exact congrFun hK x
  · intro t ht
    rw [hK, PrimeBHT.KernelFourier.fourier_smooth_kernelI hχ φ hN, hφc _, zero_mul]
    rw [abs_mul, abs_of_pos hN]
    rwa [div_lt_iff₀ hN, mul_comm] at ht
  · rw [hK]
    exact (PrimeBHT.KernelFourier.contDiff_fourier_smooth_kernelI_neg hχ φ hN _ _).contDiffOn
  · intro j t ht
    rw [hK]
    exact PrimeBHT.KernelFourier.symbol_bound_neg hχ φ j hN _ _ ht

/-! ## The arithmetic of the block size -/

/-- A pure asymptotic: for `κ + 9ε/10 > 0`, eventually `100 Q^κ log Q ≤ Q^{κ + 9ε/10} / 2` and
`Q^{κ + 9ε/10} ≥ 2000 c + 1`. -/
theorem eventually_alias_arith {c κ ε : ℝ} (hε0 : 0 < ε) (hκ : 0 < κ + 9 * ε / 10) :
    ∀ᶠ Q : ℝ in Filter.atTop, 1 ≤ Q ∧
      100 * Q ^ κ * Real.log Q ≤ Q ^ (κ + 9 * ε / 10) / 2 ∧
      2000 * c + 1 ≤ Q ^ (κ + 9 * ε / 10) := by
  have h9 : 0 < 9 * ε / 10 := by positivity
  have hlog := (isLittleO_log_rpow_atTop h9).def (c := 1 / 200) (by norm_num)
  have hpow := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2000 * c + 1)
  filter_upwards [Filter.eventually_ge_atTop 1, hlog, hpow] with Q hQ1 hQ hQ'
  refine ⟨hQ1, ?_, hQ'⟩
  have hQ0 : 0 < Q := by linarith
  have hQκ : 0 < Q ^ κ := Real.rpow_pos_of_pos hQ0 κ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hQ1),
    abs_of_pos (Real.rpow_pos_of_pos hQ0 _)] at hQ
  have h1 : 100 * Real.log Q ≤ Q ^ (9 * ε / 10) / 2 := by linarith
  rw [Real.rpow_add hQ0]
  calc 100 * Q ^ κ * Real.log Q = Q ^ κ * (100 * Real.log Q) := by ring
    _ ≤ Q ^ κ * (Q ^ (9 * ε / 10) / 2) := mul_le_mul_of_nonneg_left h1 hQκ.le
    _ = Q ^ κ * Q ^ (9 * ε / 10) / 2 := by ring

/-- For `Q ≥ Q₀`, every block `B` of squarefree integers in `(Q/2, Q]` with `|B| ≤ 24 Q^{τ-ε}`
has `lcm B · c / N(Q) ≤ 10⁻³` (`log lcm B ≤ 100 Q^{τ-ε} log Q`, `log N(Q) = Q^{τ-ε/10}`). -/
theorem exists_Q0_alias_arith {c τ ε : ℝ} (hc : 0 ≤ c) (hε0 : 0 < ε) (hετ : ε < τ) :
    ∃ Q₀ : ℕ, ∀ j : ℕ, Q₀ ≤ 2 ^ j → ∀ B : Finset ℕ, B ⊆ sqfreeSet j → B.Nonempty →
      (B.card : ℝ) ≤ 24 * ((2 : ℝ) ^ j) ^ (τ - ε) →
      ∀ N : ℕ, lcmQ B = N → (N : ℝ) * (c / PrimeBHT.BlockSum.NQ (2 ^ j) τ ε) ≤ 1 / 1000 := by
  have hκ : 0 < (τ - ε) + 9 * ε / 10 := by linarith
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
    (eventually_alias_arith (c := c) (κ := τ - ε) hε0 hκ)
  refine ⟨⌈R⌉₊, fun j hj B hB _ hcard N hN => ?_⟩
  have hQR : R ≤ (2 : ℝ) ^ j := by
    have : (⌈R⌉₊ : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hj
    push_cast at this
    exact (Nat.le_ceil R).trans this
  obtain ⟨hQ1, ha, hy⟩ := hR _ hQR
  have hexp : τ - ε / 10 = (τ - ε) + 9 * ε / 10 := by ring
  have hNQ : PrimeBHT.BlockSum.NQ (2 ^ j) τ ε =
      Real.exp (((2 : ℝ) ^ j) ^ ((τ - ε) + 9 * ε / 10)) := by
    unfold PrimeBHT.BlockSum.NQ
    rw [hexp]
    push_cast
    rfl
  have hκ0 : 0 ≤ ((2 : ℝ) ^ j) ^ (τ - ε) := Real.rpow_nonneg (by positivity) _
  have hcard' : (B.card : ℝ) ≤ 100 * ((2 : ℝ) ^ j) ^ (τ - ε) := by linarith
  have hlcm := lcmQ_le_exp hB hcard'
  subst hN
  rw [hNQ]
  generalize ((2 : ℝ) ^ j) ^ ((τ - ε) + 9 * ε / 10) = y at ha hy ⊢
  have h1 : (lcmQ B : ℝ) ≤ Real.exp (y / 2) := hlcm.trans (Real.exp_le_exp.2 ha)
  have h2 : Real.exp (y / 2) * (c / Real.exp y) = c / Real.exp (y / 2) := by
    have : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (y / 2)
    field_simp
  have h3 : c / Real.exp (y / 2) ≤ 1 / 1000 := by
    have hpos := Real.exp_pos (y / 2)
    rw [div_le_iff₀ hpos]
    have := Real.add_one_le_exp (y / 2)
    linarith
  calc (lcmQ B : ℝ) * (c / Real.exp y) ≤ Real.exp (y / 2) * (c / Real.exp y) :=
        mul_le_mul_of_nonneg_right h1 (div_nonneg hc (Real.exp_pos _).le)
    _ = c / Real.exp (y / 2) := h2
    _ ≤ 1 / 1000 := h3

end PrimeBHT.TransferenceAssembly
