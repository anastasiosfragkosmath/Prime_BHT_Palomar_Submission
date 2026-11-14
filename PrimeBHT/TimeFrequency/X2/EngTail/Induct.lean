module

public import PrimeBHT.TimeFrequency.X2.EngTail.Step

/-!
# X2, node B5: the induction on the number of tiles

`tile_bound_main`: for a finite family `S` of tiles with `TileBound` data (labels injective), the strong-type hypothesis for all
sub-families, a measurable `F'` with `‖F'‖_X ≤ 1` whose tile densities are at most `λ ≥ 0`, every sub-family `T ⊆ S` satisfies
`‖yNorm ∘ K_T F'‖_{L^q} ≤ C λ |W(T)|^{1/q}` (`C = stepConst`, independent of `S`, `F'`, `λ`, `P`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Induct

variable {ι : Type} [DecidableEq ι] {P : ℕ} [NeZero P]

/-- **The induction on `|T|`** (`λ > 0`). -/
theorem tile_induction {N M Cφ Cκ C₀ q s : ℝ}
    (hq : 1 < q) (hs : 1 < s) (hM : 3 ≤ M) (hN : M + 4 ≤ N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) (hC₀ : 0 ≤ C₀)
    (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι))
    (hStrong : ∀ T ⊆ S, ∀ G : ℝ → ZMod P → ℂ, Measurable G → (∃ B, ∀ x, yNorm s (G x) ≤ B) →
      Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) G x))) ≤
        ENNReal.ofReal C₀ * Lq q (fun x => ENNReal.ofReal (yNorm s (G x))))
    {F' : ℝ → ZMod P → ℂ} (hF'm : Measurable F') (hF'1 : ∀ x, yNorm s (F' x) ≤ 1) {lam : ℝ} (hlam : 0 < lam)
    (hdens : ∀ i ∈ S, ∫ z, ((2 : ℝ) ^ (j i))⁻¹ *
      (1 + |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-M) * yNorm s (F' z) ≤ lam) :
    ∀ T ⊆ S, Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) F' x))) ≤
      stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal (volume (Wset T j v)).toReal ^ (1 / q) := by
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hTS
    by_cases hT : T.Nonempty
    · refine step_bound hq hs hM hN hCφ hCκ hC₀ T j v φ κ (fun i hi => hb i (hTS hi))
        (hinj.mono (Finset.coe_subset.2 hTS)) (fun T' hT' => hStrong T' (hT'.trans hTS)) hF'm hF'1 hlam
        (fun i hi => hdens i (hTS hi)) hT (fun T' hT' => ih T' hT' (hT'.subset.trans hTS))
    · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.1 hT
      subst hT0
      have : (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel (∅ : Finset ι) φ κ) F' x))) =
          fun _ => 0 := by
        funext x
        have e : CZ.kernelOp (tileKernel (∅ : Finset ι) φ κ) F' x = 0 := by
          funext y; simp [CZ.kernelOp, tileKernel]
        rw [e, CZ.yNorm_zero' hs0]; simp
      rw [this, Lq_zero hq0]
      exact bot_le

theorem famConst_ne_top (q : ℝ) : famConst q ≠ ⊤ := by
  unfold famConst
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top

theorem stepConst_ne_top (N M Cφ Cκ C₀ q : ℝ) (hq : 0 < q) : stepConst N M Cφ Cκ C₀ q ≠ ⊤ := by
  unfold stepConst stepConstG
  have hr : ∀ x : ℝ, ENNReal.ofReal x ^ (1 / q) ≠ ⊤ := fun x =>
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  refine ENNReal.mul_ne_top (by norm_num) ?_
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hr _)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (famConst_ne_top q) ENNReal.ofReal_ne_top) (hr _)
  · exact ENNReal.mul_ne_top (famConst_ne_top q) ENNReal.ofReal_ne_top

/-- **The tile estimate for every `λ ≥ 0`.** -/
theorem tile_bound_main {N M Cφ Cκ C₀ q s : ℝ}
    (hq : 1 < q) (hs : 1 < s) (hM : 3 ≤ M) (hN : M + 4 ≤ N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) (hC₀ : 0 ≤ C₀)
    (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι))
    (hStrong : ∀ T ⊆ S, ∀ G : ℝ → ZMod P → ℂ, Measurable G → (∃ B, ∀ x, yNorm s (G x) ≤ B) →
      Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) G x))) ≤
        ENNReal.ofReal C₀ * Lq q (fun x => ENNReal.ofReal (yNorm s (G x))))
    {F' : ℝ → ZMod P → ℂ} (hF'm : Measurable F') (hF'1 : ∀ x, yNorm s (F' x) ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam)
    (hdens : ∀ i ∈ S, ∫ z, ((2 : ℝ) ^ (j i))⁻¹ *
      (1 + |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-M) * yNorm s (F' z) ≤ lam)
    (T : Finset ι) (hTS : T ⊆ S) :
    Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) F' x))) ≤
      stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal (volume (Wset T j v)).toReal ^ (1 / q) := by
  rcases hlam.eq_or_lt with h0 | hpos
  · -- `λ = 0`: let `λ_n = 1/(n+1) → 0`
    subst h0
    set c : ℝ≥0∞ := stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal (volume (Wset T j v)).toReal ^ (1 / q) with hc
    have hpt : ∀ n : ℕ, Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) F' x))) ≤
        c * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have := tile_induction hq hs hM hN hCφ hCκ hC₀ S j v φ κ hb hinj hStrong hF'm hF'1 hn
        (fun i hi => (hdens i hi).trans hn.le) T hTS
      refine this.trans (le_of_eq ?_)
      rw [hc]; ring
    have hlim : Tendsto (fun n : ℕ => c * ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 (c * 0)) := by
      refine ENNReal.Tendsto.const_mul ?_ (Or.inr ?_)
      · have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa using this
      · rw [hc]
        refine ENNReal.mul_ne_top (stepConst_ne_top N M Cφ Cκ C₀ q (by linarith)) ?_
        exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have := ge_of_tendsto' hlim hpt
    rw [mul_zero] at this
    simpa using this
  · exact tile_induction hq hs hM hN hCφ hCκ hC₀ S j v φ κ hb hinj hStrong hF'm hF'1 hpos hdens T hTS

end Induct

end PrimeBHT.TimeFrequency.X2
