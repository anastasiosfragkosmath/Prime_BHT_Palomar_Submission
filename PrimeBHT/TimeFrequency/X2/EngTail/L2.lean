module

public import PrimeBHT.TimeFrequency.X2.EngTail.TileData
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeToTile
public import PrimeBHT.TimeFrequency.X2.CZ.Basecase

/-!
# X2, node B5: the scalar `L²` bound of a lacunary tree operator

`‖∑_R ψ_R T_{m_R} f‖₂ ≤ A₂ ‖f‖₂` for bounded integrable `f`: Fourier orthogonality of the pieces
(`Ortho/TreeScalar.lean`: `∫|∑ g_R|² ≤ 2 sInv ∑ ∫|g̃_R|²`), Plancherel `‖T_m f‖₂ = ‖m 𝓕f‖₂` for each frequency
interval, and `∑_B |m_B|² ≤ C²` (the supports of distinct boxes are disjoint).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `T_m f = 𝓕⁻(m · 𝓕 f)` for `f ∈ L¹` and `m` continuous with compact support. -/
theorem tm_eq_fourierInv {m f : ℝ → ℂ} (hm : Continuous m) {c r : ℝ}
    (hsupp : ∀ ξ, r < |ξ - c| → m ξ = 0) (hf : Integrable f) (x : ℝ) :
    tm m f x = 𝓕⁻ (fun η => m η * 𝓕 f η) x := by
  have hρ : Integrable (fun ξ => m (-ξ)) := (integrable_of_far hm hsupp).comp_neg
  have key := integral_fourier_mul_fourier_neg (ρ := fun ξ => m (-ξ)) hρ hf x
  have hFρ : 𝓕 (fun ξ => m (-ξ)) = 𝓕⁻ m := (Real.fourierInv_eq_fourier_comp_neg m).symm
  rw [hFρ] at key
  have hL : ∫ ξ, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) * (m (-ξ) * 𝓕 f (-ξ)) =
      𝓕⁻ (fun η => m η * 𝓕 f η) x := by
    rw [Real.fourierInv_eq']
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, neg_neg]
    congr 2
    simp only [inner, RCLike.re_to_real, star_trivial]
    push_cast
    ring
  rw [← hL, key]
  unfold tm
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring


theorem integral_norm_sq_eq_of_eLpNorm_eq {g h : ℝ → ℂ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (e : eLpNorm g 2 volume = eLpNorm h 2 volume) : ∫ x, ‖g x‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at e
  have e1 := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 e
  simp only [ENNReal.toReal_ofNat] at e1
  have hA : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  have hB : 0 ≤ ∫ x, ‖h x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  have e2 : ∫ x, ‖g x‖ ^ (2 : ℝ) = ∫ x, ‖h x‖ ^ (2 : ℝ) := by
    have := congrArg (fun t : ℝ => t ^ (2 : ℝ)) e1
    rwa [← Real.rpow_mul hA, ← Real.rpow_mul hB, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num,
      Real.rpow_one, Real.rpow_one] at this
  simpa only [Real.rpow_two] using e2

/-- Plancherel for the multiplier piece: `∫ |T_m f|² = ∫ |m|² |𝓕 f|²`. -/
theorem integral_sq_tm {m f : ℝ → ℂ} (hm : Continuous m) {c r : ℝ} (hsupp : ∀ ξ, r < |ξ - c| → m ξ = 0)
    (hf : Integrable f) (_hf2 : MemLp f 2 volume) :
    MemLp (tm m f) 2 volume ∧ MemLp (fun η => m η * 𝓕 f η) 2 volume ∧
      ∫ x, ‖tm m f x‖ ^ 2 = ∫ η, ‖m η * 𝓕 f η‖ ^ 2 := by
  have hFc : Continuous (𝓕 f) := continuous_fourier_of_integrable hf
  have hhc : Continuous (fun η => m η * 𝓕 f η) := hm.mul hFc
  have hhs : HasCompactSupport (fun η => m η * 𝓕 f η) :=
    hasCompactSupport_of_far (c := c) (r := r) (fun ξ hξ => by simp [hsupp ξ hξ])
  have hh1 : Integrable (fun η => m η * 𝓕 f η) := hhc.integrable_of_hasCompactSupport hhs
  have hh2 : MemLp (fun η => m η * 𝓕 f η) 2 volume := hhc.memLp_of_hasCompactSupport hhs
  have htm : tm m f = 𝓕⁻ (fun η => m η * 𝓕 f η) := funext (tm_eq_fourierInv hm hsupp hf)
  have hpl := CZ.eLpNorm_fourierInv_eq_of_integrable _ hh1 hh2
  have hmem : MemLp (tm m f) 2 volume := by
    rw [htm]
    show eLpNorm (𝓕⁻ (fun η => m η * 𝓕 f η)) 2 volume < ⊤
    rw [hpl]; exact hh2
  refine ⟨hmem, hh2, ?_⟩
  refine integral_norm_sq_eq_of_eLpNorm_eq hmem hh2 ?_
  rw [htm]; exact hpl

/-- `‖𝓕 f‖₂ = ‖f‖₂` for `f ∈ L¹ ∩ L²`. -/
theorem integral_sq_fourier {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hpl := CZ.eLpNorm_fourierInv_eq_of_integrable f hf hf2
  have hc : Continuous (𝓕⁻ f) := CZ.continuous_fourierInv_of_integrable f hf
  have hmem : MemLp (𝓕⁻ f) 2 volume := by
    show eLpNorm (𝓕⁻ f) 2 volume < ⊤
    rw [hpl]; exact hf2
  have hF : 𝓕 f = fun w => 𝓕⁻ f (-w) := by
    funext w; rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have h1 : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ ξ, ‖𝓕⁻ f ξ‖ ^ 2 := by
    rw [hF]
    exact integral_neg_eq_self (fun ξ => ‖𝓕⁻ f ξ‖ ^ 2) volume
  have h2 := integral_norm_sq_eq_of_eLpNorm_eq hmem hf2 hpl
  refine ⟨?_, h1.trans h2⟩
  rw [hF]
  show eLpNorm ((𝓕⁻ f) ∘ Neg.neg) 2 volume < ⊤
  rw [eLpNorm_comp_measurePreserving hc.aestronglyMeasurable (Measure.measurePreserving_neg (volume : Measure ℝ))]
  exact hmem


section Tree

variable {𝔭 : Params} {J : ℕ} {Qs : Set Box} {k : Fin 3} {Tr : Finset TriTile} {m : TriTile → ℝ → ℂ}

theorem norm_m_le {R : TriTile} {c : ℝ} {n : ℝ → ℂ} (hm : InMult 𝔭 R.box.scale c n) (η : ℝ) : ‖n η‖ ≤ 𝔭.C := by
  have := hm.2.2 0 (Nat.zero_le _) η
  simpa using this

/-- Pointwise orthogonality of the frequency pieces: at most one box has `m_B(η) ≠ 0` (`β ≤ 3`). -/
theorem sum_sq_m_le (hQ : IsRankOne J Qs) (hT : IsLacunary k Tr) (hbox : ∀ R ∈ Tr, R.box ∈ Qs)
    (hdata : ∀ R ∈ Tr, InMult 𝔭 R.box.scale (R.box.centre k) (m R)) (hβ : 𝔭.β ≤ 11 / 4) (hC : 0 ≤ 𝔭.C)
    {rep : Box → TriTile} (hrep : ∀ B ∈ Tr.image TriTile.box, rep B ∈ Tr ∧ (rep B).box = B) (η : ℝ) :
    ∑ B ∈ Tr.image TriTile.box, ‖m (rep B) η‖ ^ 2 ≤ 𝔭.C ^ 2 := by
  classical
  by_cases h : ∃ B₀ ∈ Tr.image TriTile.box, m (rep B₀) η ≠ 0
  · obtain ⟨B₀, hB₀, hne₀⟩ := h
    have hzero : ∀ B ∈ Tr.image TriTile.box, B ≠ B₀ → m (rep B) η = 0 := by
      intro B hB hBB₀
      by_contra hne
      obtain ⟨hrB, hrBb⟩ := hrep B hB
      obtain ⟨hrB₀, hrB₀b⟩ := hrep B₀ hB₀
      have hω : (rep B).box.ω k ≠ (rep B₀).box.ω k := fun h =>
        hBB₀ (by
          rw [← hrBb, ← hrB₀b]
          exact box_eq_of_omega_eq hQ (hbox _ hrB) (hbox _ hrB₀) h)
      have hdis := hT _ hrB _ hrB₀ hω
      rw [dilate_three_omega, dilate_three_omega] at hdis
      have hmem : ∀ R ∈ Tr, m R η ≠ 0 → η ∈ Set.Ico (R.box.centre k - 3 * (2 : ℝ) ^ (-R.box.scale) / 2)
          (R.box.centre k + 3 * (2 : ℝ) ^ (-R.box.scale) / 2) := by
        intro R hR hmR
        have hl : (0 : ℝ) < (2 : ℝ) ^ (-R.box.scale) := zpow_pos (by norm_num) _
        have h1 : |η - R.box.centre k| ≤ 𝔭.β * (2 : ℝ) ^ (-R.box.scale) / 2 := by
          by_contra hc
          push Not at hc
          exact hmR ((hdata R hR).2.1 η hc)
        rw [abs_le] at h1
        constructor <;> nlinarith [h1.1, h1.2]
      exact Set.disjoint_left.1 hdis (hmem _ hrB hne) (hmem _ hrB₀ hne₀)
    rw [Finset.sum_eq_single B₀ (fun B hB hBB₀ => by rw [hzero B hB hBB₀]; simp) (fun hB => absurd hB₀ hB)]
    have := norm_m_le (hdata _ (hrep B₀ hB₀).1) η
    have h0 := norm_nonneg (m (rep B₀) η)
    nlinarith
  · push Not at h
    rw [Finset.sum_eq_zero (fun B hB => by rw [h B hB]; simp)]
    positivity

end Tree


section Tree2

variable {𝔭 : Params}

/-- The constant of the scalar `L²` bound. -/
def treeL2Const (𝔭 : Params) : ℝ :=
  2 * sInv * (𝔭.C * latConst (((𝔭.decN 10).N : ℕ) : ℝ)) ^ 2 * 𝔭.C ^ 2

theorem sum_sq_le_sq_of_nonneg {ι : Type*} (S : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ S, 0 ≤ a i) :
    ∑ i ∈ S, a i ^ 2 ≤ (∑ i ∈ S, a i) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ S, a i := Finset.sum_nonneg h0
  calc ∑ i ∈ S, a i ^ 2 ≤ ∑ i ∈ S, a i * (∑ j ∈ S, a j) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have : a i ≤ ∑ j ∈ S, a j := Finset.single_le_sum (f := a) h0 hi
        nlinarith [h0 i hi]
    _ = (∑ i ∈ S, a i) ^ 2 := by rw [← Finset.sum_mul]; ring

theorem tree_L2 (h𝔭 : 𝔭.Admissible) {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3}
    {Tr : Finset TriTile} (hT : IsLacunary k Tr) (hbox : ∀ R ∈ Tr, R.box ∈ Qs) {ψ m : TriTile → ℝ → ℂ}
    (hdata : ∀ R ∈ Tr, InPsi 𝔭 R.box.scale R.pos (ψ R) ∧ InMult 𝔭 R.box.scale (R.box.centre k) (m R))
    (hcons : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box = R'.box → m R = m R') {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) (hf2 : MemLp f 2 volume) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    ∫ x, ‖∑ R ∈ Tr, gfun (ψ R) (m R) f x‖ ^ 2 ≤ treeL2Const 𝔭 * ∫ x, ‖f x‖ ^ 2 := by
  classical
  have hδ8 := h𝔭.delta_le_eighth
  obtain ⟨hJ, hN, hD, hδpos, -, hβ1, hβ2, hC1⟩ := h𝔭
  have hN14 : 14 ≤ 𝔭.N := le_trans (by unfold classFloor; norm_num) hN
  have hD2 : 2 ≤ 𝔭.D := le_trans (by unfold classFloor; norm_num) hD
  have hβδ : 𝔭.β + 2 * 𝔭.δ ≤ 3 := by linarith
  have hC0 : 0 ≤ 𝔭.C := by linarith
  have hsc := tree_scalar_bound (𝔭 := 𝔭) hN14 hD2 (by linarith) hβδ hQ hT hbox hdata hf hB
  -- notation
  set N' : ℝ := (((𝔭.decN 10).N : ℕ) : ℝ) with hN'
  have hN'1 : 1 < N' := by
    simp only [hN', Params.decN]
    have : 14 ≤ 𝔭.N := hN14
    have h4 : (4 : ℝ) ≤ ((𝔭.N - 10 : ℕ) : ℝ) := by
      have : 4 ≤ 𝔭.N - 10 := by omega
      exact_mod_cast this
    linarith
  set Λ : ℝ := 𝔭.C * latConst N' with hΛ
  have hΛ0 : 0 ≤ Λ := by have := latConst_nonneg hN'1; positivity
  -- representatives of the boxes
  have : Nonempty TriTile := ⟨⟨⟨0, fun _ => 0⟩, 0⟩⟩
  have hex : ∀ B ∈ Tr.image TriTile.box, ∃ R, R ∈ Tr ∧ R.box = B := by
    intro B hB'
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hB'
    exact ⟨R, hR, rfl⟩
  choose! rep hrepmem hrepbox using hex
  have hrep : ∀ B ∈ Tr.image TriTile.box, rep B ∈ Tr ∧ (rep B).box = B := fun B hB' => ⟨hrepmem B hB', hrepbox B hB'⟩
  -- pointwise bound
  have hψt : ∀ R ∈ Tr, InPsi (𝔭.decN 10) R.box.scale R.pos (psiTilde R.box.scale R.pos (ψ R)) :=
    fun R hR => inPsi_psiTilde hN14 (hdata R hR).1
  have hpt : ∀ x, ∑ R ∈ Tr, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 ≤
      Λ ^ 2 * ∑ B ∈ Tr.image TriTile.box, ‖tm (m (rep B)) f x‖ ^ 2 := by
    intro x
    have h1 : ∑ R ∈ Tr, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 =
        ∑ B ∈ Tr.image TriTile.box, ∑ R ∈ Tr.filter (fun R => R.box = B),
          ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to (g := TriTile.box) (s := Tr) (t := Tr.image TriTile.box)
        (fun R hR => Finset.mem_image_of_mem _ hR) _).symm
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun B hB' => ?_
    have hfib : ∀ R ∈ Tr.filter (fun R => R.box = B), R ∈ Tr ∧ R.box = B := fun R hR => Finset.mem_filter.1 hR
    -- all tiles of the fibre share `m`
    have hm_eq : ∀ R ∈ Tr.filter (fun R => R.box = B), m R = m (rep B) := by
      intro R hR
      obtain ⟨hRT, hRB⟩ := hfib R hR
      exact hcons R hRT (rep B) (hrep B hB').1 (hRB.trans (hrep B hB').2.symm)
    have h2 : ∀ R ∈ Tr.filter (fun R => R.box = B),
        ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 =
          ‖psiTilde R.box.scale R.pos (ψ R) x‖ ^ 2 * ‖tm (m (rep B)) f x‖ ^ 2 := by
      intro R hR
      unfold gfun
      rw [norm_mul, mul_pow, hm_eq R hR]
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    -- `∑_R ‖ψ̃_R x‖² ≤ Λ²`
    have h3 : ∀ R ∈ Tr.filter (fun R => R.box = B),
        ‖psiTilde R.box.scale R.pos (ψ R) x‖ ≤ 𝔭.C * tw N' B.scale R.pos x := by
      intro R hR
      obtain ⟨hRT, hRB⟩ := hfib R hR
      have := (hψt R hRT).le_tw x
      have hsc : R.box.scale = B.scale := by rw [hRB]
      rw [← hsc]
      simpa [Params.decN, hN'] using this
    have h4 : ∑ R ∈ Tr.filter (fun R => R.box = B), tw N' B.scale R.pos x ≤ latConst N' := by
      have hinj : Set.InjOn TriTile.pos (Tr.filter (fun R => R.box = B) : Set TriTile) := by
        intro R₁ h₁ R₂ h₂ h
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at h₁ h₂
        cases R₁; cases R₂
        simp only at h₁ h₂ h
        simp [h₁.2, h₂.2, h]
      have e : ∑ R ∈ Tr.filter (fun R => R.box = B), tw N' B.scale R.pos x =
          ∑ v ∈ (Tr.filter (fun R => R.box = B)).image TriTile.pos,
            (1 + |x - (2 : ℝ) ^ B.scale * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ B.scale) ^ (-N') := by
        rw [Finset.sum_image hinj]; rfl
      rw [e]
      exact sum_lattice_le hN'1 (zpow_pos (by norm_num) _) x _
    have h5 : ∑ R ∈ Tr.filter (fun R => R.box = B), ‖psiTilde R.box.scale R.pos (ψ R) x‖ ≤ Λ := by
      calc _ ≤ ∑ R ∈ Tr.filter (fun R => R.box = B), 𝔭.C * tw N' B.scale R.pos x := Finset.sum_le_sum h3
        _ = 𝔭.C * ∑ R ∈ Tr.filter (fun R => R.box = B), tw N' B.scale R.pos x := by rw [← Finset.mul_sum]
        _ ≤ 𝔭.C * latConst N' := mul_le_mul_of_nonneg_left h4 hC0
    calc ∑ R ∈ Tr.filter (fun R => R.box = B), ‖psiTilde R.box.scale R.pos (ψ R) x‖ ^ 2
        ≤ (∑ R ∈ Tr.filter (fun R => R.box = B), ‖psiTilde R.box.scale R.pos (ψ R) x‖) ^ 2 :=
          sum_sq_le_sq_of_nonneg _ _ (fun _ _ => norm_nonneg _)
      _ ≤ Λ ^ 2 := by
          have : 0 ≤ ∑ R ∈ Tr.filter (fun R => R.box = B), ‖psiTilde R.box.scale R.pos (ψ R) x‖ :=
            Finset.sum_nonneg fun _ _ => norm_nonneg _
          nlinarith
  -- integrate
  have hN2 : 2 ≤ (𝔭.decN 10).N := by simp only [Params.decN]; omega
  have hgi : ∀ R ∈ Tr, Integrable (fun x => ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2) :=
    fun R hR => integrable_sq_gfun (𝔭 := 𝔭.decN 10) hN2 hD2 (by simpa [Params.decN] using (by linarith : (0 : ℝ) ≤ 𝔭.β))
      (hψt R hR) (hdata R hR).2 hf hB
  have hFc : Continuous (𝓕 f) := continuous_fourier_of_integrable hfi
  have hPl : ∀ R ∈ Tr, MemLp (tm (m R) f) 2 volume ∧ MemLp (fun η => m R η * 𝓕 f η) 2 volume ∧
      ∫ x, ‖tm (m R) f x‖ ^ 2 = ∫ η, ‖m R η * 𝓕 f η‖ ^ 2 := fun R hR =>
    integral_sq_tm (hdata R hR).2.1.continuous (c := R.box.centre k) (r := 𝔭.β * (2 : ℝ) ^ (-R.box.scale) / 2)
      (hdata R hR).2.2.1 hfi hf2
  have hui : ∀ R ∈ Tr, Integrable (fun x => ‖tm (m R) f x‖ ^ 2) := fun R hR =>
    (memLp_two_iff_integrable_sq_norm (continuous_tm hD2 (by linarith) (hdata R hR).2 hf hB).aestronglyMeasurable).1
      (hPl R hR).1
  have hvi : ∀ R ∈ Tr, Integrable (fun η => ‖m R η * 𝓕 f η‖ ^ 2) := fun R hR =>
    (memLp_two_iff_integrable_sq_norm ((hdata R hR).2.1.continuous.mul hFc).aestronglyMeasurable).1
      (hPl R hR).2.1
  obtain ⟨hF2, hFint⟩ := integral_sq_fourier hfi hf2
  have hLHS : ∑ R ∈ Tr, ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 ≤
      Λ ^ 2 * (𝔭.C ^ 2 * ∫ x, ‖f x‖ ^ 2) := by
    rw [← integral_finsetSum _ hgi]
    have hBi : ∀ B ∈ Tr.image TriTile.box, Integrable (fun x => ‖tm (m (rep B)) f x‖ ^ 2) :=
      fun B hB' => hui _ (hrep B hB').1
    calc ∫ x, ∑ R ∈ Tr, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2
        ≤ ∫ x, Λ ^ 2 * ∑ B ∈ Tr.image TriTile.box, ‖tm (m (rep B)) f x‖ ^ 2 :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => Finset.sum_nonneg fun _ _ => by positivity)
            ((integrable_finsetSum _ hBi).const_mul _) (Eventually.of_forall hpt)
      _ = Λ ^ 2 * ∑ B ∈ Tr.image TriTile.box, ∫ x, ‖tm (m (rep B)) f x‖ ^ 2 := by
          rw [integral_const_mul, integral_finsetSum _ hBi]
      _ = Λ ^ 2 * ∑ B ∈ Tr.image TriTile.box, ∫ η, ‖m (rep B) η‖ ^ 2 * ‖𝓕 f η‖ ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun B hB' => ?_
          rw [(hPl _ (hrep B hB').1).2.2]
          refine integral_congr_ae (Eventually.of_forall fun η => ?_)
          simp only [norm_mul, mul_pow]
      _ ≤ Λ ^ 2 * (𝔭.C ^ 2 * ∫ x, ‖f x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hvi' : ∀ B ∈ Tr.image TriTile.box, Integrable (fun η => ‖m (rep B) η‖ ^ 2 * ‖𝓕 f η‖ ^ 2) := by
            intro B hB'
            refine (hvi _ (hrep B hB').1).congr (Eventually.of_forall fun η => ?_)
            simp only [norm_mul, mul_pow]
          rw [← integral_finsetSum _ hvi', ← hFint, ← integral_const_mul]
          refine integral_mono_of_nonneg (Eventually.of_forall fun η => Finset.sum_nonneg fun _ _ => by positivity)
            (((memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).1 hF2).const_mul _)
            (Eventually.of_forall fun η => ?_)
          · have := sum_sq_m_le (𝔭 := 𝔭) hQ hT hbox (fun R hR => (hdata R hR).2) hβ2 hC0 hrep η
            simp only [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  calc ∫ x, ‖∑ R ∈ Tr, gfun (ψ R) (m R) f x‖ ^ 2
      ≤ 2 * sInv * ∑ R ∈ Tr, ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 := hsc
    _ ≤ 2 * sInv * (Λ ^ 2 * (𝔭.C ^ 2 * ∫ x, ‖f x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hLHS (by have := sInv_nonneg; positivity)
    _ = treeL2Const 𝔭 * ∫ x, ‖f x‖ ^ 2 := by
        simp only [treeL2Const, hΛ, hN']; ring

end Tree2

end PrimeBHT.TimeFrequency.X2
