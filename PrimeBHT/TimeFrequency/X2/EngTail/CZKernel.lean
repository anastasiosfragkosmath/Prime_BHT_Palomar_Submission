module

public import PrimeBHT.TimeFrequency.X2.EngTail.Sums
public import PrimeBHT.TimeFrequency.X2.CZ.Addendum

/-!
# X2, node B5: a finite sum of tile kernels is a Calderón-Zygmund kernel

Abstract real-analysis part of the CZ-kernel verification of tree operators.  Tiles `i ∈ S` have a scale `j i`, a
position `v i`, a cutoff `φ i` (decay of order `N` around `c_i = 2^{j i}(v i + 1/2)` at scale `2^{j i}`, with a
derivative bound) and a kernel `κ i` (decay of order `M`, derivative bound).  If `(j, v)` is injective on `S`
(one tile per scale and position), then `K x z = ∑_{i ∈ S} φ i x · κ i (x - z)` satisfies `IsCZKernel A K` with
`A = C_φ C_κ latConst(N) (4 + 2^{M+2}(2^{N+1} + 2))`, independently of `S`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The position weight of the tile `(j, v)`: `(1 + |x - 2^j (v + 1/2)|/2^j)^{-N}`. -/
def tw (N : ℝ) (j v : ℤ) (x : ℝ) : ℝ := (1 + |x - (2 : ℝ) ^ j * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ j) ^ (-N)

theorem tw_nonneg (N : ℝ) (j v : ℤ) (x : ℝ) : 0 ≤ tw N j v x := by
  unfold tw
  have : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  positivity

theorem tw_le_one {N : ℝ} (hN : 0 ≤ N) (j v : ℤ) (x : ℝ) : tw N j v x ≤ 1 := by
  unfold tw
  have : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  exact Real.rpow_le_one_of_one_le_of_nonpos (by have := div_nonneg (abs_nonneg (x - (2 : ℝ) ^ j * ((v : ℝ) + 1 / 2))) this.le; linarith) (by linarith)

/-- Peetre: `tw(ξ) ≤ 2^N tw(x)` for `|ξ - x| ≤ 2^j`. -/
theorem tw_peetre {N : ℝ} (hN : 0 ≤ N) (j v : ℤ) {x ξ : ℝ} (h : |ξ - x| ≤ (2 : ℝ) ^ j) :
    tw N j v ξ ≤ 2 ^ N * tw N j v x := by
  unfold tw
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  set c := (2 : ℝ) ^ j * ((v : ℝ) + 1 / 2)
  set L := (2 : ℝ) ^ j
  have ha : 0 < 1 + |ξ - c| / L := by positivity
  have hb : 0 < 1 + |x - c| / L := by positivity
  have hle : (1 + |x - c| / L) / 2 ≤ 1 + |ξ - c| / L := by
    have h1 : |x - c| ≤ |ξ - c| + |ξ - x| := by
      calc |x - c| = |(ξ - c) - (ξ - x)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have h2 : |x - c| / L ≤ |ξ - c| / L + 1 := by
      rw [div_le_iff₀ hL, add_mul, one_mul, div_mul_cancel₀ _ hL.ne']
      linarith
    have h3 : 0 ≤ |ξ - c| / L := by positivity
    linarith
  have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + |x - c| / L) / 2) hle (by linarith : -N ≤ 0)
  refine this.trans (le_of_eq ?_)
  rw [Real.div_rpow hb.le (by norm_num), Real.rpow_neg hb.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

theorem pow_neg_anti {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) : b ^ (-M) ≤ a ^ (-M) :=
  Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- Mean value inequality on a segment. -/
theorem norm_sub_le_of_deriv_bound {f : ℝ → ℂ} (hf : Differentiable ℝ f) {x x' B : ℝ}
    (h : ∀ ξ ∈ Set.uIcc x x', ‖deriv f ξ‖ ≤ B) : ‖f x - f x'‖ ≤ B * |x - x'| := by
  have := (convex_uIcc x x').norm_image_sub_le_of_norm_deriv_le (f := f) (fun ξ _ => hf.differentiableAt) h
    (right_mem_uIcc : x' ∈ Set.uIcc x x') (left_mem_uIcc : x ∈ Set.uIcc x x')
  refine this.trans_eq ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

/-- The bounds of one tile. -/
structure TileBound (N M Cφ Cκ : ℝ) (j v : ℤ) (φ κ : ℝ → ℂ) : Prop where
  φ_le : ∀ x, ‖φ x‖ ≤ Cφ * tw N j v x
  φ_diff : Differentiable ℝ φ
  φ'_le : ∀ x, ‖deriv φ x‖ ≤ Cφ * ((2 : ℝ) ^ j)⁻¹ * tw N j v x
  κ_le : ∀ w, ‖κ w‖ ≤ Cκ * (((2 : ℝ) ^ j)⁻¹ * (1 + |w| / (2 : ℝ) ^ j) ^ (-M))
  κ_diff : Differentiable ℝ κ
  κ'_le : ∀ w, ‖deriv κ w‖ ≤ Cκ * ((((2 : ℝ) ^ j)⁻¹) ^ 2 * (1 + |w| / (2 : ℝ) ^ j) ^ (-M))

/-- The scale-sum majorant of the smoothness terms. -/
def Hs (M d δ : ℝ) (j : ℤ) : ℝ :=
  min ((2 : ℝ) ^ j)⁻¹ (δ * (((2 : ℝ) ^ j)⁻¹) ^ 2) * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M)

theorem Hs_nonneg (M d δ : ℝ) (hd : 0 ≤ d) (hδ : 0 ≤ δ) (j : ℤ) : 0 ≤ Hs M d δ j := by
  unfold Hs
  have h2 : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  exact mul_nonneg (le_min (by positivity) (by positivity)) (by positivity)

section PerTile

variable {N M Cφ Cκ : ℝ} {j v : ℤ} {φ κ : ℝ → ℂ}

/-- Kernel bound at a point `w` with `|w| ≥ d/2`. -/
theorem TileBound.κ_le_half (hb : TileBound N M Cφ Cκ j v φ κ) (hM : 0 ≤ M) {d : ℝ} (hd : 0 ≤ d) {w : ℝ}
    (hw : d / 2 ≤ |w|) :
    ‖κ w‖ ≤ Cκ * (((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M)) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hCκ : 0 ≤ Cκ := by
    have := hb.κ_le 0
    have h0 : 0 ≤ Cκ * (((2 : ℝ) ^ j)⁻¹ * (1 + |(0 : ℝ)| / (2 : ℝ) ^ j) ^ (-M)) := (norm_nonneg _).trans this
    have hp : 0 < ((2 : ℝ) ^ j)⁻¹ * (1 + |(0 : ℝ)| / (2 : ℝ) ^ j) ^ (-M) := by positivity
    exact nonneg_of_mul_nonneg_left h0 hp
  refine (hb.κ_le w).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hCκ
  refine pow_neg_anti (by positivity) ?_ hM
  have : d / (2 * (2 : ℝ) ^ j) ≤ |w| / (2 : ℝ) ^ j := by
    rw [show d / (2 * (2 : ℝ) ^ j) = (d / 2) / (2 : ℝ) ^ j by ring]
    exact div_le_div_of_nonneg_right hw hL.le
  linarith

end PerTile


section PerTile2

variable {N M Cφ Cκ : ℝ} {j v : ℤ} {φ κ : ℝ → ℂ}

theorem TileBound.nonneg_Cκ (hb : TileBound N M Cφ Cκ j v φ κ) : 0 ≤ Cκ := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have := hb.κ_le 0
  have h0 : 0 ≤ Cκ * (((2 : ℝ) ^ j)⁻¹ * (1 + |(0 : ℝ)| / (2 : ℝ) ^ j) ^ (-M)) := (norm_nonneg _).trans this
  have hp : 0 < ((2 : ℝ) ^ j)⁻¹ * (1 + |(0 : ℝ)| / (2 : ℝ) ^ j) ^ (-M) := by positivity
  exact nonneg_of_mul_nonneg_left h0 hp

theorem TileBound.nonneg_Cφ (hb : TileBound N M Cφ Cκ j v φ κ) : 0 ≤ Cφ := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have := hb.φ_le ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2))
  have h0 : 0 ≤ Cφ * tw N j v ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2)) := (norm_nonneg _).trans this
  have hp : 0 < tw N j v ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2)) := by
    unfold tw; positivity
  exact nonneg_of_mul_nonneg_left h0 hp

/-- Kernel increments along a segment at distance `≥ d/2` from the pole `z`. -/
theorem TileBound.κ_incr (hb : TileBound N M Cφ Cκ j v φ κ) (hM : 0 ≤ M) {x x' z d : ℝ} (hd : 0 ≤ d)
    (_hx : d / 2 ≤ |x - z|) (_hx' : d / 2 ≤ |x' - z|) (hseg : ∀ ξ ∈ Set.uIcc x x', d / 2 ≤ |ξ - z|) :
    ‖κ (x - z) - κ (x' - z)‖ ≤
      Cκ * ((((2 : ℝ) ^ j)⁻¹) ^ 2 * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M)) * |x - x'| := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hdiff : Differentiable ℝ (fun ξ => κ (ξ - z)) := hb.κ_diff.comp (differentiable_id.sub_const z)
  have := norm_sub_le_of_deriv_bound (f := fun ξ => κ (ξ - z)) hdiff (x := x) (x' := x')
    (B := Cκ * ((((2 : ℝ) ^ j)⁻¹) ^ 2 * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M))) (fun ξ hξ => by
      have e : deriv (fun ξ => κ (ξ - z)) ξ = deriv κ (ξ - z) := deriv_comp_sub_const (f := κ) (a := z) (x := ξ)
      rw [e]
      refine (hb.κ'_le (ξ - z)).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hb.nonneg_Cκ
      refine pow_neg_anti (by positivity) ?_ hM
      have : d / (2 * (2 : ℝ) ^ j) ≤ |ξ - z| / (2 : ℝ) ^ j := by
        rw [show d / (2 * (2 : ℝ) ^ j) = (d / 2) / (2 : ℝ) ^ j by ring]
        exact div_le_div_of_nonneg_right (hseg ξ hξ) hL.le
      linarith)
  simpa using this

/-- **First-slot increment of one tile.** -/
theorem TileBound.termA (hb : TileBound N M Cφ Cκ j v φ κ) (hN : 0 ≤ N) (hM : 0 ≤ M) {x x' z : ℝ}
    (hd : 0 < |x - z|) (hδ : 2 * |x - x'| ≤ |x - z|) :
    ‖φ x * κ (x - z) - φ x' * κ (x' - z)‖ ≤
      2 ^ N * Cφ * Cκ * (tw N j v x + tw N j v x') * Hs M |x - z| |x - x'| j := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hCφ := hb.nonneg_Cφ
  have hCκ := hb.nonneg_Cκ
  set L : ℝ := (2 : ℝ) ^ j with hLdef
  set d : ℝ := |x - z| with hddef
  set δ : ℝ := |x - x'| with hδdef
  set E : ℝ := (1 + d / (2 * L)) ^ (-M) with hE
  have hE0 : 0 ≤ E := by positivity
  have hx1 : d / 2 ≤ |x - z| := by linarith
  have hx2 : d / 2 ≤ |x' - z| := by
    have : |x - z| ≤ |x - x'| + |x' - z| := by
      calc |x - z| = |(x - x') + (x' - z)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hseg : ∀ ξ ∈ Set.uIcc x x', d / 2 ≤ |ξ - z| := by
    intro ξ hξ
    have h1 : |x - ξ| ≤ δ := by
      have := Set.abs_sub_right_of_mem_uIcc (a := x') (b := x) (c := ξ) (by rwa [Set.uIcc_comm])
      rwa [hδdef]
    have : |x - z| ≤ |x - ξ| + |ξ - z| := by
      calc |x - z| = |(x - ξ) + (ξ - z)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have k1 := hb.κ_le_half hM hd.le hx1
  have k2 := hb.κ_le_half hM hd.le hx2
  have hφx := hb.φ_le x
  have hφx' := hb.φ_le x'
  have h2N : (1 : ℝ) ≤ 2 ^ N := Real.one_le_rpow (by norm_num) hN
  have htw0 := tw_nonneg N j v x
  have htw0' := tw_nonneg N j v x'
  unfold Hs
  by_cases hLδ : L < δ
  · -- triangle inequality
    have hmin : min L⁻¹ (δ * (L⁻¹) ^ 2) = L⁻¹ := by
      refine min_eq_left ?_
      have hLi : 0 < L⁻¹ := inv_pos.2 hL
      have h1 : 1 ≤ δ * L⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hL]; linarith
      calc L⁻¹ = 1 * L⁻¹ := (one_mul _).symm
        _ ≤ (δ * L⁻¹) * L⁻¹ := mul_le_mul_of_nonneg_right h1 hLi.le
        _ = δ * (L⁻¹) ^ 2 := by ring
    rw [hmin]
    calc ‖φ x * κ (x - z) - φ x' * κ (x' - z)‖ ≤ ‖φ x * κ (x - z)‖ + ‖φ x' * κ (x' - z)‖ := norm_sub_le _ _
      _ ≤ (Cφ * tw N j v x) * (Cκ * (L⁻¹ * E)) + (Cφ * tw N j v x') * (Cκ * (L⁻¹ * E)) := by
          rw [norm_mul, norm_mul]
          gcongr
      _ = Cφ * Cκ * (tw N j v x + tw N j v x') * (L⁻¹ * E) := by ring
      _ ≤ 2 ^ N * Cφ * Cκ * (tw N j v x + tw N j v x') * (L⁻¹ * E) := by
          have h3 : 0 ≤ Cφ * Cκ * (tw N j v x + tw N j v x') * (L⁻¹ * E) := by positivity
          calc Cφ * Cκ * (tw N j v x + tw N j v x') * (L⁻¹ * E)
              = 1 * (Cφ * Cκ * (tw N j v x + tw N j v x') * (L⁻¹ * E)) := (one_mul _).symm
            _ ≤ 2 ^ N * (Cφ * Cκ * (tw N j v x + tw N j v x') * (L⁻¹ * E)) :=
                mul_le_mul_of_nonneg_right h2N h3
            _ = _ := by ring
  · push Not at hLδ
    have hmin : min L⁻¹ (δ * (L⁻¹) ^ 2) = δ * (L⁻¹) ^ 2 := by
      refine min_eq_right ?_
      have hLi : 0 < L⁻¹ := inv_pos.2 hL
      have h1 : δ * L⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_iff₀ hL]; linarith
      calc δ * (L⁻¹) ^ 2 = (δ * L⁻¹) * L⁻¹ := by ring
        _ ≤ 1 * L⁻¹ := mul_le_mul_of_nonneg_right h1 hLi.le
        _ = L⁻¹ := one_mul _
    rw [hmin]
    -- Lipschitz of the cutoff
    have hdφ : ‖φ x - φ x'‖ ≤ (Cφ * L⁻¹ * (2 ^ N * tw N j v x)) * δ := by
      refine norm_sub_le_of_deriv_bound hb.φ_diff (fun ξ hξ => ?_)
      refine (hb.φ'_le ξ).trans ?_
      have hξx : |ξ - x| ≤ L := by
        have : |ξ - x| ≤ δ := by
          have := Set.abs_sub_left_of_mem_uIcc (a := x) (b := x') (c := ξ) hξ
          rwa [abs_sub_comm x' x] at this
        linarith
      have := tw_peetre hN j v hξx
      have hCL : 0 ≤ Cφ * L⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left this hCL
    have hdκ := hb.κ_incr hM hd.le hx1 hx2 hseg
    calc ‖φ x * κ (x - z) - φ x' * κ (x' - z)‖
        = ‖(φ x - φ x') * κ (x - z) + φ x' * (κ (x - z) - κ (x' - z))‖ := by ring_nf
      _ ≤ ‖φ x - φ x'‖ * ‖κ (x - z)‖ + ‖φ x'‖ * ‖κ (x - z) - κ (x' - z)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ((Cφ * L⁻¹ * (2 ^ N * tw N j v x)) * δ) * (Cκ * (L⁻¹ * E)) +
            (Cφ * tw N j v x') * (Cκ * ((L⁻¹) ^ 2 * E) * δ) := by
          gcongr
      _ ≤ 2 ^ N * Cφ * Cκ * (tw N j v x + tw N j v x') * (δ * (L⁻¹) ^ 2 * E) := by
          have h1 : (Cφ * L⁻¹ * (2 ^ N * tw N j v x) * δ) * (Cκ * (L⁻¹ * E)) =
              2 ^ N * Cφ * Cκ * tw N j v x * (δ * (L⁻¹) ^ 2 * E) := by ring
          have h2 : (Cφ * tw N j v x') * (Cκ * ((L⁻¹) ^ 2 * E) * δ) =
              Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E) := by ring
          rw [h1, h2]
          have h3 : 0 ≤ Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E) := by positivity
          have h4 : Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E) ≤
              2 ^ N * (Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E)) := by
            calc _ = 1 * (Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E)) := (one_mul _).symm
              _ ≤ _ := mul_le_mul_of_nonneg_right h2N h3
          calc 2 ^ N * Cφ * Cκ * tw N j v x * (δ * (L⁻¹) ^ 2 * E) +
                Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E)
              ≤ 2 ^ N * Cφ * Cκ * tw N j v x * (δ * (L⁻¹) ^ 2 * E) +
                2 ^ N * (Cφ * Cκ * tw N j v x' * (δ * (L⁻¹) ^ 2 * E)) := add_le_add_right h4 _
            _ = _ := by ring

/-- **Second-slot increment of one tile** (`K(z, x) - K(z, x')`). -/
theorem TileBound.termB (hb : TileBound N M Cφ Cκ j v φ κ) (_hN : 0 ≤ N) (hM : 0 ≤ M) {x x' z : ℝ}
    (hd : 0 < |x - z|) (hδ : 2 * |x - x'| ≤ |x - z|) :
    ‖φ z * (κ (z - x) - κ (z - x'))‖ ≤ 2 * Cφ * Cκ * tw N j v z * Hs M |x - z| |x - x'| j := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hCφ := hb.nonneg_Cφ
  have hCκ := hb.nonneg_Cκ
  set L : ℝ := (2 : ℝ) ^ j with hLdef
  set d : ℝ := |x - z| with hddef
  set δ : ℝ := |x - x'| with hδdef
  set E : ℝ := (1 + d / (2 * L)) ^ (-M) with hE
  have hE0 : 0 ≤ E := by positivity
  have hx1 : d / 2 ≤ |z - x| := by rw [abs_sub_comm]; linarith
  have hx2 : d / 2 ≤ |z - x'| := by
    have : |x - z| ≤ |x - x'| + |x' - z| := by
      calc |x - z| = |(x - x') + (x' - z)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_sub_comm z x']
    linarith
  have hφz := hb.φ_le z
  have htw0 := tw_nonneg N j v z
  have k1 := hb.κ_le_half hM hd.le hx1
  have k2 := hb.κ_le_half hM hd.le hx2
  unfold Hs
  by_cases hLδ : L < δ
  · have hmin : min L⁻¹ (δ * (L⁻¹) ^ 2) = L⁻¹ := by
      refine min_eq_left ?_
      have hLi : 0 < L⁻¹ := inv_pos.2 hL
      have h1 : 1 ≤ δ * L⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hL]; linarith
      calc L⁻¹ = 1 * L⁻¹ := (one_mul _).symm
        _ ≤ (δ * L⁻¹) * L⁻¹ := mul_le_mul_of_nonneg_right h1 hLi.le
        _ = δ * (L⁻¹) ^ 2 := by ring
    rw [hmin, norm_mul]
    calc ‖φ z‖ * ‖κ (z - x) - κ (z - x')‖ ≤ (Cφ * tw N j v z) * (Cκ * (L⁻¹ * E) + Cκ * (L⁻¹ * E)) :=
          mul_le_mul hφz ((norm_sub_le _ _).trans (add_le_add k1 k2)) (norm_nonneg _) (by positivity)
      _ = 2 * Cφ * Cκ * tw N j v z * (L⁻¹ * E) := by ring
  · push Not at hLδ
    have hmin : min L⁻¹ (δ * (L⁻¹) ^ 2) = δ * (L⁻¹) ^ 2 := by
      refine min_eq_right ?_
      have hLi : 0 < L⁻¹ := inv_pos.2 hL
      have h1 : δ * L⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_iff₀ hL]; linarith
      calc δ * (L⁻¹) ^ 2 = (δ * L⁻¹) * L⁻¹ := by ring
        _ ≤ 1 * L⁻¹ := mul_le_mul_of_nonneg_right h1 hLi.le
        _ = L⁻¹ := one_mul _
    rw [hmin, norm_mul]
    have hseg : ∀ ξ ∈ Set.uIcc x x', d / 2 ≤ |ξ - z| := by
      intro ξ hξ
      have h1 : |x - ξ| ≤ δ := by
        have := Set.abs_sub_right_of_mem_uIcc (a := x') (b := x) (c := ξ) (by rwa [Set.uIcc_comm])
        rwa [hδdef]
      have : |x - z| ≤ |x - ξ| + |ξ - z| := by
        calc |x - z| = |(x - ξ) + (ξ - z)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    -- mean value inequality for `ξ ↦ κ (z - ξ)`
    have hdiff : Differentiable ℝ (fun ξ => κ (z - ξ)) := hb.κ_diff.comp (differentiable_const z |>.sub differentiable_id)
    have hmv := norm_sub_le_of_deriv_bound (f := fun ξ => κ (z - ξ)) hdiff (x := x) (x' := x')
      (B := Cκ * ((L⁻¹) ^ 2 * E)) (fun ξ hξ => by
        have e : deriv (fun ξ => κ (z - ξ)) ξ = -deriv κ (z - ξ) := deriv_comp_const_sub (f := κ) (a := z) (x := ξ)
        rw [e, norm_neg]
        refine (hb.κ'_le (z - ξ)).trans ?_
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hCκ
        refine pow_neg_anti (by positivity) ?_ hM
        have : d / (2 * L) ≤ |z - ξ| / L := by
          rw [show d / (2 * L) = (d / 2) / L by ring, abs_sub_comm z ξ]
          exact div_le_div_of_nonneg_right (hseg ξ hξ) hL.le
        linarith)
    calc ‖φ z‖ * ‖κ (z - x) - κ (z - x')‖ ≤ (Cφ * tw N j v z) * (Cκ * ((L⁻¹) ^ 2 * E) * δ) :=
          mul_le_mul hφz hmv (norm_nonneg _) (by positivity)
      _ = Cφ * Cκ * tw N j v z * (δ * (L⁻¹) ^ 2 * E) := by ring
      _ ≤ 2 * Cφ * Cκ * tw N j v z * (δ * (L⁻¹) ^ 2 * E) := by
          have h3 : 0 ≤ Cφ * Cκ * tw N j v z * (δ * (L⁻¹) ^ 2 * E) := by positivity
          calc Cφ * Cκ * tw N j v z * (δ * (L⁻¹) ^ 2 * E)
              ≤ 2 * (Cφ * Cκ * tw N j v z * (δ * (L⁻¹) ^ 2 * E)) := le_mul_of_one_le_left h3 one_le_two
            _ = _ := by ring

end PerTile2


section Sum

variable {ι : Type*}

/-- The kernel `∑_{i ∈ S} φ i x · κ i (x - z)`. -/
def tileKernel (S : Finset ι) (φ κ : ι → ℝ → ℂ) (x z : ℝ) : ℂ := ∑ i ∈ S, φ i x * κ i (x - z)

/-- The CZ constant of a tile sum. -/
def tileCZ (N M Cφ Cκ : ℝ) : ℝ := Cφ * Cκ * latConst N * (4 + 2 ^ (M + 2) * (2 ^ (N + 1) + 2))

theorem tileKernel_size {N M Cφ Cκ : ℝ} (hN : 1 < N) (hM : 2 ≤ M) (S : Finset ι) (j v : ι → ℤ)
    (φ κ : ι → ℝ → ℂ) (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) {x z : ℝ}
    (hxz : x ≠ z) : ‖tileKernel S φ κ x z‖ ≤ Cφ * Cκ * latConst N * 4 / |x - z| := by
  have hd : 0 < |x - z| := abs_pos.2 (sub_ne_zero.2 hxz)
  obtain ⟨hGs, hGb⟩ := scaleSum_size hM hd
  set G : ℤ → ℝ := fun a => Cφ * Cκ * (((2 : ℝ) ^ a)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ a) ^ (-M)) with hG
  have hG0 : ∀ a, 0 ≤ G a := fun a => by
    have := two_zpow_pos' a; simp only [hG]; positivity
  have hGs' : Summable G := hGs.mul_left _
  have h1 : ‖tileKernel S φ κ x z‖ ≤ ∑ i ∈ S, ‖φ i x‖ * ‖κ i (x - z)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
  have h2 : ∑ i ∈ S, ‖φ i x‖ * ‖κ i (x - z)‖ ≤ latConst N * ∑' a, G a := by
    refine sum_tiles_le hN S j v hinj x hG0 hGs' (fun i hi => ?_)
    have h3 := (hb i hi).φ_le x
    have h4 := (hb i hi).κ_le (x - z)
    calc ‖φ i x‖ * ‖κ i (x - z)‖ ≤ (Cφ * tw N (j i) (v i) x) * (Cκ * (((2 : ℝ) ^ j i)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ j i) ^ (-M))) :=
          mul_le_mul h3 h4 (norm_nonneg _) (by have := tw_nonneg N (j i) (v i) x; positivity)
      _ = tw N (j i) (v i) x * G (j i) := by simp only [hG]; ring
  have h5 : ∑' a, G a = Cφ * Cκ * ∑' a : ℤ, ((2 : ℝ) ^ a)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ a) ^ (-M) := tsum_mul_left
  calc ‖tileKernel S φ κ x z‖ ≤ latConst N * ∑' a, G a := h1.trans h2
    _ = latConst N * (Cφ * Cκ * ∑' a : ℤ, ((2 : ℝ) ^ a)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ a) ^ (-M)) := by rw [h5]
    _ ≤ latConst N * (Cφ * Cκ * (4 / |x - z|)) := by
        have := latConst_nonneg hN
        gcongr
    _ = Cφ * Cκ * latConst N * 4 / |x - z| := by ring

theorem tileKernel_smooth {N M Cφ Cκ : ℝ} (hN : 1 < N) (hM : 3 ≤ M) (S : Finset ι) (j v : ι → ℤ)
    (φ κ : ι → ℝ → ℂ) (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) {x x' z : ℝ}
    (hd : 0 < |x - z|) (hδ : 2 * |x - x'| ≤ |x - z|) :
    ‖tileKernel S φ κ x z - tileKernel S φ κ x' z‖ + ‖tileKernel S φ κ z x - tileKernel S φ κ z x'‖ ≤
      tileCZ N M Cφ Cκ * |x - x'| / |x - z| ^ 2 := by
  have hN0 : 0 ≤ N := by linarith
  have hM0 : 0 ≤ M := by linarith
  set d := |x - z| with hddef
  set δ := |x - x'| with hδdef
  have hδ0 : 0 ≤ δ := abs_nonneg _
  obtain ⟨hHs, hHb⟩ := scaleSum_smooth hM hd hδ0 hδ
  have hH0 : ∀ a, 0 ≤ Hs M d δ a := fun a => Hs_nonneg M d δ hd.le hδ0 a
  have hHs' : Summable (Hs M d δ) := hHs
  set T : ℝ := ∑' a, Hs M d δ a with hT
  have hT0 : 0 ≤ T := tsum_nonneg hH0
  have hTb : T ≤ 2 ^ M * 4 * (δ / d ^ 2) := hHb
  have hlat := latConst_nonneg hN
  -- first slot
  have hA : ‖tileKernel S φ κ x z - tileKernel S φ κ x' z‖ ≤
      2 ^ N * Cφ * Cκ * (latConst N * T + latConst N * T) := by
    have e : tileKernel S φ κ x z - tileKernel S φ κ x' z =
        ∑ i ∈ S, (φ i x * κ i (x - z) - φ i x' * κ i (x' - z)) := by
      unfold tileKernel; rw [Finset.sum_sub_distrib]
    rw [e]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ S, ‖φ i x * κ i (x - z) - φ i x' * κ i (x' - z)‖
        ≤ ∑ i ∈ S, 2 ^ N * Cφ * Cκ * (tw N (j i) (v i) x * Hs M d δ (j i) + tw N (j i) (v i) x' * Hs M d δ (j i)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := (hb i hi).termA hN0 hM0 hd hδ
          refine this.trans (le_of_eq ?_)
          ring
      _ = 2 ^ N * Cφ * Cκ * (∑ i ∈ S, tw N (j i) (v i) x * Hs M d δ (j i) +
            ∑ i ∈ S, tw N (j i) (v i) x' * Hs M d δ (j i)) := by
          rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ 2 ^ N * Cφ * Cκ * (latConst N * T + latConst N * T) := by
          have h1 := sum_tiles_le hN S j v hinj x hH0 hHs' (F := fun i => tw N (j i) (v i) x * Hs M d δ (j i))
            (fun i _ => le_refl _)
          have h2 := sum_tiles_le hN S j v hinj x' hH0 hHs' (F := fun i => tw N (j i) (v i) x' * Hs M d δ (j i))
            (fun i _ => le_refl _)
          have : 0 ≤ 2 ^ N * Cφ * Cκ := by positivity
          gcongr
  -- second slot
  have hB : ‖tileKernel S φ κ z x - tileKernel S φ κ z x'‖ ≤ 2 * Cφ * Cκ * (latConst N * T) := by
    have e : tileKernel S φ κ z x - tileKernel S φ κ z x' =
        ∑ i ∈ S, φ i z * (κ i (z - x) - κ i (z - x')) := by
      unfold tileKernel; rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ S, ‖φ i z * (κ i (z - x) - κ i (z - x'))‖
        ≤ ∑ i ∈ S, 2 * Cφ * Cκ * (tw N (j i) (v i) z * Hs M d δ (j i)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := (hb i hi).termB hN0 hM0 hd hδ
          refine this.trans (le_of_eq ?_)
          ring
      _ = 2 * Cφ * Cκ * ∑ i ∈ S, tw N (j i) (v i) z * Hs M d δ (j i) := by rw [← Finset.mul_sum]
      _ ≤ 2 * Cφ * Cκ * (latConst N * T) := by
          have h1 := sum_tiles_le hN S j v hinj z hH0 hHs' (F := fun i => tw N (j i) (v i) z * Hs M d δ (j i))
            (fun i _ => le_refl _)
          have : 0 ≤ 2 * Cφ * Cκ := by positivity
          gcongr
  calc _ ≤ 2 ^ N * Cφ * Cκ * (latConst N * T + latConst N * T) + 2 * Cφ * Cκ * (latConst N * T) := add_le_add hA hB
    _ = Cφ * Cκ * latConst N * ((2 ^ (N + 1) + 2) * T) := by
        rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]; ring
    _ ≤ Cφ * Cκ * latConst N * ((2 ^ (N + 1) + 2) * (2 ^ M * 4 * (δ / d ^ 2))) := by
        have : 0 ≤ Cφ * Cκ * latConst N := by positivity
        have h2 : (0 : ℝ) ≤ 2 ^ (N + 1) + 2 := by positivity
        gcongr
    _ ≤ tileCZ N M Cφ Cκ * δ / d ^ 2 := by
        unfold tileCZ
        have h4 : (2 : ℝ) ^ (M + 2) = 2 ^ M * 4 := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
        have : 0 ≤ Cφ * Cκ * latConst N * (2 ^ (N + 1) + 2) * (2 ^ M * 4) * (δ / d ^ 2) := by positivity
        have h5 : 0 ≤ Cφ * Cκ * latConst N * 4 * δ / d ^ 2 := by positivity
        rw [h4]
        have e : Cφ * Cκ * latConst N * (4 + 2 ^ M * 4 * (2 ^ (N + 1) + 2)) * δ / d ^ 2 =
            Cφ * Cκ * latConst N * ((2 ^ (N + 1) + 2) * (2 ^ M * 4 * (δ / d ^ 2))) + Cφ * Cκ * latConst N * 4 * δ / d ^ 2 := by
          ring
        rw [e]
        linarith



theorem isCZKernel_tileKernel {N M Cφ Cκ : ℝ} (hN : 1 < N) (hM : 3 ≤ M) (S : Finset ι) (j v : ι → ℤ)
    (φ κ : ι → ℝ → ℂ) (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) :
    CZ.IsCZKernel (tileCZ N M Cφ Cκ) (tileKernel S φ κ) := by
  have hhat : 0 ≤ tileCZ N M Cφ Cκ := by
    unfold tileCZ; have := latConst_nonneg hN; positivity
  refine ⟨fun x z hxz => ?_, fun x x' z hxz => ?_⟩
  · refine (tileKernel_size hN (by linarith) S j v φ κ hb hinj hCφ hCκ hxz).trans ?_
    unfold tileCZ
    have := latConst_nonneg hN
    have : 0 ≤ Cφ * Cκ * latConst N := by positivity
    have hp : 0 < |x - z| := abs_pos.2 (sub_ne_zero.2 hxz)
    rw [div_le_div_iff_of_pos_right hp]
    have : (0 : ℝ) ≤ 2 ^ (M + 2) * (2 ^ (N + 1) + 2) := by positivity
    nlinarith [mul_nonneg ‹0 ≤ Cφ * Cκ * latConst N› this]
  · by_cases hxz' : |x - x'| = 0
    · have : x = x' := by rwa [abs_eq_zero, sub_eq_zero] at hxz'
      subst this
      simp
    · have hδpos : 0 < |x - x'| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxz')
      have hd : 0 < |x - z| := by linarith
      exact tileKernel_smooth hN hM S j v φ κ hb hinj hCφ hCκ hd hxz

theorem continuous_tileKernel (S : Finset ι) (φ κ : ι → ℝ → ℂ) (hφ : ∀ i ∈ S, Continuous (φ i))
    (hκ : ∀ i ∈ S, Continuous (κ i)) :
    Continuous (fun p : ℝ × ℝ => tileKernel S φ κ p.1 p.2) := by
  unfold tileKernel
  refine continuous_finsetSum _ fun i hi => ?_
  exact ((hφ i hi).comp continuous_fst).mul ((hκ i hi).comp (continuous_fst.sub continuous_snd))

theorem bounded_tileKernel {N M Cφ Cκ : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (S : Finset ι) (j v : ι → ℤ)
    (φ κ : ι → ℝ → ℂ) (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i)) :
    ∃ B : ℝ, ∀ x z, ‖tileKernel S φ κ x z‖ ≤ B := by
  refine ⟨∑ i ∈ S, Cφ * (Cκ * ((2 : ℝ) ^ j i)⁻¹), fun x z => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul]
  have hCφ := (hb i hi).nonneg_Cφ
  have hCκ := (hb i hi).nonneg_Cκ
  have hL : (0 : ℝ) < (2 : ℝ) ^ j i := zpow_pos (by norm_num) _
  have h1 := (hb i hi).φ_le x
  have h2 := (hb i hi).κ_le (x - z)
  have h3 := tw_le_one hN (j i) (v i) x
  have h4 : (1 + |x - z| / (2 : ℝ) ^ j i) ^ (-M) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by have := div_nonneg (abs_nonneg (x - z)) hL.le; linarith) (by linarith)
  calc ‖φ i x‖ * ‖κ i (x - z)‖ ≤ (Cφ * tw N (j i) (v i) x) * (Cκ * (((2 : ℝ) ^ j i)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ j i) ^ (-M))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by have := tw_nonneg N (j i) (v i) x; positivity)
    _ ≤ Cφ * 1 * (Cκ * (((2 : ℝ) ^ j i)⁻¹ * 1)) := by
        have := tw_nonneg N (j i) (v i) x
        have h5 : 0 ≤ ((2 : ℝ) ^ j i)⁻¹ := by positivity
        have h6 : 0 ≤ (1 + |x - z| / (2 : ℝ) ^ j i) ^ (-M) := by positivity
        gcongr
    _ = Cφ * (Cκ * ((2 : ℝ) ^ j i)⁻¹) := by ring

end Sum

end PrimeBHT.TimeFrequency.X2
