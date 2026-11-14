module

public import PrimeBHT.TimeFrequency.X2.EngTail.CZKernel

/-!
# X2, node B5: pointwise bounds for the kernel of a sub-family of tiles

For a finite family `S` of tiles with `TileBound` data (injective labels `(j, v)`), `K_S(x, z) = ∑_{i ∈ S} φ_i(x) κ_i(x - z)`:

* `sum_near_le`: if every tile has scale `2^{j i} ≥ δ` or distance `|c_i - z| ≥ δ` from `z`, then
  `∑_{i ∈ S} ‖φ_i(x) κ_i(x - z)‖ ≤ C/δ` (no cancellation);
* `sum_tail_le`: for the tiles `i` of a dyadic interval `L` (`j i ≤ jL`, `|c_i - c_L| ≤ |L|/2`) and `|z - c_L| ≥ 3|L|/2`,
  `∑_i ‖φ_i(x) κ_i(x - z)‖ ≤ C |L|⁻¹ (1 + |z - c_L|/|L|)^{-M} (1 + |x - c_L|/|L|)^{-2}` (`N ≥ M + 4`);
* `kernel_atom_le`: the atom kernel bound `‖K_S(x, z) - K_S(x, c)‖ ≤ C δ⁻¹ (1 + |x - c|/δ)^{-2}` for `|z - c| ≤ δ/2` and
  tiles with scale `≥ δ` or `|c_i - c| ≥ 3δ/2` (near zone by `sum_near_le`, far zone by the CZ smoothness `tileKernel_smooth`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Two-factor decay: `(1 + t/ℓ)^{-M} (1 + a/ℓ)^{-N} ≤ (1 + r/ℓ)^{-p} (1 + a/ℓ)^{-(N-p)}` for `0 ≤ p ≤ M`, `r ≤ t + a`. -/
theorem prod_decay_le {M N p t a r ℓ : ℝ} (hp : 0 ≤ p) (hpM : p ≤ M) (hℓ : 0 < ℓ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hr0 : 0 ≤ r) (hr : r ≤ t + a) :
    (1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N) ≤ (1 + r / ℓ) ^ (-p) * (1 + a / ℓ) ^ (-(N - p)) := by
  have hT : 1 ≤ 1 + t / ℓ := by have := div_nonneg ht hℓ.le; linarith
  have hA : 1 ≤ 1 + a / ℓ := by have := div_nonneg ha hℓ.le; linarith
  have hT0 : 0 < 1 + t / ℓ := by linarith
  have hA0 : 0 < 1 + a / ℓ := by linarith
  have h1 : (1 + t / ℓ) ^ (-M) ≤ (1 + t / ℓ) ^ (-p) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have h2 : (1 + a / ℓ) ^ (-N) = (1 + a / ℓ) ^ (-p) * (1 + a / ℓ) ^ (-(N - p)) := by
    rw [← Real.rpow_add hA0]; congr 1; ring
  have h3 : (1 + r / ℓ) ≤ (1 + t / ℓ) * (1 + a / ℓ) := by
    have : r / ℓ ≤ t / ℓ + a / ℓ := by rw [← add_div]; exact div_le_div_of_nonneg_right hr hℓ.le
    linarith [mul_nonneg (div_nonneg ht hℓ.le) (div_nonneg ha hℓ.le)]
  have hr1 : 0 < 1 + r / ℓ := by have := div_nonneg hr0 hℓ.le; linarith
  have h4 : ((1 + t / ℓ) * (1 + a / ℓ)) ^ (-p) ≤ (1 + r / ℓ) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hr1 h3 (by linarith)
  have hq1 : 0 ≤ (1 + a / ℓ) ^ (-(N - p)) := by positivity
  calc (1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N)
      ≤ (1 + t / ℓ) ^ (-p) * ((1 + a / ℓ) ^ (-p) * (1 + a / ℓ) ^ (-(N - p))) := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((1 + t / ℓ) ^ (-p) * (1 + a / ℓ) ^ (-p)) * (1 + a / ℓ) ^ (-(N - p)) := by ring
    _ = ((1 + t / ℓ) * (1 + a / ℓ)) ^ (-p) * (1 + a / ℓ) ^ (-(N - p)) := by
        rw [Real.mul_rpow hT0.le hA0.le]
    _ ≤ (1 + r / ℓ) ^ (-p) * (1 + a / ℓ) ^ (-(N - p)) := mul_le_mul_of_nonneg_right h4 hq1

/-- The product bound of one tile. -/
theorem TileBound.term_le {N M Cφ Cκ : ℝ} {j v : ℤ} {φ κ : ℝ → ℂ} (hb : TileBound N M Cφ Cκ j v φ κ) (x w : ℝ) :
    ‖φ x * κ w‖ ≤ Cφ * Cκ * ((2 : ℝ) ^ j)⁻¹ *
      ((1 + |w| / (2 : ℝ) ^ j) ^ (-M) * (1 + |x - (2 : ℝ) ^ j * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ j) ^ (-N)) := by
  rw [norm_mul]
  have h1 := hb.φ_le x
  have h2 := hb.κ_le w
  have hCφ := hb.nonneg_Cφ
  have hCκ := hb.nonneg_Cκ
  have h3 := tw_nonneg N j v x
  calc ‖φ x‖ * ‖κ w‖ ≤ (Cφ * tw N j v x) * (Cκ * (((2 : ℝ) ^ j)⁻¹ * (1 + |w| / (2 : ℝ) ^ j) ^ (-M))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by unfold tw; ring

/-! ### Near zone -/

/-- The real-variable form of the per-tile bound in the near zone. -/
theorem tile_near_real {M N ℓ a t δ r : ℝ} (hM : 2 ≤ M) (hℓ : 0 < ℓ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hδ : 0 < δ)
    (hr0 : 0 ≤ r) (hr : r ≤ t + a) (hsep : δ ≤ ℓ ∨ δ ≤ r) :
    ℓ⁻¹ * ((1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N)) ≤
      (1 + a / ℓ) ^ (-(N - 2)) * (4 * (ℓ⁻¹ * (1 + δ / ℓ) ^ (-(2 : ℝ)))) := by
  have hT : 1 ≤ 1 + t / ℓ := by have := div_nonneg ht hℓ.le; linarith
  have hA : 1 ≤ 1 + a / ℓ := by have := div_nonneg ha hℓ.le; linarith
  have hD0 : 0 < 1 + δ / ℓ := by have := div_nonneg hδ.le hℓ.le; linarith
  have hli : 0 < ℓ⁻¹ := inv_pos.2 hℓ
  rcases hsep with h | h
  · have hD2 : 1 + δ / ℓ ≤ 2 := by
      have : δ / ℓ ≤ 1 := by rw [div_le_one hℓ]; exact h
      linarith
    have hq : (1 : ℝ) / 4 ≤ (1 + δ / ℓ) ^ (-(2 : ℝ)) := by
      have := Real.rpow_le_rpow_of_nonpos hD0 hD2 (by norm_num : (-(2 : ℝ)) ≤ 0)
      refine le_trans (le_of_eq ?_) this
      rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
    have h1 : (1 + t / ℓ) ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
    have h2 : (1 + a / ℓ) ^ (-N) ≤ (1 + a / ℓ) ^ (-(N - 2)) :=
      Real.rpow_le_rpow_of_exponent_le hA (by linarith)
    have h3 : 0 ≤ (1 + t / ℓ) ^ (-M) := by positivity
    have h4 : 0 ≤ (1 + a / ℓ) ^ (-(N - 2)) := by positivity
    calc ℓ⁻¹ * ((1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N))
        ≤ ℓ⁻¹ * (1 * (1 + a / ℓ) ^ (-(N - 2))) := by
          gcongr
      _ = (1 + a / ℓ) ^ (-(N - 2)) * (ℓ⁻¹) := by ring
      _ ≤ (1 + a / ℓ) ^ (-(N - 2)) * (4 * (ℓ⁻¹ * (1 + δ / ℓ) ^ (-(2 : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ h4
          linarith [mul_le_mul_of_nonneg_left hq hli.le]
  · have hpd := prod_decay_le (M := M) (N := N) (p := 2) (by norm_num) hM hℓ ht ha hr0 hr
    have hr1 : 0 < 1 + r / ℓ := by have := div_nonneg hr0 hℓ.le; linarith
    have hmono : (1 + r / ℓ) ^ (-(2 : ℝ)) ≤ (1 + δ / ℓ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hD0 (by have := div_le_div_of_nonneg_right h hℓ.le; linarith)
        (by norm_num : (-(2 : ℝ)) ≤ 0)
    have h4 : 0 ≤ (1 + a / ℓ) ^ (-(N - 2)) := by positivity
    have h5 : 0 ≤ (1 + δ / ℓ) ^ (-(2 : ℝ)) := by positivity
    calc ℓ⁻¹ * ((1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N))
        ≤ ℓ⁻¹ * ((1 + r / ℓ) ^ (-(2 : ℝ)) * (1 + a / ℓ) ^ (-(N - 2))) := by gcongr
      _ ≤ ℓ⁻¹ * ((1 + δ / ℓ) ^ (-(2 : ℝ)) * (1 + a / ℓ) ^ (-(N - 2))) := by gcongr
      _ = (1 + a / ℓ) ^ (-(N - 2)) * (ℓ⁻¹ * (1 + δ / ℓ) ^ (-(2 : ℝ))) := by ring
      _ ≤ (1 + a / ℓ) ^ (-(N - 2)) * (4 * (ℓ⁻¹ * (1 + δ / ℓ) ^ (-(2 : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ h4
          have : 0 ≤ ℓ⁻¹ * (1 + δ / ℓ) ^ (-(2 : ℝ)) := by positivity
          linarith

/-! ### Tail -/

/-- The real-variable form of the per-tile bound in the tail zone: the tile has scale `ℓ ≤ L`, its centre is within `L/2` of the
centre of `L`, the source point `z` is at distance `dz ≥ 3L/2` from the centre of `L`. -/
theorem tile_tail_real {M N ℓ L a t ρ dz dx : ℝ} (hM : 3 ≤ M) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ t + a) (hdz : 3 * L / 2 ≤ dz) (hρdz : dz - L / 2 ≤ ρ) (hdx0 : 0 ≤ dx)
    (hadx : dx - L / 2 ≤ a) :
    ℓ⁻¹ * ((1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N)) ≤
      (1 + a / ℓ) ^ (-(N - M - 2)) *
        (4 * (5 / 2) ^ M * (L⁻¹ * ((1 + dz / L) ^ (-M) * (1 + dx / L) ^ (-(2 : ℝ)))) * (ℓ / L)) := by
  have hL : 0 < L := lt_of_lt_of_le hℓ hℓL
  have hA : 1 ≤ 1 + a / ℓ := by have := div_nonneg ha hℓ.le; linarith
  have hA0 : 0 < 1 + a / ℓ := by linarith
  have hdz0 : 0 ≤ dz := by linarith
  have hDZ : 0 < 1 + dz / L := by have := div_nonneg hdz0 hL.le; linarith
  have hDX : 0 < 1 + dx / L := by have := div_nonneg hdx0 hL.le; linarith
  have step1 := prod_decay_le (M := M) (N := N) (p := M) (by linarith) le_rfl hℓ ht ha hρ0 hρ
  -- lower bound of `1 + ρ/ℓ`
  have hlow : 2 / 5 * (L / ℓ * (1 + dz / L)) ≤ 1 + ρ / ℓ := by
    have e : 2 / 5 * (L / ℓ * (1 + dz / L)) = (2 / 5 * (L + dz)) / ℓ := by field_simp
    rw [e]
    have h1 : (2 / 5 * (L + dz)) / ℓ ≤ ρ / ℓ := div_le_div_of_nonneg_right (by linarith) hℓ.le
    have h2 : 0 ≤ 1 := by norm_num
    linarith
  have hpos : 0 < 2 / 5 * (L / ℓ * (1 + dz / L)) := by positivity
  have h2 : (1 + ρ / ℓ) ^ (-M) ≤ (2 / 5 * (L / ℓ * (1 + dz / L))) ^ (-M) :=
    Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
  have h3 : (2 / 5 * (L / ℓ * (1 + dz / L))) ^ (-M) = (5 / 2) ^ M * ((ℓ / L) ^ M * (1 + dz / L) ^ (-M)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) hDZ.le]
    have e1 : (2 / 5 : ℝ) ^ (-M) = (5 / 2) ^ M := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]; norm_num
    have e2 : (L / ℓ) ^ (-M) = (ℓ / L) ^ M := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    rw [e1, e2]
  -- the `x`-decay
  have hx1 : (1 + a / ℓ) ^ (-(N - M)) = (1 + a / ℓ) ^ (-(2 : ℝ)) * (1 + a / ℓ) ^ (-(N - M - 2)) := by
    rw [← Real.rpow_add hA0]; congr 1; ring
  have hx2 : (1 + a / ℓ) ^ (-(2 : ℝ)) ≤ (1 + a / L) ^ (-(2 : ℝ)) := by
    have : 1 + a / L ≤ 1 + a / ℓ := by
      have := div_le_div_of_nonneg_left ha hℓ hℓL
      linarith
    exact Real.rpow_le_rpow_of_nonpos (by have := div_nonneg ha hL.le; linarith) this (by norm_num)
  have hx3 : (1 + a / L) ^ (-(2 : ℝ)) ≤ 4 * (1 + dx / L) ^ (-(2 : ℝ)) := by
    have hle : 1 / 2 * (1 + dx / L) ≤ 1 + a / L := by
      have : dx / L - 1 / 2 ≤ a / L := by
        have e : dx / L - 1 / 2 = (dx - L / 2) / L := by field_simp
        rw [e]; exact div_le_div_of_nonneg_right hadx hL.le
      have : 0 ≤ dx / L := div_nonneg hdx0 hL.le
      linarith
    have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 / 2 * (1 + dx / L)) hle (by norm_num : (-(2 : ℝ)) ≤ 0)
    refine this.trans (le_of_eq ?_)
    rw [Real.mul_rpow (by norm_num) hDX.le]
    have : ((1 : ℝ) / 2) ^ (-(2 : ℝ)) = 4 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
    rw [this]
  -- the scale factor
  have hy0 : 0 < ℓ / L := by positivity
  have hy1 : ℓ / L ≤ 1 := by rw [div_le_one hL]; exact hℓL
  have hym : ℓ⁻¹ * (ℓ / L) ^ M ≤ L⁻¹ * (ℓ / L) := by
    have e : (ℓ / L) ^ M = (ℓ / L) ^ (M - 1) * (ℓ / L) := by
      rw [← Real.rpow_add_one hy0.ne']; congr 1; ring
    have e2 : ℓ⁻¹ * ((ℓ / L) ^ (M - 1) * (ℓ / L)) = (ℓ / L) ^ (M - 1) * L⁻¹ := by field_simp
    rw [e, e2]
    have h1 : (ℓ / L) ^ (M - 1) ≤ (ℓ / L) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
    rw [Real.rpow_one] at h1
    exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left h1 (inv_pos.2 hL).le)
  have hpd : 0 ≤ (1 + a / ℓ) ^ (-(N - M - 2)) := by positivity
  have hDZm : 0 ≤ (1 + dz / L) ^ (-M) := by positivity
  have hDXm : 0 ≤ (1 + dx / L) ^ (-(2 : ℝ)) := by positivity
  have hℓi : 0 < ℓ⁻¹ := inv_pos.2 hℓ
  have hρM : 0 ≤ (1 + ρ / ℓ) ^ (-M) := by positivity
  calc ℓ⁻¹ * ((1 + t / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-N))
      ≤ ℓ⁻¹ * ((1 + ρ / ℓ) ^ (-M) * (1 + a / ℓ) ^ (-(N - M))) := by gcongr
    _ ≤ ℓ⁻¹ * (((5 / 2) ^ M * ((ℓ / L) ^ M * (1 + dz / L) ^ (-M))) *
          ((1 + a / ℓ) ^ (-(2 : ℝ)) * (1 + a / ℓ) ^ (-(N - M - 2)))) := by
        rw [hx1, ← h3]
        gcongr
    _ ≤ ℓ⁻¹ * (((5 / 2) ^ M * ((ℓ / L) ^ M * (1 + dz / L) ^ (-M))) *
          ((4 * (1 + dx / L) ^ (-(2 : ℝ))) * (1 + a / ℓ) ^ (-(N - M - 2)))) := by
        gcongr
        exact hx2.trans hx3
    _ = (1 + a / ℓ) ^ (-(N - M - 2)) * (4 * (5 / 2) ^ M * ((1 + dz / L) ^ (-M) * (1 + dx / L) ^ (-(2 : ℝ))) *
          (ℓ⁻¹ * (ℓ / L) ^ M)) := by ring
    _ ≤ (1 + a / ℓ) ^ (-(N - M - 2)) * (4 * (5 / 2) ^ M * ((1 + dz / L) ^ (-M) * (1 + dx / L) ^ (-(2 : ℝ))) *
          (L⁻¹ * (ℓ / L))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hym (by positivity)) hpd
    _ = (1 + a / ℓ) ^ (-(N - M - 2)) *
        (4 * (5 / 2) ^ M * (L⁻¹ * ((1 + dz / L) ^ (-M) * (1 + dx / L) ^ (-(2 : ℝ)))) * (ℓ / L)) := by ring

section Sums

variable {ι : Type*}

/-- **Near zone, no cancellation**: if every tile has scale `≥ δ` or distance `≥ δ` from `z`, then
`∑ ‖φ_i(x) κ_i(x - z)‖ ≤ 16 Cφ Cκ latConst(N-2)/δ`. -/
theorem sum_near_le {N M Cφ Cκ : ℝ} (hN : 3 < N) (hM : 2 ≤ M) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ)
    (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) {δ : ℝ} (hδ : 0 < δ) {z : ℝ}
    (hsep : ∀ i ∈ S, δ ≤ (2 : ℝ) ^ (j i) ∨ δ ≤ |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - z|) (x : ℝ) :
    ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ ≤ 16 * (Cφ * Cκ) * latConst (N - 2) / δ := by
  have hN2 : 1 < N - 2 := by linarith
  obtain ⟨hGs, hGb⟩ := scaleSum_size (M := 2) le_rfl hδ
  set G : ℤ → ℝ := fun a => 4 * (Cφ * Cκ) * (((2 : ℝ) ^ a)⁻¹ * (1 + δ / (2 : ℝ) ^ a) ^ (-(2 : ℝ))) with hG
  have hG0 : ∀ a, 0 ≤ G a := fun a => by
    have := two_zpow_pos' a; simp only [hG]; positivity
  have hGs' : Summable G := hGs.mul_left _
  have h2 : ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ ≤ latConst (N - 2) * ∑' a, G a := by
    refine sum_tiles_le hN2 S j v hinj x hG0 hGs' (fun i hi => ?_)
    have hL : (0 : ℝ) < (2 : ℝ) ^ (j i) := two_zpow_pos' _
    have hterm := (hb i hi).term_le x (x - z)
    have hreal := tile_near_real (M := M) (N := N) (ℓ := (2 : ℝ) ^ (j i))
      (a := |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)|) (t := |x - z|) (δ := δ)
      (r := |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - z|) hM hL (abs_nonneg _) (abs_nonneg _) hδ (abs_nonneg _)
      (by
        calc |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - z|
            = |(x - z) - (x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2))| := by congr 1; ring
          _ ≤ |x - z| + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| := abs_sub _ _
          _ = _ := by ring)
      (hsep i hi)
    calc ‖φ i x * κ i (x - z)‖
        ≤ Cφ * Cκ * ((2 : ℝ) ^ (j i))⁻¹ *
          ((1 + |x - z| / (2 : ℝ) ^ (j i)) ^ (-M) *
            (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N)) := hterm
      _ = (Cφ * Cκ) * (((2 : ℝ) ^ (j i))⁻¹ *
          ((1 + |x - z| / (2 : ℝ) ^ (j i)) ^ (-M) *
            (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N))) := by ring
      _ ≤ (Cφ * Cκ) * ((1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-(N - 2)) *
          (4 * (((2 : ℝ) ^ (j i))⁻¹ * (1 + δ / (2 : ℝ) ^ (j i)) ^ (-(2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left hreal (mul_nonneg hCφ hCκ)
      _ = (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-(N - 2)) * G (j i) := by
          simp only [hG]; ring
  have h5 : ∑' a, G a = 4 * (Cφ * Cκ) * ∑' a : ℤ, ((2 : ℝ) ^ a)⁻¹ * (1 + δ / (2 : ℝ) ^ a) ^ (-(2 : ℝ)) :=
    tsum_mul_left
  have hlat := latConst_nonneg hN2
  calc ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ ≤ latConst (N - 2) * ∑' a, G a := h2
    _ = latConst (N - 2) * (4 * (Cφ * Cκ) *
          ∑' a : ℤ, ((2 : ℝ) ^ a)⁻¹ * (1 + δ / (2 : ℝ) ^ a) ^ (-(2 : ℝ))) := by rw [h5]
    _ ≤ latConst (N - 2) * (4 * (Cφ * Cκ) * (4 / δ)) := by
        have : 0 ≤ 4 * (Cφ * Cκ) := by positivity
        gcongr
    _ = 16 * (Cφ * Cκ) * latConst (N - 2) / δ := by ring

/-- **Tail zone**: the tiles of the dyadic interval `L` (`j i ≤ jL`, centre within `|L|/2` of the centre of `L`) see a source
point `z` with `|z - c_L| ≥ 3|L|/2` with total size `C |L|⁻¹ (1 + |z - c_L|/|L|)^{-M} (1 + |x - c_L|/|L|)^{-2}` (`N ≥ M + 4`). -/
theorem sum_tail_le {N M Cφ Cκ : ℝ} (hM : 3 ≤ M) (hN : M + 4 ≤ N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ)
    (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) {jL vL : ℤ}
    (hS : ∀ i ∈ S, j i ≤ jL ∧
      |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - (2 : ℝ) ^ jL * ((vL : ℝ) + 1 / 2)| ≤ (2 : ℝ) ^ jL / 2)
    {z : ℝ} (hz : 3 * (2 : ℝ) ^ jL / 2 ≤ |z - (2 : ℝ) ^ jL * ((vL : ℝ) + 1 / 2)|) (x : ℝ) :
    ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ ≤ 16 * (Cφ * Cκ) * (5 / 2) ^ M * latConst (N - M - 2) *
      (((2 : ℝ) ^ jL)⁻¹ * ((1 + |z - (2 : ℝ) ^ jL * ((vL : ℝ) + 1 / 2)| / (2 : ℝ) ^ jL) ^ (-M) *
        (1 + |x - (2 : ℝ) ^ jL * ((vL : ℝ) + 1 / 2)| / (2 : ℝ) ^ jL) ^ (-(2 : ℝ)))) := by
  have hN2 : 1 < N - M - 2 := by linarith
  have hL : (0 : ℝ) < (2 : ℝ) ^ jL := two_zpow_pos' jL
  set L : ℝ := (2 : ℝ) ^ jL with hLdef
  set cL : ℝ := (2 : ℝ) ^ jL * ((vL : ℝ) + 1 / 2) with hcL
  obtain ⟨hGs, hGb⟩ := CZ.hasSum_le_min_two_zpow (a := L⁻¹) (b := L) (inv_pos.2 hL) hL
  set K' : ℝ := 4 * (5 / 2) ^ M * (Cφ * Cκ) *
    (L⁻¹ * ((1 + |z - cL| / L) ^ (-M) * (1 + |x - cL| / L) ^ (-(2 : ℝ)))) with hK'
  have hK'0 : 0 ≤ K' := by simp only [hK']; positivity
  set G : ℤ → ℝ := fun a => K' * min (L⁻¹ * (2 : ℝ) ^ a) (L * (2 : ℝ) ^ (-a)) with hG
  have hG0 : ∀ a, 0 ≤ G a := fun a => by
    have := two_zpow_pos' a
    have := two_zpow_pos' (-a)
    simp only [hG]; positivity
  have hGs' : Summable G := hGs.mul_left _
  have h2 : ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ ≤ latConst (N - M - 2) * ∑' a, G a := by
    refine sum_tiles_le hN2 S j v hinj x hG0 hGs' (fun i hi => ?_)
    obtain ⟨hji, hci⟩ := hS i hi
    have hℓ : (0 : ℝ) < (2 : ℝ) ^ (j i) := two_zpow_pos' _
    have hℓL : (2 : ℝ) ^ (j i) ≤ L := zpow_le_zpow_right₀ (by norm_num) hji
    have hterm := (hb i hi).term_le x (x - z)
    have hreal := tile_tail_real (M := M) (N := N) (ℓ := (2 : ℝ) ^ (j i)) (L := L)
      (a := |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)|) (t := |x - z|)
      (ρ := |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)|) (dz := |z - cL|) (dx := |x - cL|) hM hℓ hℓL
      (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (by
        calc |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)|
            = |(z - x) + (x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2))| := by congr 1; ring
          _ ≤ |z - x| + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| := abs_add_le _ _
          _ = _ := by rw [abs_sub_comm z x])
      hz
      (by
        have : |z - cL| ≤ |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| +
            |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - cL| := by
          calc |z - cL| = |(z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)) + ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - cL)| := by
                congr 1; ring
            _ ≤ _ := abs_add_le _ _
        linarith)
      (abs_nonneg _)
      (by
        have : |x - cL| ≤ |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| +
            |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - cL| := by
          calc |x - cL| = |(x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)) + ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - cL)| := by
                congr 1; ring
            _ ≤ _ := abs_add_le _ _
        linarith)
    have hmin : (2 : ℝ) ^ (j i) / L ≤ min (L⁻¹ * (2 : ℝ) ^ (j i)) (L * (2 : ℝ) ^ (-(j i))) := by
      refine le_min (le_of_eq (by ring)) ?_
      rw [zpow_neg, div_le_iff₀ hL]
      have : L * ((2 : ℝ) ^ (j i))⁻¹ * L = L * L * ((2 : ℝ) ^ (j i))⁻¹ := by ring
      rw [this, ← div_eq_mul_inv, le_div_iff₀ hℓ]
      exact mul_le_mul hℓL hℓL hℓ.le hL.le
    calc ‖φ i x * κ i (x - z)‖
        ≤ Cφ * Cκ * ((2 : ℝ) ^ (j i))⁻¹ *
          ((1 + |x - z| / (2 : ℝ) ^ (j i)) ^ (-M) *
            (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N)) := hterm
      _ = (Cφ * Cκ) * (((2 : ℝ) ^ (j i))⁻¹ *
          ((1 + |x - z| / (2 : ℝ) ^ (j i)) ^ (-M) *
            (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N))) := by ring
      _ ≤ (Cφ * Cκ) * ((1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-(N - M - 2)) *
          (4 * (5 / 2) ^ M * (L⁻¹ * ((1 + |z - cL| / L) ^ (-M) * (1 + |x - cL| / L) ^ (-(2 : ℝ)))) *
            ((2 : ℝ) ^ (j i) / L))) :=
          mul_le_mul_of_nonneg_left hreal (mul_nonneg hCφ hCκ)
      _ = (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-(N - M - 2)) *
          (K' * ((2 : ℝ) ^ (j i) / L)) := by simp only [hK']; ring
      _ ≤ (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-(N - M - 2)) * G (j i) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hmin hK'0
  have hlat := latConst_nonneg hN2
  calc ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ ≤ latConst (N - M - 2) * ∑' a, G a := h2
    _ = latConst (N - M - 2) * (K' * ∑' a : ℤ, min (L⁻¹ * (2 : ℝ) ^ a) (L * (2 : ℝ) ^ (-a))) := by
        rw [show ∑' a, G a = K' * ∑' a : ℤ, min (L⁻¹ * (2 : ℝ) ^ a) (L * (2 : ℝ) ^ (-a)) from tsum_mul_left]
    _ ≤ latConst (N - M - 2) * (K' * (4 * Real.sqrt (L⁻¹ * L))) := by gcongr
    _ = 16 * (Cφ * Cκ) * (5 / 2) ^ M * latConst (N - M - 2) *
      (L⁻¹ * ((1 + |z - cL| / L) ^ (-M) * (1 + |x - cL| / L) ^ (-(2 : ℝ)))) := by
        rw [inv_mul_cancel₀ hL.ne', Real.sqrt_one, hK']; ring

/-- The constant of the atom kernel bound. -/
def atomConst (N M Cφ Cκ : ℝ) : ℝ := 2 * tileCZ N M Cφ Cκ + 36 * (16 * (Cφ * Cκ) * latConst (N - 2))

theorem atomConst_nonneg {N M Cφ Cκ : ℝ} (hN : 3 < N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) :
    0 ≤ atomConst N M Cφ Cκ := by
  unfold atomConst tileCZ
  have h1 := latConst_nonneg (by linarith : (1 : ℝ) < N)
  have h2 := latConst_nonneg (by linarith : (1 : ℝ) < N - 2)
  positivity

/-- **The atom kernel bound**: for `|z - c| ≤ δ/2` and tiles of scale `≥ δ` or with `|c_i - c| ≥ 3δ/2`,
`‖K_S(x, z) - K_S(x, c)‖ ≤ C δ⁻¹ (1 + |x - c|/δ)^{-2}`. -/
theorem kernel_atom_le {N M Cφ Cκ : ℝ} (hN : 3 < N) (hM : 3 ≤ M) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ)
    (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) {δ c : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ S, δ ≤ (2 : ℝ) ^ (j i) ∨ 3 * δ / 2 ≤ |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - c|)
    {z : ℝ} (hz : |z - c| ≤ δ / 2) (x : ℝ) :
    ‖tileKernel S φ κ x z - tileKernel S φ κ x c‖ ≤
      atomConst N M Cφ Cκ * (δ⁻¹ * (1 + |x - c| / δ) ^ (-(2 : ℝ))) := by
  have hN1 : 1 < N := by linarith
  have hlat := latConst_nonneg (by linarith : (1 : ℝ) < N - 2)
  have hlat1 := latConst_nonneg hN1
  have hczpos : 0 ≤ tileCZ N M Cφ Cκ := by unfold tileCZ; positivity
  have hX0 : 0 ≤ 16 * (Cφ * Cκ) * latConst (N - 2) := by positivity
  set d : ℝ := |x - c| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hdδ : 0 < 1 + d / δ := by have := div_nonneg hd0 hδ.le; linarith
  have hW : δ⁻¹ * (1 + d / δ) ^ (-(2 : ℝ)) = δ / (δ + d) ^ 2 := by
    rw [Real.rpow_neg hdδ.le, Real.rpow_two]
    have : 1 + d / δ = (δ + d) / δ := by field_simp
    rw [this]
    have : 0 < δ + d := by linarith
    field_simp
  have hW0 : 0 ≤ δ⁻¹ * (1 + d / δ) ^ (-(2 : ℝ)) := by positivity
  unfold atomConst
  by_cases hfar : 2 * δ ≤ d
  · -- far zone: CZ smoothness in the second slot
    have hzx : d - δ / 2 ≤ |z - x| := by
      have : |x - c| ≤ |x - z| + |z - c| := by
        calc |x - c| = |(x - z) + (z - c)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      rw [abs_sub_comm z x]; linarith
    have hpos : 0 < |z - x| := by linarith
    have hsm := tileKernel_smooth hN1 hM S j v φ κ hb hinj hCφ hCκ (x := z) (x' := c) (z := x) hpos
      (by linarith)
    have h1 : ‖tileKernel S φ κ x z - tileKernel S φ κ x c‖ ≤ tileCZ N M Cφ Cκ * |z - c| / |z - x| ^ 2 := by
      have := norm_nonneg (tileKernel S φ κ z x - tileKernel S φ κ c x)
      linarith [hsm]
    have h2 : tileCZ N M Cφ Cκ * |z - c| / |z - x| ^ 2 ≤ 2 * tileCZ N M Cφ Cκ * (δ / (δ + d) ^ 2) := by
      have hsq : (δ + d) ^ 2 / 4 ≤ |z - x| ^ 2 := by
        have h : (δ + d) / 2 ≤ |z - x| := by linarith
        calc (δ + d) ^ 2 / 4 = ((δ + d) / 2) ^ 2 := by ring
          _ ≤ |z - x| ^ 2 := pow_le_pow_left₀ (by linarith) h 2
      have hden : 0 < (δ + d) ^ 2 / 4 := by positivity
      calc tileCZ N M Cφ Cκ * |z - c| / |z - x| ^ 2 ≤ tileCZ N M Cφ Cκ * (δ / 2) / ((δ + d) ^ 2 / 4) := by
            apply div_le_div₀ (by positivity) _ hden hsq
            exact mul_le_mul_of_nonneg_left hz hczpos
        _ = 2 * tileCZ N M Cφ Cκ * (δ / (δ + d) ^ 2) := by field_simp; ring
    rw [hW]
    have h3 : 0 ≤ δ / (δ + d) ^ 2 := by positivity
    linarith [mul_nonneg hX0 h3]
  · -- near zone: sizes
    push Not at hfar
    have hsepz : ∀ i ∈ S, δ ≤ (2 : ℝ) ^ (j i) ∨ δ ≤ |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - z| := by
      intro i hi
      rcases hsep i hi with h | h
      · exact Or.inl h
      · right
        have : |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - c| ≤
            |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - z| + |z - c| := by
          calc |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - c|
              = |((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - z) + (z - c)| := by congr 1; ring
            _ ≤ _ := abs_add_le _ _
        linarith
    have hsepc : ∀ i ∈ S, δ ≤ (2 : ℝ) ^ (j i) ∨ δ ≤ |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - c| := by
      intro i hi
      rcases hsep i hi with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    have h1 := sum_near_le hN (by linarith) hCφ hCκ S j v φ κ hb hinj hδ hsepz x
    have h2 := sum_near_le hN (by linarith) hCφ hCκ S j v φ κ hb hinj hδ hsepc x
    have hn1 : ‖tileKernel S φ κ x z‖ ≤ ∑ i ∈ S, ‖φ i x * κ i (x - z)‖ := norm_sum_le _ _
    have hn2 : ‖tileKernel S φ κ x c‖ ≤ ∑ i ∈ S, ‖φ i x * κ i (x - c)‖ := norm_sum_le _ _
    have hsub : ‖tileKernel S φ κ x z - tileKernel S φ κ x c‖ ≤ 2 * (16 * (Cφ * Cκ) * latConst (N - 2) / δ) := by
      calc _ ≤ ‖tileKernel S φ κ x z‖ + ‖tileKernel S φ κ x c‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    -- `W ≥ 1/(9 δ)`
    have hWlow : (1 : ℝ) / (9 * δ) ≤ δ⁻¹ * (1 + d / δ) ^ (-(2 : ℝ)) := by
      rw [hW]
      have hsq : (δ + d) ^ 2 ≤ 9 * δ ^ 2 := by
        calc (δ + d) ^ 2 ≤ (3 * δ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          _ = 9 * δ ^ 2 := by ring
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hq : 2 * (16 * (Cφ * Cκ) * latConst (N - 2) / δ) ≤
        18 * (16 * (Cφ * Cκ) * latConst (N - 2)) * (δ⁻¹ * (1 + d / δ) ^ (-(2 : ℝ))) := by
      have e : 2 * (16 * (Cφ * Cκ) * latConst (N - 2) / δ) =
          18 * (16 * (Cφ * Cκ) * latConst (N - 2)) * (1 / (9 * δ)) := by field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hWlow (by positivity)
    have h4 : 0 ≤ 2 * tileCZ N M Cφ Cκ * (δ⁻¹ * (1 + d / δ) ^ (-(2 : ℝ))) := by positivity
    linarith [mul_nonneg hX0 hW0]

end Sums

end PrimeBHT.TimeFrequency.X2
