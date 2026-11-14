module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import PrimeBHT.TimeFrequency.X2.CZ.DyadicSum
public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair

/-!
# X2, node B5: elementary sums used by the CZ-kernel verification of tree operators

* `sum_lattice_le`: `∑_{v ∈ S} (1 + |x - L (v + 1/2)|/L)^{-N} ≤ latConst N` for every finite `S ⊆ ℤ` (`N > 1`);
* `sum_tiles_le`: the same for tiles of a family with injective labels `(j i, v i)`: the position sum is bounded and the
  scale sum is controlled by `∑' j, G j`;
* `scaleSum_size`: `∑_j 2^{-j} (1 + d/2^j)^{-M} ≤ 4/d`;
* `scaleSum_smooth`: `∑_j min(2^{-j}, δ 2^{-2j}) (1 + d/2^{j+1})^{-M} ≤ 2^{M+2} δ/d²` for `δ ≤ d/2`, `M ≥ 3`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.TimeFrequency.Tile
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The lattice constant `(3/2)^N · 2/(N - 1)`. -/
def latConst (N : ℝ) : ℝ := (3 / 2) ^ N * (2 / (N - 1))

theorem latConst_nonneg {N : ℝ} (hN : 1 < N) : 0 ≤ latConst N := by
  unfold latConst
  have : 0 < N - 1 := by linarith
  positivity

/-- Position sum: the translates `L (v + 1/2)` of the lattice `L ℤ` see a weight `(1 + |x - ·|/L)^{-N}` with total
mass at most `latConst N`. -/
theorem sum_lattice_le {N : ℝ} (hN : 1 < N) {L : ℝ} (hL : 0 < L) (x : ℝ) (S : Finset ℤ) :
    ∑ v ∈ S, (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) ≤ latConst N := by
  set f : ℝ → ℝ := fun y => (1 + |y - x| / L) ^ (-N) with hf
  have hN0 : 0 ≤ N := by linarith
  have hfpos : ∀ y, 0 ≤ f y := fun y => by simp only [hf]; positivity
  have hint : Integrable f := integrable_one_add_abs_sub_div_rpow hN x hL
  have hI : ∫ y, f y = 2 * L / (N - 1) := integral_one_add_abs_sub_div_rpow hN x hL
  -- lower bound of the integral over each cell
  have hcell : ∀ v : ℤ, (2 / 3) ^ N * L * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) ≤
      ∫ y in Ico (L * v) (L * (v + 1)), f y := by
    intro v
    have hmeas : MeasurableSet (Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1))) := measurableSet_Ico
    have hvol : volume (Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1))) ≠ ⊤ := by
      rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
    have hpt : ∀ y ∈ Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1)),
        (2 / 3) ^ N * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) ≤ f y := by
      intro y hy
      simp only [hf]
      have hy1 : |y - L * ((v : ℝ) + 1 / 2)| ≤ L / 2 := by
        rw [abs_le]; obtain ⟨h1, h2⟩ := hy; constructor <;> nlinarith
      have hA : 0 < 1 + |x - L * ((v : ℝ) + 1 / 2)| / L := by positivity
      have hB : 0 < 1 + |y - x| / L := by positivity
      have hle : 1 + |y - x| / L ≤ (3 / 2) * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) := by
        have h1 : |y - x| ≤ |y - L * ((v : ℝ) + 1 / 2)| + |x - L * ((v : ℝ) + 1 / 2)| := by
          calc |y - x| = |(y - L * ((v : ℝ) + 1 / 2)) - (x - L * ((v : ℝ) + 1 / 2))| := by ring_nf
            _ ≤ _ := abs_sub _ _
        have h2 : |y - x| / L ≤ 1 / 2 + |x - L * ((v : ℝ) + 1 / 2)| / L := by
          rw [div_le_iff₀ hL]
          have : (1 / 2 + |x - L * ((v : ℝ) + 1 / 2)| / L) * L = L / 2 + |x - L * ((v : ℝ) + 1 / 2)| := by
            field_simp
          rw [this]; linarith
        have h3 : 0 ≤ |x - L * ((v : ℝ) + 1 / 2)| / L := by positivity
        nlinarith
      have e23 : (2 / 3 : ℝ) ^ N = ((3 / 2 : ℝ) ^ N)⁻¹ := by
        rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2)]; norm_num
      calc (2 / 3) ^ N * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N)
          = ((3 / 2) * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L)) ^ (-N) := by
            rw [Real.mul_rpow (by norm_num) hA.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 2),
              Real.rpow_neg hA.le, e23]
        _ ≤ (1 + |y - x| / L) ^ (-N) :=
            Real.rpow_le_rpow_of_nonpos hB hle (by linarith)
    have hge : (2 / 3) ^ N * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) * volume.real (Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1))) ≤
        ∫ y in Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1)), f y :=
      by
        have := setIntegral_ge_of_const_le (μ := volume) (c := (2 / 3) ^ N * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N))
          hmeas hvol hpt hint.integrableOn
        simpa [smul_eq_mul, mul_comm] using this
    have hv : (volume.real (Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1)))) = L := by
      rw [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by nlinarith)]
      ring
    rw [hv] at hge
    linarith
  -- sum the cells
  have hdisj : (S : Set ℤ).PairwiseDisjoint (fun v : ℤ => Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1))) := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro y h1 h2
    have hab' : a ≠ b := hab
    rcases lt_or_gt_of_ne hab' with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast Int.add_one_le_iff.2 h
      nlinarith [h1.2, h2.1]
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast Int.add_one_le_iff.2 h
      nlinarith [h1.1, h2.2]
  have hsum : ∑ v ∈ S, ∫ y in Ico (L * (v : ℝ)) (L * ((v : ℝ) + 1)), f y ≤ ∫ y, f y := by
    rw [← integral_biUnion_finset S (fun v _ => measurableSet_Ico) hdisj (fun v _ => hint.integrableOn)]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall hfpos)
  have hlow : ∑ v ∈ S, (2 / 3) ^ N * L * (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) ≤ 2 * L / (N - 1) := by
    rw [← hI]
    exact (Finset.sum_le_sum fun v _ => hcell v).trans hsum
  have h23 : (0 : ℝ) < (2 / 3) ^ N * L := by positivity
  have hmul : (2 / 3) ^ N * L * ∑ v ∈ S, (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) ≤ 2 * L / (N - 1) := by
    rw [Finset.mul_sum]; exact hlow
  have : ∑ v ∈ S, (1 + |x - L * ((v : ℝ) + 1 / 2)| / L) ^ (-N) ≤ (2 * L / (N - 1)) / ((2 / 3) ^ N * L) := by
    rw [le_div_iff₀ h23, mul_comm]; exact hmul
  refine this.trans (le_of_eq ?_)
  unfold latConst
  have hN1 : N - 1 ≠ 0 := by linarith
  have e23 : (2 / 3 : ℝ) ^ N = ((3 / 2 : ℝ) ^ N)⁻¹ := by
    rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2)]; norm_num
  rw [e23]
  field_simp

section Tiles

variable {ι : Type*}

/-- **Sum over tiles with injective labels**: if `F i ≤ W_i(x) G(j i)` with the weight `W_i(x) = (1 + |x - c_i|/L_i)^{-N}`
of the tile `i` (scale `L_i = 2^{j i}`, position `v i`, `c_i = L_i (v i + 1/2)`), and `(j, v)` is injective on `S`,
then `∑_i F i ≤ latConst N · ∑' j, G j`. -/
theorem sum_tiles_le {N : ℝ} (hN : 1 < N) (S : Finset ι) (j v : ι → ℤ)
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) (x : ℝ) {G : ℤ → ℝ} (hG0 : ∀ a, 0 ≤ G a)
    (hG : Summable G) {F : ι → ℝ}
    (hF : ∀ i ∈ S, F i ≤ (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N) * G (j i)) :
    ∑ i ∈ S, F i ≤ latConst N * ∑' a, G a := by
  classical
  have h1 : ∑ i ∈ S, F i ≤ ∑ i ∈ S, (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N) * G (j i) :=
    Finset.sum_le_sum hF
  have h2 : ∑ i ∈ S, (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N) * G (j i) =
      ∑ a ∈ S.image j, ∑ i ∈ S.filter (fun i => j i = a),
        (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N) * G (j i) := by
    rw [Finset.sum_fiberwise_of_maps_to (g := j) (s := S) (t := S.image j)
      (fun i hi => Finset.mem_image_of_mem j hi)]
  have h3 : ∀ a ∈ S.image j, ∑ i ∈ S.filter (fun i => j i = a),
      (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N) * G (j i) ≤
        latConst N * G a := by
    intro a _
    have hL : (0 : ℝ) < (2 : ℝ) ^ a := zpow_pos (by norm_num) a
    have e : ∑ i ∈ S.filter (fun i => j i = a),
        (1 + |x - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-N) * G (j i) =
        G a * ∑ i ∈ S.filter (fun i => j i = a),
          (1 + |x - (2 : ℝ) ^ a * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ a) ^ (-N) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := (Finset.mem_filter.1 hi).2
      rw [this]; ring
    have hinj' : Set.InjOn v (S.filter (fun i => j i = a) : Set ι) := by
      intro i₁ h₁ i₂ h₂ h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at h₁ h₂
      exact hinj h₁.1 h₂.1 (Prod.ext (h₁.2.trans h₂.2.symm) h)
    have e2 : ∑ i ∈ S.filter (fun i => j i = a),
          (1 + |x - (2 : ℝ) ^ a * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ a) ^ (-N) =
        ∑ w ∈ (S.filter (fun i => j i = a)).image v,
          (1 + |x - (2 : ℝ) ^ a * ((w : ℝ) + 1 / 2)| / (2 : ℝ) ^ a) ^ (-N) := by
      rw [Finset.sum_image hinj']
    rw [e, e2, mul_comm]
    exact mul_le_mul_of_nonneg_right (sum_lattice_le hN hL x _) (hG0 a)
  calc ∑ i ∈ S, F i ≤ ∑ a ∈ S.image j, latConst N * G a := by
        rw [h2] at h1; exact h1.trans (Finset.sum_le_sum h3)
    _ = latConst N * ∑ a ∈ S.image j, G a := by rw [Finset.mul_sum]
    _ ≤ latConst N * ∑' a, G a :=
        mul_le_mul_of_nonneg_left (hG.sum_le_tsum _ (fun a _ => hG0 a)) (latConst_nonneg hN)

end Tiles

/-! ### Scale sums -/

theorem two_zpow_pos' (j : ℤ) : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j

/-- Pointwise majorant: `L⁻¹ (1 + d/L)^{-M} ≤ min(L/d², L⁻¹)` for `M ≥ 2`. -/
theorem size_le_min {M d L : ℝ} (hM : 2 ≤ M) (hd : 0 < d) (hL : 0 < L) :
    L⁻¹ * (1 + d / L) ^ (-M) ≤ min (d⁻¹ ^ 2 * L) L⁻¹ := by
  have hb : (1 : ℝ) ≤ 1 + d / L := by have := div_nonneg hd.le hL.le; linarith
  have h1 : (1 + d / L) ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  refine le_min ?_ ?_
  · rcases le_total L d with h | h
    · have h2 : (1 + d / L) ^ (-M) ≤ (d / L) ^ (-M) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have h3 : (d / L) ^ (-M) = (L / d) ^ M := by
        rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
      have h4 : (L / d) ^ M ≤ (L / d) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hd]; exact h) hM
      calc L⁻¹ * (1 + d / L) ^ (-M) ≤ L⁻¹ * (L / d) ^ (2 : ℝ) := by
            gcongr; exact h2.trans (h3 ▸ h4)
        _ = d⁻¹ ^ 2 * L := by rw [Real.rpow_two]; field_simp
    · calc L⁻¹ * (1 + d / L) ^ (-M) ≤ L⁻¹ * 1 := by gcongr
        _ = L⁻¹ := mul_one _
        _ ≤ d⁻¹ ^ 2 * L := by
            rw [inv_pow, ← one_div, ← one_div, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hL (by positivity)]
            nlinarith
  · calc L⁻¹ * (1 + d / L) ^ (-M) ≤ L⁻¹ * 1 := by gcongr
      _ = L⁻¹ := mul_one _

/-- `∑_j 2^{-j} (1 + d/2^j)^{-M} ≤ 4/d`. -/
theorem scaleSum_size {M d : ℝ} (hM : 2 ≤ M) (hd : 0 < d) :
    Summable (fun j : ℤ => ((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 : ℝ) ^ j) ^ (-M)) ∧
      ∑' j : ℤ, ((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 : ℝ) ^ j) ^ (-M) ≤ 4 / d := by
  have hd2 : 0 < d⁻¹ ^ 2 := by positivity
  obtain ⟨hs, hb⟩ := CZ.hasSum_le_min_two_zpow hd2 (one_pos : (0 : ℝ) < 1)
  have hle : ∀ j : ℤ, ((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 : ℝ) ^ j) ^ (-M) ≤
      min (d⁻¹ ^ 2 * (2 : ℝ) ^ j) (1 * (2 : ℝ) ^ (-j)) := by
    intro j
    have := size_le_min hM hd (two_zpow_pos' j)
    rwa [one_mul, zpow_neg]
  have hnn : ∀ j : ℤ, 0 ≤ ((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 : ℝ) ^ j) ^ (-M) := fun j => by
    have := two_zpow_pos' j; positivity
  have hsum : Summable (fun j : ℤ => ((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 : ℝ) ^ j) ^ (-M)) :=
    Summable.of_nonneg_of_le hnn hle (by simpa using hs)
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℤ, ((2 : ℝ) ^ j)⁻¹ * (1 + d / (2 : ℝ) ^ j) ^ (-M)
      ≤ ∑' j : ℤ, min (d⁻¹ ^ 2 * (2 : ℝ) ^ j) (1 * (2 : ℝ) ^ (-j)) := hsum.tsum_le_tsum hle (by simpa using hs)
    _ ≤ 4 * Real.sqrt (d⁻¹ ^ 2 * 1) := hb
    _ = 4 / d := by
        rw [mul_one, Real.sqrt_sq (by positivity)]; field_simp

/-- Pointwise majorant of the smoothness terms:
`min(L⁻¹, δ L⁻²) (1 + d/(2L))^{-M} ≤ 2^M (δ/d²) min(L/d, d/L)` for `δ ≤ d/2`, `M ≥ 3`. -/
theorem smooth_le_min {M d δ L : ℝ} (hM : 3 ≤ M) (hd : 0 < d) (hδ : 0 ≤ δ) (_hδd : 2 * δ ≤ d) (hL : 0 < L) :
    min L⁻¹ (δ * (L⁻¹) ^ 2) * (1 + d / (2 * L)) ^ (-M) ≤ 2 ^ M * (δ / d ^ 2) * min (L / d) (d / L) := by
  have hb : (1 : ℝ) ≤ 1 + d / (2 * L) := by have := div_nonneg hd.le (by positivity : (0 : ℝ) ≤ 2 * L); linarith
  have hM0 : 0 ≤ M := by linarith
  have h1 : (1 + d / (2 * L)) ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  have h2 : (1 + d / (2 * L)) ^ (-M) ≤ (2 * L / d) ^ M := by
    have h' : (1 + d / (2 * L)) ^ (-M) ≤ (d / (2 * L)) ^ (-M) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have e : (d / (2 * L)) ^ (-M) = (2 * L / d) ^ M := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    rwa [e] at h'
  have hmin : min (L / d) (d / L) = if L ≤ d then L / d else d / L := by
    by_cases h : L ≤ d
    · rw [ite_eq_left h, min_eq_left]; rw [div_le_div_iff₀ hd hL]; nlinarith
    · rw [ite_eq_right h, min_eq_right]; push Not at h; rw [div_le_div_iff₀ hL hd]; nlinarith
  rw [hmin]
  have hpow : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (2 * L / d) ^ M = 2 ^ M * (L / d) ^ M := by
    intro a _ _
    rw [show 2 * L / d = 2 * (L / d) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  by_cases hLd : L ≤ d
  · simp only [ite_eq_left hLd]
    have hLd' : L / d ≤ 1 := by rw [div_le_one hd]; exact hLd
    have hLM : (L / d) ^ M ≤ (L / d) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) hLd' hM
    have hL3 : (L / d) ^ (3 : ℝ) = (L / d) ^ 3 := by norm_cast
    have h2' : (1 + d / (2 * L)) ^ (-M) ≤ 2 ^ M * (L / d) ^ 3 := by
      refine h2.trans ?_
      rw [hpow 0 le_rfl zero_le_one]
      gcongr
      exact hLM.trans (le_of_eq hL3)
    have hmn : min L⁻¹ (δ * (L⁻¹) ^ 2) ≤ δ * (L⁻¹) ^ 2 ∨ δ * (L⁻¹) ^ 2 ≤ min L⁻¹ (δ * (L⁻¹) ^ 2) := by
      exact Or.inl (min_le_right _ _)
    -- use `min ≤ δ L⁻²` if `δ ≤ L`, else `min ≤ L⁻¹`
    rcases le_total δ L with hδL | hLδ
    · calc min L⁻¹ (δ * (L⁻¹) ^ 2) * (1 + d / (2 * L)) ^ (-M)
          ≤ (δ * (L⁻¹) ^ 2) * (2 ^ M * (L / d) ^ 3) :=
            mul_le_mul (min_le_right _ _) h2' (by positivity) (by positivity)
        _ = 2 ^ M * (δ / d ^ 2) * (L / d) := by field_simp
    · calc min L⁻¹ (δ * (L⁻¹) ^ 2) * (1 + d / (2 * L)) ^ (-M)
          ≤ L⁻¹ * (2 ^ M * (L / d) ^ 3) :=
            mul_le_mul (min_le_left _ _) h2' (by positivity) (by positivity)
        _ ≤ 2 ^ M * (δ / d ^ 2) * (L / d) := by
            have hl : L / d ≤ 1 := hLd'
            -- `L⁻¹ (L/d)^3 = L²/d³ ≤ δ L / d³` needs `L ≤ δ`
            have : L⁻¹ * (L / d) ^ 3 = L ^ 2 / d ^ 3 := by field_simp
            calc L⁻¹ * (2 ^ M * (L / d) ^ 3) = 2 ^ M * (L ^ 2 / d ^ 3) := by rw [← this]; ring
              _ ≤ 2 ^ M * (δ / d ^ 2 * (L / d)) := by
                  gcongr
                  rw [show δ / d ^ 2 * (L / d) = δ * L / d ^ 3 by field_simp]
                  rw [div_le_div_iff_of_pos_right (by positivity)]
                  nlinarith
              _ = _ := by ring
  · simp only [ite_eq_right hLd]
    push Not at hLd
    have hdL : d / L ≤ 1 := by rw [div_le_one hL]; exact hLd.le
    calc min L⁻¹ (δ * (L⁻¹) ^ 2) * (1 + d / (2 * L)) ^ (-M)
        ≤ (δ * (L⁻¹) ^ 2) * 1 := mul_le_mul (min_le_right _ _) h1 (by positivity) (by positivity)
      _ = δ * (L⁻¹) ^ 2 := mul_one _
      _ ≤ 2 ^ M * (δ / d ^ 2) * (d / L) := by
          have e : 2 ^ M * (δ / d ^ 2) * (d / L) = 2 ^ M * (δ / (d * L)) := by field_simp
          rw [e]
          have h2M : (1 : ℝ) ≤ 2 ^ M := Real.one_le_rpow (by norm_num) hM0
          have : δ * (L⁻¹) ^ 2 ≤ δ / (d * L) := by
            rw [inv_pow, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_nonneg hδ (sub_nonneg.2 hLd.le), hL.le]
          calc δ * (L⁻¹) ^ 2 ≤ δ / (d * L) := this
            _ = 1 * (δ / (d * L)) := (one_mul _).symm
            _ ≤ 2 ^ M * (δ / (d * L)) := by gcongr

/-- `∑_j min(2^{-j}, δ 2^{-2j}) (1 + d/2^{j+1})^{-M} ≤ 2^{M+2} δ / d²` for `2δ ≤ d`, `M ≥ 3`. -/
theorem scaleSum_smooth {M d δ : ℝ} (hM : 3 ≤ M) (hd : 0 < d) (hδ : 0 ≤ δ) (hδd : 2 * δ ≤ d) :
    Summable (fun j : ℤ => min ((2 : ℝ) ^ j)⁻¹ (δ * (((2 : ℝ) ^ j)⁻¹) ^ 2) * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M)) ∧
      ∑' j : ℤ, min ((2 : ℝ) ^ j)⁻¹ (δ * (((2 : ℝ) ^ j)⁻¹) ^ 2) * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M) ≤
        2 ^ M * 4 * (δ / d ^ 2) := by
  have hd1 : 0 < d⁻¹ := by positivity
  obtain ⟨hs, hb⟩ := CZ.hasSum_le_min_two_zpow hd1 hd
  set c : ℝ := 2 ^ M * (δ / d ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hle : ∀ j : ℤ, min ((2 : ℝ) ^ j)⁻¹ (δ * (((2 : ℝ) ^ j)⁻¹) ^ 2) * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M) ≤
      c * min (d⁻¹ * (2 : ℝ) ^ j) (d * (2 : ℝ) ^ (-j)) := by
    intro j
    have this := smooth_le_min hM hd hδ hδd (two_zpow_pos' j)
    have e1 : (2 : ℝ) ^ j / d = d⁻¹ * (2 : ℝ) ^ j := by ring
    have e2 : d / (2 : ℝ) ^ j = d * (2 : ℝ) ^ (-j) := by rw [zpow_neg]; ring
    rw [e1, e2] at this
    rw [hc]
    exact this
  have hnn : ∀ j : ℤ, 0 ≤ min ((2 : ℝ) ^ j)⁻¹ (δ * (((2 : ℝ) ^ j)⁻¹) ^ 2) * (1 + d / (2 * (2 : ℝ) ^ j)) ^ (-M) := by
    intro j
    have := two_zpow_pos' j
    exact mul_nonneg (le_min (by positivity) (by positivity)) (by positivity)
  have hs' : Summable (fun j : ℤ => c * min (d⁻¹ * (2 : ℝ) ^ j) (d * (2 : ℝ) ^ (-j))) := hs.mul_left c
  have hsum := Summable.of_nonneg_of_le hnn hle hs'
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' j : ℤ, c * min (d⁻¹ * (2 : ℝ) ^ j) (d * (2 : ℝ) ^ (-j)) := hsum.tsum_le_tsum hle hs'
    _ = c * ∑' j : ℤ, min (d⁻¹ * (2 : ℝ) ^ j) (d * (2 : ℝ) ^ (-j)) := tsum_mul_left
    _ ≤ c * (4 * Real.sqrt (d⁻¹ * d)) := mul_le_mul_of_nonneg_left hb hc0
    _ = 2 ^ M * 4 * (δ / d ^ 2) := by
        rw [inv_mul_cancel₀ hd.ne', Real.sqrt_one, hc]; ring

end PrimeBHT.TimeFrequency.X2
