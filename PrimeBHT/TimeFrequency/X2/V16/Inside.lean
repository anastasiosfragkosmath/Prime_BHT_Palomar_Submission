module

public import PrimeBHT.TimeFrequency.X2.V16.Outside

/-!
# X2, node V16: B11 (the inside part, single-scale layers)

`inside_le_of_hyps`: the form over `insidePart Ps Ω`, `Ω = exceptionalOmega 48 E τ`, is at most `C · CT · ∏ |E_i|^{β_i}`.
CONDITIONAL on B5 (`EngLeTailMassStatement`), V12 (`EnergyLemmaStatement`, in particular its localized part B6') and V15
(`TreeLemmaStatement`).

Proof (route check B11): the inside tiles split into the layers `layer Ps W n` (`W ∈ maxDyadicKeys Ω`, `n ∈ ℕ`; B3,
`mem_layer_iff_of_subset`).  On one layer: `form_le_main` (B7) with `Λb_v` from B5 and B2(b), (c) (tail masses at depth `n`
below `W`), the localized counts `Ar_v = Ca |W| μ''_v` of V12 (B6') with `p_W^{-q_X} ≤ 2^{50 q_X} ⟨(x - c_W)/|W|⟩^{-100 q_X}` and
B2(d), then `tsum_min_le_region` at `θ = η` (B9 + B8): the layer is `≲ a^n |W| ∏ μ''_v^{β_v}` with
`a = 4 · 2^{-(M-1)η} < 1` (`(M-1) η > 2` for `M = 33 R + 2`).  Summation over `n` (geometric) and over `W` (`∑ |W| ≤ |Ω|`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-! ### The localizing weight -/

/-- `(1 + t²)^{50} ≤ 2^{50} (1 + t^{100})`. -/
theorem one_add_sq_pow_le (t : ℝ) : (1 + t ^ 2) ^ 50 ≤ 2 ^ 50 * (1 + t ^ 100) := by
  have h100 : t ^ 100 = (t ^ 2) ^ 50 := by rw [← pow_mul]
  have h0 : 0 ≤ t ^ 2 := sq_nonneg t
  rcases le_total (t ^ 2) 1 with h | h
  · have h1 : 1 + t ^ 2 ≤ 2 := by linarith
    have h2 : (1 + t ^ 2) ^ 50 ≤ 2 ^ 50 := pow_le_pow_left₀ (by linarith) h1 50
    have h3 : 0 ≤ t ^ 100 := by rw [h100]; positivity
    exact h2.trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right h3))
  · have h1 : 1 + t ^ 2 ≤ 2 * t ^ 2 := by linarith
    have h2 : (1 + t ^ 2) ^ 50 ≤ (2 * t ^ 2) ^ 50 := pow_le_pow_left₀ (by linarith) h1 50
    rw [mul_pow, ← h100] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))

/-- `p_W(x)^{-q} ≤ 2^{50 q} ⟨(x - c_W)/|W|⟩^{-100 q}`, `p_W = 1 + t^{100}`, `t = (x - c_W)/|W|`. -/
theorem inv_locPoly_rpow_le {q : ℝ} (hq : 0 < q) (W : ℤ × ℤ) (x : ℝ) :
    ((locPoly W x)⁻¹) ^ q ≤
      2 ^ (50 * q) * tailWeight (100 * q) ((x - intervalCentre (dyadicInt W.1 W.2)) / (2 : ℝ) ^ W.1) := by
  set t : ℝ := (x - intervalCentre (dyadicInt W.1 W.2)) / (2 : ℝ) ^ W.1 with ht
  have hp : locPoly W x = 1 + t ^ 100 := by
    unfold locPoly locLoss
    rw [ht, intervalCentre_dyadicInt]
    rfl
  have ha : 0 < 1 + t ^ 2 := by positivity
  have h100 : 0 ≤ t ^ 100 := by rw [show (100 : ℕ) = 2 * 50 by norm_num, pow_mul]; positivity
  have hpp : 0 < 1 + t ^ 100 := add_pos_of_pos_of_nonneg one_pos h100
  have h1 := one_add_sq_pow_le t
  have hA : 0 < (1 + t ^ 2) ^ 50 := by positivity
  have h2 : (1 + t ^ 100)⁻¹ ≤ 2 ^ 50 * ((1 + t ^ 2) ^ 50)⁻¹ := by
    calc (1 + t ^ 100)⁻¹ = ((1 + t ^ 2) ^ 50 * (1 + t ^ 100)⁻¹) * ((1 + t ^ 2) ^ 50)⁻¹ := by
          field_simp
      _ ≤ 2 ^ 50 * ((1 + t ^ 2) ^ 50)⁻¹ := by
          gcongr
          rw [mul_inv_le_iff₀ hpp]; exact h1
  rw [hp]
  calc ((1 + t ^ 100)⁻¹) ^ q ≤ (2 ^ 50 * ((1 + t ^ 2) ^ 50)⁻¹) ^ q :=
        Real.rpow_le_rpow (by positivity) h2 hq.le
    _ = 2 ^ (50 * q) * tailWeight (100 * q) t := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        · rw [show (2 : ℝ) ^ 50 = (2 : ℝ) ^ ((50 : ℕ) : ℝ) by rw [Real.rpow_natCast],
            ← Real.rpow_mul (by norm_num)]
          norm_num
        · unfold tailWeight
          rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le]
          congr 1
          push_cast
          ring


theorem locPoly_pos (W : ℤ × ℤ) (x : ℝ) : 0 < locPoly W x := by
  unfold locPoly locLoss
  have : 0 ≤ ((x - dyCentre W.1 W.2) / (2 : ℝ) ^ W.1) ^ 100 := by positivity
  exact add_pos_of_pos_of_nonneg one_pos this

/-- `y ≤ 1_S x` implies `y^q ≤ 1_S x` (`y ≥ 0`, `q > 0`). -/
theorem rpow_le_indicator {S : Set ℝ} {y q : ℝ} (hy : 0 ≤ y) (hq : 0 < q) {x : ℝ}
    (h : y ≤ S.indicator (fun _ => (1 : ℝ)) x) : y ^ q ≤ S.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx] at h ⊢
    calc y ^ q ≤ 1 ^ q := Real.rpow_le_rpow hy h hq.le
      _ = 1 := Real.one_rpow q
  · rw [Set.indicator_of_notMem hx] at h ⊢
    have : y = 0 := le_antisymm h hy
    rw [this, Real.zero_rpow hq.ne']

/-- **The localized `mixedPow`.**  For `F` dominated by `1_S`:
`‖F/p_W‖_{L^q(ℝ; L^s)}^q ≤ 2^{50 q} ∫ 1_S ⟨(x - c_W)/|W|⟩^{-100 q}`. -/
theorem mixedPow_locPoly_le {P : ℕ} [NeZero P] {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) {S : Set ℝ}
    (hS : MeasurableSet S) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ x, yNorm s (F x) ≤ S.indicator (fun _ => (1 : ℝ)) x) (W : ℤ × ℤ) :
    mixedPow q s (fun x => ((locPoly W x)⁻¹ : ℂ) • F x) ≤
      ENNReal.ofReal (2 ^ (50 * q) * ∫ x, S.indicator (1 : ℝ → ℝ) x *
        tailWeight (100 * q) ((x - intervalCentre (dyadicInt W.1 W.2)) / (2 : ℝ) ^ W.1)) := by
  have hq0 : 0 < q := by linarith
  set c := intervalCentre (dyadicInt W.1 W.2) with hc
  set tw : ℝ → ℝ := fun x => tailWeight (100 * q) ((x - c) / (2 : ℝ) ^ W.1) with htw
  have hL : (0 : ℝ) < (2 : ℝ) ^ W.1 := by positivity
  have hint : Integrable (fun x => S.indicator (1 : ℝ → ℝ) x * tw x) := by
    refine (integrable_tailWeight (by linarith : 1 < 100 * q) c hL).mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((measurable_const.indicator hS).mul
        ((measurable_tailWeight _).comp (by fun_prop))).aestronglyMeasurable
    · have h0 : 0 ≤ S.indicator (1 : ℝ → ℝ) x := by by_cases hx : x ∈ S <;> simp [hx]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (tailWeight_nonneg _ _))]
      exact mul_le_of_le_one_left (tailWeight_nonneg _ _) (indicator_one_le_one S x)
  have hnn : ∀ x, 0 ≤ 2 ^ (50 * q) * (S.indicator (1 : ℝ → ℝ) x * tw x) := fun x => by
    have h0 : 0 ≤ S.indicator (1 : ℝ → ℝ) x := by by_cases hx : x ∈ S <;> simp [hx]
    exact mul_nonneg (by positivity) (mul_nonneg h0 (tailWeight_nonneg _ _))
  calc mixedPow q s (fun x => ((locPoly W x)⁻¹ : ℂ) • F x)
      ≤ ∫⁻ x, ENNReal.ofReal (2 ^ (50 * q) * (S.indicator (1 : ℝ → ℝ) x * tw x)) := by
        unfold mixedPow
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have hp := locPoly_pos W x
        have hn : ‖((locPoly W x)⁻¹ : ℂ)‖ = (locPoly W x)⁻¹ := by
          simp [abs_of_pos hp]
        rw [yNorm_smul hs, hn, Real.mul_rpow (inv_nonneg.2 hp.le) (yNorm_nonneg' _ _)]
        have h1 := inv_locPoly_rpow_le hq0 W x
        have h2 := rpow_le_indicator (yNorm_nonneg' s (F x)) hq0 (hF x)
        have h3 : S.indicator (1 : ℝ → ℝ) x = S.indicator (fun _ => (1 : ℝ)) x := rfl
        rw [h3]
        calc (locPoly W x)⁻¹ ^ q * yNorm s (F x) ^ q
            ≤ (2 ^ (50 * q) * tw x) * S.indicator (fun _ => (1 : ℝ)) x :=
              mul_le_mul h1 h2 (Real.rpow_nonneg (yNorm_nonneg' _ _) _) (by
                have := tailWeight_nonneg (100 * q) ((x - c) / (2 : ℝ) ^ W.1); positivity)
          _ = _ := by ring
    _ = ENNReal.ofReal (∫ x, 2 ^ (50 * q) * (S.indicator (1 : ℝ → ℝ) x * tw x)) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (ae_of_all _ hnn)).symm
    _ = _ := by rw [integral_const_mul]


/-! ### The truncated mass to a power (either sign) -/

theorem min_one_mul_rpow_le {r β : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hβ : β ≤ 1) :
    (min 1 (96 * r)) ^ β ≤ 96 * r ^ β := by
  have hrβ : 0 ≤ r ^ β := Real.rpow_nonneg hr0.le _
  have hm0 : 0 < min 1 (96 * r) := lt_min one_pos (by positivity)
  rcases le_or_gt 0 β with hb | hb
  · calc (min 1 (96 * r)) ^ β ≤ (96 * r) ^ β :=
          Real.rpow_le_rpow hm0.le (min_le_right _ _) hb
      _ = 96 ^ β * r ^ β := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ 96 * r ^ β := by
          refine mul_le_mul_of_nonneg_right ?_ hrβ
          calc (96 : ℝ) ^ β ≤ 96 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
            _ = 96 := Real.rpow_one _
  · have hle : r ≤ min 1 (96 * r) := le_min hr1 (by linarith)
    calc (min 1 (96 * r)) ^ β ≤ r ^ β := Real.rpow_le_rpow_of_nonpos hr0 hle hb.le
      _ ≤ 96 * r ^ β := by nlinarith

/-! ### Sums over the layers -/

/-- `∑_{(W,n) ∈ t} a^n |W| ≤ (1 - a)^{-1} |Ω|` for a finite set `t` of keys of maximal dyadic intervals of `Ω`. -/
theorem sum_geom_mul_le {Ω : Set ℝ} (hΩ : volume Ω ≠ ⊤) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (t : Finset ((ℤ × ℤ) × ℕ)) (ht : ∀ wn ∈ t, wn.1 ∈ maxDyadicKeys Ω) :
    ∑ wn ∈ t, a ^ wn.2 * (2 : ℝ) ^ wn.1.1 ≤ (1 - a)⁻¹ * (volume Ω).toReal := by
  classical
  set t₁ : Finset (ℤ × ℤ) := t.image Prod.fst with ht₁
  set N : ℕ := t.sup Prod.snd + 1 with hN
  have hsub : t ⊆ t₁ ×ˢ Finset.range N := by
    intro wn hwn
    rw [Finset.mem_product]
    refine ⟨Finset.mem_image_of_mem _ hwn, ?_⟩
    rw [Finset.mem_range, hN]
    have : wn.2 ≤ t.sup Prod.snd := Finset.le_sup (f := Prod.snd) hwn
    omega
  have hnn : ∀ wn : (ℤ × ℤ) × ℕ, 0 ≤ a ^ wn.2 * (2 : ℝ) ^ wn.1.1 := fun wn => by positivity
  calc ∑ wn ∈ t, a ^ wn.2 * (2 : ℝ) ^ wn.1.1
      ≤ ∑ wn ∈ t₁ ×ˢ Finset.range N, a ^ wn.2 * (2 : ℝ) ^ wn.1.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun wn _ _ => hnn wn
    _ = (∑ W ∈ t₁, (2 : ℝ) ^ W.1) * ∑ n ∈ Finset.range N, a ^ n := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun n _ => ?_
        ring
    _ ≤ (volume Ω).toReal * (1 - a)⁻¹ := by
        refine mul_le_mul ?_ ?_ (Finset.sum_nonneg fun n _ => pow_nonneg ha0 n) ENNReal.toReal_nonneg
        · have hdisj : (↑t₁ : Set (ℤ × ℤ)).PairwiseDisjoint fun p => dyadicInt p.1 p.2 :=
            (pairwiseDisjoint_maxDyadicKeys Ω).subset fun W hW => by
              obtain ⟨wn, hwn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hW)
              exact ht wn hwn
          have hunion : (⋃ W ∈ t₁, dyadicInt W.1 W.2) ⊆ Ω := by
            intro x hx
            obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 hx
            obtain ⟨wn, hwn, rfl⟩ := Finset.mem_image.1 hW
            exact (ht wn hwn).1 hxW
          have h1 := measure_biUnion_finset (μ := volume) hdisj (fun W _ => measurableSet_dyadicInt W.1 W.2)
          have h2 : ∑ W ∈ t₁, (2 : ℝ) ^ W.1 = (volume (⋃ W ∈ t₁, dyadicInt W.1 W.2)).toReal := by
            rw [h1, ENNReal.toReal_sum (fun W _ => by rw [volume_dyadicInt]; exact ENNReal.ofReal_ne_top)]
            exact Finset.sum_congr rfl fun W _ => (toReal_volume_dyadicInt W.1 W.2).symm
          rw [h2]
          exact ENNReal.toReal_mono hΩ (measure_mono hunion)
        · calc ∑ n ∈ Finset.range N, a ^ n ≤ ∑' n : ℕ, a ^ n :=
                (summable_geometric_of_lt_one ha0 ha1).sum_le_tsum _ (fun n _ => pow_nonneg ha0 n)
            _ = (1 - a)⁻¹ := tsum_geometric_of_lt_one ha0 ha1
    _ = _ := mul_comm _ _

/-! ### Decomposition of the inside tiles into layers -/

/-- B3: the sum over the inside tiles is the sum over finitely many layers `(W, n)`, `W ∈ maxDyadicKeys Ω`. -/
theorem exists_layer_decomposition {Ω : Set ℝ} (hΩ : volume Ω ≠ ⊤) (Ps : Finset TriTile) :
    ∃ t : Finset ((ℤ × ℤ) × ℕ), (∀ wn ∈ t, wn.1 ∈ maxDyadicKeys Ω) ∧
      ∀ (G : Type) [AddCommMonoid G] (f : TriTile → G),
        ∑ R ∈ insidePart Ps Ω, f R = ∑ wn ∈ t, ∑ R ∈ layer Ps wn.1 wn.2, f R := by
  classical
  have hex : ∀ R : TriTile, ∃ wn : (ℤ × ℤ) × ℕ, R ∈ insidePart Ps Ω →
      (wn.1 ∈ maxDyadicKeys Ω ∧ R ∈ layer Ps wn.1 wn.2) := by
    intro R
    by_cases hR : R ∈ insidePart Ps Ω
    · obtain ⟨hRP, hRΩ⟩ := mem_insidePart.1 hR
      obtain ⟨wn, hwn, -⟩ := mem_layer_iff_of_subset hΩ hRP hRΩ
      exact ⟨wn, fun _ => hwn⟩
    · exact ⟨default, fun h => absurd h hR⟩
  choose g hg using hex
  have huniq : ∀ R ∈ insidePart Ps Ω, ∀ wn : (ℤ × ℤ) × ℕ, wn.1 ∈ maxDyadicKeys Ω →
      R ∈ layer Ps wn.1 wn.2 → g R = wn := by
    intro R hR wn hW hRl
    obtain ⟨hRP, hRΩ⟩ := mem_insidePart.1 hR
    obtain ⟨wn', -, hu⟩ := mem_layer_iff_of_subset hΩ hRP hRΩ
    exact (hu _ (hg R hR)).trans (hu _ ⟨hW, hRl⟩).symm
  refine ⟨(insidePart Ps Ω).image g, ?_, ?_⟩
  · intro wn hwn
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hwn
    exact (hg R hR).1
  · intro G _ f
    rw [← Finset.sum_fiberwise_of_maps_to (s := insidePart Ps Ω) (t := (insidePart Ps Ω).image g) (g := g)
      (fun R hR => Finset.mem_image_of_mem g hR)]
    refine Finset.sum_congr rfl fun wn hwn => ?_
    congr 1
    ext R
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hR, rfl⟩
      exact (hg R hR).2
    · intro hRl
      obtain ⟨R₀, hR₀, rfl⟩ := Finset.mem_image.1 hwn
      have hW : (g R₀).1 ∈ maxDyadicKeys Ω := (hg R₀ hR₀).1
      obtain ⟨hRP, hRW, -⟩ := mem_layer.1 hRl
      have hRΩ : R.I ⊆ Ω := hRW.trans hW.1
      have hRin : R ∈ insidePart Ps Ω := mem_insidePart.2 ⟨hRP, hRΩ⟩
      exact ⟨hRin, huniq R hRin _ hW hRl⟩


/-! ### The ratio of the depth sum and the truncated masses -/

/-- The ratio `a = 4 · 2^{-(M-1) η}` of the depth sum of B11 (`η = 1/(16 R)`, `M` the tail order). -/
def layerRatio (R M : ℝ) : ℝ := 4 * (2 : ℝ) ^ (-((M - 1) * etaR R))

theorem layerRatio_nonneg (R M : ℝ) : 0 ≤ layerRatio R M := by unfold layerRatio; positivity

/-- `a < 1` iff `(M - 1) η > 2` iff `M > 32 R + 1`. -/
theorem layerRatio_lt_one {R M : ℝ} (hR : 4 ≤ R) (hM : 32 * R + 1 < M) : layerRatio R M < 1 := by
  have hR0 : 0 < R := by linarith
  have h1 : (2 : ℝ) < (M - 1) * etaR R := by
    unfold etaR
    rw [← div_eq_mul_one_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have h2 : (2 : ℝ) ^ (-((M - 1) * etaR R)) < (2 : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  unfold layerRatio
  rw [h3] at h2
  linarith

/-- `μ''_v`, with the convention `μ''_τ = 1`. -/
def muTrunc (E : Fin 3 → Set ℝ) (τ v : Fin 3) : ℝ := if v = τ then 1 else excMassTrunc 48 E τ v

theorem muTrunc_pos {E : Fin 3 → Set ℝ} (hvol : ∀ v, 0 < (volume (E v)).toReal) (τ v : Fin 3) :
    0 < muTrunc E τ v := by
  unfold muTrunc
  split_ifs
  · exact one_pos
  · unfold excMassTrunc excMass
    have := hvol v
    have := hvol τ
    exact lt_min one_pos (by positivity)

theorem muTrunc_le_one (E : Fin 3 → Set ℝ) (τ v : Fin 3) : muTrunc E τ v ≤ 1 := by
  unfold muTrunc
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem muTrunc_rpow_le {E : Fin 3 → Set ℝ} {τ : Fin 3} (hvol : ∀ v, 0 < (volume (E v)).toReal)
    (hmax : ∀ v, (volume (E v)).toReal ≤ (volume (E τ)).toReal) {β : ℝ} (hβ : β ≤ 1) (v : Fin 3) :
    muTrunc E τ v ^ β ≤ 96 * ((volume (E v)).toReal / (volume (E τ)).toReal) ^ β := by
  unfold muTrunc
  by_cases hv : v = τ
  · subst hv
    simp only [ite_true, div_self (hvol v).ne', Real.one_rpow]
    norm_num
  · simp only [hv, ite_false]
    have hτ := hvol τ
    have hr0 : 0 < (volume (E v)).toReal / (volume (E τ)).toReal := div_pos (hvol v) hτ
    have hr1 : (volume (E v)).toReal / (volume (E τ)).toReal ≤ 1 := by
      rw [div_le_one hτ]; exact hmax v
    have : excMassTrunc 48 E τ v = min 1 (96 * ((volume (E v)).toReal / (volume (E τ)).toReal)) := by
      unfold excMassTrunc excMass
      congr 1
      ring
    rw [this]
    exact min_one_mul_rpow_le hr0 hr1 hβ


/-! ### One layer -/

theorem prod_ite_const (τ : Fin 3) (a : ℝ) : ∏ v : Fin 3, (if v = τ then (1 : ℝ) else a) = a ^ 2 := by
  fin_cases τ <;> simp [Fin.prod_univ_three] <;> ring

/-- **One layer of B11**: `‖Λ(layer Ps W n)‖ ≤ C CT a^n |W| ∏_v μ''_v^{β_v}`, generic in the energy family `e`
(conditional on the abstract B5, V12 and the single-scale tree lemma V15s `EnergyTreeSS`).  `M > 32 R + 1` is the tail order. -/
theorem layer_le_of_energy {u : ℝ} (hu : 1 < u) (𝔭 : Params) {e : EnergyFamily} {ints : IntFamily}
    {M : ℝ} (hM : 32 * Rof u + 1 < M) (hints : IntsScale ints) (hmono : EnergyMono e)
    (htail : EnergyTailBound e ints u 𝔭 M)
    (hstep : EnergyStep e u 𝔭) (htree : EnergyTreeSS e u 𝔭) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
      ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
      ∀ (β : Fin 3 → ℝ), Interp.InCornerNbhd (Rof u) β → ∀ (E : Fin 3 → Set ℝ) (τ : Fin 3)
        (h : Fin 3 → ℝ → ZMod P → ℂ), IsHullData u E τ h →
        ∀ W : ℤ × ℤ, W ∈ maxDyadicKeys (exceptionalOmega 48 E τ) → ∀ n : ℕ,
          ‖modelForm T (layer Ps W n) χ m (h 0) (h 1) (h 2)‖ ≤
            C * CT * (layerRatio (Rof u) M ^ n * ((2 : ℝ) ^ W.1 * ∏ v, muTrunc E τ v ^ β v)) := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  have hM2 : 2 ≤ M := by linarith
  obtain ⟨C5, hC5nn, hC5⟩ := htail
  obtain ⟨CE, hCEnn, hCE⟩ := hstep
  obtain ⟨Cf, hCf0, hCf⟩ := form_le_of_energy (A := SingleScale) hu hmono htree
  set Ca : ℝ := ∑ v, CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v))) + 1 with hCa
  have hterm0 : ∀ v, 0 ≤ CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v))) :=
    fun v => mul_nonneg hCEnn (mul_nonneg (by positivity) (by
      have := tailC_nonneg (100 * qX (Rof u) v); linarith))
  have hCa1 : 1 ≤ Ca := by
    have : 0 ≤ ∑ v, CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v))) :=
      Finset.sum_nonneg fun v _ => hterm0 v
    linarith
  have hCaCE : ∀ v, CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v))) ≤ Ca := fun v => by
    have : CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v))) ≤
        ∑ v, CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v))) :=
      Finset.single_le_sum (f := fun v => CE * (2 ^ (50 * qX (Rof u) v) *
        (2 * tailC (100 * qX (Rof u) v)))) (fun v _ => hterm0 v) (Finset.mem_univ v)
    linarith
  set cm : Fin 3 → ℝ := fun _ => max 1 (C5 * tailC M) with hcm
  have hcm1 : ∀ v, 1 ≤ cm v := fun v => le_max_left _ _
  have hcm0 : ∀ v, 0 ≤ cm v := fun v => by linarith [hcm1 v]
  refine ⟨Cf * (∏ v, cm v) * 4 * countConst (Rof u) * Ca, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCf0 (Finset.prod_nonneg fun v _ => hcm0 v))
      (by norm_num)) (countConst_nonneg hR4)) (by linarith)
  intro P _ T CT hT Qs hQ Ps hPs χ m hmd β hβ E τ h hH W hW n
  obtain ⟨hβsum, hβ0, hβ1⟩ := hβ
  have hβsum' : ∑ v, β v = 1 := by rw [Fin.sum_univ_three]; exact hβsum
  have hCT : 0 ≤ CT := not_lt.1 fun hneg => not_bound_of_neg T (by linarith) hneg hT
  have hEm : ∀ i, MeasurableSet (E i) := hH.1
  have hEpos : ∀ i, 0 < volume (E i) := hH.2.1
  have hEfin : ∀ i, volume (E i) < ⊤ := hH.2.2.1
  have hhm : ∀ i, Measurable (h i) := hH.2.2.2.2.1
  have hbdd := hH.yNorm_le_one
  have hvolpos : ∀ v, 0 < (volume (E v)).toReal := fun v =>
    ENNReal.toReal_pos (hEpos v).ne' (hEfin v).ne
  -- the layer
  set L := layer Ps W n with hL
  have hboxL : ∀ R' ∈ L, R'.box ∈ Qs := by
    obtain ⟨Q, W₀, hQ0, hP⟩ := hPs
    intro R' hR'
    exact hQ0 ((hP R').1 (mem_layer.1 hR').1).1
  have hTCL : HasTC L := (hPs.layer W n).hasTC
  have hmdL : IsModelData 𝔭 L χ m := hmd.mono (fun R' hR' => (mem_layer.1 hR').1)
  -- positive reals
  have hmupos : ∀ v, 0 < muTrunc E τ v := muTrunc_pos hvolpos τ
  have hmule : ∀ v, muTrunc E τ v ≤ 1 := muTrunc_le_one E τ
  have hW2 : (0 : ℝ) < (2 : ℝ) ^ W.1 := by positivity
  set Ar : Fin 3 → ℝ := fun v => Ca * (2 : ℝ) ^ W.1 * muTrunc E τ v with hAr
  have hArpos : ∀ v, 0 < Ar v := fun v => mul_pos (mul_pos (by linarith) hW2) (hmupos v)
  have hmuτ : muTrunc E τ τ = 1 := by simp [muTrunc]
  have hArτ : ∀ v, Ar v ≤ Ar τ := fun v => by
    simp only [hAr, hmuτ]
    exact mul_le_mul_of_nonneg_left (hmule v) (mul_pos (by linarith) hW2).le
  have hratio : ∀ v, Ar v / Ar τ = muTrunc E τ v := fun v => by
    simp only [hAr, hmuτ, mul_one]
    exact mul_div_cancel_left₀ _ (mul_pos (by linarith) hW2).ne'
  -- the energy bounds
  set ε : ℝ := (2 : ℝ) ^ (-(M - 1) * (n : ℝ)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : 0 ≤ (M - 1) * (n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
    linarith [neg_mul (M - 1) (n : ℝ)]
  set cc : Fin 3 → ℝ := fun v => cm v * (if v = τ then 1 else (2 : ℝ) ^ (n + 1)) with hcc
  have hcc1 : ∀ v, 1 ≤ cc v := fun v => by
    simp only [hcc]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    split_ifs
    · simpa using hcm1 v
    · exact one_le_mul_of_one_le_of_one_le (hcm1 v) h2
  set Λr : Fin 3 → ℝ := fun v => cc v * (if v = τ then ε else Ar v / Ar τ) with hΛr
  have hΛr0 : ∀ v, 0 ≤ Λr v := fun v => by
    simp only [hΛr]
    refine mul_nonneg (by linarith [hcc1 v]) ?_
    split_ifs
    · exact hε0
    · exact (div_pos (hArpos v) (hArpos τ)).le
  have hΛ : ∀ v, e P h v L ≤ ENNReal.ofReal (Λr v) := by
    intro v
    have hB := hC5 P Qs hQ L hboxL h hhm hbdd v
    by_cases hv : v = τ
    · subst hv
      have hdomτ : ∀ x, yNorm (slotExp u v) (h v x) ≤
          (exceptionalMajor 48 E v).indicator (fun _ => (1 : ℝ)) x := by
        have := hH.dom v
        simp only [domSet, ite_true] at this
        exact this
      refine (le_ofReal_of_tailMass_le (bound := tailConst M * ε) hC5nn hB
        fun W' hW' => ?_).trans ?_
      · obtain ⟨R', hR', rfl⟩ := hints L (W.1 - n) (fun R hR => (mem_layer.1 hR).2.2) W' hW'
        obtain ⟨-, hRW, hs⟩ := mem_layer.1 hR'
        refine (tailMass_slot_le (by linarith) (measurableSet_exceptionalMajor 48 v (hEm v)) hdomτ
          (dyadicInt_toReal_volume_pos (R'.box.scale, R'.pos))).trans ?_
        exact tailMass_exceptionalMajor_le (M := M) (by linarith) (C₀ := 48) (E := E)
          (τ := v) (J := W) hW (s := R'.box.scale) (w := R'.pos) (n := n) hRW (by omega)
      · refine ENNReal.ofReal_le_ofReal ?_
        simp only [hΛr, hcc, hcm, ite_true, mul_one]
        have h1 : C5 * tailConst M ≤ max 1 (C5 * tailC M) :=
          (mul_le_mul_of_nonneg_left (tailConst_le_tailC _) hC5nn).trans (le_max_right _ _)
        calc C5 * (tailConst M * ε) = (C5 * tailConst M) * ε := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h1 hε0
    · have hdomv : ∀ x, yNorm (slotExp u v) (h v x) ≤ (E v).indicator (fun _ => (1 : ℝ)) x := by
        have := hH.dom v
        simp only [domSet, hv, ite_false] at this
        exact this
      refine (le_ofReal_of_tailMass_le
        (bound := tailC M * ((2 : ℝ) ^ (n + 1) * excMassTrunc 48 E τ v)) hC5nn hB
        fun W' hW' => ?_).trans ?_
      · obtain ⟨R', hR', rfl⟩ := hints L (W.1 - n) (fun R hR => (mem_layer.1 hR).2.2) W' hW'
        obtain ⟨-, hRW, hs⟩ := mem_layer.1 hR'
        refine (tailMass_slot_le (by linarith) (hEm v) hdomv
          (dyadicInt_toReal_volume_pos (R'.box.scale, R'.pos))).trans ?_
        exact tailMass_indicator_le_excMassTrunc (M := M) (by linarith) (by norm_num) hv (hEm v)
          (hEfin v).ne hW (s := R'.box.scale) (w := R'.pos) (n := n) hRW (by omega)
      · refine ENNReal.ofReal_le_ofReal ?_
        have hmuv : muTrunc E τ v = excMassTrunc 48 E τ v := by simp [muTrunc, hv]
        simp only [hΛr, hcc, hcm, hv, ite_false, hratio, hmuv]
        have h1 : C5 * tailC M ≤ max 1 (C5 * tailC M) := le_max_right _ _
        have hex0 : 0 ≤ excMassTrunc 48 E τ v := by
          have := (hmupos v).le; rwa [hmuv] at this
        have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1) * excMassTrunc 48 E τ v := mul_nonneg (by positivity) hex0
        calc C5 * (tailC M * ((2 : ℝ) ^ (n + 1) * excMassTrunc 48 E τ v))
            = (C5 * tailC M) * ((2 : ℝ) ^ (n + 1) * excMassTrunc 48 E τ v) := by ring
          _ ≤ max 1 (C5 * tailC M) * ((2 : ℝ) ^ (n + 1) * excMassTrunc 48 E τ v) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = _ := by ring
  -- the localized counts of V12 (B6')
  have hstepE : ∀ (v : Fin 3) (S : Finset TriTile), IsResidual L S → ∃ ts : List Top,
      e P h v (removeTrees S ts) ≤ e P h v S / 2 ∧
      topSum (removedTrees S ts) * e P h v S ^ qPlus (Rof u) v ≤ ENNReal.ofReal (Ar v) := by
    intro v S hS
    obtain ⟨ts, h1, -, h3⟩ := hCE P Qs hQ L S hboxL hTCL hS h hhm hbdd v
    have hSW : ∀ R ∈ S, R.I ⊆ dyadicInt W.1 W.2 := fun R hR => (mem_layer.1 (hS.subset hR)).2.1
    refine ⟨ts, h1, (h3 W hSW).trans ?_⟩
    have hq1 : 1 ≤ qX (Rof u) v := by linarith [two_le_qX hR4 v]
    have hmp := mixedPow_locPoly_le (slotExp_pos hu v) hq1 (measurableSet_domSet hEm τ v) (hH.dom v) W
    have hK2 : (2 : ℝ) ≤ 100 * qX (Rof u) v := by linarith [two_le_qX hR4 v]
    have hint : ∫ x, (domSet E τ v).indicator (1 : ℝ → ℝ) x *
        tailWeight (100 * qX (Rof u) v) ((x - intervalCentre (dyadicInt W.1 W.2)) / (2 : ℝ) ^ W.1) ≤
        2 * tailC (100 * qX (Rof u) v) * (2 : ℝ) ^ W.1 * muTrunc E τ v := by
      by_cases hv : v = τ
      · subst hv
        have := integral_exceptionalMajor_mul_tailWeight_le (K := 100 * qX (Rof u) v) (by linarith) 48 E v
          W.1 W.2
        simp only [domSet, ite_true, hmuτ, mul_one]
        refine this.trans ?_
        have h1 := tailConst_le_tailC (100 * qX (Rof u) v)
        have h2 := tailC_nonneg (100 * qX (Rof u) v)
        exact mul_le_mul_of_nonneg_right (by linarith only [h1, h2]) hW2.le
      · have := integral_indicator_mul_tailWeight_le_excMassTrunc hK2 (by norm_num) hv (hEm v)
          (hEfin v).ne hW
        have hmuv : muTrunc E τ v = excMassTrunc 48 E τ v := by simp [muTrunc, hv]
        simpa only [domSet, hv, ite_false, hmuv] using this
    calc ENNReal.ofReal CE * mixedPow (qX (Rof u) v) (slotExp u v)
          (fun x => ((locPoly W x)⁻¹ : ℂ) • h v x)
        ≤ ENNReal.ofReal CE * ENNReal.ofReal (2 ^ (50 * qX (Rof u) v) *
            (2 * tailC (100 * qX (Rof u) v) * (2 : ℝ) ^ W.1 * muTrunc E τ v)) := by
          gcongr
          refine hmp.trans (ENNReal.ofReal_le_ofReal ?_)
          exact mul_le_mul_of_nonneg_left hint (by positivity)
      _ = ENNReal.ofReal (CE * (2 ^ (50 * qX (Rof u) v) *
            (2 * tailC (100 * qX (Rof u) v) * (2 : ℝ) ^ W.1 * muTrunc E τ v))) :=
          (ENNReal.ofReal_mul hCEnn).symm
      _ ≤ ENNReal.ofReal (Ar v) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : 0 ≤ (2 : ℝ) ^ W.1 * muTrunc E τ v := mul_nonneg hW2.le (hmupos v).le
          calc CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v) * (2 : ℝ) ^ W.1 * muTrunc E τ v))
              = (CE * (2 ^ (50 * qX (Rof u) v) * (2 * tailC (100 * qX (Rof u) v)))) *
                  ((2 : ℝ) ^ W.1 * muTrunc E τ v) := by ring
            _ ≤ Ca * ((2 : ℝ) ^ W.1 * muTrunc E τ v) := mul_le_mul_of_nonneg_right (hCaCE v) h2
            _ = Ar v := by simp only [hAr]; ring
  have hssL : ∀ S : Finset TriTile, S ⊆ L → SingleScale S := fun S hS =>
    ⟨W.1 - n, fun R' hR' => ((mem_layer.1 (hS hR')).2.2)⟩
  have hmainB := hCf P T CT hT Qs hQ L hboxL hTCL hssL χ m hmdL h hhm hbdd
    (fun v => ENNReal.ofReal (Λr v)) (fun v => ENNReal.ofReal_lt_top) hΛ Ar hArpos hstepE
  have hη0 : 0 ≤ etaR (Rof u) := by unfold etaR; positivity
  have hts := tsum_min_le_region (R := Rof u) (θ := etaR (Rof u)) hR4 hη0 le_rfl τ Ar hArpos hArτ
    hβsum' hβ0 hβ1 Λr cc ε hΛr0 hcc1 hε0 hε1 (fun v => le_rfl)
  have hfin := hmainB.trans (mul_le_mul_right hts _)
  rw [← ENNReal.ofReal_mul (mul_nonneg hCf0 hCT), ← ofReal_norm] at hfin
  -- the algebra
  have hprodA : ∏ v, Ar v ^ β v = Ca * (2 : ℝ) ^ W.1 * ∏ v, muTrunc E τ v ^ β v := by
    simp only [hAr]
    rw [Finset.prod_congr rfl fun v _ => Real.mul_rpow (by positivity : (0 : ℝ) ≤ Ca * (2 : ℝ) ^ W.1)
        (hmupos v).le, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by positivity : 0 < Ca * (2 : ℝ) ^ W.1), hβsum', Real.rpow_one]
  have hprodcc : ∏ v, cc v = (∏ v, cm v) * ((2 : ℝ) ^ (n + 1)) ^ 2 := by
    simp only [hcc]
    rw [Finset.prod_mul_distrib, prod_ite_const]
  have hε_eq : ε ^ etaR (Rof u) = (2 ^ (-((M - 1) * etaR (Rof u)))) ^ n := by
    simp only [hε]
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  have h4 : ((2 : ℝ) ^ (n + 1)) ^ 2 = 4 * 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
    ring
  have hnn : 0 ≤ Cf * CT * ((∏ v, cc v) * ε ^ etaR (Rof u) * (countConst (Rof u) * ∏ v, Ar v ^ β v)) := by
    refine mul_nonneg (mul_nonneg hCf0 hCT) (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg fun v _ => by linarith [hcc1 v]) (Real.rpow_nonneg hε0 _))
      (mul_nonneg (countConst_nonneg hR4) (Finset.prod_nonneg fun v _ =>
        Real.rpow_nonneg (hArpos v).le _)))
  refine ((ENNReal.ofReal_le_ofReal_iff hnn).1 hfin).trans_eq ?_
  rw [hprodA, hprodcc, hε_eq, h4]
  unfold layerRatio
  rw [mul_pow]
  ring


/-! ### B11: the sum over the layers -/

/-- **B11 (inside)**, generic in the energy family `e`: the sum of the layers (B3), a geometric sum over the depth
`n` and `∑_W |W| ≤ |Ω| ≤ |E_τ|`. -/
theorem inside_le_of_energy {u : ℝ} (hu : 1 < u) (𝔭 : Params) {e : EnergyFamily} {ints : IntFamily}
    {M : ℝ} (hM : 32 * Rof u + 1 < M) (hints : IntsScale ints) (hmono : EnergyMono e)
    (htail : EnergyTailBound e ints u 𝔭 M)
    (hstep : EnergyStep e u 𝔭) (htree : EnergyTreeSS e u 𝔭) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
      ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
      ∀ (β : Fin 3 → ℝ), Interp.InCornerNbhd (Rof u) β → ∀ (E : Fin 3 → Set ℝ) (τ : Fin 3)
        (h : Fin 3 → ℝ → ZMod P → ℂ), IsHullData u E τ h →
          ‖modelForm T (insidePart Ps (exceptionalOmega 48 E τ)) χ m (h 0) (h 1) (h 2)‖ ≤
            C * CT * ∏ i, (volume (E i)).toReal ^ β i := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  obtain ⟨Cl, hCl0, hCl⟩ := layer_le_of_energy hu 𝔭 hM hints hmono htail hstep htree
  have ha0 := layerRatio_nonneg (Rof u) M
  have ha1 := layerRatio_lt_one hR4 hM
  refine ⟨Cl * 96 ^ 3 * (1 - layerRatio (Rof u) M)⁻¹, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg hCl0 (by positivity)) (inv_nonneg.2 (by linarith))
  intro P _ T CT hT Qs hQ Ps hPs χ m hmd β hβ E τ h hH
  have hβ' := hβ
  obtain ⟨hβsum, hβ0, hβ1⟩ := hβ
  have hβsum' : ∑ v, β v = 1 := by rw [Fin.sum_univ_three]; exact hβsum
  have hCT : 0 ≤ CT := not_lt.1 fun hneg => not_bound_of_neg T (by linarith) hneg hT
  have hEm : ∀ i, MeasurableSet (E i) := hH.1
  have hEpos : ∀ i, 0 < volume (E i) := hH.2.1
  have hEfin : ∀ i, volume (E i) < ⊤ := hH.2.2.1
  have hEmax : ∀ i, volume (E i) ≤ volume (E τ) := hH.2.2.2.1
  have hvolpos : ∀ v, 0 < (volume (E v)).toReal := fun v =>
    ENNReal.toReal_pos (hEpos v).ne' (hEfin v).ne
  have hvolmax : ∀ v, (volume (E v)).toReal ≤ (volume (E τ)).toReal := fun v =>
    ENNReal.toReal_mono (hEfin τ).ne (hEmax v)
  have hΩ0 : 0 < (volume (E τ)).toReal := hvolpos τ
  set Ω := exceptionalOmega 48 E τ with hΩ
  have hΩtop : volume Ω ≠ ⊤ :=
    volume_exceptionalOmega_ne_top hEm (fun i => (hEpos i).ne') (fun i => (hEfin i).ne) (by norm_num) τ
  -- `|Ω| ≤ |E τ|`
  have hΩvol : (volume Ω).toReal ≤ (volume (E τ)).toReal := by
    have h1 := volume_exceptionalOmega_le hEm (fun i => (hEpos i).ne') (fun i => (hEfin i).ne)
      (by norm_num : (0 : ℝ) < 48) τ
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    refine h2.trans ?_
    have : 8 * (volume (E τ)).toReal / 48 ≤ (volume (E τ)).toReal := by linarith
    exact this
  -- `β_v ≤ 1`
  have hβle : ∀ v, β v ≤ 1 := by
    have hR0 : 0 < Rof u := by linarith
    have h8 : 1 / (8 * Rof u) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    obtain ⟨a0, b0⟩ := abs_le.1 hβ0
    obtain ⟨a1, b1⟩ := abs_le.1 hβ1
    intro v
    fin_cases v
    · show β 0 ≤ 1; linarith
    · show β 1 ≤ 1; linarith
    · show β 2 ≤ 1; linarith
  -- the sum over layers
  obtain ⟨t, ht, hdec⟩ := exists_layer_decomposition hΩtop Ps
  have hsplit : modelForm T (insidePart Ps Ω) χ m (h 0) (h 1) (h 2) =
      ∑ wn ∈ t, modelForm T (layer Ps wn.1 wn.2) χ m (h 0) (h 1) (h 2) := by
    unfold modelForm
    exact hdec ℂ (fun R => ∫ x, (χ R x : ℂ) *
      T (tmult (m R 0) (h 0) x) (tmult (m R 1) (h 1) x) (tmult (m R 2) (h 2) x))
  -- `∏ μ''^β ≤ 96³ ∏ (|E_v|/|E_τ|)^β = 96³ ∏ |E_v|^β / |E_τ|`
  have hmuprod : ∏ v, muTrunc E τ v ^ β v ≤ 96 ^ 3 *
      ((∏ v, (volume (E v)).toReal ^ β v) / (volume (E τ)).toReal) := by
    have h1 : ∏ v, muTrunc E τ v ^ β v ≤
        ∏ v, 96 * ((volume (E v)).toReal / (volume (E τ)).toReal) ^ β v :=
      Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg (muTrunc_pos hvolpos τ v).le _)
        (fun v _ => muTrunc_rpow_le hvolpos hvolmax (hβle v) v)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ∏ v, ((volume (E v)).toReal / (volume (E τ)).toReal) ^ β v =
        (∏ v, (volume (E v)).toReal ^ β v) / (volume (E τ)).toReal := by
      rw [Finset.prod_congr rfl fun v _ => Real.div_rpow ENNReal.toReal_nonneg hΩ0.le (β v),
        Finset.prod_div_distrib, ← Real.rpow_sum_of_pos hΩ0, hβsum', Real.rpow_one]
    rw [h2] at h1
    exact h1
  set pr : ℝ := (∏ v, (volume (E v)).toReal ^ β v) / (volume (E τ)).toReal with hpr
  have hpr0 : 0 ≤ pr := div_nonneg (Finset.prod_nonneg fun v _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    hΩ0.le
  have hlayer : ∀ wn ∈ t, ‖modelForm T (layer Ps wn.1 wn.2) χ m (h 0) (h 1) (h 2)‖ ≤
      (Cl * CT * 96 ^ 3 * pr) * (layerRatio (Rof u) M ^ wn.2 * (2 : ℝ) ^ wn.1.1) := by
    intro wn hwn
    refine (hCl P T CT hT Qs hQ Ps hPs χ m hmd β hβ' E τ h hH wn.1 (ht wn hwn) wn.2).trans ?_
    have h2 : (0 : ℝ) ≤ Cl * CT := mul_nonneg hCl0 hCT
    calc Cl * CT * (layerRatio (Rof u) M ^ wn.2 * ((2 : ℝ) ^ wn.1.1 * ∏ v, muTrunc E τ v ^ β v))
        ≤ Cl * CT * (layerRatio (Rof u) M ^ wn.2 * ((2 : ℝ) ^ wn.1.1 * (96 ^ 3 * pr))) := by
          gcongr
      _ = _ := by ring
  have hsum := sum_geom_mul_le hΩtop ha0 ha1 t ht
  calc ‖modelForm T (insidePart Ps Ω) χ m (h 0) (h 1) (h 2)‖
      = ‖∑ wn ∈ t, modelForm T (layer Ps wn.1 wn.2) χ m (h 0) (h 1) (h 2)‖ := by rw [hsplit]
    _ ≤ ∑ wn ∈ t, ‖modelForm T (layer Ps wn.1 wn.2) χ m (h 0) (h 1) (h 2)‖ := norm_sum_le _ _
    _ ≤ ∑ wn ∈ t, (Cl * CT * 96 ^ 3 * pr) * (layerRatio (Rof u) M ^ wn.2 * (2 : ℝ) ^ wn.1.1) :=
        Finset.sum_le_sum hlayer
    _ = (Cl * CT * 96 ^ 3 * pr) * ∑ wn ∈ t, layerRatio (Rof u) M ^ wn.2 * (2 : ℝ) ^ wn.1.1 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (Cl * CT * 96 ^ 3 * pr) * ((1 - layerRatio (Rof u) M)⁻¹ * (volume (E τ)).toReal) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hΩvol (inv_nonneg.2 (by linarith))
    _ = Cl * 96 ^ 3 * (1 - layerRatio (Rof u) M)⁻¹ * CT * ∏ v, (volume (E v)).toReal ^ β v := by
        simp only [hpr]
        field_simp

end PrimeBHT.TimeFrequency.X2.V16
