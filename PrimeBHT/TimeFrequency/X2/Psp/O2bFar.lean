module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardMu
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapCoef

/-!
# X2, V13 O2 (b-far): the outside terms (d1)/(d2) of the overlapping projection (pure analysis part)

`docs/audits/X2-O2-coordination.md` rows d1/d2-a, d1/d2-b.  Owner: V13.

* `integral_Ioi_one_add_rpow`, `tail_integral_le`: `∫_{|y - x| ≥ r} (1 + l |y - x|)^{-q} dy ≤ 2 (1 + l r)^{-(q-1)} / (l (q - 1))`;
* `exists_endpoint_between`, `exists_bdryEtil_between`: a point of `Ẽ_σ` and a point outside are separated by an endpoint of `∂Ẽ_σ`;
* `growth_around`: `‖T_σF(y)‖ ≤ polyC ⟨(y - x)/2^σ⟩^{N'} E` around ANY `x ∈ Ẽ_σ`;
* `outside_conv_bound`: for a kernel `K` with `‖K w‖ ≤ κ (1 + l |w|)^{-M}` and a (`Y`-valued) function `Φ` with
  `‖Φ(y)‖_{L²(Y)} ≤ A (1 + l |y - x'|)^N` supported in `{|y - x| ≥ r}`: `‖∫ K(x - y) Φ(y) dy‖_{L²(Y)} ≤ 2 κ A (1 + l |x - x'|)^N (1 + l r)^{-(M-N-1)}/(l (M-N-1))`
  (needs `M ≥ N + 2`; with `M = 𝔭.D`, `N = 𝔭.N/8` and the margin `N/8 + 3 ≤ D` the exponent is `≥ 2`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- `∫_{u > r} (1 + l u)^{-q} du = (1 + l r)^{-(q-1)} / (l (q - 1))`. -/
theorem integral_Ioi_one_add_rpow {l q r : ℝ} (hl : 0 < l) (hq : 1 < q) (hr : 0 ≤ r) :
    ∫ u in Ioi r, (1 + l * u) ^ (-q) = (1 + l * r) ^ (-(q - 1)) / (l * (q - 1)) ∧
      IntegrableOn (fun u => (1 + l * u) ^ (-q)) (Ioi r) := by
  have hq1 : 0 < q - 1 := by linarith
  have hd : ∀ u ∈ Ici r, HasDerivAt (fun u : ℝ => -((1 + l * u) ^ (-(q - 1)) / (l * (q - 1)))) ((1 + l * u) ^ (-q)) u := by
    intro u hu
    have hu0 : 0 < 1 + l * u := by have := hu.out; nlinarith
    have h1 : HasDerivAt (fun u : ℝ => 1 + l * u) l u := by
      simpa using ((hasDerivAt_id u).const_mul l).const_add 1
    have h2 := h1.rpow_const (p := -(q - 1)) (Or.inl hu0.ne')
    have h3 := (h2.div_const (l * (q - 1))).neg
    convert h3 using 1
    rw [show -(q - 1) - 1 = -q by ring]
    field_simp
  have hnn : ∀ u ∈ Ioi r, 0 ≤ (1 + l * u) ^ (-q) := fun u hu =>
    Real.rpow_nonneg (by have := hu.out; nlinarith) _
  have ht : Tendsto (fun u : ℝ => -((1 + l * u) ^ (-(q - 1)) / (l * (q - 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => 1 + l * u) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hl)
    have h2 : Tendsto (fun u : ℝ => (1 + l * u) ^ (-(q - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hq1).comp h1
    have h3 := (h2.div_const (l * (q - 1))).neg
    simpa using h3
  refine ⟨?_, integrableOn_Ioi_deriv_of_nonneg' hd hnn ht⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn ht]
  ring

/-- The tail `{|y - x| ≥ r}` of `(1 + l |y - x|)^{-q}`: integrable, integral `≤ 2 (1 + l r)^{-(q-1)} / (l (q - 1))`. -/
theorem tail_integral_le {l q r : ℝ} (x : ℝ) (hl : 0 < l) (hq : 1 < q) (hr : 0 ≤ r) :
    Integrable (fun y : ℝ => if r ≤ |y - x| then (1 + l * |y - x|) ^ (-q) else 0) ∧
      ∫ y, (if r ≤ |y - x| then (1 + l * |y - x|) ^ (-q) else 0) ≤ 2 * ((1 + l * r) ^ (-(q - 1)) / (l * (q - 1))) := by
  obtain ⟨hI, hint⟩ := integral_Ioi_one_add_rpow hl hq hr
  set h : ℝ → ℝ := fun u => (1 + l * u) ^ (-q) with hh
  set T : ℝ → ℝ := fun y => if r ≤ |y - x| then (1 + l * |y - x|) ^ (-q) else 0 with hT
  set T₁ : ℝ → ℝ := fun y => (Ici r).indicator h (y - x) with hT₁
  set T₂ : ℝ → ℝ := fun y => T₁ (2 * x - y) with hT₂
  have hint' : IntegrableOn h (Ici r) := (integrableOn_Ici_iff_integrableOn_Ioi).2 hint
  have hT₁i : Integrable T₁ := by
    have : Integrable ((Ici r).indicator h) := (integrable_indicator_iff measurableSet_Ici).2 hint'
    exact this.comp_sub_right x
  have hT₂i : Integrable T₂ := hT₁i.comp_sub_left (2 * x)
  have hT₁int : ∫ y, T₁ y = ∫ u in Ioi r, h u := by
    rw [hT₁, integral_sub_right_eq_self ((Ici r).indicator h) x, integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi]
  have hT₂int : ∫ y, T₂ y = ∫ y, T₁ y := by
    rw [hT₂]
    exact integral_sub_left_eq_self T₁ volume (2 * x)
  have hnn : ∀ u, 0 ≤ (Ici r).indicator h u := fun u => by
    unfold Set.indicator; split_ifs with hu
    · exact Real.rpow_nonneg (by have := hu.out; nlinarith) _
    · exact le_rfl
  have hle : ∀ y, T y ≤ T₁ y + T₂ y := by
    intro y
    have h1 : 0 ≤ T₁ y := hnn _
    have h2 : 0 ≤ T₂ y := hnn _
    by_cases hy : r ≤ |y - x|
    · have hTy : T y = (1 + l * |y - x|) ^ (-q) := by simp [hT, hy]
      rcases abs_cases (y - x) with ⟨ha, _⟩ | ⟨ha, _⟩
      · have hmem : y - x ∈ Ici r := by rw [ha] at hy; exact hy
        have : T₁ y = (1 + l * |y - x|) ^ (-q) := by
          simp only [hT₁, Set.indicator_of_mem hmem, hh, ha]
        rw [hTy, ← this]; linarith
      · have hmem : 2 * x - y - x ∈ Ici r := by
          rw [Set.mem_Ici, show 2 * x - y - x = -(y - x) by ring]; rw [ha] at hy; linarith
        have : T₂ y = (1 + l * |y - x|) ^ (-q) := by
          simp only [hT₂, hT₁, Set.indicator_of_mem hmem, hh]
          rw [show 2 * x - y - x = -(y - x) by ring, ha]
        rw [hTy, ← this]; linarith
    · have : T y = 0 := by simp [hT, hy]
      rw [this]; linarith
  have hTm : Measurable T := by
    refine Measurable.ite (measurableSet_le measurable_const (by fun_prop)) ?_ measurable_const
    exact ((by fun_prop : Continuous fun y : ℝ => 1 + l * |y - x|).rpow_const (fun y => Or.inl (by positivity))).measurable
  have hT0 : ∀ y, 0 ≤ T y := fun y => by
    simp only [hT]; split_ifs
    · exact Real.rpow_nonneg (by positivity) _
    · exact le_rfl
  have hTi : Integrable T := by
    refine (hT₁i.add hT₂i).mono' hTm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (hT0 y)]
    exact hle y
  refine ⟨hTi, ?_⟩
  calc ∫ y, T y ≤ ∫ y, (T₁ y + T₂ y) := integral_mono hTi (hT₁i.add hT₂i) hle
    _ = (∫ y, T₁ y) + ∫ y, T₂ y := integral_add hT₁i hT₂i
    _ = 2 * ((1 + l * r) ^ (-(q - 1)) / (l * (q - 1))) := by
        rw [hT₂int, hT₁int, hI]; ring

theorem peetre_one_add {l : ℝ} (hl : 0 < l) (x x' y : ℝ) :
    1 + l * |y - x'| ≤ (1 + l * |y - x|) * (1 + l * |x - x'|) := by
  have h1 : |y - x'| ≤ |y - x| + |x - x'| := by
    have := abs_add_le (y - x) (x - x')
    rwa [show y - x + (x - x') = y - x' by ring] at this
  nlinarith [abs_nonneg (y - x), abs_nonneg (x - x'), mul_nonneg hl.le (abs_nonneg (y - x)),
    mul_nonneg hl.le (abs_nonneg (x - x')), mul_nonneg (mul_nonneg hl.le (abs_nonneg (y - x))) (mul_nonneg hl.le (abs_nonneg (x - x')))]

theorem inv_pow_mul_pow {a : ℝ} (ha : 1 ≤ a) {N M : ℕ} (hM : N + 2 ≤ M) :
    (a⁻¹) ^ M * a ^ N = a ^ (-(((M - N : ℕ) : ℝ))) := by
  have ha0 : 0 < a := by linarith
  rw [Real.rpow_neg ha0.le, Real.rpow_natCast, inv_pow]
  have : a ^ M = a ^ N * a ^ (M - N) := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

/-- **(d1)/(d2), pure analysis**: the convolution of a kernel with decay `M` against a function of polynomial growth `N` (relative to a point
`x'`), supported at distance `≥ r` from `x`, decays like `(1 + l r)^{-(M - N - 1)}` (needs `M ≥ N + 2`). -/
theorem outside_conv_bound {P : ℕ} [NeZero P] {l κ A : ℝ} {N M : ℕ} (hl : 0 < l) (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hM : N + 2 ≤ M)
    {x x' r : ℝ} (hr : 0 ≤ r) {K : ℝ → ℂ} (hKm : Measurable K) (hK : ∀ w, ‖K w‖ ≤ κ * ((1 + l * |w|)⁻¹) ^ M)
    {Φ : ℝ → ZMod P → ℂ} (hΦm : Measurable Φ)
    (hΦ : ∀ y, yNorm 2 (Φ y) ≤ if r ≤ |y - x| then A * (1 + l * |y - x'|) ^ N else 0) :
    yNorm 2 (fun y' => ∫ y, K (x - y) * Φ y y') ≤
      2 * (κ * A * (1 + l * |x - x'|) ^ N) *
        ((1 + l * r) ^ (-(((M - N : ℕ) : ℝ) - 1)) / (l * (((M - N : ℕ) : ℝ) - 1))) := by
  have hq : (2 : ℝ) ≤ ((M - N : ℕ) : ℝ) := by
    have : 2 ≤ M - N := by omega
    exact_mod_cast this
  set q : ℝ := ((M - N : ℕ) : ℝ) with hqdef
  obtain ⟨hTi, hTint⟩ := tail_integral_le (l := l) (q := q) (r := r) x hl (by linarith) hr
  set T : ℝ → ℝ := fun y => if r ≤ |y - x| then (1 + l * |y - x|) ^ (-q) else 0 with hT
  set b : ℝ := 1 + l * |x - x'| with hb
  have hb1 : 1 ≤ b := by rw [hb]; have := mul_nonneg hl.le (abs_nonneg (x - x')); linarith
  set c₁ : ℝ := b ^ N with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hP : 0 ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ := by positivity
  -- the pointwise bound
  have hV : ∀ y, yNorm 2 (fun y' => K (x - y) * Φ y y') ≤ κ * A * c₁ * T y := by
    intro y
    rw [yNorm_fun_const_mul (by norm_num)]
    by_cases hy : r ≤ |y - x|
    · have h1 := hΦ y
      rw [ite_eq_left hy] at h1
      have hT' : T y = (1 + l * |y - x|) ^ (-q) := by simp [hT, hy]
      rw [hT']
      set a : ℝ := 1 + l * |y - x| with ha
      have ha1 : 1 ≤ a := by rw [ha]; have := mul_nonneg hl.le (abs_nonneg (y - x)); linarith
      have hKy : ‖K (x - y)‖ ≤ κ * (a⁻¹) ^ M := by
        have := hK (x - y)
        rwa [show |x - y| = |y - x| from abs_sub_comm _ _] at this
      have hpe := peetre_one_add hl x x' y
      have h2 : yNorm 2 (Φ y) ≤ A * (a ^ N * c₁) := by
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
        calc (1 + l * |y - x'|) ^ N ≤ (a * b) ^ N := pow_le_pow_left₀ (by positivity) hpe N
          _ = a ^ N * c₁ := by rw [mul_pow]
      have hid := inv_pow_mul_pow ha1 hM
      calc ‖K (x - y)‖ * yNorm 2 (Φ y) ≤ (κ * (a⁻¹) ^ M) * (A * (a ^ N * c₁)) :=
            mul_le_mul hKy h2 (yNorm_nonneg' _ _) (by positivity)
        _ = κ * A * c₁ * ((a⁻¹) ^ M * a ^ N) := by ring
        _ = _ := by rw [hid]
    · have h1 := hΦ y
      rw [ite_eq_right hy] at h1
      have h0 : yNorm 2 (Φ y) = 0 := le_antisymm h1 (yNorm_nonneg' _ _)
      have hT' : T y = 0 := by simp [hT, hy]
      rw [h0, hT']; simp
  -- coordinate integrability
  have hmaj : Integrable (fun y => (P : ℝ) ^ (2 : ℝ)⁻¹ * (κ * A * c₁ * T y)) := (hTi.const_mul (κ * A * c₁)).const_mul _
  have hcoord : ∀ y', Integrable (fun y => K (x - y) * Φ y y') := by
    intro y'
    have hmeas : AEStronglyMeasurable (fun y => K (x - y) * Φ y y') volume := by
      refine Measurable.aestronglyMeasurable ?_
      exact (hKm.comp (measurable_const.sub measurable_id)).mul ((measurable_pi_apply y').comp hΦm)
    refine hmaj.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
    have h1 := norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (fun y' => K (x - y) * Φ y y') y'
    exact h1.trans (mul_le_mul_of_nonneg_left (hV y) hP)
  refine (yNorm_integral_le_of_one_le (by norm_num) (fun y y' => K (x - y) * Φ y y') hcoord).trans ?_
  have hTi' : Integrable (fun y => κ * A * c₁ * T y) := hTi.const_mul _
  calc ∫ y, yNorm 2 (fun y' => K (x - y) * Φ y y') ≤ ∫ y, κ * A * c₁ * T y :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => yNorm_nonneg' _ _) hTi'
          (Filter.Eventually.of_forall hV)
    _ = κ * A * c₁ * ∫ y, T y := integral_const_mul _ _
    _ ≤ κ * A * c₁ * (2 * ((1 + l * r) ^ (-(q - 1)) / (l * (q - 1)))) :=
        mul_le_mul_of_nonneg_left hTint (by positivity)
    _ = _ := by ring
theorem exists_edge_right (V : Finset ℤ) {a : ℤ} (ha : a ∈ V) :
    ∀ (n : ℕ) (b : ℤ), b = a + 1 + n → b ∉ V → ∃ c : ℤ, a < c ∧ c ≤ b ∧ c - 1 ∈ V ∧ c ∉ V := by
  intro n
  induction n with
  | zero => intro b hb hbV; exact ⟨b, by omega, le_rfl, by simpa [show b - 1 = a by omega] using ha, hbV⟩
  | succ n ih =>
    intro b hb hbV
    by_cases h : b - 1 ∈ V
    · exact ⟨b, by omega, le_rfl, h, hbV⟩
    · obtain ⟨c, h1, h2, h3, h4⟩ := ih (b - 1) (by omega) h
      exact ⟨c, h1, by omega, h3, h4⟩

theorem exists_edge_left (V : Finset ℤ) {a : ℤ} (ha : a ∈ V) :
    ∀ (n : ℕ) (b : ℤ), b = a - 1 - n → b ∉ V → ∃ c : ℤ, c < a ∧ b ≤ c ∧ c + 1 ∈ V ∧ c ∉ V := by
  intro n
  induction n with
  | zero => intro b hb hbV; exact ⟨b, by omega, le_rfl, by simpa [show b + 1 = a by omega] using ha, hbV⟩
  | succ n ih =>
    intro b hb hbV
    by_cases h : b + 1 ∈ V
    · exact ⟨b, by omega, le_rfl, h, hbV⟩
    · obtain ⟨c, h1, h2, h3, h4⟩ := ih (b + 1) (by omega) h
      exact ⟨c, h1, by omega, h3, h4⟩

/-- **A crossing point is an endpoint**: if `x` lies in a key interval of `V` and `y` in a non-key interval, some endpoint of `V` is at least as
close to `x` as `y` is. -/
theorem exists_endpoint_between (σ : ℤ) (V : Finset ℤ) {x y : ℝ} (hx : ⌊x / (2 : ℝ) ^ σ⌋ ∈ V) (hy : ⌊y / (2 : ℝ) ^ σ⌋ ∉ V) :
    ∃ z ∈ leftEndsOf σ V ∪ rightEndsOf σ V, |x - z| ≤ |y - x| ∧ |y - z| ≤ |y - x| := by
  have hp := zpow_two_pos σ
  set a : ℤ := ⌊x / (2 : ℝ) ^ σ⌋ with ha
  set b : ℤ := ⌊y / (2 : ℝ) ^ σ⌋ with hb
  have hxa1 : (2 : ℝ) ^ σ * a ≤ x := by
    have := Int.floor_le (x / (2 : ℝ) ^ σ)
    rw [le_div_iff₀ hp] at this; linarith
  have hxa2 : x < (2 : ℝ) ^ σ * (a + 1) := by
    have := Int.lt_floor_add_one (x / (2 : ℝ) ^ σ)
    rw [div_lt_iff₀ hp] at this; linarith
  have hyb1 : (2 : ℝ) ^ σ * b ≤ y := by
    have := Int.floor_le (y / (2 : ℝ) ^ σ)
    rw [le_div_iff₀ hp] at this; linarith
  have hyb2 : y < (2 : ℝ) ^ σ * (b + 1) := by
    have := Int.lt_floor_add_one (y / (2 : ℝ) ^ σ)
    rw [div_lt_iff₀ hp] at this; linarith
  have hab : a ≠ b := fun h => hy (h ▸ hx)
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_edge_right V hx (b - a - 1).toNat b (by omega) hy
    refine ⟨(2 : ℝ) ^ σ * (c : ℝ), Finset.mem_union_right _ (mem_rightEndsOf.2 ⟨c - 1, hc3, by simpa using hc4, by push_cast; ring⟩), ?_⟩
    have hca : ((a : ℝ) + 1) ≤ c := by exact_mod_cast hc1
    have hcb : (c : ℝ) ≤ b := by exact_mod_cast hc2
    have h1 : x < (2 : ℝ) ^ σ * c := by nlinarith
    have h2 : (2 : ℝ) ^ σ * c ≤ y := by nlinarith
    rw [abs_of_neg (show x - (2 : ℝ) ^ σ * (c : ℝ) < 0 by linarith), abs_of_pos (show 0 < y - x by linarith),
      abs_of_nonneg (show 0 ≤ y - (2 : ℝ) ^ σ * (c : ℝ) by linarith)]
    constructor <;> linarith
  · obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_edge_left V hx (a - b - 1).toNat b (by omega) hy
    refine ⟨(2 : ℝ) ^ σ * ((c : ℝ) + 1), Finset.mem_union_left _ (mem_leftEndsOf.2 ⟨c + 1, hc3, by simpa using hc4, by push_cast; ring⟩), ?_⟩
    have hca : (c : ℝ) + 1 ≤ a := by exact_mod_cast hc1
    have hcb : (b : ℝ) ≤ c := by exact_mod_cast hc2
    have h1 : y < (2 : ℝ) ^ σ * ((c : ℝ) + 1) := by nlinarith
    have h2 : (2 : ℝ) ^ σ * ((c : ℝ) + 1) ≤ x := by nlinarith
    rw [abs_of_nonneg (show 0 ≤ x - (2 : ℝ) ^ σ * ((c : ℝ) + 1) by linarith), abs_of_neg (show y - x < 0 by linarith),
      abs_of_neg (show y - (2 : ℝ) ^ σ * ((c : ℝ) + 1) < 0 by linarith)]
    constructor <;> linarith

theorem mem_eTil_floor {TA : Finset TriTile} {W : ℤ × ℤ} {σ : ℤ} {x : ℝ} :
    x ∈ eTil TA W σ ↔ ⌊x / (2 : ℝ) ^ σ⌋ ∈ eTilKeysF TA W σ := by
  constructor
  · intro hx
    unfold eTil at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    rw [← (mem_dyadicInt_iff_floor.1 hxv)]
    exact mem_eTilKeysF.2 hv
  · intro h
    unfold eTil
    simp only [Set.mem_iUnion]
    exact ⟨_, mem_eTilKeysF.1 h, mem_dyadicInt_floor σ x⟩

/-- **A point of `Ẽ_σ` and a point outside are separated by an endpoint of `∂Ẽ_σ`** at least as close to the first as the second is. -/
theorem exists_bdryEtil_between {TA : Finset TriTile} {W : ℤ × ℤ} {σ : ℤ} {x y : ℝ} (hx : x ∈ eTil TA W σ) (hy : y ∉ eTil TA W σ) :
    ∃ z ∈ bdryEnds TA W σ, |x - z| ≤ |y - x| ∧ |y - z| ≤ |y - x| :=
  exists_endpoint_between σ (eTilKeysF TA W σ) (mem_eTil_floor.1 hx) (fun h => hy (mem_eTil_floor.2 h))

/-- **Growth of the low-pass operator around any point of `Ẽ_σ`** (`poly_growth` at the centre `x`): for `x ∈ Ẽ_σ`, all `y`,
`‖T_σ F(y)‖_{L^s(Y)} ≤ polyC · ⟨(y - x)/2^σ⟩^{N'} · engTop` (`N' = 𝔭.N`, for the class `𝔭 = 𝔭.tree` of the energies). -/
theorem growth_around {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {σ : ℤ} (hlat : ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ)
    {x : ℝ} (hx : x ∈ eTil TA t.1 σ) (y : ℝ) :
    ENNReal.ofReal (yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F y)) ≤
      ENNReal.ofReal (polyC 𝔭 q) * ENNReal.ofReal (jb ((y - x) / (2 : ℝ) ^ σ) ^ 𝔭.N) * engTop 𝔭 s k F Cs q := by
  have hp := zpow_two_pos σ
  have hu := mem_dyadicInt_floor σ x
  have hxu : x ∈ dilate 3 (dyadicInt σ ⌊x / (2 : ℝ) ^ σ⌋) ∩ eTil TA t.1 σ :=
    ⟨dyadicInt_subset_dilate (by norm_num) σ _ hu, hx⟩
  obtain ⟨R, hR, hRs, v, hRv, hRJ, hv5⟩ := exists_lattice_key_near hJ2 hlat ⟨x, hxu⟩
  have hdist : |x - dyCentre σ v| ≤ 3 * (2 : ℝ) ^ σ := by
    have hlt : (2 : ℝ) ^ σ * v < (2 : ℝ) ^ σ * ((v : ℝ) + 1) := by nlinarith
    have hsub5 := hv5
    rw [dilate_dyadicInt, dyadicInt_eq_Ico] at hsub5
    obtain ⟨h1, h2⟩ := (Set.Ico_subset_Ico_iff hlt).1 hsub5
    obtain ⟨hx1, hx2⟩ := hu
    unfold dyCentre
    rw [abs_le]
    constructor <;> nlinarith
  exact poly_growth h𝔭 hη' hs hq hF hFb (hsub hR) (hov R hR) hRv (by simpa using hRJ) hdist y

end PrimeBHT.TimeFrequency.X2
