module

public import PrimeBHT.TimeFrequency.X2.Psp.O2bOut
public import PrimeBHT.TimeFrequency.X2.Psp.O2bWeight
public import PrimeBHT.TimeFrequency.X2.Psp.O2dAux

/-!
# X2, V13 O2 (b-out-main): `OutBound 𝔭 (outConst 𝔭)` and `outBound_exists`

The outside part of the overlapping projection (MTT2 (d1)-(d4)), the exact statement `OutBound` of `O2Close.lean`.  Two regimes, ONE application
of `outside_conv_bound` (via `conv_simpl`, `κ = K₁ l`) to `Φ = D_out` (`O2bOut.lean`: `dout_eq_zero_of_mem`, `dout_norm_le`):

* `x₀ ∈ Ẽ_σ`: `D_out` is supported in `{|y - x₀| ≥ r}`, `r = |x₀ - z*|`, `z*` the nearest endpoint of `∂Ẽ_σ` (`exists_bdryEtil_between`), and
  `‖T_m D_out(x₀)‖ ≤ (2 K₁ Ab e/(M-N'-1)) ⟨r/2^σ⟩^{-(M-N'-1)}`, `M - N' - 1 ≥ 2` by the margin `hND : N/8 + 3 ≤ D`;
* `x₀ ∉ Ẽ_σ`: `r = 0`, growth relative to `x' ∈ Ẽ_σ` near `z*`, and `χ̃_σ(x₀) ≲ ⟨δ/2^σ⟩^{-(N-2)}` (`layerCut_decay_off`), `N - 2 - N' ≥ 2`;
* in both cases `⟨δ/2^σ⟩^{-2} ≤ (9/4) w_{I₀}(z*) ≤ (9/4) 2^{101} a` (`jb_rpow_le_ow`, `ovFactor_ge_self`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real FourierTransform ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem jb_rpow_le_ow {σ v : ℤ} {z x₀ : ℝ} (hx₀ : x₀ ∈ dyadicInt σ v) :
    jb ((x₀ - z) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) ≤ 9 / 4 * ovWeight 2 σ v z := by
  have hp := zpow_two_pos σ
  rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, jb_rpow_neg_nat, ovWeight_eq]
  set u : ℝ := (z - x₀) / (2 : ℝ) ^ σ with hu
  set a : ℝ := (z - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ with ha
  have hjbu : jb ((x₀ - z) / (2 : ℝ) ^ σ) = jb u := by
    unfold jb; rw [hu, ← neg_sub, neg_div, abs_neg]
  have hau : |a - u| ≤ 1 / 2 := by
    have e : a - u = (x₀ - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ := by rw [ha, hu]; field_simp; ring
    rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    obtain ⟨h1, h2⟩ := hx₀
    rw [abs_le]; constructor <;> nlinarith
  have hja : jb a ≤ 3 / 2 * jb u := jb_le_three_halves_mul hau
  rw [hjbu]
  have h2 : jb a ^ 2 ≤ 9 / 4 * jb u ^ 2 := by
    calc jb a ^ 2 ≤ (3 / 2 * jb u) ^ 2 := pow_le_pow_left₀ (jb_pos _).le hja 2
      _ = _ := by ring
  have hu2 := pow_pos (jb_pos u) 2
  have ha2 := pow_pos (jb_pos a) 2
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hu2 ha2]
  nlinarith

/-- the key of a tile of a layer -/
theorem layer_key_mem {TA : Finset TriTile} {t : Top} (hT : IsTree TA t) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) :
    R₀.pos ∈ eTilKeys TA t.1 σ := by
  obtain ⟨hRT, hs⟩ := mem_layer'_iff.1 hR₀
  have hI : dyadicInt σ R₀.pos ⊆ dyadicInt t.1.1 t.1.2 := by
    have := (hT R₀ hRT).1
    unfold TriTile.I at this
    rwa [hs] at this
  refine mem_eTilKeys.2 ⟨hI, R₀, hRT, ?_⟩
  unfold TriTile.I
  rw [hs]
  exact dyadicInt_subset_dilate (by norm_num) σ R₀.pos

theorem dyCentre_mem_eTil {TA : Finset TriTile} {t : Top} (hT : IsTree TA t) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) :
    dyCentre σ R₀.pos ∈ eTil TA t.1 σ := by
  have hkey := layer_key_mem hT hR₀
  unfold eTil
  simp only [Set.mem_iUnion]
  refine ⟨R₀.pos, hkey, ?_⟩
  have hp := zpow_two_pos σ
  unfold dyCentre
  constructor <;> nlinarith


theorem jb_div_zpow (u : ℝ) (σ : ℤ) : jb (u / (2 : ℝ) ^ σ) = 1 + (2 : ℝ) ^ (-σ) * |u| := by
  unfold jb
  rw [abs_div, abs_of_pos (zpow_two_pos σ), div_eq_mul_inv, zpow_neg, mul_comm]

/-- the constant `K₁ = 2^{D+1} · 6 · C` of the kernel bound `‖𝓕⁻ m w‖ ≤ K₁ l ((1 + l|w|)⁻¹)^D`, `l = 2^{-σ}` -/
def Kc (𝔭 : Params) : ℝ := 2 ^ (𝔭.D + 1) * 6 * 𝔭.C

/-- the denominator `M - N' - 1` of the outside bound -/
def qq (𝔭 : Params) : ℝ := ((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1

/-- `2 K₁ Ab / (M - N' - 1)` -/
def cA (𝔭 : Params) : ℝ := |2 * Kc 𝔭 * Ab 𝔭.tree / qq 𝔭|

def cLC (𝔭 : Params) : ℝ := |cutK 𝔭 * (2 ^ 2 * jbConst 2)|

/-- **The constant of `OutBound`.** -/
def outConst (𝔭 : Params) : ℝ := 9 / 4 * 2 ^ 101 * (cA 𝔭 + cLC 𝔭 * cA 𝔭 * (3 / 2) ^ 𝔭.tree.N)

theorem outConst_nonneg (𝔭 : Params) : 0 ≤ outConst 𝔭 := by
  unfold outConst cA cLC; positivity

/-- **The convolution bound with the constants collected** (`outside_conv_bound`, `κ = K₁ l`):
`‖∫ K(x - y) Φ(y) dy‖ ≤ (2 K₁ A/(q-1)) (1 + l|x - x'|)^N (1 + l r)^{-(q-1)}`. -/
theorem conv_simpl {P : ℕ} [NeZero P] {l K₁ A : ℝ} {N M : ℕ} (hl : 0 < l) (hK₁ : 0 ≤ K₁) (hA : 0 ≤ A) (hM : N + 2 ≤ M)
    {x x' r : ℝ} (hr : 0 ≤ r) {K : ℝ → ℂ} (hKm : Measurable K) (hK : ∀ w, ‖K w‖ ≤ (K₁ * l) * ((1 + l * |w|)⁻¹) ^ M)
    {Φ : ℝ → ZMod P → ℂ} (hΦm : Measurable Φ)
    (hΦ : ∀ y, yNorm 2 (Φ y) ≤ if r ≤ |y - x| then A * (1 + l * |y - x'|) ^ N else 0) :
    yNorm 2 (fun y' => ∫ y, K (x - y) * Φ y y') ≤
      (2 * K₁ * A / (((M - N : ℕ) : ℝ) - 1)) * (1 + l * |x - x'|) ^ N * (1 + l * r) ^ (-(((M - N : ℕ) : ℝ) - 1)) := by
  have hq : (2 : ℝ) ≤ ((M - N : ℕ) : ℝ) := by
    have : 2 ≤ M - N := by omega
    exact_mod_cast this
  have h := outside_conv_bound (P := P) (l := l) (κ := K₁ * l) (A := A) hl (mul_nonneg hK₁ hl.le) hA hM hr hKm hK hΦm hΦ
  refine h.trans (le_of_eq ?_)
  have : ((M - N : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  field_simp


/-- **`OutBound`** (MTT2 (d1)-(d4)): the outside part of the overlapping projection. -/
theorem outBound_main (𝔭 : Params) : OutBound 𝔭 (outConst 𝔭) := by
  intro hND P _ Qs Tr TA t k η χ m s₀ hk h𝔭 h𝔭t hη hη'ex hQ hsub hTr hgood hov hlac hlat F hF hFb σ R₀ hR₀ v S hS1 hS2 e hE he0 x₀ hx₀
  obtain ⟨η', hη'⟩ := hη'ex
  obtain ⟨hR₀T, hσ⟩ := mem_layer'_iff.1 hR₀
  have hJ2 : 2 ≤ 𝔭.J := by have := h𝔭.1; unfold jFloor at this; omega
  have hJ2' : 2 ≤ 𝔭.tree.J := by simpa using hJ2
  have hp := zpow_two_pos σ
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-σ) := zpow_two_pos _
  set l : ℝ := (2 : ℝ) ^ (-σ) with hldef
  have hlσ : l * (2 : ℝ) ^ σ = 1 := by rw [hldef, ← zpow_add₀ (by norm_num)]; simp
  set lo : ℤ := -((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1 with hlo
  set θ : ℝ := t.2 * freqDir k with hθdef
  -- the multiplier
  have hmIn : InMult 𝔭 σ (R₀.box.centre k) (m R₀ k) := by
    have := hlac.mult R₀ hR₀T; rwa [hσ] at this
  have hθ : |θ - R₀.box.centre k| ≤ 13 / 8 * (2 : ℝ) ^ (-σ) := by
    have := abs_theta_sub_centre_le_of_ov (hov R₀ hR₀T); rwa [hσ] at this
  have hβ : 𝔭.β ≤ 11 / 4 := by obtain ⟨-, -, -, -, -, -, h7, -⟩ := h𝔭; exact h7
  have hmcd : ContDiff ℝ ∞ (m R₀ k) := hmIn.1
  have hmcs : HasCompactSupport (m R₀ k) := hasCompactSupport_of_far (c := R₀.box.centre k) hmIn.2.1
  have hKm : Measurable (𝓕⁻ (m R₀ k)) := (kernel_facts hmcd hmcs).1.measurable
  have hK : ∀ w, ‖𝓕⁻ (m R₀ k) w‖ ≤ (Kc 𝔭 * l) * ((1 + l * |w|)⁻¹) ^ 𝔭.D := by
    intro w
    have h := kernel_decay_layer hmIn hβ hθ w
    have e1 : (2 : ℝ) ^ (𝔭.D + 1) * (2 * (3 * (2 : ℝ) ^ (-σ))) * 𝔭.C = Kc 𝔭 * l := by
      unfold Kc; rw [hldef]; ring
    rwa [e1] at h
  have hK1 : 0 ≤ Kc 𝔭 := by
    have hC : 0 ≤ 𝔭.C := by have := h𝔭.2.2.2.2.2.2.2; linarith
    unfold Kc; positivity
  -- σ ∈ L
  have hσL : σ ∈ ovScales 𝔭.J s₀ lo t.1.1 := by
    rw [mem_ovScales]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : (R₀.box.scale.natAbs : ℕ) ≤ TA.sup (fun R => R.box.scale.natAbs) :=
        Finset.le_sup (f := fun R : TriTile => R.box.scale.natAbs) hR₀T
      rw [← hσ]; omega
    · have := (hgood.1 R₀ hR₀T).1
      unfold TriTile.I at this
      rw [hσ] at this
      exact scale_le_of_dyadicInt_subset this
    · have := hlat R₀ hR₀T; rwa [hσ] at this
  have hσL' : σ ∈ ovScales 𝔭.tree.J s₀ lo t.1.1 := by simpa using hσL
  have hlatT : ∀ R ∈ TA, (𝔭.tree.J : ℤ) ∣ R.box.scale - s₀ := by simpa using hlat
  -- Φ and its bounds
  set cL : ℤ → ℝ → ZMod P → ℂ := fun τ x => ovCoef 𝔭.J θ F τ x with hcL
  set cR : ℤ → ℝ → ZMod P → ℂ := fun τ x => -ovCoef 𝔭.J θ F τ x with hcR
  set Φ : ℝ → ZMod P → ℂ := fun z => Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z with hΦdef
  have hΦm : Measurable Φ := measurable_dout (J := 𝔭.J) (s₀ := s₀) (lo := lo) TA t.1 θ cL cR σ hF
  have hΦ0 : ∀ y ∈ eTil TA t.1 σ, yNorm 2 (Φ y) = 0 := by
    intro y hy
    have : Φ y = 0 := dout_eq_zero_of_mem hy
    rw [this, yNorm_zero_ov (by norm_num)]
  have hΦbd : ∀ x' ∈ eTil TA t.1 σ, ∀ y, y ∉ eTil TA t.1 σ →
      yNorm 2 (Φ y) ≤ (Ab 𝔭.tree * e) * (1 + l * |y - x'|) ^ 𝔭.tree.N := by
    intro x' hx' y hy
    have h := dout_norm_le (𝔮 := 𝔭.tree) h𝔭t hJ2' hη' hF hFb hsub hov (s₀ := s₀) (lo := lo) hσL' hlatT hE he0 hx' hy
    rw [jb_div_zpow] at h
    exact h
  have hAb0 : 0 ≤ Ab 𝔭.tree := Ab_nonneg _
  -- the weight `a`
  have hbd : (bdryEnds TA t.1 σ).Nonempty := bdryEnds_nonempty_of_layer hgood.1 hR₀
  have hσS : σ ∈ S := hS2 σ (by simp) hbd
  obtain ⟨zs, hzs, hmin⟩ := Finset.exists_min_image (bdryEnds TA t.1 σ) (fun z => |x₀ - z|) hbd
  have haz : (1 / 2 ^ 101) * ovWeight 2 σ v zs ≤ ((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y :=
    ovFactor_ge_self 𝔭.J hσS hzs
  set a : ℝ := ((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y with ha
  have ha0 : 0 ≤ a := ovFactor_nonneg 𝔭.J S (bdryEnds TA t.1) σ v
  have hwt : (1 + l * |x₀ - zs|) ^ (-(2 : ℝ)) ≤ 9 / 4 * 2 ^ 101 * a := by
    have h1 := jb_rpow_le_ow (σ := σ) (v := v) (z := zs) hx₀
    rw [jb_div_zpow] at h1
    have h2 : ovWeight 2 σ v zs ≤ 2 ^ 101 * a := by
      have := mul_le_mul_of_nonneg_left haz (by positivity : (0 : ℝ) ≤ 2 ^ 101)
      calc ovWeight 2 σ v zs = 2 ^ 101 * ((1 / 2 ^ 101) * ovWeight 2 σ v zs) := by field_simp
        _ ≤ _ := this
    calc _ ≤ 9 / 4 * ovWeight 2 σ v zs := h1
      _ ≤ 9 / 4 * (2 ^ 101 * a) := by gcongr
      _ = _ := by ring
  have hND' : 𝔭.tree.N + 3 ≤ 𝔭.D := by simpa using hND
  have hq3 : (3 : ℝ) ≤ ((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) := by
    have : 3 ≤ 𝔭.D - 𝔭.tree.N := by omega
    exact_mod_cast this
  have hconv := fun (x' r : ℝ) (hr : 0 ≤ r) (hb : ∀ y, yNorm 2 (Φ y) ≤ if r ≤ |y - x₀| then (Ab 𝔭.tree * e) * (1 + l * |y - x'|) ^ 𝔭.tree.N else 0) =>
    conv_simpl (P := P) (l := l) (K₁ := Kc 𝔭) (A := Ab 𝔭.tree * e) (N := 𝔭.tree.N) (M := 𝔭.D) hl hK1 (mul_nonneg hAb0 he0)
      (by omega) hr hKm hK hΦm hb
  have hy0 : 0 ≤ yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y) := yNorm_nonneg' _ _
  have hlc1 : |layerCut η TA σ x₀| ≤ 1 := by
    rw [abs_of_nonneg (layerCut_nonneg hη TA σ x₀)]
    exact layerCut_le_one hη (by have := h𝔭.2.1; unfold classFloor at this; omega) hgood.2.1 σ x₀
  have hcA : 0 ≤ cA 𝔭 := abs_nonneg _
  have hcoef : 2 * Kc 𝔭 * (Ab 𝔭.tree * e) / qq 𝔭 ≤ cA 𝔭 * e := by
    have : 2 * Kc 𝔭 * (Ab 𝔭.tree * e) / qq 𝔭 = (2 * Kc 𝔭 * Ab 𝔭.tree / qq 𝔭) * e := by ring
    rw [this]; unfold cA
    exact mul_le_mul_of_nonneg_right (le_abs_self _) he0
  show |layerCut η TA σ x₀| * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y) ≤ outConst 𝔭 * e * a
  by_cases hxE : x₀ ∈ eTil TA t.1 σ
  · -- Case A: `x₀ ∈ Ẽ_σ`
    set r : ℝ := |x₀ - zs| with hr
    have hr0 : 0 ≤ r := abs_nonneg _
    have hb : ∀ y, yNorm 2 (Φ y) ≤ if r ≤ |y - x₀| then (Ab 𝔭.tree * e) * (1 + l * |y - x₀|) ^ 𝔭.tree.N else 0 := by
      intro y
      by_cases hy : y ∈ eTil TA t.1 σ
      · rw [hΦ0 y hy]
        split_ifs
        · exact mul_nonneg (mul_nonneg hAb0 he0) (pow_nonneg (by positivity) _)
        · exact le_rfl
      · have hry : r ≤ |y - x₀| := by
          obtain ⟨z, hz, hz1, hz2⟩ := exists_bdryEtil_between hxE hy
          exact (hmin z hz).trans hz1
        rw [ite_eq_left hry]
        exact hΦbd x₀ hxE y hy
    have h := hconv x₀ r hr0 hb
    rw [sub_self, abs_zero, mul_zero, add_zero, one_pow, mul_one] at h
    have hq' : (2 : ℝ) ≤ ((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1 := by linarith only [hq3]
    have hpow : (1 + l * r) ^ (-(((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1)) ≤ (1 + l * r) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by have := mul_nonneg hl.le hr0; linarith only [this]) (by linarith only [hq'])
    have hcoef0 : 0 ≤ 2 * Kc 𝔭 * (Ab 𝔭.tree * e) / (((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1) :=
      div_nonneg (by have := mul_nonneg hAb0 he0; positivity) (by linarith only [hq3])
    have hY : yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y) ≤
        (cA 𝔭 * e) * (9 / 4 * 2 ^ 101 * a) := by
      calc _ ≤ (2 * Kc 𝔭 * (Ab 𝔭.tree * e) / (((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1)) * (1 + l * r) ^ (-(((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1)) := h
        _ ≤ (2 * Kc 𝔭 * (Ab 𝔭.tree * e) / (((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1)) * (9 / 4 * 2 ^ 101 * a) :=
            mul_le_mul_of_nonneg_left (hpow.trans hwt) hcoef0
        _ ≤ (cA 𝔭 * e) * (9 / 4 * 2 ^ 101 * a) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact hcoef
    have hextra : 0 ≤ 9 / 4 * 2 ^ 101 * (cLC 𝔭 * cA 𝔭 * (3 / 2) ^ 𝔭.tree.N) * e * a := by
      unfold cLC cA; positivity
    calc |layerCut η TA σ x₀| * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y)
        ≤ 1 * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y) := mul_le_mul_of_nonneg_right hlc1 hy0
      _ ≤ (cA 𝔭 * e) * (9 / 4 * 2 ^ 101 * a) := by rw [one_mul]; exact hY
      _ ≤ outConst 𝔭 * e * a := by
          unfold outConst
          linarith only [hextra]
  · -- Case B: `x₀ ∉ Ẽ_σ`
    set δ : ℝ := |x₀ - zs| with hδ
    have hδ0 : 0 ≤ δ := abs_nonneg _
    obtain ⟨x', hx'E, hx'z⟩ := exists_Etil_near_endpoint hzs
    have hN400 : 400 ≤ 𝔭.N := by have := h𝔭.2.1; unfold classFloor at this; omega
    have hlcd : layerCut η TA σ x₀ ≤ cutK 𝔭 * (2 ^ 2 * jbConst 2) * (1 + δ / 2 ^ σ) ^ (-((𝔭.N : ℝ) - 2)) := by
      refine layerCut_decay_off hη (by omega) hgood.2.1 σ hδ0 ?_
      intro R hR
      have hcE := dyCentre_mem_eTil hgood.1 hR
      obtain ⟨z, hz, hz1, hz2⟩ := exists_bdryEtil_between hcE hxE
      exact (hmin z hz).trans hz2
    have hb : ∀ y, yNorm 2 (Φ y) ≤ if (0 : ℝ) ≤ |y - x₀| then (Ab 𝔭.tree * e) * (1 + l * |y - x'|) ^ 𝔭.tree.N else 0 := by
      intro y
      by_cases hy : y ∈ eTil TA t.1 σ
      · rw [hΦ0 y hy, ite_eq_left (abs_nonneg _)]
        exact mul_nonneg (mul_nonneg hAb0 he0) (pow_nonneg (by positivity) _)
      · rw [ite_eq_left (abs_nonneg _)]
        exact hΦbd x' hx'E y hy
    have h := hconv x' 0 le_rfl hb
    rw [mul_zero, add_zero, Real.one_rpow, mul_one] at h
    -- the distance to `x'`
    have hlx : l * |x₀ - x'| ≤ l * δ + 1 / 2 := by
      have h1 : |x₀ - x'| ≤ δ + (2 : ℝ) ^ σ / 2 := by
        calc |x₀ - x'| = |(x₀ - zs) + (zs - x')| := by ring_nf
          _ ≤ |x₀ - zs| + |zs - x'| := abs_add_le _ _
          _ ≤ δ + (2 : ℝ) ^ σ / 2 := by rw [abs_sub_comm zs x']; exact add_le_add le_rfl hx'z
      calc l * |x₀ - x'| ≤ l * (δ + (2 : ℝ) ^ σ / 2) := mul_le_mul_of_nonneg_left h1 hl.le
        _ = l * δ + 1 / 2 := by rw [mul_add, mul_div_assoc', show l * (2 : ℝ) ^ σ = 1 from hlσ]
    have hbase : 1 + l * |x₀ - x'| ≤ 3 / 2 * (1 + l * δ) := by
      have := mul_nonneg hl.le hδ0
      linarith only [hlx, this]
    have hpowx : (1 + l * |x₀ - x'|) ^ 𝔭.tree.N ≤ (3 / 2) ^ 𝔭.tree.N * (1 + l * δ) ^ 𝔭.tree.N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by have := mul_nonneg hl.le (abs_nonneg (x₀ - x')); linarith only [this]) hbase _
    have hcoef0 : 0 ≤ 2 * Kc 𝔭 * (Ab 𝔭.tree * e) / (((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1) :=
      div_nonneg (by have := mul_nonneg hAb0 he0; positivity) (by linarith only [hq3])
    have hY : yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y) ≤
        (2 * Kc 𝔭 * (Ab 𝔭.tree * e) / (((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1)) * ((3 / 2) ^ 𝔭.tree.N * (1 + l * δ) ^ 𝔭.tree.N) :=
      h.trans (mul_le_mul_of_nonneg_left hpowx hcoef0)
    -- the product with the decay of the cutoff
    have e1 : δ / 2 ^ σ = l * δ := by rw [hldef, zpow_neg, div_eq_inv_mul]
    rw [e1] at hlcd
    have hbl : 1 ≤ 1 + l * δ := by have := mul_nonneg hl.le hδ0; linarith only [this]
    have hexp : (1 + l * δ) ^ (-((𝔭.N : ℝ) - 2)) * (1 + l * δ) ^ 𝔭.tree.N ≤ (1 + l * δ) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith only [hbl])]
      refine Real.rpow_le_rpow_of_exponent_le hbl ?_
      have : 𝔭.tree.N + 4 ≤ 𝔭.N := by simp only [Params.tree_N]; omega
      have h' : ((𝔭.tree.N : ℕ) : ℝ) + 4 ≤ (𝔭.N : ℝ) := by exact_mod_cast this
      linarith only [h']
    have hlc0 : 0 ≤ layerCut η TA σ x₀ := layerCut_nonneg hη TA σ x₀
    have hpos1 : 0 ≤ (1 + l * δ) ^ (-((𝔭.N : ℝ) - 2)) := Real.rpow_nonneg (by linarith only [hbl]) _
    have hpos2 : 0 ≤ (1 + l * δ) ^ 𝔭.tree.N := pow_nonneg (by linarith only [hbl]) _
    have hwt' : (1 + l * δ) ^ (-(2 : ℝ)) ≤ 9 / 4 * 2 ^ 101 * a := hwt
    set c0 : ℝ := cutK 𝔭 * (2 ^ 2 * jbConst 2) with hc0
    set cf : ℝ := 2 * Kc 𝔭 * (Ab 𝔭.tree * e) / (((𝔭.D - 𝔭.tree.N : ℕ) : ℝ) - 1) with hcf
    have hcfle : cf ≤ cA 𝔭 * e := hcoef
    have hcfp : 0 ≤ cf := hcoef0
    have hc0le : c0 ≤ cLC 𝔭 := le_abs_self _
    have hcLC0 : 0 ≤ cLC 𝔭 := abs_nonneg _
    have h3N : 0 ≤ (3 / 2 : ℝ) ^ 𝔭.tree.N := by positivity
    have hextra : 0 ≤ 9 / 4 * 2 ^ 101 * cA 𝔭 * e * a := by unfold cA; positivity
    have hCpos : 0 < 𝔭.C := by have := h𝔭.2.2.2.2.2.2.2; linarith only [this]
    have hc0nn : 0 ≤ c0 := by
      rw [hc0]; have := jbConst_nonneg 2; have := cutK_pos hCpos; positivity
    rw [abs_of_nonneg hlc0]
    calc layerCut η TA σ x₀ * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Φ z y)
        ≤ (c0 * (1 + l * δ) ^ (-((𝔭.N : ℝ) - 2))) * (cf * ((3 / 2) ^ 𝔭.tree.N * (1 + l * δ) ^ 𝔭.tree.N)) :=
          mul_le_mul hlcd hY hy0 (mul_nonneg hc0nn hpos1)
      _ = (c0 * cf * (3 / 2) ^ 𝔭.tree.N) * ((1 + l * δ) ^ (-((𝔭.N : ℝ) - 2)) * (1 + l * δ) ^ 𝔭.tree.N) := by ring
      _ ≤ (cLC 𝔭 * (cA 𝔭 * e) * (3 / 2) ^ 𝔭.tree.N) * (9 / 4 * 2 ^ 101 * a) := by
          refine mul_le_mul ?_ (hexp.trans hwt') (mul_nonneg hpos1 hpos2) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul hc0le hcfle hcfp hcLC0) h3N
      _ ≤ outConst 𝔭 * e * a := by
          unfold outConst
          have : 9 / 4 * 2 ^ 101 * (cA 𝔭 + cLC 𝔭 * cA 𝔭 * (3 / 2) ^ 𝔭.tree.N) * e * a -
              (cLC 𝔭 * (cA 𝔭 * e) * (3 / 2) ^ 𝔭.tree.N) * (9 / 4 * 2 ^ 101 * a) = 9 / 4 * 2 ^ 101 * cA 𝔭 * e * a := by ring
          linarith only [this, hextra]

end PrimeBHT.TimeFrequency.X2
