module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeLayers

/-!
# X2, V15 (assembly), step 2: the boundary layer of the cutoff `χ̃_σ` (MTT2 Lemma 7.3, `χ̃ → χ̃³`)

For a good tree `Tr` (one box per scale), `E_σ = layerSet Tr σ`, `χ̃_σ = layerCut η Tr σ = 1_{E_σ} * η_σ`:

* `exists_bdry_between`: if exactly one of `x, y` lies in `E_σ`, a boundary point of `E_σ` lies between them
  (the Heaviside identity of `Psp/Geometry.lean`);
* `layerCut_eq_integral`: `χ̃_σ(x) = ∫_{E_σ} 2^{-σ} η((x - y)/2^σ) dy`, so `0 ≤ χ̃_σ ≤ 1`;
* `boundary_layer_le`: `χ̃_σ(x)^{1/2} (1 - χ̃_σ(x)) ≤ C Σ_{z ∈ ∂E_σ} ⟨(x - z)/2^σ⟩^{-κ}`;
* `lintegral_boundary_layer_le`: `∫ ... ≤ C #∂E_σ 2^σ`, hence (G-1) `Σ_σ ∫ ... ≤ C |I_t|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## A boundary point between a point of `E_σ` and a point outside -/

theorem exists_bdry_between {Tr : Finset TriTile} {σ : ℤ} {x y : ℝ}
    (h : (x ∈ layerSet Tr σ) ≠ (y ∈ layerSet Tr σ)) :
    ∃ z ∈ bdryEndsE Tr σ, (x < z ∧ z ≤ y) ∨ (y < z ∧ z ≤ x) := by
  by_contra hne
  push Not at hne
  have heq : ∀ z ∈ bdryEndsE Tr σ, heav (x - z) = heav (y - z) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hne z hz
    unfold heav
    by_cases hzx : z ≤ x
    · by_cases hzy : z ≤ y
      · rw [ite_eq_left (by linarith), ite_eq_left (by linarith)]
      · exfalso; exact absurd hzx (not_le.2 (h2 (not_le.1 hzy)))
    · by_cases hzy : z ≤ y
      · exfalso; exact absurd hzy (not_le.2 (h1 (not_le.1 hzx)))
      · rw [ite_eq_right (by linarith), ite_eq_right (by linarith)]
  have e1 := indicator_layerSet_eq_heaviside Tr σ x
  have e2 := indicator_layerSet_eq_heaviside Tr σ y
  have hs1 : ∑ z ∈ leftEndsE Tr σ, heav (x - z) = ∑ z ∈ leftEndsE Tr σ, heav (y - z) :=
    Finset.sum_congr rfl fun z hz => heq z (Finset.mem_union_left _ hz)
  have hs2 : ∑ z ∈ rightEndsE Tr σ, heav (x - z) = ∑ z ∈ rightEndsE Tr σ, heav (y - z) :=
    Finset.sum_congr rfl fun z hz => heq z (Finset.mem_union_right _ hz)
  have : (if x ∈ layerSet Tr σ then (1 : ℝ) else 0) = (if y ∈ layerSet Tr σ then (1 : ℝ) else 0) := by
    rw [e1, e2, hs1, hs2]
  apply h
  by_cases hx : x ∈ layerSet Tr σ <;> by_cases hy : y ∈ layerSet Tr σ <;> simp [hx, hy] at this ⊢

/-- If there is no boundary point then `E_σ` is empty. -/
theorem layerSet_eq_empty_of_bdry_empty {Tr : Finset TriTile} {σ : ℤ} (h : bdryEndsE Tr σ = ∅) :
    layerSet Tr σ = ∅ := by
  have hl : leftEndsE Tr σ = ∅ := Finset.eq_empty_of_forall_notMem fun z hz =>
    by have : z ∈ bdryEndsE Tr σ := Finset.mem_union_left _ hz
       rw [h] at this; exact absurd this (Finset.notMem_empty _)
  have hr : rightEndsE Tr σ = ∅ := Finset.eq_empty_of_forall_notMem fun z hz =>
    by have : z ∈ bdryEndsE Tr σ := Finset.mem_union_right _ hz
       rw [h] at this; exact absurd this (Finset.notMem_empty _)
  ext y
  have := indicator_layerSet_eq_heaviside Tr σ y
  rw [hl, hr] at this
  simp only [Finset.sum_empty, sub_zero] at this
  by_contra hy
  have hy' : y ∈ layerSet Tr σ := by
    by_contra hh; exact hy (by simp [hh])
  simp [hy'] at this

/-! ## `χ̃_σ = 1_{E_σ} * η_σ` -/

section Cutoff

variable {𝔭 : Params} {η : ℝ → ℝ}

theorem integral_eta_scaled_eq (hη : IsEtaCut 𝔭 η) (σ : ℤ) (x : ℝ) :
    ∫ y, (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ) = 1 := by
  have hp := zpow_two_pos σ
  rw [integral_sub_left_eq_self (fun w => (2 : ℝ) ^ (-σ) * η (w / (2 : ℝ) ^ σ)) volume x]
  rw [integral_const_mul, Measure.integral_comp_div (fun w => η w) ((2 : ℝ) ^ σ), hη.2.2.1, smul_eq_mul,
    abs_of_pos hp, mul_one, ← zpow_add₀ (by norm_num)]
  simp

theorem integrable_eta_shift (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) (σ : ℤ) (x : ℝ) :
    Integrable (fun y : ℝ => (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ)) := by
  have := (integrable_eta_scaled hη hN σ).comp_sub_left x
  exact this

theorem layerSet_eq_biUnion (Tr : Finset TriTile) (σ : ℤ) :
    layerSet Tr σ = ⋃ v ∈ layerKeys Tr σ, dyadicInt σ v := by
  unfold layerSet
  ext y
  simp only [Set.mem_iUnion, mem_layerKeys_iff, mem_layer'_iff]
  constructor
  · rintro ⟨R, ⟨hR, hs⟩, hy⟩
    exact ⟨R.pos, ⟨R, hR, hs, rfl⟩, by unfold TriTile.I at hy; rw [hs] at hy; exact hy⟩
  · rintro ⟨v, ⟨R, hR, hs, hp⟩, hy⟩
    exact ⟨R, ⟨hR, hs⟩, by unfold TriTile.I; rw [hs, hp]; exact hy⟩

theorem measurableSet_layerSet (Tr : Finset TriTile) (σ : ℤ) : MeasurableSet (layerSet Tr σ) := by
  rw [layerSet_eq_biUnion]
  exact Finset.measurableSet_biUnion _ fun v _ => measurableSet_dyadicInt σ v

/-- **`χ̃_σ = 1_{E_σ} * η_σ`** (one box per scale: the tile intervals of a layer are disjoint). -/
theorem layerCut_eq_integral (hη : IsEtaCut 𝔭 η) {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) (x : ℝ) :
    layerCut η Tr σ x = ∫ y in layerSet Tr σ, (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ) := by
  unfold layerCut
  rw [sum_layer'_eq_sum_keys hb σ (fun v => tileCutoff η σ v x), layerSet_eq_biUnion,
    integral_biUnion_finset _ (fun v _ => measurableSet_dyadicInt σ v)]
  · rfl
  · intro v _ v' _ hne
    rcases dyadicInt_nested_or_disjoint σ v σ v' with h | h | h
    · exact absurd (index_eq_of_dyadicInt_subset rfl h) hne
    · exact absurd (index_eq_of_dyadicInt_subset rfl h).symm hne
    · exact h
  · intro v _
    exact integrableOn_cutoff_integrand hη σ v x

theorem layerCut_le_one (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) (x : ℝ) :
    layerCut η Tr σ x ≤ 1 := by
  rw [layerCut_eq_integral hη hb, ← integral_eta_scaled_eq hη σ x]
  exact setIntegral_le_integral (integrable_eta_shift hη hN σ x)
    (Filter.Eventually.of_forall fun y => mul_nonneg (zpow_two_pos _).le (hη.2.1 _))

theorem one_sub_layerCut_eq (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) (x : ℝ) :
    1 - layerCut η Tr σ x = ∫ y in (layerSet Tr σ)ᶜ, (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ) := by
  have h := integral_add_compl (measurableSet_layerSet Tr σ) (integrable_eta_shift hη hN σ x) (μ := volume)
  rw [integral_eta_scaled_eq hη σ x, ← layerCut_eq_integral hη hb] at h
  linarith

theorem IsEtaCut.C_nonneg (hη : IsEtaCut 𝔭 η) : 0 ≤ 𝔭.C := by
  by_contra hC
  push Not at hC
  have h0 := hη.2.2.2.1 0
  have h00 := hη.2.1 0
  have : 𝔭.C * jb 0 ^ (-(𝔭.N : ℝ)) < 0 := mul_neg_of_neg_of_pos hC (Real.rpow_pos_of_pos (jb_pos 0) _)
  linarith

/-- **Tail of `η_σ`**: `∫_S η_σ(x - y) dy ≤ 2 C ⟨D/2^σ⟩^{-(N-2)}` on `S ⊆ {|x - y| ≥ D}`. -/
theorem eta_tail_le (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) (σ : ℤ) (x : ℝ) {D : ℝ} (hD : 0 ≤ D) {S : Set ℝ}
    (hS : MeasurableSet S) (hSD : ∀ y ∈ S, D ≤ |x - y|) :
    ∫ y in S, (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ) ≤
      2 * 𝔭.C * jb (D / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) - 2)) := by
  have hp := zpow_two_pos σ
  have hp' := zpow_two_pos (-σ)
  have hC := hη.C_nonneg
  set r : ℝ := jb (D / (2 : ℝ) ^ σ) with hr
  have hr0 : 0 < r := jb_pos _
  set g : ℝ → ℝ := fun y => (2 : ℝ) ^ (-σ) * 𝔭.C * r ^ (-((𝔭.N : ℝ) - 2)) * jb ((y - x) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) with hg
  have hgint : Integrable g := by
    have := (integrable_jb_rpow (c := x) hp (r := 2) (by norm_num)).const_mul
      ((2 : ℝ) ^ (-σ) * 𝔭.C * r ^ (-((𝔭.N : ℝ) - 2)))
    exact this
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    simp only [hg]
    have := Real.rpow_pos_of_pos hr0 (-((𝔭.N : ℝ) - 2))
    have := Real.rpow_pos_of_pos (jb_pos ((y - x) / (2 : ℝ) ^ σ)) (-(2 : ℝ))
    positivity
  have hf : ∀ y ∈ S, (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ) ≤ g y := by
    intro y hy
    set t : ℝ := (x - y) / (2 : ℝ) ^ σ with ht
    have hjt : r ≤ jb t := by
      rw [hr]; unfold jb
      have : |D / (2 : ℝ) ^ σ| ≤ |t| := by
        rw [abs_of_nonneg (div_nonneg hD hp.le), ht, abs_div, abs_of_pos hp]
        exact div_le_div_of_nonneg_right (hSD y hy) hp.le
      linarith
    have hjt' : jb ((y - x) / (2 : ℝ) ^ σ) = jb t := by
      unfold jb
      rw [ht, ← abs_neg]
      congr 2; ring
    have h2 : η t ≤ 𝔭.C * jb t ^ (-(𝔭.N : ℝ)) := hη.2.2.2.1 t
    have hN2 : (2 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
    have h3 : jb t ^ (-(𝔭.N : ℝ)) ≤ r ^ (-((𝔭.N : ℝ) - 2)) * jb t ^ (-(2 : ℝ)) := by
      have e : jb t ^ (-(𝔭.N : ℝ)) = jb t ^ (-((𝔭.N : ℝ) - 2)) * jb t ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add (jb_pos t)]; congr 1; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hr0 hjt (by linarith))
        (Real.rpow_pos_of_pos (jb_pos t) _).le
    simp only [hg]
    rw [hjt']
    calc (2 : ℝ) ^ (-σ) * η t ≤ (2 : ℝ) ^ (-σ) * (𝔭.C * (r ^ (-((𝔭.N : ℝ) - 2)) * jb t ^ (-(2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hC)) hp'.le
      _ = _ := by ring
  have h1 : ∫ y in S, (2 : ℝ) ^ (-σ) * η ((x - y) / (2 : ℝ) ^ σ) ≤ ∫ y in S, g y :=
    setIntegral_mono_on (integrable_eta_shift hη hN σ x).integrableOn hgint.integrableOn hS hf
  have h2 : ∫ y in S, g y ≤ ∫ y, g y := setIntegral_le_integral hgint (Filter.Eventually.of_forall hg0)
  have h3 : ∫ y, g y = 2 * 𝔭.C * r ^ (-((𝔭.N : ℝ) - 2)) := by
    simp only [hg]
    rw [integral_const_mul]
    have := integral_one_add_abs_sub_div_rpow (p := 2) (by norm_num) x (L := (2 : ℝ) ^ σ) hp
    have e : ∀ y : ℝ, jb ((y - x) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) = (1 + |y - x| / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) := by
      intro y; unfold jb; rw [abs_div, abs_of_pos hp]
    simp_rw [e]
    rw [this]
    have : (2 : ℝ) ^ (-σ) * (2 * (2 : ℝ) ^ σ) = 2 := by
      rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← zpow_add₀ (by norm_num)]; simp
    calc (2 : ℝ) ^ (-σ) * 𝔭.C * r ^ (-((𝔭.N : ℝ) - 2)) * (2 * (2 : ℝ) ^ σ / (2 - 1))
        = ((2 : ℝ) ^ (-σ) * (2 * (2 : ℝ) ^ σ)) * 𝔭.C * r ^ (-((𝔭.N : ℝ) - 2)) := by ring
      _ = _ := by rw [this]
  linarith

/-- The boundary-layer function `β_σ(x) = χ̃_σ(x)^{1/2} (1 - χ̃_σ(x))`. -/
def bLayer (η : ℝ → ℝ) (Tr : Finset TriTile) (σ : ℤ) (x : ℝ) : ℝ :=
  layerCut η Tr σ x ^ (1 / 2 : ℝ) * (1 - layerCut η Tr σ x)

/-- **The boundary layer decays away from `∂E_σ`**: `β_σ(x) ≤ (A + A^{1/2}) Σ_{z ∈ ∂E_σ} ⟨(x - z)/2^σ⟩^{-(N-2)/2}`, `A = 2C`. -/
theorem bLayer_le (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) (x : ℝ) :
    bLayer η Tr σ x ≤ (2 * 𝔭.C + (2 * 𝔭.C) ^ (1 / 2 : ℝ)) *
      ∑ z ∈ bdryEndsE Tr σ, jb ((x - z) / (2 : ℝ) ^ σ) ^ (-(((𝔭.N : ℝ) - 2) / 2)) := by
  have hp := zpow_two_pos σ
  have hC := hη.C_nonneg
  have hN2 : (2 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
  set c : ℝ := layerCut η Tr σ x with hc
  have hc0 : 0 ≤ c := by
    rw [hc, layerCut_eq_integral hη hb]
    exact setIntegral_nonneg (measurableSet_layerSet Tr σ) fun y _ =>
      mul_nonneg (zpow_two_pos _).le (hη.2.1 _)
  have hc1 : c ≤ 1 := layerCut_le_one hη hN hb σ x
  by_cases hbd : bdryEndsE Tr σ = ∅
  · have hE := layerSet_eq_empty_of_bdry_empty hbd
    have : c = 0 := by rw [hc, layerCut_eq_integral hη hb, hE]; simp
    rw [hbd]
    simp [bLayer, ← hc, this]
  · obtain ⟨z₀, hz₀, hmin⟩ := Finset.exists_min_image (bdryEndsE Tr σ) (fun z => |x - z|)
      (Finset.nonempty_iff_ne_empty.2 hbd)
    set d : ℝ := |x - z₀| with hd
    have hd0 : 0 ≤ d := abs_nonneg _
    set r : ℝ := jb (d / (2 : ℝ) ^ σ) with hr
    have hr1 : 1 ≤ r := one_le_jb _
    set A : ℝ := 2 * 𝔭.C with hA
    have hA0 : 0 ≤ A := by positivity
    -- the tail bound
    have hsep : ∀ y, (x ∈ layerSet Tr σ) ≠ (y ∈ layerSet Tr σ) → d ≤ |x - y| := by
      intro y hxy
      obtain ⟨z, hz, hzb⟩ := exists_bdry_between hxy
      have h1 : d ≤ |x - z| := hmin z hz
      refine h1.trans ?_
      rcases hzb with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    have hT : ∀ w : ℝ, w ≤ A * r ^ (-((𝔭.N : ℝ) - 2)) → w ≤ A * r ^ (-((𝔭.N : ℝ) - 2)) := fun w h => h
    have hκ : r ^ (-((𝔭.N : ℝ) - 2)) ≤ r ^ (-(((𝔭.N : ℝ) - 2) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
    have hκ' : (A * r ^ (-((𝔭.N : ℝ) - 2))) ^ (1 / 2 : ℝ) ≤ A ^ (1 / 2 : ℝ) * r ^ (-(((𝔭.N : ℝ) - 2) / 2)) := by
      rw [Real.mul_rpow hA0 (Real.rpow_pos_of_pos (by linarith) _).le, ← Real.rpow_mul (by linarith)]
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Real.rpow_nonneg hA0 _)
      congr 1; ring
    have hmain : bLayer η Tr σ x ≤ (A + A ^ (1 / 2 : ℝ)) * r ^ (-(((𝔭.N : ℝ) - 2) / 2)) := by
      have hrk := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < r) (-(((𝔭.N : ℝ) - 2) / 2))
      have hAh : 0 ≤ A ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA0 _
      by_cases hx : x ∈ layerSet Tr σ
      · have h1 : 1 - c ≤ A * r ^ (-((𝔭.N : ℝ) - 2)) := by
          rw [hc, one_sub_layerCut_eq hη hN hb]
          refine eta_tail_le hη hN σ x hd0 (measurableSet_layerSet Tr σ).compl fun y hy => ?_
          exact hsep y (fun h => hy (by rw [← h]; exact hx))
        have hc12 : c ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hc0 hc1 (by norm_num)
        calc bLayer η Tr σ x = c ^ (1 / 2 : ℝ) * (1 - c) := rfl
          _ ≤ 1 * (A * r ^ (-(((𝔭.N : ℝ) - 2) / 2))) := by
              refine mul_le_mul hc12 (h1.trans (mul_le_mul_of_nonneg_left hκ hA0)) (by linarith) (by norm_num)
          _ ≤ _ := by nlinarith [mul_nonneg hAh hrk.le]
      · have h1 : c ≤ A * r ^ (-((𝔭.N : ℝ) - 2)) := by
          rw [hc, layerCut_eq_integral hη hb]
          refine eta_tail_le hη hN σ x hd0 (measurableSet_layerSet Tr σ) fun y hy => ?_
          exact hsep y (fun h => hx (by rw [h]; exact hy))
        have hc12 : c ^ (1 / 2 : ℝ) ≤ (A * r ^ (-((𝔭.N : ℝ) - 2))) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hc0 h1 (by norm_num)
        calc bLayer η Tr σ x = c ^ (1 / 2 : ℝ) * (1 - c) := rfl
          _ ≤ c ^ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hc0 _)
          _ ≤ A ^ (1 / 2 : ℝ) * r ^ (-(((𝔭.N : ℝ) - 2) / 2)) := by rw [mul_one]; exact hc12.trans hκ'
          _ ≤ _ := by nlinarith [mul_nonneg hA0 hrk.le]
    have hsum : r ^ (-(((𝔭.N : ℝ) - 2) / 2)) ≤
        ∑ z ∈ bdryEndsE Tr σ, jb ((x - z) / (2 : ℝ) ^ σ) ^ (-(((𝔭.N : ℝ) - 2) / 2)) := by
      have : jb ((x - z₀) / (2 : ℝ) ^ σ) = r := by
        rw [hr]; unfold jb; simp only [abs_div, abs_of_pos hp, hd, abs_abs]
      rw [← this]
      exact Finset.single_le_sum (f := fun z => jb ((x - z) / (2 : ℝ) ^ σ) ^ (-(((𝔭.N : ℝ) - 2) / 2)))
        (fun z _ => (Real.rpow_pos_of_pos (jb_pos _) _).le) hz₀
    calc bLayer η Tr σ x ≤ (A + A ^ (1 / 2 : ℝ)) * r ^ (-(((𝔭.N : ℝ) - 2) / 2)) := hmain
      _ ≤ (A + A ^ (1 / 2 : ℝ)) * ∑ z ∈ bdryEndsE Tr σ, jb ((x - z) / (2 : ℝ) ^ σ) ^ (-(((𝔭.N : ℝ) - 2) / 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)

theorem bLayer_nonneg (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) (x : ℝ) :
    0 ≤ bLayer η Tr σ x := by
  have hc0 : 0 ≤ layerCut η Tr σ x := by
    rw [layerCut_eq_integral hη hb]
    exact setIntegral_nonneg (measurableSet_layerSet Tr σ) fun y _ =>
      mul_nonneg (zpow_two_pos _).le (hη.2.1 _)
  have := layerCut_le_one hη hN hb σ x
  unfold bLayer
  exact mul_nonneg (Real.rpow_nonneg hc0 _) (by linarith)

/-- The constant of the boundary-layer integral. -/
def bLayerConst (𝔭 : Params) : ℝ :=
  (2 * 𝔭.C + (2 * 𝔭.C) ^ (1 / 2 : ℝ)) * (2 / ((((𝔭.N : ℝ) - 2) / 2) - 1))

/-- **`∫ β_σ ≤ C 2^σ #∂E_σ`**. -/
theorem lintegral_bLayer_le (hη : IsEtaCut 𝔭 η) (hN : 5 ≤ 𝔭.N) {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) :
    ∫⁻ x, ENNReal.ofReal (bLayer η Tr σ x) ≤
      ENNReal.ofReal (bLayerConst 𝔭 * ((2 : ℝ) ^ σ * ((bdryEndsE Tr σ).card : ℝ))) := by
  have hp := zpow_two_pos σ
  have hC := hη.C_nonneg
  have hN5 : (5 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
  set κ : ℝ := (((𝔭.N : ℝ) - 2) / 2) with hκ
  have hκ1 : 1 < κ := by rw [hκ]; linarith
  set C₄ : ℝ := 2 * 𝔭.C + (2 * 𝔭.C) ^ (1 / 2 : ℝ) with hC₄
  have hC₄0 : 0 ≤ C₄ := by positivity
  set g : ℝ → ℝ := fun x => C₄ * ∑ z ∈ bdryEndsE Tr σ, jb ((x - z) / (2 : ℝ) ^ σ) ^ (-κ) with hg
  have hgint : Integrable g := by
    refine Integrable.const_mul (integrable_finset_sum _ fun z _ => ?_) C₄
    exact integrable_jb_rpow (c := z) hp hκ1
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    simp only [hg]
    exact mul_nonneg hC₄0 (Finset.sum_nonneg fun z _ => (Real.rpow_pos_of_pos (jb_pos _) _).le)
  have hle : ∀ x, ENNReal.ofReal (bLayer η Tr σ x) ≤ ENNReal.ofReal (g x) := fun x =>
    ENNReal.ofReal_le_ofReal (bLayer_le hη (by omega) hb σ x)
  calc ∫⁻ x, ENNReal.ofReal (bLayer η Tr σ x) ≤ ∫⁻ x, ENNReal.ofReal (g x) := lintegral_mono hle
    _ = ENNReal.ofReal (∫ x, g x) := (ofReal_integral_eq_lintegral_ofReal hgint
          (Filter.Eventually.of_forall hg0)).symm
    _ = _ := by
        congr 1
        simp only [hg]
        rw [integral_const_mul, integral_finset_sum _ fun z _ => integrable_jb_rpow (c := z) hp hκ1]
        have hz : ∀ z : ℝ, ∫ x, jb ((x - z) / (2 : ℝ) ^ σ) ^ (-κ) = 2 * (2 : ℝ) ^ σ / (κ - 1) := by
          intro z
          have := integral_one_add_abs_sub_div_rpow (p := κ) hκ1 z (L := (2 : ℝ) ^ σ) hp
          have e : ∀ x : ℝ, jb ((x - z) / (2 : ℝ) ^ σ) ^ (-κ) = (1 + |x - z| / (2 : ℝ) ^ σ) ^ (-κ) := by
            intro x; unfold jb; rw [abs_div, abs_of_pos hp]
          simp_rw [e]
          exact this
        simp_rw [hz]
        rw [Finset.sum_const, nsmul_eq_mul]
        unfold bLayerConst
        rw [← hκ, ← hC₄]
        have hk0 : κ - 1 ≠ 0 := by linarith
        field_simp

theorem bLayerConst_nonneg (hη : IsEtaCut 𝔭 η) (hN : 5 ≤ 𝔭.N) : 0 ≤ bLayerConst 𝔭 := by
  have hC := hη.C_nonneg
  have hN5 : (5 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
  unfold bLayerConst
  have : 0 < (((𝔭.N : ℝ) - 2) / 2) - 1 := by linarith
  positivity

/-- **(G-1) for the boundary layers**: `Σ_σ ∫ β_σ ≤ 12 C |I_t|` for a good tree. -/
theorem sum_lintegral_bLayer_le (hη : IsEtaCut 𝔭 η) (hN : 5 ≤ 𝔭.N) {Tr : Finset TriTile} {t : Top}
    (hg : IsGoodTree Tr t) :
    ∑ σ ∈ treeScales Tr, ∫⁻ x, ENNReal.ofReal (bLayer η Tr σ x) ≤
      ENNReal.ofReal (12 * bLayerConst 𝔭 * (2 : ℝ) ^ t.1.1) := by
  have hb := hg.2.1
  have hc := bLayerConst_nonneg hη hN
  calc ∑ σ ∈ treeScales Tr, ∫⁻ x, ENNReal.ofReal (bLayer η Tr σ x)
      ≤ ∑ σ ∈ treeScales Tr, ENNReal.ofReal (bLayerConst 𝔭 * ((2 : ℝ) ^ σ * ((bdryEndsE Tr σ).card : ℝ))) :=
        Finset.sum_le_sum fun σ _ => lintegral_bLayer_le hη hN hb σ
    _ = ENNReal.ofReal (∑ σ ∈ treeScales Tr, bLayerConst 𝔭 * ((2 : ℝ) ^ σ * ((bdryEndsE Tr σ).card : ℝ))) :=
        (ENNReal.ofReal_sum_of_nonneg fun σ _ => by
          have := zpow_two_pos σ
          positivity).symm
    _ ≤ ENNReal.ofReal (12 * bLayerConst 𝔭 * (2 : ℝ) ^ t.1.1) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        have := sum_bdryEndsE_le hg (S := treeScales Tr) (Finset.Subset.refl _)
        calc bLayerConst 𝔭 * ∑ σ ∈ treeScales Tr, (2 : ℝ) ^ σ * ((bdryEndsE Tr σ).card : ℝ)
            ≤ bLayerConst 𝔭 * (12 * (2 : ℝ) ^ t.1.1) := mul_le_mul_of_nonneg_left this hc
          _ = _ := by ring

end Cutoff

end PrimeBHT.TimeFrequency.X2
