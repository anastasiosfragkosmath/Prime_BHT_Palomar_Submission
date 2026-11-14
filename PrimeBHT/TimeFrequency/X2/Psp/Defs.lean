module

public import PrimeBHT.TimeFrequency.X2.GoodTree
public import PrimeBHT.TimeFrequency.X2.Collections
public import PrimeBHT.TimeFrequency.X2.Classes
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# X2, V13 (phase-space projections), the objects (`X2/Psp/Defs.lean`)

`docs/audits/X2-V13-route-check.md` §1.3 adapted to REV3 (`docs/audits/X2-REV3-fat-top.md`: `hullDil = 128`,
`hullConst = 256`, `ovThr = 13/4`).

* the layers of a tree: `treeScales`, `layer'`, `layerKeys`, `layerCut` (`χ̃_σ = 1_{E_σ} * η_σ`), `layerSet` (`E_σ`);
* the lattice geometry on `s₀ + Jℤ` (MTT2 §4): `freeKey`, `eTilKeys`, `eTil` (`Ẽ_σ`), endpoint sets
  (`leftEndsOf`, `rightEndsOf`, `leftEnds`, `rightEnds`, `leftEndsE`, `rightEndsE`), bump intervals, `muW`
  (MTT2 (51));
* the symbols of the projections: the fixed profiles `lacProfile`, `lowProfile` (smooth), `lacSym`, `lowSym`;
* the split: `ovThr`, `IsOvSlot`, `slotType`, `treePart`.

**Deviation (the definition of `Ẽ_σ`).** MTT2 Def 4.9 defines `Ẽ_σ` as the union of the maximal "free" lattice
intervals `I` (those with `3I` containing no tile interval) with `|I| < 2^σ`.  Here `Ẽ_σ` is defined directly as the
union of the lattice intervals of length `2^σ` inside the top `W` that are NOT free (`eTilKeys`); this is the same set
for lattice `σ` (the dichotomy of MTT2 Lemma 4.10: a `σ`-interval is inside a maximal free interval or is partitioned
into strictly smaller ones), but needs no maximality bookkeeping, and every property V13 uses is a one-line
consequence (`X2/Psp/Geometry.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Layers of a tree -/

/-- The scales occurring in a tree. -/
def treeScales (Tr : Finset TriTile) : Finset ℤ := Tr.image (fun R => R.box.scale)

/-- The tiles of scale `σ`: `Q^σ`. -/
def layer' (Tr : Finset TriTile) (σ : ℤ) : Finset TriTile := Tr.filter (fun R => R.box.scale = σ)

/-- The positions of the tiles of scale `σ`. -/
def layerKeys (Tr : Finset TriTile) (σ : ℤ) : Finset ℤ := (layer' Tr σ).image (fun R => R.pos)

/-- `χ̃_σ = Σ_{R ∈ Q^σ} 1_{I_R} * η_σ` (the cutoff of the scale `σ`). -/
def layerCut (η : ℝ → ℝ) (Tr : Finset TriTile) (σ : ℤ) (x : ℝ) : ℝ :=
  ∑ R ∈ layer' Tr σ, tileCutoff η σ R.pos x

/-- The spatial set `E_{Q^σ, T} = ⋃_{R ∈ Q^σ} I_R`. -/
def layerSet (Tr : Finset TriTile) (σ : ℤ) : Set ℝ := ⋃ R ∈ layer' Tr σ, R.I

theorem mem_layer'_iff {Tr : Finset TriTile} {σ : ℤ} {R : TriTile} :
    R ∈ layer' Tr σ ↔ R ∈ Tr ∧ R.box.scale = σ := by
  simp [layer']

/-- With the model cutoffs `χ_R = 1_{I_R} * η_s` (R3 of `IsModelData`), `Σ_{R ∈ Q^σ} χ_R = χ̃_σ`. -/
theorem sum_layer'_cutoff_eq_layerCut {η : ℝ → ℝ} {χ : TriTile → ℝ → ℝ} {Tr : Finset TriTile}
    (h : ∀ R ∈ Tr, χ R = tileCutoff η R.box.scale R.pos) (σ : ℤ) (x : ℝ) :
    ∑ R ∈ layer' Tr σ, χ R x = layerCut η Tr σ x := by
  unfold layerCut
  refine Finset.sum_congr rfl fun R hR => ?_
  obtain ⟨hRT, hs⟩ := mem_layer'_iff.1 hR
  rw [h R hRT, hs]

theorem mem_treeScales_iff {Tr : Finset TriTile} {σ : ℤ} :
    σ ∈ treeScales Tr ↔ ∃ R ∈ Tr, R.box.scale = σ := by
  simp [treeScales]

theorem mem_layerKeys_iff {Tr : Finset TriTile} {σ v : ℤ} :
    v ∈ layerKeys Tr σ ↔ ∃ R ∈ Tr, R.box.scale = σ ∧ R.pos = v := by
  simp only [layerKeys, Finset.mem_image, mem_layer'_iff]
  constructor
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩; exact ⟨R, h1, h2, h3⟩
  · rintro ⟨R, h1, h2, h3⟩; exact ⟨R, ⟨h1, h2⟩, h3⟩

/-! ## The lattice geometry (MTT2 §4) -/

/-- A lattice key `K = (s, v)` is FREE for the tree `Tr` if `3 I_K` contains no tile interval of `Tr`. -/
def freeKey (Tr : Finset TriTile) (K : ℤ × ℤ) : Prop :=
  ∀ R ∈ Tr, ¬ R.I ⊆ dilate 3 (dyadicInt K.1 K.2)

/-- The keys `v` of the `σ`-intervals of `Ẽ_σ` inside the top `W`: the non-free lattice intervals of length `2^σ`. -/
def eTilKeys (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : Set ℤ :=
  {v | dyadicInt σ v ⊆ dyadicInt W.1 W.2 ∧ ¬ freeKey Tr (σ, v)}

/-- `Ẽ_σ` (MTT2 Def 4.9; see the module docstring for the deviation). -/
def eTil (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : Set ℝ := ⋃ v ∈ eTilKeys Tr W σ, dyadicInt σ v

/-- The set of keys inside `W` at scale `σ` is finite. -/
theorem finite_keys_in (W : ℤ × ℤ) (σ : ℤ) : {v : ℤ | dyadicInt σ v ⊆ dyadicInt W.1 W.2}.Finite := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ σ := zpow_pos (by norm_num) _
  refine (Set.finite_Icc ⌈(2 : ℝ) ^ W.1 * W.2 / (2 : ℝ) ^ σ⌉ ⌊(2 : ℝ) ^ W.1 * (W.2 + 1) / (2 : ℝ) ^ σ⌋).subset
    ?_
  intro v hv
  have hx : (2 : ℝ) ^ σ * v ∈ dyadicInt σ v := ⟨le_rfl, by nlinarith⟩
  have hx' : (2 : ℝ) ^ σ * (v + 1) - (2 : ℝ) ^ σ * ((1 : ℝ) / 2) ∈ dyadicInt σ v :=
    ⟨by nlinarith, by nlinarith⟩
  obtain ⟨h1, h2⟩ := hv hx
  obtain ⟨h3, h4⟩ := hv hx'
  simp only [Set.mem_Icc]
  constructor
  · rw [Int.ceil_le, div_le_iff₀ hp]
    nlinarith
  · rw [Int.le_floor, le_div_iff₀ hp]
    nlinarith

theorem eTilKeys_finite (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : (eTilKeys Tr W σ).Finite :=
  (finite_keys_in W σ).subset fun _ hv => hv.1

/-- `eTilKeys` as a finset. -/
def eTilKeysF (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : Finset ℤ := (eTilKeys_finite Tr W σ).toFinset

theorem mem_eTilKeysF {Tr : Finset TriTile} {W : ℤ × ℤ} {σ v : ℤ} :
    v ∈ eTilKeysF Tr W σ ↔ v ∈ eTilKeys Tr W σ := by
  simp [eTilKeysF]

/-- Left endpoints of the components of the union of the `σ`-intervals with keys in `V`
(`x = 2^σ v`, `v ∈ V`, `v - 1 ∉ V`). -/
def leftEndsOf (σ : ℤ) (V : Finset ℤ) : Finset ℝ :=
  (V.filter (fun v => v - 1 ∉ V)).image (fun v : ℤ => (2 : ℝ) ^ σ * (v : ℝ))

/-- Right endpoints of the components (`x = 2^σ (v + 1)`, `v ∈ V`, `v + 1 ∉ V`). -/
def rightEndsOf (σ : ℤ) (V : Finset ℤ) : Finset ℝ :=
  (V.filter (fun v => v + 1 ∉ V)).image (fun v : ℤ => (2 : ℝ) ^ σ * ((v : ℝ) + 1))

/-- The left endpoints of `Ẽ_σ`. -/
def leftEnds (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : Finset ℝ := leftEndsOf σ (eTilKeysF Tr W σ)

/-- The right endpoints of `Ẽ_σ`. -/
def rightEnds (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : Finset ℝ := rightEndsOf σ (eTilKeysF Tr W σ)

/-- `∂Ẽ_σ`. -/
def bdryEnds (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : Finset ℝ := leftEnds Tr W σ ∪ rightEnds Tr W σ

/-- The left endpoints of `E_σ = layerSet Tr σ`. -/
def leftEndsE (Tr : Finset TriTile) (σ : ℤ) : Finset ℝ := leftEndsOf σ (layerKeys Tr σ)

/-- The right endpoints of `E_σ`. -/
def rightEndsE (Tr : Finset TriTile) (σ : ℤ) : Finset ℝ := rightEndsOf σ (layerKeys Tr σ)

/-- `∂E_σ`. -/
def bdryEndsE (Tr : Finset TriTile) (σ : ℤ) : Finset ℝ := leftEndsE Tr σ ∪ rightEndsE Tr σ

/-- The bump interval to the left of a left endpoint `x` of scale `σ`:
`I^ℓ_σ(x) = (x - 2^{σ-1}, x - 2^{σ-2})` (MTT2 Lemma 4.12; length `2^{σ-2}`). -/
def leftBump (σ : ℤ) (x : ℝ) : Set ℝ := Set.Ioo (x - (2 : ℝ) ^ (σ - 1)) (x - (2 : ℝ) ^ (σ - 2))

/-- The bump interval to the right of a right endpoint `x`: `I^r_σ(x) = (x + 2^{σ-2}, x + 2^{σ-1})`. -/
def rightBump (σ : ℤ) (x : ℝ) : Set ℝ := Set.Ioo (x + (2 : ℝ) ^ (σ - 2)) (x + (2 : ℝ) ^ (σ - 1))

/-- **MTT2 (51)**: `μ_σ(x) = Σ_{σ'} 2^{-|σ - σ'|/(100 J)} Σ_{y ∈ ∂Ẽ_{σ'}} ⟨(x - y)/2^{σ'}⟩^{-100}`, the sum over the
finite set `S` of lattice scales (`σ' ∈ S`), `ends σ'` the endpoint set of the scale `σ'`. -/
def muW (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ : ℤ) (x : ℝ) : ℝ :=
  ∑ σ' ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
    ∑ y ∈ ends σ', jb ((x - y) / (2 : ℝ) ^ σ') ^ (-100 : ℝ)

/-! ## The symbols of the projections -/

/-- The smooth step `0` for `x ≤ a`, `1` for `x ≥ b` (`a < b` or `a > b`). -/
def smoothStep (a b : ℝ) (x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

theorem contDiff_smoothStep (a b : ℝ) : ContDiff ℝ ∞ (smoothStep a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem smoothStep_eq_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : smoothStep a b x = 1 := by
  unfold smoothStep
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem smoothStep_eq_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : smoothStep a b x = 0 := by
  unfold smoothStep
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem smoothStep_eq_one' {a b x : ℝ} (hab : b < a) (hx : x ≤ b) : smoothStep a b x = 1 := by
  unfold smoothStep
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff_of_neg (by linarith)]
  linarith

theorem smoothStep_eq_zero' {a b x : ℝ} (hab : b < a) (hx : a ≤ x) : smoothStep a b x = 0 := by
  unfold smoothStep
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem smoothStep_nonneg (a b x : ℝ) : 0 ≤ smoothStep a b x := Real.smoothTransition.nonneg _

theorem smoothStep_le_one (a b x : ℝ) : smoothStep a b x ≤ 1 := Real.smoothTransition.le_one _

/-- The upper edge of the annulus where `lacProfile = 1`: `2 hullConst + 4` (the Fourier support of a lacunary
piece lies in `{1/4 - δ ≤ |ξ - θ_k|/ℓ ≤ 2 hullConst + 11/8 + δ}`; `X2/Psp/Split.lean`). -/
def lacHi : ℝ := 2 * hullConst + 4

/-- The upper edge of the support of `lacProfile`: `2 hullConst + 5`. -/
def lacHi0 : ℝ := 2 * hullConst + 5

/-- The fixed smooth lacunary profile: `= 1` on `{3/16 ≤ |u| ≤ lacHi}`, `= 0` on `{|u| ≤ 1/8}` and on
`{|u| ≥ lacHi0}`. -/
def lacProfile (u : ℝ) : ℝ :=
  smoothStep (1 / 64) (9 / 256) (u ^ 2) * smoothStep (lacHi0 ^ 2) (lacHi ^ 2) (u ^ 2)

/-- The fixed smooth low-pass profile: `= 1` on `{|u| ≤ 4}`, `= 0` on `{|u| ≥ 17/4}` (MTT2's `T_j`). -/
def lowProfile (u : ℝ) : ℝ := smoothStep (289 / 16) 16 (u ^ 2)

/-- The lacunary symbol of scale `σ` modulated to the slot frequency `θ`:
`lacSym θ σ ξ = ψlac((ξ - θ) 2^σ)`. -/
def lacSym (θ : ℝ) (σ : ℤ) (ξ : ℝ) : ℂ := ((lacProfile ((ξ - θ) * (2 : ℝ) ^ σ) : ℝ) : ℂ)

/-- The low-pass symbol of scale `σ` modulated to `θ`: `lowSym θ σ ξ = λ0((ξ - θ) 2^σ)`. -/
def lowSym (θ : ℝ) (σ : ℤ) (ξ : ℝ) : ℂ := ((lowProfile ((ξ - θ) * (2 : ℝ) ^ σ) : ℝ) : ℂ)

theorem lacHi_eq : lacHi = 516 := by unfold lacHi hullConst; norm_num

theorem lacHi0_eq : lacHi0 = 517 := by unfold lacHi0 hullConst; norm_num

theorem sq_le_of_abs_le {u r : ℝ} (_hr : 0 ≤ r) (h : |u| ≤ r) : u ^ 2 ≤ r ^ 2 :=
  calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    _ ≤ r ^ 2 := pow_le_pow_left₀ (abs_nonneg u) h 2

theorem sq_ge_of_abs_ge {u r : ℝ} (hr : 0 ≤ r) (h : r ≤ |u|) : r ^ 2 ≤ u ^ 2 :=
  calc r ^ 2 ≤ |u| ^ 2 := pow_le_pow_left₀ hr h 2
    _ = u ^ 2 := sq_abs u

theorem contDiff_lowProfile : ContDiff ℝ ∞ lowProfile :=
  (contDiff_smoothStep _ _).comp (contDiff_id.pow 2)

theorem lowProfile_eq_one {u : ℝ} (h : |u| ≤ 4) : lowProfile u = 1 :=
  smoothStep_eq_one' (by norm_num) (by have := sq_le_of_abs_le (by norm_num) h; nlinarith)

theorem lowProfile_eq_zero {u : ℝ} (h : 17 / 4 ≤ |u|) : lowProfile u = 0 :=
  smoothStep_eq_zero' (by norm_num) (by have := sq_ge_of_abs_ge (by norm_num) h; nlinarith)

theorem contDiff_lacProfile : ContDiff ℝ ∞ lacProfile :=
  ((contDiff_smoothStep _ _).comp (contDiff_id.pow 2)).mul ((contDiff_smoothStep _ _).comp (contDiff_id.pow 2))

theorem lacProfile_eq_one {u : ℝ} (h1 : 3 / 16 ≤ |u|) (h2 : |u| ≤ lacHi) : lacProfile u = 1 := by
  unfold lacProfile
  rw [smoothStep_eq_one (by norm_num) (by have := sq_ge_of_abs_ge (by norm_num) h1; nlinarith),
    smoothStep_eq_one' (by rw [lacHi0_eq, lacHi_eq]; norm_num)
      (by have := sq_le_of_abs_le (by rw [lacHi_eq]; norm_num) h2; nlinarith), one_mul]

theorem lacProfile_eq_zero_of_le {u : ℝ} (h : |u| ≤ 1 / 8) : lacProfile u = 0 := by
  unfold lacProfile
  rw [smoothStep_eq_zero (by norm_num) (by have := sq_le_of_abs_le (by norm_num) h; nlinarith), zero_mul]

theorem lacProfile_eq_zero_of_ge {u : ℝ} (h : lacHi0 ≤ |u|) : lacProfile u = 0 := by
  unfold lacProfile
  have h0 : smoothStep (lacHi0 ^ 2) (lacHi ^ 2) (u ^ 2) = 0 :=
    smoothStep_eq_zero' (by rw [lacHi0_eq, lacHi_eq]; norm_num)
      (by have := sq_ge_of_abs_ge (by rw [lacHi0_eq]; norm_num) h; nlinarith)
  rw [h0, mul_zero]

theorem lowProfile_nonneg (u : ℝ) : 0 ≤ lowProfile u := smoothStep_nonneg _ _ _

theorem lowProfile_le_one (u : ℝ) : lowProfile u ≤ 1 := smoothStep_le_one _ _ _

theorem contDiff_lacSym (θ : ℝ) (σ : ℤ) : ContDiff ℝ ∞ (lacSym θ σ) :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_lacProfile.comp ((contDiff_id.sub contDiff_const).mul contDiff_const))

theorem contDiff_lowSym (θ : ℝ) (σ : ℤ) : ContDiff ℝ ∞ (lowSym θ σ) :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_lowProfile.comp ((contDiff_id.sub contDiff_const).mul contDiff_const))

theorem abs_sub_mul_zpow (θ ξ : ℝ) (σ : ℤ) : |(ξ - θ) * (2 : ℝ) ^ σ| = |ξ - θ| * (2 : ℝ) ^ σ := by
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) σ)]

theorem le_zpow_neg_iff {x r : ℝ} (σ : ℤ) : x * (2 : ℝ) ^ σ ≤ r ↔ x ≤ r * (2 : ℝ) ^ (-σ) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ σ := zpow_pos (by norm_num) _
  rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ hp]

theorem ge_zpow_neg_iff {x r : ℝ} (σ : ℤ) : r ≤ x * (2 : ℝ) ^ σ ↔ r * (2 : ℝ) ^ (-σ) ≤ x := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ σ := zpow_pos (by norm_num) _
  rw [zpow_neg, ← div_eq_mul_inv, div_le_iff₀ hp]

theorem lowSym_eq_one {θ ξ : ℝ} {σ : ℤ} (h : |ξ - θ| ≤ 4 * (2 : ℝ) ^ (-σ)) : lowSym θ σ ξ = 1 := by
  unfold lowSym
  rw [lowProfile_eq_one (by rw [abs_sub_mul_zpow]; exact (le_zpow_neg_iff σ).2 h), Complex.ofReal_one]

theorem lowSym_eq_zero {θ ξ : ℝ} {σ : ℤ} (h : 17 / 4 * (2 : ℝ) ^ (-σ) ≤ |ξ - θ|) : lowSym θ σ ξ = 0 := by
  unfold lowSym
  rw [lowProfile_eq_zero (by rw [abs_sub_mul_zpow]; exact (ge_zpow_neg_iff σ).2 h), Complex.ofReal_zero]

theorem lacSym_eq_one {θ ξ : ℝ} {σ : ℤ} (h1 : 3 / 16 * (2 : ℝ) ^ (-σ) ≤ |ξ - θ|)
    (h2 : |ξ - θ| ≤ lacHi * (2 : ℝ) ^ (-σ)) : lacSym θ σ ξ = 1 := by
  unfold lacSym
  rw [lacProfile_eq_one (by rw [abs_sub_mul_zpow]; exact (ge_zpow_neg_iff σ).2 h1)
    (by rw [abs_sub_mul_zpow]; exact (le_zpow_neg_iff σ).2 h2), Complex.ofReal_one]

theorem lacSym_eq_zero_of_le {θ ξ : ℝ} {σ : ℤ} (h : |ξ - θ| ≤ 1 / 8 * (2 : ℝ) ^ (-σ)) :
    lacSym θ σ ξ = 0 := by
  unfold lacSym
  rw [lacProfile_eq_zero_of_le (by rw [abs_sub_mul_zpow]; exact (le_zpow_neg_iff σ).2 h), Complex.ofReal_zero]

theorem lacSym_eq_zero_of_ge {θ ξ : ℝ} {σ : ℤ} (h : lacHi0 * (2 : ℝ) ^ (-σ) ≤ |ξ - θ|) :
    lacSym θ σ ξ = 0 := by
  unfold lacSym
  rw [lacProfile_eq_zero_of_ge (by rw [abs_sub_mul_zpow]; exact (ge_zpow_neg_iff σ).2 h), Complex.ofReal_zero]

theorem mem_leftEndsOf {σ : ℤ} {V : Finset ℤ} {x : ℝ} :
    x ∈ leftEndsOf σ V ↔ ∃ v ∈ V, v - 1 ∉ V ∧ (2 : ℝ) ^ σ * (v : ℝ) = x := by
  simp [leftEndsOf, Finset.mem_image, Finset.mem_filter, and_assoc]

theorem mem_rightEndsOf {σ : ℤ} {V : Finset ℤ} {x : ℝ} :
    x ∈ rightEndsOf σ V ↔ ∃ v ∈ V, v + 1 ∉ V ∧ (2 : ℝ) ^ σ * ((v : ℝ) + 1) = x := by
  simp [rightEndsOf, Finset.mem_image, Finset.mem_filter, and_assoc]

/-! ## The split of a good tree -/

/-- The threshold of the split (`13/4`: `β + 2δ < 3 < 13/4`, and `13/4 ≤ 4` for the single-box condition (g)). -/
def ovThr : ℝ := 13 / 4

/-- The slot `k` of the box `B` is OVERLAPPING (non-lacunary) for the top `t`: `ξ_T ∈ (13/4) ω̃_k(B)`
(normalized coordinates). -/
def IsOvSlot (t : Top) (k : Fin 3) (B : Box) : Prop := t.2 ∈ dilate ovThr (B.ωn k)

/-- `A(B)`: the LACUNARY slots of the box `B` (those where `ξ_T ∉ (13/4) ω̃_k(B)`). -/
def slotType (t : Top) (B : Box) : Finset (Fin 3) := Finset.univ.filter (fun k => ¬ IsOvSlot t k B)

/-- The part `T_A` of a tree: the tiles whose lacunary slot set is `A`. -/
def treePart (Tr : Finset TriTile) (t : Top) (A : Finset (Fin 3)) : Finset TriTile :=
  Tr.filter (fun R => slotType t R.box = A)

theorem mem_treePart {Tr : Finset TriTile} {t : Top} {A : Finset (Fin 3)} {R : TriTile} :
    R ∈ treePart Tr t A ↔ R ∈ Tr ∧ slotType t R.box = A := by
  simp [treePart]

theorem mem_slotType {t : Top} {B : Box} {k : Fin 3} : k ∈ slotType t B ↔ ¬ IsOvSlot t k B := by
  simp [slotType]

end PrimeBHT.TimeFrequency.X2
