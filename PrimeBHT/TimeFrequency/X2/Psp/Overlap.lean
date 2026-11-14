module

public import PrimeBHT.TimeFrequency.X2.Psp.Defs
public import PrimeBHT.TimeFrequency.X2.Psp.Split
public import PrimeBHT.TimeFrequency.X2.Psp.Geometry
public import PrimeBHT.TimeFrequency.X2.EnergyTop
public import PrimeBHT.TimeFrequency.X2.TopSelect
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.ClassLemmas

/-!
# X2, V13 part 2 (B): the overlapping projection, the top-operator bookkeeping (fat data)

`docs/audits/X2-V13-route-check.md` §2.6, `docs/audits/X2-REV3-fat-top.md` §1.1.  This file proves everything about the
low-pass symbols `T_σ = lowSym θ_k σ` as REV3 TOP OPERATORS:

* `lowSym_inTopMult`: `c₀ · lowSym θ σ` is an `InTopMult` multiplier at the datum `(W, ξ')` (`W.1 = σ`) whenever
  `9/2 · 2^{-σ} ≤ |ξ' f_k - θ| ≤ 31/4 · 2^{-σ}` (hole `1/4` avoided, support radius `≤ 12`), with `c₀` depending only on
  `𝔭.C, 𝔭.D` (derivative bounds of the fixed profile);
* `exists_fat_grid_datum`: for a tile `R ∈ Cs` with `ξ_T ∈ (13/4) ω̃_k(R)` (overlapping slot), every lattice interval `W ⊇ I_R`
  (`J ∣ W.1 - R.scale`, no scale gap needed) and a sign `ε = ±1`, there is a grid frequency `ξ'` with
  `|ξ' f_k - (θ + 5 ε 2^{-W.1})| ≤ 2^{-W.1}/8` and `IsTopDatum J Cs W ξ'` (`isTopDatum_of_nonlacunary`);
* `lowSym_le_engTop`: the resulting bound `|W|^{-1/q} ‖ψ T_σ F‖_{L^q(L^s)} ≤ engTop` for every cutoff `ψ ∈ Ψ_W(𝔭)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Derivative bounds of the low-pass symbol -/

theorem hasCompactSupport_lowProfileC : HasCompactSupport (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) :=
  hasCompactSupport_of_far (c := 0) (r := 17 / 4) (fun u hu => by
    rw [sub_zero] at hu
    rw [lowProfile_eq_zero hu.le, Complex.ofReal_zero])

theorem exists_lowProfile_deriv_bound (D : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ a ≤ D, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) u‖ ≤ Λ := by
  have hs : ContDiff ℝ ∞ (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_lowProfile
  obtain ⟨C, hC0, hC⟩ := hasCompactSupport_lowProfileC.exists_bound_iteratedFDeriv hs D
  exact ⟨C, hC0, fun a ha u => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC a ha u⟩

theorem norm_iteratedDeriv_lowSym_le {D : ℕ} {Λ : ℝ}
    (hΛ : ∀ a ≤ D, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) u‖ ≤ Λ)
    (θ : ℝ) (σ : ℤ) {a : ℕ} (ha : a ≤ D) (ξ : ℝ) :
    ‖iteratedDeriv a (lowSym θ σ) ξ‖ ≤ ((2 : ℝ) ^ σ) ^ a * Λ := by
  have hf : ContDiff ℝ a (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_lowProfile).of_le (by exact_mod_cast le_top)
  set g : ℝ → ℂ := fun x => ((lowProfile ((2 : ℝ) ^ σ * x) : ℝ) : ℂ) with hg
  have e : lowSym θ σ = fun ξ => g (ξ - θ) := by
    funext ξ; simp only [hg]; unfold lowSym; rw [mul_comm]
  have e2 : g = fun x => (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) ((2 : ℝ) ^ σ * x) := rfl
  have h1 := congrFun (iteratedDeriv_comp_sub_const (n := a) (f := g) (s := θ)) ξ
  have h2 := congrFun (iteratedDeriv_comp_const_smul (n := a) (f := fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) hf
    ((2 : ℝ) ^ σ : ℝ)) (ξ - θ)
  rw [e, h1]
  rw [e2, h2]
  simp only [norm_smul, norm_pow, Real.norm_of_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) σ)]
  exact mul_le_mul_of_nonneg_left (hΛ a ha _) (by positivity)

/-! ## The low-pass symbols are top multipliers -/

/-! ## Fat grid data for the low-pass operators -/

/-- **REV3 fatness of the data of the overlapping projection** (re-derived): for a tile `R ∈ Cs` whose slot `k` is overlapping
(`ξ_T ∈ (13/4) ω̃_k(R)`), EVERY lattice interval `W ⊇ I_R` with `J ∣ W.1 - R.scale` (in particular `W.1 = R.scale`: no scale gap
needed) and every sign `ε = ±1`, there is a grid frequency `ξ'` with `|ξ' f_k - (θ_k + 5 ε 2^{-W.1})| ≤ 2^{-W.1}/8`
(`θ_k = ξ_T f_k`) that is a TOP DATUM of `Cs` (`IsTopDatum`, fat radius `24 · 2^{-W.1}` inside `hull R`). -/
theorem exists_fat_grid_datum {J : ℕ} {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {k : Fin 3} {t : Top}
    (hov : IsOvSlot t k R.box) {W : ℤ × ℤ} (hW : R.I ⊆ dyadicInt W.1 W.2) (hJ : (J : ℤ) ∣ W.1 - R.box.scale)
    (ε : ℝ) (hε : |ε| = 1) :
    ∃ ξ' : ℝ, |ξ' * freqDir k - (t.2 * freqDir k + 5 * ε * (2 : ℝ) ^ (-W.1))| ≤ (2 : ℝ) ^ (-W.1) / 8 ∧
      IsTopDatum J Cs W ξ' := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  have hf1 : 1 ≤ freqDir k := by fin_cases k <;> simp [freqDir]
  have hf2 := freqDir_le_two' k
  have hfp := freqDir_pos' k
  set a : ℝ := (2 : ℝ) ^ (-W.1) with hadef
  obtain ⟨z, hz⟩ := exists_grid_near W (t.2 + 5 * ε * a / freqDir k)
  set ξ' : ℝ := (z : ℝ) * (gridMesh * (2 : ℝ) ^ (-W.1)) with hξ'
  have hg : gridMesh * (2 : ℝ) ^ (-W.1) / 2 = a / 16 := by unfold gridMesh; try ring
  rw [hg] at hz
  have h1 : |ξ' - (t.2 + 5 * ε * a / freqDir k)| ≤ a / 16 := hz
  refine ⟨ξ', ?_, ?_⟩
  · have e : ξ' * freqDir k - (t.2 * freqDir k + 5 * ε * a) =
        freqDir k * (ξ' - (t.2 + 5 * ε * a / freqDir k)) := by field_simp
    rw [e, abs_mul, abs_of_pos hfp]
    calc freqDir k * |ξ' - (t.2 + 5 * ε * a / freqDir k)| ≤ 2 * (a / 16) :=
          mul_le_mul hf2 h1 (abs_nonneg _) (by norm_num)
      _ = a / 8 := by ring
  · refine isTopDatum_of_nonlacunary hR hov hW hJ ⟨z, rfl⟩ ?_
    have h2 : |5 * ε * a / freqDir k| ≤ 5 * a := by
      have e : |5 * ε * a / freqDir k| = 5 * a / freqDir k := by
        rw [abs_div, abs_of_pos hfp]
        congr 1
        rw [abs_mul, abs_mul, hε, abs_of_pos ha]; norm_num
      rw [e]; exact div_le_self (by positivity) hf1
    calc |ξ' - t.2| = |(ξ' - (t.2 + 5 * ε * a / freqDir k)) + 5 * ε * a / freqDir k| := by ring_nf
      _ ≤ |ξ' - (t.2 + 5 * ε * a / freqDir k)| + |5 * ε * a / freqDir k| := abs_add_le _ _
      _ ≤ 6 * a := by linarith

/-- A top operator is bounded by the top energy (the definition of `engTop`). -/
theorem topOp_le_engTop {𝔭 : Params} {P : ℕ} [NeZero P] {s q : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    {Cs : Finset TriTile} {W : ℤ × ℤ} {ξ' : ℝ} (hd : IsTopDatum 𝔭.J Cs W ξ') {ψ m : ℝ → ℂ}
    (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMult 𝔭 W ξ' k m) :
    ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal q) volume ≤ engTop 𝔭 s k F Cs q :=
  le_iSup₂_of_le W ξ' (le_iSup_of_le hd (le_iSup₂_of_le ψ m (le_iSup₂_of_le hψ hm le_rfl)))

/-! ## The scale bookkeeping: from `Ẽ_σ` to a lattice interval above a tile -/

/-- **G-3 + REV3**: if `3 I₀ ∩ Ẽ_σ ≠ ∅` (`I₀` a lattice `σ`-interval, `σ ≡` the tile scales mod `J ≥ 2`), there is a tile
`R ∈ TA` (overlapping in slot `k`: `ξ_T ∈ (13/4) ω̃_k(R)`), a lattice interval `W = (σ, v) ⊇ I_R` with `J ∣ σ - R.scale`
(so the low-pass top operator at scale `σ` is covered by `exists_lowSym_le_engTop`) and `W ⊆ 5 I₀`.  Nothing requires
`σ ≥ R.scale + O(1)`: `σ = R.scale` is allowed. -/
theorem exists_lattice_key_near {J : ℕ} (hJ : 2 ≤ J) {TA : Finset TriTile} {W₀ : ℤ × ℤ} {σ u : ℤ}
    (hlat : ∀ R ∈ TA, (J : ℤ) ∣ R.box.scale - σ)
    (h : (dilate 3 (dyadicInt σ u) ∩ eTil TA W₀ σ).Nonempty) :
    ∃ R ∈ TA, R.box.scale ≤ σ ∧ ∃ v : ℤ, R.I ⊆ dyadicInt σ v ∧ (J : ℤ) ∣ σ - R.box.scale ∧
      dyadicInt σ v ⊆ dilate 5 (dyadicInt σ u) := by
  obtain ⟨R, hR, hRs, hRI⟩ := exists_tile_near hJ hlat h
  obtain ⟨v, hv⟩ := exists_dyadicInt_superset R.box.scale R.pos hRs
  refine ⟨R, hR, hRs, v, hv, ?_, ?_⟩
  · have := hlat R hR
    have := dvd_neg.2 this
    simpa using this
  · -- the key `(σ, v)` meets `5 I₀` (at a point of `I_R`), hence lies inside it
    have hx : (2 : ℝ) ^ R.box.scale * R.pos ∈ R.I := by unfold TriTile.I; exact mem_dyadicInt_left _ _
    have hx5 := hRI hx
    have hxv := hv hx
    rw [mem_dilate_dyadicInt_iff] at hx5
    intro y hy
    rw [mem_dilate_dyadicInt_iff]
    have hp := zpow_two_pos σ
    obtain ⟨h1, h2⟩ := hxv
    obtain ⟨h3, h4⟩ := hx5
    obtain ⟨h5, h6⟩ := hy
    have a1 : (v : ℝ) < (u : ℝ) + 3 := by
      by_contra hc; push Not at hc; nlinarith
    have a2 : (u : ℝ) - 3 < (v : ℝ) := by
      by_contra hc; push Not at hc; nlinarith
    have b1 : v < u + 3 := by exact_mod_cast a1
    have b2 : u - 3 < v := by exact_mod_cast a2
    have c1 : (u : ℝ) - 2 ≤ v := by exact_mod_cast (by omega : u - 2 ≤ v)
    have c2 : (v : ℝ) ≤ u + 2 := by exact_mod_cast (by omega : v ≤ u + 2)
    constructor <;> nlinarith

/-! ## The named missing lemma: (O1) -/

end PrimeBHT.TimeFrequency.X2
