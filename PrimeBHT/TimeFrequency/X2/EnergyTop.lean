module

public import PrimeBHT.TimeFrequency.X2.V16.Defs
public import PrimeBHT.TimeFrequency.X2.Energy
public import PrimeBHT.TimeFrequency.X2.ClassLemmas
public import PrimeBHT.TimeFrequency.X2.GoodTree

/-!
# X2, REV2: top-term energies, combined energies `engV`, and the halving step of `engV`

Promoted from `drafts/x2-interface/10-rev2-EnergyTop-TreeLemma-V16.lean.txt` (design doc `docs/x2-interface-design.md`
§REV2, `docs/audits/X2-R1-route-check.md`):

* `topRad`, `topHole`, `InTopMult`, `topOpNorm`, `fatRad`, `gridMesh`, `IsTopDatum` (REV3: fat, sandwich-free), `engTop`
  (monotone in the collection), `qv`, `engV`
  (`max` of `eng` and `engTop`, both in the class `𝔭.tree`; monotone);
* the V12 statements `EnergyLemmaStatement` (for `eng`) and `EnergyLemmaTopStatement` (for `engTop`, UNVERIFIED);
* `engV_step`: the halving step of `engV` with the global and the localized count, DERIVED from the two V12 statements
  (apply the step of one part only when that part is above half of `engV`).

## Deviation from the draft

`engV_step` takes `hX : IsEnergyExponent (slotExp u k) (qv R k)` instead of `4 ≤ R`: for `k = 2` the energy exponent
condition `u < R`, `u/(u-1) < R` does NOT follow from `1 < u`, `4 ≤ R` (the draft statement is not provable as printed).
For `R = Rof u` it holds (`isEnergyExponent_slot` in `V16/Hyps.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-! ## Top operators (MTT2's size top term, made maximal) -/

/-- Support radius of a top multiplier, in units of `2^{-W.1}` (the frequency scale of the top interval `W`). -/
def topRad : ℝ := 12

/-- Radius of the hole of a top multiplier around the top frequency. -/
def topHole : ℝ := 1 / 4

/-- Top multiplier class at the virtual tile `(W, ξ)`, slot `k`. -/
def InTopMult (𝔭 : Params) (W : ℤ × ℤ) (ξ : ℝ) (k : Fin 3) (m : ℝ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) m ∧
    (∀ η, topRad * (2 : ℝ) ^ (-W.1) < |η - ξ * freqDir k| → m η = 0) ∧
    (∀ η, |η - ξ * freqDir k| < topHole * (2 : ℝ) ^ (-W.1) → m η = 0) ∧
    ∀ a : ℕ, a ≤ 𝔭.D → ∀ η, ((2 : ℝ) ^ (-W.1)) ^ a * ‖iteratedDeriv a m η‖ ≤ 𝔭.C

/-- `|W|^{-1/q} sup ‖ψ T_m F‖_{L^q(L^s)}` over top operators at `(W, ξ)`. -/
def topOpNorm (𝔭 : Params) (s q : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (W : ℤ × ℤ) (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : ℝ → ℂ) (m : ℝ → ℂ) (_ : InPsi 𝔭 W.1 W.2 ψ) (_ : InTopMult 𝔭 W ξ k m),
    ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / q)) *
      eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal q) volume

/-- Radius of the fat interval of a top datum, in units of `2^{-W.1}` (REV3; `≥ 47/2 = 2 (topRad - topHole)`, see
`top_separation_pair_H` in `X2/TopSelect.lean`). -/
def fatRad : ℝ := 24

/-- Mesh of the grid of top frequencies, in units of `2^{-W.1}` (REV3, TB-0: finitely many candidates, so the maximum of
`ξ` over the candidates of a selection exists). -/
def gridMesh : ℝ := 1 / 8

/-- **Admissible top data of a collection (REV3, FAT and sandwich-free)**: a grid frequency `ξ ∈ (gridMesh·2^{-W.1}) ℤ`
and a tile `R ∈ Cs` with `I_R ⊆ W`, `J ∣ W.1 - R.scale`, whose hull contains the whole interval
`[ξ - fatRad·2^{-W.1}, ξ + fatRad·2^{-W.1}]`.  (REV2 had a coarse partner `R'` with `W ⊆ I_{R'}` and a point `ζ`: the
sandwich is unsatisfiable for the lattice scales V13 needs, and the printed data break the count of V12-top,
`docs/audits/X2-TB3-check.md`, `docs/audits/X2-REV3-fat-top.md`.) -/
def IsTopDatum (J : ℕ) (Cs : Finset TriTile) (W : ℤ × ℤ) (ξ : ℝ) : Prop :=
  (∃ z : ℤ, ξ = z * (gridMesh * (2 : ℝ) ^ (-W.1))) ∧
    ∃ R ∈ Cs, R.I ⊆ dyadicInt W.1 W.2 ∧ (J : ℤ) ∣ W.1 - R.box.scale ∧
      Set.Icc (ξ - fatRad * (2 : ℝ) ^ (-W.1)) (ξ + fatRad * (2 : ℝ) ^ (-W.1)) ⊆ R.box.hull

/-- **Top-term energy** (R1 of `docs/audits/X2-V13-route-check.md`, fat data of REV3). -/
def engTop (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (Cs : Finset TriTile) (q : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℤ × ℤ) (ξ : ℝ) (_ : IsTopDatum 𝔭.J Cs W ξ), topOpNorm 𝔭 s q k F W ξ

theorem engTop_mono (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) {Cs Cs' : Finset TriTile}
    (h : Cs ⊆ Cs') (q : ℝ) : engTop 𝔭 s k F Cs q ≤ engTop 𝔭 s k F Cs' q := by
  refine iSup_mono fun W => iSup_mono fun ξ => iSup_le fun hd => ?_
  obtain ⟨hg, R, hR, h1, h2, h3⟩ := hd
  exact le_iSup_of_le (⟨hg, R, h hR, h1, h2, h3⟩ : IsTopDatum 𝔭.J Cs' W ξ) le_rfl

/-- The slot exponents `(q_X) = (2, 2, R)`. -/
def qv (R : ℝ) (k : Fin 3) : ℝ := if k = 2 then R else 2

/-- **Combined energy** used by the tree lemma and by B7. -/
def engV (𝔭 : Params) (u R : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (Cs : Finset TriTile) : ℝ≥0∞ :=
  max (eng 𝔭.tree (slotExp u k) k F Cs (qv R k)) (engTop 𝔭.tree (slotExp u k) k F Cs (qv R k))

theorem engV_mono (𝔭 : Params) (u R : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) {Cs Cs' : Finset TriTile}
    (h : Cs ⊆ Cs') : engV 𝔭 u R k F Cs ≤ engV 𝔭 u R k F Cs' :=
  max_le_max (eng_mono _ _ _ _ h _) (engTop_mono _ _ _ _ h _)

/-! ## V12 for `eng` and for `engTop` (statements) -/

/-! ## The halving step for the combined energy -/

theorem removedTrees_append (S : Finset TriTile) (ts₁ ts₂ : List Top) :
    removedTrees S (ts₁ ++ ts₂) = removedTrees S ts₁ ++ removedTrees (removeTrees S ts₁) ts₂ := by
  induction ts₁ generalizing S with
  | nil => rfl
  | cons t ts ih =>
    show (maxTree S t.1 t.2, t) :: removedTrees (S \ maxTree S t.1 t.2) (ts ++ ts₂) = _
    rw [ih]
    rfl

/-- One halving step relative to an upper bound `E ≥ e S`: if `e` has a step with counts `A i` (for conditions
`Cond i S`), then there are tops removing the trees such that `e` drops below `E/2`, with counts `2^q A i` relative to
`E^q`.  (Apply the step of `e` only if `E/2 < e S`; then `E < 2 e S`.) -/
theorem half_step {ι : Type*} (Cond : ι → Finset TriTile → Prop) (Res : Finset TriTile → Prop)
    (e : Finset TriTile → ℝ≥0∞) {q : ℝ} (hq : 0 ≤ q) (A : ι → ℝ≥0∞)
    (st : ∀ S, Res S → ∃ ts : List Top, e (removeTrees S ts) ≤ e S / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * e S ^ q ≤ A i)
    {S : Finset TriTile} (hS : Res S) {E : ℝ≥0∞} (hE : e S ≤ E) :
    ∃ ts : List Top, e (removeTrees S ts) ≤ E / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * E ^ q ≤ 2 ^ q * A i := by
  by_cases h : E / 2 < e S
  · obtain ⟨ts, hh, hc⟩ := st S hS
    refine ⟨ts, hh.trans (ENNReal.div_le_div_right hE 2), fun i hi => ?_⟩
    have h1 : E ≤ e S * 2 := by
      have := (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).1 h
      exact this.le
    have h2 : E ^ q ≤ 2 ^ q * e S ^ q := by
      calc E ^ q ≤ (e S * 2) ^ q := ENNReal.rpow_le_rpow h1 hq
        _ = e S ^ q * 2 ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
        _ = 2 ^ q * e S ^ q := mul_comm _ _
    calc topSum (removedTrees S ts) * E ^ q ≤ topSum (removedTrees S ts) * (2 ^ q * e S ^ q) := by gcongr
      _ = 2 ^ q * (topSum (removedTrees S ts) * e S ^ q) := by ring
      _ ≤ 2 ^ q * A i := by gcongr; exact hc i hi
  · refine ⟨[], ?_, fun i _ => ?_⟩
    swap
    · show topSum [] * _ ≤ _
      rw [topSum_nil, zero_mul]; exact zero_le
    show e S ≤ _
    rw [not_lt] at h
    exact h

/-- **The halving step for `max (e₁, e₂)`**: apply the step of `e₁` (if `e₁ > E/2`), then, on the residual, the step of
`e₂` (if `e₂ > E/2`); the counts add up to `2^q (A₁ + A₂)` relative to `E^q`, `E = max (e₁ S) (e₂ S)`. -/
theorem two_step {ι : Type*} (Cond : ι → Finset TriTile → Prop)
    (hCond : ∀ i S S', S' ⊆ S → Cond i S → Cond i S') (Res : Finset TriTile → Prop)
    (hRes : ∀ S ts, Res S → Res (removeTrees S ts)) (e₁ e₂ : Finset TriTile → ℝ≥0∞)
    (hm₁ : ∀ S S', S ⊆ S' → e₁ S ≤ e₁ S') (hm₂ : ∀ S S', S ⊆ S' → e₂ S ≤ e₂ S') {q : ℝ} (hq : 0 ≤ q)
    (A₁ A₂ : ι → ℝ≥0∞)
    (st₁ : ∀ S, Res S → ∃ ts : List Top, e₁ (removeTrees S ts) ≤ e₁ S / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * e₁ S ^ q ≤ A₁ i)
    (st₂ : ∀ S, Res S → ∃ ts : List Top, e₂ (removeTrees S ts) ≤ e₂ S / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * e₂ S ^ q ≤ A₂ i)
    {S : Finset TriTile} (hS : Res S) :
    ∃ ts : List Top,
      max (e₁ (removeTrees S ts)) (e₂ (removeTrees S ts)) ≤ max (e₁ S) (e₂ S) / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * (max (e₁ S) (e₂ S)) ^ q ≤ 2 ^ q * (A₁ i + A₂ i) := by
  set E := max (e₁ S) (e₂ S) with hE
  obtain ⟨ts₁, h₁a, h₁b⟩ := half_step Cond Res e₁ hq A₁ st₁ hS (E := E) (le_max_left _ _)
  have hS₁ : Res (removeTrees S ts₁) := hRes S ts₁ hS
  have hsub₁ : removeTrees S ts₁ ⊆ S := removeTrees_subset S ts₁
  obtain ⟨ts₂, h₂a, h₂b⟩ := half_step Cond Res e₂ hq A₂ st₂ hS₁ (E := E)
    ((hm₂ _ _ hsub₁).trans (le_max_right _ _))
  refine ⟨ts₁ ++ ts₂, ?_, fun i hi => ?_⟩
  · rw [← removeTrees_removeTrees]
    refine max_le ?_ h₂a
    exact (hm₁ _ _ (removeTrees_subset _ _)).trans h₁a
  · rw [removedTrees_append, topSum_append, add_mul]
    have h1 := h₁b i hi
    have h2 := h₂b i (hCond i S _ hsub₁ hi)
    calc topSum (removedTrees S ts₁) * E ^ q +
          topSum (removedTrees (removeTrees S ts₁) ts₂) * E ^ q ≤ 2 ^ q * A₁ i + 2 ^ q * A₂ i :=
        add_le_add h1 h2
      _ = 2 ^ q * (A₁ i + A₂ i) := by ring


end PrimeBHT.TimeFrequency.X2
