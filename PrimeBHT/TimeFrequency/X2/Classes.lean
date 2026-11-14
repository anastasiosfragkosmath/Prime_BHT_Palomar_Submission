module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.TimeFrequency.Tile.Grid

/-!
# X2, node V07: carriers, class parameters, tiles, adapted classes, single-tile / tree operators, the model form

Definitions of `docs/x2-interface-design.md` §2 / `drafts/x2-interface/01-V07-Classes.lean.txt`.
Every later X2 node uses ONLY these definitions; no node may introduce its own copy of a class.
The lemmas `norm_singleTile_le` and `treeOp_locPoly` are in `X2/ClassLemmas.lean`.

Design decisions (design doc §2):
* slot values live in `ZMod P → ℂ`; slot norms are the frozen `yNorm s`;
* one parameter record `Params` for all classes (DPLMV's `(N, δ, β, c, C)` plus the grid ratio `J` and the
  number `D` of controlled multiplier derivatives); every node lemma is stated for every `𝔭` with
  `𝔭.Admissible`, constants depending on `𝔭`; the one parameter change used by V16 is `Params.loc`;
* the cutoff of the model form is ONE function `χ P` in `X_{I_P}` (MTT2's exact identity), not `χ³`.

## Deviations from the draft (all minimal)

* module header and imports; the maximal function (`maximalHLR`) is only needed in `ClassLemmas`;
* `Box.ω`, `Box.hull`, `TriTile.I`, `TriTile.len` are kept as drafted (`Set`-valued / `ℝ`-valued, unfoldable);
* a few `rfl` simp lemmas for `Params.loc` and `TriTile.I`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap ComplexConjugate ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ## Elementary objects -/

/-- The normalized pairing `⟨a, b⟩_Y = P⁻¹ Σ_y a_y conj(b_y)` (Hölder: `‖⟨a,b⟩‖ ≤ yNorm s' a · yNorm s b`). -/
def yPair {P : ℕ} [NeZero P] (a b : ZMod P → ℂ) : ℂ := (P : ℂ)⁻¹ * ∑ y, a y * conj (b y)

/-- The bracket `⟨t⟩ = 1 + |t|` (comparable to DPLMV's `(1 + t²)^{1/2}`). -/
def jb (t : ℝ) : ℝ := 1 + |t|

theorem one_le_jb (t : ℝ) : 1 ≤ jb t := by unfold jb; linarith [abs_nonneg t]

theorem jb_pos (t : ℝ) : 0 < jb t := lt_of_lt_of_le one_pos (one_le_jb t)

/-- Centre of the standard dyadic interval `dyadicInt s v = [2^s v, 2^s (v+1))`. -/
def dyCentre (s v : ℤ) : ℝ := (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2)

/-! ## Class parameters (the V07 API decision, design doc §2) -/

/-- One record for all adapted classes.
* `J`: grid ratio `2^J` (time intervals have lengths `2^{J j}`); DPLMV `J > 10`;
* `N`: spatial decay order of the cutoffs `ψ ∈ Ψ_I`, `χ ∈ X_I`;
* `D`: number of controlled derivatives of the multipliers `m ∈ M_ω`;
* `δ`: Fourier support radius of the cutoffs, in units of `1/|I|`;
* `β`: support dilation of the multipliers (`supp m ⊆ β ω`);
* `C`: amplitude constant (and `1/C` is the lower constant of `X_I`). -/
structure Params where
  J : ℕ
  N : ℕ
  D : ℕ
  δ : ℝ
  β : ℝ
  C : ℝ

/-- Floor for decay and derivative orders.  Node workers may RAISE this numeral if a proof needs
more (V05 produces every finite order, so raising it changes no consumer). -/
def classFloor : ℕ := 400

/-- Lemmas in `ClassLemmas` use only that the floor is at least `400` (raising `classFloor` is harmless). -/
theorem classFloor_ge : 400 ≤ classFloor := le_rfl

/-- Floor for the grid ratio `J` (DPLMV: `J > 10`; raise if a node needs a larger `J`: V05 produces
every large `J`). -/
def jFloor : ℕ := 16

/-- The loss of decay and derivative order in the localization `S ↦ S(p_W ·)` (`p_W` of degree 100). -/
def locLoss : ℕ := 100

/-- The admissible range (DPLMV Remark L443-452 made explicit). `β ≤ 11/4` (finding X2-I8 of `docs/audits/X2-V06-V05-check.md` gave `β ≤ 3`; the V13 route check X2-I10 and the V10 worker need a STRICT margin: `β + 2δ < 3`, split threshold 13/4): `k`-lacunarity is `3ω`-disjointness, so
multipliers supported in `βω` with `β > 3` are not uniformly bounded on lacunary trees (B5 and the tree-operator bounds of V10/V11
would be false). -/
def Params.Admissible (𝔭 : Params) : Prop :=
  jFloor ≤ 𝔭.J ∧ classFloor ≤ 𝔭.N ∧ classFloor ≤ 𝔭.D ∧ 0 < 𝔭.δ ∧
    𝔭.δ ≤ (2 : ℝ) ^ (-(3 * (𝔭.J : ℝ) / 2)) ∧ 1 ≤ 𝔭.β ∧ 𝔭.β ≤ 11 / 4 ∧ 1 ≤ 𝔭.C

/-- The localized class (B6' of the V16 route check, redone with a POLYNOMIAL weight, design doc §2):
decay and derivative orders drop by `locLoss`; `J, δ, β, C` are unchanged. -/
def Params.loc (𝔭 : Params) : Params :=
  { 𝔭 with N := 𝔭.N - locLoss, D := 𝔭.D - locLoss }

@[simp] theorem Params.loc_J (𝔭 : Params) : 𝔭.loc.J = 𝔭.J := by cases 𝔭; rfl
@[simp] theorem Params.loc_N (𝔭 : Params) : 𝔭.loc.N = 𝔭.N - locLoss := by cases 𝔭; rfl
@[simp] theorem Params.loc_D (𝔭 : Params) : 𝔭.loc.D = 𝔭.D - locLoss := by cases 𝔭; rfl
@[simp] theorem Params.loc_δ (𝔭 : Params) : 𝔭.loc.δ = 𝔭.δ := by cases 𝔭; rfl
@[simp] theorem Params.loc_β (𝔭 : Params) : 𝔭.loc.β = 𝔭.β := by cases 𝔭; rfl
@[simp] theorem Params.loc_C (𝔭 : Params) : 𝔭.loc.C = 𝔭.C := by cases 𝔭; rfl

/-- The energy class of the tree lemma V15 (R4 of the V13 route check): the decay order of the model data is divided by
`8`, because the losses of the projection construction are multiplicative. -/
def Params.tree (𝔭 : Params) : Params :=
  { 𝔭 with N := 𝔭.N / 8 }

@[simp] theorem Params.tree_J (𝔭 : Params) : 𝔭.tree.J = 𝔭.J := by cases 𝔭; rfl
@[simp] theorem Params.tree_N (𝔭 : Params) : 𝔭.tree.N = 𝔭.N / 8 := by cases 𝔭; rfl
@[simp] theorem Params.tree_D (𝔭 : Params) : 𝔭.tree.D = 𝔭.D := by cases 𝔭; rfl
@[simp] theorem Params.tree_δ (𝔭 : Params) : 𝔭.tree.δ = 𝔭.δ := by cases 𝔭; rfl
@[simp] theorem Params.tree_β (𝔭 : Params) : 𝔭.tree.β = 𝔭.β := by cases 𝔭; rfl
@[simp] theorem Params.tree_C (𝔭 : Params) : 𝔭.tree.C = 𝔭.C := by cases 𝔭; rfl

/-! ## Frequency boxes and tri-tiles -/

/-- A frequency box `Q = ω₁ × ω₂ × ω₃` at scale `s`: `ω_k` has length `2^{-s}` and centre `centre k`. -/
structure Box where
  scale : ℤ
  centre : Fin 3 → ℝ

/-- A tri-tile: a box and a time position; `I_P = dyadicInt P.box.scale P.pos` (length `2^scale`). -/
structure TriTile where
  box : Box
  pos : ℤ

noncomputable instance : DecidableEq Box := Classical.decEq _
noncomputable instance : DecidableEq TriTile := Classical.decEq _

/-- `ω_k`, half-open, centre `centre k`, length `2^{-scale}`. -/
def Box.ω (B : Box) (k : Fin 3) : Set ℝ :=
  Set.Ico (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) (B.centre k + (2 : ℝ) ^ (-B.scale) / 2)

/-- The direction of the singular line in the frozen coordinates `(ξ₁, ξ₂, ξ₁ + ξ₂)`: `m(ξ₂ - ξ₁)` is
singular on `ξ₁ = ξ₂`, i.e. on `t (1, 1, 2)`. -/
def freqDir : Fin 3 → ℝ := ![1, 1, 2]

/-- Dilation factor of the tree hull (REV3, `docs/audits/X2-REV3-fat-top.md`): `Box.hull` is the convex hull of
`hullDil · ω̃_k`.  MTT2's `ω̄_P ⊇ 1000 Q̃`: the top data (`IsTopDatum`) of the top-term energy must have the interval
`[ξ ± 24·2^{-W.1}]` inside the hull of a tile; with `hullDil = 128` this holds for every tile whose slot `k` is
non-lacunary (`ξ_T ∈ (13/4) ω̃_k`) at every lattice scale `W ⊇ I_R` (`fat_icc_subset_hull`, `X2/TopSelect.lean`;
necessary: `hullDil ≥ 123.25`). -/
def hullDil : ℝ := 128

/-- DPLMV's `ω_P` (REV3: convex hull of the `hullDil · ω_k`, was `3 ω_k`) in NORMALIZED coordinates: `ω_k` is divided by
`freqDir k`, so that for a box near the singular line the three normalized intervals sit near one common point `ξ`
(DPLMV and MTT2 normalize the degenerate direction; with raw coordinates the slot-3 interval sits near `2ξ` and the hull
would be meaningless). -/
def Box.hull (B : Box) : Set ℝ :=
  Set.Icc (min (min ((B.centre 0 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0)
      ((B.centre 1 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 1))
      ((B.centre 2 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 2))
    (max (max ((B.centre 0 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0)
      ((B.centre 1 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 1))
      ((B.centre 2 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 2))

/-- The time interval `I_P`. -/
def TriTile.I (P : TriTile) : Set ℝ := dyadicInt P.box.scale P.pos

/-! ## The adapted classes (DPLMV L402-452) -/

/-- `Ψ_I(𝔭)`, `I = dyadicInt s v`: continuous, `|ψ x| ≤ C ⟨(x - c_I)/|I|⟩^{-N}`,
`𝓕 ψ = 0` outside `[-δ/|I|, δ/|I|]`. -/
def InPsi (𝔭 : Params) (s v : ℤ) (ψ : ℝ → ℂ) : Prop :=
  Continuous ψ ∧
    (∀ x, ‖ψ x‖ ≤ 𝔭.C * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) ∧
    ∀ ξ, 𝔭.δ * (2 : ℝ) ^ (-s) < |ξ| → 𝓕 ψ ξ = 0

/-- `X_I(𝔭)`: real-valued, in `Ψ_I(𝔭)`, and bounded below by `C⁻¹ ⟨(x - c_I)/|I|⟩^{-N}`. -/
def InX (𝔭 : Params) (s v : ℤ) (χ : ℝ → ℝ) : Prop :=
  InPsi 𝔭 s v (fun x => (χ x : ℂ)) ∧
    ∀ x, 𝔭.C⁻¹ * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) ≤ χ x

/-- `M_ω(𝔭)` for `ω` of length `2^{-s}` and centre `c`: smooth, `m = 0` outside `β ω`, and
`ℓ(ω)^a |m^{(a)}| ≤ C` for `a ≤ D`. -/
def InMult (𝔭 : Params) (s : ℤ) (c : ℝ) (m : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ m ∧ (∀ ξ, 𝔭.β * (2 : ℝ) ^ (-s) / 2 < |ξ - c| → m ξ = 0) ∧
    ∀ a : ℕ, a ≤ 𝔭.D → ∀ ξ, ((2 : ℝ) ^ (-s)) ^ a * ‖iteratedDeriv a m ξ‖ ≤ 𝔭.C

/-! ## Operators on `ℝ → (ZMod P → ℂ)` -/

section Operators

variable {P : ℕ}

/-- The Fourier multiplier `T_m ⊗ Id` on vector functions, as convolution with `𝓕⁻ m` (meaningful for
`m` smooth compactly supported and `F` locally integrable of at most polynomial growth). -/
def tmult (m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x y => ∫ z, 𝓕⁻ m (x - z) * F z y

/-- The tree operator `T_Tr F = Σ_{P ∈ Tr} ψ_P · T_{m_P} F` (one slot). -/
def treeOp (Tr : Finset TriTile) (ψ m : TriTile → ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x => ∑ Q ∈ Tr, ψ Q x • tmult (m Q) F x

/-- Tree-operator data of slot `k` in the class `𝔭`, with the consistency condition (e:conscond). -/
def IsTreeOpData (𝔭 : Params) (k : Fin 3) (Tr : Finset TriTile) (ψ m : TriTile → ℝ → ℂ) : Prop :=
  (∀ Q ∈ Tr, InPsi 𝔭 Q.box.scale Q.pos (ψ Q) ∧ InMult 𝔭 Q.box.scale (Q.box.centre k) (m Q)) ∧
    ∀ Q ∈ Tr, ∀ Q' ∈ Tr, Q.box = Q'.box → m Q = m Q'

/-- The smoothing profile `η` of the tile cutoffs (R3 of the V13 route check, MTT2's exact form): continuous, nonnegative,
`∫ η = 1`, two-sided polynomial decay of order `N`, `𝓕 η` supported in `[-δ, δ]`. -/
def IsEtaCut (𝔭 : Params) (η : ℝ → ℝ) : Prop :=
  Continuous η ∧ (∀ x, 0 ≤ η x) ∧ ∫ x, η x = 1 ∧ (∀ x, η x ≤ 𝔭.C * jb x ^ (-(𝔭.N : ℝ))) ∧
    (∀ x, 𝔭.C⁻¹ * jb x ^ (-(𝔭.N : ℝ)) ≤ η x) ∧ ∀ ξ, 𝔭.δ < |ξ| → 𝓕 (fun x => (η x : ℂ)) ξ = 0

/-- The tile cutoff `χ_P = 1_{I_P} * η_s`, `η_s x = 2^{-s} η (x / 2^s)`, for the tile with time interval
`dyadicInt s v` (MTT2's exact form; the tree lemma needs it, finding X2-I11). -/
def tileCutoff (η : ℝ → ℝ) (s v : ℤ) (x : ℝ) : ℝ :=
  ∫ y in dyadicInt s v, (2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s)

/-- Model data of the form: cutoffs `χ P ∈ X_{I_P}(𝔭)`, multipliers `m P k ∈ M_{ω_{P_k}}(𝔭)`,
consistency (e:conscond), and (R3, finding X2-I11 of `docs/audits/X2-V13-route-check.md`) the cutoffs have MTT2's exact form
`χ_P = 1_{I_P} * η_s` for one profile `η`. -/
def IsModelData (𝔭 : Params) (Ps : Finset TriTile) (χ : TriTile → ℝ → ℝ)
    (m : TriTile → Fin 3 → ℝ → ℂ) : Prop :=
  (∀ Q ∈ Ps, InX 𝔭 Q.box.scale Q.pos (χ Q) ∧
      ∀ k, InMult 𝔭 Q.box.scale (Q.box.centre k) (m Q k)) ∧
    (∀ Q ∈ Ps, ∀ Q' ∈ Ps, Q.box = Q'.box → m Q = m Q') ∧
    ∃ η : ℝ → ℝ, IsEtaCut 𝔭 η ∧ ∀ Q ∈ Ps, χ Q = tileCutoff η Q.box.scale Q.pos

/-- The type of the frozen forms `Π` (linear, linear, conjugate-linear). -/
abbrev Form (P : ℕ) : Type :=
  (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ

/-- The frozen bound on `Π` (`‖Π(F,G,H)‖ ≤ CT ‖F‖₂ ‖G‖₂ ‖H‖_u`). -/
def FormBound [NeZero P] (u : ℝ) (T : Form P) (CT : ℝ) : Prop :=
  ∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H

/-- **The model form** `Λ_Ps^Π(F₁,F₂,F₃) = Σ_{P∈Ps} ∫ χ_P(x) Π(T_{m_{P,1}}F₁(x), T_{m_{P,2}}F₂(x), T_{m_{P,3}}F₃(x)) dx`
(x-space form of the frozen `multiplierForm`: slot 3 is conjugate-linear, frequencies `ω₃ ≈ ω₁ + ω₂`). -/
def modelForm (T : Form P) (Ps : Finset TriTile) (χ : TriTile → ℝ → ℝ)
    (m : TriTile → Fin 3 → ℝ → ℂ) (F₁ F₂ F₃ : ℝ → ZMod P → ℂ) : ℂ :=
  ∑ Q ∈ Ps, ∫ x, (χ Q x : ℂ) *
    T (tmult (m Q 0) F₁ x) (tmult (m Q 1) F₂ x) (tmult (m Q 2) F₃ x)

end Operators

/-- The localizing polynomial `p_W(x) = 1 + ((x - c_W)/|W|)^100` of a dyadic key `W` (degree `locLoss`).
`p_W ≥ 1` and `p_W ≥ 2^{-100} ⟨(x - c_W)/|W|⟩^{100}`. -/
def locPoly (W : ℤ × ℤ) (x : ℝ) : ℝ := 1 + ((x - dyCentre W.1 W.2) / (2 : ℝ) ^ W.1) ^ locLoss

end PrimeBHT.TimeFrequency.X2
