module

public import PrimeBHT.TimeFrequency.X2.EnergyTop
public import PrimeBHT.TimeFrequency.X2.Ortho.Geometry
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeScalar
public import PrimeBHT.TimeFrequency.X2.GoodTree

/-!
# X2, node V12: definitions (strong disjointness in nested form, `PintStatement`, B5 consequence)

* `IsStronglyDisjointN`: the HLC / MTT form of `k`-strong disjointness (`ω_P ⊊ ω_{P'}` NESTED, not `10`-close),
  with the tile sets of the trees pairwise disjoint as a separate conjunct.  This is the form a greedy selection
  can produce.  The built `IsStronglyDisjoint` (`≤` of scales, `10`-closeness, both clauses for equal scales) cannot
  be produced by a selection (see `EnergyLemma.lean`, module docstring).
* `PintStatement`: the corrected V11 (`pint`) for `IsStronglyDisjointN` families, general `(s, qX)`.
* `EngBoundStatement`: the consequence `eng ≲ ‖F‖_∞` of B5 used by the energy lemma.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **`k`-strong disjointness, nested form** (HLC `eq:disjProp`, MTT Lemma 7.7).  Each tree is a `k`-lacunary
tree with its top; tile sets are pairwise disjoint; if `R ∈ T` has a frequency interval strictly containing the
one of `R' ∈ T'` (distinct boxes), then `I_R` is disjoint from the top of `T'`. -/
def IsStronglyDisjointN (k : Fin 3) (𝒯 : List (Finset TriTile × Top)) : Prop :=
  (∀ T ∈ 𝒯, IsTree T.1 T.2 ∧ IsLacunary k T.1) ∧
    𝒯.Pairwise (fun T T' =>
      Disjoint T.1 T'.1 ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R'.box.ω k ⊆ R.box.ω k →
          Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2)) ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R.box.ω k ⊆ R'.box.ω k →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2)))

/-- **LEGACY / FALSE for `E ∋ (2,2)` (nested form; do not build on it): the nested predicate `IsStronglyDisjointN` admits
shell chains, which give counterexamples to this `pint` (hand argument, `Ortho/Nested.lean`, `Ortho/PintNested.lean`:
`PintStatementFor HilbertExp` is false).  The true form is `PintStatementOFor` (`Ortho/PintNested.lean`, for
`IsStronglyDisjointO`); `PintStatementOFor HilbertExp` is PROVED (`pint_two_O_statement`).**
**V11 (`pint`), corrected**, for the exponent pairs `(s, qX)` with `E s qX`: for `k`-strongly disjoint (nested form)
families of `k`-lacunary trees of boxes of a rank-1 box set,
`∑_T |I_T| topNorm(F;T;qX)^{qX} ≤ C (‖F‖_{qX}^{qX} + (B^{qX} ∑_T|I_T|)^{1-α} ‖F‖_{qX}^{α qX})`, `B ≥ ‖F‖_∞`, `0 < α < 1`.
The class margin is the one of the built `pint_two` (`𝔭.decN 10`). -/
def PintStatementFor (E : ℝ → ℝ → Prop) : Prop :=
  ∀ (𝔭 : Params), (𝔭.decN 10).Admissible → ∀ {s qX α : ℝ}, E s qX → 0 < α → α < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (k : Fin 3) (𝒯 : List (Finset TriTile × Top)), IsStronglyDisjointN k 𝒯 →
        (∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
          (∀ x, yNorm s (F x) ≤ B) →
            (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * topNorm 𝔭 s k F T.1 T.2 qX ^ qX)).sum ≤
              ENNReal.ofReal C * (mixedPow qX s F +
                (ENNReal.ofReal (B ^ qX) * topSum 𝒯) ^ (1 - α) * mixedPow qX s F ^ α)

/-- The Hilbert endpoint `(s, qX) = (2, 2)` (V10). -/
def HilbertExp (s qX : ℝ) : Prop := s = 2 ∧ qX = 2

/-- The consequence `eng ≲ ‖F‖_∞` of B5 (`EngLeTailMassStatement`: `λ_M(‖F‖; I) ≤ C` for `‖F‖ ≤ 1`). -/
def EngBoundStatementFor (E : ℝ → ℝ → Prop) : Prop :=
  ∀ (𝔭 : Params), 𝔭.Admissible → ∀ {s qX : ℝ}, E s qX →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (Cs : Finset TriTile), (∀ R ∈ Cs, R.box ∈ Qs) → ∀ (k : Fin 3) (F : ℝ → ZMod P → ℂ),
        Measurable F → (∀ x, yNorm s (F x) ≤ 1) → eng 𝔭 s k F Cs qX ≤ ENNReal.ofReal C

def EngBoundStatement : Prop := EngBoundStatementFor IsEnergyExponent

/-- **V12, repaired margin**: identical to `EnergyLemmaStatement`, except that the class hypothesis is
`(𝔭.loc.decN 10).Admissible` instead of `𝔭.loc.Admissible` (the localized count applies `pint` in the class `𝔭.loc`,
whose proof (`pint_two`) costs `10` orders of decay); for the exponent pairs `E`. -/
def EnergyLemmaStatementFor (E : ℝ → ℝ → Prop) : Prop :=
  ∀ (𝔭 : Params), (𝔭.loc.decN 10).Admissible → ∀ {s qX q : ℝ}, E s qX → qX < q →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (Cs₀ Cs : Finset TriTile), (∀ R ∈ Cs₀, R.box ∈ Qs) → HasTC Cs₀ → IsResidual Cs₀ Cs →
        ∀ (k : Fin 3) (F : ℝ → ZMod P → ℂ), Measurable F → (∀ x, yNorm s (F x) ≤ 1) →
          ∃ ts : List Top,
            eng 𝔭 s k F (removeTrees Cs ts) qX ≤ eng 𝔭 s k F Cs qX / 2 ∧
            topSum (removedTrees Cs ts) * eng 𝔭 s k F Cs qX ^ q ≤
              ENNReal.ofReal C * mixedPow qX s F ∧
            ∀ W : ℤ × ℤ, (∀ R ∈ Cs, R.I ⊆ dyadicInt W.1 W.2) →
              topSum (removedTrees Cs ts) * eng 𝔭 s k F Cs qX ^ q ≤
                ENNReal.ofReal C * mixedPow qX s (fun x => ((locPoly W x)⁻¹ : ℂ) • F x)

def EnergyLemmaStatementR : Prop := EnergyLemmaStatementFor IsEnergyExponent

/-- Restriction to a smaller set of exponents. -/
theorem PintStatementFor.mono {E E' : ℝ → ℝ → Prop} (h : ∀ s qX, E' s qX → E s qX)
    (hp : PintStatementFor E) : PintStatementFor E' :=
  fun 𝔭 h𝔭 _ _ _ hX hα0 hα1 => hp 𝔭 h𝔭 (h _ _ hX) hα0 hα1

theorem EngBoundStatementFor.mono {E E' : ℝ → ℝ → Prop} (h : ∀ s qX, E' s qX → E s qX)
    (hp : EngBoundStatementFor E) : EngBoundStatementFor E' :=
  fun 𝔭 h𝔭 _ _ hX => hp 𝔭 h𝔭 (h _ _ hX)

theorem EnergyLemmaStatementFor.mono {E E' : ℝ → ℝ → Prop} (h : ∀ s qX, E' s qX → E s qX)
    (hp : EnergyLemmaStatementFor E) : EnergyLemmaStatementFor E' :=
  fun 𝔭 h𝔭 _ _ _ hX hq => hp 𝔭 h𝔭 (h _ _ hX) hq

/-! ## Margins -/

theorem Params.Admissible.of_loc_decN {𝔭 : Params} (h : (𝔭.loc.decN 10).Admissible) :
    𝔭.loc.Admissible ∧ (𝔭.decN 10).Admissible ∧ 𝔭.Admissible ∧ (𝔭.loc.decN 10).Admissible := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have h2' : 400 ≤ 𝔭.N - 100 - 10 := h2
  have h3' : 400 ≤ 𝔭.D - 100 := h3
  refine ⟨⟨h1, ?_, ?_, h4, h5, h6, h7, h8⟩, ⟨h1, ?_, ?_, h4, h5, h6, h7, h8⟩,
    ⟨h1, ?_, ?_, h4, h5, h6, h7, h8⟩, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩ <;>
    simp only [Params.decN, Params.loc, locLoss, classFloor] <;> omega

end PrimeBHT.TimeFrequency.X2
