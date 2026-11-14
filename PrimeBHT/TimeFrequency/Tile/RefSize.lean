module

public import PrimeBHT.TimeFrequency.Tile.Energy
public import PrimeBHT.TimeFrequency.Tile.Maximal
public import PrimeBHT.TimeFrequency.Tile.Lacunary
public import PrimeBHT.TimeFrequency.Tile.Trees
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqInt
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.TriValid
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Node C9 of the X1 blueprint: the exceptional set and the sizes outside it (`TT.refsize`)

Setting (slots `0, 1, 2` are the source's slots `1, 2, 3`): measurable `E : Fin 3 → Set ℝ` with
`0 < |E 0| ≤ |E 1| ≤ |E 2|`, `1/2 < |E 2| ≤ 1`, measurable `h k` with `‖h k‖ ≤ 1_{E k}`, and the
normalizations (`refG`)
`g 0 = |E 0|⁻¹ h 0` (`L¹`), `g 1 = |E 1|^{-1/2} h 1`, `g 2 = |E 2|^{-1/2} h 2` (`L²`),
and the `L²`-normalized `refG'` (`g' k = |E k|^{-1/2} h k`, so `g' 0 = |E 0|^{1/2} g 0`, `g' k = g k` else).

* (i) `isOpen_refExceptional`, `volume_refExceptional_lt`: `F := {M 1_{E 0} > 100 |E 0|} ∪
  {M 1_{E 1} > 100 |E 1|}` is open and `|F| < 1/12`.
* (ii) `size_refG_le`: for finite `P' ⊆ triIdx s' α` with `I_t ⊄ F` for all `t ∈ P'`, all packets adapted
  with exponent `N` (`4 ≤ N`, `N₀ ≤ N`), all `i, k`: `size_{i,k}(g_k, P') ≤ C`, with the explicit
  constant `refSizeConst (CO N) (B N) = 2250 + 10 CO(N) + 100 √(energyConst (B N))`.
  Conditional on two hypotheses, stated as local Props: `SizeOffMax CO N₀` (C8(b) for `i ≠ k`, the
  tile-wise maximal-function form) and `TreeBessel B N₀` (C8(a), the Bessel inequality of an `i`-tree for the
  packets of slot `k ≠ i`, consumed by C7 for the `L¹`-normalized slot). Their constants `CO N`, `B N` are
  allowed to depend on the packet exponent `N` (as C8's `orthSizeConst N`, `sameScaleConst N` do); `C₀ = 100`
  is absolute, and for a fixed `N` the constant `C` is absolute. The diagonal part of C8(b)
  (`size_{k,k}`) is proved here from (M5) (`sizeDiag_le_of_exists_maximalHLR_le`).
  Discharging them with C8 (`Tile/Orth.lean`, once built): `TreeBessel sameScaleConst 3` is
  `fun a b s' α hν N hN φ P' hP' hφ i k hik T hT g hg =>
    sum_norm_sq_pairing_tree_le hN hν hik φ hP' hT (fun t ht => hφ t (hT.subset ht) k) hg`,
  and `SizeOffMax orthSizeConst 3` is `sizeOff_le_of_maximalHLR_sq_le` (via `size_of_ne`).
* (ii') `size_refG'_zero_le`: `size_{i,0}(g'_0, P') ≤ C |E 0|^{1/2}`; for `k ≠ 0` `refG' = refG`.

Normalization bookkeeping (where an `ε` could be lost): `A = |E 0|⁻¹`, `λ = C₀ |E 0|`, `A² λ² = C₀²` in C7
(done inside `sum_norm_sq_pairing_normalized_le_of_bessel`); `|g 1| ≤ |E 1|^{-1/2}`, `M(|g 1|²) ≤ |E 1|⁻¹ M 1_{E 1}
≤ C₀` (uses `M 1_E ≤ C₀ |E|` off the exceptional set), `M|g 1| ≤ C₀ |E 1|^{1/2} ≤ C₀` (uses `|E 1| ≤ 1`),
`|g 2| ≤ |E 2|^{-1/2} < √2 ≤ 3/2` (uses `|E 2| > 1/2`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.Statements
open PrimeCarleson.Proof.Common (maximalHLR)
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Definitions: the constant `C₀`, the exceptional set `F`, the normalizations `g_k` -/

/-- The absolute constant `C₀ = 100 = 25 C_w` of C9 (`C_w = 4` the weak-`(1,1)` constant of C6). -/
def refC0 : ℝ := 100

theorem refC0_pos : 0 < refC0 := by norm_num [refC0]

/-- The exceptional set `F = {M 1_{E₁} > C₀ |E₁|} ∪ {M 1_{E₂} > C₀ |E₂|}` of C9, with `C₀ = 100`. -/
def refExceptional (E₁ E₂ : Set ℝ) : Set ℝ :=
  exceptionalSet E₁ refC0 ∪ exceptionalSet E₂ refC0

/-- The scalars of the normalizations of C9: `|E₁|⁻¹` (`L¹`) and `|E₂|^{-1/2}`, `|E₃|^{-1/2}` (`L²`). -/
def refScale (E : Fin 3 → Set ℝ) : Fin 3 → ℝ :=
  ![((volume (E 0)).toReal)⁻¹, (volume (E 1)).toReal ^ (-(1 : ℝ) / 2),
    (volume (E 2)).toReal ^ (-(1 : ℝ) / 2)]

/-- The scalars of the `L²`-normalized functions `g'_k = |E_k|^{-1/2} h_k`. -/
def refScale' (E : Fin 3 → Set ℝ) (k : Fin 3) : ℝ := (volume (E k)).toReal ^ (-(1 : ℝ) / 2)

/-- The `L²`-normalized functions `g'_k = |E_k|^{-1/2} h_k` (C10: `g'_1 = |E_1|^{1/2} g_1`, `g'_2 = g_2`,
`g'_3 = g_3`). -/
def refG' (E : Fin 3 → Set ℝ) (h : Fin 3 → ℝ → ℂ) (k : Fin 3) : ℝ → ℂ :=
  fun x => ((refScale' E k : ℝ) : ℂ) * h k x

theorem refScale_two (E : Fin 3 → Set ℝ) : refScale E 2 = (volume (E 2)).toReal ^ (-(1 : ℝ) / 2) :=
  rfl

theorem refScale_nonneg (E : Fin 3 → Set ℝ) (k : Fin 3) : 0 ≤ refScale E k := by
  fin_cases k
  · exact inv_nonneg.2 ENNReal.toReal_nonneg
  · exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  · exact Real.rpow_nonneg ENNReal.toReal_nonneg _

theorem refScale'_nonneg (E : Fin 3 → Set ℝ) (k : Fin 3) : 0 ≤ refScale' E k :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-! ### Part (i): the exceptional set is open and small -/

/-- **C9 (i)**: `|F| < 1/12` (`|F| ≤ 8/C₀ = 2/25`). -/
theorem volume_refExceptional_lt {E₁ E₂ : Set ℝ} (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (h₁ : volume E₁ ≠ 0) (h₂ : volume E₂ ≠ 0) (t₁ : volume E₁ ≠ ⊤) (t₂ : volume E₂ ≠ ⊤) :
    volume (refExceptional E₁ E₂) < ENNReal.ofReal (1 / 12) :=
  volume_exceptionalSet_union_lt_one_twelfth hE₁ hE₂ h₁ h₂ t₁ t₂ (by norm_num [refC0])

/-- The nondegeneracy facts from the normalization `0 < |E 0| ≤ |E 1| ≤ |E 2|`, `1/2 < |E 2|`. -/
theorem volume_ne_zero_ne_top_of_normalized {E : Fin 3 → Set ℝ}
    (h01 : volume (E 0) ≤ volume (E 1)) (h12 : volume (E 1) ≤ volume (E 2))
    (hE0 : volume (E 0) ≠ 0) (hhalf : 1 / 2 < (volume (E 2)).toReal) :
    (∀ k, volume (E k) ≠ 0) ∧ ∀ k, volume (E k) ≠ ⊤ := by
  have h2top : volume (E 2) ≠ ⊤ :=
    (ENNReal.toReal_pos_iff.1 (lt_trans (by norm_num) hhalf)).2.ne
  have h1top : volume (E 1) ≠ ⊤ := ne_top_of_le_ne_top h2top h12
  have h0top : volume (E 0) ≠ ⊤ := ne_top_of_le_ne_top h1top h01
  have h1 : volume (E 1) ≠ 0 := fun h => hE0 (le_antisymm (h ▸ h01) bot_le)
  have h2 : volume (E 2) ≠ 0 := fun h => h1 (le_antisymm (h ▸ h12) bot_le)
  constructor
  · intro k; fin_cases k
    · exact hE0
    · exact h1
    · exact h2
  · intro k; fin_cases k
    · exact h0top
    · exact h1top
    · exact h2top

/-! ### Maximal-function bounds for the `g_k` off the exceptional set -/

section Maximal

/-- `‖c h x‖ ≤ c 1_E x` for `c ≥ 0` and `‖h‖ ≤ 1_E`. -/
theorem norm_ofReal_mul_le_indicator {c : ℝ} (hc : 0 ≤ c) {E : Set ℝ} {h : ℝ → ℂ}
    (hdom : ∀ x, ‖h x‖ ≤ E.indicator (1 : ℝ → ℝ) x) (x : ℝ) :
    ‖((c : ℝ) : ℂ) * h x‖ ≤ c * E.indicator (1 : ℝ → ℝ) x := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  gcongr
  exact hdom x

/-- `|E_3|^{-1/2} ≤ 3/2` for `1/2 < |E_3|` (`|E_3|^{-1/2} < √2`). -/
theorem refScale_two_le {E : Fin 3 → Set ℝ} (hhalf : 1 / 2 < (volume (E 2)).toReal) :
    refScale E 2 ≤ 3 / 2 := by
  have hpos : 0 < (volume (E 2)).toReal := lt_trans (by norm_num) hhalf
  have hsq : (refScale E 2) ^ 2 = ((volume (E 2)).toReal)⁻¹ := by
    rw [refScale_two, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num [Real.rpow_neg_one]
  have h2 : ((volume (E 2)).toReal)⁻¹ < 2 := by
    rw [inv_lt_comm₀ hpos (by norm_num)]
    linarith
  have h0 : 0 ≤ refScale E 2 := refScale_nonneg E 2
  by_contra hcon
  have hcon' := not_le.1 hcon
  nlinarith

end Maximal

/-! ### The diagonal sizes from (M5) -/

/-- **C8(b), `i = k`** (from (M5), `K = 1`, `R = 1/2`): if for each `t ∈ P'` there is `x_t ∈ I_t` with
`M f (x_t) ≤ μ`, then `size_{k,k}(f, P') ≤ (45/2) μ`. -/
theorem sizeDiag_le_of_exists_maximalHLR_le {a b : ℤ} {N : ℕ} (hN : 2 ≤ N)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) (k : Fin 3)
    {f : ℝ → ℂ} (hf : Measurable f) {μ : ℝ} (hμ : 0 ≤ μ)
    (hM : ∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR f x ≤ ENNReal.ofReal μ) :
    sizeDiag φ k f P' ≤ ENNReal.ofReal (45 / 2 * μ) := by
  refine sizeDiag_le fun t ht => ?_
  obtain ⟨x, hx, hMx⟩ := hM t ht
  have hI : (timeInt t).OrdConnected := by
    unfold timeInt
    infer_instance
  exact ENNReal.ofReal_le_ofReal (norm_pairing_le_of_maximalHLR_le_of_mem hN (hφ t ht k) hI
    (toReal_volume_timeInt_pos t) hf hx hμ hMx)

/-! ### Homogeneity of the sizes -/

private theorem pairing_const_mul' (c : ℂ) (f φ : ℝ → ℂ) :
    pairing (fun x => c * f x) φ = c * pairing f φ := by
  unfold pairing
  simp_rw [mul_assoc]
  exact integral_const_mul c _

section ConstMul

variable {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P : Finset (ℤ × ℤ × ℤ)}

theorem sizeDiag_const_mul_le {c : ℝ} (hc : 0 ≤ c) (k : Fin 3) (f : ℝ → ℂ) :
    sizeDiag φ k (fun x => ((c : ℝ) : ℂ) * f x) P ≤ ENNReal.ofReal c * sizeDiag φ k f P := by
  refine sizeDiag_le fun t ht => ?_
  have h1 := le_sizeDiag (φ := φ) (k := k) (f := f) ht
  rw [pairing_const_mul', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
    ← mul_assoc, mul_comm _ c, mul_assoc, ENNReal.ofReal_mul hc]
  exact mul_le_mul' le_rfl h1

theorem treeEnergy_const_mul {c : ℝ} (k : Fin 3) (f : ℝ → ℂ) (T : TreeData) :
    treeEnergy φ k (fun x => ((c : ℝ) : ℂ) * f x) T = c ^ 2 * treeEnergy φ k f T := by
  unfold treeEnergy
  simp only [pairing_const_mul', norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum]
  ring

theorem sizeOff_const_mul_le {c : ℝ} (hc : 0 ≤ c) (i k : Fin 3) (f : ℝ → ℂ) :
    sizeOff a b φ i k (fun x => ((c : ℝ) : ℂ) * f x) P ≤
      ENNReal.ofReal c * sizeOff a b φ i k f P := by
  refine sizeOff_le fun T hT => ?_
  have h1 := le_sizeOff (φ := φ) (k := k) (f := f) hT
  rw [treeEnergy_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, ENNReal.ofReal_mul hc]
  exact mul_le_mul' le_rfl h1

/-- **Homogeneity**: `size_{i,k}(c f, P) ≤ c · size_{i,k}(f, P)` for `c ≥ 0`. -/
theorem size_const_mul_le {c : ℝ} (hc : 0 ≤ c) (i k : Fin 3) (f : ℝ → ℂ) :
    size a b φ i k (fun x => ((c : ℝ) : ℂ) * f x) P ≤ ENNReal.ofReal c * size a b φ i k f P := by
  unfold size
  split_ifs
  · exact sizeDiag_const_mul_le hc k f
  · exact sizeOff_const_mul_le hc i k f

end ConstMul

/-! ### The two inputs from C8, as hypotheses -/

/-- **C8(b), `i ≠ k` part**, tile-wise form (hypothesis, proved by the C8 worker): for adapted packets
(exponent `N ≥ N₀`) of a finite `P' ⊆ Idx_ν`, `i ≠ k`, and a measurable `f`: if every `t ∈ P'` has a point
`x_t ∈ I_t` with `M(‖f‖²)(x_t) ≤ μ²` (that is, `M² f (x_t) ≤ μ`), then `size_{i,k}(f, P') ≤ CO(N) μ`. -/
def SizeOffMax (CO : ℕ → ℝ) (N₀ : ℕ) : Prop :=
  ∀ (a b s' α : ℤ), TriValid a b s' α → ∀ (N : ℕ), N₀ ≤ N →
    ∀ (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P' : Finset (ℤ × ℤ × ℤ)),
      (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
      (∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
      ∀ (i k : Fin 3), i ≠ k → ∀ f : ℝ → ℂ, Measurable f → ∀ μ : ℝ, 0 ≤ μ →
        (∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR (fun y => ‖f y‖ₑ ^ 2) x ≤ ENNReal.ofReal (μ ^ 2)) →
        size a b φ i k f P' ≤ ENNReal.ofReal (CO N * μ)

/-- **C8(a), the Bessel inequality of a tree** (hypothesis, proved by the C8 worker; the input of C7):
for an `i`-tree `T ⊆ P'` of tiles of `Idx_ν` with adapted packets (exponent `N ≥ N₀`) and `k ≠ i`,
`∑_{t ∈ T} |⟨g, φ_{t,k}⟩|² ≤ B(N) ‖g‖₂²` for all `g ∈ L²`. -/
def TreeBessel (B : ℕ → ℝ) (N₀ : ℕ) : Prop :=
  ∀ (a b s' α : ℤ), TriValid a b s' α → ∀ (N : ℕ), N₀ ≤ N →
    ∀ (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P' : Finset (ℤ × ℤ × ℤ)),
      (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
      (∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
      ∀ (i k : Fin 3), i ≠ k → ∀ T : TreeData, IsTree a b i P' T →
        ∀ g : ℝ → ℂ, MemLp g 2 volume →
          ∑ t ∈ T.tiles, ‖pairing g (φ t k)‖ ^ 2 ≤ B N * ∫ x, ‖g x‖ ^ 2

/-! ### `k = 1` (the `L¹`-normalized slot), `i ≠ k`: C7 -/

/-! ### Part (ii): the sizes outside the exceptional set -/

/-- The explicit constant of C9 (ii): `2250 + 10 CO + 100 √(energyConst B)` (`CO` the constant of
`SizeOffMax`, `B` the constant of `TreeBessel`, both at the exponent `N` of the packets; `2250 = (45/2) C₀` from (M5), `10 = √C₀`, `100 = C₀`). -/
def refSizeConst (CO B : ℝ) : ℝ := 2250 + 10 * CO + 100 * Real.sqrt (energyConst B)

/-! ### The `L²`-normalized forms (input of C10a, step 1) -/

end PrimeBHT.TimeFrequency.Tile
