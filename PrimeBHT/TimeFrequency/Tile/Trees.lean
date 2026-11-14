module

public import PrimeBHT.TimeFrequency.Tile.Grid
public import PrimeBHT.Frozen.Pairing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Trees and sizes (blueprint node C0, item 3, unshifted)

An `i`-tree is data `T = (P_T, I_T, ξ_T)` (`TreeData`): a finite set of tiles, a dyadic top interval
`I_T = 2^s[v, v + 1)` given by `(s, v)`, and a real `ξ_T`. The predicate `IsTree a b i P T` says
`P_T ⊆ P`, and for all `t ∈ P_T`: `ξ_T ∈ 3ω_{t,i}` and `I_t ⊆ I_T`. Nothing is bundled.

The sizes of a finite family `P` and a function `f` (with packets `φ t k`), in `ℝ≥0∞`:

* `sizeOff a b φ i k f P = sup_{T ⊆ P, T an i-tree} ((1/|I_T|) Σ_{t ∈ T} |⟨f, φ_{t,k}⟩|²)^{1/2}` (`i ≠ k`),
* `sizeDiag φ k f P = sup_{t ∈ P} |I_t|^{-1/2} |⟨f, φ_{t,k}⟩|` (`size_{k,k}`),
* `size a b φ i k f P` is `sizeOff` if `i ≠ k` and `sizeDiag` if `i = k`.

A single tile is an `i`-tree for every `i` with `I_T = I_t`, hence `size_{k,k} ≤ size_{i,k}`
(`sizeDiag_le_sizeOff`). The canonical `ξ_T := L_T` of finding F4 (the maximum of the left endpoints
of the `3ω_{t,i}`, `t ∈ P_T`) is `canonXi`; it lies in `3ω_{t,i}` for all `t` whenever some `ξ` does
(`IsTree.canonical`), and the supremum defining the size may be restricted to canonical trees
(`sizeOff_eq_iSup_canonical`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Tree data -/

/-- The data `(P_T, I_T, ξ_T)` of a tree: tiles, dyadic top `I_T = 2^{top.1}[top.2, top.2 + 1)`, and the
frequency `ξ_T`. -/
structure TreeData where
  /-- The set of tiles `P_T`. -/
  tiles : Finset (ℤ × ℤ × ℤ)
  /-- The top `I_T ∈ 𝒟_0`, as the pair `(s, v)` of `2^s[v, v+1)`. -/
  top : ℤ × ℤ
  /-- The central frequency `ξ_T`. -/
  ξ : ℝ

namespace TreeData

/-- The top interval `I_T`. -/
def topInt (T : TreeData) : Set ℝ := dyadicInt T.top.1 T.top.2

theorem toReal_volume_topInt (T : TreeData) : (volume T.topInt).toReal = (2 : ℝ) ^ T.top.1 :=
  toReal_volume_dyadicInt _ _

theorem toReal_volume_topInt_pos (T : TreeData) : 0 < (volume T.topInt).toReal := by
  rw [toReal_volume_topInt]; exact zpow_pos (by norm_num) _

end TreeData

/-- `T` is an `i`-tree in `P`: `P_T ⊆ P`, and for all `t ∈ P_T`, `ξ_T ∈ 3ω_{t,i}` and `I_t ⊆ I_T`
(unshifted BD26 `e:tree`, blueprint C0 item 3). -/
def IsTree (a b : ℤ) (i : Fin 3) (P : Finset (ℤ × ℤ × ℤ)) (T : TreeData) : Prop :=
  T.tiles ⊆ P ∧ ∀ t ∈ T.tiles, T.ξ ∈ dilate 3 (freqInt a b i t) ∧ timeInt t ⊆ T.topInt

theorem IsTree.subset {a b : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)} {T : TreeData}
    (h : IsTree a b i P T) : T.tiles ⊆ P := h.1

theorem IsTree.xi_mem {a b : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)} {T : TreeData}
    (h : IsTree a b i P T) {t : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles) :
    T.ξ ∈ dilate 3 (freqInt a b i t) := (h.2 t ht).1

theorem IsTree.timeInt_subset {a b : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)} {T : TreeData}
    (h : IsTree a b i P T) {t : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles) : timeInt t ⊆ T.topInt :=
  (h.2 t ht).2

theorem IsTree.mono {a b : ℤ} {i : Fin 3} {P P' : Finset (ℤ × ℤ × ℤ)} {T : TreeData}
    (h : IsTree a b i P T) (hP : P ⊆ P') : IsTree a b i P' T :=
  ⟨h.1.trans hP, h.2⟩

/-- A subset of the tiles of a tree is a tree with the same `(I_T, ξ_T)`. -/
theorem IsTree.restrict {a b : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)} {T : TreeData}
    (h : IsTree a b i P T) {S : Finset (ℤ × ℤ × ℤ)} (hS : S ⊆ T.tiles) :
    IsTree a b i P { T with tiles := S } :=
  ⟨hS.trans h.1, fun t ht => h.2 t (hS ht)⟩

/-- A single tile is an `i`-tree for every `i`, with `I_T = I_t` and `ξ_T` the centre of `ω_{t,i}`. -/
theorem isTree_singleton (a b : ℤ) (i : Fin 3) {P : Finset (ℤ × ℤ × ℤ)} {t : ℤ × ℤ × ℤ}
    (ht : t ∈ P) :
    IsTree a b i P ⟨{t}, (t.1, t.2.1), intervalCentre (freqInt a b i t)⟩ := by
  refine ⟨Finset.singleton_subset_iff.2 ht, ?_⟩
  intro u hu
  rw [Finset.mem_singleton] at hu
  subst hu
  refine ⟨?_, fun x hx => hx⟩
  have hlt := freqCell_lt u.1 (freqNum a b u i)
  have hmem : intervalCentre (freqInt a b i u) ∈ freqInt a b i u := by
    rw [freqInt_eq_freqCell, intervalCentre_freqCell]
    constructor <;> nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (-u.1)]
  exact freqInt_subset_dilate (by norm_num) a b i u hmem

/-! ### Sizes -/

/-- `(1/|I_T|) Σ_{t ∈ T} |⟨f, φ_{t,k}⟩|²`, the square of the quantity whose supremum is `size_{i,k}`. -/
def treeEnergy (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3) (f : ℝ → ℂ) (T : TreeData) : ℝ :=
  (volume T.topInt).toReal⁻¹ * ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2

/-- The `(i, k)`-size for `i ≠ k` (BD26 `size_{i,j,k}`, unshifted):
`sup_{T ⊆ P, T an i-tree} ((1/|I_T|) Σ_{t∈T} |⟨f, φ_{t,k}⟩|²)^{1/2}`, in `ℝ≥0∞`. -/
def sizeOff (a b : ℤ) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (i k : Fin 3) (f : ℝ → ℂ)
    (P : Finset (ℤ × ℤ × ℤ)) : ℝ≥0∞ :=
  ⨆ (T : TreeData) (_ : IsTree a b i P T), ENNReal.ofReal (Real.sqrt (treeEnergy φ k f T))

/-- The diagonal size `size_{k,k}(f, P) = sup_{t ∈ P} |I_t|^{-1/2} |⟨f, φ_{t,k}⟩|`, in `ℝ≥0∞`. -/
def sizeDiag (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3) (f : ℝ → ℂ)
    (P : Finset (ℤ × ℤ × ℤ)) : ℝ≥0∞ :=
  ⨆ t ∈ P, ENNReal.ofReal ((volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ‖pairing f (φ t k)‖)

/-- `size_{i,k}(f, P)`: `sizeOff` for `i ≠ k`, `sizeDiag` for `i = k`. -/
def size (a b : ℤ) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (i k : Fin 3) (f : ℝ → ℂ)
    (P : Finset (ℤ × ℤ × ℤ)) : ℝ≥0∞ :=
  if i = k then sizeDiag φ k f P else sizeOff a b φ i k f P

theorem size_of_ne {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {i k : Fin 3} (h : i ≠ k)
    (f : ℝ → ℂ) (P : Finset (ℤ × ℤ × ℤ)) : size a b φ i k f P = sizeOff a b φ i k f P := by
  simp only [size, h, ↓reduceIte]

theorem size_self (a b : ℤ) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3) (f : ℝ → ℂ)
    (P : Finset (ℤ × ℤ × ℤ)) : size a b φ k k f P = sizeDiag φ k f P := by
  simp only [size, ↓reduceIte]

section SizeApi

variable {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {i k : Fin 3} {f : ℝ → ℂ}
  {P P' : Finset (ℤ × ℤ × ℤ)}

theorem le_sizeOff {T : TreeData} (hT : IsTree a b i P T) :
    ENNReal.ofReal (Real.sqrt (treeEnergy φ k f T)) ≤ sizeOff a b φ i k f P :=
  le_iSup₂ (f := fun (T : TreeData) (_ : IsTree a b i P T) =>
    ENNReal.ofReal (Real.sqrt (treeEnergy φ k f T))) T hT

theorem sizeOff_le {c : ℝ≥0∞}
    (h : ∀ T : TreeData, IsTree a b i P T → ENNReal.ofReal (Real.sqrt (treeEnergy φ k f T)) ≤ c) :
    sizeOff a b φ i k f P ≤ c :=
  iSup₂_le h

theorem le_sizeDiag {t : ℤ × ℤ × ℤ} (ht : t ∈ P) :
    ENNReal.ofReal ((volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ‖pairing f (φ t k)‖) ≤
      sizeDiag φ k f P :=
  le_iSup₂ (f := fun (t : ℤ × ℤ × ℤ) (_ : t ∈ P) =>
    ENNReal.ofReal ((volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ‖pairing f (φ t k)‖)) t ht

theorem sizeDiag_le {c : ℝ≥0∞}
    (h : ∀ t ∈ P,
      ENNReal.ofReal ((volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ‖pairing f (φ t k)‖) ≤ c) :
    sizeDiag φ k f P ≤ c :=
  iSup₂_le h

theorem sizeOff_mono (hP : P ⊆ P') : sizeOff a b φ i k f P ≤ sizeOff a b φ i k f P' :=
  sizeOff_le fun _ hT => le_sizeOff (hT.mono hP)

theorem sizeDiag_mono (hP : P ⊆ P') : sizeDiag φ k f P ≤ sizeDiag φ k f P' :=
  sizeDiag_le fun _ ht => le_sizeDiag (hP ht)

theorem size_mono (hP : P ⊆ P') : size a b φ i k f P ≤ size a b φ i k f P' := by
  unfold size
  split_ifs
  · exact sizeDiag_mono hP
  · exact sizeOff_mono hP

/-- Real-valued form of `sizeOff ≤ c`: for every `i`-tree `T ⊆ P`,
`Σ_{t ∈ T} |⟨f, φ_{t,k}⟩|² ≤ c² |I_T|`. -/
theorem sizeOff_le_ofReal_iff {c : ℝ} (hc : 0 ≤ c) :
    sizeOff a b φ i k f P ≤ ENNReal.ofReal c ↔
      ∀ T : TreeData, IsTree a b i P T →
        ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ c ^ 2 * (volume T.topInt).toReal := by
  constructor
  · intro h T hT
    have h1 := (le_sizeOff (φ := φ) (k := k) (f := f) hT).trans h
    rw [ENNReal.ofReal_le_ofReal_iff hc] at h1
    have h2 : treeEnergy φ k f T ≤ c ^ 2 := by
      have := Real.sqrt_le_left hc |>.1 h1
      exact this
    have hv := T.toReal_volume_topInt_pos
    unfold treeEnergy at h2
    rw [inv_mul_le_iff₀ hv] at h2
    linarith
  · intro h
    refine sizeOff_le fun T hT => ?_
    rw [ENNReal.ofReal_le_ofReal_iff hc]
    apply Real.sqrt_le_iff.2
    refine ⟨hc, ?_⟩
    have hv := T.toReal_volume_topInt_pos
    unfold treeEnergy
    rw [inv_mul_le_iff₀ hv]
    linarith [h T hT]

/-- The tile bound: `size_{k,k}(f, P) ≤ c` gives `|⟨f, φ_{t,k}⟩| ≤ c |I_t|^{1/2}` for `t ∈ P`. -/
theorem norm_pairing_le_of_sizeDiag_le {c : ℝ} (hc : 0 ≤ c) (h : sizeDiag φ k f P ≤ ENNReal.ofReal c)
    {t : ℤ × ℤ × ℤ} (ht : t ∈ P) :
    ‖pairing f (φ t k)‖ ≤ c * (volume (timeInt t)).toReal ^ ((1 : ℝ) / 2) := by
  have h1 := (le_sizeDiag (φ := φ) (k := k) (f := f) ht).trans h
  rw [ENNReal.ofReal_le_ofReal_iff hc] at h1
  have hv := toReal_volume_timeInt_pos t
  have hpos : 0 < (volume (timeInt t)).toReal ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hv _
  have e : (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * (volume (timeInt t)).toReal ^
      ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hv]; norm_num
  calc ‖pairing f (φ t k)‖
      = ((volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ‖pairing f (φ t k)‖) *
          (volume (timeInt t)).toReal ^ ((1 : ℝ) / 2) := by
        rw [mul_right_comm, e, one_mul]
    _ ≤ c * (volume (timeInt t)).toReal ^ ((1 : ℝ) / 2) := by gcongr

/-- The energy of a one-tile tree is the square of `|I_t|^{-1/2} |⟨f, φ_{t,k}⟩|`. -/
theorem sqrt_treeEnergy_singleton (t : ℤ × ℤ × ℤ) (ξ : ℝ) :
    Real.sqrt (treeEnergy φ k f ⟨{t}, (t.1, t.2.1), ξ⟩) =
      (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ‖pairing f (φ t k)‖ := by
  have hv := toReal_volume_timeInt_pos t
  have e : (volume (TreeData.topInt ⟨{t}, (t.1, t.2.1), ξ⟩)).toReal = (volume (timeInt t)).toReal :=
    by simp only [TreeData.topInt, toReal_volume_dyadicInt, toReal_volume_timeInt]
  unfold treeEnergy
  rw [e, Finset.sum_singleton, Real.sqrt_mul (inv_nonneg.2 hv.le), Real.sqrt_inv,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_neg hv.le]
  congr 2
  ring

/-- **`size_{k,k} ≤ size_{i,k}` for `i ≠ k`** (BD26 L730-755; a single tile is an `i`-tree for every `i`). -/
theorem sizeDiag_le_sizeOff : sizeDiag φ k f P ≤ sizeOff a b φ i k f P := by
  refine sizeDiag_le fun t ht => ?_
  have h := le_sizeOff (a := a) (b := b) (φ := φ) (i := i) (k := k) (f := f)
    (isTree_singleton a b i ht)
  rwa [sqrt_treeEnergy_singleton] at h

end SizeApi

/-! ### The canonical frequency `ξ_T = L_T` -/

/-- The left endpoint `2^{-s}(n/3 - 1)` of `3 ω_{t,i}`. -/
def leftEnd3 (a b : ℤ) (i : Fin 3) (t : ℤ × ℤ × ℤ) : ℝ :=
  (2 : ℝ) ^ (-t.1) * ((freqNum a b t i : ℝ) / 3 - 1)

/-- The right endpoint `2^{-s}(n/3 + 2)` of `3 ω_{t,i}`. -/
def rightEnd3 (a b : ℤ) (i : Fin 3) (t : ℤ × ℤ × ℤ) : ℝ :=
  (2 : ℝ) ^ (-t.1) * ((freqNum a b t i : ℝ) / 3 + 2)

/-- `3 ω_{t,i} = [2^{-s}(n/3 - 1), 2^{-s}(n/3 + 2))`. -/
theorem dilate_three_freqInt (a b : ℤ) (i : Fin 3) (t : ℤ × ℤ × ℤ) :
    dilate 3 (freqInt a b i t) = Set.Ico (leftEnd3 a b i t) (rightEnd3 a b i t) := by
  rw [dilate_freqInt]
  unfold leftEnd3 rightEnd3
  congr 1 <;> ring

theorem mem_dilate_three_freqInt {a b : ℤ} {i : Fin 3} {t : ℤ × ℤ × ℤ} {ξ : ℝ} :
    ξ ∈ dilate 3 (freqInt a b i t) ↔ leftEnd3 a b i t ≤ ξ ∧ ξ < rightEnd3 a b i t := by
  rw [dilate_three_freqInt]; rfl

/-- The canonical frequency `L_T = max_{t ∈ S} (left endpoint of 3ω_{t,i})` (junk value `0` for `S = ∅`). -/
def canonXi (a b : ℤ) (i : Fin 3) (S : Finset (ℤ × ℤ × ℤ)) : ℝ :=
  open Classical in
  if h : S.Nonempty then S.sup' h (leftEnd3 a b i) else 0

theorem leftEnd3_le_canonXi {a b : ℤ} {i : Fin 3} {S : Finset (ℤ × ℤ × ℤ)} {t : ℤ × ℤ × ℤ}
    (ht : t ∈ S) : leftEnd3 a b i t ≤ canonXi a b i S := by
  have hne : S.Nonempty := ⟨t, ht⟩
  unfold canonXi
  simp only [hne, ↓reduceDIte]
  exact Finset.le_sup' (leftEnd3 a b i) ht

theorem canonXi_le {a b : ℤ} {i : Fin 3} {S : Finset (ℤ × ℤ × ℤ)} {ξ : ℝ}
    (hS : S.Nonempty) (h : ∀ t ∈ S, leftEnd3 a b i t ≤ ξ) : canonXi a b i S ≤ ξ := by
  unfold canonXi
  simp only [hS, ↓reduceDIte]
  exact Finset.sup'_le hS _ h

/-- If some `ξ` lies in `3ω_{t,i}` for all `t ∈ S`, then so does the canonical `L_S`. -/
theorem canonXi_mem_dilate_three {a b : ℤ} {i : Fin 3} {S : Finset (ℤ × ℤ × ℤ)} {ξ : ℝ}
    (hξ : ∀ t ∈ S, ξ ∈ dilate 3 (freqInt a b i t)) {t : ℤ × ℤ × ℤ} (ht : t ∈ S) :
    canonXi a b i S ∈ dilate 3 (freqInt a b i t) := by
  rw [mem_dilate_three_freqInt]
  refine ⟨leftEnd3_le_canonXi ht, ?_⟩
  have h1 : canonXi a b i S ≤ ξ :=
    canonXi_le ⟨t, ht⟩ fun u hu => (mem_dilate_three_freqInt.1 (hξ u hu)).1
  exact lt_of_le_of_lt h1 (mem_dilate_three_freqInt.1 (hξ t ht)).2

/-- **Canonical trees.** Replacing `ξ_T` by `L_T` keeps an `i`-tree an `i`-tree (same tiles, same top). -/
theorem IsTree.canonical {a b : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)} {T : TreeData}
    (h : IsTree a b i P T) : IsTree a b i P { T with ξ := canonXi a b i T.tiles } :=
  ⟨h.1, fun _ ht => ⟨canonXi_mem_dilate_three (fun _ hu => h.xi_mem hu) ht, h.timeInt_subset ht⟩⟩

end PrimeBHT.TimeFrequency.Tile
