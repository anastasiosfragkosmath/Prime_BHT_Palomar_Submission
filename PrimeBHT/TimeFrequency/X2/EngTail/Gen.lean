module

public import PrimeBHT.TimeFrequency.X2.EngTail.Tail

/-!
# X2, node B5: near tiles of the Calderón-Zygmund intervals, and `L^q` of the atom family

For the Calderón-Zygmund intervals `Q_q = [a_q, b_q)` (centre `ctr_q`, length `δ_q`), a tile `i` is *near* if there is `q` with
`|I_i| ≤ δ_q` and `I_i ∩ 3 Q_q ≠ ∅`.

* `volume_Wset_near_le`: `|W(T)| ≤ 7 ∑_q δ_q` for a family `T` of near tiles;
* `sep_of_not_near`: a tile that is not near has, for each `q`, `|I_i| ≥ δ_q` or `|c_i - ctr_q| ≥ 3 δ_q/2`;
* `Lq_famPhiT_le`: the `L^q` norm of `∑_q α (1 + |x - ctr_q|/δ_q)^{-2}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem dyadicInt_eq_Ico' (j v : ℤ) : dyadicInt j v =
    Ico ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2) - (2 : ℝ) ^ j / 2) ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2) + (2 : ℝ) ^ j / 2) := by
  unfold dyadicInt
  congr 1 <;> ring

section NearTiles

variable {ι : Type*} {ι' : Type}

/-- The tile `i` is near the Calderón-Zygmund interval `Q_q`. -/
def IsNear (a b : ι' → ℝ) (j v : ι → ℤ) (i : ι) : Prop :=
  ∃ q, (2 : ℝ) ^ (j i) ≤ b q - a q ∧
    ¬ Disjoint (dyadicInt (j i) (v i)) (Ico (CZ.ctr a b q - 3 * (b q - a q) / 2) (CZ.ctr a b q + 3 * (b q - a q) / 2))

theorem volume_Wset_near_le [Countable ι'] {a b : ι' → ℝ} (hab : ∀ q, a q < b q) (hsum : Summable fun q => b q - a q)
    (T : Finset ι) (j v : ι → ℤ) (hT : ∀ i ∈ T, IsNear a b j v i) :
    (volume (Wset T j v)).toReal ≤ 7 * ∑' q, (b q - a q) := by
  have hsub : Wset T j v ⊆ ⋃ q, Ico (CZ.ctr a b q - 7 * (b q - a q) / 2) (CZ.ctr a b q + 7 * (b q - a q) / 2) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hz
    obtain ⟨q, hlq, hnd⟩ := hT i hi
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨p, hp1, hp2⟩ := hnd
    rw [dyadicInt_eq_Ico'] at hp1
    simp only [dil3, mem_Ico] at hz
    simp only [mem_Ico] at hp1 hp2
    refine mem_iUnion.2 ⟨q, ?_⟩
    have hl := two_zpow_pos' (j i)
    simp only [CZ.ctr, mem_Ico] at hp2 ⊢
    constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2, hz.1, hz.2]
  have hnn : ∀ q, 0 ≤ b q - a q := fun q => sub_nonneg.2 (hab q).le
  have hm : volume (Wset T j v) ≤ ENNReal.ofReal (7 * ∑' q, (b q - a q)) := by
    calc volume (Wset T j v)
        ≤ volume (⋃ q, Ico (CZ.ctr a b q - 7 * (b q - a q) / 2) (CZ.ctr a b q + 7 * (b q - a q) / 2)) :=
          measure_mono hsub
      _ ≤ ∑' q, volume (Ico (CZ.ctr a b q - 7 * (b q - a q) / 2) (CZ.ctr a b q + 7 * (b q - a q) / 2)) :=
          measure_iUnion_le _
      _ = ∑' q, ENNReal.ofReal (7 * (b q - a q)) := by
          refine tsum_congr fun q => ?_
          rw [Real.volume_Ico]; congr 1; ring
      _ = ENNReal.ofReal (∑' q, 7 * (b q - a q)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun q => by have := hnn q; positivity) (hsum.mul_left 7)).symm
      _ = ENNReal.ofReal (7 * ∑' q, (b q - a q)) := by rw [tsum_mul_left]
  have h0 : 0 ≤ ∑' q, (b q - a q) := tsum_nonneg hnn
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hm

theorem sep_of_not_near {a b : ι' → ℝ} {j v : ι → ℤ} {i : ι} (h : ¬ IsNear a b j v i) (q : ι') :
    b q - a q ≤ (2 : ℝ) ^ (j i) ∨
      3 * (b q - a q) / 2 ≤ |(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - CZ.ctr a b q| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply h
  refine ⟨q, h1.le, Set.not_disjoint_iff.2 ⟨(2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2), ?_, ?_⟩⟩
  · rw [dyadicInt_eq_Ico']
    have := two_zpow_pos' (j i)
    constructor <;> linarith
  · rw [abs_lt] at h2
    constructor <;> linarith [h2.1, h2.2]

end NearTiles

section LqAtoms

/-- `Lq` of the atom family `∑_i α (1 + |x - c_i|/ℓ_i)^{-2}`. -/
theorem Lq_famPhiT_le {ι : Type*} [Countable ι] {q : ℝ} (hq : 1 < q) (c ℓ : ι → ℝ) {α : ℝ} (hα : 0 ≤ α) (hℓ : ∀ i, 0 < ℓ i)
    (hsum : Summable ℓ)
    (hdisj : Pairwise fun i j => Disjoint (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2))) :
    Lq q (famPhiT c ℓ (fun _ => α)) ≤ famConst q * ENNReal.ofReal α * ENNReal.ofReal (∑' i, ℓ i) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  have h := famPhiT_norm_le (c := c) (ℓ := ℓ) (a := fun _ => α) hq hℓ (fun _ => hα) hdisj
  unfold Lq
  refine h.trans (le_of_eq ?_)
  have e : ∑' i, ENNReal.ofReal α ^ q * ENNReal.ofReal (ℓ i) =
      ENNReal.ofReal α ^ q * ENNReal.ofReal (∑' i, ℓ i) := by
    rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun i => (hℓ i).le) hsum]
  rw [e, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne',
    ENNReal.rpow_one, mul_assoc]

end LqAtoms

end PrimeBHT.TimeFrequency.X2
