module

public import PrimeBHT.TimeFrequency.X2.Collections
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# X2, node V05-4: the Whitney box classes and their rank-1 property

A *class* `c : WClass` is a tuple `(s₀, r, t, db, e)`: scale residue `s₀` (mod `16`), index residue `r` (mod `2^10`),
grid offset `θ = t/3` (`t ∈ {0, 1}`), box gap `db = i₂ - i₁`, slot-3 shape `e = i₃ - 2 i₁`.  Its boxes are, for
`s ≡ s₀ (16)` and `i ≡ r (1024)`, with `ℓ = 2^{-s}`,
`ω₁ = ℓ[i + θ, i + θ + 1)`, `ω₂ = ℓ[i + db + θ, ·+1)`, `ω₃ = ℓ[2i + e + 2θ, ·+1)`.
`WClass.Valid c` (bounds on `db`, `e`, and the residue window condition for `(f)`) implies `IsRankOne 16 c.set`
(`isRankOne_set`), for ALL scale gaps.  See `docs/audits/X2-V06-V05-check.md` §2.3 and `X2-REV3-fat-top.md` §4
(here `J = 16`, `J' = 10`, hull dilation `128`, hull constant `256`).
-/

@[expose] public noncomputable section

open Set
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements
open MeasureTheory

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- `ℓ(s) = 2^{-s}`, the frequency length of a box of scale `s`. -/
def ell (s : ℤ) : ℝ := (2 : ℝ) ^ (-s)

theorem ell_pos (s : ℤ) : 0 < ell s := zpow_pos (by norm_num) _

theorem ell_add (s : ℤ) (n : ℕ) : ell (s - n) = (2 : ℝ) ^ n * ell s := by
  unfold ell
  rw [show -(s - (n : ℤ)) = (n : ℤ) + -s by ring, zpow_add₀ (by norm_num), zpow_natCast]

/-- A class of Whitney boxes. -/
structure WClass where
  /-- scale residue (mod 16) -/
  s₀ : ℤ
  /-- index residue (mod 1024) -/
  r : ℤ
  /-- the grid offset is `t / 3`, `t ∈ {0, 1}` -/
  t : ℤ
  /-- box gap `i₂ - i₁` -/
  db : ℤ
  /-- slot-3 shape `i₃ - 2 i₁` -/
  e : ℤ

namespace WClass

variable (c : WClass)

/-- The grid offset `θ = t/3`. -/
def θ : ℝ := (c.t : ℝ) / 3

/-- The box of the class at scale `s` and index `i`. -/
def box (s i : ℤ) : Box :=
  ⟨s, ![ell s * ((i : ℝ) + c.θ + 1 / 2), ell s * ((i : ℝ) + c.db + c.θ + 1 / 2),
    ell s * (2 * (i : ℝ) + c.e + 2 * c.θ + 1 / 2)]⟩

/-- The box set of the class. -/
def set : Set Box :=
  {B | ∃ s i : ℤ, (16 : ℤ) ∣ s - c.s₀ ∧ (1024 : ℤ) ∣ i - c.r ∧ B = c.box s i}

/-- `q = 2 λ₀`, twice the (half-integer) left offset of the hull of a box in units of `ℓ`
(after subtracting `θ`): the hull of `(s, i)` is `ℓ [i + θ + λ₀, i + θ + λ₀ + h]`. -/
def q : ℤ := if 0 < c.db then -127 else 2 * c.db - 127

/-- Hull length in units of `ℓ`: `h = |db| + 128`. -/
def hh : ℤ := |c.db| + 128

/-- Validity of a class: `t ∈ {0,1}`, `15 ≤ |db| ≤ 65`, `e - db ∈ {0, 1}`, and the residue window condition
(`r` outside the bad window of the hull-nesting field (f)). -/
def Valid : Prop :=
  (c.t = 0 ∨ c.t = 1) ∧ 15 ≤ |c.db| ∧ |c.db| ≤ 65 ∧ (c.e = c.db ∨ c.e = c.db + 1) ∧
    ∀ w : ℤ, ¬ (0 ≤ 2048 * w - c.q + 682 * c.t - 2 * c.r ∧
      2048 * w - c.q + 682 * c.t - 2 * c.r ≤ 2 * c.hh)

theorem box_scale (s i : ℤ) : (c.box s i).scale = s := rfl

theorem box_centre0 (s i : ℤ) : (c.box s i).centre 0 = ell s * ((i : ℝ) + c.θ + 1 / 2) := rfl
theorem box_centre1 (s i : ℤ) : (c.box s i).centre 1 = ell s * ((i : ℝ) + c.db + c.θ + 1 / 2) := rfl
theorem box_centre2 (s i : ℤ) : (c.box s i).centre 2 =
    ell s * (2 * (i : ℝ) + c.e + 2 * c.θ + 1 / 2) := rfl

/-- The slot intervals: `ω_k = ℓ [a_k, a_k + 1)`. -/
theorem box_ω0 (s i : ℤ) : (c.box s i).ω 0 = Ico (ell s * ((i : ℝ) + c.θ)) (ell s * ((i : ℝ) + c.θ + 1)) := by
  unfold Box.ω
  rw [box_centre0, box_scale]
  have : (2 : ℝ) ^ (-s) = ell s := rfl
  rw [this]
  congr 1 <;> ring

theorem box_ω1 (s i : ℤ) :
    (c.box s i).ω 1 = Ico (ell s * ((i : ℝ) + c.db + c.θ)) (ell s * ((i : ℝ) + c.db + c.θ + 1)) := by
  unfold Box.ω
  rw [box_centre1, box_scale]
  have : (2 : ℝ) ^ (-s) = ell s := rfl
  rw [this]
  congr 1 <;> ring

theorem box_ω2 (s i : ℤ) :
    (c.box s i).ω 2 =
      Ico (ell s * (2 * (i : ℝ) + c.e + 2 * c.θ)) (ell s * (2 * (i : ℝ) + c.e + 2 * c.θ + 1)) := by
  unfold Box.ω
  rw [box_centre2, box_scale]
  have : (2 : ℝ) ^ (-s) = ell s := rfl
  rw [this]
  congr 1 <;> ring


theorem Valid.db_cases {c : WClass} (hV : c.Valid) : 15 ≤ c.db ∨ c.db ≤ -15 := by
  obtain ⟨-, h1, -⟩ := hV
  rcases le_total 0 c.db with h | h
  · left; rwa [abs_of_nonneg h] at h1
  · right; rw [abs_of_nonpos h] at h1; linarith

theorem Valid.e_cases {c : WClass} (hV : c.Valid) : c.e = c.db ∨ c.e = c.db + 1 := hV.2.2.2.1

/-- Left offset of the hull (in units of `ℓ`, after subtracting `i + θ`). -/
def lo0 : ℝ := ((min 0 c.db : ℤ) : ℝ) - 127 / 2

/-- Right offset of the hull. -/
def hi0 : ℝ := ((max 0 c.db : ℤ) : ℝ) + 129 / 2

theorem hi0_sub_lo0 : c.hi0 - c.lo0 = (c.hh : ℝ) := by
  unfold hi0 lo0 hh
  have : ((max 0 c.db : ℤ) : ℝ) - ((min 0 c.db : ℤ) : ℝ) = ((|c.db| : ℤ) : ℝ) := by
    rw [← Int.cast_sub]
    congr 1
    rcases le_total 0 c.db with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos h]; ring
  push_cast at this ⊢
  linarith

theorem hull_box (hV : c.Valid) (s i : ℤ) :
    (c.box s i).hull = Icc (ell s * ((i : ℝ) + c.θ + c.lo0)) (ell s * ((i : ℝ) + c.θ + c.hi0)) := by
  have hℓ := ell_pos s
  have hd := hV.db_cases
  have he := hV.e_cases
  have heR : (c.e : ℝ) = c.db ∨ (c.e : ℝ) = c.db + 1 := by
    rcases he with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hs : (2 : ℝ) ^ (-s) = ell s := rfl
  unfold Box.hull
  simp only [box_scale, hs, box_centre0, box_centre1, box_centre2, hullDil, freqDir]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, div_one]
  have e1 : ell s * ((i : ℝ) + c.θ + 1 / 2) - 128 * ell s / 2 = ell s * ((i : ℝ) + c.θ + -127 / 2) := by ring
  have e2 : ell s * ((i : ℝ) + c.db + c.θ + 1 / 2) - 128 * ell s / 2 =
      ell s * ((i : ℝ) + c.θ + (c.db - 127 / 2)) := by ring
  have e3 : (ell s * (2 * (i : ℝ) + c.e + 2 * c.θ + 1 / 2) - 128 * ell s / 2) / 2 =
      ell s * ((i : ℝ) + c.θ + (c.e / 2 - 127 / 4)) := by ring
  have f1 : ell s * ((i : ℝ) + c.θ + 1 / 2) + 128 * ell s / 2 = ell s * ((i : ℝ) + c.θ + 129 / 2) := by ring
  have f2 : ell s * ((i : ℝ) + c.db + c.θ + 1 / 2) + 128 * ell s / 2 =
      ell s * ((i : ℝ) + c.θ + (c.db + 129 / 2)) := by ring
  have f3 : (ell s * (2 * (i : ℝ) + c.e + 2 * c.θ + 1 / 2) + 128 * ell s / 2) / 2 =
      ell s * ((i : ℝ) + c.θ + (c.e / 2 + 129 / 4)) := by ring
  rw [e1, e2, e3, f1, f2, f3]
  rcases hd with h | h
  · -- db ≥ 15
    have hdbR : (15 : ℝ) ≤ c.db := by exact_mod_cast h
    have hmin : min 0 c.db = 0 := min_eq_left (by omega)
    have hmax : max 0 c.db = c.db := max_eq_right (by omega)
    have l0 : c.lo0 = -127 / 2 := by unfold lo0; rw [hmin]; norm_num
    have h0 : c.hi0 = c.db + 129 / 2 := by unfold hi0; rw [hmax]
    rw [l0, h0]
    have a1 : ell s * ((i : ℝ) + c.θ + -127 / 2) ≤ ell s * ((i : ℝ) + c.θ + (c.db - 127 / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hdbR]) hℓ.le
    have a2 : ell s * ((i : ℝ) + c.θ + -127 / 2) ≤ ell s * ((i : ℝ) + c.θ + (c.e / 2 - 127 / 4)) :=
      mul_le_mul_of_nonneg_left (by rcases heR with h' | h' <;> rw [h'] <;> linarith only [hdbR]) hℓ.le
    have b1 : ell s * ((i : ℝ) + c.θ + 129 / 2) ≤ ell s * ((i : ℝ) + c.θ + (c.db + 129 / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hdbR]) hℓ.le
    have b2 : ell s * ((i : ℝ) + c.θ + (c.e / 2 + 129 / 4)) ≤ ell s * ((i : ℝ) + c.θ + (c.db + 129 / 2)) :=
      mul_le_mul_of_nonneg_left (by rcases heR with h' | h' <;> rw [h'] <;> linarith only [hdbR]) hℓ.le
    rw [min_eq_left a1, min_eq_left a2, max_eq_right b1, max_eq_left b2]
  · -- db ≤ -15
    have hdbR : (c.db : ℝ) ≤ -15 := by exact_mod_cast h
    have hmin : min 0 c.db = c.db := min_eq_right (by omega)
    have hmax : max 0 c.db = 0 := max_eq_left (by omega)
    have l0 : c.lo0 = c.db - 127 / 2 := by unfold lo0; rw [hmin]
    have h0 : c.hi0 = 129 / 2 := by unfold hi0; rw [hmax]; simp
    rw [l0, h0]
    have a1 : ell s * ((i : ℝ) + c.θ + (c.db - 127 / 2)) ≤ ell s * ((i : ℝ) + c.θ + -127 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hdbR]) hℓ.le
    have a2 : ell s * ((i : ℝ) + c.θ + (c.db - 127 / 2)) ≤ ell s * ((i : ℝ) + c.θ + (c.e / 2 - 127 / 4)) :=
      mul_le_mul_of_nonneg_left (by rcases heR with h' | h' <;> rw [h'] <;> linarith only [hdbR]) hℓ.le
    have b1 : ell s * ((i : ℝ) + c.θ + (c.db + 129 / 2)) ≤ ell s * ((i : ℝ) + c.θ + 129 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hdbR]) hℓ.le
    have b2 : ell s * ((i : ℝ) + c.θ + (c.e / 2 + 129 / 4)) ≤ ell s * ((i : ℝ) + c.θ + 129 / 2) :=
      mul_le_mul_of_nonneg_left (by rcases heR with h' | h' <;> rw [h'] <;> linarith only [hdbR]) hℓ.le
    rw [min_eq_right a1, min_eq_left a2, max_eq_left b1, max_eq_left b2]


/-! ### Arithmetic of the scale gap `K = 2^{16 m}` -/

theorem three_dvd_pow_sub_one (m : ℕ) : (3 : ℤ) ∣ (2 : ℤ) ^ (16 * m) - 1 := by
  have h : (2 : ℤ) ^ (16 * m) = (65536 : ℤ) ^ m := by rw [pow_mul]; norm_num
  rw [h]
  have : (65536 : ℤ) ≡ 1 [ZMOD 3] := by decide
  have h1 := (this.pow m).symm
  rw [one_pow] at h1
  exact (Int.modEq_iff_dvd.1 h1)

/-- For `m ≥ 1`, `2^{16 m} = 2048 (3y - 1)`. -/
theorem exists_y (m : ℕ) (hm : 1 ≤ m) : ∃ y : ℤ, (2 : ℤ) ^ (16 * m) = 2048 * (3 * y - 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 16 * m = 11 + (2 * n + 1) + 4 := ⟨(16 * m - 16) / 2, by omega⟩
  have h2 : (2 : ℤ) ^ (16 * m) = 2048 * (2 * 4 ^ n) * 16 := by
    have h4 : (4 : ℤ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [hn, h4, pow_add, pow_add, pow_succ]; norm_num; ring
  have h4 : (3 : ℤ) ∣ 2 * 4 ^ n * 16 + 1 := by
    have : (4 : ℤ) ^ n ≡ 1 [ZMOD 3] := by
      have := (show (4 : ℤ) ≡ 1 [ZMOD 3] by decide).pow n
      simpa using this
    have h5 : 2 * (4 : ℤ) ^ n * 16 + 1 ≡ 2 * 1 * 16 + 1 [ZMOD 3] :=
      ((this.mul_left 2).mul_right 16).add_right 1
    exact (Int.modEq_zero_iff_dvd.1 (h5.trans (by decide)))
  obtain ⟨y, hy⟩ := h4
  refine ⟨y, ?_⟩
  rw [h2]
  linarith


/-! ### Slot grids -/

/-- The slot multiplicities `(1, 1, 2)` of `freqDir`. -/
def jk : Fin 3 → ℤ := ![1, 1, 2]

/-- Slot offsets `(0, db, e)`. -/
def ok : Fin 3 → ℤ := ![0, c.db, c.e]

/-- The start of slot `k` in units of `ℓ`. -/
def start (k : Fin 3) (i : ℤ) : ℝ := (jk k : ℝ) * i + (ok c k : ℝ) + (jk k : ℝ) * c.θ

theorem box_ω (k : Fin 3) (s i : ℤ) :
    (c.box s i).ω k = Ico (ell s * c.start k i) (ell s * (c.start k i + 1)) := by
  fin_cases k
  · rw [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl, box_ω0]
    simp only [start, jk, ok, Matrix.cons_val_zero]
    congr 1 <;> push_cast <;> ring_nf
  · rw [show (⟨1, by decide⟩ : Fin 3) = 1 from rfl, box_ω1]
    simp only [start, jk, ok, Matrix.cons_val_one]
    congr 1 <;> push_cast <;> ring_nf
  · rw [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl, box_ω2]
    simp only [start, jk, ok, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    congr 1 <;> push_cast <;> ring_nf

theorem jk_pos (k : Fin 3) : 0 < jk k := by fin_cases k <;> simp [jk]

theorem grid_aux {ℓ : ℝ} {K : ℤ} (hℓ : 0 < ℓ) {x X : ℝ} {z : ℤ} (hz : x - (K : ℝ) * X = z) :
    ((0 ≤ z ∧ z < K) ∧ Ico (ℓ * x) (ℓ * (x + 1)) ⊆ Ico ((K : ℝ) * ℓ * X) ((K : ℝ) * ℓ * (X + 1))) ∨
      Disjoint (Ico (ℓ * x) (ℓ * (x + 1))) (Ico ((K : ℝ) * ℓ * X) ((K : ℝ) * ℓ * (X + 1))) := by
  have hx : x = (K : ℝ) * X + z := by linarith
  subst hx
  by_cases h1 : 0 ≤ z ∧ z < K
  · left
    refine ⟨h1, ?_⟩
    have hz0 : (0 : ℝ) ≤ z := by exact_mod_cast h1.1
    have hz1 : (z : ℝ) + 1 ≤ K := by exact_mod_cast h1.2
    apply Ico_subset_Ico
    · nlinarith [mul_nonneg hℓ.le hz0]
    · nlinarith [mul_le_mul_of_nonneg_left hz1 hℓ.le]
  · right
    rw [not_and_or, not_le, not_lt] at h1
    rw [Set.disjoint_left]
    intro y hy hy'
    rcases h1 with h | h
    · have : (z : ℝ) + 1 ≤ 0 := by exact_mod_cast (by omega : z + 1 ≤ 0)
      nlinarith [mul_le_mul_of_nonneg_left this hℓ.le, hy.2, hy'.1]
    · have : (K : ℝ) ≤ z := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_left this hℓ.le, hy.1, hy'.2]


theorem ell_gap {s s' : ℤ} {m : ℕ} (hs : s = s' + 16 * m) :
    ell s' = (((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ell s := by
  have : s' = s - ((16 * m : ℕ) : ℤ) := by push_cast; omega
  rw [this, ell_add]
  push_cast
  rfl

theorem start_sub_mul {K w : ℤ} (hK : K = 3 * w + 1) (k : Fin 3) (i i' : ℤ) :
    c.start k i - (K : ℝ) * c.start k i' =
      ((jk k * (i - K * i') - (K - 1) * ok c k - jk k * c.t * w : ℤ) : ℝ) := by
  unfold start θ
  have hKR : (K : ℝ) = 3 * w + 1 := by exact_mod_cast hK
  rw [hKR]
  push_cast
  rw [hKR] at *
  ring

theorem slot_cases (k : Fin 3) {s s' : ℤ} {m : ℕ} (hs : s = s' + 16 * m) (i i' : ℤ) :
    ((c.box s i).ω k ⊆ (c.box s' i').ω k ∧ ∃ z : ℤ, 0 ≤ z ∧ z < (2 : ℤ) ^ (16 * m) ∧
        c.start k i - (((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * c.start k i' = z) ∨
      Disjoint ((c.box s i).ω k) ((c.box s' i').ω k) := by
  obtain ⟨w, hw⟩ := three_dvd_pow_sub_one m
  have hK : (2 : ℤ) ^ (16 * m) = 3 * w + 1 := by linarith
  have hz := start_sub_mul c hK k i i'
  have hℓ := ell_pos s
  have hgap := ell_gap hs
  rw [box_ω, box_ω, hgap]
  rcases grid_aux hℓ hz with ⟨⟨h0, h1⟩, hsub⟩ | hd
  · left
    exact ⟨hsub, _, h0, h1, hz⟩
  · right; exact hd

/-- (a): the scale gap is a multiple of `16`. -/
theorem field_a {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set) : (16 : ℤ) ∣ B.scale - B'.scale := by
  obtain ⟨s, i, hs, -, rfl⟩ := hB
  obtain ⟨s', i', hs', -, rfl⟩ := hB'
  simp only [box_scale]
  have := dvd_sub hs hs'
  simpa using this

theorem exists_gap {s s' : ℤ} (hs : (16 : ℤ) ∣ s - s') (h : s' ≤ s) : ∃ m : ℕ, s = s' + 16 * m := by
  obtain ⟨n, hn⟩ := hs
  refine ⟨n.toNat, ?_⟩
  have : 0 ≤ n := by omega
  rw [Int.toNat_of_nonneg this]; omega

/-- (a), grids: the slot-`k` intervals of two boxes of the class are nested or disjoint. -/
theorem field_grid {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set) (k : Fin 3) :
    B.ω k ⊆ B'.ω k ∨ B'.ω k ⊆ B.ω k ∨ Disjoint (B.ω k) (B'.ω k) := by
  obtain ⟨s, i, hs, -, rfl⟩ := hB
  obtain ⟨s', i', hs', -, rfl⟩ := hB'
  have hdiv : (16 : ℤ) ∣ s - s' := by simpa using dvd_sub hs hs'
  rcases le_total s' s with h | h
  · obtain ⟨m, hm⟩ := exists_gap hdiv h
    rcases slot_cases c k hm i i' with ⟨hsub, -⟩ | hd
    · exact Or.inl hsub
    · exact Or.inr (Or.inr hd)
  · obtain ⟨m, hm⟩ := exists_gap (by simpa using dvd_sub hs' hs) h
    rcases slot_cases c k hm i' i with ⟨hsub, -⟩ | hd
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr hd.symm)

/-- (b): distinct boxes of the same scale have disjoint slot intervals. -/
theorem field_same_scale {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set) (hne : B ≠ B')
    (hsc : B.scale = B'.scale) (k : Fin 3) : Disjoint (B.ω k) (B'.ω k) := by
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  obtain ⟨s', i', hs', hi', rfl⟩ := hB'
  simp only [box_scale] at hsc
  subst hsc
  rcases slot_cases c k (m := 0) (s := s) (s' := s) (by simp) i i' with ⟨-, z, h0, h1, hz⟩ | hd
  · exfalso
    apply hne
    have hz0 : z = 0 := by simpa using (by omega : z = 0)
    subst hz0
    have hjk := jk_pos k
    have : (jk k : ℝ) * ((i : ℝ) - i') = 0 := by
      unfold start at hz
      have hK1 : (((2 : ℤ) ^ (16 * 0) : ℤ) : ℝ) = 1 := by norm_num
      rw [hK1, Int.cast_zero] at hz
      linarith
    have h2 : (jk k : ℝ) ≠ 0 := by exact_mod_cast hjk.ne'
    have h3 : (i : ℝ) = i' := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h2
      · linarith
    have : i = i' := by exact_mod_cast h3
    rw [this]
  · exact hd


/-! ### Hulls: (e), (h) and the arithmetic of (f) -/

theorem hh_le (hV : c.Valid) : c.hh ≤ 193 := by
  obtain ⟨-, -, h2, -⟩ := hV
  unfold hh; omega

theorem lo0_eq_q (hV : c.Valid) : c.lo0 = (c.q : ℝ) / 2 := by
  unfold lo0 q
  rcases hV.db_cases with h | h
  · rw [min_eq_left (by omega), ite_eq_left (by omega)]; push_cast; ring
  · rw [min_eq_right (by omega), ite_eq_right (by omega)]; push_cast; ring

theorem hi0_eq (_hV : c.Valid) : c.hi0 = c.lo0 + (c.hh : ℝ) := by
  have := hi0_sub_lo0 c
  linarith

/-- (e): distinct boxes of the same scale have disjoint hulls. -/
theorem field_hull_disjoint (hV : c.Valid) {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set)
    (hne : B ≠ B') (hsc : B.scale = B'.scale) : Disjoint B.hull B'.hull := by
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  obtain ⟨s', i', hs', hi', rfl⟩ := hB'
  simp only [box_scale] at hsc
  subst hsc
  have hii : i ≠ i' := fun h => hne (by rw [h])
  rw [hull_box c hV, hull_box c hV]
  have hd : (1024 : ℤ) ∣ i - i' := by
    have := dvd_sub hi hi'
    have e : i - c.r - (i' - c.r) = i - i' := by ring
    rwa [e] at this
  have hℓ := ell_pos s
  have hhR : (c.hh : ℝ) ≤ 193 := by exact_mod_cast hh_le c hV
  have hhi := hi0_eq c hV
  have key : ∀ j j' : ℤ, 1024 ∣ j - j' → j < j' →
      Disjoint (Icc (ell s * ((j : ℝ) + c.θ + c.lo0)) (ell s * ((j : ℝ) + c.θ + c.hi0)))
        (Icc (ell s * ((j' : ℝ) + c.θ + c.lo0)) (ell s * ((j' : ℝ) + c.θ + c.hi0))) := by
    intro j j' hjj hlt
    obtain ⟨n, hn⟩ := hjj
    have h1 : (1024 : ℤ) ≤ j' - j := by omega
    have h2 : (1024 : ℝ) ≤ (j' : ℝ) - j := by exact_mod_cast h1
    rw [Set.disjoint_left]
    intro y hy hy'
    have : ell s * ((j : ℝ) + c.θ + c.hi0) < ell s * ((j' : ℝ) + c.θ + c.lo0) := by
      apply mul_lt_mul_of_pos_left _ hℓ
      linarith
    linarith [hy.2, hy'.1]
  rcases lt_or_gt_of_ne hii with h | h
  · exact key i i' hd h
  · exact (key i' i (by simpa using (dvd_neg.2 hd)) h).symm

/-- (h): the hull has length at most `hullConst * 2^{-scale}`. -/
theorem field_hull_length (hV : c.Valid) {B : Box} (hB : B ∈ c.set) :
    ∀ x ∈ B.hull, ∀ y ∈ B.hull, |x - y| ≤ hullConst * (2 : ℝ) ^ (-B.scale) := by
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  rw [hull_box c hV]
  intro x hx y hy
  have hℓ := ell_pos s
  have hhR : (c.hh : ℝ) ≤ 193 := by exact_mod_cast hh_le c hV
  have hhi := hi0_eq c hV
  have hs' : (2 : ℝ) ^ (-(c.box s i).scale) = ell s := rfl
  rw [hs']
  unfold hullConst
  rw [abs_le]
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]


/-- The integer arithmetic of (f), for ALL scale gaps `K = 2^{16 m}`, `m ≥ 1` (`K = 2048 (3y - 1) = 3w + 1`):
`N' = 2 K i' - 2 i + w (2t + 3q) + 2 K ε h ≡ -q + 682 t - 2 r (mod 2048)`. -/
theorem endpoint_excluded (hV : c.Valid) {K w y z i i' : ℤ} (hKy : K = 2048 * (3 * y - 1))
    (hw : K = 3 * w + 1) (hi : i = c.r + 1024 * z) (ε : ℤ) :
    ¬ (0 ≤ 2 * K * i' - 2 * i + w * (2 * c.t + 3 * c.q) + 2 * K * ε * c.hh ∧
      2 * K * i' - 2 * i + w * (2 * c.t + 3 * c.q) + 2 * K * ε * c.hh ≤ 2 * c.hh) := by
  have hwy : w = 2048 * y - 683 := by omega
  have hV' := hV.2.2.2.2
  have hEq : 2 * K * i' - 2 * i + w * (2 * c.t + 3 * c.q) + 2 * K * ε * c.hh =
      2048 * (2 * (3 * y - 1) * i' - z + y * (2 * c.t + 3 * c.q) + 2 * (3 * y - 1) * ε * c.hh - c.q - c.t)
        - c.q + 682 * c.t - 2 * c.r := by
    subst hwy hKy hi
    ring
  rw [hEq]
  exact hV' _

/-- (f): hull nesting, for every scale gap. -/
theorem field_hull_nest (hV : c.Valid) {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set)
    (hlt : B'.scale < B.scale) (hne : (B.hull ∩ B'.hull).Nonempty) : B.hull ⊆ B'.hull := by
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  obtain ⟨s', i', hs', hi', rfl⟩ := hB'
  simp only [box_scale] at hlt
  have hdiv : (16 : ℤ) ∣ s - s' := by simpa using dvd_sub hs hs'
  obtain ⟨m, hm⟩ := exists_gap hdiv hlt.le
  have hm1 : 1 ≤ m := by omega
  obtain ⟨y, hy⟩ := exists_y m hm1
  obtain ⟨w, hw⟩ := three_dvd_pow_sub_one m
  have hKw : (2 : ℤ) ^ (16 * m) = 3 * w + 1 := by linarith
  obtain ⟨z, hz⟩ := hi
  have hiz : i = c.r + 1024 * z := by omega
  have hℓ := ell_pos s
  have hgap := ell_gap hm
  have hKR : (2 : ℝ) ^ (16 * m) = 3 * (w : ℝ) + 1 := by exact_mod_cast hKw
  rw [hull_box c hV, hull_box c hV] at hne ⊢
  rw [hgap] at hne ⊢
  obtain ⟨x, ⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩ := hne
  by_contra hnot
  have hnot' : ¬ ((((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ell s * ((i' : ℝ) + c.θ + c.lo0) ≤
        ell s * ((i : ℝ) + c.θ + c.lo0) ∧
      ell s * ((i : ℝ) + c.θ + c.hi0) ≤ (((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ell s * ((i' : ℝ) + c.θ + c.hi0)) :=
    fun h => hnot (Icc_subset_Icc h.1 h.2)
  have hhi := hi0_eq c hV
  have hlo := lo0_eq_q c hV
  -- the real identity
  have hN : ∀ ε : ℤ, (((2 * ((2 : ℤ) ^ (16 * m)) * i' - 2 * i + w * (2 * c.t + 3 * c.q) +
        2 * ((2 : ℤ) ^ (16 * m)) * ε * c.hh : ℤ)) : ℝ) =
      2 * ((((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ((i' : ℝ) + c.θ + c.lo0 + ε * c.hh) -
        ((i : ℝ) + c.θ + c.lo0)) := by
    intro ε
    push_cast
    rw [hlo]
    unfold θ
    rw [hKR]
    ring
  simp only [not_and_or, not_le] at hnot'
  rcases hnot' with h | h
  · -- left endpoint of the coarse hull is inside the fine hull
    have h1 : ell s * ((i : ℝ) + c.θ + c.lo0) <
        ell s * ((((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ((i' : ℝ) + c.θ + c.lo0)) := by linarith
    have h2 : ell s * ((((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ((i' : ℝ) + c.θ + c.lo0)) ≤
        ell s * ((i : ℝ) + c.θ + c.hi0) := by linarith
    have h1' := lt_of_mul_lt_mul_left h1 hℓ.le
    have h2' := le_of_mul_le_mul_left h2 hℓ
    have hn := hN 0
    simp only [Int.cast_zero, zero_mul, add_zero, mul_zero] at hn
    exact endpoint_excluded c hV (K := (2 : ℤ) ^ (16 * m)) (w := w) (y := y) (z := z) hy hKw hiz 0
      (by
        simp only [mul_zero, zero_mul, add_zero]
        constructor
        · have : (0 : ℝ) ≤ ((2 * ((2 : ℤ) ^ (16 * m)) * i' - 2 * i + w * (2 * c.t + 3 * c.q) : ℤ) : ℝ) := by
            rw [hn]; linarith
          exact_mod_cast this
        · have : ((2 * ((2 : ℤ) ^ (16 * m)) * i' - 2 * i + w * (2 * c.t + 3 * c.q) : ℤ) : ℝ) ≤
              ((2 * c.hh : ℤ) : ℝ) := by
            rw [hn, show ((2 * c.hh : ℤ) : ℝ) = 2 * (c.hh : ℝ) by push_cast; ring]; linarith
          exact_mod_cast this)
  · -- right endpoint of the coarse hull is inside the fine hull
    have h1 : (((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ell s * ((i' : ℝ) + c.θ + c.hi0) <
        ell s * ((i : ℝ) + c.θ + c.hi0) := h
    have h3 : ell s * ((i : ℝ) + c.θ + c.lo0) ≤
        ell s * ((((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ((i' : ℝ) + c.θ + c.hi0)) := by linarith
    have h1' : (((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ((i' : ℝ) + c.θ + c.hi0) < (i : ℝ) + c.θ + c.hi0 := by
      have : ell s * ((((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) * ((i' : ℝ) + c.θ + c.hi0)) <
          ell s * ((i : ℝ) + c.θ + c.hi0) := by linarith
      exact lt_of_mul_lt_mul_left this hℓ.le
    have h3' := le_of_mul_le_mul_left h3 hℓ
    have hn := hN 1
    rw [hhi] at h1' h3'
    simp only [Int.cast_one, one_mul] at hn
    exact endpoint_excluded c hV (K := (2 : ℤ) ^ (16 * m)) (w := w) (y := y) (z := z) hy hKw hiz 1
      (by
        constructor
        · have : (0 : ℝ) ≤ ((2 * ((2 : ℤ) ^ (16 * m)) * i' - 2 * i + w * (2 * c.t + 3 * c.q) +
              2 * ((2 : ℤ) ^ (16 * m)) * 1 * c.hh : ℤ) : ℝ) := by
            rw [hn]; linarith
          exact_mod_cast this
        · have : ((2 * ((2 : ℤ) ^ (16 * m)) * i' - 2 * i + w * (2 * c.t + 3 * c.q) +
              2 * ((2 : ℤ) ^ (16 * m)) * 1 * c.hh : ℤ) : ℝ) ≤ ((2 * c.hh : ℤ) : ℝ) := by
            rw [hn, show ((2 * c.hh : ℤ) : ℝ) = 2 * (c.hh : ℝ) by push_cast; ring]; linarith
          exact_mod_cast this)


/-! ### Dilates, (c), (d), (g) -/

theorem dilate_Icc {x y : ℝ} (h : x ≤ y) (C : ℝ) :
    dilate C (Icc x y) = Ico ((x + y) / 2 - C * (y - x) / 2) ((x + y) / 2 + C * (y - x) / 2) := by
  unfold dilate intervalCentre
  rw [csInf_Icc h, csSup_Icc h, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem dilate_Icc_mono {x y x' y' : ℝ} (h : x ≤ y) (hsub : Icc x y ⊆ Icc x' y') {C : ℝ} (hC : 1 ≤ C) :
    dilate C (Icc x y) ⊆ dilate C (Icc x' y') := by
  have h' : x' ≤ y' := by
    have := hsub (Set.left_mem_Icc.2 h)
    exact this.1.trans this.2
  have hh := (Set.Icc_subset_Icc_iff h).1 hsub
  rw [dilate_Icc h, dilate_Icc h']
  apply Ico_subset_Ico <;> nlinarith [hh.1, hh.2]

theorem dilate_ω (B : Box) (k : Fin 3) (C : ℝ) :
    dilate C (B.ω k) = Ico (B.centre k - C * (2 : ℝ) ^ (-B.scale) / 2) (B.centre k + C * (2 : ℝ) ^ (-B.scale) / 2) := by
  have hℓ : 0 < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  unfold Box.ω
  rw [dilate_Ico (by linarith)]
  congr 1 <;> ring

/-- (d): the `3ω_k` of boxes with a nested `ω_j` are disjoint.  Core computation. -/
theorem d_core {ℓ ℓ' cj cj' ck ck' α β : ℝ} (hℓ : 0 < ℓ) (hℓ' : 2 * ℓ ≤ ℓ') (hα : 0 ≤ α)
    (hc : |cj - cj'| ≤ (ℓ' - ℓ) / 2) (hk : ck = α * cj + ℓ * β) (hk' : ck' = α * cj' + ℓ' * β)
    (hβ : 9 / 2 + α / 2 ≤ |β|) :
    Disjoint (Ico (ck - 3 * ℓ / 2) (ck + 3 * ℓ / 2)) (Ico (ck' - 3 * ℓ' / 2) (ck' + 3 * ℓ' / 2)) := by
  have hdiff : ck - ck' = α * (cj - cj') - (ℓ' - ℓ) * β := by rw [hk, hk']; ring
  have hc1 := abs_le.1 hc
  have hpos : 0 ≤ ℓ' - ℓ := by linarith
  rw [Set.disjoint_left]
  intro y hy hy'
  rcases le_total 0 β with hb | hb
  · rw [abs_of_nonneg hb] at hβ
    have h1 : (ℓ' - ℓ) * (9 / 2 + α / 2) ≤ (ℓ' - ℓ) * β := mul_le_mul_of_nonneg_left hβ hpos
    have h2 : α * (cj - cj') ≤ α * ((ℓ' - ℓ) / 2) := mul_le_mul_of_nonneg_left hc1.2 hα
    nlinarith [hy.2, hy'.1]
  · rw [abs_of_nonpos hb] at hβ
    have h1 : (ℓ' - ℓ) * (9 / 2 + α / 2) ≤ (ℓ' - ℓ) * (-β) := mul_le_mul_of_nonneg_left (by linarith) hpos
    have h2 : α * (-((ℓ' - ℓ) / 2)) ≤ α * (cj - cj') := mul_le_mul_of_nonneg_left hc1.1 hα
    nlinarith [hy.1, hy'.2]


theorem ico_disjoint_of_dist {a b r r' : ℝ} (h : r + r' ≤ |a - b|) :
    Disjoint (Ico (a - r) (a + r)) (Ico (b - r') (b + r')) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  rcases le_total 0 (a - b) with h0 | h0
  · rw [abs_of_nonneg h0] at h
    linarith [hy.1, hy'.2]
  · rw [abs_of_nonpos h0] at h
    linarith [hy.2, hy'.1]

theorem box_centre_start (k : Fin 3) (s i : ℤ) :
    (c.box s i).centre k = ell s * (c.start k i + 1 / 2) := by
  fin_cases k
  · simp only [Fin.zero_eta, box_centre0, start, jk, ok, Matrix.cons_val_zero]; push_cast; ring
  · simp only [Fin.mk_one, box_centre1, start, jk, ok, Matrix.cons_val_one]; push_cast; ring
  · simp only [Fin.reduceFinMk, box_centre2, start, jk, ok, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]; push_cast; ring

theorem ell_le_iff {s s' : ℤ} : ell s ≤ ell s' ↔ s' ≤ s := by
  unfold ell
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  omega

/-- If `ω_j(B) ⊆ ω_j(B')` for two distinct boxes of the class, then `B'` is strictly coarser by a gap
`16 m`, `m ≥ 1`, and the centres are close. -/
theorem nested_gap (_hV : c.Valid) {s s' i i' : ℤ} (hs : (16 : ℤ) ∣ s - c.s₀) (hs' : (16 : ℤ) ∣ s' - c.s₀)
    (hi : (1024 : ℤ) ∣ i - c.r) (hi' : (1024 : ℤ) ∣ i' - c.r) (hne : c.box s i ≠ c.box s' i') (j : Fin 3)
    (hsub : (c.box s i).ω j ⊆ (c.box s' i').ω j) :
    s' < s ∧ 2 * ell s ≤ ell s' ∧ |(c.box s i).centre j - (c.box s' i').centre j| ≤ (ell s' - ell s) / 2 := by
  have hℓ := ell_pos s
  have hℓ' := ell_pos s'
  rw [box_ω, box_ω] at hsub
  have hlt : ell s ≤ ell s' ∧ ell s' * c.start j i' ≤ ell s * c.start j i ∧
      ell s * (c.start j i + 1) ≤ ell s' * (c.start j i' + 1) := by
    have := (Set.Ico_subset_Ico_iff (by nlinarith : ell s * c.start j i < ell s * (c.start j i + 1))).1 hsub
    refine ⟨?_, this.1, this.2⟩
    nlinarith [this.1, this.2]
  have hs's : s' ≤ s := ell_le_iff.1 hlt.1
  have hne' : s' ≠ s := by
    intro h
    subst h
    have hd := field_same_scale c ⟨s', i, hs, hi, rfl⟩ ⟨s', i', hs', hi', rfl⟩ hne rfl j
    rw [box_ω, box_ω] at hd
    rw [Set.disjoint_left] at hd
    have hmem : ell s' * c.start j i ∈ Ico (ell s' * c.start j i) (ell s' * (c.start j i + 1)) :=
      ⟨le_rfl, by nlinarith⟩
    exact hd hmem (hsub hmem)
  have hstrict : s' < s := lt_of_le_of_ne hs's hne'
  obtain ⟨m, hm⟩ := exists_gap (by simpa using dvd_sub hs hs') hs's
  have hm1 : 1 ≤ m := by omega
  have hgap := ell_gap hm
  have hK : (2 : ℝ) ≤ (((2 : ℤ) ^ (16 * m) : ℤ) : ℝ) := by
    have : (2 : ℤ) ≤ 2 ^ (16 * m) := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (16 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast this
  refine ⟨hstrict, ?_, ?_⟩
  · rw [hgap]; nlinarith
  · rw [box_centre_start, box_centre_start, abs_le]
    constructor <;> nlinarith [hlt.2.1, hlt.2.2]

/-- The relation `c_k = α c_j + ℓ β` between slot centres of one box. -/
theorem centre_rel {j k : Fin 3} (s i : ℤ) :
    (c.box s i).centre k =
      ((jk k : ℝ) / (jk j : ℝ)) * (c.box s i).centre j +
        ell s * ((c.ok k : ℝ) + 1 / 2 - ((jk k : ℝ) / (jk j : ℝ)) * ((c.ok j : ℝ) + 1 / 2)) := by
  have hj : (jk j : ℝ) ≠ 0 := by exact_mod_cast (jk_pos j).ne'
  rw [box_centre_start, box_centre_start]
  unfold start
  field_simp
  ring


theorem le_abs_of {a b : ℝ} (h : a ≤ b ∨ a ≤ -b) : a ≤ |b| := by
  rcases h with h | h
  · exact h.trans (le_abs_self _)
  · exact h.trans (neg_le_abs _)

theorem db_e_real (hV : c.Valid) :
    ((15 : ℝ) ≤ c.db ∨ (c.db : ℝ) ≤ -15) ∧ ((c.e : ℝ) = c.db ∨ (c.e : ℝ) = c.db + 1) := by
  refine ⟨?_, ?_⟩
  · rcases hV.db_cases with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rcases hV.e_cases with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h

theorem beta_bound (hV : c.Valid) (j k : Fin 3) (hk : k ≠ j) :
    9 / 2 + ((jk k : ℝ) / (jk j : ℝ)) / 2 ≤
      |(c.ok k : ℝ) + 1 / 2 - ((jk k : ℝ) / (jk j : ℝ)) * ((c.ok j : ℝ) + 1 / 2)| := by
  obtain ⟨hd, he⟩ := db_e_real c hV
  fin_cases j <;> fin_cases k <;> simp [jk, ok] at hk ⊢ <;> apply le_abs_of <;>
    rcases hd with h | h <;> rcases he with h' | h' <;>
    first
      | (left; rw [h']; linarith)
      | (right; rw [h']; linarith)
      | (left; linarith)
      | (right; linarith)

/-- (d) -/
theorem field_d (hV : c.Valid) {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set) (hne : B ≠ B')
    (j : Fin 3) (hsub : B.ω j ⊆ B'.ω j) (k : Fin 3) (hk : k ≠ j) :
    Disjoint (dilate 3 (B.ω k)) (dilate 3 (B'.ω k)) := by
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  obtain ⟨s', i', hs', hi', rfl⟩ := hB'
  obtain ⟨-, h2, hc⟩ := nested_gap c hV hs hs' hi hi' hne j hsub
  have hℓ := ell_pos s
  rw [dilate_ω, dilate_ω]
  have e1 : (2 : ℝ) ^ (-(c.box s i).scale) = ell s := rfl
  have e2 : (2 : ℝ) ^ (-(c.box s' i').scale) = ell s' := rfl
  rw [e1, e2]
  have hα : 0 ≤ (jk k : ℝ) / (jk j : ℝ) := by
    have := jk_pos k; have := jk_pos j
    positivity
  exact d_core hℓ h2 hα hc (centre_rel c s i) (centre_rel c s' i') (beta_bound c hV j k hk)


theorem freqDir_pos (k : Fin 3) : 0 < freqDir k := by fin_cases k <;> simp [freqDir]

theorem freqDir_eq (k : Fin 3) : freqDir k = (jk k : ℝ) := by fin_cases k <;> simp [freqDir, jk]

theorem ωn_nonempty (B : Box) (k : Fin 3) : (B.ωn k).Nonempty := by
  have hℓ : 0 < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hf := freqDir_pos k
  refine ⟨(B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k, le_rfl, ?_⟩
  apply div_lt_div_of_pos_right _ hf
  linarith

theorem ωn_mono {B B' : Box} {k : Fin 3} (h : B.ω k ⊆ B'.ω k) : B.ωn k ⊆ B'.ωn k := by
  have hℓ : 0 < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hf := freqDir_pos k
  unfold Box.ω at h
  have := (Set.Ico_subset_Ico_iff (by linarith : B.centre k - (2 : ℝ) ^ (-B.scale) / 2 <
      B.centre k + (2 : ℝ) ^ (-B.scale) / 2)).1 h
  unfold Box.ωn
  apply Ico_subset_Ico
  · exact div_le_div_of_nonneg_right this.1 hf.le
  · exact div_le_div_of_nonneg_right this.2 hf.le

theorem ωn_subset_hull (B : Box) (k : Fin 3) : B.ωn k ⊆ B.hull := by
  have hℓ : 0 < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  intro x hx
  simp only [Box.ωn, Set.mem_Ico] at hx
  unfold Box.hull hullDil
  simp only [Set.mem_Icc]
  fin_cases k <;> simp only [freqDir, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_one] at hx ⊢
  · constructor
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (by linarith [hx.1]))
    · exact (le_max_left _ _).trans' ((le_max_left _ _).trans' (by linarith [hx.2]))
  · constructor
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith [hx.1]))
    · exact (le_max_left _ _).trans' ((le_max_right _ _).trans' (by linarith [hx.2]))
  · constructor
    · exact (min_le_right _ _).trans (by linarith [hx.1])
    · exact (le_max_right _ _).trans' (by linarith [hx.2])

theorem hull_le (hV : c.Valid) (s i : ℤ) :
    ell s * ((i : ℝ) + c.θ + c.lo0) ≤ ell s * ((i : ℝ) + c.θ + c.hi0) := by
  have hℓ := ell_pos s
  have h := hi0_eq c hV
  have : (0 : ℝ) ≤ c.hh := by
    have : (0 : ℤ) ≤ c.hh := by unfold hh; positivity
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_left (by linarith) hℓ.le

/-- (c): `ω_k(B) ⊆ ω_k(B')` implies nested dilated hulls (from (f)). -/
theorem field_c (hV : c.Valid) {B B' : Box} (hB : B ∈ c.set) (hB' : B' ∈ c.set) (k : Fin 3)
    (hsub : B.ω k ⊆ B'.ω k) {C : ℝ} (hC : 1 ≤ C) : dilate C B.hull ⊆ dilate C B'.hull := by
  by_cases hBB : B = B'
  · subst hBB; exact subset_rfl
  have hB0 := hB
  have hB'0 := hB'
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  obtain ⟨s', i', hs', hi', rfl⟩ := hB'
  obtain ⟨hlt, -, -⟩ := nested_gap c hV hs hs' hi hi' hBB k hsub
  have hnest : (c.box s i).hull ⊆ (c.box s' i').hull := by
    apply field_hull_nest c hV hB0 hB'0 hlt
    obtain ⟨x, hx⟩ := ωn_nonempty (c.box s i) k
    exact ⟨x, ωn_subset_hull _ k hx, ωn_subset_hull _ k (ωn_mono hsub hx)⟩
  have h1 := hnest
  rw [hull_box c hV, hull_box c hV] at h1 ⊢
  exact dilate_Icc_mono (hull_le c hV s i) h1 hC

theorem dilate_ωn (B : Box) (k : Fin 3) (C : ℝ) :
    dilate C (B.ωn k) = Ico (B.centre k / freqDir k - C * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k))
      (B.centre k / freqDir k + C * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k)) := by
  have hℓ : 0 < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hf := freqDir_pos k
  unfold Box.ωn
  rw [dilate_Ico (by apply div_lt_div_of_pos_right _ hf; linarith)]
  congr 1 <;> field_simp <;> ring

/-- (g): the normalized `4`-dilates of the three slot intervals are pairwise disjoint. -/
theorem field_g (hV : c.Valid) {B : Box} (hB : B ∈ c.set) (k k' : Fin 3) (hkk : k ≠ k') :
    Disjoint (dilate 4 (B.ωn k)) (dilate 4 (B.ωn k')) := by
  obtain ⟨s, i, hs, hi, rfl⟩ := hB
  obtain ⟨hd, he⟩ := db_e_real c hV
  have hℓ := ell_pos s
  rw [dilate_ωn, dilate_ωn]
  have e1 : (2 : ℝ) ^ (-(c.box s i).scale) = ell s := rfl
  rw [e1, box_centre_start, box_centre_start, freqDir_eq, freqDir_eq]
  apply ico_disjoint_of_dist
  have hj := jk_pos k
  have hj' := jk_pos k'
  unfold start
  fin_cases k <;> fin_cases k' <;> simp [jk, ok] at hkk ⊢ <;> apply le_abs_of <;>
    rcases hd with h | h <;> rcases he with h' | h' <;> (have hm := mul_le_mul_of_nonneg_left h hℓ.le) <;>
    first
      | (left; rw [h']; linarith)
      | (right; rw [h']; linarith)
      | (left; linarith)
      | (right; linarith)


/-- **V05-4: every valid class is a rank-1 box set** (`J = 16`), all fields (a)-(h), for all scale gaps. -/
theorem isRankOne_set (hV : c.Valid) : IsRankOne 16 c.set := by
  refine ⟨fun B hB B' hB' => by simpa using field_a c hB hB',
    fun B hB B' hB' k => field_grid c hB hB' k,
    fun B hB B' hB' hne hsc k => field_same_scale c hB hB' hne hsc k,
    fun B hB B' hB' k hsub => ?_,
    fun B hB B' hB' hne j hsub k hk => field_d c hV hB hB' hne j hsub k hk,
    fun B hB B' hB' hne hsc => field_hull_disjoint c hV hB hB' hne hsc,
    fun B hB B' hB' hlt hne => field_hull_nest c hV hB hB' hlt hne,
    fun B hB k k' hkk => field_g c hV hB k k' hkk,
    fun B hB => field_hull_length c hV hB⟩
  exact field_c c hV hB hB' k hsub (Real.one_le_rpow (by norm_num) (by positivity))

end WClass

end PrimeBHT.TimeFrequency.X2.Disc
