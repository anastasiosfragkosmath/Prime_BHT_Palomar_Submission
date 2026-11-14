module

public import PrimeBHT.TimeFrequency.X2.Disc.Boxes

/-!
# X2, node V05-4 (selection): every Whitney pair lands in a valid class

For a Whitney pair `(n₁, n₂ = n₁ + d)` with `62 ≤ |d| ≤ 258` (Whitney exponent `a = 7`) at box scale `s`, and a grid
offset `θ = t/3`, `t ∈ {0, 1}`, the box has slot starts `i₁ = ⌊n₁/4 - θ⌋`, `i₂ = ⌊n₂/4 - θ⌋`, `i₃ = ⌊(n₁+n₂)/4 - 2θ⌋`
(`ω_k ∋ ℓ · (bump origin)`, `ℓ = 4 b`).  `pairClass s n₁ d t` is the class (finitely many values) containing it.
`selT` selects `θ = 0` if the class is valid, else `θ = 1/3`; `pairClass_valid` shows that the selected class is
valid, for every pair (exhaustively checked by exact arithmetic for all residues, `docs/audits`, and proved here by
`omega`).
-/

@[expose] public noncomputable section

open Set

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

open Classical in
/-- `⌊n/4 - t/3⌋`. -/
def i1 (t n : ℤ) : ℤ := (3 * n - 4 * t) / 12

/-- `⌊(n + m)/4 - 2t/3⌋`. -/
def i3 (t n m : ℤ) : ℤ := (3 * (n + m) - 8 * t) / 12

/-- The class of the Whitney pair `(n₁, n₁ + d)` at box scale `s` with offset `t/3`. -/
def pairClass (s n₁ d t : ℤ) : WClass :=
  ⟨s % 16, i1 t n₁ % 1024, t, i1 t (n₁ + d) - i1 t n₁, i3 t n₁ (n₁ + d) - 2 * i1 t n₁⟩

/-- The box of the Whitney pair. -/
def pairBox (s n₁ d t : ℤ) : Box := (pairClass s n₁ d t).box s (i1 t n₁)

theorem pairClass_t (s n d t : ℤ) : (pairClass s n d t).t = t := rfl
theorem pairClass_r (s n d t : ℤ) : (pairClass s n d t).r = i1 t n % 1024 := rfl
theorem pairClass_db (s n d t : ℤ) : (pairClass s n d t).db = i1 t (n + d) - i1 t n := rfl
theorem pairClass_e (s n d t : ℤ) : (pairClass s n d t).e = i3 t n (n + d) - 2 * i1 t n := rfl

theorem pairBox_mem (s n₁ d t : ℤ) : pairBox s n₁ d t ∈ (pairClass s n₁ d t).set := by
  refine ⟨s, i1 t n₁, ?_, ?_, rfl⟩
  · show (16 : ℤ) ∣ s - s % 16
    exact ⟨s / 16, by omega⟩
  · show (1024 : ℤ) ∣ i1 t n₁ - i1 t n₁ % 1024
    exact ⟨i1 t n₁ / 1024, by omega⟩

namespace WClass

/-- A box of a class determines its scale and index. -/
theorem box_injective (c : WClass) {s i s' i' : ℤ} (h : c.box s i = c.box s' i') : s = s' ∧ i = i' := by
  have hs : s = s' := congrArg Box.scale h
  subst hs
  refine ⟨rfl, ?_⟩
  have h0 := congrArg (fun B : Box => B.centre 0) h
  simp only [box_centre0] at h0
  have hℓ := ell_pos s
  have : (i : ℝ) = i' := by
    have := mul_left_cancel₀ hℓ.ne' h0
    linarith
  exact_mod_cast this

theorem valid_of_pos {c : WClass} (ht : c.t = 0 ∨ c.t = 1) (h1 : 15 ≤ c.db) (h2 : c.db ≤ 65)
    (he : c.e = c.db ∨ c.e = c.db + 1)
    (hw : ∀ w : ℤ, ¬ (0 ≤ 2048 * w + 127 + 682 * c.t - 2 * c.r ∧
      2048 * w + 127 + 682 * c.t - 2 * c.r ≤ 2 * (c.db + 128))) : c.Valid := by
  refine ⟨ht, by rw [abs_of_nonneg (by omega)]; exact h1, by rw [abs_of_nonneg (by omega)]; exact h2, he, ?_⟩
  intro w
  have hq : c.q = -127 := by unfold q; rw [ite_eq_left (by omega)]
  have hh : c.hh = c.db + 128 := by unfold hh; rw [abs_of_nonneg (by omega)]
  rw [hq, hh]
  have := hw w
  intro ⟨a, b⟩
  apply this
  constructor <;> linarith

theorem valid_of_neg {c : WClass} (ht : c.t = 0 ∨ c.t = 1) (h1 : c.db ≤ -15) (h2 : -65 ≤ c.db)
    (he : c.e = c.db ∨ c.e = c.db + 1)
    (hw : ∀ w : ℤ, ¬ (0 ≤ 2048 * w - (2 * c.db - 127) + 682 * c.t - 2 * c.r ∧
      2048 * w - (2 * c.db - 127) + 682 * c.t - 2 * c.r ≤ 2 * (128 - c.db))) : c.Valid := by
  refine ⟨ht, by rw [abs_of_nonpos (by omega)]; omega, by rw [abs_of_nonpos (by omega)]; omega, he, ?_⟩
  intro w
  have hq : c.q = 2 * c.db - 127 := by unfold q; rw [ite_eq_right (by omega)]
  have hh : c.hh = 128 - c.db := by unfold hh; rw [abs_of_nonpos (by omega)]; ring
  rw [hq, hh]
  exact hw w

end WClass


open Classical in
/-- The offset selection rule: `θ = 0` if the class of the pair with `θ = 0` is valid, else `θ = 1/3`. -/
def selT (s n₁ d : ℤ) : ℤ := if (pairClass s n₁ d 0).Valid then 0 else 1

/-- **Selection.**  For every Whitney pair with `62 ≤ |d| ≤ 258`, every scale and every `n₁`, the class selected by
the rule is valid.  (Exhaustively checked by exact arithmetic over all residues; proved here by `omega`.) -/
theorem pairClass_valid (s n₁ d : ℤ) (hd : 62 ≤ |d| ∧ |d| ≤ 258) :
    (pairClass s n₁ d (selT s n₁ d)).Valid := by
  by_cases h0 : (pairClass s n₁ d 0).Valid
  · have : selT s n₁ d = 0 := by unfold selT; rw [ite_eq_left h0]
    rw [this]; exact h0
  · have hsel : selT s n₁ d = 1 := by unfold selT; rw [ite_eq_right h0]
    rw [hsel]
    rcases le_or_gt 0 d with hd0 | hd0
    · rw [abs_of_nonneg hd0] at hd
      -- d ≥ 62
      have hnot : ¬ ∀ w : ℤ, ¬ (0 ≤ 2048 * w + 127 + 682 * (pairClass s n₁ d 0).t - 2 * (pairClass s n₁ d 0).r ∧
          2048 * w + 127 + 682 * (pairClass s n₁ d 0).t - 2 * (pairClass s n₁ d 0).r ≤
            2 * ((pairClass s n₁ d 0).db + 128)) := by
        intro hall
        apply h0
        apply WClass.valid_of_pos _ _ _ _ hall
        · exact Or.inl rfl
        · simp only [pairClass_db, i1]; omega
        · simp only [pairClass_db, i1]; omega
        · simp only [pairClass_db, pairClass_e, i1, i3]; omega
      obtain ⟨w₀, hw₀⟩ := not_forall.1 hnot
      have hw₀' := not_not.1 hw₀
      apply WClass.valid_of_pos
      · exact Or.inr rfl
      · simp only [pairClass_db, i1]; omega
      · simp only [pairClass_db, i1]; omega
      · simp only [pairClass_db, pairClass_e, i1, i3]; omega
      · intro w ⟨a, b⟩
        simp only [pairClass_t, pairClass_r, pairClass_db, i1] at hw₀' a b
        omega
    · rw [abs_of_neg hd0] at hd
      have hnot : ¬ ∀ w : ℤ, ¬ (0 ≤ 2048 * w - (2 * (pairClass s n₁ d 0).db - 127) +
          682 * (pairClass s n₁ d 0).t - 2 * (pairClass s n₁ d 0).r ∧
          2048 * w - (2 * (pairClass s n₁ d 0).db - 127) + 682 * (pairClass s n₁ d 0).t -
            2 * (pairClass s n₁ d 0).r ≤ 2 * (128 - (pairClass s n₁ d 0).db)) := by
        intro hall
        apply h0
        apply WClass.valid_of_neg _ _ _ _ hall
        · exact Or.inl rfl
        · simp only [pairClass_db, i1]; omega
        · simp only [pairClass_db, i1]; omega
        · simp only [pairClass_db, pairClass_e, i1, i3]; omega
      obtain ⟨w₀, hw₀⟩ := not_forall.1 hnot
      have hw₀' := not_not.1 hw₀
      apply WClass.valid_of_neg
      · exact Or.inr rfl
      · simp only [pairClass_db, i1]; omega
      · simp only [pairClass_db, i1]; omega
      · simp only [pairClass_db, pairClass_e, i1, i3]; omega
      · intro w ⟨a, b⟩
        simp only [pairClass_t, pairClass_r, pairClass_db, i1] at hw₀' a b
        omega


/-- Within a fixed residue `n₁ mod 4` and offset, `n₁ ↦ ⌊n₁/4 - t/3⌋` is injective (so inside a fine class
`(class, n₁ mod 4, d)` the box determines the Whitney pair). -/
theorem i1_injective (t n n' : ℤ) (h : n % 4 = n' % 4) (h1 : i1 t n = i1 t n') : n = n' := by
  unfold i1 at h1; omega

/-! ### Support geometry of the bumps -/

theorem i1_bounds (t n : ℤ) : 12 * i1 t n ≤ 3 * n - 4 * t ∧ 3 * n - 4 * t < 12 * i1 t n + 12 := by
  unfold i1; omega

theorem i3_bounds (t n m : ℤ) :
    12 * i3 t n m ≤ 3 * (n + m) - 8 * t ∧ 3 * (n + m) - 8 * t < 12 * i3 t n m + 12 := by
  unfold i3; omega

theorem pairBox_centre0 (s n₁ d t : ℤ) :
    (pairBox s n₁ d t).centre 0 = ell s * ((i1 t n₁ : ℝ) + (t : ℝ) / 3 + 1 / 2) := by
  unfold pairBox
  rw [WClass.box_centre0]
  unfold WClass.θ
  rw [pairClass_t]

theorem pairBox_centre1 (s n₁ d t : ℤ) :
    (pairBox s n₁ d t).centre 1 = ell s * ((i1 t (n₁ + d) : ℝ) + (t : ℝ) / 3 + 1 / 2) := by
  unfold pairBox
  rw [WClass.box_centre1]
  unfold WClass.θ
  rw [pairClass_t, pairClass_db]
  push_cast
  ring

theorem pairBox_centre2 (s n₁ d t : ℤ) :
    (pairBox s n₁ d t).centre 2 = ell s * ((i3 t n₁ (n₁ + d) : ℝ) + 2 * (t : ℝ) / 3 + 1 / 2) := by
  unfold pairBox
  rw [WClass.box_centre2]
  unfold WClass.θ
  rw [pairClass_t, pairClass_e]
  push_cast
  ring

/-- The supports of the three bumps of the pair `(n₁, n₁ + d)` (bump scale `b = ℓ/4`: `φ(·/b - n₁)` lives on
`b[n₁ - 1/2, n₁ + 3/2]`, likewise `n₂`, and `φ₃(·/b - n₁ - n₂)` on `b[n₁ + n₂ - 3/2, n₁ + n₂ + 7/2]`) lie in
`(11/8) ℓ`-neighbourhoods of the slot centres, i.e. in `β ω_k` for `β = 11/4`. -/
theorem pairBox_support (s n₁ d t : ℤ) :
    let ℓ := ell s
    let b := ℓ / 4
    ((pairBox s n₁ d t).centre 0 - 11 * ℓ / 8 ≤ b * ((n₁ : ℝ) - 1 / 2) ∧
        b * ((n₁ : ℝ) + 3 / 2) ≤ (pairBox s n₁ d t).centre 0 + 11 * ℓ / 8) ∧
      ((pairBox s n₁ d t).centre 1 - 11 * ℓ / 8 ≤ b * (((n₁ + d : ℤ) : ℝ) - 1 / 2) ∧
        b * (((n₁ + d : ℤ) : ℝ) + 3 / 2) ≤ (pairBox s n₁ d t).centre 1 + 11 * ℓ / 8) ∧
      ((pairBox s n₁ d t).centre 2 - 11 * ℓ / 8 ≤ b * (((n₁ + (n₁ + d) : ℤ) : ℝ) - 3 / 2) ∧
        b * (((n₁ + (n₁ + d) : ℤ) : ℝ) + 7 / 2) ≤ (pairBox s n₁ d t).centre 2 + 11 * ℓ / 8) := by
  intro ℓ b
  have hℓ : 0 < ℓ := ell_pos s
  obtain ⟨a1, a2⟩ := i1_bounds t n₁
  obtain ⟨b1, b2⟩ := i1_bounds t (n₁ + d)
  obtain ⟨c1, c2⟩ := i3_bounds t n₁ (n₁ + d)
  have a1' : (12 : ℝ) * (i1 t n₁ : ℝ) ≤ 3 * (n₁ : ℝ) - 4 * (t : ℝ) := by exact_mod_cast a1
  have a2' : 3 * (n₁ : ℝ) - 4 * (t : ℝ) < 12 * (i1 t n₁ : ℝ) + 12 := by exact_mod_cast a2
  have b1' : (12 : ℝ) * (i1 t (n₁ + d) : ℝ) ≤ 3 * ((n₁ : ℝ) + d) - 4 * (t : ℝ) := by exact_mod_cast b1
  have b2' : 3 * ((n₁ : ℝ) + d) - 4 * (t : ℝ) < 12 * (i1 t (n₁ + d) : ℝ) + 12 := by exact_mod_cast b2
  have c1' : (12 : ℝ) * (i3 t n₁ (n₁ + d) : ℝ) ≤ 3 * ((n₁ : ℝ) + ((n₁ : ℝ) + d)) - 8 * (t : ℝ) := by
    exact_mod_cast c1
  have c2' : 3 * ((n₁ : ℝ) + ((n₁ : ℝ) + d)) - 8 * (t : ℝ) < 12 * (i3 t n₁ (n₁ + d) : ℝ) + 12 := by
    exact_mod_cast c2
  rw [pairBox_centre0, pairBox_centre1, pairBox_centre2]
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show ell s * _ - 11 * ell s / 8 ≤ ell s / 4 * _
    nlinarith [mul_le_mul_of_nonneg_left (show (i1 t n₁ : ℝ) + (t : ℝ) / 3 + 1 / 2 - 11 / 8 ≤
      ((n₁ : ℝ) - 1 / 2) / 4 by linarith) hℓ.le]
  · show ell s / 4 * _ ≤ ell s * _ + 11 * ell s / 8
    nlinarith [mul_le_mul_of_nonneg_left (show ((n₁ : ℝ) + 3 / 2) / 4 ≤ (i1 t n₁ : ℝ) + (t : ℝ) / 3 + 1 / 2 +
      11 / 8 by linarith) hℓ.le]
  · show ell s * _ - 11 * ell s / 8 ≤ ell s / 4 * _
    nlinarith [mul_le_mul_of_nonneg_left (show (i1 t (n₁ + d) : ℝ) + (t : ℝ) / 3 + 1 / 2 - 11 / 8 ≤
      (((n₁ : ℝ) + d) - 1 / 2) / 4 by linarith) hℓ.le]
  · show ell s / 4 * _ ≤ ell s * _ + 11 * ell s / 8
    nlinarith [mul_le_mul_of_nonneg_left (show (((n₁ : ℝ) + d) + 3 / 2) / 4 ≤ (i1 t (n₁ + d) : ℝ) +
      (t : ℝ) / 3 + 1 / 2 + 11 / 8 by linarith) hℓ.le]
  · show ell s * _ - 11 * ell s / 8 ≤ ell s / 4 * _
    nlinarith [mul_le_mul_of_nonneg_left (show (i3 t n₁ (n₁ + d) : ℝ) + 2 * (t : ℝ) / 3 + 1 / 2 - 11 / 8 ≤
      (((n₁ : ℝ) + ((n₁ : ℝ) + d)) - 3 / 2) / 4 by linarith) hℓ.le]
  · show ell s / 4 * _ ≤ ell s * _ + 11 * ell s / 8
    nlinarith [mul_le_mul_of_nonneg_left (show (((n₁ : ℝ) + ((n₁ : ℝ) + d)) + 7 / 2) / 4 ≤
      (i3 t n₁ (n₁ + d) : ℝ) + 2 * (t : ℝ) / 3 + 1 / 2 + 11 / 8 by linarith) hℓ.le]

end PrimeBHT.TimeFrequency.X2.Disc
