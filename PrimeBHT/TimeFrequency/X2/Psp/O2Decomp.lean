module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Theta

/-!
# X2, V13 O2 (g): the decomposition `T_σ F - G = D_out + D_fine` (MTT2 (d1)–(d6))

For the lattice scales `L = ovScales J s₀ lo W.1` and a layer scale `σ ∈ L`:

* `tele_lattice`: telescoping along the lattice, `Σ_{τ ∈ L, a ≤ τ < b} (f τ - f (τ + J)) = f a - f b` for `a ≤ b` in `L`;
* `exists_min_scale`: for `z ∈ Ẽ_σ` the finest scale `σ₁ ≤ σ` with `z ∈ Ẽ_{σ₁}` satisfies `z ∈ Ẽ_τ ⇔ σ₁ ≤ τ` (`τ ∈ L`);
* `tele_Pi`: `T_σF - Π̃F = - Σ_{τ ∈ L, τ < σ} 1_{Ẽ_τ} S_τ F` on `Ẽ_σ`;
* `decomp`: `T_σ F - G = D_out + D_fine` pointwise.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Telescoping along the lattice -/

section Tele

variable {V : Type*} [AddCommGroup V]

theorem mem_ovScales {J : ℕ} {s₀ lo hi τ : ℤ} : τ ∈ ovScales J s₀ lo hi ↔ (lo ≤ τ ∧ τ ≤ hi) ∧ (J : ℤ) ∣ τ - s₀ := by
  unfold ovScales; simp [Finset.mem_filter, Finset.mem_Icc]

/-- **Telescoping along the lattice.** -/
theorem tele_lattice {J : ℕ} (hJ : 0 < J) {s₀ lo hi : ℤ} (f : ℤ → V) {a b : ℤ}
    (ha : a ∈ ovScales J s₀ lo hi) (hb : b ∈ ovScales J s₀ lo hi) (hab : a ≤ b) :
    ∑ τ ∈ (ovScales J s₀ lo hi).filter (fun τ => a ≤ τ ∧ τ < b), (f τ - f (τ + (J : ℤ))) = f a - f b := by
  have hJ' : (0 : ℤ) < J := by exact_mod_cast hJ
  obtain ⟨⟨hlo_a, hhi_a⟩, hda⟩ := mem_ovScales.1 ha
  obtain ⟨⟨hlo_b, hhi_b⟩, hdb⟩ := mem_ovScales.1 hb
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n * J := by
    have hd : (J : ℤ) ∣ b - a := by
      have : b - a = (b - s₀) - (a - s₀) := by ring
      rw [this]; exact dvd_sub hdb hda
    obtain ⟨i, hi⟩ := hd
    have hi0 : 0 ≤ i := by
      by_contra h; push Not at h; nlinarith
    refine ⟨i.toNat, ?_⟩
    rw [Int.toNat_of_nonneg hi0]; linarith
  subst hn
  have hset : (ovScales J s₀ lo hi).filter (fun τ => a ≤ τ ∧ τ < a + n * J) =
      (Finset.range n).image (fun i : ℕ => a + (i : ℤ) * J) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hτ, h1, h2⟩
      obtain ⟨-, hdτ⟩ := mem_ovScales.1 hτ
      have hd : (J : ℤ) ∣ τ - a := by
        have : τ - a = (τ - s₀) - (a - s₀) := by ring
        rw [this]; exact dvd_sub hdτ hda
      obtain ⟨i, hi⟩ := hd
      have hi0 : 0 ≤ i := by
        by_contra h; push Not at h; nlinarith
      have hin : i < n := by
        by_contra h; push Not at h; nlinarith
      refine ⟨i.toNat, by omega, ?_⟩
      rw [Int.toNat_of_nonneg hi0]; linarith
    · rintro ⟨i, hi, rfl⟩
      have hi1 : (i : ℤ) < n := by exact_mod_cast hi
      refine ⟨?_, by nlinarith [Int.natCast_nonneg i], by nlinarith⟩
      rw [mem_ovScales]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · nlinarith [Int.natCast_nonneg i]
      · nlinarith
      · have : a + (i : ℤ) * J - s₀ = (a - s₀) + J * i := by ring
        rw [this]; exact dvd_add hda (dvd_mul_right _ _)
  rw [hset, Finset.sum_image]
  · have := Finset.sum_range_sub' (fun i : ℕ => f (a + (i : ℤ) * J)) n
    rw [show a + (n : ℤ) * J = a + ((n : ℕ) : ℤ) * J from rfl] at this
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    push_cast; ring
  · intro i _ j _ h
    have : (i : ℤ) * J = j * J := by linarith
    have := mul_right_cancel₀ hJ'.ne' this
    exact_mod_cast this

end Tele

/-! ## The finest scale -/

theorem mem_overlapA {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {σ : ℤ} {z : ℝ} :
    z ∈ overlapA TA W L σ ↔ z ∈ eTil TA W σ ∧ ∀ τ ∈ L, τ < σ → z ∉ eTil TA W τ := by
  unfold overlapA
  simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_filter, not_exists, not_and, exists_prop]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun τ hτ hlt hz => h2 τ ⟨hτ, hlt⟩ hz⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun τ hτ hz => h2 τ hτ.1 hτ.2 hz⟩

theorem exists_min_scale {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} (hLW : ∀ τ ∈ L, τ ≤ W.1) {σ : ℤ}
    (hσ : σ ∈ L) {z : ℝ} (hz : z ∈ eTil TA W σ) :
    ∃ σ₁ ∈ L, σ₁ ≤ σ ∧ z ∈ overlapA TA W L σ₁ ∧ ∀ τ ∈ L, (z ∈ eTil TA W τ ↔ σ₁ ≤ τ) := by
  set S := L.filter (fun τ => z ∈ eTil TA W τ) with hS
  have hne : S.Nonempty := ⟨σ, by simp [hS, hσ, hz]⟩
  set σ₁ := S.min' hne with hσ₁
  have hσ₁S : σ₁ ∈ S := Finset.min'_mem S hne
  have hσ₁L : σ₁ ∈ L := (Finset.mem_filter.1 hσ₁S).1
  have hσ₁z : z ∈ eTil TA W σ₁ := (Finset.mem_filter.1 hσ₁S).2
  have hmin : ∀ τ ∈ L, z ∈ eTil TA W τ → σ₁ ≤ τ := fun τ hτ hzτ =>
    Finset.min'_le S τ (by simp [hS, hτ, hzτ])
  refine ⟨σ₁, hσ₁L, hmin σ hσ hz, ?_, fun τ hτ => ⟨hmin τ hτ, fun hle => ?_⟩⟩
  · rw [mem_overlapA]
    exact ⟨hσ₁z, fun τ hτ hlt hzτ => absurd (hmin τ hτ hzτ) (not_le.2 hlt)⟩
  · exact eTil_mono hle (hLW τ hτ) hσ₁z

section Decomp

variable {P : ℕ} [NeZero P]

/-- `Σ_{x ∈ ∂Ẽ_τ} (e(θ z) φ_x(z)) c_x`: the bumps of scale `τ`. -/
def bumpAt (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) (cL cR : ℤ → ℝ → ZMod P → ℂ) (τ : ℤ) (z : ℝ) : ZMod P → ℂ :=
  (∑ x ∈ leftEnds TA W τ, (ovPhase θ z * ((leftPhi τ x z : ℝ) : ℂ)) • cL τ x) +
    ∑ x ∈ rightEnds TA W τ, (ovPhase θ z * ((rightPhi τ x z : ℝ) : ℂ)) • cR τ x

omit [NeZero P] in
theorem overlapBumps_eq_sum (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) (cL cR : ℤ → ℝ → ZMod P → ℂ)
    (z : ℝ) : overlapBumps TA W L θ cL cR z = ∑ τ ∈ L, bumpAt TA W θ cL cR τ z := by
  unfold overlapBumps bumpAt
  rw [Finset.sum_sigma, Finset.sum_sigma, ← Finset.sum_add_distrib]

/-- **Telescoping on `Ẽ_σ`**: `T_σ F - Π̃ F = - Σ_{τ ∈ L, τ < σ} 1_{Ẽ_τ} S_τ F`. -/
theorem tele_Pi {J : ℕ} (hJ : 0 < J) {s₀ lo : ℤ} (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ)
    {σ : ℤ} (hσ : σ ∈ ovScales J s₀ lo W.1) {z : ℝ} (hz : z ∈ eTil TA W σ) :
    tmult (lowSym θ σ) F z - overlapPi TA W (ovScales J s₀ lo W.1) θ F z =
      -∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), (eTil TA W τ).indicator (ovS J θ τ F) z := by
  have hLW : ∀ τ ∈ ovScales J s₀ lo W.1, τ ≤ W.1 := fun τ hτ => (mem_ovScales.1 hτ).1.2
  obtain ⟨σ₁, hσ₁L, hσ₁σ, hA, hiff⟩ := exists_min_scale hLW hσ hz
  rw [overlapPi_eq hσ₁L hA]
  have e1 : ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), (eTil TA W τ).indicator (ovS J θ τ F) z =
      ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => σ₁ ≤ τ ∧ τ < σ),
        (tmult (lowSym θ τ) F z - tmult (lowSym θ (τ + (J : ℤ))) F z) := by
    rw [← Finset.sum_filter_add_sum_filter_not ((ovScales J s₀ lo W.1).filter (fun τ => τ < σ)) (fun τ => σ₁ ≤ τ)]
    have h0 : ∑ τ ∈ ((ovScales J s₀ lo W.1).filter (fun τ => τ < σ)).filter (fun τ => ¬ σ₁ ≤ τ),
        (eTil TA W τ).indicator (ovS J θ τ F) z = 0 := by
      refine Finset.sum_eq_zero fun τ hτ => ?_
      simp only [Finset.mem_filter] at hτ
      have : z ∉ eTil TA W τ := fun h => hτ.2 ((hiff τ hτ.1.1).1 h)
      simp [Set.indicator_of_notMem this]
    rw [h0, add_zero]
    have hset : ((ovScales J s₀ lo W.1).filter (fun τ => τ < σ)).filter (fun τ => σ₁ ≤ τ) =
        (ovScales J s₀ lo W.1).filter (fun τ => σ₁ ≤ τ ∧ τ < σ) := by
      ext τ; simp only [Finset.mem_filter]; tauto
    rw [hset]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    simp only [Finset.mem_filter] at hτ
    have : z ∈ eTil TA W τ := (hiff τ hτ.1).2 hτ.2.1
    simp [Set.indicator_of_mem this, ovS]
  rw [e1, tele_lattice hJ (fun τ => tmult (lowSym θ τ) F z) hσ₁L hσ hσ₁σ]
  abel

/-- `D_out`: the part of `T_σ F - G` supported outside `Ẽ_σ` (terms (d1)–(d4)). -/
def Dout (J : ℕ) (s₀ lo : ℤ) (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ)
    (cL cR : ℤ → ℝ → ZMod P → ℂ) (σ : ℤ) (z : ℝ) : ZMod P → ℂ :=
  (eTil TA W σ)ᶜ.indicator (fun z => tmult (lowSym θ σ) F z - overlapPi TA W (ovScales J s₀ lo W.1) θ F z) z +
    ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ), bumpAt TA W θ cL cR τ z

/-- `D_fine`: the finer scales, `- Σ_{τ < σ} (1_{Ẽ_τ} S_τ F - bumps_τ)` (terms (d5), (d6)). -/
def Dfine (J : ℕ) (s₀ lo : ℤ) (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ)
    (cL cR : ℤ → ℝ → ZMod P → ℂ) (σ : ℤ) (z : ℝ) : ZMod P → ℂ :=
  -∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ),
    ((eTil TA W τ).indicator (ovS J θ τ F) z - bumpAt TA W θ cL cR τ z)

/-- **The decomposition `T_σ F - G = D_out + D_fine`.** -/
theorem decomp {J : ℕ} (hJ : 0 < J) {s₀ lo : ℤ} (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ)
    (cL cR : ℤ → ℝ → ZMod P → ℂ) {σ : ℤ} (hσ : σ ∈ ovScales J s₀ lo W.1) (z : ℝ) :
    tmult (lowSym θ σ) F z - overlapG TA W (ovScales J s₀ lo W.1) θ F cL cR z =
      Dout J s₀ lo TA W θ F cL cR σ z + Dfine J s₀ lo TA W θ F cL cR σ z := by
  have hLW : ∀ τ ∈ ovScales J s₀ lo W.1, τ ≤ W.1 := fun τ hτ => (mem_ovScales.1 hτ).1.2
  have hσW : σ ≤ W.1 := hLW σ hσ
  unfold overlapG Dout Dfine
  rw [overlapBumps_eq_sum]
  rw [← Finset.sum_filter_add_sum_filter_not (ovScales J s₀ lo W.1) (fun τ => τ < σ)]
  have hnot : (ovScales J s₀ lo W.1).filter (fun τ => ¬ τ < σ) = (ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ) :=
    Finset.filter_congr fun τ _ => not_lt
  rw [hnot, Finset.sum_sub_distrib]
  by_cases hz : z ∈ eTil TA W σ
  · have h1 := tele_Pi hJ TA W θ F hσ hz
    have e0 : (eTil TA W σ)ᶜ.indicator (fun z => tmult (lowSym θ σ) F z - overlapPi TA W (ovScales J s₀ lo W.1) θ F z) z = 0 :=
      Set.indicator_of_notMem (by simpa using hz) _
    rw [e0]
    have : tmult (lowSym θ σ) F z - (overlapPi TA W (ovScales J s₀ lo W.1) θ F z -
        (∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), bumpAt TA W θ cL cR τ z +
          ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ), bumpAt TA W θ cL cR τ z)) =
        (tmult (lowSym θ σ) F z - overlapPi TA W (ovScales J s₀ lo W.1) θ F z) +
          (∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), bumpAt TA W θ cL cR τ z +
            ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ), bumpAt TA W θ cL cR τ z) := by abel
    rw [this, h1]
    abel
  · have hzc : z ∈ (eTil TA W σ)ᶜ := hz
    rw [Set.indicator_of_mem hzc]
    have h0 : ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), (eTil TA W τ).indicator (ovS J θ τ F) z = 0 := by
      refine Finset.sum_eq_zero fun τ hτ => ?_
      simp only [Finset.mem_filter] at hτ
      have : z ∉ eTil TA W τ := fun h => hz (eTil_mono hτ.2.le hσW h)
      simp [Set.indicator_of_notMem this]
    rw [h0]
    abel

end Decomp

end PrimeBHT.TimeFrequency.X2
