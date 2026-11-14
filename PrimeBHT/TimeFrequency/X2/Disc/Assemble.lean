module

public import PrimeBHT.TimeFrequency.X2.Disc.Fibre

/-!
# X2, node V05 (R4-4c): the bound of a finite double sum of Whitney pair terms

`finite_bound`: for finite `G ⊆ ℤ²` of `(k, n)` and finite `H ⊆ ℤ²` of `(n₁, n₂)`,
`‖Σ_{p ∈ G} Σ_{q ∈ H} c_{p} 1_D(q) pairTerm p q‖ₑ ≤ ofReal(2 |S| Σ_n w_n) · ofReal(C₀ CT) ‖F₁‖ ‖F₂‖ ‖F₃‖`, by partitioning the finite
index set into fibres `(n, d, n₁ mod 4, coarse class)` and using `fibre_bound` on each (at most `|S|` fibres per `n`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

noncomputable instance : DecidableEq WClass := Classical.decEq _

/-- The bounds of a valid selected class. -/
theorem pairClass_bounds (s n d : ℤ) (hd : 62 ≤ |d| ∧ |d| ≤ 258) :
    ((pairClass s n d (selT s n d)).t = 0 ∨ (pairClass s n d (selT s n d)).t = 1) ∧
      |(pairClass s n d (selT s n d)).db| ≤ 65 ∧
      ((pairClass s n d (selT s n d)).e = (pairClass s n d (selT s n d)).db ∨
        (pairClass s n d (selT s n d)).e = (pairClass s n d (selT s n d)).db + 1) := by
  have hV := pairClass_valid s n d hd
  exact ⟨hV.1, hV.2.2.1, hV.2.2.2.1⟩

/-- A finite box containing every class `pairClass s n d (selT s n d)`. -/
@[irreducible] def Scl : Finset WClass :=
  (Finset.Ico (0 : ℤ) 16 ×ˢ Finset.Ico (0 : ℤ) 1024 ×ˢ Finset.Icc (0 : ℤ) 1 ×ˢ Finset.Icc (-65 : ℤ) 65 ×ˢ
    Finset.Icc (-66 : ℤ) 66).image (fun x => (⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩ : WClass))

theorem mem_Scl_of {c : WClass} (h₀ : 0 ≤ c.s₀ ∧ c.s₀ < 16) (h₁ : 0 ≤ c.r ∧ c.r < 1024)
    (h₂ : 0 ≤ c.t ∧ c.t ≤ 1) (h₃ : -65 ≤ c.db ∧ c.db ≤ 65) (h₄ : -66 ≤ c.e ∧ c.e ≤ 66) : c ∈ Scl := by
  unfold Scl
  rw [Finset.mem_image]
  refine ⟨(c.s₀, c.r, c.t, c.db, c.e), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc]
  exact ⟨h₀, h₁, h₂, h₃, h₄⟩

theorem pairClass_mem_Scl (s n d : ℤ) (hd : 62 ≤ |d| ∧ |d| ≤ 258) :
    pairClass s n d (selT s n d) ∈ Scl := by
  obtain ⟨ht, hdb, he⟩ := pairClass_bounds s n d hd
  rw [pairClass_t] at ht
  rw [abs_le] at hdb
  apply mem_Scl_of
  · show 0 ≤ s % 16 ∧ s % 16 < 16; omega
  · show 0 ≤ i1 (selT s n d) n % 1024 ∧ i1 (selT s n d) n % 1024 < 1024; omega
  · show 0 ≤ selT s n d ∧ selT s n d ≤ 1; rcases ht with h | h <;> omega
  · omega
  · rcases he with h | h <;> omega

/-- The finite set of fibre labels `(d, n₁ mod 4, class)`. -/
@[irreducible] def Slab : Finset (ℤ × ℤ × WClass) :=
  (Finset.Icc (62 : ℤ) 258 ∪ Finset.Icc (-258 : ℤ) (-62)) ×ˢ Finset.Ico (0 : ℤ) 4 ×ˢ Scl

theorem mem_Slab {d ρ : ℤ} {cl : WClass} (hd : d ∈ Finset.Icc (62 : ℤ) 258 ∪ Finset.Icc (-258 : ℤ) (-62))
    (hρ : 0 ≤ ρ ∧ ρ < 4) (hcl : cl ∈ Scl) : (d, ρ, cl) ∈ Slab := by
  unfold Slab
  simp only [Finset.mem_product, Finset.mem_Ico]
  exact ⟨hd, hρ, hcl⟩

theorem mem_Slab_iff {d ρ : ℤ} {cl : WClass} : (d, ρ, cl) ∈ Slab ↔
    d ∈ Finset.Icc (62 : ℤ) 258 ∪ Finset.Icc (-258 : ℤ) (-62) ∧ (0 ≤ ρ ∧ ρ < 4) ∧ cl ∈ Scl := by
  unfold Slab
  simp only [Finset.mem_product, Finset.mem_Ico]

theorem abs_range_of_mem {d : ℤ} (h : d ∈ Finset.Icc (62 : ℤ) 258 ∪ Finset.Icc (-258 : ℤ) (-62)) :
    62 ≤ |d| ∧ |d| ≤ 258 := by
  simp only [Finset.mem_union, Finset.mem_Icc] at h
  rcases h with h | h
  · rw [abs_of_nonneg (by omega)]; omega
  · rw [abs_of_nonpos (by omega)]; omega

theorem mem_range_of_abs {d : ℤ} (h : 62 ≤ |d| ∧ |d| ≤ 258) :
    d ∈ Finset.Icc (62 : ℤ) 258 ∪ Finset.Icc (-258 : ℤ) (-62) := by
  simp only [Finset.mem_union, Finset.mem_Icc]
  rcases le_total 0 d with h0 | h0
  · rw [abs_of_nonneg h0] at h; left; omega
  · rw [abs_of_nonpos h0] at h; right; omega

section Vector

variable {P : ℕ} [NeZero P]

/-- **R4-4c.** -/
theorem finite_bound {u : ℝ} {𝔭 : Params} {C₀ : ℝ} (hM : ModelBoundAt u 𝔭 C₀) (hJ𝔭 : 𝔭.J = 16)
    (hC : 0 < 𝔭.C) {M₁ M₃ : ℝ} (h₁ : 0 ≤ M₁) (h₃ : 0 ≤ M₃)
    (hI₁ : IMStmt 𝔭 wphi (-1 / 2) (3 / 2) M₁) (hI₃ : IMStmt 𝔭 wphi3 (-3 / 2) (7 / 2) M₃)
    {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (hX : ∀ s v : ℤ, InX 𝔭 s v (tileCutoff η s v))
    {T : Form P} {CT : ℝ} (hT : FormBound u T CT) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ))
    (c : ℤ → ℤ → ℂ) (Bn : ℤ → ℝ) (hBn : ∀ n, 0 < Bn n) (hcB : ∀ k n, ‖c k n‖ ≤ Bn n)
    (hw : Summable fun n : ℤ => Bn n * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃) (G H : Finset (ℤ × ℤ)) :
    ‖∑ p ∈ G, ∑ q ∈ H, c p.1 p.2 * (if 62 ≤ |q.2 - q.1| ∧ |q.2 - q.1| ≤ 258 then
        pairTerm T f₁ f₂ f₃ p.1 p.2 q.1 (q.2 - q.1) else 0)‖ₑ ≤
      ENNReal.ofReal (2 * (Slab.card : ℝ) * ∑' n, Bn n * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃) *
        (ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x => yNorm 2 (tensorFun f₁ x)) 2 volume *
          eLpNorm (fun x => yNorm 2 (tensorFun f₂ x)) 2 volume *
          eLpNorm (fun x => yNorm u (tensorFun f₃ x)) ⊤ volume) := by
  classical
  set R : ℝ≥0∞ := ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x => yNorm 2 (tensorFun f₁ x)) 2 volume *
    eLpNorm (fun x => yNorm 2 (tensorFun f₂ x)) 2 volume *
    eLpNorm (fun x => yNorm u (tensorFun f₃ x)) ⊤ volume with hR
  set w : ℤ → ℝ := fun n => Bn n * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃ with hwdef
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    (mul_nonneg (mul_nonneg (mul_nonneg (hBn n).le (Qa_pos hC h₁ n).le) (Qa_pos hC h₁ n).le) (Qc_pos hC h₃).le)
  set H' : Finset (ℤ × ℤ) := H.filter (fun q => 62 ≤ |q.2 - q.1| ∧ |q.2 - q.1| ≤ 258) with hH'
  have hsum1 : ∑ p ∈ G, ∑ q ∈ H, c p.1 p.2 * (if 62 ≤ |q.2 - q.1| ∧ |q.2 - q.1| ≤ 258 then
        pairTerm T f₁ f₂ f₃ p.1 p.2 q.1 (q.2 - q.1) else 0) =
      ∑ x ∈ G ×ˢ H', c x.1.1 x.1.2 * pairTerm T f₁ f₂ f₃ x.1.1 x.1.2 x.2.1 (x.2.2 - x.2.1) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hH', Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  rw [hsum1]
  -- fibre map
  let lab : (ℤ × ℤ) × (ℤ × ℤ) → ℤ × (ℤ × ℤ × WClass) := fun x =>
    (x.1.2, (x.2.2 - x.2.1, x.2.1 % 4, pairClass (5 - x.1.1) x.2.1 (x.2.2 - x.2.1)
      (selT (5 - x.1.1) x.2.1 (x.2.2 - x.2.1))))
  let t : Finset (ℤ × (ℤ × ℤ × WClass)) := (G.image (fun p => p.2)) ×ˢ Slab
  have hmaps : ∀ x ∈ G ×ˢ H', lab x ∈ t := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨hxG, hxH⟩ := hx
    rw [hH', Finset.mem_filter] at hxH
    have hd := hxH.2
    simp only [t, lab, Finset.mem_product]
    refine ⟨Finset.mem_image.2 ⟨x.1, hxG, rfl⟩, ?_⟩
    exact mem_Slab (mem_range_of_abs hd) ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
      (pairClass_mem_Scl _ _ _ hd)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- bound each fibre
  have hfib : ∀ ℓ ∈ t, ‖∑ x ∈ (G ×ˢ H').filter (fun x => lab x = ℓ),
      c x.1.1 x.1.2 * pairTerm T f₁ f₂ f₃ x.1.1 x.1.2 x.2.1 (x.2.2 - x.2.1)‖ₑ ≤ ENNReal.ofReal (w ℓ.1) * (2 * R) := by
    intro ℓ hℓ
    obtain ⟨n, d, ρ, cl⟩ := ℓ
    simp only [t, Finset.mem_product] at hℓ
    have hd := abs_range_of_mem ((mem_Slab_iff.1 hℓ.2).1)
    set Fb := (G ×ˢ H').filter (fun x => lab x = (n, d, ρ, cl)) with hFb
    set Jf : Finset (ℤ × ℤ) := Fb.image (fun x => (x.1.1, x.2.1)) with hJf
    have hmem : ∀ x ∈ Fb, x.1.2 = n ∧ x.2.2 - x.2.1 = d ∧ x.2.1 % 4 = ρ ∧
        pairClass (5 - x.1.1) x.2.1 (x.2.2 - x.2.1) (selT (5 - x.1.1) x.2.1 (x.2.2 - x.2.1)) = cl := by
      intro x hx
      rw [hFb, Finset.mem_filter] at hx
      have := hx.2
      simp only [lab, Prod.mk.injEq] at this
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
    have hinj : Set.InjOn (fun x : (ℤ × ℤ) × (ℤ × ℤ) => (x.1.1, x.2.1)) ↑Fb := by
      intro x hx y hy hxy
      have hx' := hmem x (Finset.mem_coe.1 hx)
      have hy' := hmem y (Finset.mem_coe.1 hy)
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have e1 : x.1.2 = y.1.2 := by rw [hx'.1, hy'.1]
      have e2 : x.2.2 = y.2.2 := by omega
      exact Prod.ext (Prod.ext h1 e1) (Prod.ext h2 e2)
    have hsumFb : ∑ x ∈ Fb, c x.1.1 x.1.2 * pairTerm T f₁ f₂ f₃ x.1.1 x.1.2 x.2.1 (x.2.2 - x.2.1) =
        ∑ q ∈ Jf, c q.1 n * pairTerm T f₁ f₂ f₃ q.1 n q.2 d := by
      rw [hJf, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨h1, h2, -, -⟩ := hmem x hx
      simp only [h1, h2]
    rw [hsumFb]
    refine fibre_bound hM hJ𝔭 hC h₁ h₃ hI₁ hI₃ hη hX hT f₁ f₂ f₃ c (hBn n) n (hcB · n) d hd ρ cl Jf ?_
    intro q hq
    rw [hJf, Finset.mem_image] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    obtain ⟨h1, h2, h3, h4⟩ := hmem x hx
    refine ⟨h3, ?_⟩
    rw [h2] at h4
    exact h4
  calc ‖∑ ℓ ∈ t, ∑ x ∈ (G ×ˢ H').filter (fun x => lab x = ℓ),
        c x.1.1 x.1.2 * pairTerm T f₁ f₂ f₃ x.1.1 x.1.2 x.2.1 (x.2.2 - x.2.1)‖ₑ
      ≤ ∑ ℓ ∈ t, ‖∑ x ∈ (G ×ˢ H').filter (fun x => lab x = ℓ),
        c x.1.1 x.1.2 * pairTerm T f₁ f₂ f₃ x.1.1 x.1.2 x.2.1 (x.2.2 - x.2.1)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ ℓ ∈ t, ENNReal.ofReal (w ℓ.1) * (2 * R) := Finset.sum_le_sum hfib
    _ = (∑ ℓ ∈ t, ENNReal.ofReal (w ℓ.1)) * (2 * R) := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal (Slab.card * ∑' n, w n) * (2 * R) := by
        gcongr
        have h1 : ∑ ℓ ∈ t, ENNReal.ofReal (w ℓ.1) = (Slab.card : ℝ≥0∞) *
            ∑ n ∈ G.image (fun p => p.2), ENNReal.ofReal (w n) := by
          simp only [t, Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
          rw [← Finset.mul_sum]
        rw [h1, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        gcongr
        rw [ENNReal.ofReal_tsum_of_nonneg hw0 hw]
        exact ENNReal.sum_le_tsum _
    _ = ENNReal.ofReal (2 * (Slab.card : ℝ) * ∑' n, w n) * R := by
        have : 2 * (Slab.card : ℝ) * ∑' n, w n = 2 * (Slab.card * ∑' n, w n) := by ring
        rw [this, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

end Vector

end PrimeBHT.TimeFrequency.X2.Disc
