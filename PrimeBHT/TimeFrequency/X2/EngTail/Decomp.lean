module

public import PrimeBHT.TimeFrequency.X2.CZ.WeakType
public import PrimeBHT.TimeFrequency.X2.EngTail.FamSum

/-!
# X2, node B5: the Calderón-Zygmund step for a kernel with a pointwise atom bound

For a bounded measurable kernel `K`, a vector function `F` and the Calderón-Zygmund intervals `Q_i = [a_i, b_i)` of
`CZ.exists_cz_intervals`, if `‖K(x, u) - K(x, c_i)‖ ≤ A₁ |Q_i|⁻¹ (1 + |x - c_i|/|Q_i|)^{-2}` for `u ∈ Q_i`, then pointwise
`‖K * F(x)‖ ≤ ‖K * g(x)‖ + ∑_i 4 λ A₁ (1 + |x - c_i|/|Q_i|)^{-2}` (`g` the good part, `∫_{Q_i} ‖F‖ ≤ 2 λ |Q_i|`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Step

variable {P : ℕ} [NeZero P] {ι : Type} [Countable ι] {a b : ι → ℝ} {F : ℝ → ZMod P → ℂ}
  {K : ℝ → ℝ → ℂ} {B s lam A₁ : ℝ}

/-- **Pointwise Calderón-Zygmund step**: `‖K * F‖_X ≤ ‖K * g‖_X + ∑_i 4 λ A₁ (1 + |x - c_i|/|Q_i|)^{-2}`. -/
theorem cz_step (hs : 1 < s) (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ B)
    (hab : ∀ i, a i < b i) (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (hG : Integrable (fun u => yNorm s (F u)) volume) (hA₁ : 0 ≤ A₁)
    (hQ : ∀ i, ∫ u in Ico (a i) (b i), yNorm s (F u) ≤ 2 * lam * (b i - a i))
    (hsm : ∀ i x, ∀ u ∈ Ico (a i) (b i), ‖K x u - K x (CZ.ctr a b i)‖ ≤
      A₁ * ((b i - a i)⁻¹ * (1 + |x - CZ.ctr a b i| / (b i - a i)) ^ (-(2 : ℝ)))) (x : ℝ) :
    ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => F u y) x)) ≤
      ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => CZ.goodPart a b F u y) x)) +
        famPhiT (CZ.ctr a b) (fun i => b i - a i) (fun _ => 4 * lam * A₁) x := by
  have hs0 : 0 < s := by linarith
  set g : ℝ → ZMod P → ℂ := CZ.goodPart a b F with hg
  have hgi : ∀ y, Integrable fun u => g u y := fun y => CZ.integrable_goodPart hab hd hFm hFi y
  have hbi : ∀ y, Integrable fun u => CZ.badPart a b F u y := fun y => CZ.integrable_badPart hab hd hFm hFi y
  have hsplit : ∀ y, CZ.kop K (fun u => F u y) x =
      CZ.kop K (fun u => g u y) x + CZ.kop K (fun u => CZ.badPart a b F u y) x := by
    intro y
    unfold CZ.kop
    rw [← integral_add (CZ.integrable_kernel_mul hKm hKb (hgi y) x)
      (CZ.integrable_kernel_mul hKm hKb (hbi y) x)]
    congr 1; ext u
    simp only [hg, CZ.goodPart]; ring
  have htri : yNorm s (fun y => CZ.kop K (fun u => F u y) x) ≤
      yNorm s (fun y => CZ.kop K (fun u => g u y) x) +
        yNorm s (fun y => CZ.kop K (fun u => CZ.badPart a b F u y) x) := by
    have : (fun y => CZ.kop K (fun u => F u y) x) =
        (fun y => CZ.kop K (fun u => g u y) x) + (fun y => CZ.kop K (fun u => CZ.badPart a b F u y) x) := by
      ext y; exact hsplit y
    rw [this]; exact CZ.yNorm_add_le hs.le _ _
  have hsm' := CZ.summable_yNorm_kconv_atom hs hKm hKb hab hd hFm hFi hG x
  have hbad : yNorm s (fun y => CZ.kop K (fun u => CZ.badPart a b F u y) x) ≤
      ∑' i, yNorm s (fun y => CZ.kop K (fun u => CZ.atom a b F i u y) x) :=
    CZ.yNorm_tsum_le hs.le _ _ (fun y => CZ.hasSum_kconv_atom hKm hKb hab hd hFm hFi x y) hsm'
  -- each atom
  have hat : ∀ i, yNorm s (fun y => CZ.kop K (fun u => CZ.atom a b F i u y) x) ≤
      4 * lam * A₁ * famK (CZ.ctr a b i) (b i - a i) x := by
    intro i
    have hl : (0 : ℝ) < b i - a i := sub_pos.2 (hab i)
    have hΦ := CZ.integrableOn_yNorm_atom_sub hs hFm hG i (a := a) (b := b)
    set Wx : ℝ := (b i - a i)⁻¹ * (1 + |x - CZ.ctr a b i| / (b i - a i)) ^ (-(2 : ℝ)) with hWx
    have hW0 : 0 ≤ Wx := by simp only [hWx]; positivity
    calc yNorm s (fun y => CZ.kop K (fun u => CZ.atom a b F i u y) x)
        ≤ ∫ u in Ico (a i) (b i), ‖K x u - K x (CZ.ctr a b i)‖ *
            yNorm s (fun y => F u y - CZ.meanVal a b F i y) :=
          CZ.yNorm_kconv_atom_le hs hKm hKb hab hFm hFi hG i x
      _ ≤ ∫ u in Ico (a i) (b i), (A₁ * Wx) * yNorm s (fun y => F u y - CZ.meanVal a b F i y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun u =>
            mul_nonneg (norm_nonneg _) (CZ.yNorm_nonneg s _)) (hΦ.const_mul _) ?_
          refine (ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun u hu => ?_)
          exact mul_le_mul_of_nonneg_right (hsm i x u hu) (CZ.yNorm_nonneg s _)
      _ = (A₁ * Wx) * ∫ u in Ico (a i) (b i), yNorm s (fun y => F u y - CZ.meanVal a b F i y) := by
          rw [integral_const_mul]
      _ ≤ (A₁ * Wx) * (2 * ∫ u in Ico (a i) (b i), yNorm s (F u)) :=
          mul_le_mul_of_nonneg_left (CZ.integral_yNorm_atom_le hs hab hFm hFi hG i) (by positivity)
      _ ≤ (A₁ * Wx) * (2 * (2 * lam * (b i - a i))) := by
          gcongr; exact hQ i
      _ = 4 * lam * A₁ * famK (CZ.ctr a b i) (b i - a i) x := by
          simp only [hWx, famK]
          field_simp
          ring
  -- the ENNReal assembly
  have h1 : ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => CZ.badPart a b F u y) x)) ≤
      ∑' i, ENNReal.ofReal (4 * lam * A₁ * famK (CZ.ctr a b i) (b i - a i) x) := by
    calc _ ≤ ENNReal.ofReal (∑' i, yNorm s (fun y => CZ.kop K (fun u => CZ.atom a b F i u y) x)) :=
          ENNReal.ofReal_le_ofReal hbad
      _ = ∑' i, ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => CZ.atom a b F i u y) x)) :=
          ENNReal.ofReal_tsum_of_nonneg (fun i => CZ.yNorm_nonneg s _) hsm'
      _ ≤ _ := ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hat i)
  calc ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => F u y) x))
      ≤ ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => g u y) x) +
          yNorm s (fun y => CZ.kop K (fun u => CZ.badPart a b F u y) x)) := ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => g u y) x)) +
          ENNReal.ofReal (yNorm s (fun y => CZ.kop K (fun u => CZ.badPart a b F u y) x)) :=
        ENNReal.ofReal_add (CZ.yNorm_nonneg s _) (CZ.yNorm_nonneg s _)
    _ ≤ _ := by
        unfold famPhiT
        exact add_le_add le_rfl h1

/-- **The good part in `L^q`**: `∫ ‖g‖_X^q ≤ (2λ)^{q-1} ∫ ‖F‖_X` (`‖g‖_X ≤ 2λ` a.e., `∫ ‖g‖_X ≤ ∫ ‖F‖_X`). -/
theorem lintegral_good_rpow_le (hs : 1 < s) {q : ℝ} (hq : 1 < q) (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFi : ∀ y, Integrable fun u => F u y) (hG : Integrable (fun u => yNorm s (F u)) volume) {lam : ℝ}
    (hlam : 0 < lam) (hQ : ∀ i, ∫ u in Ico (a i) (b i), yNorm s (F u) ≤ 2 * lam * (b i - a i))
    (hout : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ⋃ i, Ico (a i) (b i) → yNorm s (F u) ≤ lam) :
    ∫⁻ u, ENNReal.ofReal (yNorm s (CZ.goodPart a b F u)) ^ q ≤
      ENNReal.ofReal ((2 * lam) ^ (q - 1)) * ENNReal.ofReal (∫ u, yNorm s (F u)) := by
  have hq0 : 0 < q := by linarith
  have hbd := CZ.yNorm_goodPart_le hs hab hd hFi hG hlam hQ hout
  calc ∫⁻ u, ENNReal.ofReal (yNorm s (CZ.goodPart a b F u)) ^ q
      ≤ ∫⁻ u, ENNReal.ofReal ((2 * lam) ^ (q - 1)) * ENNReal.ofReal (yNorm s (CZ.goodPart a b F u)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hbd] with u hu
        rw [ENNReal.ofReal_rpow_of_nonneg (CZ.yNorm_nonneg s _) hq0.le,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hx0 := CZ.yNorm_nonneg s (CZ.goodPart a b F u)
        calc yNorm s (CZ.goodPart a b F u) ^ q = yNorm s (CZ.goodPart a b F u) ^ (q - 1) *
              yNorm s (CZ.goodPart a b F u) := by
              rw [← Real.rpow_add_one' hx0 (by linarith)]; congr 1; ring
          _ ≤ (2 * lam) ^ (q - 1) * yNorm s (CZ.goodPart a b F u) := by
              refine mul_le_mul_of_nonneg_right ?_ hx0
              exact Real.rpow_le_rpow hx0 hu (by linarith)
    _ = ENNReal.ofReal ((2 * lam) ^ (q - 1)) * ∫⁻ u, ENNReal.ofReal (yNorm s (CZ.goodPart a b F u)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 * lam) ^ (q - 1)) * ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) :=
        mul_le_mul' le_rfl (CZ.lintegral_goodPart_le hs hab hd hFi hG)
    _ = ENNReal.ofReal ((2 * lam) ^ (q - 1)) * ENNReal.ofReal (∫ u, yNorm s (F u)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hG (Eventually.of_forall fun u => CZ.yNorm_nonneg s _)]

/-- The good part is bounded by `1` everywhere if `F` is. -/
theorem yNorm_goodPart_le_one (hs : 1 < s) (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFi : ∀ y, Integrable fun u => F u y) (hG : Integrable (fun u => yNorm s (F u)) volume)
    (h1 : ∀ u, yNorm s (F u) ≤ 1) (u : ℝ) : yNorm s (CZ.goodPart a b F u) ≤ 1 := by
  by_cases h : ∃ j, u ∈ Ico (a j) (b j)
  · obtain ⟨j, hj⟩ := h
    have hfun : CZ.goodPart a b F u = CZ.meanVal a b F j := by
      ext y; exact CZ.goodPart_of_mem hd hj y
    rw [hfun]
    have hl : (0 : ℝ) < b j - a j := sub_pos.2 (hab j)
    have h2 := CZ.yNorm_meanVal_le hs hab hFi hG j
    have h3 : ∫ u in Ico (a j) (b j), yNorm s (F u) ≤ b j - a j := by
      calc ∫ u in Ico (a j) (b j), yNorm s (F u) ≤ ∫ u in Ico (a j) (b j), (1 : ℝ) :=
            setIntegral_mono_on hG.integrableOn (integrableOn_const (by simp)) measurableSet_Ico
              (fun u _ => h1 u)
        _ = b j - a j := by
            rw [setIntegral_const, Real.volume_real_Ico_of_le (hab j).le, smul_eq_mul, mul_one]
    nlinarith [CZ.yNorm_nonneg s (CZ.meanVal a b F j)]
  · push Not at h
    have hfun : CZ.goodPart a b F u = F u := by
      ext y; exact CZ.goodPart_of_notMem h y
    rw [hfun]; exact h1 u

end Step

end PrimeBHT.TimeFrequency.X2
