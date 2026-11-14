module

public import PrimeBHT.TimeFrequency.X2.CZ.WeakAtoms

/-!
# V08 phase 2: weak type `(1,1)` of kernel operators on `L^s(Y_P)`-valued functions

Abstract statement (`weak11_of_kernel`): `K : ℝ → ℂ` bounded continuous with
* the Hörmander condition `∫_{|x - c| > ℓ} |K(x - u) - K(x - c)| dx ≤ cH` for `|u - c| ≤ ℓ/2`
  (`hH`), and
* the good-part bound `‖K * g‖_{L^s(ℝ; L^s(Y))}^s ≤ A^s ‖g‖^s_{L^s(ℝ; L^s(Y))}` for bounded integrable
  `g` (`hGood`; for `s = 2` this is Plancherel at every fibre, for other `s` it is the scalar `L^s` bound,
  the base case `q = s` of V08(a), and is *not* proved by the Hilbert-space argument),

then `|{x : ‖(K * F)(x)‖_{L^s(Y)} > t}| ≤ C t⁻¹ ‖F‖_{L¹(ℝ; L^s(Y))}` with `C = 2 + 2^{2s-1} A^s + 4 cH`,
independent of `P`, `K`, `F`.  Proof: Calderón-Zygmund decomposition of `G = ‖F‖_{L^s(Y)}` at height `t`
(`CZDecomp.lean`), good part by `hGood`, bad atoms by the Hörmander condition and Minkowski.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-- The convolution `(K * h)(x) = ∫ K(x - u) h(u) du`. -/
noncomputable def kop (K : ℝ → ℝ → ℂ) (h : ℝ → ℂ) (x : ℝ) : ℂ := ∫ u, K x u * h u

/-- The convolution `(K * h)(x) = ∫ K(x - u) h(u) du` (the translation-invariant case of `kop`). -/
noncomputable def kconv (K : ℝ → ℂ) (h : ℝ → ℂ) (x : ℝ) : ℂ := kop (fun x u => K (x - u)) h x

section Conv

variable {K : ℝ → ℝ → ℂ} {M : ℝ}

theorem integrable_kernel_mul (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M)
    {h : ℝ → ℂ} (hh : Integrable h volume) (x : ℝ) : Integrable (fun u => K x u * h u) volume :=
  hh.bdd_mul (hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Eventually.of_forall fun u => hKb x u)

theorem measurable_kop (hKm : Measurable (Function.uncurry K)) {h : ℝ → ℂ} (hhm : Measurable h) :
    Measurable (kop K h) := by
  have hf : Measurable fun p : ℝ × ℝ => K p.1 p.2 * h p.2 :=
    (hKm.mul (hhm.comp measurable_snd))
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end Conv

section Bad

variable {P : ℕ} [NeZero P] {ι : Type} [Countable ι] {a b : ι → ℝ} {F : ℝ → ZMod P → ℂ}
  {K : ℝ → ℝ → ℂ} {M : ℝ} {s : ℝ}

/-- The centre of `Q_i`. -/
def ctr (a b : ι → ℝ) (i : ι) : ℝ := (a i + b i) / 2

theorem kconv_atom_eq (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M) (hab : ∀ i, a i < b i)
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y) (i : ι)
    (x : ℝ) (y : ZMod P) :
    kop K (fun u => atom a b F i u y) x =
      ∫ u in Ico (a i) (b i), (K x u - K x (ctr a b i)) * (F u y - meanVal a b F i y) := by
  have hat := integrable_atom hFi hFm (a := a) (b := b) i y
  have h0 := integral_atom_eq_zero hab hFi (a := a) (b := b) i y
  have hint1 := integrable_kernel_mul hKm hKb hat x
  have hint2 : Integrable (fun u => K x (ctr a b i) * atom a b F i u y) volume := hat.const_mul _
  have e : kop K (fun u => atom a b F i u y) x =
      ∫ u, (K x u - K x (ctr a b i)) * atom a b F i u y := by
    unfold kop
    have : (fun u => (K x u - K x (ctr a b i)) * atom a b F i u y) =
        fun u => K x u * atom a b F i u y - K x (ctr a b i) * atom a b F i u y := by
      ext u; ring
    rw [this, integral_sub hint1 hint2, integral_const_mul, h0]
    ring
  rw [e]
  unfold atom
  rw [← integral_indicator measurableSet_Ico]
  congr 1; ext u
  by_cases hu : u ∈ Ico (a i) (b i) <;> simp [hu, indicator_of_mem, indicator_of_notMem]

/-- **Bad-atom estimate, pointwise in `x`** (Minkowski): `‖K * atom_i (x)‖_X ≤
∫_{Q_i} |K(x - u) - K(x - c_i)| ‖F(u) - m_i‖_X du`. -/
theorem yNorm_kconv_atom_le (hs : 1 < s) (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M)
    (hab : ∀ i, a i < b i) (hFm : ∀ y, Measurable fun u => F u y)
    (hFi : ∀ y, Integrable fun u => F u y) (hG : Integrable (fun u => yNorm s (F u)) volume)
    (i : ι) (x : ℝ) :
    yNorm s (fun y => kop K (fun u => atom a b F i u y) x) ≤
      ∫ u in Ico (a i) (b i), ‖K x u - K x (ctr a b i)‖ *
        yNorm s (fun y => F u y - meanVal a b F i y) := by
  have hQ : MeasurableSet (Ico (a i) (b i)) := measurableSet_Ico
  have hfin : volume (Ico (a i) (b i)) ≠ ⊤ := by simp
  set m : ZMod P → ℂ := meanVal a b F i with hm
  set D : ℝ → ℂ := fun u => K x u - K x (ctr a b i) with hD
  have hDc : Measurable D := by
    simp only [hD]
    exact (hKm.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  have hDb : ∀ u, ‖D u‖ ≤ 2 * M := fun u => by
    simp only [hD]
    calc ‖K x u - K x (ctr a b i)‖ ≤ ‖K x u‖ + ‖K x (ctr a b i)‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hKb x u, hKb x (ctr a b i)]
  have hfun : (fun y => kop K (fun u => atom a b F i u y) x) =
      fun y => ∫ u, (D u * (F u y - m y)) ∂(volume.restrict (Ico (a i) (b i))) := by
    ext y; rw [kconv_atom_eq hKm hKb hab hFm hFi i x y]
  rw [hfun]
  have hFm' : ∀ y, Measurable fun u => F u y - m y := fun y => (hFm y).sub measurable_const
  have hint : ∀ y, Integrable (fun u => D u * (F u y - m y)) (volume.restrict (Ico (a i) (b i))) := by
    intro y
    have h1 : Integrable (fun u => F u y - m y) (volume.restrict (Ico (a i) (b i))) :=
      (hFi y).integrableOn.sub (integrableOn_const hfin)
    exact h1.bdd_mul hDc.aestronglyMeasurable (Eventually.of_forall hDb)
  have hnrm : (fun u => yNorm s (fun y => D u * (F u y - m y))) =
      fun u => ‖D u‖ * yNorm s (fun y => F u y - m y) := by
    ext u; rw [yNorm_const_mul (by linarith)]
  have hGm : Integrable (fun u => yNorm s (fun y => F u y - m y))
      (volume.restrict (Ico (a i) (b i))) := by
    have hmeas : AEMeasurable (fun u => yNorm s (fun y => F u y - m y)) volume :=
      aemeasurable_yNorm s (fun y => (hFm' y).aestronglyMeasurable)
    refine Integrable.mono' (g := fun u => yNorm s (F u) + yNorm s m) ?_
      hmeas.aestronglyMeasurable.restrict ?_
    · exact hG.integrableOn.add (integrableOn_const hfin)
    · refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (yNorm_nonneg s _)]
      exact yNorm_sub_le hs.le _ _
  have hn : Integrable (fun u => yNorm s (fun y => D u * (F u y - m y)))
      (volume.restrict (Ico (a i) (b i))) := by
    rw [hnrm]
    refine Integrable.mono' (g := fun u => (2 * M) * yNorm s (fun y => F u y - m y))
      (hGm.const_mul _) ?_ ?_
    · exact (hDc.norm.aestronglyMeasurable.mul hGm.1)
    · refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (yNorm_nonneg s _))]
      exact mul_le_mul_of_nonneg_right (hDb u) (yNorm_nonneg s _)
  have := yNorm_integral_le hs (μ := volume.restrict (Ico (a i) (b i)))
    (fun u y => D u * (F u y - m y)) hint hn
  rw [hnrm] at this
  exact this

theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf)).le
  · rw [integral_undef hi]; simp

theorem measurable_yNorm {P : ℕ} [NeZero P] (s : ℝ) {α : Type*} [MeasurableSpace α]
    {F : α → ZMod P → ℂ} (hF : ∀ y, Measurable fun x => F x y) :
    Measurable fun x => yNorm s (F x) := by
  unfold yNorm
  refine Measurable.pow_const (Measurable.const_mul ?_ _) _
  exact Finset.measurable_sum _ fun y _ => ((hF y).norm).pow_const s

/-- **Bad-atom estimate integrated in `x`** (Hörmander + Tonelli): off the dilated interval
`{|x - c_i| > ℓ_i}` the atom's image has `L¹(L^s(Y))` mass at most `cH ∫_{Q_i} ‖F - m_i‖_X`. -/
theorem lintegral_kconv_atom_le (hs : 1 < s) (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M)
    (hab : ∀ i, a i < b i) (hFm : ∀ y, Measurable fun u => F u y)
    (hFi : ∀ y, Integrable fun u => F u y) (hG : Integrable (fun u => yNorm s (F u)) volume)
    {cH : ℝ}
    (hH : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
      ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖K x u - K x c‖ₑ ≤ ENNReal.ofReal cH) (i : ι) :
    ∫⁻ x in {x : ℝ | b i - a i < |x - ctr a b i|},
        ENNReal.ofReal (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) ≤
      ENNReal.ofReal cH * ∫⁻ u in Ico (a i) (b i),
        ENNReal.ofReal (yNorm s (fun y => F u y - meanVal a b F i y)) := by
  set m : ZMod P → ℂ := meanVal a b F i with hm
  set c : ℝ := ctr a b i with hc
  set Φ : ℝ → ℝ := fun u => yNorm s (fun y => F u y - m y) with hΦ
  have hΦm : Measurable Φ := measurable_yNorm s (fun y => (hFm y).sub measurable_const)
  have hQ : MeasurableSet (Ico (a i) (b i)) := measurableSet_Ico
  have hS : MeasurableSet {x : ℝ | b i - a i < |x - c|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const _))
  -- pointwise bound by the double lintegral
  have h1 : ∀ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) ≤
      ∫⁻ u in Ico (a i) (b i), ‖K x u - K x c‖ₑ * ENNReal.ofReal (Φ u) := by
    intro x
    refine (ENNReal.ofReal_le_ofReal (yNorm_kconv_atom_le hs hKm hKb hab hFm hFi hG i x)).trans ?_
    refine (ofReal_integral_le_lintegral (fun u => mul_nonneg (norm_nonneg _) (yNorm_nonneg s _))).trans ?_
    refine le_of_eq (lintegral_congr fun u => ?_)
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  calc ∫⁻ x in {x : ℝ | b i - a i < |x - c|},
        ENNReal.ofReal (yNorm s (fun y => kop K (fun u => atom a b F i u y) x))
      ≤ ∫⁻ x in {x : ℝ | b i - a i < |x - c|},
          ∫⁻ u in Ico (a i) (b i), ‖K x u - K x c‖ₑ * ENNReal.ofReal (Φ u) :=
        lintegral_mono h1
    _ = ∫⁻ u in Ico (a i) (b i), ∫⁻ x in {x : ℝ | b i - a i < |x - c|},
          ‖K x u - K x c‖ₑ * ENNReal.ofReal (Φ u) := by
        refine lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        have h2 : Measurable fun z : ℝ × ℝ => ‖K z.1 z.2 - K z.1 c‖ₑ :=
          (hKm.sub (hKm.comp (measurable_fst.prodMk measurable_const))).enorm
        have h3 : Measurable fun z : ℝ × ℝ => ENNReal.ofReal (Φ z.2) :=
          (hΦm.comp measurable_snd).ennreal_ofReal
        exact h2.mul h3
    _ ≤ ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal cH * ENNReal.ofReal (Φ u) := by
        refine setLIntegral_mono' hQ fun u hu => ?_
        have h2 : Measurable fun x : ℝ => ‖K x u - K x c‖ₑ :=
          ((hKm.comp (measurable_id.prodMk measurable_const)).sub
            (hKm.comp (measurable_id.prodMk measurable_const))).enorm
        rw [lintegral_mul_const _ h2]
        refine mul_le_mul_left (hH c u (b i - a i) ?_) _
        have hu' := hu
        simp only [mem_Ico] at hu'
        simp only [hc, ctr]
        rw [abs_le]; constructor <;> linarith [hu'.1, hu'.2]
    _ = ENNReal.ofReal cH * ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal (Φ u) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

omit [Countable ι] in
/-- `∫_{Q_i} ‖F - m_i‖_X ≤ 2 ∫_{Q_i} ‖F‖_X`. -/
theorem integral_yNorm_atom_le (hs : 1 < s) (hab : ∀ i, a i < b i)
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (hG : Integrable (fun u => yNorm s (F u)) volume) (i : ι) :
    ∫ u in Ico (a i) (b i), yNorm s (fun y => F u y - meanVal a b F i y) ≤
      2 * ∫ u in Ico (a i) (b i), yNorm s (F u) := by
  have hl : (0 : ℝ) < b i - a i := sub_pos.2 (hab i)
  have hfin : volume (Ico (a i) (b i)) ≠ ⊤ := by simp
  have hGi : IntegrableOn (fun u => yNorm s (F u)) (Ico (a i) (b i)) := hG.integrableOn
  have hm : yNorm s (meanVal a b F i) * (b i - a i) ≤ ∫ u in Ico (a i) (b i), yNorm s (F u) := by
    have h := yNorm_average_le hs hl F (fun y => (hFi y).integrableOn) hGi
    have h' : yNorm s (meanVal a b F i) ≤ (b i - a i)⁻¹ * ∫ u in Ico (a i) (b i), yNorm s (F u) := h
    calc yNorm s (meanVal a b F i) * (b i - a i)
        ≤ ((b i - a i)⁻¹ * ∫ u in Ico (a i) (b i), yNorm s (F u)) * (b i - a i) :=
          mul_le_mul_of_nonneg_right h' hl.le
      _ = ∫ u in Ico (a i) (b i), yNorm s (F u) := by field_simp
  have hmeas : AEMeasurable (fun u => yNorm s (fun y => F u y - meanVal a b F i y)) volume :=
    (measurable_yNorm s (fun y => (hFm y).sub measurable_const)).aemeasurable
  calc ∫ u in Ico (a i) (b i), yNorm s (fun y => F u y - meanVal a b F i y)
      ≤ ∫ u in Ico (a i) (b i), (yNorm s (F u) + yNorm s (meanVal a b F i)) := by
        refine setIntegral_mono_on ?_ (hGi.add (integrableOn_const hfin)) measurableSet_Ico
          (fun u _ => yNorm_sub_le hs.le _ _)
        refine Integrable.mono' (g := fun u => yNorm s (F u) + yNorm s (meanVal a b F i))
          (hGi.add (integrableOn_const hfin)) hmeas.aestronglyMeasurable.restrict ?_
        refine Eventually.of_forall fun u => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (yNorm_nonneg s _)]
        exact yNorm_sub_le hs.le _ _
    _ = (∫ u in Ico (a i) (b i), yNorm s (F u)) + yNorm s (meanVal a b F i) * (b i - a i) := by
        rw [integral_add hGi (integrableOn_const hfin), setIntegral_const,
          Real.volume_real_Ico_of_le (hab i).le, smul_eq_mul, mul_comm]
    _ ≤ 2 * ∫ u in Ico (a i) (b i), yNorm s (F u) := by linarith

omit [Countable ι] in
theorem integrableOn_yNorm_atom_sub (hs : 1 < s) (hFm : ∀ y, Measurable fun u => F u y)
    (hG : Integrable (fun u => yNorm s (F u)) volume) (i : ι) :
    IntegrableOn (fun u => yNorm s (fun y => F u y - meanVal a b F i y)) (Ico (a i) (b i)) := by
  have hfin : volume (Ico (a i) (b i)) ≠ ⊤ := by simp
  have hmeas : Measurable (fun u => yNorm s (fun y => F u y - meanVal a b F i y)) :=
    measurable_yNorm s (fun y => (hFm y).sub measurable_const)
  refine Integrable.mono' (g := fun u => yNorm s (F u) + yNorm s (meanVal a b F i))
    (hG.integrableOn.add (integrableOn_const hfin)) hmeas.aestronglyMeasurable.restrict ?_
  refine Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (yNorm_nonneg s _)]
  exact yNorm_sub_le hs.le _ _

theorem hasSum_kconv_atom (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M) (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (x : ℝ) (y : ZMod P) :
    HasSum (fun i => kop K (fun u => atom a b F i u y) x)
      (kop K (fun u => badPart a b F u y) x) := by
  have hint : ∀ i, Integrable (fun u => K x u * atom a b F i u y) volume := fun i =>
    integrable_kernel_mul hKm hKb (integrable_atom hFi hFm i y) x
  have hM : 0 ≤ M := (norm_nonneg _).trans (hKb 0 0)
  have hsum : Summable fun i => ∫ u, ‖K x u * atom a b F i u y‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun u => norm_nonneg _)
      (fun i => ?_) ((summable_integral_norm_atom hab hd hFi y).mul_left M)
    rw [← integral_const_mul]
    refine integral_mono (hint i).norm ((integrable_atom hFi hFm i y).norm.const_mul M) fun u => ?_
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (hKb _ _) (norm_nonneg _)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have e : (fun u => ∑' i, K x u * atom a b F i u y) =
      fun u => K x u * badPart a b F u y := by
    ext u; unfold badPart; rw [tsum_mul_left]
  rw [e] at h
  exact h

theorem summable_yNorm_kconv_atom (hs : 1 < s) (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M)
    (hab : ∀ i, a i < b i) (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (hG : Integrable (fun u => yNorm s (F u)) volume) (x : ℝ) :
    Summable fun i => yNorm s (fun y => kop K (fun u => atom a b F i u y) x) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hKb 0 0)
  have h1 : HasSum (fun i => ∫ u in Ico (a i) (b i), yNorm s (F u))
      (∫ u in ⋃ i, Ico (a i) (b i), yNorm s (F u)) :=
    hasSum_integral_iUnion (fun i => measurableSet_Ico) hd hG.integrableOn
  refine Summable.of_nonneg_of_le (fun i => yNorm_nonneg s _) (fun i => ?_)
    (h1.summable.mul_left (4 * M))
  have hΦ := integrableOn_yNorm_atom_sub hs hFm hG i (a := a) (b := b)
  have hDb : ∀ u, ‖K x u - K x (ctr a b i)‖ ≤ 2 * M := fun u =>
    (norm_sub_le _ _).trans (by linarith [hKb x u, hKb x (ctr a b i)])
  calc yNorm s (fun y => kop K (fun u => atom a b F i u y) x)
      ≤ ∫ u in Ico (a i) (b i), ‖K x u - K x (ctr a b i)‖ *
          yNorm s (fun y => F u y - meanVal a b F i y) :=
        yNorm_kconv_atom_le hs hKm hKb hab hFm hFi hG i x
    _ ≤ ∫ u in Ico (a i) (b i), (2 * M) * yNorm s (fun y => F u y - meanVal a b F i y) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u =>
          mul_nonneg (norm_nonneg _) (yNorm_nonneg s _)) (hΦ.const_mul _)
          (Eventually.of_forall fun u => ?_)
        exact mul_le_mul_of_nonneg_right (hDb u) (yNorm_nonneg s _)
    _ = (2 * M) * ∫ u in Ico (a i) (b i), yNorm s (fun y => F u y - meanVal a b F i y) := by
        rw [integral_const_mul]
    _ ≤ (2 * M) * (2 * ∫ u in Ico (a i) (b i), yNorm s (F u)) :=
        mul_le_mul_of_nonneg_left (integral_yNorm_atom_le hs hab hFm hFi hG i) (by positivity)
    _ = 4 * M * ∫ u in Ico (a i) (b i), yNorm s (F u) := by ring

/-- The dilated intervals `⋃ [c_i - ℓ_i, c_i + ℓ_i]`. -/
def dilated (a b : ι → ℝ) : Set ℝ := ⋃ i, {x : ℝ | |x - ctr a b i| ≤ b i - a i}

/-- **The bad part away from the dilated intervals** (Hörmander, Minkowski, Tonelli): its image under `K`
has `L¹(L^s(Y))` mass at most `2 cH ‖F‖_{L¹(L^s(Y))}` outside `⋃ [c_i - ℓ_i, c_i + ℓ_i]`. -/
theorem lintegral_kconv_bad_le (hs : 1 < s) (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M)
    (hab : ∀ i, a i < b i) (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (hG : Integrable (fun u => yNorm s (F u)) volume) {cH : ℝ}
    (hH : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
      ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖K x u - K x c‖ₑ ≤ ENNReal.ofReal cH) :
    ∫⁻ x in (dilated a b)ᶜ,
        ENNReal.ofReal (yNorm s (fun y => kop K (fun u => badPart a b F u y) x)) ≤
      2 * ENNReal.ofReal cH * ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) := by
  have hs0 : 0 < s := by linarith
  -- pointwise triangle inequality
  have h1 : ∀ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => badPart a b F u y) x)) ≤
      ∑' i, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) := by
    intro x
    have hsm := summable_yNorm_kconv_atom hs hKm hKb hab hd hFm hFi hG x
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => yNorm_nonneg s _) hsm]
    exact ENNReal.ofReal_le_ofReal (yNorm_tsum_le hs.le _ _
      (fun y => hasSum_kconv_atom hKm hKb hab hd hFm hFi x y) hsm)
  have hmeas : ∀ i, Measurable fun x => ENNReal.ofReal
      (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) := by
    intro i
    have hc : Measurable fun x => yNorm s (fun y => kop K (fun u => atom a b F i u y) x) :=
      measurable_yNorm s (fun y => measurable_kop hKm (measurable_atom hFm i y))
    exact hc.ennreal_ofReal
  have hcompl : MeasurableSet (dilated a b)ᶜ := by
    refine MeasurableSet.compl (MeasurableSet.iUnion fun i => ?_)
    exact measurableSet_le (continuous_abs.measurable.comp (measurable_id.sub_const _))
      measurable_const
  have hG1 : ∀ i, ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal (yNorm s (fun y => F u y - meanVal a b F i y)) ≤
      2 * ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal (yNorm s (F u)) := by
    intro i
    have hΦ := integrableOn_yNorm_atom_sub hs hFm hG i (a := a) (b := b)
    rw [← ofReal_integral_eq_lintegral_ofReal hΦ (Eventually.of_forall fun u => yNorm_nonneg s _),
      ← ofReal_integral_eq_lintegral_ofReal hG.integrableOn
        (Eventually.of_forall fun u => yNorm_nonneg s _)]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal (2 * ∫ u in Ico (a i) (b i), yNorm s (F u)) :=
          ENNReal.ofReal_le_ofReal (integral_yNorm_atom_le hs hab hFm hFi hG i)
      _ = 2 * ENNReal.ofReal (∫ u in Ico (a i) (b i), yNorm s (F u)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
  calc ∫⁻ x in (dilated a b)ᶜ,
        ENNReal.ofReal (yNorm s (fun y => kop K (fun u => badPart a b F u y) x))
      ≤ ∫⁻ x in (dilated a b)ᶜ, ∑' i, ENNReal.ofReal
          (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) := lintegral_mono h1
    _ = ∑' i, ∫⁻ x in (dilated a b)ᶜ, ENNReal.ofReal
          (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) :=
        lintegral_tsum fun i => (hmeas i).aemeasurable
    _ ≤ ∑' i, ENNReal.ofReal cH * (2 * ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal (yNorm s (F u))) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        calc ∫⁻ x in (dilated a b)ᶜ, ENNReal.ofReal
              (yNorm s (fun y => kop K (fun u => atom a b F i u y) x))
            ≤ ∫⁻ x in {x : ℝ | b i - a i < |x - ctr a b i|}, ENNReal.ofReal
              (yNorm s (fun y => kop K (fun u => atom a b F i u y) x)) := by
              refine lintegral_mono_set ?_
              intro x hx
              simp only [dilated, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hx
              exact hx i
          _ ≤ ENNReal.ofReal cH * ∫⁻ u in Ico (a i) (b i),
              ENNReal.ofReal (yNorm s (fun y => F u y - meanVal a b F i y)) :=
              lintegral_kconv_atom_le hs hKm hKb hab hFm hFi hG hH i
          _ ≤ ENNReal.ofReal cH * (2 * ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal (yNorm s (F u))) :=
              mul_le_mul' le_rfl (hG1 i)
    _ = 2 * ENNReal.ofReal cH * ∑' i, ∫⁻ u in Ico (a i) (b i), ENNReal.ofReal (yNorm s (F u)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i => ?_
        ring
    _ = 2 * ENNReal.ofReal cH * ∫⁻ u in ⋃ i, Ico (a i) (b i), ENNReal.ofReal (yNorm s (F u)) := by
        rw [lintegral_iUnion (fun i => measurableSet_Ico) hd]
    _ ≤ 2 * ENNReal.ofReal cH * ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

omit [Countable ι] in
/-- The `X`-norm of the mean over `Q_i` is at most the average of `G` over `Q_i`. -/
theorem yNorm_meanVal_le (hs : 1 < s) (hab : ∀ i, a i < b i) (hFi : ∀ y, Integrable fun u => F u y)
    (hG : Integrable (fun u => yNorm s (F u)) volume) (i : ι) :
    yNorm s (meanVal a b F i) * (b i - a i) ≤ ∫ u in Ico (a i) (b i), yNorm s (F u) := by
  have hl : (0 : ℝ) < b i - a i := sub_pos.2 (hab i)
  have h := yNorm_average_le hs hl F (Q := Ico (a i) (b i)) (fun y => (hFi y).integrableOn)
    hG.integrableOn
  have h' : yNorm s (meanVal a b F i) ≤ (b i - a i)⁻¹ * ∫ u in Ico (a i) (b i), yNorm s (F u) := h
  calc yNorm s (meanVal a b F i) * (b i - a i)
      ≤ ((b i - a i)⁻¹ * ∫ u in Ico (a i) (b i), yNorm s (F u)) * (b i - a i) :=
        mul_le_mul_of_nonneg_right h' hl.le
    _ = ∫ u in Ico (a i) (b i), yNorm s (F u) := by field_simp

/-- **The good part is bounded by `2 λ`** in `X`-norm (a.e.). -/
theorem yNorm_goodPart_le (hs : 1 < s) (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFi : ∀ y, Integrable fun u => F u y) (hG : Integrable (fun u => yNorm s (F u)) volume)
    {lam : ℝ} (hlam : 0 < lam)
    (hQ : ∀ i, ∫ u in Ico (a i) (b i), yNorm s (F u) ≤ 2 * lam * (b i - a i))
    (hout : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ⋃ i, Ico (a i) (b i) → yNorm s (F u) ≤ lam) :
    ∀ᵐ u ∂(volume : Measure ℝ), yNorm s (fun y => goodPart a b F u y) ≤ 2 * lam := by
  filter_upwards [hout] with u hu
  by_cases h : ∃ j, u ∈ Ico (a j) (b j)
  · obtain ⟨j, hj⟩ := h
    have hfun : (fun y => goodPart a b F u y) = meanVal a b F j := by
      ext y; exact goodPart_of_mem hd hj y
    rw [hfun]
    have hl : (0 : ℝ) < b j - a j := sub_pos.2 (hab j)
    have := yNorm_meanVal_le hs hab hFi hG j
    nlinarith [hQ j, yNorm_nonneg s (meanVal a b F j)]
  · push Not at h
    have hfun : (fun y => goodPart a b F u y) = F u := by
      ext y; exact goodPart_of_notMem h y
    rw [hfun]
    have := hu (by simpa using h)
    linarith

/-- **The good part has no more mass than `F`**: `∫ ‖g‖_X ≤ ∫ ‖F‖_X`. -/
theorem lintegral_goodPart_le (hs : 1 < s) (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFi : ∀ y, Integrable fun u => F u y) (hG : Integrable (fun u => yNorm s (F u)) volume) :
    ∫⁻ u, ENNReal.ofReal (yNorm s (fun y => goodPart a b F u y)) ≤
      ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) := by
  set U : Set ℝ := ⋃ i, Ico (a i) (b i) with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun i => measurableSet_Ico
  rw [← lintegral_add_compl _ hUm, ← lintegral_add_compl (fun u => ENNReal.ofReal (yNorm s (F u))) hUm]
  refine add_le_add ?_ ?_
  · rw [hU, lintegral_iUnion (fun i => measurableSet_Ico) hd,
      lintegral_iUnion (fun i => measurableSet_Ico) hd]
    refine ENNReal.tsum_le_tsum fun i => ?_
    have hfun : ∀ u ∈ Ico (a i) (b i), ENNReal.ofReal (yNorm s (fun y => goodPart a b F u y)) =
        ENNReal.ofReal (yNorm s (meanVal a b F i)) := by
      intro u hu
      congr 2
      ext y; exact goodPart_of_mem hd hu y
    rw [setLIntegral_congr_fun measurableSet_Ico hfun, setLIntegral_const, Real.volume_Ico,
      ← ENNReal.ofReal_mul (yNorm_nonneg s _),
      ← ofReal_integral_eq_lintegral_ofReal hG.integrableOn
        (Eventually.of_forall fun u => yNorm_nonneg s _)]
    exact ENNReal.ofReal_le_ofReal (yNorm_meanVal_le hs hab hFi hG i)
  · refine le_of_eq (setLIntegral_congr_fun hUm.compl fun u hu => ?_)
    have h : ∀ j, u ∉ Ico (a j) (b j) := fun j hj => hu (mem_iUnion.2 ⟨j, hj⟩)
    have hfun : (fun y => goodPart a b F u y) = F u := by
      ext y; exact goodPart_of_notMem h y
    rw [hfun]

/-- The dilated intervals have total measure at most `2 ∑ ℓ_i ≤ 2 ‖G‖₁ / λ`. -/
theorem volume_dilated_le (hab : ∀ i, a i < b i) {G : ℝ → ℝ} (hG0 : ∀ x, 0 ≤ G x)
    (hG : Integrable G volume) {lam : ℝ} (hlam : 0 < lam)
    (hsum : Summable fun i => b i - a i) (htsum : ∑' i, (b i - a i) ≤ (∫ x, G x) / lam) :
    volume (dilated a b) ≤ ENNReal.ofReal (2 / lam) * ∫⁻ x, ENNReal.ofReal (G x) := by
  have hvol : ∀ i, volume {x : ℝ | |x - ctr a b i| ≤ b i - a i} = ENNReal.ofReal (2 * (b i - a i)) := by
    intro i
    have : {x : ℝ | |x - ctr a b i| ≤ b i - a i} = Icc (ctr a b i - (b i - a i)) (ctr a b i + (b i - a i)) := by
      ext x; simp only [mem_ofPred_eq, mem_Icc, abs_le]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [this, Real.volume_Icc]; congr 1; ring
  have hnn : ∀ i, 0 ≤ b i - a i := fun i => (sub_pos.2 (hab i)).le
  calc volume (dilated a b) ≤ ∑' i, volume {x : ℝ | |x - ctr a b i| ≤ b i - a i} := measure_iUnion_le _
    _ = ∑' i, ENNReal.ofReal (2 * (b i - a i)) := tsum_congr hvol
    _ = ENNReal.ofReal (∑' i, 2 * (b i - a i)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by linarith [hnn i]) (hsum.mul_left 2)).symm
    _ ≤ ENNReal.ofReal (2 / lam * ∫ x, G x) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        calc 2 * ∑' i, (b i - a i) ≤ 2 * ((∫ x, G x) / lam) := by linarith
          _ = 2 / lam * ∫ x, G x := by ring
    _ = ENNReal.ofReal (2 / lam) * ∫⁻ x, ENNReal.ofReal (G x) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ofReal_integral_eq_lintegral_ofReal hG (Eventually.of_forall hG0)]

end Bad

theorem rpow_const_identity {s t : ℝ} (ht : 0 < t) :
    (((t / 2) ^ s)⁻¹ * (2 * t) ^ (s - 1) : ℝ) = (2 : ℝ) ^ (2 * s - 1) / t := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.div_rpow ht.le h2.le, Real.mul_rpow h2.le ht.le, Real.rpow_sub_one ht.ne',
    Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
  have e : (2 : ℝ) ^ (2 * s) = (2 : ℝ) ^ s * (2 : ℝ) ^ s := by
    rw [two_mul, Real.rpow_add h2]
  have hts : (0 : ℝ) < t ^ s := Real.rpow_pos_of_pos ht s
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos h2 s
  rw [e]
  field_simp

theorem meas_le_of_mul_le {ε X m : ℝ≥0∞} (h0 : ε ≠ 0) (ht : ε ≠ ⊤) (h : ε * m ≤ X) : m ≤ ε⁻¹ * X := by
  calc m = ε⁻¹ * (ε * m) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ ε⁻¹ * X := mul_le_mul' le_rfl h

theorem yNorm_le_sum_norm {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (v : ZMod P → ℂ) :
    yNorm s v ≤ ∑ y, ‖v y‖ :=
  (PrimeBHT.Lift.yNorm_le_yNormInf hs v).trans
    (PrimeBHT.Lift.yNormInf_le (Finset.sum_nonneg fun _y _ => norm_nonneg _) fun y =>
      Finset.single_le_sum (f := fun y => ‖v y‖) (fun _y _ => norm_nonneg _) (Finset.mem_univ y))

/-- **Weak type `(1,1)` of a kernel operator on `L^s(Y_P)`-valued functions** (see the module docstring).
`C = 2 + 2^{2s-1} A^s + 4 cH`, independent of `P`, `K`, `F`. -/
theorem weak11_of_kernel {P : ℕ} [NeZero P] {s : ℝ} (hs : 1 < s) {K : ℝ → ℝ → ℂ} {M : ℝ}
    (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M) {cH A : ℝ} (hA0 : 0 ≤ A) (hcH : 0 ≤ cH)
    (hH : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
      ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖K x u - K x c‖ₑ ≤ ENNReal.ofReal cH)
    (hGood : ∀ g : ℝ → ZMod P → ℂ, (∀ y, Measurable fun u => g u y) →
      (∀ y, Integrable fun u => g u y) → (∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C) →
      ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => g u y) x)) ^ s ≤
        ENNReal.ofReal A ^ s * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s)
    (F : ℝ → ZMod P → ℂ) (hFm : ∀ y, Measurable fun u => F u y)
    (hFi : ∀ y, Integrable fun u => F u y) (hFb : ∀ y, ∃ C, ∀ u, ‖F u y‖ ≤ C) {t : ℝ} (ht : 0 < t) :
    volume {x : ℝ | t < yNorm s (fun y => kop K (fun u => F u y) x)} ≤
      ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) / t) *
        ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) := by
  have hs0 : 0 < s := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hKb 0 0)
  -- `G = ‖F‖_X`
  have hGm : Measurable fun u => yNorm s (F u) := measurable_yNorm s hFm
  have hG : Integrable (fun u => yNorm s (F u)) volume := by
    refine Integrable.mono' (g := fun u => ∑ y, ‖F u y‖)
      (integrable_finsetSum _ fun y _ => (hFi y).norm) hGm.aestronglyMeasurable ?_
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (yNorm_nonneg s _)]
    exact yNorm_le_sum_norm hs0 _
  -- the Calderón-Zygmund decomposition of `G` at height `t`
  obtain ⟨ι, hcnt, a, b, hab, hd, -, hup, hae, hsum, htsum⟩ :=
    exists_cz_intervals (G := fun u => yNorm s (F u)) (fun u => yNorm_nonneg s _) hG ht
  have hQ : ∀ i, ∫ u in Ico (a i) (b i), yNorm s (F u) ≤ 2 * t * (b i - a i) := hup
  -- good and bad parts
  set g : ℝ → ZMod P → ℂ := goodPart a b F with hg
  have hgm : ∀ y, Measurable fun u => g u y := fun y => measurable_goodPart hd hFm y
  have hgi : ∀ y, Integrable fun u => g u y := fun y => integrable_goodPart hab hd hFm hFi y
  have hgb : ∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C := fun y => by
    obtain ⟨C, hC⟩ := hFb y
    exact ⟨C, norm_goodPart_le hab hd hFi y hC⟩
  have hbi : ∀ y, Integrable fun u => badPart a b F u y := fun y => integrable_badPart hab hd hFm hFi y
  -- the pointwise splitting `K * F = K * g + K * bad`
  have hsplit : ∀ x, ∀ y, kop K (fun u => F u y) x =
      kop K (fun u => g u y) x + kop K (fun u => badPart a b F u y) x := by
    intro x y
    unfold kop
    rw [← integral_add (integrable_kernel_mul hKm hKb (hgi y) x)
      (integrable_kernel_mul hKm hKb (hbi y) x)]
    congr 1; ext u
    simp only [hg, goodPart]; ring
  have htri : ∀ x, yNorm s (fun y => kop K (fun u => F u y) x) ≤
      yNorm s (fun y => kop K (fun u => g u y) x) +
        yNorm s (fun y => kop K (fun u => badPart a b F u y) x) := by
    intro x
    have : (fun y => kop K (fun u => F u y) x) =
        (fun y => kop K (fun u => g u y) x) + (fun y => kop K (fun u => badPart a b F u y) x) := by
      ext y; exact hsplit x y
    rw [this]; exact yNorm_add_le hs.le _ _
  -- continuity (hence measurability) of the two convolutions
  have hbm : ∀ y, Measurable fun u => badPart a b F u y := fun y =>
    measurable_of_hasSum (fun i => measurable_atom hFm i y) (fun u => hasSum_atom hd u y)
  have hcg : Measurable fun x => yNorm s (fun y => kop K (fun u => g u y) x) :=
    measurable_yNorm s (fun y => measurable_kop hKm (hgm y))
  have hcb : Measurable fun x => yNorm s (fun y => kop K (fun u => badPart a b F u y) x) :=
    measurable_yNorm s (fun y => measurable_kop hKm (hbm y))
  -- the set inclusion
  have hsub : {x : ℝ | t < yNorm s (fun y => kop K (fun u => F u y) x)} ⊆
      dilated a b ∪ {x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => g u y) x)} ∪
        ({x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => badPart a b F u y) x)} ∩ (dilated a b)ᶜ) := by
    intro x hx
    by_cases h1 : x ∈ dilated a b
    · exact Or.inl (Or.inl h1)
    by_cases h2 : t / 2 < yNorm s (fun y => kop K (fun u => g u y) x)
    · exact Or.inl (Or.inr h2)
    refine Or.inr ⟨?_, h1⟩
    have := htri x
    simp only [mem_ofPred_eq] at hx ⊢
    linarith [not_lt.1 h2]
  -- the three pieces
  set I : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) with hI
  have h1 : volume (dilated a b) ≤ ENNReal.ofReal (2 / t) * I :=
    volume_dilated_le hab (G := fun u => yNorm s (F u)) (fun u => yNorm_nonneg s _) hG ht hsum htsum
  have h3 : volume ({x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => badPart a b F u y) x)} ∩
      (dilated a b)ᶜ) ≤ ENNReal.ofReal (4 * cH / t) * I := by
    set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
      (yNorm s (fun y => kop K (fun u => badPart a b F u y) x)) with hf
    have hfm : Measurable f := hcb.ennreal_ofReal
    have hEm : MeasurableSet (dilated a b)ᶜ := by
      refine MeasurableSet.compl (MeasurableSet.iUnion fun i => ?_)
      exact measurableSet_le (continuous_abs.measurable.comp (measurable_id.sub_const _))
        measurable_const
    have hsetm : MeasurableSet {x : ℝ | ENNReal.ofReal (t / 2) ≤ f x} :=
      measurableSet_le measurable_const hfm
    have hcheb := mul_meas_ge_le_lintegral₀ (μ := volume.restrict (dilated a b)ᶜ)
      hfm.aemeasurable (ENNReal.ofReal (t / 2))
    rw [Measure.restrict_apply hsetm] at hcheb
    have hbad := lintegral_kconv_bad_le hs hKm hKb hab hd hFm hFi hG hH
    have hsub3 : {x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => badPart a b F u y) x)} ∩
        (dilated a b)ᶜ ⊆ {x : ℝ | ENNReal.ofReal (t / 2) ≤ f x} ∩ (dilated a b)ᶜ := by
      intro x hx
      refine ⟨?_, hx.2⟩
      simp only [mem_ofPred_eq, hf]
      exact ENNReal.ofReal_le_ofReal hx.1.le
    have hpos : ENNReal.ofReal (t / 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have := meas_le_of_mul_le hpos ENNReal.ofReal_ne_top (hcheb.trans hbad)
    calc _ ≤ volume ({x : ℝ | ENNReal.ofReal (t / 2) ≤ f x} ∩ (dilated a b)ᶜ) := measure_mono hsub3
      _ ≤ _ := this
      _ = ENNReal.ofReal (4 * cH / t) * I := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < t / 2), ← mul_assoc]
        have : ENNReal.ofReal ((t / 2)⁻¹) * (2 * ENNReal.ofReal cH) =
            ENNReal.ofReal (4 * cH / t) := by
          have h2c : (2 : ℝ≥0∞) * ENNReal.ofReal cH = ENNReal.ofReal (2 * cH) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2c, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp; ring
        rw [this]
  have h2 : volume {x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => g u y) x)} ≤
      ENNReal.ofReal (2 ^ (2 * s - 1) * A ^ s / t) * I := by
    set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal
      (yNorm s (fun y => kop K (fun u => g u y) x)) ^ s with hf
    have hfm : Measurable f := hcg.ennreal_ofReal.pow_const s
    set ε : ℝ≥0∞ := ENNReal.ofReal ((t / 2) ^ s) with hε
    have hsetm : MeasurableSet {x : ℝ | ε ≤ f x} := measurableSet_le measurable_const hfm
    have hcheb := mul_meas_ge_le_lintegral₀ (μ := volume) hfm.aemeasurable ε
    have hsub2 : {x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => g u y) x)} ⊆
        {x : ℝ | ε ≤ f x} := by
      intro x hx
      simp only [mem_ofPred_eq, hf, hε] at hx ⊢
      rw [ENNReal.ofReal_rpow_of_nonneg (yNorm_nonneg s _) hs0.le]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hx.le hs0.le)
    -- the good part: `∫ ‖K*g‖^s ≤ A^s ∫ ‖g‖^s ≤ A^s (2t)^{s-1} ∫ ‖g‖`
    have hgood := hGood g hgm hgi hgb
    have hbd := yNorm_goodPart_le hs hab hd hFi hG ht hQ hae
    have hpow : ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s ≤
        ENNReal.ofReal ((2 * t) ^ (s - 1)) * I := by
      calc ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s
          ≤ ∫⁻ u, ENNReal.ofReal ((2 * t) ^ (s - 1)) * ENNReal.ofReal (yNorm s (g u)) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hbd] with u hu
            rw [ENNReal.ofReal_rpow_of_nonneg (yNorm_nonneg s _) hs0.le,
              ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hx0 := yNorm_nonneg s (g u)
            calc yNorm s (g u) ^ s = yNorm s (g u) ^ (s - 1) * yNorm s (g u) := by
                  rw [← Real.rpow_add_one' hx0 (by linarith)]; congr 1; ring
              _ ≤ (2 * t) ^ (s - 1) * yNorm s (g u) := by
                  refine mul_le_mul_of_nonneg_right ?_ hx0
                  exact Real.rpow_le_rpow hx0 hu (by linarith)
        _ = ENNReal.ofReal ((2 * t) ^ (s - 1)) * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ((2 * t) ^ (s - 1)) * I :=
            mul_le_mul' le_rfl (lintegral_goodPart_le hs hab hd hFi hG)
    have hpos : ε ≠ 0 := by
      simp only [hε, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos (by positivity) s
    have h4 := meas_le_of_mul_le hpos ENNReal.ofReal_ne_top
      (hcheb.trans (hgood.trans (mul_le_mul' le_rfl hpow)))
    have h5 : ε⁻¹ * (ENNReal.ofReal A ^ s * (ENNReal.ofReal ((2 * t) ^ (s - 1)) * I)) =
        ENNReal.ofReal (2 ^ (2 * s - 1) * A ^ s / t) * I := by
      rw [hε, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (by positivity) s),
        ENNReal.ofReal_rpow_of_nonneg hA0 hs0.le, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [mul_comm (((t / 2) ^ s)⁻¹) (A ^ s), mul_assoc, rpow_const_identity ht]
      ring
    exact (measure_mono hsub2).trans (h4.trans (le_of_eq h5))
  calc volume {x : ℝ | t < yNorm s (fun y => kop K (fun u => F u y) x)}
      ≤ volume (dilated a b ∪ {x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => g u y) x)} ∪
        ({x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => badPart a b F u y) x)} ∩
          (dilated a b)ᶜ)) := measure_mono hsub
    _ ≤ volume (dilated a b) + volume {x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => g u y) x)} +
        volume ({x : ℝ | t / 2 < yNorm s (fun y => kop K (fun u => badPart a b F u y) x)} ∩
          (dilated a b)ᶜ) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (2 / t) * I + ENNReal.ofReal (2 ^ (2 * s - 1) * A ^ s / t) * I +
        ENNReal.ofReal (4 * cH / t) * I := add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) / t) * I := by
        rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2; ring


/-- **The good-part hypothesis from a scalar `L^s(ℝ)` bound**: if `‖K * h‖_{L^s(ℝ)} ≤ A ‖h‖_{L^s(ℝ)}` for
bounded integrable `h` then `‖K * g‖_{L^s(ℝ; L^s(Y))} ≤ A ‖g‖_{L^s(ℝ; L^s(Y))}` (Fubini: `K` acts
fibrewise in `y`), for every `P`. -/
theorem hGood_of_scalar {P : ℕ} [NeZero P] {s : ℝ} (hs : 1 < s) {K : ℝ → ℝ → ℂ} {M : ℝ}
    (hKm : Measurable (Function.uncurry K)) (_hKb : ∀ x z, ‖K x z‖ ≤ M) {A : ℝ}
    (hScalar : ∀ h : ℝ → ℂ, Measurable h → Integrable h volume → (∃ C, ∀ u, ‖h u‖ ≤ C) →
      eLpNorm (kop K h) (ENNReal.ofReal s) volume ≤
        ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume)
    (g : ℝ → ZMod P → ℂ) (hgm : ∀ y, Measurable fun u => g u y)
    (hgi : ∀ y, Integrable fun u => g u y) (hgb : ∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C) :
    ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => g u y) x)) ^ s ≤
      ENNReal.ofReal A ^ s * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s := by
  have hs0 : 0 < s := by linarith
  set Tg : ℝ → ZMod P → ℂ := fun x y => kop K (fun u => g u y) x with hTg
  have hTm : ∀ y, AEStronglyMeasurable (fun x => Tg x y) volume := fun y =>
    (measurable_kop hKm (hgm y)).aestronglyMeasurable
  have hgm' : ∀ y, AEStronglyMeasurable (fun x => g x y) volume := fun y =>
    (hgm y).aestronglyMeasurable
  have e1 := mixedENorm_rpow hs0 s hTm
  have e2 := mixedENorm_rpow hs0 s hgm'
  have d1 := mixedENorm_diag_rpow_fibre hs0 hTm
  have d2 := mixedENorm_diag_rpow_fibre hs0 hgm'
  rw [← e1, d1, ← e2, d2]
  calc (P : ℝ≥0∞)⁻¹ * ∑ y, eLpNorm (fun x => Tg x y) (ENNReal.ofReal s) volume ^ s
      ≤ (P : ℝ≥0∞)⁻¹ * ∑ y, (ENNReal.ofReal A * eLpNorm (fun x => g x y) (ENNReal.ofReal s) volume) ^ s := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun y _ => ?_)
        exact ENNReal.rpow_le_rpow (hScalar _ (hgm y) (hgi y) (hgb y)) hs0.le
    _ = ENNReal.ofReal A ^ s * ((P : ℝ≥0∞)⁻¹ * ∑ y, eLpNorm (fun x => g x y) (ENNReal.ofReal s) volume ^ s) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le]
        rw [← Finset.mul_sum]
        ring

end PrimeBHT.TimeFrequency.X2.CZ
