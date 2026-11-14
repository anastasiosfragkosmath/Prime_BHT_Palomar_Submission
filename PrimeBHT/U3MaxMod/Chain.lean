module

public import PrimeBHT.U3MaxMod.Basic

/-!
# `l:U3maxmod`, part 2: the Cauchy-Schwarz chain

For `I`, `D` finite with `D ⊇ I - I` and `c` supported in `I`,
`(∑_x |S(x)|²)⁴ ≤ |D|⁴ (∑ |f|⁴)² (∑ |g|⁴)² ∑_{h,k ∈ D} |A(h,k)|²`
where `A(h,k) = ∑_n Δ_{h,k} c(n)` (steps 2-4 of the blueprint).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson PrimeCarleson.Proof.Common

/-- Cauchy-Schwarz for sums from termwise Cauchy-Schwarz. -/
lemma sq_sum_le_of_sq_le {ι : Type*} (s : Finset ι) (z α β : ι → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (h : ∀ i, z i ^ 2 ≤ α i * β i) :
    (∑ i ∈ s, z i) ^ 2 ≤ (∑ i ∈ s, α i) * ∑ i ∈ s, β i := by
  have h1 : ∀ i, z i ≤ Real.sqrt (α i) * Real.sqrt (β i) := fun i => by
    rw [← Real.sqrt_mul (hα i)]
    exact Real.le_sqrt_of_sq_le (h i)
  calc (∑ i ∈ s, z i) ^ 2
      ≤ (∑ i ∈ s, Real.sqrt (α i) * Real.sqrt (β i)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hz i) (Finset.sum_le_sum fun i _ => h1 i) 2
    _ ≤ (∑ i ∈ s, Real.sqrt (α i) ^ 2) * ∑ i ∈ s, Real.sqrt (β i) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = _ := by
        simp only [Real.sq_sqrt (hα _), Real.sq_sqrt (hβ _)]

lemma amgm4 (a b c d : ℝ) :
    a * b * c * d ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2), sq_nonneg (a * b - c * d)]

lemma summable_norm_pow_shift {g : ℤ → ℂ} (hg : (Function.support g).Finite) (a : ℤ) (m : ℕ) :
    Summable (fun x => ‖g (x + a)‖ ^ (m + 1)) :=
  summable_of_hasFiniteSupport (fin_supp_of_imp a hg fun x hx h0 => hx (by simp [h0]))

lemma tsum_norm_pow_shift (g : ℤ → ℂ) (a : ℤ) (m : ℕ) :
    ∑' x, ‖g (x + a)‖ ^ m = ∑' x, ‖g x‖ ^ m :=
  (Equiv.addRight a).tsum_eq (fun x => ‖g x‖ ^ m)

/-- **(G4)**: `|∑_x Δ_{h,k} g(x)| ≤ ‖g‖_4^4`. -/
theorem norm_tsum_multDiff_two_le (g : ℤ → ℂ) (hg : (Function.support g).Finite) (h k : ℤ) :
    ‖∑' x, multDiff 2 ![h, k] g x‖ ≤ ∑' x, ‖g x‖ ^ 4 := by
  have hp : ∀ a : ℤ, Summable (fun x => ‖g (x + a)‖ ^ 4) := fun a =>
    summable_norm_pow_shift hg a 3
  have hp0 : Summable (fun x => ‖g x‖ ^ 4) := by simpa using hp 0
  have hs : ∀ a : ℤ, HasSum (fun x => ‖g (x + a)‖ ^ 4) (∑' x, ‖g x‖ ^ 4) := fun a => by
    rw [← tsum_norm_pow_shift g a 4]; exact (hp a).hasSum
  have hF : Summable (fun x => ‖multDiff 2 ![h, k] g x‖) :=
    summable_of_hasFiniteSupport (fin_supp_of_imp'
      (F := fun x => ‖multDiff 2 ![h, k] g x‖) hg fun x hx h0 => hx (by
        simp only [multDiff_two_eq, h0]; simp))
  have hS : HasSum (fun x => (‖g x‖ ^ 4 + ‖g (x + h)‖ ^ 4 + ‖g (x + k)‖ ^ 4 +
      ‖g (x + k + h)‖ ^ 4) / 4) ((∑' x, ‖g x‖ ^ 4 + ∑' x, ‖g x‖ ^ 4 + ∑' x, ‖g x‖ ^ 4 +
      ∑' x, ‖g x‖ ^ 4) / 4) := by
    have h0 : HasSum (fun x => ‖g x‖ ^ 4) (∑' x, ‖g x‖ ^ 4) := hp0.hasSum
    have h3 : HasSum (fun x => ‖g (x + k + h)‖ ^ 4) (∑' x, ‖g x‖ ^ 4) := by
      rw [← tsum_norm_pow_shift g (k + h) 4]
      simpa [add_assoc] using (hp (k + h)).hasSum
    exact (((h0.add (hs h)).add (hs k)).add h3).div_const 4
  calc ‖∑' x, multDiff 2 ![h, k] g x‖ ≤ ∑' x, ‖multDiff 2 ![h, k] g x‖ :=
        norm_tsum_le_tsum_norm hF
    _ ≤ ∑' x, (‖g x‖ ^ 4 + ‖g (x + h)‖ ^ 4 + ‖g (x + k)‖ ^ 4 + ‖g (x + k + h)‖ ^ 4) / 4 := by
        refine hF.tsum_le_tsum (fun x => ?_) hS.summable
        rw [multDiff_two_eq]
        simp only [norm_mul, RCLike.norm_conj]
        rw [← mul_assoc]
        exact amgm4 _ _ _ _
    _ = ∑' x, ‖g x‖ ^ 4 := by
        rw [hS.tsum_eq]; ring


/-- **(G6)** for one shift: `∑_y |f y|² |f (y - h)|² ≤ ‖f‖_4^4`. -/
lemma tsum_sq_aF_le (f : ℤ → ℂ) (hf : (Function.support f).Finite) (h : ℤ) :
    ∑' y, ‖aF f h y‖ ^ 2 ≤ ∑' y, ‖f y‖ ^ 4 := by
  have hp0 : Summable (fun x => ‖f x‖ ^ 4) := by simpa using summable_norm_pow_shift hf 0 3
  have hp1 : HasSum (fun x => ‖f (x + -h)‖ ^ 4) (∑' x, ‖f x‖ ^ 4) := by
    rw [← tsum_norm_pow_shift f (-h) 4]; exact (summable_norm_pow_shift hf (-h) 3).hasSum
  have hs : HasSum (fun x => (‖f x‖ ^ 4 + ‖f (x + -h)‖ ^ 4) / 2)
      ((∑' x, ‖f x‖ ^ 4 + ∑' x, ‖f x‖ ^ 4) / 2) := (hp0.hasSum.add hp1).div_const 2
  have hF : Summable (fun y => ‖aF f h y‖ ^ 2) :=
    summable_of_hasFiniteSupport (fin_supp_of_imp' (F := fun y => ‖aF f h y‖ ^ 2) hf
      (fun y hy h0 => hy (by simp [aF, h0])))
  calc ∑' y, ‖aF f h y‖ ^ 2 ≤ ∑' y, (‖f y‖ ^ 4 + ‖f (y + -h)‖ ^ 4) / 2 := by
        refine hF.tsum_le_tsum (fun y => ?_) hs.summable
        simp only [aF, norm_mul, RCLike.norm_conj, ← sub_eq_add_neg]
        nlinarith [sq_nonneg (‖f y‖ ^ 2 - ‖f (y - h)‖ ^ 2)]
    _ = ∑' y, ‖f y‖ ^ 4 := by rw [hs.tsum_eq]; ring

/-- **Steps 2-4 of `l:U3maxmod`** (Cauchy-Schwarz chain). -/
theorem fourth_power_le (I D : Finset ℤ) (hD : ∀ n ∈ I, ∀ n' ∈ I, n' - n ∈ D)
    (c : ℤ → ℂ) (hc : ∀ n, n ∉ I → c n = 0) (f g : ℤ → ℂ)
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    (∑' x, ‖sF I c f g x‖ ^ 2) ^ 4 ≤ (D.card : ℝ) ^ 4 * (∑' x, ‖f x‖ ^ 4) ^ 2 *
      (∑' x, ‖g x‖ ^ 4) ^ 2 * ∑ h ∈ D, ∑ k ∈ D, ‖AF I c h k‖ ^ 2 := by
  set L : ℝ := ∑' x, ‖sF I c f g x‖ ^ 2 with hLdef
  set u : ℝ := ∑' x, ‖f x‖ ^ 4 with hudef
  set v : ℝ := ∑' x, ‖g x‖ ^ 4 with hvdef
  set w : ℝ := ∑ h ∈ D, ∑ k ∈ D, ‖AF I c h k‖ ^ 2 with hwdef
  set d : ℝ := (D.card : ℝ) with hd
  set α : ℤ → ℝ := fun h => ∑' y, ‖aF f h y‖ ^ 2 with hα
  set β : ℤ → ℝ := fun h => ∑' y, ‖bF I c g h y‖ ^ 2 with hβ
  have hL0 : 0 ≤ L := tsum_nonneg fun x => by positivity
  have hu0 : 0 ≤ u := tsum_nonneg fun x => by positivity
  have hv0 : 0 ≤ v := tsum_nonneg fun x => by positivity
  have hα0 : ∀ h, 0 ≤ α h := fun h => tsum_nonneg fun y => by positivity
  have hβ0 : ∀ h, 0 ≤ β h := fun h => tsum_nonneg fun y => by positivity
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hLc : (L : ℂ) = ∑ h ∈ D, ∑' y, aF f h y * bF I c g h y := by
    rw [← sq_tsum_eq_sum_tsum I D hD c hc f g hf, hLdef, Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hL1 : L ≤ ∑ h ∈ D, ‖∑' y, aF f h y * bF I c g h y‖ := by
    have : L = ‖(L : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hL0]
    rw [this, hLc]
    exact norm_sum_le _ _
  have hz : ∀ h, ‖∑' y, aF f h y * bF I c g h y‖ ^ 2 ≤ α h * β h := by
    intro h
    have := GowersCS.norm_tsum_mul_conj_sq_le (aF f h) (fun y => conj (bF I c g h y)) (fs_aF hf h)
      (fin_supp_of_imp' (fs_bF I c hg h) fun y hy h0 => hy (by simp [h0]))
    simpa [Complex.conj_conj, α, β] using this
  have h1 := sq_sum_le_of_sq_le D (fun h => ‖∑' y, aF f h y * bF I c g h y‖) α β
    (fun h => norm_nonneg _) hα0 hβ0 hz
  have hL2 : L ^ 2 ≤ (∑ h ∈ D, α h) * ∑ h ∈ D, β h :=
    (pow_le_pow_left₀ hL0 hL1 2).trans h1
  have hαsum : ∑ h ∈ D, α h ≤ d * u := by
    calc ∑ h ∈ D, α h ≤ ∑ h ∈ D, u := Finset.sum_le_sum fun h _ => tsum_sq_aF_le f hf h
      _ = d * u := by simp [hd]
  have hβle : ∀ h, β h ≤ ∑ k ∈ D, ‖AF I c h k‖ * ‖GF g h k‖ := by
    intro h
    have hh := sq_tsum_bF I D hD c hc g hg h
    have : β h = ‖((β h : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg (hβ0 h)]
    rw [this]
    show ‖(((∑' y, ‖bF I c g h y‖ ^ 2 : ℝ)) : ℂ)‖ ≤ _
    rw [hh]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun k _ => norm_mul _ _
  have hGle : ∀ h k, ‖GF g h k‖ ≤ v := fun h k => norm_tsum_multDiff_two_le g hg h (2 * k)
  set B : ℝ := ∑ h ∈ D, β h with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun h _ => hβ0 h
  have hBle : B ≤ ∑ h ∈ D, ∑ k ∈ D, ‖AF I c h k‖ * ‖GF g h k‖ :=
    Finset.sum_le_sum fun h _ => hβle h
  have hCS : (∑ h ∈ D, ∑ k ∈ D, ‖AF I c h k‖ * ‖GF g h k‖) ^ 2 ≤ w * (d ^ 2 * v ^ 2) := by
    rw [← Finset.sum_product' (f := fun h k => ‖AF I c h k‖ * ‖GF g h k‖)]
    calc (∑ p ∈ D ×ˢ D, ‖AF I c p.1 p.2‖ * ‖GF g p.1 p.2‖) ^ 2
        ≤ (∑ p ∈ D ×ˢ D, ‖AF I c p.1 p.2‖ ^ 2) * ∑ p ∈ D ×ˢ D, ‖GF g p.1 p.2‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ w * (d ^ 2 * v ^ 2) := by
        have e1 : ∑ p ∈ D ×ˢ D, ‖AF I c p.1 p.2‖ ^ 2 = w := by
          rw [Finset.sum_product]
        have e2 : ∑ p ∈ D ×ˢ D, ‖GF g p.1 p.2‖ ^ 2 ≤ d ^ 2 * v ^ 2 := by
          calc ∑ p ∈ D ×ˢ D, ‖GF g p.1 p.2‖ ^ 2 ≤ ∑ p ∈ D ×ˢ D, v ^ 2 :=
                Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (hGle _ _) 2
            _ = d ^ 2 * v ^ 2 := by
                rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
                simp only [hd]
                push_cast
                ring
        rw [e1]
        exact mul_le_mul_of_nonneg_left e2 (Finset.sum_nonneg fun h _ =>
          Finset.sum_nonneg fun k _ => by positivity)
  have hB2 : B ^ 2 ≤ w * (d ^ 2 * v ^ 2) := (pow_le_pow_left₀ hB0 hBle 2).trans hCS
  have hL3 : L ^ 2 ≤ d * u * B :=
    hL2.trans (mul_le_mul_of_nonneg_right hαsum hB0)
  have hw0 : 0 ≤ w := Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun k _ => by positivity
  calc L ^ 4 = (L ^ 2) ^ 2 := by ring
    _ ≤ (d * u * B) ^ 2 := pow_le_pow_left₀ (sq_nonneg L) hL3 2
    _ = d ^ 2 * u ^ 2 * B ^ 2 := by ring
    _ ≤ d ^ 2 * u ^ 2 * (w * (d ^ 2 * v ^ 2)) := by gcongr
    _ = d ^ 4 * u ^ 2 * v ^ 2 * w := by ring

end PrimeBHT.U3MaxMod
