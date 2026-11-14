module

public import PrimeBHT.PeriodicBlock
public import PrimeBHT.Lift
public import PrimeBHT.Transference
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.MeanInequalities

/-!
# N42 (42e): the twisted form `Π_{B,d,v}`

On `Y_N = ZMod N` (normalized counting measure), with `e_N(x) = ZMod.stdAddChar x`
(`= exp(2πi x/N)`) and the characters `e_a(y) = e_N(a y)` (`charN a`):

* `twistedForm Λ d v F₁ F₂ F₃ = 𝔼_{y,t} Λ(t) e_N(vy - dt) F₁(y-t) F₂(y+t) conj(F₃ y)`;
* `twistedForm_charN`: `Π_{B,d,v}(e_a,e_b,e_c) = 1_{a+b-c+v = 0} F_N(Λ)(a-b+d)`;
* `twistedForm_eq_trilinForm`: `Π_{B,d,v}(F₁,F₂,F₃) = Π_B(e_d F₁, F₂, e_{d-v} F₃)`;
* `norm_twistedForm_le` (`e:twisted-Pi-norm`, inequality form): if
  `‖A_B(F,G)‖_{L^p} ≤ D ‖F‖₂ ‖G‖₂` for all `F, G`, and `1/p + 1/u = 1`, then
  `|Π_{B,d,v}(F₁,F₂,F₃)| ≤ D ‖F₁‖₂ ‖F₂‖₂ ‖F₃‖_{L^u}`, for all `d v : ZMod N` (in particular for
  the casts of all integers `d, v`).

`F_N(Λ)(ℓ) = 𝔼_t Λ(t) e_N(-ℓ t)` is `fourierN`.
-/

@[expose] public section

namespace PrimeBHT.TransferenceAssembly

open Finset PrimeBHT.PeriodicBlock PrimeBHT.Lift
open scoped BigOperators ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- The character `e_a(y) = e_N(a y)` on `Y_N`. -/
noncomputable def charN (a : ZMod N) (y : ZMod N) : ℂ := ZMod.stdAddChar (a * y)

/-- The normalized Fourier transform on `Y_N`: `F_N Λ (ℓ) = 𝔼_t Λ(t) e_N(-ℓ t)`. -/
noncomputable def fourierN (Λ : ZMod N → ℂ) (ℓ : ZMod N) : ℂ :=
  𝔼 t, Λ t * ZMod.stdAddChar (-(ℓ * t))

/-- The twisted form `Π_{B,d,v}(F₁,F₂,F₃) = 𝔼_{y,t} Λ(t) e_N(vy-dt) F₁(y-t) F₂(y+t) conj(F₃ y)`. -/
noncomputable def twistedForm (Λ : ZMod N → ℂ) (d v : ZMod N) (F₁ F₂ F₃ : ZMod N → ℂ) : ℂ :=
  𝔼 y, 𝔼 t, Λ t * ZMod.stdAddChar (v * y - d * t) * F₁ (y - t) * F₂ (y + t) * conj (F₃ y)

theorem norm_stdAddChar (x : ZMod N) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

theorem norm_charN (a y : ZMod N) : ‖charN a y‖ = 1 := norm_stdAddChar _

/-- Orthogonality: `𝔼_y e_N(y m) = 1_{m = 0}`. -/
theorem expect_stdAddChar_mul (m : ZMod N) :
    𝔼 y, (ZMod.stdAddChar (y * m) : ℂ) = if m = 0 then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, AddChar.sum_mulShift m (ZMod.isPrimitive_stdAddChar N)]
  have hN : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  simp only [ZMod.card]
  split_ifs
  · exact div_self hN
  · simp

/-- (42e) `Π_{B,d,v}(e_a, e_b, e_c) = 1_{a+b-c+v ≡ 0 (N)} F_N(Λ_B)(a - b + d)`. -/
theorem twistedForm_charN (Λ : ZMod N → ℂ) (d v a b c : ZMod N) :
    twistedForm Λ d v (charN a) (charN b) (charN c) =
      if a + b - c + v = 0 then fourierN Λ (a - b + d) else 0 := by
  have key : ∀ y t : ZMod N,
      Λ t * ZMod.stdAddChar (v * y - d * t) * charN a (y - t) * charN b (y + t) *
          conj (charN c y) =
        ZMod.stdAddChar (y * (a + b - c + v)) * (Λ t * ZMod.stdAddChar (-((a - b + d) * t))) := by
    intro y t
    unfold charN
    rw [← AddChar.map_neg_eq_conj]
    have h1 : (ZMod.stdAddChar (v * y - d * t) : ℂ) * ZMod.stdAddChar (a * (y - t)) *
        ZMod.stdAddChar (b * (y + t)) * ZMod.stdAddChar (-(c * y)) =
        ZMod.stdAddChar (y * (a + b - c + v)) * ZMod.stdAddChar (-((a - b + d) * t)) := by
      simp only [← AddChar.map_add_eq_mul]
      congr 1; ring
    calc _ = Λ t * ((ZMod.stdAddChar (v * y - d * t) : ℂ) * ZMod.stdAddChar (a * (y - t)) *
        ZMod.stdAddChar (b * (y + t)) * ZMod.stdAddChar (-(c * y))) := by ring
      _ = _ := by rw [h1]; ring
  unfold twistedForm
  simp_rw [key, ← Finset.mul_expect, ← Finset.expect_mul]
  rw [expect_stdAddChar_mul]
  unfold fourierN
  split_ifs <;> simp

/-- (42e) `Π_{B,d,v}(F₁,F₂,F₃) = Π_B(e_d F₁, F₂, e_{d-v} F₃)`. -/
theorem twistedForm_eq_trilinForm (Λ : ZMod N → ℂ) (d v : ZMod N) (F₁ F₂ F₃ : ZMod N → ℂ) :
    twistedForm Λ d v F₁ F₂ F₃ =
      trilinForm Λ (fun y => charN d y * F₁ y) F₂ (fun y => charN (d - v) y * F₃ y) := by
  rw [trilinForm_eq]
  unfold twistedForm
  refine Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => ?_
  unfold charN
  rw [map_mul (starRingEnd ℂ), ← AddChar.map_neg_eq_conj]
  have h1 : (ZMod.stdAddChar (v * y - d * t) : ℂ) =
      ZMod.stdAddChar (d * (y - t)) * ZMod.stdAddChar (-((d - v) * y)) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [h1]; ring

/-- Modulation by a character does not change `l2`. -/
theorem l2_charN_mul (a : ZMod N) (F : ZMod N → ℂ) : l2 (fun y => charN a y * F y) = l2 F := by
  unfold l2; simp only [norm_mul, norm_charN, one_mul]

/-- Modulation by a character does not change `yNorm`. -/
theorem yNorm_charN_mul (s : ℝ) (a : ZMod N) (F : ZMod N → ℂ) :
    yNorm s (fun y => charN a y * F y) = yNorm s F := by
  unfold yNorm; simp only [norm_mul, norm_charN, one_mul]

/-- Hölder on the probability space `Y_N`:
`|𝔼_y A(y) conj(H y)| ≤ ‖A‖_{L^p} ‖H‖_{L^u}` for conjugate exponents. -/
theorem norm_expect_mul_conj_le {p u : ℝ} (hpu : p.HolderConjugate u) (A H : ZMod N → ℂ) :
    ‖𝔼 y, A y * conj (H y)‖ ≤ yNorm p A * yNorm u H := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNi : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN.le
  have hp0 : 0 < p := hpu.pos
  have hu0 : 0 < u := hpu.symm.pos
  calc ‖𝔼 y, A y * conj (H y)‖ ≤ 𝔼 y, ‖A y * conj (H y)‖ := RCLike.norm_expect_le (K := ℝ)
    _ = (N : ℝ)⁻¹ * ∑ y, ‖A y‖ * ‖H y‖ := by
        rw [Fintype.expect_eq_sum_div_card, ZMod.card, div_eq_inv_mul]
        simp only [norm_mul, RCLike.norm_conj]
    _ ≤ (N : ℝ)⁻¹ * ((∑ y, ‖A y‖ ^ p) ^ (1 / p) * (∑ y, ‖H y‖ ^ u) ^ (1 / u)) := by
        gcongr
        exact Real.inner_le_Lp_mul_Lq_of_nonneg _ hpu (fun _ _ => norm_nonneg _)
          (fun _ _ => norm_nonneg _)
    _ = yNorm p A * yNorm u H := by
        unfold yNorm
        have hs1 : 0 ≤ ∑ y, ‖A y‖ ^ p := Finset.sum_nonneg fun _ _ => by positivity
        have hs2 : 0 ≤ ∑ y, ‖H y‖ ^ u := Finset.sum_nonneg fun _ _ => by positivity
        rw [Real.mul_rpow hNi hs1, Real.mul_rpow hNi hs2, one_div, one_div]
        have hsplit : (N : ℝ)⁻¹ = (N : ℝ)⁻¹ ^ p⁻¹ * (N : ℝ)⁻¹ ^ u⁻¹ := by
          rw [← Real.rpow_add (inv_pos.2 hN), hpu.inv_add_inv_eq_one, Real.rpow_one]
        conv_lhs => rw [hsplit]
        ring

/-- (42e, `e:twisted-Pi-norm`, inequality form) If `‖A_B(F,G)‖_{L^p} ≤ D ‖F‖₂ ‖G‖₂` for all
`F, G` and `1/p + 1/u = 1`, then `|Π_{B,d,v}(F₁,F₂,F₃)| ≤ D ‖F₁‖₂ ‖F₂‖₂ ‖F₃‖_{L^u}`,
uniformly in `d, v`. -/
theorem norm_twistedForm_le {p u D : ℝ} (hpu : p.HolderConjugate u) (Λ : ZMod N → ℂ)
    (hD : ∀ F G : ZMod N → ℂ, yNorm p (bilinAvg Λ F G) ≤ D * l2 F * l2 G)
    (d v : ZMod N) (F₁ F₂ F₃ : ZMod N → ℂ) :
    ‖twistedForm Λ d v F₁ F₂ F₃‖ ≤ D * l2 F₁ * l2 F₂ * yNorm u F₃ := by
  rw [twistedForm_eq_trilinForm, trilinForm]
  refine (norm_expect_mul_conj_le hpu _ _).trans ?_
  rw [yNorm_charN_mul]
  have h := hD (fun y => charN d y * F₁ y) F₂
  rw [l2_charN_mul] at h
  exact mul_le_mul_of_nonneg_right h (yNorm_nonneg _ _)

section Sesquilinear

variable (Λ : ZMod N → ℂ) (d v : ZMod N)

/-- `F₃ ↦ Π_{B,d,v}(F₁,F₂,F₃)` is conjugate-linear. -/
noncomputable def twistedFormConj (F₁ F₂ : ZMod N → ℂ) : (ZMod N → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun F₃ := twistedForm Λ d v F₁ F₂ F₃
  map_add' F G := by
    simp only [twistedForm, Pi.add_apply, map_add, ← Finset.expect_add_distrib]
    exact Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => by ring
  map_smul' c F := by
    simp only [twistedForm, Pi.smul_apply, smul_eq_mul, map_mul,
      Finset.mul_expect]
    exact Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => by ring

/-- `Π_{B,d,v}` as a form: complex-linear in slots 1 and 2, conjugate-linear in slot 3 (the shape
of `Π` in `BilinearVVBound`). -/
noncomputable def twistedFormMap :
    (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (twistedFormConj Λ d v)
    (fun F G H => LinearMap.ext fun K => by
      simp only [twistedFormConj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        twistedForm, Pi.add_apply, ← Finset.expect_add_distrib]
      exact Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => by ring)
    (fun c F G => LinearMap.ext fun K => by
      simp only [twistedFormConj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        twistedForm, Pi.smul_apply, smul_eq_mul, Finset.mul_expect]
      exact Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => by ring)
    (fun F G H => LinearMap.ext fun K => by
      simp only [twistedFormConj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        twistedForm, Pi.add_apply, ← Finset.expect_add_distrib]
      exact Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => by ring)
    (fun c F G => LinearMap.ext fun K => by
      simp only [twistedFormConj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        twistedForm, Pi.smul_apply, smul_eq_mul, Finset.mul_expect]
      exact Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun t _ => by ring)

@[simp] theorem twistedFormMap_apply (F₁ F₂ F₃ : ZMod N → ℂ) :
    twistedFormMap Λ d v F₁ F₂ F₃ = twistedForm Λ d v F₁ F₂ F₃ := rfl

/-- The norm bound for `twistedFormMap` in the form required by `BilinearVVBound`. -/
theorem norm_twistedFormMap_le {p u D : ℝ} (hpu : p.HolderConjugate u)
    (hD : ∀ F G : ZMod N → ℂ, yNorm p (bilinAvg Λ F G) ≤ D * l2 F * l2 G)
    (F₁ F₂ F₃ : ZMod N → ℂ) :
    ‖twistedFormMap Λ d v F₁ F₂ F₃‖ ≤ D * l2 F₁ * l2 F₂ * yNorm u F₃ :=
  norm_twistedForm_le hpu Λ hD d v F₁ F₂ F₃

end Sesquilinear

/-- `fourierN` agrees with `Transference.finFourier` (the `F_N` of the sampled multiplier, 42c). -/
theorem fourierN_eq_finFourier (w : ℤ → ℂ) (ℓ : ZMod N) :
    fourierN (fun r : ZMod N => w (r.val : ℤ)) ℓ = Transference.finFourier N w ℓ := by
  unfold fourierN Transference.finFourier
  rw [Fintype.expect_eq_sum_div_card, ZMod.card, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have h : -(ℓ * r) = (((-((ℓ.val : ℤ) * r.val)) : ℤ) : ZMod N) := by
    push_cast; simp
  rw [h, ZMod.stdAddChar_coe]
  unfold PrimeCarleson.e
  congr 1
  push_cast
  ring

/-- (42f, the algebra of step 7) Multilinear expansion of `Π_{B,d,v}` on character sums:
`Π_{B,d,v}(∑_a x_a e_a, ∑_b y_b e_b, ∑_c z_c e_c)
  = ∑_{c,b,a} x_a y_b conj(z_c) 1_{a+b-c+v = 0} F_N(Λ)(a-b+d)`. -/
theorem twistedForm_sum_charN (Λ : ZMod N → ℂ) (d v : ZMod N) (x y z : ZMod N → ℂ) :
    twistedForm Λ d v (fun t => ∑ a, x a * charN a t) (fun t => ∑ b, y b * charN b t)
        (fun t => ∑ c, z c * charN c t) =
      ∑ c, ∑ b, ∑ a, x a * y b * conj (z c) *
        (if a + b - c + v = 0 then fourierN Λ (a - b + d) else 0) := by
  have hs : ∀ w : ZMod N → ℂ, (fun t => ∑ a, w a * charN a t) = ∑ a, w a • charN a := by
    intro w; ext t; simp [Finset.sum_apply]
  rw [← twistedFormMap_apply, hs x, hs y, hs z]
  simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    twistedFormMap_apply, twistedForm_charN, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

end PrimeBHT.TransferenceAssembly
