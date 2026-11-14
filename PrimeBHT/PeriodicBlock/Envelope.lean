module

public import PrimeBHT.PeriodicBlock.Divisor
public import PrimeCarleson.Proof.Goal0.Fiber
public import Mathlib.Analysis.Fourier.ZMod

/-!
# The fibre envelope (blueprint N33)

Setting: `d, D` coprime, `N = d D`, `Y_N = ZMod (d * D) ≅ ZMod d × ZMod D` via
`ZMod.chineseRemainder`. `lamCRT B hdD α β = Λ_B(CRT⁻¹(α, β))`, `fourierZMod` is the normalized
`D`-Fourier transform `𝓕_D u(ξ) = 𝔼_β u(β) e_D(-ξ β)`, `sigmaD d α = ∑_{g | gcd(d, α)} g`,
`envelope B hB d α = d_div(d) · (max_{q ∈ B} 1/φ(q)) · σ_d(α)`.

* `norm_fourierZMod_lamCRT_le` (N33(i)): `sup_ξ |𝓕_D(Λ_B(α, ·))(ξ)| ≤ H_d(α)`;
* `expect_envelope_eq` / `expect_envelope_le` (N33(ii)): `𝔼_α H_d(α) = d_div(d)² max_q 1/φ(q) ≤ C_ε Q^{ε-1}`.

The proof reduces (through the affine reindexing `β = u + d l` of `ZMod D`) to the audited
integer-coordinate envelope `Goal0.norm_avg_blockWeight_le` of the vendored library, followed by
the sharper count `|c_{q₁}(α)| ≤ σ_d(α)` of the blueprint.
-/

@[expose] public section

namespace PrimeBHT.PeriodicBlock

open Finset PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Goal0
open scoped BigOperators ComplexConjugate

/-- The normalized `D`-Fourier transform `𝓕_D u(ξ) = 𝔼_β u(β) e_D(-ξ β)` on `ZMod D`. -/
noncomputable def fourierZMod {D : ℕ} [NeZero D] (u : ZMod D → ℂ) (ξ : ZMod D) : ℂ :=
  𝔼 β, u β * ZMod.stdAddChar (-(ξ * β))

/-- `σ_d(α) = ∑_{g | gcd(d, α)} g` for `α ∈ ZMod d` (`gcd(d, 0) = d`). -/
def sigmaD (d : ℕ) [NeZero d] (α : ZMod d) : ℕ := ∑ g ∈ (Nat.gcd d α.val).divisors, g

/-- `max_{q ∈ B} 1/φ(q)` for a nonempty block. -/
noncomputable def maxInvTotient (B : Finset ℕ) (hB : B.Nonempty) : ℝ :=
  B.sup' hB fun q => ((q.totient : ℝ))⁻¹

/-- The fibre envelope `H_d(α) = d_div(d) · (max_{q ∈ B} φ(q)⁻¹) · σ_d(α)`. -/
noncomputable def envelope (B : Finset ℕ) (hB : B.Nonempty) (d : ℕ) [NeZero d] (α : ZMod d) : ℝ :=
  (d.divisors.card : ℝ) * maxInvTotient B hB * (sigmaD d α : ℝ)

/-- `Λ_B(α, β) = Λ_B(CRT⁻¹(α, β))` on `Y_d × Y_D`, `N = d D`. -/
noncomputable def lamCRT (B : Finset ℕ) {d D : ℕ} (hdD : d.Coprime D) (α : ZMod d) (β : ZMod D) :
    ℂ :=
  lam B (d * D) ((ZMod.chineseRemainder hdD).symm (α, β))

theorem inv_totient_le_maxInvTotient {B : Finset ℕ} (hB : B.Nonempty) {q : ℕ} (hq : q ∈ B) :
    ((q.totient : ℝ))⁻¹ ≤ maxInvTotient B hB :=
  Finset.le_sup' (fun q => ((q.totient : ℝ))⁻¹) hq

theorem maxInvTotient_nonneg {B : Finset ℕ} (hB : B.Nonempty) : 0 ≤ maxInvTotient B hB := by
  obtain ⟨q, hq⟩ := hB
  exact (inv_nonneg.2 (Nat.cast_nonneg _)).trans (inv_totient_le_maxInvTotient ⟨q, hq⟩ hq)

/-! ### The integer-coordinate envelope with the sharper count `σ_d(u)` -/

/-- The envelope of the vendored library with the sharper factor `∑_{f | d, f | u} f` (the blueprint's
`σ_d(u)`) in place of `∑_{r | d} |c_r(u)|`. -/
theorem norm_avg_blockWeight_le_sigma {B : Finset ℕ} {d D : ℕ} (hd : 0 < d) (hD : 0 < D)
    (hdD : d.Coprime D) (hB : ∀ q ∈ B, q ∣ d * D) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ M) (ρ u : ℤ) :
    ‖(D : ℂ)⁻¹ * ∑ l ∈ Finset.range D, blockWeight B (u + d * l) * e ((l : ℝ) * ρ / D)‖ ≤
      d.divisors.card * M * ∑ f ∈ d.divisors with ((f : ℕ) : ℤ) ∣ u, (f : ℝ) := by
  refine (norm_avg_blockWeight_le hD hdD hB ρ u).trans ?_
  have hg : 0 < Int.gcd ρ D := Int.gcd_pos_of_ne_zero_right ρ (by exact_mod_cast hD.ne')
  set S : ℝ := ∑ f ∈ d.divisors with ((f : ℕ) : ℤ) ∣ u, (f : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun f _ => Nat.cast_nonneg _
  have hsub : (B.filter fun q => Nat.gcd q D * Int.gcd ρ D = D) ⊆
      B.filter fun q => Nat.gcd q D = D / Int.gcd ρ D := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, (Nat.div_eq_of_eq_mul_left hg hq.2.symm).symm⟩
  have hcard := (Finset.card_le_card hsub).trans
    (card_filter_gcd_eq_le hd hdD hB (D / Int.gcd ρ D))
  calc ∑ q ∈ B with Nat.gcd q D * Int.gcd ρ D = D,
        ‖ramanujanSum (Nat.gcd q d) u‖ / (q.totient : ℝ)
      ≤ ∑ q ∈ B with Nat.gcd q D * Int.gcd ρ D = D, M * S := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_filter] at hq
        have h1 : ‖ramanujanSum (Nat.gcd q d) u‖ ≤ S := by
          refine (norm_ramanujanSum_le _ _).trans ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun f _ _ => Nat.cast_nonneg _
          intro f hf
          simp only [Finset.mem_filter, Nat.mem_divisors] at hf ⊢
          exact ⟨⟨hf.1.1.trans (Nat.gcd_dvd_right q d), hd.ne'⟩, hf.2⟩
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul (hM q hq.1) h1 (norm_nonneg _) hM0
    _ = ((B.filter fun q => Nat.gcd q D * Int.gcd ρ D = D).card : ℝ) * (M * S) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ d.divisors.card * (M * S) := by
        gcongr
    _ = d.divisors.card * M * S := by ring

/-! ### CRT coordinates -/

section CRT

variable {d D : ℕ}

/-- The CRT preimage of the pair `(α, β)` is the class of any integer `n` with `n ≡ α (d)`,
`n ≡ β (D)`. -/
theorem chineseRemainder_symm_intCast (hdD : d.Coprime D) (α : ZMod d) (β : ZMod D) (n : ℤ)
    (h1 : (n : ZMod d) = α) (h2 : (n : ZMod D) = β) :
    (ZMod.chineseRemainder hdD).symm (α, β) = ((n : ℤ) : ZMod (d * D)) := by
  rw [RingEquiv.symm_apply_eq, map_intCast]
  exact Prod.ext h1.symm h2.symm

/-- The affine reindexing `l ↦ u + d l` of `ZMod D` (a bijection as `d` is a unit mod `D`). -/
def affEquiv [NeZero D] (hdD : d.Coprime D) (u : ZMod D) : ZMod D ≃ ZMod D :=
  (Units.mulLeft (ZMod.unitOfCoprime d hdD)).trans (Equiv.addLeft u)

theorem affEquiv_apply [NeZero D] (hdD : d.Coprime D) (u l : ZMod D) :
    affEquiv hdD u l = u + (d : ZMod D) * l := by
  simp [affEquiv, ZMod.coe_unitOfCoprime]

/-- `Λ_B(α, u + d l) = w_B(α.val + d · l.val)` (the CRT preimage is the residue class of the
integer `α.val + d l.val`). -/
theorem lamCRT_affEquiv [NeZero d] [NeZero D] {B : Finset ℕ} (hdD : d.Coprime D) (hBN : ∀ q ∈ B, q ∣ d * D)
    (α : ZMod d) (l : ZMod D) :
    lamCRT B hdD α (affEquiv hdD ((α.val : ℕ) : ZMod D) l) =
      blockWeight B (((α.val : ℕ) : ℤ) + d * (l.val : ℤ)) := by
  unfold lamCRT
  rw [chineseRemainder_symm_intCast hdD α _ (((α.val : ℕ) : ℤ) + d * (l.val : ℤ)),
    lam_intCast hBN]
  · push_cast
    simp
  · push_cast
    rw [affEquiv_apply]
    simp

/-- Conversion of the `D`-Fourier transform of the fibre `Λ_B(α, ·)` to the integer-coordinate
average of the vendored envelope: with `u = α.val` and `ρ = -(ξ.val · d)`,
`𝓕_D(Λ_B(α, ·))(ξ) = e_D(-ξ u) · D⁻¹ ∑_{l < D} w_B(u + d l) e(l ρ / D)`. -/
theorem fourierZMod_lamCRT_eq [NeZero d] [NeZero D] {B : Finset ℕ} (hdD : d.Coprime D)
    (hBN : ∀ q ∈ B, q ∣ d * D) (α : ZMod d) (ξ : ZMod D) :
    fourierZMod (lamCRT B hdD α) ξ =
      ZMod.stdAddChar (-(ξ * ((α.val : ℕ) : ZMod D))) *
        ((D : ℂ)⁻¹ * ∑ l ∈ Finset.range D, blockWeight B (((α.val : ℕ) : ℤ) + d * (l : ℤ)) *
          e ((l : ℝ) * ((-((ξ.val : ℤ) * d) : ℤ) : ℝ) / D)) := by
  unfold fourierZMod
  rw [← Fintype.expect_equiv (affEquiv hdD ((α.val : ℕ) : ZMod D)) _ _ (fun _ => rfl)]
  have h1 : ∀ l : ZMod D, lamCRT B hdD α (affEquiv hdD ((α.val : ℕ) : ZMod D) l) *
      ZMod.stdAddChar (-(ξ * affEquiv hdD ((α.val : ℕ) : ZMod D) l)) =
      ZMod.stdAddChar (-(ξ * ((α.val : ℕ) : ZMod D))) *
        (blockWeight B (((α.val : ℕ) : ℤ) + d * (l.val : ℤ)) *
          e ((l.val : ℝ) * ((-((ξ.val : ℤ) * d) : ℤ) : ℝ) / D)) := by
    intro l
    rw [lamCRT_affEquiv hdD hBN, affEquiv_apply]
    have h2 : (-(ξ * (((α.val : ℕ) : ZMod D) + (d : ZMod D) * l)) : ZMod D) =
        -(ξ * ((α.val : ℕ) : ZMod D)) + (((-((ξ.val : ℤ) * d) * (l.val : ℤ) : ℤ)) : ZMod D) := by
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring
    rw [h2, AddChar.map_add_eq_mul, ZMod.stdAddChar_coe]
    have h3 : Complex.exp (2 * Real.pi * Complex.I *
        ((-((ξ.val : ℤ) * d) * (l.val : ℤ) : ℤ) : ℂ) / (D : ℂ)) =
        e ((l.val : ℝ) * ((-((ξ.val : ℤ) * d) : ℤ) : ℝ) / D) := by
      unfold e
      congr 1
      push_cast
      ring
    rw [h3]
    ring
  simp_rw [h1]
  rw [← Finset.mul_expect, Fintype.expect_eq_sum_div_card, ZMod.card, div_eq_inv_mul]
  congr 2
  exact sum_zmod_val D (fun l => blockWeight B (((α.val : ℕ) : ℤ) + d * (l : ℤ)) *
    e ((l : ℝ) * ((-((ξ.val : ℤ) * d) : ℤ) : ℝ) / D))

theorem sum_divisors_dvd_eq_sigmaD [NeZero d] (α : ZMod d) :
    ∑ f ∈ d.divisors with ((f : ℕ) : ℤ) ∣ ((α.val : ℕ) : ℤ), (f : ℝ) = (sigmaD d α : ℝ) := by
  unfold sigmaD
  push_cast
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨h1, h2⟩, fun h => NeZero.ne d (Nat.eq_zero_of_gcd_eq_zero_left h)⟩
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h1, NeZero.ne d⟩, h2⟩

/-- **N33(i)**: `sup_ξ |𝓕_D(Λ_B(α, ·))(ξ)| ≤ H_d(α)` for every `α ∈ Y_d`. -/
theorem norm_fourierZMod_lamCRT_le [NeZero d] [NeZero D] {B : Finset ℕ} (hB : B.Nonempty)
    (hdD : d.Coprime D) (hBN : ∀ q ∈ B, q ∣ d * D) (α : ZMod d) (ξ : ZMod D) :
    ‖fourierZMod (lamCRT B hdD α) ξ‖ ≤ envelope B hB d α := by
  rw [fourierZMod_lamCRT_eq hdD hBN α ξ, norm_mul]
  have h1 : ‖ZMod.stdAddChar (-(ξ * ((α.val : ℕ) : ZMod D)))‖ = 1 := by
    rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [h1, one_mul]
  have h2 := norm_avg_blockWeight_le_sigma (B := B) (Nat.pos_of_ne_zero (NeZero.ne d))
    (Nat.pos_of_ne_zero (NeZero.ne D)) hdD hBN (maxInvTotient_nonneg hB)
    (fun q hq => inv_totient_le_maxInvTotient hB hq) (-((ξ.val : ℤ) * d)) ((α.val : ℕ) : ℤ)
  rw [sum_divisors_dvd_eq_sigmaD] at h2
  exact h2

end CRT

/-! ### The average of the envelope (N33(ii)) -/

theorem avg_ite_dvd {d g : ℕ} (hd : 0 < d) (hg : g ∣ d) :
    (d : ℝ)⁻¹ * ∑ a ∈ range d, (if g ∣ a then (g : ℝ) else 0) = 1 := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg hd
  have h := inv_mul_sum_ite_dvd (N := d) (d := g) hg0 hg (fun _ => (1 : ℂ))
  have hq : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hg) hg0
  have hq' : ((d / g : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hR : ((d / g : ℕ) : ℂ)⁻¹ * ∑ l ∈ range (d / g), (1 : ℂ) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hq']
  rw [hR] at h
  simp only [mul_one] at h
  have h4 : ((((d : ℝ)⁻¹ * ∑ a ∈ range d, (if g ∣ a then (g : ℝ) else 0) : ℝ)) : ℂ) = 1 := by
    push_cast
    simp only [apply_ite (Complex.ofReal), Complex.ofReal_natCast, Complex.ofReal_zero]
    exact h
  exact_mod_cast h4

/-- `E_{α ∈ Y_d} σ_d(α) = d_div(d)`. -/
theorem expect_sigmaD (d : ℕ) [NeZero d] : 𝔼 α : ZMod d, (sigmaD d α : ℝ) = (d.divisors.card : ℝ) := by
  have h1 : ∀ α : ZMod d, (sigmaD d α : ℝ) = ∑ g ∈ d.divisors, (if g ∣ α.val then (g : ℝ) else 0) := by
    intro α
    unfold sigmaD
    push_cast
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨⟨h1, NeZero.ne d⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨⟨h1, h2⟩, fun h => NeZero.ne d (Nat.eq_zero_of_gcd_eq_zero_left h)⟩
  simp_rw [h1]
  rw [Fintype.expect_eq_sum_div_card, ZMod.card, Finset.sum_comm, Finset.sum_div]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [sum_zmod_val d (fun a => if g ∣ a then (g : ℝ) else 0), div_eq_inv_mul,
    avg_ite_dvd (Nat.pos_of_ne_zero (NeZero.ne d)) (Nat.dvd_of_mem_divisors hg)]
  simp

/-- **N33(ii)**: `E_{α ∈ Y_d} H_d(α) = d_div(d)² max_{q ∈ B} φ(q)⁻¹`. -/
theorem expect_envelope_eq (B : Finset ℕ) (hB : B.Nonempty) (d : ℕ) [NeZero d] :
    𝔼 α : ZMod d, envelope B hB d α =
      (d.divisors.card : ℝ) ^ 2 * maxInvTotient B hB := by
  unfold envelope
  rw [← Finset.mul_expect, expect_sigmaD]
  ring

/-- **N33(ii), explicit-`ε` form**: for `d ∈ Dset_B` (`d ∣ q` for some `q ∈ B`) and
`B ⊆ (Q/2, Q]`, `E_{α ∈ Y_d} H_d(α) ≤ C_ε Q^{ε-1}`. -/
theorem exists_expect_envelope_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ) (hB : B.Nonempty) (d : ℕ) [NeZero d], 1 ≤ Q →
      (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) → (∃ q ∈ B, d ∣ q) →
        𝔼 α : ZMod d, envelope B hB d α ≤ C * Q ^ (ε - 1) := by
  have hδ : 0 < ε / 3 := by linarith
  obtain ⟨C, hC1, hC⟩ := exists_card_divisors_le_rpow hδ
  refine ⟨2 * C * C * C, by positivity, fun Q B hB d _ hQ hBQ ⟨q₀, hq₀, hdq₀⟩ => ?_⟩
  rw [expect_envelope_eq]
  have hQ0 : 0 < Q := by linarith
  have hq0 : ∀ q ∈ B, 0 < q := fun q hq => by
    have : (0 : ℝ) < q := by linarith [(hBQ q hq).1]
    exact_mod_cast this
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdQ : (d : ℝ) ≤ Q := by
    have : d ≤ q₀ := Nat.le_of_dvd (hq0 q₀ hq₀) hdq₀
    exact (Nat.cast_le.2 this).trans (hBQ q₀ hq₀).2
  have hτ : (d.divisors.card : ℝ) ≤ C * Q ^ (ε / 3) :=
    (hC d hdpos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hdQ hδ.le) (by linarith))
  have hM : maxInvTotient B hB ≤ 2 * C * Q ^ (ε / 3 - 1) := by
    refine Finset.sup'_le hB _ fun q hq => ?_
    obtain ⟨h1, h2⟩ := hBQ q hq
    exact inv_totient_le (C := C) (ε := ε / 3) hδ (by linarith) hC (hq0 q hq) h1.le hQ
  have hτ2 : (d.divisors.card : ℝ) ^ 2 ≤ (C * Q ^ (ε / 3)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hτ 2
  calc (d.divisors.card : ℝ) ^ 2 * maxInvTotient B hB
      ≤ (C * Q ^ (ε / 3)) ^ 2 * (2 * C * Q ^ (ε / 3 - 1)) :=
        mul_le_mul hτ2 hM (maxInvTotient_nonneg hB) (by positivity)
    _ = 2 * C * C * C * (Q ^ (ε / 3) * Q ^ (ε / 3) * Q ^ (ε / 3 - 1)) := by ring
    _ = 2 * C * C * C * Q ^ (ε - 1) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
        congr 2
        ring

/-! ### Transport to `Y_N` for `N = d D` -/

/-- The CRT isomorphism `Y_d × Y_D ≅ Y_N` for `d D = N`. -/
def crtN {d D N : ℕ} (hdD : d.Coprime D) (hN : d * D = N) : ZMod d × ZMod D ≃+* ZMod N :=
  (ZMod.chineseRemainder hdD).symm.trans (ZMod.ringEquivCongr hN)

/-- `Λ_B(α, β) = Λ_B(CRT⁻¹(α, β))` on `Y_N`, `N = d D`. -/
noncomputable def lamCRTN (B : Finset ℕ) {d D N : ℕ} (hdD : d.Coprime D) (hN : d * D = N)
    (α : ZMod d) (β : ZMod D) : ℂ :=
  lam B N (crtN hdD hN (α, β))

theorem lamCRTN_eq (B : Finset ℕ) {d D N : ℕ} (hdD : d.Coprime D) (hN : d * D = N) :
    lamCRTN B hdD hN = lamCRT B hdD := by
  subst hN
  funext α β
  simp [lamCRTN, crtN, lamCRT]

/-- **N33(i)** on `Y_N`, `N = d D`: `sup_ξ |𝓕_D(Λ_B(α, ·))(ξ)| ≤ H_d(α)`. -/
theorem norm_fourierZMod_lamCRTN_le {B : Finset ℕ} {d D N : ℕ} [NeZero d] [NeZero D]
    (hB : B.Nonempty) (hdD : d.Coprime D) (hN : d * D = N) (hBN : ∀ q ∈ B, q ∣ N) (α : ZMod d)
    (ξ : ZMod D) : ‖fourierZMod (lamCRTN B hdD hN α) ξ‖ ≤ envelope B hB d α := by
  rw [lamCRTN_eq B hdD hN]
  exact norm_fourierZMod_lamCRT_le hB hdD (hN ▸ hBN) α ξ

end PrimeBHT.PeriodicBlock
