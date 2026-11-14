module

public import PrimeBHT.Periodic.Product
public import PrimeBHT.Periodic.Greedy
public import Mathlib.Data.Nat.Squarefree

/-!
# Periodic analysis: the unweighted fibre estimate (N32) and the greedy decomposition (N35)

`blueprint.md` §5.0 (setting), N32 (`l:unweighted-fibre`), N35 (`p:greedy`).  Finite-group Fourier
analysis only; no arithmetic input.

## Setting

`N` is a natural number, and `s : Split N` is a splitting `N = d * D` with `gcd(d, D) = 1`
(for squarefree `N` and `d ∣ N` take `D = N / d`, see `Split.ofDvd`).  `Y_N = ZMod N`,
`Y_d = ZMod d`, `Y_D = ZMod D` carry the *normalized* counting measures; `l1`, `l2` are the
corresponding norms (`E_y ‖F y‖`, `(E_y ‖F y‖²)^{1/2}`) and `ip F G = E_y F y * conj (G y)`.
`s.crt : ZMod N ≃+* ZMod d × ZMod D` is the Chinese remainder isomorphism, and for
`F : ZMod N → ℂ` we write `F_α(β) = F(α, β)` in these coordinates (`s.fibre F`).

* `dft h ξ = E_β h β * eD (-(ξ β))` with `eD x = exp(2πi x / D)`: the normalized Fourier transform on
  `ZMod D` (`PrimeBHT.Periodic.Fibre`).
* `s.M F y = max_ξ ‖dft (F_α) ξ‖` where `α = (s.crt y).1`: the fibre maximal function `M_d F`.
* `s.A F G y = E_{λ ∈ ZMod D} F(y - dλ) G(y + dλ)`: the average operator `A_d`.
* `s.IsAtom Φ`: `Φ(α, β) = v(α) e_D(ϑ(α) β)` with `‖v‖_{L²(Y_d)} = 1` (`Atoms_d`).

## Main results

* `Split.A_crt_symm`: in coordinates, `A_d(F,G)(α,β) = E_λ F(α, β - λ) G(α, β + λ)`.
* `Split.l1_A_le` (N32): `‖A_d(F,G)‖_{L¹(Y_N)} ≤ √2 ‖M_d F‖_{L²(Y_N)} ‖G‖_{L²(Y_N)}`.
* `Split.exists_isAtom_ip_eq` (key step of N35): the inverse theorem for `M_d`.
* `exists_greedy_decomposition` (N35): the greedy decomposition for a finite set of splittings, and
  `exists_greedy_decomposition_of_dvd` for a finite set of divisors of a squarefree `N`.
-/

@[expose] public section

namespace PrimeBHT.Periodic

open Finset
open scoped BigOperators ComplexConjugate

/-- A splitting `N = d * D` of `N` into coprime factors (`blueprint.md` §5.0). -/
structure Split (N : ℕ) where
  /-- the divisor `d` -/
  d : ℕ
  /-- the cofactor `D = N / d` -/
  D : ℕ
  [neZero_d : NeZero d]
  [neZero_D : NeZero D]
  mul_eq : d * D = N
  coprime : Nat.Coprime d D

attribute [instance] Split.neZero_d Split.neZero_D

namespace Split

/-- The splitting of a squarefree `N ≠ 0` at a divisor `d`: `D = N / d` (`gcd(d, D) = 1` because
`N` is squarefree). -/
def ofDvd {N : ℕ} [NeZero N] (hN : Squarefree N) {d : ℕ} (hd : d ∣ N) : Split N :=
  haveI hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hNpos
  haveI : NeZero d := ⟨hdpos.ne'⟩
  haveI : NeZero (N / d) := ⟨(Nat.div_pos (Nat.le_of_dvd hNpos hd) hdpos).ne'⟩
  { d := d
    D := N / d
    mul_eq := Nat.mul_div_cancel' hd
    coprime := Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' hd]) }

@[simp] theorem ofDvd_d {N : ℕ} [NeZero N] (hN : Squarefree N) {d : ℕ} (hd : d ∣ N) :
    (ofDvd hN hd).d = d := rfl

@[simp] theorem ofDvd_D {N : ℕ} [NeZero N] (hN : Squarefree N) {d : ℕ} (hd : d ∣ N) :
    (ofDvd hN hd).D = N / d := rfl

variable {N : ℕ} (s : Split N)

/-- The Chinese remainder isomorphism `Y_N ≃ Y_d × Y_D`. -/
noncomputable def crt : ZMod N ≃+* ZMod s.d × ZMod s.D :=
  (ZMod.ringEquivCongr s.mul_eq.symm).trans (ZMod.chineseRemainder s.coprime)

/-- `F` in Chinese-remainder coordinates: `fibre F (α, β) = F(α, β)`. -/
noncomputable def fibre (F : ZMod N → ℂ) : ZMod s.d × ZMod s.D → ℂ := fun p => F (s.crt.symm p)

/-- The fibre maximal function `M_d F (y) = max_ξ ‖F_D (F_α) (ξ)‖`, `α = y mod d`. -/
noncomputable def M (F : ZMod N → ℂ) : ZMod N → ℝ := fun y => fibMax (s.fibre F) (s.crt y).1

/-- The map `l ↦ d l` from `Y_D` to `Y_N`. -/
noncomputable def emb (l : ZMod s.D) : ZMod N := (s.d : ZMod N) * ((l.val : ℕ) : ZMod N)

/-- The average operator `A_d(F, G)(y) = E_{λ ∈ Y_D} F(y - dλ) G(y + dλ)`. -/
noncomputable def A (F G : ZMod N → ℂ) : ZMod N → ℂ :=
  fun y => 𝔼 l : ZMod s.D, F (y - s.emb l) * G (y + s.emb l)

/-- Structured atoms (`Atoms_d`): `Φ(α, β) = v(α) e_D(ϑ(α) β)` with `‖v‖_{L²(Y_d)} = 1`. -/
def IsAtom (Φ : ZMod N → ℂ) : Prop :=
  ∃ (v : ZMod s.d → ℂ) (ϑ : ZMod s.d → ZMod s.D), l2 v = 1 ∧
    ∀ y, Φ y = v (s.crt y).1 * eD (ϑ (s.crt y).1 * (s.crt y).2)

theorem crt_emb (l : ZMod s.D) : s.crt (s.emb l) = (0, (s.d : ZMod s.D) * l) := by
  unfold emb
  rw [map_mul, map_natCast, map_natCast]
  refine Prod.ext ?_ ?_
  · simp
  · simp

theorem crt_sub_emb (y : ZMod N) (l : ZMod s.D) :
    s.crt (y - s.emb l) = ((s.crt y).1, (s.crt y).2 - (s.d : ZMod s.D) * l) := by
  rw [map_sub, crt_emb]
  refine Prod.ext ?_ ?_ <;> simp

theorem crt_add_emb (y : ZMod N) (l : ZMod s.D) :
    s.crt (y + s.emb l) = ((s.crt y).1, (s.crt y).2 + (s.d : ZMod s.D) * l) := by
  rw [map_add, crt_emb]
  refine Prod.ext ?_ ?_ <;> simp

/-- Since `d` is a unit modulo `D`, `l ↦ d l` is a bijection of `Y_D`. -/
theorem expect_mul_d {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (f : ZMod s.D → M) :
    𝔼 l : ZMod s.D, f ((s.d : ZMod s.D) * l) = 𝔼 l : ZMod s.D, f l := by
  have hu : ((ZMod.unitOfCoprime s.d s.coprime : (ZMod s.D)ˣ) : ZMod s.D) = (s.d : ZMod s.D) :=
    ZMod.coe_unitOfCoprime _ _
  refine Fintype.expect_equiv (Units.mulLeft (ZMod.unitOfCoprime s.d s.coprime)) _ _ fun l => ?_
  simp only [Units.mulLeft_apply, hu]

/-- **Fibrewise form of `A_d`** (blueprint §5.0): in Chinese-remainder coordinates,
`A_d(F, G)(α, β) = E_λ F(α, β - λ) G(α, β + λ)`. -/
theorem A_crt_symm (F G : ZMod N → ℂ) (p : ZMod s.d × ZMod s.D) :
    s.A F G (s.crt.symm p) = avgP (s.fibre F) (s.fibre G) p := by
  have hy : s.crt (s.crt.symm p) = p := s.crt.apply_symm_apply p
  have h1 : ∀ l : ZMod s.D, F (s.crt.symm p - s.emb l) =
      s.fibre F (p.1, p.2 - (s.d : ZMod s.D) * l) := by
    intro l
    unfold fibre
    congr 1
    rw [eq_comm, RingEquiv.symm_apply_eq, crt_sub_emb, hy]
  have h2 : ∀ l : ZMod s.D, G (s.crt.symm p + s.emb l) =
      s.fibre G (p.1, p.2 + (s.d : ZMod s.D) * l) := by
    intro l
    unfold fibre
    congr 1
    rw [eq_comm, RingEquiv.symm_apply_eq, crt_add_emb, hy]
  unfold A avgP
  simp_rw [h1, h2]
  exact s.expect_mul_d (fun l => s.fibre F (p.1, p.2 - l) * s.fibre G (p.1, p.2 + l))

variable [NeZero N]

theorem l2_fibre (F : ZMod N → ℂ) : l2 (s.fibre F) = l2 F :=
  l2_comp_equiv s.crt.symm.toEquiv F

theorem l2_M (F : ZMod N → ℂ) : l2 (s.M F) = l2 (fibMax (s.fibre F)) := by
  have h : s.M F = (fun p : ZMod s.d × ZMod s.D => fibMax (s.fibre F) p.1) ∘ s.crt.toEquiv := rfl
  rw [h, l2_comp_equiv, l2_comp_fst]

/-- **N32** (`l:unweighted-fibre`): `‖A_d(F, G)‖_{L¹(Y_N)} ≤ √2 ‖M_d F‖_{L²(Y_N)} ‖G‖_{L²(Y_N)}`. -/
theorem l1_A_le (F G : ZMod N → ℂ) : l1 (s.A F G) ≤ √2 * l2 (s.M F) * l2 G := by
  have h1 : l1 (s.A F G) = l1 (avgP (s.fibre F) (s.fibre G)) := by
    rw [← l1_comp_equiv s.crt.symm.toEquiv (s.A F G)]
    congr 1
    funext p
    exact s.A_crt_symm F G p
  rw [h1, s.l2_M, ← s.l2_fibre G]
  exact l1_avgP_le _ _

/-- **Inverse theorem for `M_d`** (key step of N35): if `M_d R ≠ 0` there is `Φ ∈ Atoms_d` with
`⟨R, Φ⟩ = ‖M_d R‖_{L²(Y_N)}`. -/
theorem exists_isAtom_ip_eq (R : ZMod N → ℂ) (hR : 0 < l2 (s.M R)) :
    ∃ Φ : ZMod N → ℂ, s.IsAtom Φ ∧ l2 Φ = 1 ∧ ip R Φ = ((l2 (s.M R) : ℝ) : ℂ) := by
  rw [s.l2_M] at hR ⊢
  obtain ⟨v, ϑ, hv, hip⟩ := exists_atom (s.fibre R) hR
  have hΦ : (atom v ϑ ∘ s.crt.toEquiv) = fun y => atom v ϑ (s.crt y) := rfl
  have hRR : R = s.fibre R ∘ s.crt.toEquiv := by
    funext y
    simp [fibre]
  refine ⟨atom v ϑ ∘ s.crt.toEquiv, ⟨v, ϑ, hv, fun y => rfl⟩, ?_, ?_⟩
  · rw [l2_comp_equiv, l2_atom, hv]
  · conv_lhs => rw [hRR]
    rw [ip_comp_equiv, hip]

end Split

section Greedy

variable {N : ℕ} [NeZero N]

/-- **N35** (`p:greedy`).  For a finite set `S` of splittings of `N`, `t > 0` and `F : Y_N → ℂ` there
are `J ≤ t⁻²`, splittings `s_j ∈ S`, atoms `Φ_j ∈ Atoms_{d_j}`, reals `c_j > 0` with
`∑ c_j² ≤ ‖F‖²_{L²(Y_N)}` such that `R = F - ∑ c_j Φ_j` satisfies `‖M_d R‖_{L²(Y_N)} ≤ t ‖F‖_{L²(Y_N)}`
for **every** `s' ∈ S`. -/
theorem exists_greedy_decomposition (S : Finset (Split N)) {t : ℝ} (ht : 0 < t)
    (F : ZMod N → ℂ) :
    ∃ (J : ℕ) (s : Fin J → Split N) (Φ : Fin J → ZMod N → ℂ) (c : Fin J → ℝ),
      (J : ℝ) ≤ t⁻¹ ^ 2 ∧ (∀ j, s j ∈ S) ∧ (∀ j, (s j).IsAtom (Φ j)) ∧ (∀ j, 0 < c j) ∧
      ∑ j, c j ^ 2 ≤ l2 F ^ 2 ∧
      ∀ s' ∈ S, l2 (s'.M (F - ∑ j, (c j : ℂ) • Φ j)) ≤ t * l2 F := by
  obtain ⟨J, s, Φ, c, hJ, hs, hA, -, hc, hsum, hstop⟩ :=
    exists_greedy_decomposition_abstract S (fun s R => l2 (Split.M s R)) (fun s Φ => s.IsAtom Φ)
      (fun s _ R hR => s.exists_isAtom_ip_eq R hR) ht F
  exact ⟨J, s, Φ, c, hJ, hs, hA, hc, hsum, hstop⟩

/-- **N35** for a finite set `Ds` of divisors of a squarefree `N` (the splittings are
`D = N / d`, `Split.ofDvd`). -/
theorem exists_greedy_decomposition_of_dvd (hN : Squarefree N) (Ds : Finset ℕ)
    (hDs : ∀ d ∈ Ds, d ∣ N) {t : ℝ} (ht : 0 < t) (F : ZMod N → ℂ) :
    ∃ (J : ℕ) (d : Fin J → ℕ) (hd : ∀ j, d j ∈ Ds) (Φ : Fin J → ZMod N → ℂ) (c : Fin J → ℝ),
      (J : ℝ) ≤ t⁻¹ ^ 2 ∧ (∀ j, (Split.ofDvd hN (hDs _ (hd j))).IsAtom (Φ j)) ∧
      (∀ j, 0 < c j) ∧ ∑ j, c j ^ 2 ≤ l2 F ^ 2 ∧
      ∀ (d' : ℕ) (hd' : d' ∈ Ds),
        l2 ((Split.ofDvd hN (hDs d' hd')).M (F - ∑ j, (c j : ℂ) • Φ j)) ≤ t * l2 F := by
  classical
  let S : Finset (Split N) := Ds.attach.image fun d => Split.ofDvd hN (hDs d.1 d.2)
  obtain ⟨J, s, Φ, c, hJ, hs, hA, hc, hsum, hstop⟩ := exists_greedy_decomposition S ht F
  have hs' : ∀ j, ∃ (d : ℕ) (hd : d ∈ Ds), Split.ofDvd hN (hDs d hd) = s j := by
    intro j
    obtain ⟨⟨d, hd⟩, -, h⟩ := Finset.mem_image.1 (hs j)
    exact ⟨d, hd, h⟩
  choose d hd hds using hs'
  refine ⟨J, d, hd, Φ, c, hJ, fun j => ?_, hc, hsum, fun d' hd' => hstop _ ?_⟩
  · rw [hds j]
    exact hA j
  · exact Finset.mem_image.2 ⟨⟨d', hd'⟩, Finset.mem_attach _ _, rfl⟩

end Greedy

end PrimeBHT.Periodic
