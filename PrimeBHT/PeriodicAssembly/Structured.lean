module

public import PrimeBHT.Periodic
public import PrimeBHT.PeriodicBlock
public import PrimeBHT.PeriodicAssembly.Decomp

/-!
# Structured atoms: `l:structured-bound` (blueprint N34)

First (product model `A × Y_D`, no arithmetic): the correlation inequality
`E_b |E_β w(β) h(b+β)| ≤ M ‖h‖_{L²(Y_D)}` when `|F_D w| ≤ M` (`l1_corr_le`), and the bound
`‖E_r L(r) Φ(p - r) G(p + r)‖_{L¹(A × Y_D)} ≤ (E_α H(α)) ‖v‖₂ ‖G‖₂` for an atom
`Φ(α, β) = v(α) e_D(ϑ(α) β)` when `|F_D L(α, ·)| ≤ H(α)` (`l1_bilinP_atom_le`): the Fourier
transform of a correlation is a product (Parseval), then Cauchy-Schwarz in `α`
(the source's "Young's inequality", FINDINGS F8).

Then, transported to `Y_N ≅ Y_d × Y_D` and combined with the envelope `N33(i)`:
`l1_bilinAvg_atom_le`, `exists_l1_bilinAvg_atom_le`.
-/

@[expose] public section

namespace PrimeBHT.PeriodicAssembly

open Finset PrimeBHT.Periodic
open scoped BigOperators ComplexConjugate

section Corr

variable {D : ℕ} [NeZero D]

/-- The Fourier transform of the correlation `b ↦ E_β w(β) h(b + β)` is a product. -/
theorem dft_corr (w h : ZMod D → ℂ) (ξ : ZMod D) :
    dft (fun b => 𝔼 β : ZMod D, w β * h (b + β)) ξ = dft w (-ξ) * dft h ξ := by
  unfold dft
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  refine Finset.expect_congr rfl fun β _ => ?_
  rw [Finset.mul_expect]
  refine Fintype.expect_equiv (Equiv.addRight β) _ _ fun b => ?_
  have e1 : eD (-(-ξ * β)) * eD (-(ξ * (b + β))) = eD (-(ξ * b)) := by
    rw [← eD_add]; congr 1; ring
  show w β * h (b + β) * eD (-(ξ * b)) =
    w β * eD (-(-ξ * β)) * (h (b + β) * eD (-(ξ * (b + β))))
  rw [← e1]; ring

/-- Correlation inequality (blueprint N34, step 2): if `|F_D w| ≤ M` then
`E_b |E_β w(β) h(b+β)| ≤ M ‖h‖_{L²(Y_D)}`. -/
theorem l1_corr_le (w h : ZMod D → ℂ) {M : ℝ} (hM : ∀ ξ, ‖dft w ξ‖ ≤ M) :
    l1 (fun b => 𝔼 β : ZMod D, w β * h (b + β)) ≤ M * l2 h := by
  set c : ZMod D → ℂ := fun b => 𝔼 β : ZMod D, w β * h (b + β) with hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (l1_le_l2 c).trans ?_
  have h1 : 𝔼 b, ‖c b‖ ^ 2 = ∑ ξ, ‖dft c ξ‖ ^ 2 := parseval c
  have h2 : ∑ ξ, ‖dft c ξ‖ ^ 2 ≤ M ^ 2 * ∑ ξ, ‖dft h ξ‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [hc, dft_corr, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM _) 2) (sq_nonneg _)
  rw [← parseval h, ← h1] at h2
  unfold l2
  calc √(𝔼 b, ‖c b‖ ^ 2) ≤ √(M ^ 2 * 𝔼 b, ‖h b‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = M * √(𝔼 b, ‖h b‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]

end Corr

section ProdModel

variable {A : Type*} [AddCommGroup A] [Fintype A] {D : ℕ} [NeZero D]

/-- The bilinear average with weight `L` on the group `A × Y_D`. -/
noncomputable def bilinP (L F G : A × ZMod D → ℂ) (p : A × ZMod D) : ℂ :=
  𝔼 r : A × ZMod D, L r * F (p - r) * G (p + r)

theorem bilinP_atom (L G : A × ZMod D → ℂ) (v : A → ℂ) (ϑ : A → ZMod D) (a : A) (b : ZMod D) :
    bilinP L (atom v ϑ) G (a, b) =
      𝔼 α : A, (v (a - α) * eD (ϑ (a - α) * b)) *
        𝔼 β : ZMod D, (L (α, β) * eD (-(ϑ (a - α) * β))) * G (a + α, b + β) := by
  unfold bilinP
  rw [expect_prod']
  refine Finset.expect_congr rfl fun α _ => ?_
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl fun β _ => ?_
  have h1 : eD (ϑ (a - α) * (b - β)) = eD (ϑ (a - α) * b) * eD (-(ϑ (a - α) * β)) := by
    rw [← eD_add]; congr 1; ring
  simp only [atom, Prod.mk_sub_mk, Prod.mk_add_mk, h1]
  ring

theorem dft_mul_eD_neg (f : ZMod D → ℂ) (θ ξ : ZMod D) :
    dft (fun β => f β * eD (-(θ * β))) ξ = dft f (ξ + θ) := by
  unfold dft
  refine Finset.expect_congr rfl fun β _ => ?_
  have : eD (-(θ * β)) * eD (-(ξ * β)) = eD (-((ξ + θ) * β)) := by
    rw [← eD_add]; congr 1; ring
  rw [mul_assoc, this]

omit [AddCommGroup A] in
theorem l2_fibreNorm (G : A × ZMod D → ℂ) :
    l2 (fun c : A => l2 (fibreOf G c)) = l2 G := by
  have h1 : l2 (fun c : A => l2 (fibreOf G c)) ^ 2 = l2 G ^ 2 := by
    rw [l2_sq, l2_sq, expect_prod']
    refine Finset.expect_congr rfl fun α _ => ?_
    rw [Real.norm_of_nonneg (l2_nonneg _), l2_sq]
    rfl
  exact (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).1 h1

/-- **N34 in the product model.** If `|F_D L(α, ·)| ≤ H(α)` for all `α`, then for the atom
`Φ(α, β) = v(α) e_D(ϑ(α) β)`:
`‖bilinP L Φ G‖_{L¹(A × Y_D)} ≤ (E_α H(α)) ‖v‖_{L²(A)} ‖G‖_{L²(A × Y_D)}`. -/
theorem l1_bilinP_atom_le (L G : A × ZMod D → ℂ) (v : A → ℂ) (ϑ : A → ZMod D) {H : A → ℝ}
    (hH : ∀ α ξ, ‖dft (fun β => L (α, β)) ξ‖ ≤ H α) :
    l1 (bilinP L (atom v ϑ) G) ≤ (𝔼 α, H α) * l2 v * l2 G := by
  set g : A → ℝ := fun c => l2 (fibreOf G c) with hg
  set K : A → A → ZMod D → ℝ := fun a α b =>
    ‖𝔼 β : ZMod D, (L (α, β) * eD (-(ϑ (a - α) * β))) * G (a + α, b + β)‖ with hK
  have hpt : ∀ a b, ‖bilinP L (atom v ϑ) G (a, b)‖ ≤ 𝔼 α, ‖v (a - α)‖ * K a α b := by
    intro a b
    rw [bilinP_atom]
    refine (RCLike.norm_expect_le (K := ℂ)).trans (le_of_eq ?_)
    refine Finset.expect_congr rfl fun α _ => ?_
    rw [norm_mul, norm_mul, norm_eD, mul_one]
  have hfib : ∀ a α, 𝔼 b : ZMod D, K a α b ≤ H α * g (a + α) := by
    intro a α
    have := l1_corr_le (fun β => L (α, β) * eD (-(ϑ (a - α) * β))) (fun β => G (a + α, β))
      (M := H α) (fun ξ => by rw [dft_mul_eD_neg]; exact hH α _)
    exact this
  have hcs : ∀ α, 𝔼 a : A, ‖v (a - α)‖ * g (a + α) ≤ l2 v * l2 G := by
    intro α
    have h1 := expect_norm_mul_le (fun a => v (a - α)) (fun a => g (a + α))
    have h2 : l2 (fun a => v (a - α)) = l2 v := l2_comp_equiv (Equiv.subRight α) v
    have h3 : l2 (fun a => g (a + α)) = l2 g := l2_comp_equiv (Equiv.addRight α) g
    rw [h2, h3, hg, l2_fibreNorm] at h1
    simpa only [hg, Real.norm_of_nonneg (l2_nonneg _)] using h1
  have hH0 : ∀ α, 0 ≤ H α := fun α => (norm_nonneg _).trans (hH α 0)
  unfold l1
  rw [expect_prod']
  calc 𝔼 a : A, 𝔼 b : ZMod D, ‖bilinP L (atom v ϑ) G (a, b)‖
      ≤ 𝔼 a : A, 𝔼 b : ZMod D, 𝔼 α : A, ‖v (a - α)‖ * K a α b :=
        Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun b _ => hpt a b
    _ = 𝔼 a : A, 𝔼 α : A, ‖v (a - α)‖ * 𝔼 b : ZMod D, K a α b := by
        refine Finset.expect_congr rfl fun a _ => ?_
        rw [Finset.expect_comm]
        refine Finset.expect_congr rfl fun α _ => ?_
        rw [Finset.mul_expect]
    _ ≤ 𝔼 a : A, 𝔼 α : A, ‖v (a - α)‖ * (H α * g (a + α)) :=
        Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun α _ =>
          mul_le_mul_of_nonneg_left (hfib a α) (norm_nonneg _)
    _ = 𝔼 α : A, H α * 𝔼 a : A, ‖v (a - α)‖ * g (a + α) := by
        rw [Finset.expect_comm]
        refine Finset.expect_congr rfl fun α _ => ?_
        rw [Finset.mul_expect]
        refine Finset.expect_congr rfl fun a _ => ?_
        ring
    _ ≤ 𝔼 α : A, H α * (l2 v * l2 G) :=
        Finset.expect_le_expect fun α _ => mul_le_mul_of_nonneg_left (hcs α) (hH0 α)
    _ = (𝔼 α, H α) * l2 v * l2 G := by
        rw [← Finset.expect_mul, mul_assoc]

end ProdModel


section Transfer

open PrimeBHT.PeriodicBlock (lam bilinAvg envelope lamCRTN crtN norm_fourierZMod_lamCRTN_le
  exists_expect_envelope_le)

theorem ringEquivCongr_symm_symm {a b : ℕ} (h : a = b) (x : ZMod a) :
    (ZMod.ringEquivCongr h.symm).symm x = ZMod.ringEquivCongr h x := by
  rw [ZMod.ringEquivCongr_symm h.symm]

/-- `Split.crt.symm` is the transport `crtN` of the envelope file. -/
theorem crt_symm_eq_crtN {N : ℕ} (s : Split N) (p : ZMod s.d × ZMod s.D) :
    s.crt.symm p = crtN s.coprime s.mul_eq p := by
  unfold Split.crt crtN
  rw [RingEquiv.symm_trans_apply]
  exact ringEquivCongr_symm_symm s.mul_eq _

theorem bilinAvg_eq_bilinP {N : ℕ} [NeZero N] (s : Split N) (Λ F G : ZMod N → ℂ) (y : ZMod N) :
    bilinAvg Λ F G y =
      bilinP (fun p => Λ (s.crt.symm p)) (s.fibre F) (s.fibre G) (s.crt y) := by
  unfold PrimeBHT.PeriodicBlock.bilinAvg bilinP
  refine Fintype.expect_equiv s.crt.toEquiv _ _ fun r => ?_
  show Λ r * F (y - r) * G (y + r) =
    Λ (s.crt.symm (s.crt r)) * F (s.crt.symm (s.crt y - s.crt r)) *
      G (s.crt.symm (s.crt y + s.crt r))
  rw [← map_sub, ← map_add, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply]

/-- **N34** (`l:structured-bound`), exact form: for a splitting `N = d D`, `q ∣ N` for all `q ∈ B`,
an atom `Φ ∈ Atoms_d` and `G : Y_N → ℂ`,
`‖A_B(Φ, G)‖_{L¹(Y_N)} ≤ (E_{α ∈ Y_d} H_d(α)) ‖G‖_{L²(Y_N)}`. -/
theorem l1_bilinAvg_atom_le {B : Finset ℕ} (hB : B.Nonempty) {N : ℕ} [NeZero N]
    (hBN : ∀ q ∈ B, q ∣ N) (s : Split N) {Φ : ZMod N → ℂ} (hΦ : s.IsAtom Φ)
    (G : ZMod N → ℂ) :
    l1 (bilinAvg (lam B N) Φ G) ≤ (𝔼 α : ZMod s.d, envelope B hB s.d α) * l2 G := by
  obtain ⟨v, ϑ, hv, hΦ'⟩ := hΦ
  have hfib : s.fibre Φ = atom v ϑ := by
    funext p
    simp only [Split.fibre, hΦ', atom, RingEquiv.apply_symm_apply]
  have h1 : bilinAvg (lam B N) Φ G =
      (bilinP (fun p => lam B N (s.crt.symm p)) (atom v ϑ) (s.fibre G)) ∘ s.crt.toEquiv := by
    funext y
    rw [bilinAvg_eq_bilinP s, hfib]
    rfl
  rw [h1, l1_comp_equiv s.crt.toEquiv]
  have := l1_bilinP_atom_le (fun p => lam B N (s.crt.symm p)) (s.fibre G) v ϑ
    (H := envelope B hB s.d) (fun α ξ => by
      have h2 := norm_fourierZMod_lamCRTN_le hB s.coprime s.mul_eq hBN α ξ
      have h3 : (fun β => lam B N (s.crt.symm (α, β))) = lamCRTN B s.coprime s.mul_eq α := by
        funext β
        rw [crt_symm_eq_crtN]
        rfl
      rw [h3]
      exact h2)
  rwa [hv, mul_one, s.l2_fibre] at this

/-- **N34**, explicit-`ε` form: for `B ⊆ (Q/2, Q]` and a splitting with `d ∣ q` for some `q ∈ B`
(`d ∈ Dset_B`), `‖A_B(Φ, G)‖_{L¹(Y_N)} ≤ C_ε Q^{ε-1} ‖G‖_{L²(Y_N)}`. -/
theorem exists_l1_bilinAvg_atom_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ), B.Nonempty → ∀ (N : ℕ) [NeZero N], 1 ≤ Q →
      (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) → (∀ q ∈ B, q ∣ N) → ∀ (s : Split N),
      (∃ q ∈ B, s.d ∣ q) → ∀ {Φ : ZMod N → ℂ}, s.IsAtom Φ → ∀ G : ZMod N → ℂ,
        l1 (bilinAvg (lam B N) Φ G) ≤ C * Q ^ (ε - 1) * l2 G := by
  obtain ⟨C, hC0, hC⟩ := exists_expect_envelope_le hε hε1
  refine ⟨C, hC0, fun Q B hB N _ hQ hBQ hBN s hs Φ hΦ G => ?_⟩
  refine (l1_bilinAvg_atom_le hB hBN s hΦ G).trans ?_
  exact mul_le_mul_of_nonneg_right (hC Q B hB s.d hQ hBQ hs) (l2_nonneg G)

end Transfer

end PrimeBHT.PeriodicAssembly
