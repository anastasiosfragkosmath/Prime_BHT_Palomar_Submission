module

public import PrimeCarleson.Proof.Paper.Defs.Gowers

/-!
# `l:U3maxmod`, part 1: expansion of the square

For finitely supported pieces `Φ n` and a coefficient `c` supported in a finite set `I`, with `D`
containing all differences of `I`,
`∑'_x |∑_{n ∈ I} c n Φ n x|² = ∑_{h ∈ D} ∑_{n ∈ I} c n conj (c (n+h)) ∑'_x Φ n x conj (Φ (n+h) x)`.
This is applied twice in the proof of `l:U3maxmod` (steps 1 and 3 of the blueprint).
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

/-- The support of `x ↦ c * (Φ x * conj (Ψ x))` is finite when that of `Φ` is. -/
lemma summable_mul_conj_of_finite {Φ Ψ : ℤ → ℂ} (c : ℂ) (hΦ : (Function.support Φ).Finite) :
    Summable (fun x => c * (Φ x * conj (Ψ x))) := by
  apply summable_of_hasFiniteSupport
  refine hΦ.subset fun x hx => ?_
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro h0
  apply hx
  simp [h0]

/-- **Expansion of the square** (a general form of steps 1 and 3 of `l:U3maxmod`). -/
theorem tsum_sq_sum_eq (I D : Finset ℤ) (hD : ∀ n ∈ I, ∀ n' ∈ I, n' - n ∈ D)
    (c : ℤ → ℂ) (hc : ∀ n, n ∉ I → c n = 0) (Φ : ℤ → ℤ → ℂ)
    (hΦ : ∀ n, (Function.support (Φ n)).Finite) :
    ∑' x, (∑ n ∈ I, c n * Φ n x) * conj (∑ n ∈ I, c n * Φ n x) =
      ∑ h ∈ D, ∑ n ∈ I, c n * conj (c (n + h)) * ∑' x, Φ n x * conj (Φ (n + h) x) := by
  have step1 : ∀ x, (∑ n ∈ I, c n * Φ n x) * conj (∑ n ∈ I, c n * Φ n x) =
      ∑ n ∈ I, ∑ n' ∈ I, (c n * conj (c n')) * (Φ n x * conj (Φ n' x)) := by
    intro x
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    rw [map_mul]; ring
  simp_rw [step1]
  rw [Summable.tsum_finsetSum (fun n _ => summable_sum fun n' _ =>
    summable_mul_conj_of_finite _ (hΦ n))]
  have step2 : ∀ n ∈ I, ∑' x, ∑ n' ∈ I, (c n * conj (c n')) * (Φ n x * conj (Φ n' x)) =
      ∑ n' ∈ I, (c n * conj (c n')) * ∑' x, Φ n x * conj (Φ n' x) := by
    intro n _
    rw [Summable.tsum_finsetSum (fun n' _ => summable_mul_conj_of_finite _ (hΦ n))]
    exact Finset.sum_congr rfl fun n' _ => tsum_mul_left
  rw [Finset.sum_congr rfl step2, Finset.sum_comm (s := D) (t := I)]
  refine Finset.sum_congr rfl fun n hn => ?_
  exact (PrimeCarleson.Proof.Common.gowersLp_sum_shift I D hD
    (fun n' => c n * conj (c n') * ∑' x, Φ n x * conj (Φ n' x))
    (fun n' hn' => by simp [hc n' hn']) hn).symm


open PrimeCarleson PrimeCarleson.Proof.Common

/-- A function that is nonzero only where a shift of a finitely supported function is nonzero has
finite support. -/
lemma fin_supp_of_imp {M : Type*} [Zero M] {F : ℤ → M} {f : ℤ → ℂ} (a : ℤ)
    (hf : (Function.support f).Finite)
    (h : ∀ x, F x ≠ 0 → f (x + a) ≠ 0) : (Function.support F).Finite :=
  (hf.preimage (add_left_injective a).injOn).subset fun x hx => h x hx

lemma fin_supp_of_imp' {M : Type*} [Zero M] {F : ℤ → M} {f : ℤ → ℂ}
    (hf : (Function.support f).Finite)
    (h : ∀ x, F x ≠ 0 → f x ≠ 0) : (Function.support F).Finite :=
  hf.subset fun x hx => h x hx

/-- `Δ_h g (z) = g z conj g (z + h)`. -/
def dl (h : ℤ) (g : ℤ → ℂ) (z : ℤ) : ℂ := g z * conj (g (z + h))

/-- `a_h(y) = f y conj f (y - h)` (that is `Δ_{-h} f (y)`). -/
def aF (f : ℤ → ℂ) (h y : ℤ) : ℂ := f y * conj (f (y - h))

/-- `b_h(y) = ∑_n Δ_h c(n) Δ_h g(y + 2n)`. -/
def bF (I : Finset ℤ) (c g : ℤ → ℂ) (h y : ℤ) : ℂ :=
  ∑ n ∈ I, (c n * conj (c (n + h))) * dl h g (y + 2 * n)

/-- The bilinear sum `S(x) = ∑_{n ∈ I} c n f(x - n) g(x + n)`. -/
def sF (I : Finset ℤ) (c f g : ℤ → ℂ) (x : ℤ) : ℂ := ∑ n ∈ I, c n * (f (x - n) * g (x + n))

lemma fs_dl {g : ℤ → ℂ} (hg : (Function.support g).Finite) (h : ℤ) :
    (Function.support (dl h g)).Finite :=
  fin_supp_of_imp' hg fun _ hz => left_ne_zero_of_mul hz

lemma fs_aF {f : ℤ → ℂ} (hf : (Function.support f).Finite) (h : ℤ) :
    (Function.support (aF f h)).Finite :=
  fin_supp_of_imp' hf fun _ hz => left_ne_zero_of_mul hz

lemma fs_dl_shift {g : ℤ → ℂ} (hg : (Function.support g).Finite) (h a : ℤ) :
    (Function.support (fun y => dl h g (y + a))).Finite :=
  fin_supp_of_imp a (fs_dl hg h) fun _ hy => hy

lemma fs_bF (I : Finset ℤ) (c : ℤ → ℂ) {g : ℤ → ℂ} (hg : (Function.support g).Finite) (h : ℤ) :
    (Function.support (bF I c g h)).Finite := by
  have : Function.support (bF I c g h) ⊆
      ⋃ n ∈ I, Function.support (fun y => dl h g (y + 2 * n)) := by
    intro y hy
    simp only [Function.mem_support, bF, ne_eq] at hy
    obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    simp only [Set.mem_iUnion, Function.mem_support, ne_eq]
    exact ⟨n, hn, right_ne_zero_of_mul hne⟩
  exact (Set.Finite.biUnion I.finite_toSet fun n _ => fs_dl_shift hg h (2 * n)).subset this

/-- Inner computation: translation `x = y + n`. -/
lemma inner1 (f g : ℤ → ℂ) (n h : ℤ) :
    ∑' x, (f (x - n) * g (x + n)) * conj (f (x - (n + h)) * g (x + (n + h))) =
      ∑' y, aF f h y * dl h g (y + 2 * n) := by
  rw [← (Equiv.addRight n).tsum_eq]
  refine tsum_congr fun y => ?_
  simp only [Equiv.coe_addRight, aF, dl, map_mul]
  have e1 : y + n - n = y := by ring
  have e2 : y + n - (n + h) = y - h := by ring
  have e3 : y + n + n = y + 2 * n := by ring
  have e4 : y + n + (n + h) = y + 2 * n + h := by ring
  rw [e1, e2, e3, e4]
  ring

/-- Step 1 of `l:U3maxmod`: `‖S‖₂² = ∑_h ∑_y Δ_{-h} f(y) b_h(y)`. -/
theorem sq_tsum_eq_sum_tsum (I D : Finset ℤ) (hD : ∀ n ∈ I, ∀ n' ∈ I, n' - n ∈ D)
    (c : ℤ → ℂ) (hc : ∀ n, n ∉ I → c n = 0) (f g : ℤ → ℂ)
    (hf : (Function.support f).Finite) :
    ∑' x, sF I c f g x * conj (sF I c f g x) = ∑ h ∈ D, ∑' y, aF f h y * bF I c g h y := by
  have hΦ : ∀ n, (Function.support (fun x => f (x - n) * g (x + n))).Finite := fun n =>
    fin_supp_of_imp (-n) hf fun x hx => by
      simpa [sub_eq_add_neg] using left_ne_zero_of_mul hx
  have key := tsum_sq_sum_eq I D hD c hc (fun n x => f (x - n) * g (x + n)) hΦ
  unfold sF
  rw [key]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp_rw [inner1]
  unfold bF
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun n _ => summable_of_hasFiniteSupport
    (fin_supp_of_imp' (fs_aF hf h) fun y hy => left_ne_zero_of_mul hy))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun y => by ring


/-- `A(h,k) = ∑_n Δ_{h,k} c(n)`. -/
def AF (I : Finset ℤ) (c : ℤ → ℂ) (h k : ℤ) : ℂ := ∑ n ∈ I, multDiff 2 ![h, k] c n

/-- `G(h,k) = ∑_x Δ_{h,2k} g(x)`. -/
def GF (g : ℤ → ℂ) (h k : ℤ) : ℂ := ∑' x, multDiff 2 ![h, 2 * k] g x

lemma multDiff_two_eq (h k : ℤ) (c : ℤ → ℂ) (n : ℤ) :
    multDiff 2 ![h, k] c n =
      (c n * conj (c (n + h))) * conj (c (n + k) * conj (c (n + k + h))) := by
  simp [multDiff, Fin.init, Fin.last]

lemma inner2 (g : ℤ → ℂ) (h k n : ℤ) :
    ∑' y, dl h g (y + 2 * n) * conj (dl h g (y + 2 * (n + k))) = GF g h k := by
  unfold GF
  rw [← (Equiv.addRight (2 * n)).tsum_eq (fun x => multDiff 2 ![h, 2 * k] g x)]
  refine tsum_congr fun y => ?_
  simp only [Equiv.coe_addRight, multDiff_two_eq, dl]
  have e1 : y + 2 * (n + k) = y + 2 * n + 2 * k := by ring
  rw [e1]

/-- Step 3 of `l:U3maxmod`: `∑_y |b_h(y)|² = ∑_k A(h,k) G(h,k)`. -/
theorem sq_tsum_bF (I D : Finset ℤ) (hD : ∀ n ∈ I, ∀ n' ∈ I, n' - n ∈ D)
    (c : ℤ → ℂ) (hc : ∀ n, n ∉ I → c n = 0) (g : ℤ → ℂ)
    (hg : (Function.support g).Finite) (h : ℤ) :
    ((∑' y, ‖bF I c g h y‖ ^ 2 : ℝ) : ℂ) = ∑ k ∈ D, AF I c h k * GF g h k := by
  have key := tsum_sq_sum_eq I D hD (fun n => c n * conj (c (n + h))) (fun n hn => by simp [hc n hn])
    (fun n y => dl h g (y + 2 * n)) (fun n => fs_dl_shift hg h (2 * n))
  rw [Complex.ofReal_tsum]
  have e : ∀ y, (((‖bF I c g h y‖ ^ 2 : ℝ)) : ℂ) =
      (∑ n ∈ I, (c n * conj (c (n + h))) * dl h g (y + 2 * n)) *
        conj (∑ n ∈ I, (c n * conj (c (n + h))) * dl h g (y + 2 * n)) := by
    intro y
    rw [Complex.mul_conj']
    unfold bF
    push_cast
    rfl
  simp_rw [e]
  rw [key]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold AF
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner2, multDiff_two_eq]

end PrimeBHT.U3MaxMod
