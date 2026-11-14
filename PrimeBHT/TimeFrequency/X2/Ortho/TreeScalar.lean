module

public import PrimeBHT.TimeFrequency.X2.Ortho.Fourier
public import PrimeBHT.TimeFrequency.X2.Ortho.Families
public import PrimeBHT.TimeFrequency.X2.Ortho.Geometry
public import PrimeBHT.TimeFrequency.X2.Collections

/-!
# X2, node V10: the scalar `L²` almost-orthogonality of a lacunary tree (DPLMV `l:ortho0`)

For a `k`-lacunary tree `T` of rank-1 boxes, tile data `ψ_R ∈ Ψ_{I_R}(𝔭)`, `m_R ∈ M_{ω_{R,k}}(𝔭)` and a bounded
measurable `f`, with `g_R = ψ_R · (𝓕⁻m_R * f)` and `h_R = ψ̃_R · (𝓕⁻m_R * f)`,
`ψ̃_R = (1 + ((x - c_R)/|I_R|)²) ψ_R`:

  `∫ |∑_R g_R|² ≤ C ∑_R ∫ |h_R|²`.

Cross terms of different frequency intervals vanish (Fourier support, `gfun_orthogonal`, needs `β + 2δ ≤ 3`);
cross terms of the same box are controlled by `|g_R| |g_{R'}| = u_R u_{R'} |h_R| |h_{R'}|`, `u = (1 + t²)^{-1}`,
`u_R u_{R'} ≤ 2 (1 + n²)^{-1}` (`n` the difference of the positions), and `∑_n (1 + n²)^{-1} < ∞`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Lower the decay order `N` of a class by `n`. -/
def Params.decN (𝔭 : Params) (n : ℕ) : Params := { 𝔭 with N := 𝔭.N - n }

@[simp] theorem Params.decN_J (𝔭 : Params) (n : ℕ) : (𝔭.decN n).J = 𝔭.J := rfl

/-- `ψ̃ = (1 + ((x - c_I)/|I|)²) ψ`. -/
def psiTilde (s v : ℤ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((1 + ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ 2 : ℝ) : ℂ) * ψ x

theorem psiTilde_eq (s v : ℤ) (ψ : ℝ → ℂ) (x : ℝ) :
    psiTilde s v ψ x = ψ x + (((2 : ℝ) ^ s)⁻¹ ^ 2 : ℝ) * ((((x - dyCentre s v) ^ 2 : ℝ) : ℂ) * ψ x) := by
  unfold psiTilde
  push_cast
  rw [div_pow, div_eq_mul_inv, inv_pow]
  ring

theorem norm_psiTilde (s v : ℤ) (ψ : ℝ → ℂ) (x : ℝ) :
    ‖psiTilde s v ψ x‖ = (1 + ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ 2) * ‖ψ x‖ := by
  unfold psiTilde
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

section Classes

variable {𝔭 : Params} {s v : ℤ} {ψ : ℝ → ℂ}

theorem inPsi_psiTilde (hN : 14 ≤ 𝔭.N) (hψ : InPsi 𝔭 s v ψ) :
    InPsi (𝔭.decN 10) s v (psiTilde s v ψ) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  obtain ⟨hcont, hdec, hsupp⟩ := hψ
  refine ⟨?_, ?_, ?_⟩
  · unfold psiTilde; exact (by fun_prop : Continuous fun x : ℝ => (((1 + ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ 2 : ℝ)) : ℂ)).mul hcont
  · intro x
    rw [norm_psiTilde]
    set t := (x - dyCentre s v) / (2 : ℝ) ^ s with ht
    have h1 := one_le_jb t
    have h2 : 1 + t ^ 2 ≤ jb t ^ 2 := by unfold jb; nlinarith [abs_nonneg t, sq_abs t]
    have hjpos := jb_pos t
    have h3 : jb t ^ 2 * jb t ^ (-(𝔭.N : ℝ)) ≤ jb t ^ (-(((𝔭.decN 10).N : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hjpos]
      apply Real.rpow_le_rpow_of_exponent_le h1
      simp only [Params.decN]
      have : ((𝔭.N - 10 : ℕ) : ℝ) = (𝔭.N : ℝ) - 10 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [this]; push_cast; linarith
    calc (1 + t ^ 2) * ‖ψ x‖ ≤ jb t ^ 2 * (𝔭.C * jb t ^ (-(𝔭.N : ℝ))) :=
          mul_le_mul h2 (hdec x) (norm_nonneg _) (by positivity)
      _ = 𝔭.C * (jb t ^ 2 * jb t ^ (-(𝔭.N : ℝ))) := by ring
      _ ≤ 𝔭.C * jb t ^ (-(((𝔭.decN 10).N : ℕ) : ℝ)) := by
          have hC : 0 ≤ 𝔭.C := by
            have := hdec x
            have h0 : 0 ≤ 𝔭.C * jb t ^ (-(𝔭.N : ℝ)) := (norm_nonneg _).trans this
            by_contra hneg
            push Not at hneg
            have : 0 < jb t ^ (-(𝔭.N : ℝ)) := Real.rpow_pos_of_pos hjpos _
            nlinarith
          exact mul_le_mul_of_nonneg_left h3 hC
  · intro ξ hξ
    have hξ' : 𝔭.δ * (2 : ℝ) ^ (-s) < |ξ| := hξ
    have hN' : (2 : ℝ) + 1 < (𝔭.N : ℝ) := by
      have : (14 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
      linarith
    have hint0 : Integrable ψ := by
      have h1 := (integrable_jb_rpow (c := dyCentre s v) hL (r := (𝔭.N : ℝ)) (by linarith)).const_mul 𝔭.C
      exact h1.mono' hcont.aestronglyMeasurable (Eventually.of_forall hdec)
    have hint2 : Integrable (fun x : ℝ => (((x - dyCentre s v) ^ 2 : ℝ) : ℂ) * ψ x) :=
      integrable_pow_mul_jb (c := dyCentre s v) (a := dyCentre s v) hL 2 (by push_cast; linarith) hcont hdec
    have h2 := fourier_pow_mul_eq_zero (c := dyCentre s v) hL hcont hdec hsupp (dyCentre s v) 2
      (by push_cast; linarith) ξ hξ'
    have e : psiTilde s v ψ = fun x => ψ x + (((2 : ℝ) ^ s)⁻¹ ^ 2 : ℝ) *
        ((((x - dyCentre s v) ^ 2 : ℝ) : ℂ) * ψ x) := funext (psiTilde_eq s v ψ)
    rw [e, fourier_add' hint0 (hint2.const_mul _), fourier_const_mul', h2, hsupp ξ hξ', mul_zero, add_zero]

end Classes

/-! ### Cross terms of the same frequency interval -/

theorem sq_mul_le (a b : ℝ) : 1 + (a - b) ^ 2 ≤ 2 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a * b)]

/-- Abstract cross-term bound: `|g| (1 + a²) = |h|`, `a - a' = n` give
`|∫ g ḡ'| ≤ (1 + n²)⁻¹ (∫|h|² + ∫|h'|²)`. -/
theorem cross_abstract {g g' h h' : ℝ → ℂ} {a a' : ℝ → ℝ} {n : ℝ}
    (hg : ∀ x, ‖g x‖ * (1 + a x ^ 2) = ‖h x‖) (hg' : ∀ x, ‖g' x‖ * (1 + a' x ^ 2) = ‖h' x‖)
    (hdiff : ∀ x, a x - a' x = n) (hh : Integrable (fun x => ‖h x‖ ^ 2))
    (hh' : Integrable (fun x => ‖h' x‖ ^ 2)) :
    ‖∫ x, g x * (starRingEnd ℂ) (g' x)‖ ≤ (1 + n ^ 2)⁻¹ * ((∫ x, ‖h x‖ ^ 2) + ∫ x, ‖h' x‖ ^ 2) := by
  have hn : 0 < 1 + n ^ 2 := by positivity
  have hpt : ∀ x, ‖g x * (starRingEnd ℂ) (g' x)‖ ≤ (1 + n ^ 2)⁻¹ * (‖h x‖ ^ 2 + ‖h' x‖ ^ 2) := by
    intro x
    rw [norm_mul, Complex.norm_conj, ← hdiff x]
    set A := 1 + a x ^ 2 with hA
    set A' := 1 + a' x ^ 2 with hA'
    have hApos : 0 < A := by positivity
    have hA'pos : 0 < A' := by positivity
    have h1 := sq_mul_le (a x) (a' x)
    rw [← hg x, ← hg' x]
    rw [inv_mul_eq_div, le_div_iff₀ (by rw [hdiff x]; exact hn)]
    have hnn : 0 ≤ ‖g x‖ * ‖g' x‖ := by positivity
    have h2 : ‖g x‖ * ‖g' x‖ * (1 + (a x - a' x) ^ 2) ≤ ‖g x‖ * ‖g' x‖ * (2 * (A * A')) :=
      mul_le_mul_of_nonneg_left h1 hnn
    nlinarith [sq_nonneg (‖g x‖ * A - ‖g' x‖ * A')]
  calc ‖∫ x, g x * (starRingEnd ℂ) (g' x)‖ ≤ ∫ x, ‖g x * (starRingEnd ℂ) (g' x)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, (1 + n ^ 2)⁻¹ * (‖h x‖ ^ 2 + ‖h' x‖ ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          ((hh.add hh').const_mul _) (Eventually.of_forall hpt)
    _ = _ := by rw [integral_const_mul, integral_add hh hh']

/-! ### The translation sum -/

/-- `∑_{n ∈ ℤ} (1 + n²)⁻¹`. -/
def sInv : ℝ := ∑' n : ℤ, (1 + (n : ℝ) ^ 2)⁻¹

theorem summable_sInv : Summable fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_one_add_abs_int_rpow_neg (p := 2) (by norm_num)).mul_left 2)
  have h1 : 0 < 1 + |(n : ℝ)| := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_two, ← one_div, ← one_div, mul_one_div, div_le_div_iff₀
    (by positivity) (by positivity)]
  nlinarith [sq_nonneg (|(n : ℝ)| - 1), sq_abs (n : ℝ)]

theorem sInv_nonneg : 0 ≤ sInv := tsum_nonneg fun n => by positivity

/-- Row sums of the translation weights over the tiles of one box. -/
theorem row_sum_le (T : Finset TriTile) (R : TriTile) :
    ∑ R' ∈ T, (if R.box = R'.box then (1 + ((R'.pos : ℝ) - R.pos) ^ 2)⁻¹ else 0) ≤ sInv := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun R' : TriTile => R'.pos - R.pos) (T.filter (fun R' => R.box = R'.box) : Set TriTile) := by
    intro R₁ h₁ R₂ h₂ h
    simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have : R₁.pos = R₂.pos := by simpa using h
    cases R₁; cases R₂
    simp_all
  have e : ∑ R' ∈ T.filter (fun R' => R.box = R'.box), (1 + ((R'.pos : ℝ) - R.pos) ^ 2)⁻¹ =
      ∑ n ∈ (T.filter (fun R' => R.box = R'.box)).image (fun R' => R'.pos - R.pos),
        (1 + (n : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun R' _ => ?_
    push_cast; rfl
  rw [e]
  exact summable_sInv.sum_le_tsum _ (fun n _ => by positivity)

/-! ### Boundedness and square integrability of the pieces -/

section Pieces

variable {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ}

theorem nonneg_C_of_inPsi (hψ : InPsi 𝔭 s v ψ) : 0 ≤ 𝔭.C := by
  have h := hψ.2.1 0
  have h0 : 0 ≤ 𝔭.C * jb ((0 - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) := (norm_nonneg _).trans h
  have hpos : 0 < jb ((0 - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) :=
    Real.rpow_pos_of_pos (jb_pos _) _
  exact nonneg_of_mul_nonneg_left h0 hpos

theorem norm_psi_le (hψ : InPsi 𝔭 s v ψ) (x : ℝ) : ‖ψ x‖ ≤ 𝔭.C := by
  refine (hψ.2.1 x).trans ?_
  have h1 := one_le_jb ((x - dyCentre s v) / (2 : ℝ) ^ s)
  have : jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by simp)
  calc _ ≤ 𝔭.C * 1 := mul_le_mul_of_nonneg_left this (nonneg_C_of_inPsi hψ)
    _ = _ := mul_one _

theorem norm_gfun_le (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    {f : ℝ → ℂ} {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) :
    ‖gfun ψ m f x‖ ≤ 𝔭.C * (B * ∫ w, ‖𝓕⁻ m w‖) := by
  unfold gfun
  rw [norm_mul]
  exact mul_le_mul (norm_psi_le hψ x) (norm_tm_le hD hβ hm hB x) (norm_nonneg _)
    (nonneg_C_of_inPsi hψ)

theorem integrable_sq_gfun (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (fun x => ‖gfun ψ m f x‖ ^ 2) := by
  have hint := integrable_gfun hN hD hβ hψ hm hf hB
  have hcont := continuous_gfun hD hβ hψ hm hf hB
  refine (hint.norm.const_mul (𝔭.C * (B * ∫ w, ‖𝓕⁻ m w‖))).mono'
    ((hcont.norm.pow 2).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  have h1 := norm_gfun_le hD hβ hψ hm hB x
  have h2 : 0 ≤ ‖gfun ψ m f x‖ := norm_nonneg _
  simp only [norm_pow, norm_norm]
  nlinarith

theorem integrable_gfun_mul_conj (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) {s' v' : ℤ} {c' : ℝ}
    {ψ' m' : ℝ → ℂ} (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m) (hψ' : InPsi 𝔭 s' v' ψ')
    (hm' : InMult 𝔭 s' c' m') {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (fun x => gfun ψ m f x * (starRingEnd ℂ) (gfun ψ' m' f x)) := by
  have hint := integrable_gfun hN hD hβ hψ hm hf hB
  have hcont' := continuous_gfun hD hβ hψ' hm' hf hB
  have := hint.bdd_mul (f := fun x => (starRingEnd ℂ) (gfun ψ' m' f x))
    (c := 𝔭.C * (B * ∫ w, ‖𝓕⁻ m' w‖))
    (Complex.continuous_conj.comp hcont').aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Complex.norm_conj]; exact norm_gfun_le hD hβ hψ' hm' hB x)
  exact this.congr (Eventually.of_forall fun x => mul_comm _ _)

end Pieces

/-! ### The scalar tree estimate -/

theorem tree_scalar_bound {𝔭 : Params} (hN : 14 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β)
    (hβδ : 𝔭.β + 2 * 𝔭.δ ≤ 3) {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3}
    {T : Finset TriTile} (hT : IsLacunary k T) (hbox : ∀ R ∈ T, R.box ∈ Qs) {ψ m : TriTile → ℝ → ℂ}
    (hdata : ∀ R ∈ T, InPsi 𝔭 R.box.scale R.pos (ψ R) ∧
      InMult 𝔭 R.box.scale (R.box.centre k) (m R))
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    ∫ x, ‖∑ R ∈ T, gfun (ψ R) (m R) f x‖ ^ 2 ≤ 2 * sInv * ∑ R ∈ T,
      ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 := by
  classical
  have hN2 : 2 ≤ 𝔭.N := by omega
  set g : TriTile → ℝ → ℂ := fun R => gfun (ψ R) (m R) f with hg
  set H : TriTile → ℝ := fun R => ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2 with hH
  have hψt : ∀ R ∈ T, InPsi (𝔭.decN 10) R.box.scale R.pos (psiTilde R.box.scale R.pos (ψ R)) :=
    fun R hR => inPsi_psiTilde hN (hdata R hR).1
  have hN' : 2 ≤ (𝔭.decN 10).N := by simp only [Params.decN]; omega
  have hHint : ∀ R ∈ T, Integrable (fun x => ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f x‖ ^ 2) :=
    fun R hR => integrable_sq_gfun (𝔭 := 𝔭.decN 10) hN' hD hβ (hψt R hR) (hdata R hR).2 hf hB
  have hprod : ∀ R ∈ T, ∀ R' ∈ T, Integrable (fun x => g R x * (starRingEnd ℂ) (g R' x)) := by
    intro R hR R' hR'
    exact integrable_gfun_mul_conj hN2 hD hβ (hdata R hR).1 (hdata R hR).2 (hdata R' hR').1
      (hdata R' hR').2 hf hB
  -- Step 1: expand the square
  have key : ∀ x, ‖∑ R ∈ T, g R x‖ ^ 2 =
      (∑ R ∈ T, ∑ R' ∈ T, g R x * (starRingEnd ℂ) (g R' x)).re := by
    intro x
    have h1 : (∑ R ∈ T, g R x) * (starRingEnd ℂ) (∑ R ∈ T, g R x) =
        ∑ R ∈ T, ∑ R' ∈ T, g R x * (starRingEnd ℂ) (g R' x) := by
      rw [map_sum, Finset.sum_mul_sum]
    rw [← h1, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hint2 : Integrable (fun x => ∑ R ∈ T, ∑ R' ∈ T, g R x * (starRingEnd ℂ) (g R' x)) :=
    integrable_finsetSum _ fun R hR => integrable_finsetSum _ fun R' hR' => hprod R hR R' hR'
  have hI : ∫ x, ‖∑ R ∈ T, g R x‖ ^ 2 = (∑ R ∈ T, ∑ R' ∈ T, ∫ x, g R x * (starRingEnd ℂ) (g R' x)).re := by
    simp_rw [key]
    have hre : ∫ x, (∑ R ∈ T, ∑ R' ∈ T, g R x * (starRingEnd ℂ) (g R' x)).re =
        (∫ x, ∑ R ∈ T, ∑ R' ∈ T, g R x * (starRingEnd ℂ) (g R' x)).re := by
      simpa using (Complex.reCLM.integral_comp_comm hint2)
    rw [hre, integral_finsetSum _ (fun R hR => integrable_finsetSum _
      fun R' hR' => hprod R hR R' hR')]
    congr 1
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [integral_finsetSum _ (fun R' hR' => hprod R hR R' hR')]
  -- Step 2: bounds for the entries
  set w : TriTile → TriTile → ℝ := fun R R' =>
    if R.box = R'.box then (1 + ((R'.pos : ℝ) - R.pos) ^ 2)⁻¹ else 0 with hw
  have hentry : ∀ R ∈ T, ∀ R' ∈ T, ‖∫ x, g R x * (starRingEnd ℂ) (g R' x)‖ ≤ w R R' * (H R + H R') := by
    intro R hR R' hR'
    by_cases hb : R.box = R'.box
    · have hs : R.box.scale = R'.box.scale := by rw [hb]
      have hψ' : InPsi 𝔭 R.box.scale R'.pos (ψ R') := by rw [hs]; exact (hdata R' hR').1
      have hm' : InMult 𝔭 R.box.scale (R'.box.centre k) (m R') := by rw [hs]; exact (hdata R' hR').2
      have hψt' : InPsi (𝔭.decN 10) R.box.scale R'.pos (psiTilde R.box.scale R'.pos (ψ R')) :=
        inPsi_psiTilde hN hψ'
      have hψtR := hψt R hR
      have hcross := cross_abstract
        (g := g R) (g' := g R') (a := fun x => (x - dyCentre R.box.scale R.pos) / (2 : ℝ) ^ R.box.scale)
        (a' := fun x => (x - dyCentre R.box.scale R'.pos) / (2 : ℝ) ^ R.box.scale)
        (h := gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) f)
        (h' := gfun (psiTilde R.box.scale R'.pos (ψ R')) (m R') f)
        (n := ((R'.pos : ℝ) - R.pos))
        (fun x => by
          simp only [hg, gfun, norm_mul, norm_psiTilde]; ring)
        (fun x => by
          simp only [hg, gfun, norm_mul, norm_psiTilde]; ring)
        (fun x => by
          have hL : (2 : ℝ) ^ R.box.scale ≠ 0 := (zpow_pos (by norm_num) _).ne'
          unfold dyCentre
          field_simp
          ring)
        (hHint R hR)
        (by
          have := integrable_sq_gfun (𝔭 := 𝔭.decN 10) hN' hD hβ hψt' hm' hf hB
          exact this)
      have hH' : (∫ x, ‖gfun (psiTilde R.box.scale R'.pos (ψ R')) (m R') f x‖ ^ 2) = H R' := by
        simp only [hH]; rw [hs]
      rw [hH'] at hcross
      simp only [hw, hb, ↓reduceIte]
      exact hcross
    · -- orthogonality
      have hωne : R.box.ω k ≠ R'.box.ω k := fun h => hb (box_eq_of_omega_eq hQ (hbox R hR) (hbox R' hR') h)
      have hdis := hT R hR R' hR' hωne
      rw [dilate_three_omega, dilate_three_omega] at hdis
      have := gfun_orthogonal hN2 hD hβ hβδ (hdata R hR).1 (hdata R' hR').1 (hdata R hR).2
        (hdata R' hR').2 hf hf hB hB hdis
      have h0 : ∫ x, g R x * (starRingEnd ℂ) (g R' x) = 0 := this
      have hw0' : w R R' = 0 := by
        show (if R.box = R'.box then (1 + ((R'.pos : ℝ) - R.pos) ^ 2)⁻¹ else 0) = 0
        rw [ite_eq_right hb]
      rw [h0, norm_zero, hw0', zero_mul]
  -- Step 3: sum the bounds
  have hH0 : ∀ R, 0 ≤ H R := fun R => integral_nonneg fun x => by positivity
  have hw0 : ∀ R R', 0 ≤ w R R' := fun R R' => by simp only [hw]; split_ifs <;> positivity
  have hwsymm : ∀ R R', w R R' = w R' R := by
    intro R R'
    simp only [hw]
    by_cases hb : R.box = R'.box
    · have hb' : R'.box = R.box := hb.symm
      rw [ite_eq_left hb, ite_eq_left hb']
      congr 2
      ring
    · have hb' : ¬ R'.box = R.box := fun h => hb h.symm
      rw [ite_eq_right hb, ite_eq_right hb']
  calc ∫ x, ‖∑ R ∈ T, g R x‖ ^ 2 = (∑ R ∈ T, ∑ R' ∈ T, ∫ x, g R x * (starRingEnd ℂ) (g R' x)).re := hI
    _ ≤ ‖∑ R ∈ T, ∑ R' ∈ T, ∫ x, g R x * (starRingEnd ℂ) (g R' x)‖ := Complex.re_le_norm _
    _ ≤ ∑ R ∈ T, ∑ R' ∈ T, ‖∫ x, g R x * (starRingEnd ℂ) (g R' x)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun R _ => norm_sum_le _ _)
    _ ≤ ∑ R ∈ T, ∑ R' ∈ T, w R R' * (H R + H R') :=
        Finset.sum_le_sum fun R hR => Finset.sum_le_sum fun R' hR' => hentry R hR R' hR'
    _ = ∑ R ∈ T, H R * ∑ R' ∈ T, w R R' + ∑ R' ∈ T, H R' * ∑ R ∈ T, w R R' := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun R' _ => by ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun R' _ => Finset.sum_congr rfl fun R _ => by ring
    _ ≤ ∑ R ∈ T, H R * sInv + ∑ R' ∈ T, H R' * sInv := by
        refine add_le_add (Finset.sum_le_sum fun R _ => ?_) (Finset.sum_le_sum fun R' _ => ?_)
        · exact mul_le_mul_of_nonneg_left (row_sum_le T R) (hH0 R)
        · have : ∑ R ∈ T, w R R' = ∑ R ∈ T, w R' R := Finset.sum_congr rfl fun R _ => hwsymm R R'
          rw [this]
          exact mul_le_mul_of_nonneg_left (row_sum_le T R') (hH0 R')
    _ = 2 * sInv * ∑ R ∈ T, H R := by
        rw [← Finset.sum_mul]; ring

end PrimeBHT.TimeFrequency.X2
