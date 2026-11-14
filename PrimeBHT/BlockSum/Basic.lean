module

public import PrimeBHT.Kernel
public import PrimeBHT.PeriodicAssembly
public import PrimeCarleson.Proof.Paper.P5.Assembly
public import PrimeCarleson.Proof.FplusProp21.Application

/-!
# Block sum (blueprint N43 and N26): definitions, the block partition, bilinear-sum algebra

Definitions of `a_Q`, `N(Q)`, `K_{Q;τ}`, `H^J_{Q;τ,B}`, `U^J_{Q;τ}` (local copy of the draft `uOp`),
the conditional hypothesis `BlockTransferBound` (the conclusion of N42 plus the chart sum of
N43(a)), and

* N43(b), `exists_blockPartition_sqfree`: the squarefree integers in `(Q/2, Q]` are partitioned
  into blocks, with the vendored constants `A = 24` (blueprint: `2`; see the docstring);
* algebra of `bilin` for finitely supported inputs;
* `eLpNorm` bridges for the final `p_key0` shape.
-/

@[expose] public section

namespace PrimeBHT.BlockSum

open PrimeBHT.Kernel PrimeCarleson
open PrimeCarleson.Proof.Paper (sqfreeSet mem_sqfreeSet lcmQ BlockPartition exists_blockPartition_24)
open scoped FourierTransform

/-! ## Definitions -/

/-- `a_Q = ⌈Q^τ⌉`. -/
noncomputable def aQ (Q : ℕ) (τ : ℝ) : ℕ := ⌈(Q : ℝ) ^ τ⌉₊

/-- `N(Q) = exp(Q^{τ - ε/10})`. -/
noncomputable def NQ (Q : ℕ) (τ ε : ℝ) : ℝ := Real.exp ((Q : ℝ) ^ (τ - ε / 10))

/-- `K^J_{Q;τ} = φ_{N(Q)} * ∑_{a_Q ≤ k ≤ J} ψ_k` (convolution on `ℝ`; evaluated at integers). -/
noncomputable def KQ (φ : SchwartzMap ℝ ℝ) (χ : ℝ → ℝ) (Q : ℕ) (τ ε : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  smooth φ (NQ Q τ ε) (kernelI χ (aQ Q τ) J) t

/-- `H^J_{Q;τ,B}(f, g)(x) = ∑_n K^J_{Q;τ}(n) w_{Q,B}(n) f(x - n) g(x + n)`, with
`w_{Q,B} = blockWeight B`. -/
noncomputable def hOp (φ : SchwartzMap ℝ ℝ) (χ : ℝ → ℝ) (Q : ℕ) (τ ε : ℝ) (J : ℕ) (B : Finset ℕ)
    (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  bilin (fun n : ℤ => ((KQ φ χ Q τ ε J (n : ℝ) : ℝ) : ℂ) * blockWeight B n) f g x

/-- The unsmoothed truncated operator `U^J_{Q;τ}(f, g)(x) = ∑_{Q^τ ≤ k ≤ J} ∑_n ψ_k(n) w_Q(n)
f(x - n) g(x + n)`; the same body as the draft `PrimeBHT.Statements.uOp`
(`docs/audits/Key0Statement.draft.lean.txt`). -/
noncomputable def uOp (χ : ℝ → ℝ) (Q : ℕ) (τ : ℝ) (J : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc ⌈(Q : ℝ) ^ τ⌉₊ J,
    ∑' n : ℤ, ((PrimeBHT.Kernel.psiK χ k (n : ℝ) : ℝ) : ℂ) *
      PrimeCarleson.blockWeight (Finset.Ioc (Q / 2) Q) n * f (x - n) * g (x + n)

/-- **The per-block transference bound (HYPOTHESIS).** The conclusion of N42 together with the
chart-sum argument of N43(a): there are `C` and `Q₀` such that for every dyadic `Q = 2^j ≥ Q₀`,
every `J`, every nonempty set `B` of squarefree integers in `(Q/2, Q]` with `|B| ≤ A Q^κ`
(`κ = τ - ε`), `N = lcm B`, and every constant `D` dominating the periodic operator norm,
`‖A_B(F, G)‖_{L^p(Y_N)} ≤ D ‖F‖₂ ‖G‖₂` for all `F, G : ZMod N → ℂ` (so `D ≥ d_B(p)`),
`‖H^J_{Q;τ,B}(f, g)‖_{ℓ¹} ≤ C · D · ‖f‖₂ ‖g‖₂` for finitely supported `f, g`.
The premise is the standing assumption that `φ̂` vanishes outside `[-c, c]`. -/
def BlockTransferBound (φ : SchwartzMap ℝ ℝ) (c : ℝ) (χ : ℝ → ℝ) (τ ε p A : ℝ) : Prop :=
  (∀ ξ : ℝ, c < |ξ| → 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) ξ = 0) →
  ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ j : ℕ, Q₀ ≤ 2 ^ j → ∀ J : ℕ,
    ∀ B : Finset ℕ, B ⊆ sqfreeSet j → B.Nonempty →
    (B.card : ℝ) ≤ A * ((2 : ℝ) ^ j) ^ (τ - ε) →
    ∀ (N : ℕ) [NeZero N], lcmQ B = N →
    ∀ D : ℝ, (∀ F G : ZMod N → ℂ,
      PrimeBHT.PeriodicAssembly.lpNorm p
          (PrimeBHT.PeriodicBlock.bilinAvg (PrimeBHT.PeriodicBlock.lam B N) F G) ≤
        D * PrimeBHT.Periodic.l2 F * PrimeBHT.Periodic.l2 G) →
    ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
      Summable (fun x => ‖hOp φ χ (2 ^ j) τ ε J B f g x‖) ∧
      ∑' x, ‖hOp φ χ (2 ^ j) τ ε J B f g x‖ ≤ C * D * (l2norm f * l2norm g)

/-! ## N43(b): the block partition -/

/-- The squarefree membership as real inequalities `Q/2 < q ≤ Q`, `Q = 2^j`. -/
theorem real_bounds_of_mem_sqfreeSet {j q : ℕ} (hq : q ∈ sqfreeSet j) :
    (2 : ℝ) ^ j / 2 < (q : ℝ) ∧ (q : ℝ) ≤ (2 : ℝ) ^ j := by
  obtain ⟨h1, h2, -⟩ := mem_sqfreeSet.1 hq
  have h1' : 2 ^ j < q * 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 h1
  refine ⟨?_, by exact_mod_cast h2⟩
  have : ((2 ^ j : ℕ) : ℝ) < ((q * 2 : ℕ) : ℝ) := by exact_mod_cast h1'
  push_cast at this
  linarith

/-! ## Algebra of `bilin` for finitely supported inputs -/

theorem summable_bilinTerm {f : ℤ → ℂ} (hf : (Function.support f).Finite) (a : ℤ → ℂ)
    (g : ℤ → ℂ) (x : ℤ) : Summable (fun n : ℤ => a n * f (x - n) * g (x + n)) := by
  have hfin : {n : ℤ | f (x - n) ≠ 0}.Finite :=
    hf.preimage (f := fun n : ℤ => x - n) (sub_right_injective.injOn)
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hn
  simp [hn]

theorem bilin_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ → ℂ) {f : ℤ → ℂ}
    (hf : (Function.support f).Finite) (g : ℤ → ℂ) (x : ℤ) :
    bilin (fun n => ∑ i ∈ s, a i n) f g x = ∑ i ∈ s, bilin (a i) f g x := by
  unfold bilin
  rw [← Summable.tsum_finsetSum fun i _ => summable_bilinTerm hf (a i) g x]
  refine tsum_congr fun n => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

theorem bilin_sub {f : ℤ → ℂ} (hf : (Function.support f).Finite) (a b : ℤ → ℂ) (g : ℤ → ℂ)
    (x : ℤ) :
    bilin (fun n => a n - b n) f g x = bilin a f g x - bilin b f g x := by
  unfold bilin
  rw [← Summable.tsum_sub (summable_bilinTerm hf a g x) (summable_bilinTerm hf b g x)]
  refine tsum_congr fun n => ?_
  ring

/-- `U = bilin (K_I · w_Q)` for finitely supported `f`. -/
theorem uOp_eq_bilin (χ : ℝ → ℝ) (Q : ℕ) (τ : ℝ) (J : ℕ) {f : ℤ → ℂ}
    (hf : (Function.support f).Finite) (g : ℤ → ℂ) (x : ℤ) :
    uOp χ Q τ J f g x =
      bilin (fun n : ℤ => ((kernelI χ ⌈(Q : ℝ) ^ τ⌉₊ J (n : ℝ) : ℝ) : ℂ) *
        blockWeight (Finset.Ioc (Q / 2) Q) n) f g x := by
  unfold bilin uOp
  have hs : ∀ k ∈ Finset.Icc ⌈(Q : ℝ) ^ τ⌉₊ J, Summable (fun n : ℤ =>
      ((psiK χ k (n : ℝ) : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n * f (x - n) *
        g (x + n)) := fun k _ =>
    summable_bilinTerm hf (fun n => ((psiK χ k (n : ℝ) : ℝ) : ℂ) *
      blockWeight (Finset.Ioc (Q / 2) Q) n) g x
  rw [← Summable.tsum_finsetSum hs]
  refine tsum_congr fun n => ?_
  simp only [kernelI, Complex.ofReal_sum, Finset.sum_mul]

/-- `U - H = bilin (w_Q (K_I - φ_N * K_I))` (the integrand of the smoothing error). -/
theorem uOp_sub_hOp (φ : SchwartzMap ℝ ℝ) (χ : ℝ → ℝ) (Q : ℕ) (τ ε : ℝ) (J : ℕ)
    {f : ℤ → ℂ} (hf : (Function.support f).Finite) (g : ℤ → ℂ) (x : ℤ) :
    uOp χ Q τ J f g x - hOp φ χ Q τ ε J (Finset.Ioc (Q / 2) Q) f g x =
      bilin (fun n : ℤ => blockWeight (Finset.Ioc (Q / 2) Q) n *
        ((kernelI χ (aQ Q τ) J (n : ℝ) -
          smooth φ (NQ Q τ ε) (kernelI χ (aQ Q τ) J) (n : ℝ) : ℝ) : ℂ)) f g x := by
  rw [uOp_eq_bilin χ Q τ J hf g x]
  unfold hOp KQ
  rw [← bilin_sub hf]
  congr 1
  funext n
  simp only [aQ]
  push_cast
  ring

/-- The weights add up over a block partition (`Q = 2^j`, using `μ(q) = 0` for non-squarefree
`q`): `hOp B_Q = ∑_B hOp B`. -/
theorem hOp_eq_sum_blocks {j : ℕ} {κ A : ℝ} (π : BlockPartition j κ A) (φ : SchwartzMap ℝ ℝ)
    (χ : ℝ → ℝ) (τ ε : ℝ) (J : ℕ) {f : ℤ → ℂ} (hf : (Function.support f).Finite) (g : ℤ → ℂ)
    (x : ℤ) :
    hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x =
      ∑ B ∈ π.blocks, hOp φ χ (2 ^ j) τ ε J B f g x := by
  unfold hOp
  rw [← bilin_finset_sum π.blocks _ hf]
  congr 1
  funext n
  rw [π.blockWeight_eq_sum_blocks n, Finset.mul_sum]

/-! ## `ℓ¹`/`ℓ²` norm bridges -/

/-- For finitely supported `f`, `‖f‖_{ℓ²}` as an `eLpNorm` is `ofReal (l2norm f)`. -/
theorem eLpNorm_two_count_eq_ofReal {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ENNReal.ofReal (l2norm f) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (measurable_of_countable f).aestronglyMeasurable, MeasureTheory.lintegral_count]
  have hS := summable_norm_sq_of_finite_support hf
  have h1 : ∑' x, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∑' x, ‖f x‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => sq_nonneg _) hS]
    refine tsum_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]
  have h2 : (2 : ENNReal).toReal = 2 := rfl
  simp only [h2]
  rw [h1, ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun x => sq_nonneg _) (by norm_num),
    l2norm, Real.sqrt_eq_rpow]

/-- `‖F‖_{ℓ¹}` as an `eLpNorm` is `ofReal ∑' ‖F x‖` when the norms are summable. -/
theorem eLpNorm_one_count_eq_ofReal {F : ℤ → ℂ} (hF : Summable fun x => ‖F x‖) :
    MeasureTheory.eLpNorm F 1 MeasureTheory.Measure.count = ENNReal.ofReal (∑' x, ‖F x‖) := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (measurable_of_countable F).aestronglyMeasurable,
    MeasureTheory.lintegral_count, ENNReal.ofReal_tsum_of_nonneg (fun x => norm_nonneg _) hF]
  exact tsum_congr fun x => (ofReal_norm _).symm

end PrimeBHT.BlockSum
