module

public import PrimeBHT.TimeFrequency.X2.EngTail.Top
public import PrimeBHT.TimeFrequency.X2.V16.Hyps

/-!
# X2, node B5: the corrected statement and its reduction to one lacunary tree

* `EngLeTailMassStatementD`: the printed `EngLeTailMassStatement` of `X2/V16/Hyps.lean` plus the hypothesis
  `M + 100 ≤ 𝔭.D` (without a derivative margin the statement is false, see `EngTail/Top.lean`).
* `TreeLqBound 𝔭 s q M`: the single-tree estimate (DPLMV `e:engbd1`): for one `k`-lacunary tree `Tr` with top `t`,
  one choice of tree-operator data `(ψ, m)` of the class `𝔭`, `|I_t|^{-1/q} ‖T_Tr F‖_{L^q(ℝ; L^s(Y))} ≤ C sup_{R ∈ Tr} λ_M(‖F‖; I_R)`.
* `engLeTailMass_of_treeLqBound`: `TreeLqBound ⟹ EngLeTailMassStatementD` (pure bookkeeping, proved here); `TreeLqBound` itself is
  proved in `Tree.lean` (`treeLqBound`), hence `engLeTailMass : EngLeTailMassStatementD` unconditionally.

## Proof plan for `TreeLqBound` (DPLMV `l:engbd` / `e:engbd1`, redone without BMO) and its status

`F ↦ T_Tr F` is linear, so only `λ = sup_{R ∈ Tr} λ_M(‖F‖; I_R)` matters.  The sup-norm bound is FALSE (the Hilbert
transform of `1_{[0,1]}` is `log`-unbounded) and the trivial `L^q` bound by the strong type loses `λ ↦ λ^{1/q}`.
Corrected hypotheses needed by the proof: `M + 1 ≤ 𝔭.D` (kernel and derivative decay), `N ≥ M + 4`, `1 < q < ∞`
(`q ≥ 2` is NOT used), lacunarity (disjoint `3ω`, with `β ≤ 11/4`) is used only in the scalar `L²` bound.

**Reduction (done).**  Demodulate by `θ = t.2 · freqDir k` (`centre_sub_theta_le`: `|c_k(R) - θ| ≤ 2 hullConst 2^{-scale}`):
`T_Tr F = e(θ x) · kernelOp K' F'`, `K' = ∑_R ψ_R(x) κ'_R(x - z)`, `κ'_R = kernelDemod θ (m R) = 𝓕⁻(m_R(· + θ))`,
`F' = e(-θ ·) F` (`yNorm` unchanged).  `exists_tileBound` gives `TileBound N M C_φ C_κ` for every tile (decay of `ψ`, `ψ'`
(weighted Bernstein), `κ'`, `(κ')'`).

**Built pieces (this folder; everything is proved, no hypothesis).**
* (1) CZ verification: `isCZKernel_tileKernel` (`IsCZKernel` of a finite tile sum, `CZKernel.lean`), `tree_L2` (scalar `L²`
  bound by Fourier orthogonality, `L2.lean`), `CZ.vectorCZ_strong_bdd` (strong half of `vectorCZStatement` with the `L²`
  hypothesis for bounded integrable `g`, `CZWeak.lean`), `tileKernelOp_strong` / `treeOp_strong` (strong type of every lacunary
  sub-tree operator, uniform constants, `TreeStrong.lean`).
* (3) `famPhiT_norm_le` (`FamSum.lean`): `‖∑_i a_i (1 + |x - c_i|/ℓ_i)^{-2}‖_q ≤ C_q (∑ a_i^q ℓ_i)^{1/q}` for pairwise disjoint
  intervals `[c_i ± ℓ_i/2)`.
* (2) pointwise kernel bounds (`Near.lean`): `sum_near_le` (no cancellation, scale `≥ δ` or distance `≥ δ`), `sum_tail_le`
  (tiles of a dyadic interval `L` against a source outside `3L`, `N ≥ M + 4`), `kernel_atom_le`
  (`‖K(x,z) - K(x,c)‖ ≤ C δ⁻¹ (1 + |x - c|/δ)^{-2}`, near zone by `sum_near_le`, far zone by `tileKernel_smooth`).
* (4) bookkeeping: `Cover.lean` (`W(S) = ⋃ 3 I_i`, maximal tiles, `∫_{W(S)} u ≤ (5/2)^M λ |W(S)|`), `Decomp.lean` (`cz_step`:
  pointwise CZ decomposition `‖K F‖ ≤ ‖K g‖ + ∑_i 4λ A₁ (1 + |x - c_i|/|Q_i|)^{-2}`), `Ops.lean` (Minkowski tools, `Lq`),
  `Tail.lean` (`tail_op_le`: `‖K_T (F' 1_{W^c})(x)‖_X ≤ ∑_{L max} C λ (1 + |x - c_L|/|I_L|)^{-2}`), `Gen.lean` (near tiles
  `S_near`, `|W(S_near)| ≤ 7 ∑ |Q_i|`), `Step.lean` (`step_bound`: one step of the induction, contraction `2^{-q}` from
  `A = 7 (5/2)^M 2^q`), `Induct.lean` (`tile_induction`, `tile_bound_main`: induction on `|T|`, `λ = 0` by a limit),
  `Tree.lean` (`treeLqBound`, `engLeTailMass : EngLeTailMassStatementD`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **B5, corrected**: the printed statement plus the derivative margin `M + 100 ≤ 𝔭.D`. -/
def EngLeTailMassStatementD : Prop :=
  ∀ (𝔭 : Params), 𝔭.Admissible → ∀ {s q M : ℝ}, 1 < s → 2 ≤ q → 3 ≤ M → M + 100 ≤ 𝔭.N → M + 100 ≤ 𝔭.D →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (Cs : Finset TriTile), (∀ R ∈ Cs, R.box ∈ Qs) → ∀ (k : Fin 3) (F : ℝ → ZMod P → ℂ),
        Measurable F → (∀ x, yNorm s (F x) ≤ 1) →
          eng 𝔭 s k F Cs q ≤
            ENNReal.ofReal C * ⨆ R ∈ Cs, ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) R.I)

/-- The single-tree estimate (DPLMV `e:engbd1`, with the tail masses `λ_M`). -/
def TreeLqBound (𝔭 : Params) (s q M : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (k : Fin 3)
    (Tr : Finset TriTile) (t : Top), (∀ R ∈ Tr, R.box ∈ Qs) → IsTree Tr t → IsLacunary k Tr →
    ∀ (ψ m : TriTile → ℝ → ℂ), IsTreeOpData 𝔭 k Tr ψ m → ∀ (F : ℝ → ZMod P → ℂ), Measurable F →
      (∀ x, yNorm s (F x) ≤ 1) →
        treeOpNorm s q Tr t ψ m F ≤
          ENNReal.ofReal C * ⨆ R ∈ Tr, ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) R.I)

/-- `TreeLqBound` implies B5 (the sup over trees of `Cs`, the sup over tree data, and monotonicity of the sup of
tail masses in the collection). -/
theorem engLeTailMass_of_treeLqBound
    (h : ∀ (𝔭 : Params), 𝔭.Admissible → ∀ {s q M : ℝ}, 1 < s → 2 ≤ q → 3 ≤ M → M + 100 ≤ 𝔭.N →
      M + 100 ≤ 𝔭.D → TreeLqBound 𝔭 s q M) : EngLeTailMassStatementD := by
  intro 𝔭 h𝔭 s q M hs hq hM hN hD
  obtain ⟨C, hC0, hC⟩ := h 𝔭 h𝔭 hs hq hM hN hD
  refine ⟨C, hC0, ?_⟩
  intro P _ Qs hQ Cs hbox k F hF hFb
  refine eng_le_of_forall fun Tr hTr t ht hlac => ?_
  refine topNorm_le_of_forall fun ψ m hψm => ?_
  refine (hC P Qs hQ k Tr t (fun R hR => hbox R (hTr hR)) ht hlac ψ m hψm F hF hFb).trans ?_
  refine mul_le_mul' le_rfl ?_
  exact iSup₂_le fun R hR => le_iSup₂_of_le R (hTr hR) le_rfl

end PrimeBHT.TimeFrequency.X2
