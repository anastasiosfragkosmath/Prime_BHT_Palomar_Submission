module

public import PrimeBHT.TimeFrequency.X2.Psp.Lacunary
public import PrimeBHT.TimeFrequency.X2.Psp.Bernstein
public import PrimeBHT.TimeFrequency.X2.Psp.Geometry
public import PrimeBHT.TimeFrequency.X2.ClassKernel

/-!
# X2, V13 part 2 (A): the single-scale sup bound (L3)

* `sum_jb_le`: `Σ_{v ∈ V} ⟨a - v⟩^{-M} ≤ 2^M Σ_{j ∈ ℤ} ⟨j⟩^{-M}` (lattice sum, `M > 1`);
* `single_tile_sup_le`: `‖θ'_R(x)‖ · ‖T_m F(x)‖_{L^s(Y)} ≤ C eng` for a single tile `R` (Bernstein `L^q → L^∞` + the single-tile
  energy bound);
* `lacunary_L3` (L3): `‖χ̃_σ(x) T_{m_σ}F(x)‖_{L^s(Y)} ≤ C eng 𝔭.tree s k F Tr q` for every `x`, `σ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Measurability (local copies of `Ortho.TileEng.measurable_tmult`, to keep the Psp chain free of `Ortho.TileEng`, which clashes
with `Paraproduct.General.measurable_tmult`) -/

theorem measurable_tmult_psp {P : ℕ} {𝔭 : Params} {sc : ℤ} {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 sc c m)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) : Measurable (tmult m F) := by
  have hK : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : StronglyMeasurable (Function.uncurry fun (x z : ℝ) => 𝓕⁻ m (x - z) * F z y) :=
    ((hK.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).mul
      ((((measurable_pi_apply y).comp hF).comp measurable_snd).stronglyMeasurable)
  exact (h1.integral_prod_right).measurable

theorem measurable_psi_smul_tmult_psp {P : ℕ} {𝔭 : Params} {sc v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ}
    (hψ : InPsi 𝔭 sc v ψ) (hm : InMult 𝔭 sc c m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (fun x => ψ x • tmult m F x) := by
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : Measurable fun x => tmult m F x y := (measurable_pi_apply y).comp (measurable_tmult_psp hm hF)
  show Measurable fun x => ψ x * tmult m F x y
  exact hψ.1.measurable.mul h1

/-! ## The lattice sum -/

theorem summable_jb_int {M : ℝ} (hM : 1 < M) : Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ (-M)) := by
  have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-M)) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -M < -1))
    refine this.congr fun n => ?_
    simp [add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · refine h1.congr fun n => ?_
    simp
  · refine h1.congr fun n => ?_
    simp

/-- The constant `Σ_{j ∈ ℤ} ⟨j⟩^{-M}`. -/
def jbConst (M : ℝ) : ℝ := ∑' j : ℤ, (1 + |(j : ℝ)|) ^ (-M)

theorem jbConst_nonneg (M : ℝ) : 0 ≤ jbConst M :=
  tsum_nonneg fun j => Real.rpow_nonneg (by positivity) _

theorem sum_jb_le {M : ℝ} (hM : 1 < M) (V : Finset ℤ) (a : ℝ) :
    ∑ v ∈ V, jb (a - v) ^ (-M) ≤ 2 ^ M * jbConst M := by
  set n : ℤ := ⌊a⌋ with hn
  have hfl : |a - n| ≤ 1 := by
    have h1 := Int.floor_le a
    have h2 := Int.lt_floor_add_one a
    rw [abs_le]; constructor <;> linarith
  have hpt : ∀ v : ℤ, jb (a - v) ^ (-M) ≤ 2 ^ M * (1 + |((v - n : ℤ) : ℝ)|) ^ (-M) := by
    intro v
    have h1 : 1 + |((v - n : ℤ) : ℝ)| ≤ 2 * jb (a - v) := by
      unfold jb
      push_cast
      have := abs_sub_le (v : ℝ) a n
      have h3 : |(v : ℝ) - a| = |a - v| := abs_sub_comm _ _
      nlinarith [abs_nonneg (a - v), abs_nonneg ((v : ℝ) - n)]
    have hp : 0 < 1 + |((v - n : ℤ) : ℝ)| := by positivity
    have h2 : jb (a - v) ^ (-M) ≤ ((1 + |((v - n : ℤ) : ℝ)|) / 2) ^ (-M) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    refine h2.trans (le_of_eq ?_)
    rw [Real.div_rpow hp.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
    ring
  have hs := summable_jb_int hM
  calc ∑ v ∈ V, jb (a - v) ^ (-M) ≤ ∑ v ∈ V, 2 ^ M * (1 + |((v - n : ℤ) : ℝ)|) ^ (-M) :=
        Finset.sum_le_sum fun v _ => hpt v
    _ = 2 ^ M * ∑ v ∈ V, (1 + |((v - n : ℤ) : ℝ)|) ^ (-M) := by rw [Finset.mul_sum]
    _ ≤ 2 ^ M * jbConst M := by
        gcongr
        have hs' : Summable (fun v : ℤ => (1 + |((v - n : ℤ) : ℝ)|) ^ (-M)) :=
          (Equiv.summable_iff (f := fun j : ℤ => (1 + |(j : ℝ)|) ^ (-M)) (Equiv.subRight n)).2 hs
        calc ∑ v ∈ V, (1 + |((v - n : ℤ) : ℝ)|) ^ (-M)
            ≤ ∑' v : ℤ, (1 + |((v - n : ℤ) : ℝ)|) ^ (-M) :=
              hs'.sum_le_tsum V fun i _ => Real.rpow_nonneg (by positivity) _
          _ = jbConst M := (Equiv.subRight n).tsum_eq (fun j : ℤ => (1 + |(j : ℝ)|) ^ (-M))

/-! ## A single tile -/

/-- The constant of the single-tile sup bound. -/
def tileSupConst (𝔭 : Params) (q : ℝ) : ℝ :=
  bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) * (𝔭.β + 2 * 𝔭.δ) ^ (1 / q)

theorem tileSupConst_nonneg (𝔭 : Params) {q : ℝ} (hq : 1 < q) (hβ : 0 ≤ 𝔭.β + 2 * 𝔭.δ) : 0 ≤ tileSupConst 𝔭 q := by
  unfold tileSupConst
  have hq' : 1 < Real.conjExponent q := (Real.HolderConjugate.conjExponent hq).symm.lt
  have : 0 < 2 * Real.conjExponent q - 1 := by linarith
  have := bernC2_pos
  positivity

/-- **Single tile, sup bound**: `‖θ'_R(x)‖ ‖T_m F(x)‖_{L^s(Y)} ≤ C eng` (Bernstein `L^q → L^∞` for the band-limited piece
`θ'_R T_m F`, normalized by the single-tile energy). -/
theorem single_tile_sup_le {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η)
    {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {ξ : ℝ}
    (hξ : ξ ∈ R.box.hull) {m : ℝ → ℂ} (hm : InMult 𝔭 R.box.scale (R.box.centre k) m) (x : ℝ) :
    ENNReal.ofReal (‖cutoffPsi 𝔭 η R.box.scale R.pos x‖ * yNorm s (tmult m F x)) ≤
      ENNReal.ofReal (tileSupConst 𝔭 q) * eng 𝔭 s k F Cs q := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hδ0 : 0 < 𝔭.δ := h𝔭.2.2.2.1
  obtain ⟨B, hB⟩ := hFb
  set σ : ℤ := R.box.scale with hσ
  set c : ℝ := R.box.centre k with hc
  set θ : ℝ → ℂ := cutoffPsi 𝔭 η σ R.pos with hθ
  have hψ : InPsi 𝔭 σ R.pos θ := inPsi_cutoffPsi hη (by linarith) (by omega) σ R.pos
  set w : ℝ := (𝔭.β / 2 + 𝔭.δ) * (2 : ℝ) ^ (-σ) with hw
  have hw0 : 0 < w := by have := zpow_two_pos (-σ); positivity
  set G : ℝ → ZMod P → ℂ := fun z => θ z • tmult m F z with hG
  have hcoord : ∀ y : ZMod P, IsBandLimited (fun z => G z y) (Icc (c - w) (c + w)) := by
    intro y
    have hf : Measurable (fun z => F z y) := (measurable_pi_apply y).comp hF
    have hfB : ∀ z, ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z =>
      (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
        (mul_le_mul_of_nonneg_left (hB z) (by positivity))
    exact isBandLimited_gfun (by omega) (by omega) (by linarith) hψ hm hf hfB
  have hmeasG : Measurable fun z => yNorm s (G z) :=
    (measurable_yNorm_fun s).comp (measurable_pi_iff.2 fun y => (hcoord y).continuous.measurable)
  set L' : ℝ := (2 * w)⁻¹ with hL'
  have hL'0 : 0 < L' := inv_pos.2 (by linarith)
  have hS : Icc (c - w) (c + w) ⊆ Icc (c - 1 / (2 * L')) (c + 1 / (2 * L')) := by
    have : 1 / (2 * L') = w := by rw [hL']; field_simp
    rw [this]
  have hb := bernstein_Lq_Linf hs hq hcoord hL'0 hS hmeasG x
  -- the single-tile energy
  have hE := single_tile_le_eng (𝔭 := 𝔭) (s := s) (q := q) (k := k) (F := F) hR hξ hψ hm
  have ha : 0 < ((2 : ℝ) ^ σ) ^ (-1 / q) := Real.rpow_pos_of_pos (zpow_two_pos σ) _
  have hE2 : eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * eng 𝔭 s k F Cs q := by
    have e : ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (-1 / q)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (zpow_two_pos σ).le _), ← Real.rpow_add (zpow_two_pos σ)]
      have : 1 / q + -1 / q = 0 := by ring
      rw [this, Real.rpow_zero, ENNReal.ofReal_one]
    calc eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume
        = ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (-1 / q)) *
            eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hE
  have hnorm : ‖θ x‖ * yNorm s (tmult m F x) = yNorm s (G x) :=
    (yNorm_fun_const_mul (by linarith) (θ x) (tmult m F x)).symm
  rw [hnorm]
  refine hb.trans ?_
  -- constants
  have hconst : bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) * L' ^ (-(1 / q)) *
      ((2 : ℝ) ^ σ) ^ (1 / q) = tileSupConst 𝔭 q := by
    unfold tileSupConst
    have h2w : 2 * w = (𝔭.β + 2 * 𝔭.δ) * (2 : ℝ) ^ (-σ) := by rw [hw]; ring
    have e1 : L' ^ (-(1 / q)) = (2 * w) ^ (1 / q) := by
      rw [hL', Real.rpow_neg (inv_pos.2 (by linarith)).le, Real.inv_rpow (by linarith), inv_inv]
    have hbd : 0 < 𝔭.β + 2 * 𝔭.δ := by linarith
    have e2 : (2 * w) ^ (1 / q) * ((2 : ℝ) ^ σ) ^ (1 / q) = (𝔭.β + 2 * 𝔭.δ) ^ (1 / q) := by
      rw [h2w, Real.mul_rpow hbd.le (zpow_two_pos _).le, mul_assoc, ← Real.mul_rpow (zpow_two_pos _).le (zpow_two_pos _).le,
        ← zpow_add₀ (by norm_num)]
      simp
    rw [e1, mul_assoc, e2]
  calc ENNReal.ofReal (bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) * L' ^ (-(1 / q))) *
        eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal (bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) * L' ^ (-(1 / q))) *
        (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * eng 𝔭 s k F Cs q) := mul_le_mul' le_rfl hE2
    _ = ENNReal.ofReal (tileSupConst 𝔭 q) * eng 𝔭 s k F Cs q := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by
          have hq' : 1 < Real.conjExponent q := (Real.HolderConjugate.conjExponent hq).symm.lt
          have : 0 < 2 * Real.conjExponent q - 1 := by linarith
          have := bernC2_pos
          have := Real.rpow_pos_of_pos hL'0 (-(1 / q))
          positivity), hconst]

/-! ## (L3) -/

/-- The constant of (L3). -/
def lacL3Const (𝔭 : Params) (q : ℝ) : ℝ :=
  cutK 𝔭 * (𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ))) * tileSupConst 𝔭.tree q *
    (2 ^ ((𝔭.N : ℝ) / 2) * jbConst ((𝔭.N : ℝ) / 2)) + 1

/-- **(L3)**: for every `x`, `‖χ̃_σ(x) T_{m_σ}F(x)‖_{L^s(Y)} ≤ C · eng 𝔭.tree s k F Tr q` (`TA ⊆ Tr`).  Uses a second cutoff
profile `η'` of the class `𝔭.tree` (V05-1 at decay `N/8`): the model profile `η` decays like `⟨·⟩^{-N}`, faster than the weights
`⟨·⟩^{-N/2}` that are dominated by `θ'_{η'}` (D-2). -/
theorem lacunary_L3 {𝔭 : Params} {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) (h𝔭 : 𝔭.Admissible)
    (h𝔭t : 𝔭.tree.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭.tree η') {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η)
    {Tr TA : Finset TriTile} {t : Top} {k : Fin 3} {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}
    (hT : IsGoodTree TA t) (hsub : TA ⊆ Tr) (hd : LacData 𝔭 TA k η χ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    ENNReal.ofReal (yNorm s ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x)) ≤
      ENNReal.ofReal (lacL3Const 𝔭 q) * eng 𝔭.tree s k F Tr q := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  obtain ⟨hNt, hDt, hβt, hCt⟩ := h𝔭t.bounds
  have hs0 : 0 < s := by linarith
  set E : ℝ≥0∞ := eng 𝔭.tree s k F Tr q with hE
  set Cl : ℝ := lacL3Const 𝔭 q with hCl
  set M : ℝ := (𝔭.N : ℝ) / 2 with hM
  have hM1 : 1 < M := by
    have : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
    rw [hM]; linarith
  set D : ℝ := 𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ)) with hDdef
  have hDpos : 0 < D := by
    have : (0 : ℝ) < 𝔭.tree.C := by linarith
    rw [hDdef]; positivity
  have hCpos : 0 < 𝔭.C := by linarith
  have hK := cutK_pos hCpos
  have hβδ : 0 ≤ 𝔭.tree.β + 2 * 𝔭.tree.δ := by
    have := h𝔭t.2.2.2.1; linarith
  have hCs := tileSupConst_nonneg 𝔭.tree hq hβδ
  have hjb := jbConst_nonneg M
  have hClpos : 0 < Cl := by
    rw [hCl, lacL3Const]
    have : 0 ≤ cutK 𝔭 * D * tileSupConst 𝔭.tree q * (2 ^ M * jbConst M) := by positivity
    linarith
  by_cases hEtop : E = ⊤
  · rw [hEtop, ENNReal.mul_top (by simpa using hClpos)]; exact le_top
  · obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
    set y : ℝ := yNorm s (tmult (m R₀ k) F x) with hy
    have hy0 : 0 ≤ y := yNorm_nonneg' s _
    have hlc0 := layerCut_nonneg hη TA σ x
    -- step A
    have hA : yNorm s ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x) = layerCut η TA σ x * y := by
      have := yNorm_fun_const_mul hs0 ((layerCut η TA σ x : ℝ) : ℂ) (tmult (m R₀ k) F x)
      rw [Complex.norm_real, Real.norm_of_nonneg hlc0] at this
      exact this
    -- single tile bounds (real form)
    have hTile : ∀ R ∈ layer' TA σ, ‖cutoffPsi 𝔭.tree η' σ R.pos x‖ * y ≤ tileSupConst 𝔭.tree q * E.toReal := by
      intro R hR
      obtain ⟨hRT, hs'⟩ := mem_layer'_iff.1 hR
      have hb : R.box = R₀.box := hT.2.1 R hRT R₀ hR₀T (hs'.trans hs₀.symm)
      have hmR : m R k = m R₀ k := hd.cons R hRT R₀ hR₀T hb
      have h1 := single_tile_sup_le (𝔭 := 𝔭.tree) h𝔭t hη' (s := s) (q := q) hs hq (k := k) (F := F) hF hFb
        (Cs := Tr) (R := R) (hsub hRT) (ξ := t.2) (hT.1 R hRT).2 (m := m R k) ((hd.mult R hRT).tree) x
      rw [hs'] at h1
      rw [hmR] at h1
      have hfin : (ENNReal.ofReal (tileSupConst 𝔭.tree q) * E) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEtop
      have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCs] at this
    -- weights
    have hpt : ∀ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) * y ≤
        jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) * (D * (tileSupConst 𝔭.tree q * E.toReal)) := by
      intro R hR
      set a : ℝ := jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) with ha
      have hp : 0 < a := jb_pos _
      have hdom := norm_le_cutoffPsi (𝔭 := 𝔭.tree) hη' (by linarith) (N' := M) (A := 1) (by
        have : ((𝔭.N / 8 : ℕ) : ℝ) ≤ (𝔭.N : ℝ) / 8 := Nat.cast_div_le
        show ((𝔭.N / 8 : ℕ) : ℝ) ≤ M
        rw [hM]; have : (0 : ℝ) ≤ 𝔭.N := by positivity
        linarith) (by norm_num) (s := σ) (v := R.pos)
        (w := fun z => ((jb ((z - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) : ℝ) : ℂ)) (fun z => by
          rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos _).le _), one_mul]) x
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), one_mul] at hdom
      have e : a ^ (-(𝔭.N : ℝ)) = a ^ (-M) * a ^ (-M) := by
        rw [← Real.rpow_add hp]; congr 1; rw [hM]; ring
      have h2 := hTile R hR
      have hdom' : a ^ (-M) ≤ D * ‖cutoffPsi 𝔭.tree η' σ R.pos x‖ := by rw [hDdef]; exact hdom
      have h3 : a ^ (-M) * y ≤ D * (tileSupConst 𝔭.tree q * E.toReal) :=
        calc a ^ (-M) * y ≤ (D * ‖cutoffPsi 𝔭.tree η' σ R.pos x‖) * y := mul_le_mul_of_nonneg_right hdom' hy0
          _ = D * (‖cutoffPsi 𝔭.tree η' σ R.pos x‖ * y) := by ring
          _ ≤ D * (tileSupConst 𝔭.tree q * E.toReal) := mul_le_mul_of_nonneg_left h2 hDpos.le
      calc a ^ (-(𝔭.N : ℝ)) * y = a ^ (-M) * (a ^ (-M) * y) := by rw [e]; ring
        _ ≤ a ^ (-M) * (D * (tileSupConst 𝔭.tree q * E.toReal)) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hp.le _)
    -- the lattice sum
    have hsum : ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) ≤ 2 ^ M * jbConst M := by
      have hp2 := zpow_two_pos σ
      have := sum_layer'_eq_sum_keys (Tr := TA) hT.2.1 σ
        (fun v => jb ((x - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-M))
      rw [this]
      have e : ∀ v : ℤ, (x - dyCentre σ v) / (2 : ℝ) ^ σ = (x / (2 : ℝ) ^ σ - 1 / 2) - v := by
        intro v; unfold dyCentre; field_simp; ring
      simp_rw [e]
      exact sum_jb_le hM1 _ _
    -- assemble
    have hlc : layerCut η TA σ x ≤ cutK 𝔭 * ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) :=
      layerCut_le hη TA σ x
    have hmain : layerCut η TA σ x * y ≤ cutK 𝔭 * D * tileSupConst 𝔭.tree q * (2 ^ M * jbConst M) * E.toReal := by
      calc layerCut η TA σ x * y
          ≤ (cutK 𝔭 * ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ))) * y :=
            mul_le_mul_of_nonneg_right hlc hy0
        _ = cutK 𝔭 * ∑ R ∈ layer' TA σ, (jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) * y) := by
            rw [mul_assoc, Finset.sum_mul]
        _ ≤ cutK 𝔭 * ∑ R ∈ layer' TA σ, (jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) *
              (D * (tileSupConst 𝔭.tree q * E.toReal))) := by
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => hpt R hR) hK.le
        _ = cutK 𝔭 * ((∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M)) *
              (D * (tileSupConst 𝔭.tree q * E.toReal))) := by rw [← Finset.sum_mul]
        _ ≤ cutK 𝔭 * ((2 ^ M * jbConst M) * (D * (tileSupConst 𝔭.tree q * E.toReal))) := by
            have : 0 ≤ E.toReal := ENNReal.toReal_nonneg
            have h0 : 0 ≤ D * (tileSupConst 𝔭.tree q * E.toReal) := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum h0) hK.le
        _ = _ := by ring
    rw [hA]
    have hE0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
    calc ENNReal.ofReal (layerCut η TA σ x * y)
        ≤ ENNReal.ofReal (Cl * E.toReal) := by
          refine ENNReal.ofReal_le_ofReal (hmain.trans ?_)
          rw [hCl, lacL3Const]
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ cutK 𝔭 * D * tileSupConst 𝔭.tree q * (2 ^ M * jbConst M)) hE0]
      _ = ENNReal.ofReal Cl * E := by
          rw [ENNReal.ofReal_mul hClpos.le, ENNReal.ofReal_toReal hEtop]

/-! ## (S), `p = ∞`: the weighted single-scale sup bound -/

/-- The constant of the weighted sup bound with weight exponent `N_w` (`M = N_w - 𝔭.tree.N`). -/
def lacSConst (𝔭 : Params) (q Nw : ℝ) : ℝ :=
  (𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ))) * tileSupConst 𝔭.tree q *
    (2 ^ (Nw - (𝔭.tree.N : ℝ)) * jbConst (Nw - (𝔭.tree.N : ℝ))) + 1

/-- **(S) for `p = ∞`** (DPLMV `l:sscale`, weights `Σ_R ⟨(x - c_R)/2^σ⟩^{-N_w}`, `N_w > 𝔭.tree.N + 1`; `N_w = N/6` is the case of
the route check): `Σ_{R ∈ T(σ)} ⟨(x - c_R)/2^σ⟩^{-N_w} ‖T_{m_σ}F(x)‖_{L^s(Y)} ≤ C eng 𝔭.tree s k F Tr q`. -/
theorem lacunary_S_sup {𝔭 : Params} {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q)
    (h𝔭t : 𝔭.tree.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭.tree η') {η : ℝ → ℝ}
    {Tr TA : Finset TriTile} {t : Top} {k : Fin 3} {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}
    (hT : IsGoodTree TA t) (hsub : TA ⊆ Tr) (hd : LacData 𝔭 TA k η χ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Nw : ℝ} (hNw : (𝔭.tree.N : ℝ) + 1 < Nw) {σ : ℤ} {R₀ : TriTile}
    (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    ENNReal.ofReal (∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) *
        yNorm s (tmult (m R₀ k) F x)) ≤ ENNReal.ofReal (lacSConst 𝔭 q Nw) * eng 𝔭.tree s k F Tr q := by
  obtain ⟨hNt, hDt, hβt, hCt⟩ := h𝔭t.bounds
  have hs0 : 0 < s := by linarith
  set E : ℝ≥0∞ := eng 𝔭.tree s k F Tr q with hE
  set Cl : ℝ := lacSConst 𝔭 q Nw with hCl
  set M : ℝ := Nw - (𝔭.tree.N : ℝ) with hM
  have hM1 : 1 < M := by rw [hM]; linarith
  set D : ℝ := 𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ)) with hDdef
  have hDpos : 0 < D := by
    have : (0 : ℝ) < 𝔭.tree.C := by linarith
    rw [hDdef]; positivity
  have hβδ : 0 ≤ 𝔭.tree.β + 2 * 𝔭.tree.δ := by
    have := h𝔭t.2.2.2.1; linarith
  have hCs := tileSupConst_nonneg 𝔭.tree hq hβδ
  have hjb := jbConst_nonneg M
  have hClpos : 0 < Cl := by
    rw [hCl, lacSConst]
    have : 0 ≤ D * tileSupConst 𝔭.tree q * (2 ^ M * jbConst M) := by positivity
    linarith
  by_cases hEtop : E = ⊤
  · rw [hEtop, ENNReal.mul_top (by simpa using hClpos)]; exact le_top
  · obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
    set y : ℝ := yNorm s (tmult (m R₀ k) F x) with hy
    have hy0 : 0 ≤ y := yNorm_nonneg' s _
    have hTile : ∀ R ∈ layer' TA σ, ‖cutoffPsi 𝔭.tree η' σ R.pos x‖ * y ≤ tileSupConst 𝔭.tree q * E.toReal := by
      intro R hR
      obtain ⟨hRT, hs'⟩ := mem_layer'_iff.1 hR
      have hb : R.box = R₀.box := hT.2.1 R hRT R₀ hR₀T (hs'.trans hs₀.symm)
      have hmR : m R k = m R₀ k := hd.cons R hRT R₀ hR₀T hb
      have h1 := single_tile_sup_le (𝔭 := 𝔭.tree) h𝔭t hη' (s := s) (q := q) hs hq (k := k) (F := F) hF hFb
        (Cs := Tr) (R := R) (hsub hRT) (ξ := t.2) (hT.1 R hRT).2 (m := m R k) ((hd.mult R hRT).tree) x
      rw [hs'] at h1
      rw [hmR] at h1
      have hfin : (ENNReal.ofReal (tileSupConst 𝔭.tree q) * E) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEtop
      have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCs] at this
    have hpt : ∀ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * y ≤
        jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) * (D * (tileSupConst 𝔭.tree q * E.toReal)) := by
      intro R hR
      set a : ℝ := jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) with ha
      have hp : 0 < a := jb_pos _
      have hdom := norm_le_cutoffPsi (𝔭 := 𝔭.tree) hη' (by linarith) (N' := (𝔭.tree.N : ℝ)) (A := 1) le_rfl
        (by norm_num) (s := σ) (v := R.pos)
        (w := fun z => ((jb ((z - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.tree.N : ℝ)) : ℝ) : ℂ)) (fun z => by
          rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos _).le _), one_mul]) x
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), one_mul] at hdom
      have e : a ^ (-Nw) = a ^ (-M) * a ^ (-(𝔭.tree.N : ℝ)) := by
        rw [← Real.rpow_add hp]; congr 1; rw [hM]; ring
      have h2 := hTile R hR
      have hdom' : a ^ (-(𝔭.tree.N : ℝ)) ≤ D * ‖cutoffPsi 𝔭.tree η' σ R.pos x‖ := by rw [hDdef]; exact hdom
      have h3 : a ^ (-(𝔭.tree.N : ℝ)) * y ≤ D * (tileSupConst 𝔭.tree q * E.toReal) :=
        calc a ^ (-(𝔭.tree.N : ℝ)) * y ≤ (D * ‖cutoffPsi 𝔭.tree η' σ R.pos x‖) * y :=
              mul_le_mul_of_nonneg_right hdom' hy0
          _ = D * (‖cutoffPsi 𝔭.tree η' σ R.pos x‖ * y) := by ring
          _ ≤ D * (tileSupConst 𝔭.tree q * E.toReal) := mul_le_mul_of_nonneg_left h2 hDpos.le
      calc a ^ (-Nw) * y = a ^ (-M) * (a ^ (-(𝔭.tree.N : ℝ)) * y) := by rw [e]; ring
        _ ≤ a ^ (-M) * (D * (tileSupConst 𝔭.tree q * E.toReal)) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hp.le _)
    have hsum : ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) ≤ 2 ^ M * jbConst M := by
      have hp2 := zpow_two_pos σ
      have := sum_layer'_eq_sum_keys (Tr := TA) hT.2.1 σ
        (fun v => jb ((x - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-M))
      rw [this]
      have e : ∀ v : ℤ, (x - dyCentre σ v) / (2 : ℝ) ^ σ = (x / (2 : ℝ) ^ σ - 1 / 2) - v := by
        intro v; unfold dyCentre; field_simp; ring
      simp_rw [e]
      exact sum_jb_le hM1 _ _
    have hE0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
    have hmain : ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * y ≤
        D * tileSupConst 𝔭.tree q * (2 ^ M * jbConst M) * E.toReal := by
      calc ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * y
          ≤ ∑ R ∈ layer' TA σ, (jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M) *
              (D * (tileSupConst 𝔭.tree q * E.toReal))) := Finset.sum_le_sum fun R hR => hpt R hR
        _ = (∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-M)) *
              (D * (tileSupConst 𝔭.tree q * E.toReal)) := by rw [← Finset.sum_mul]
        _ ≤ (2 ^ M * jbConst M) * (D * (tileSupConst 𝔭.tree q * E.toReal)) := by
            have h0 : 0 ≤ D * (tileSupConst 𝔭.tree q * E.toReal) := by positivity
            exact mul_le_mul_of_nonneg_right hsum h0
        _ = _ := by ring
    rw [← Finset.sum_mul]
    calc ENNReal.ofReal ((∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw)) * y)
        ≤ ENNReal.ofReal (Cl * E.toReal) := by
          rw [Finset.sum_mul]
          refine ENNReal.ofReal_le_ofReal (hmain.trans ?_)
          rw [hCl, lacSConst]
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ D * tileSupConst 𝔭.tree q * (2 ^ M * jbConst M)) hE0]
      _ = ENNReal.ofReal Cl * E := by
          rw [ENNReal.ofReal_mul hClpos.le, ENNReal.ofReal_toReal hEtop]

/-! ## (S), `p = q`: the weighted single-scale `L^q(I₀)` bound -/

theorem continuous_jb_rpow (c L N : ℝ) : Continuous (fun x : ℝ => jb ((x - c) / L) ^ (-N)) :=
  Continuous.rpow_const (by unfold jb; fun_prop) (fun x => Or.inl (jb_pos _).ne')

/-- The constant of the `L^q(I₀)` bound. -/
def lacSqConst (𝔭 : Params) (Nw : ℝ) : ℝ :=
  ((3 : ℝ) / 2) ^ (Nw - (𝔭.tree.N : ℝ)) * (𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ))) *
    (2 ^ (Nw - (𝔭.tree.N : ℝ)) * jbConst (Nw - (𝔭.tree.N : ℝ))) + 1

/-- **(S) for `p = q`** (`1 ≤ q`; the route check's `‖w T_mF‖_{L^p}` is the norm over the `σ`-interval `I₀ = dyadicInt σ u`):
`‖1_{I₀} Σ_{R ∈ T(σ)} ⟨(x - c_R)/2^σ⟩^{-N_w} ‖T_{m_σ}F‖_{L^s(Y)}‖_{L^q} ≤ C |I₀|^{1/q} eng 𝔭.tree s k F Tr q`
(`N_w > 𝔭.tree.N + 1`).  Minkowski over the tiles, domination by `θ'_R` (D-2), the single-tile energy, and the lattice sum
over the distance `⟨u - pos_R⟩^{-M}` (D-3 in the form `⟨u - v⟩ ≤ (3/2)⟨a_R(x)⟩` for `x ∈ I₀`). -/
theorem lacunary_S_Lq {𝔭 : Params} {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ q)
    (h𝔭t : 𝔭.tree.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭.tree η') {η : ℝ → ℝ}
    {Tr TA : Finset TriTile} {t : Top} {k : Fin 3} {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}
    (hT : IsGoodTree TA t) (hsub : TA ⊆ Tr) (hd : LacData 𝔭 TA k η χ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    {Nw : ℝ} (hNw : (𝔭.tree.N : ℝ) + 1 < Nw) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (u : ℤ) :
    eLpNorm ((dyadicInt σ u).indicator (fun x => ∑ R ∈ layer' TA σ,
        jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * yNorm s (tmult (m R₀ k) F x)))
      (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (lacSqConst 𝔭 Nw) * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * eng 𝔭.tree s k F Tr q := by
  obtain ⟨hNt, hDt, hβt, hCt⟩ := h𝔭t.bounds
  have hs0 : 0 < s := by linarith
  obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
  set E : ℝ≥0∞ := eng 𝔭.tree s k F Tr q with hE
  set M : ℝ := Nw - (𝔭.tree.N : ℝ) with hM
  have hM1 : 1 < M := by rw [hM]; linarith
  set D : ℝ := 𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ)) with hDdef
  have hDpos : 0 < D := by
    have : (0 : ℝ) < 𝔭.tree.C := by linarith
    rw [hDdef]; positivity
  have hjb := jbConst_nonneg M
  have h32 : (0 : ℝ) < ((3 : ℝ) / 2) ^ M := Real.rpow_pos_of_pos (by norm_num) _
  set θ : TriTile → ℝ → ℂ := fun R => cutoffPsi 𝔭.tree η' σ R.pos with hθ
  set G : TriTile → ℝ → ℝ := fun R x => yNorm s (θ R x • tmult (m R₀ k) F x) with hG
  set cR : TriTile → ℝ := fun R => ((3 : ℝ) / 2) ^ M * D * jb ((u : ℝ) - R.pos) ^ (-M) with hcR
  have hcR0 : ∀ R, 0 ≤ cR R := fun R => by
    have := Real.rpow_nonneg (jb_pos ((u : ℝ) - R.pos)).le (-M)
    rw [hcR]; positivity
  have hG0 : ∀ R x, 0 ≤ G R x := fun R x => yNorm_nonneg' s _
  have hmult : ∀ R ∈ layer' TA σ, InMult 𝔭.tree R.box.scale (R.box.centre k) (m R₀ k) := by
    intro R hR
    obtain ⟨hRT, hs'⟩ := mem_layer'_iff.1 hR
    have hb : R.box = R₀.box := hT.2.1 R hRT R₀ hR₀T (hs'.trans hs₀.symm)
    have := (hd.mult R hRT).tree
    rwa [hd.cons R hRT R₀ hR₀T hb] at this
  have hψ : ∀ R ∈ layer' TA σ, InPsi 𝔭.tree R.box.scale R.pos (θ R) := by
    intro R hR
    obtain ⟨-, hs'⟩ := mem_layer'_iff.1 hR
    rw [hs']
    exact inPsi_cutoffPsi hη' (by linarith) (by omega) σ R.pos
  -- measurability
  have hTm : Measurable (tmult (m R₀ k) F) := measurable_tmult_psp (hd.mult R₀ hR₀T) hF
  have hy : Measurable fun x => yNorm s (tmult (m R₀ k) F x) := (measurable_yNorm_fun s).comp hTm
  have hfm : Measurable (fun x => ∑ R ∈ layer' TA σ,
      jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * yNorm s (tmult (m R₀ k) F x)) :=
    Finset.measurable_sum _ fun R _ => (continuous_jb_rpow _ _ _).measurable.mul hy
  have hGm : ∀ R ∈ layer' TA σ, Measurable (G R) := fun R hR =>
    (measurable_yNorm_fun s).comp (by
      have := measurable_psi_smul_tmult_psp (hψ R hR) (hmult R hR) hF
      exact this)
  -- the pointwise bound
  have hpt : ∀ x, (dyadicInt σ u).indicator (fun x => ∑ R ∈ layer' TA σ,
      jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * yNorm s (tmult (m R₀ k) F x)) x ≤
      ∑ R ∈ layer' TA σ, cR R * G R x := by
    intro x
    by_cases hx : x ∈ dyadicInt σ u
    · rw [Set.indicator_of_mem hx]
      refine Finset.sum_le_sum fun R hR => ?_
      set a : ℝ := jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) with ha
      have hp : 0 < a := jb_pos _
      have hy0 : 0 ≤ yNorm s (tmult (m R₀ k) F x) := yNorm_nonneg' s _
      have hp2 := zpow_two_pos σ
      -- `jb(u - pos) ≤ (3/2) a`
      have hnear : |((u : ℝ) - R.pos) - (x - dyCentre σ R.pos) / (2 : ℝ) ^ σ| ≤ 1 / 2 := by
        obtain ⟨h1, h2⟩ := hx
        have e : ((u : ℝ) - R.pos) - (x - dyCentre σ R.pos) / (2 : ℝ) ^ σ =
            (u : ℝ) + 1 / 2 - x / (2 : ℝ) ^ σ := by unfold dyCentre; field_simp; ring
        rw [e, abs_le]
        constructor
        · have : x / (2 : ℝ) ^ σ < (u : ℝ) + 1 := by rw [div_lt_iff₀ hp2]; linarith
          linarith
        · have : (u : ℝ) ≤ x / (2 : ℝ) ^ σ := by rw [le_div_iff₀ hp2]; linarith
          linarith
      have hj := jb_le_three_halves_mul (a := (u : ℝ) - R.pos) (u := (x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) hnear
      have hjp := jb_pos ((u : ℝ) - R.pos)
      have hM' : a ^ (-M) ≤ ((3 : ℝ) / 2) ^ M * jb ((u : ℝ) - R.pos) ^ (-M) := by
        have h2 : (2 / 3) * jb ((u : ℝ) - R.pos) ≤ a := by rw [ha]; linarith
        calc a ^ (-M) ≤ ((2 / 3) * jb ((u : ℝ) - R.pos)) ^ (-M) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
          _ = ((2 / 3 : ℝ)) ^ (-M) * jb ((u : ℝ) - R.pos) ^ (-M) := Real.mul_rpow (by norm_num) hjp.le
          _ = _ := by
              congr 1
              rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
              norm_num
      -- domination by `θ'`
      have hdom := norm_le_cutoffPsi (𝔭 := 𝔭.tree) hη' (by linarith) (N' := (𝔭.tree.N : ℝ)) (A := 1) le_rfl
        (by norm_num) (s := σ) (v := R.pos)
        (w := fun z => ((jb ((z - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.tree.N : ℝ)) : ℝ) : ℂ)) (fun z => by
          rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos _).le _), one_mul]) x
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), one_mul] at hdom
      have hdom' : a ^ (-(𝔭.tree.N : ℝ)) ≤ D * ‖θ R x‖ := by rw [hDdef]; exact hdom
      have e : a ^ (-Nw) = a ^ (-M) * a ^ (-(𝔭.tree.N : ℝ)) := by
        rw [← Real.rpow_add hp]; congr 1; rw [hM]; ring
      have hGR : G R x = ‖θ R x‖ * yNorm s (tmult (m R₀ k) F x) := yNorm_fun_const_mul hs0 _ _
      calc a ^ (-Nw) * yNorm s (tmult (m R₀ k) F x)
          = a ^ (-M) * (a ^ (-(𝔭.tree.N : ℝ)) * yNorm s (tmult (m R₀ k) F x)) := by rw [e]; ring
        _ ≤ (((3 : ℝ) / 2) ^ M * jb ((u : ℝ) - R.pos) ^ (-M)) *
            ((D * ‖θ R x‖) * yNorm s (tmult (m R₀ k) F x)) :=
          mul_le_mul hM' (mul_le_mul_of_nonneg_right hdom' hy0) (by positivity) (by positivity)
        _ = cR R * G R x := by rw [hcR, hGR]; ring
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg fun R _ => mul_nonneg (hcR0 R) (hG0 R x)
  -- Minkowski
  have hq0 : 1 ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hEG : ∀ R ∈ layer' TA σ, eLpNorm (G R) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * E := by
    intro R hR
    obtain ⟨hRT, hs'⟩ := mem_layer'_iff.1 hR
    have h1 := single_tile_le_eng (𝔭 := 𝔭.tree) (s := s) (q := q) (k := k) (F := F) (Cs := Tr) (R := R)
      (hsub hRT) (ξ := t.2) (hT.1 R hRT).2 (hψ R hR) (hmult R hR)
    rw [hs'] at h1
    have ha : 0 < ((2 : ℝ) ^ σ) ^ (-1 / q) := Real.rpow_pos_of_pos (zpow_two_pos σ) _
    have e : ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (-1 / q)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (zpow_two_pos σ).le _), ← Real.rpow_add (zpow_two_pos σ)]
      have : 1 / q + -1 / q = 0 := by ring
      rw [this, Real.rpow_zero, ENNReal.ofReal_one]
    calc eLpNorm (G R) (ENNReal.ofReal q) volume
        = ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (-1 / q)) *
            eLpNorm (G R) (ENNReal.ofReal q) volume) := by rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h1
  have hsumeq : (fun x => ∑ R ∈ layer' TA σ, cR R * G R x) = ∑ R ∈ layer' TA σ, (fun x => cR R * G R x) := by
    funext x; simp [Finset.sum_apply]
  have hmk : ∀ R ∈ layer' TA σ, eLpNorm (fun x => cR R * G R x) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (cR R) * (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * E) := by
    intro R hR
    have := eLpNorm_const_smul (μ := volume) (p := ENNReal.ofReal q) (c := cR R) (f := G R)
    simp only [Real.enorm_eq_ofReal (hcR0 R)] at this
    have e : (fun x => cR R * G R x) = cR R • G R := by funext x; simp [smul_eq_mul]
    rw [e, this]
    exact mul_le_mul' le_rfl (hEG R hR)
  -- the lattice sum
  have hsum : ∑ R ∈ layer' TA σ, cR R ≤ ((3 : ℝ) / 2) ^ M * D * (2 ^ M * jbConst M) := by
    have hcs : ∑ R ∈ layer' TA σ, cR R = ((3 : ℝ) / 2) ^ M * D * ∑ R ∈ layer' TA σ, jb ((u : ℝ) - R.pos) ^ (-M) := by
      rw [Finset.mul_sum]
    rw [hcs]
    have := sum_layer'_eq_sum_keys (Tr := TA) hT.2.1 σ (fun v => jb ((u : ℝ) - v) ^ (-M))
    rw [this]
    exact mul_le_mul_of_nonneg_left (sum_jb_le hM1 _ _) (by positivity)
  have hmeasf : AEStronglyMeasurable ((dyadicInt σ u).indicator (fun x => ∑ R ∈ layer' TA σ,
      jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * yNorm s (tmult (m R₀ k) F x))) volume :=
    (hfm.indicator (measurableSet_dyadicInt σ u)).aestronglyMeasurable
  have hnn : ∀ x, 0 ≤ (dyadicInt σ u).indicator (fun x => ∑ R ∈ layer' TA σ,
      jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * yNorm s (tmult (m R₀ k) F x)) x := by
    intro x
    by_cases hx : x ∈ dyadicInt σ u
    · rw [Set.indicator_of_mem hx]
      exact Finset.sum_nonneg fun R _ => mul_nonneg (Real.rpow_nonneg (jb_pos _).le _) (yNorm_nonneg' s _)
    · rw [Set.indicator_of_notMem hx]
  have hmono : eLpNorm ((dyadicInt σ u).indicator (fun x => ∑ R ∈ layer' TA σ,
      jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-Nw) * yNorm s (tmult (m R₀ k) F x))) (ENNReal.ofReal q) volume ≤
      eLpNorm (fun x => ∑ R ∈ layer' TA σ, cR R * G R x) (ENNReal.ofReal q) volume :=
    eLpNorm_mono_real hmeasf (fun x => by rw [Real.norm_of_nonneg (hnn x)]; exact hpt x)
  refine hmono.trans ?_
  calc eLpNorm (fun x => ∑ R ∈ layer' TA σ, cR R * G R x) (ENNReal.ofReal q) volume
    _ ≤ ∑ R ∈ layer' TA σ, eLpNorm (fun x => cR R * G R x) (ENNReal.ofReal q) volume := by
        rw [hsumeq]; exact eLpNorm_sum_le hq0
    _ ≤ ∑ R ∈ layer' TA σ, ENNReal.ofReal (cR R) * (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * E) :=
        Finset.sum_le_sum hmk
    _ = ENNReal.ofReal (∑ R ∈ layer' TA σ, cR R) * (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * E) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun R _ => hcR0 R)]
    _ ≤ ENNReal.ofReal (lacSqConst 𝔭 Nw) * (ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) * E) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (hsum.trans ?_)) le_rfl
        rw [lacSqConst]; linarith
    _ = _ := by ring

end PrimeBHT.TimeFrequency.X2
