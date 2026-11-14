module

public import PrimeBHT.TimeFrequency.X2.FourierSupport
public import PrimeBHT.TimeFrequency.X2.Psp.Defs
public import PrimeBHT.TimeFrequency.X2.Psp.Split
public import PrimeBHT.TimeFrequency.X2.Psp.Domination

/-!
# X2, V13 part 2 (A): the lacunary projections (L1), (L2), (L4)

`docs/audits/X2-V13-route-check.md` §1.2 (L), §2.5.  For a part `T_A` of a good tree (`k` lacunary at every box of `T_A`),
`G = treeOp T_A χ (m · k) F`:

* `lacunary_L1`: `‖G‖_{L^q(L^s)}` is a tree-operator norm, hence `≤ |I_t|^{1/q} eng` (definition + `topNorm_le_eng`);
* `lacunary_layer_proj` (L2): `T_{lacSym(θ_k, σ)} G = χ̃_σ · T_{m_σ} F` pointwise, for every tree scale `σ` of `T_A`;
* `lacunary_L4` (L4, `s = 2`): `Σ_σ ‖χ̃_σ T_{m_σ} F‖²_{L²(H)} = ‖G‖²_{L²(H)}`.

The single-scale bounds (L3), (S) are in `X2/Psp/LacunaryLinf.lean` (`lacunary_L3`, `lacunary_S_sup`, `lacunary_S_Lq`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Linearity of `tm` -/

theorem integrable_kernel_mul_fourierInv {n : ℝ → ℂ} (hn : Continuous n) {c r : ℝ} (hs : ∀ ξ, r < |ξ - c| → n ξ = 0)
    {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) : Integrable (fun z => 𝓕⁻ n (x - z) * g z) := by
  have hKc : Continuous (𝓕⁻ n) := continuous_fourierInv_of_integrable' (integrable_of_far hn hs)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w, ‖𝓕⁻ n w‖ ≤ M :=
    ⟨∫ ξ, ‖n ξ‖, fun w => by
      rw [Real.fourierInv_eq_fourier_neg]; exact Real.norm_fourier_le_integral_norm _ _⟩
  exact hg.bdd_mul (c := M) ((hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => hM _)

theorem tm_finsetSum {ι : Type*} (I : Finset ι) {n : ℝ → ℂ} (hn : Continuous n) {c r : ℝ}
    (hs : ∀ ξ, r < |ξ - c| → n ξ = 0) (g : ι → ℝ → ℂ) (hg : ∀ i ∈ I, Integrable (g i)) (x : ℝ) :
    tm n (fun z => ∑ i ∈ I, g i z) x = ∑ i ∈ I, tm n (g i) x := by
  unfold tm
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ fun i hi => integrable_kernel_mul_fourierInv hn hs (hg i hi) x

/-! ## Coordinates of the tree operator -/

theorem treeOp_apply_coord {P : ℕ} (Tr : Finset TriTile) (ψ m : TriTile → ℝ → ℂ) (F : ℝ → ZMod P → ℂ) (x : ℝ)
    (y : ZMod P) :
    treeOp Tr ψ m F x y = ∑ R ∈ Tr, gfun (ψ R) (m R) (fun z => F z y) x := by
  unfold treeOp
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun R _ => ?_
  simp [gfun, tmult_apply_eq_tm]

/-! ## The data of a lacunary part -/

/-- The data of a part `T_A` for the lacunary projection: the cutoffs `χ_R = 1_{I_R} * η_s` in `Ψ_{I_R}(𝔭)`, the slot-`k`
multipliers in `M_{ω_{R,k}}(𝔭)`, constant on the boxes (all consequences of `IsModelData`). -/
structure LacData (𝔭 : Params) (TA : Finset TriTile) (k : Fin 3) (η : ℝ → ℝ) (χ : TriTile → ℝ → ℝ)
    (m : TriTile → Fin 3 → ℝ → ℂ) : Prop where
  psi : ∀ R ∈ TA, InPsi 𝔭 R.box.scale R.pos (fun x => (χ R x : ℂ))
  mult : ∀ R ∈ TA, InMult 𝔭 R.box.scale (R.box.centre k) (m R k)
  cons : ∀ R ∈ TA, ∀ R' ∈ TA, R.box = R'.box → m R k = m R' k
  cut : ∀ R ∈ TA, χ R = tileCutoff η R.box.scale R.pos

theorem IsModelData.lacData {𝔭 : Params} {Tr TA : Finset TriTile} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (h : IsModelData 𝔭 Tr χ m) (hsub : TA ⊆ Tr) (k : Fin 3) :
    ∃ η, IsEtaCut 𝔭 η ∧ LacData 𝔭 TA k η χ m := by
  obtain ⟨h1, h2, η, hη, h3⟩ := h
  exact ⟨η, hη, ⟨fun R hR => (h1 R (hsub hR)).1.1, fun R hR => (h1 R (hsub hR)).2 k,
    fun R hR R' hR' hb => by rw [h2 R (hsub hR) R' (hsub hR') hb], fun R hR => h3 R (hsub hR)⟩⟩

theorem not_isOvSlot_of_mem_treePart {Tr : Finset TriTile} {t : Top} {A : Finset (Fin 3)} {k : Fin 3} (hk : k ∈ A)
    {R : TriTile} (hR : R ∈ treePart Tr t A) : ¬ IsOvSlot t k R.box :=
  mem_slotType.1 ((mem_treePart.1 hR).2 ▸ hk)

/-! ## The layers are band-limited -/

section Layers

variable {𝔭 : Params} {J : ℕ} {Qs : Set Box} {TA : Finset TriTile} {t : Top} {k : Fin 3} {η : ℝ → ℝ}
  {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}

/-- The Fourier support of the layer of scale `σ`: `[c - (β/2 + δ) 2^{-σ}, c + (β/2 + δ) 2^{-σ}]`, `c = c_k` of the box. -/
def layerSupp (𝔭 : Params) (c : ℝ) (σ : ℤ) : Set ℝ :=
  Icc (c - (𝔭.β / 2 + 𝔭.δ) * (2 : ℝ) ^ (-σ)) (c + (𝔭.β / 2 + 𝔭.δ) * (2 : ℝ) ^ (-σ))

/-- The layer `Σ_{R ∈ T(σ)} χ_R T_{m_R} f` is band-limited with Fourier support `layerSupp` (all tiles of one scale of a good
tree share one box). -/
theorem layer_bandLimited (h𝔭 : 𝔭.Admissible) (hT : IsGoodTree TA t) (hd : LacData 𝔭 TA k η χ m) {σ : ℤ}
    {R' : TriTile} (hR' : R' ∈ layer' TA σ) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    IsBandLimited (fun x => ∑ R ∈ layer' TA σ, gfun (fun x => (χ R x : ℂ)) (m R k) f x)
      (layerSupp 𝔭 (R'.box.centre k) σ) := by
  obtain ⟨hN, hD, hβ, -⟩ := h𝔭.bounds
  obtain ⟨hR'T, hs'⟩ := mem_layer'_iff.1 hR'
  refine IsBandLimited.sum (layer' TA σ) (Metric.isBounded_Icc _ _) fun R hR => ?_
  obtain ⟨hRT, hs⟩ := mem_layer'_iff.1 hR
  have hb : R.box = R'.box := hT.2.1 R hRT R' hR'T (hs.trans hs'.symm)
  have := isBandLimited_gfun (by omega) (by omega) (by linarith) (hd.psi R hRT) (hd.mult R hRT) hf hB
  have e1 : R.box.centre k = R'.box.centre k := by rw [hb]
  rw [e1, hs] at this
  exact this

theorem layer_eq_layerCut_mul (hT : IsGoodTree TA t) (hd : LacData 𝔭 TA k η χ m) {σ : ℤ} {R₀ : TriTile}
    (hR₀ : R₀ ∈ layer' TA σ) (f : ℝ → ℂ) (x : ℝ) :
    ∑ R ∈ layer' TA σ, gfun (fun x => (χ R x : ℂ)) (m R k) f x =
      (layerCut η TA σ x : ℂ) * tm (m R₀ k) f x := by
  obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
  have h1 : ∀ R ∈ layer' TA σ, gfun (fun x => (χ R x : ℂ)) (m R k) f x = (χ R x : ℂ) * tm (m R₀ k) f x := by
    intro R hR
    obtain ⟨hRT, hs⟩ := mem_layer'_iff.1 hR
    have hb : R.box = R₀.box := hT.2.1 R hRT R₀ hR₀T (hs.trans hs₀.symm)
    simp only [gfun]
    rw [hd.cons R hRT R₀ hR₀T hb]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  congr 1
  have := sum_layer'_cutoff_eq_layerCut (η := η) (χ := χ) (Tr := TA) hd.cut σ x
  rw [← this]
  push_cast
  rfl

/-- **(L2)** the lacunary projection: for a tree scale `σ` of the lacunary part `T_A` (`k` lacunary at every box of `T_A`),
`T_{lacSym(θ_k, σ)} G = χ̃_σ · T_{m_σ} F` pointwise, where `G = treeOp T_A χ (m · k) F`, `θ_k = ξ_T f_k`,
`χ̃_σ = layerCut`, `m_σ = m R₀ k` for any tile `R₀` of scale `σ`.  (FS-1 `tm_eq_self`/`tm_eq_zero` + S-3.) -/
theorem lacunary_layer_proj {P : ℕ} [NeZero P] (h𝔭 : 𝔭.Admissible) (hJ : jFloor ≤ J) (hQ : IsRankOne J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) (hT : IsGoodTree TA t) (hlac : ∀ R ∈ TA, ¬ IsOvSlot t k R.box)
    (hd : LacData 𝔭 TA k η χ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B)
    {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    tmult (lacSym (t.2 * freqDir k) σ) (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F) x =
      (layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x := by
  obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
  subst hs₀
  funext y
  obtain ⟨B, hB⟩ := hFb
  set f : ℝ → ℂ := fun z => F z y with hfdef
  have hf : Measurable f := (measurable_pi_apply y).comp hF
  have hfB : ∀ z, ‖f z‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z =>
    (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
      (mul_le_mul_of_nonneg_left (hB z) (by positivity))
  set θ : ℝ := t.2 * freqDir k with hθ
  have hn : Continuous (lacSym θ R₀.box.scale) := (contDiff_lacSym θ _).continuous
  have hs : ∀ ξ, lacHi0 * (2 : ℝ) ^ (-R₀.box.scale) < |ξ - θ| → lacSym θ R₀.box.scale ξ = 0 :=
    fun ξ h => lacSym_eq_zero_of_ge h.le
  -- the coordinate function of `G` as a sum over the layers
  have hcoord : (fun z => treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F z y) =
      fun z => ∑ σ' ∈ treeScales TA, ∑ R ∈ layer' TA σ', gfun (fun x => (χ R x : ℂ)) (m R k) f z := by
    funext z
    rw [treeOp_apply_coord]
    exact (Finset.sum_fiberwise_of_maps_to (s := TA) (t := treeScales TA) (g := fun R => R.box.scale)
      (fun R hR => mem_treeScales_iff.2 ⟨R, hR, rfl⟩) (fun R => gfun (fun x => (χ R x : ℂ)) (m R k) f z)).symm
  have hlayer : ∀ σ' ∈ treeScales TA, ∃ R' ∈ layer' TA σ',
      IsBandLimited (fun z => ∑ R ∈ layer' TA σ', gfun (fun x => (χ R x : ℂ)) (m R k) f z)
        (layerSupp 𝔭 (R'.box.centre k) σ') := by
    intro σ' hσ'
    obtain ⟨R', hR'T, hs'⟩ := mem_treeScales_iff.1 hσ'
    have hR' : R' ∈ layer' TA σ' := mem_layer'_iff.2 ⟨hR'T, hs'⟩
    exact ⟨R', hR', layer_bandLimited h𝔭 hT hd hR' hf hfB⟩
  show tm (lacSym θ R₀.box.scale) (fun z => treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F z y) x = _
  rw [hcoord, tm_finsetSum (treeScales TA) hn hs _ (fun σ' hσ' => (hlayer σ' hσ').choose_spec.2.integrable) x]
  have hσmem : R₀.box.scale ∈ treeScales TA := mem_treeScales_iff.2 ⟨R₀, hR₀T, rfl⟩
  rw [Finset.sum_eq_single R₀.box.scale]
  · -- the term `σ' = σ`
    have hbl := layer_bandLimited h𝔭 hT hd hR₀ hf hfB
    rw [hbl.tm_eq_self hn hs (fun ξ hξ => lacSym_eq_one_of_piece hQ (hbox R₀ hR₀T) (hT.1 R₀ hR₀T).2
      (hlac R₀ hR₀T) h𝔭 (by
        have hh := hξ
        unfold layerSupp at hh
        rw [mem_Icc] at hh
        rw [abs_le]
        constructor <;> linarith [hh.1, hh.2]))]
    beta_reduce
    rw [layer_eq_layerCut_mul hT hd hR₀ f x]
    rfl
  · intro σ' hσ' hne
    obtain ⟨R'', hR''l, hbl''⟩ := hlayer σ' hσ'
    obtain ⟨hR''T, hs''⟩ := mem_layer'_iff.1 hR''l
    refine hbl''.tm_eq_zero hn hs (fun ξ hξ => ?_) x
    have hone : lacSym θ R''.box.scale ξ = 1 := by
      refine lacSym_eq_one_of_piece hQ (hbox R'' hR''T) (hT.1 R'' hR''T).2 (hlac R'' hR''T) h𝔭 ?_
      have hh := hξ
      unfold layerSupp at hh
      rw [mem_Icc] at hh
      rw [abs_le, hs'']
      constructor <;> linarith [hh.1, hh.2]
    rcases lacSym_disjoint_scales hJ hQ (hbox R₀ hR₀T) (hbox R'' hR''T) (by rw [hs'']; exact fun h => hne h.symm) θ ξ
      with h | h
    · exact h
    · rw [hone] at h; exact absurd h one_ne_zero
  · intro h; exact absurd hσmem h

/-! ## (L1) -/

theorem InPsi.tree {𝔭 : Params} {s v : ℤ} {ψ : ℝ → ℂ} (h : InPsi 𝔭 s v ψ) : InPsi 𝔭.tree s v ψ := by
  refine ⟨h.1, fun x => (h.2.1 x).trans ?_, h.2.2⟩
  show _ ≤ 𝔭.C * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-((𝔭.N / 8 : ℕ) : ℝ))
  have hC : 0 ≤ 𝔭.C := by
    have h1 := (norm_nonneg _).trans (h.2.1 (dyCentre s v))
    have hp : 0 < jb ((dyCentre s v - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) :=
      Real.rpow_pos_of_pos (jb_pos _) _
    exact (mul_nonneg_iff_of_pos_right hp).1 h1
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (one_le_jb _) ?_) hC
  have : ((𝔭.N / 8 : ℕ) : ℝ) ≤ 𝔭.N := by exact_mod_cast Nat.div_le_self _ _
  linarith

theorem InMult.tree {𝔭 : Params} {s : ℤ} {c : ℝ} {m : ℝ → ℂ} (h : InMult 𝔭 s c m) : InMult 𝔭.tree s c m := h

theorem LacData.tree {𝔭 : Params} {TA : Finset TriTile} {k : Fin 3} {η : ℝ → ℝ} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (hd : LacData 𝔭 TA k η χ m) :
    IsTreeOpData 𝔭.tree k TA (fun R x => (χ R x : ℂ)) (fun R => m R k) :=
  ⟨fun R hR => ⟨(hd.psi R hR).tree, (hd.mult R hR).tree⟩, fun R hR R' hR' hb => hd.cons R hR R' hR' hb⟩

/-- **(L1)**: the normalized `L^q(L^s)` norm of the tree operator of the lacunary part is `≤ eng` (definition of the energy;
`topNorm_le_eng`): `|I_t|^{-1/q} ‖G‖_{L^q(L^s)} ≤ eng 𝔭 s k F Cs q` for every sub-collection `TA ⊆ Cs` that is a tree with top
`t` and `k`-lacunary and every tree-operator datum of the class `𝔭`. -/
theorem lacunary_L1 {𝔭 : Params} {P : ℕ} [NeZero P] {s q : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    {Cs TA : Finset TriTile} {t : Top} (hsub : TA ⊆ Cs) (hT : IsTree TA t) (hlac : IsLacunary k TA)
    {ψ m' : TriTile → ℝ → ℂ} (hdata : IsTreeOpData 𝔭 k TA ψ m') :
    treeOpNorm s q TA t ψ m' F ≤ eng 𝔭 s k F Cs q :=
  (le_topNorm hdata).trans (topNorm_le_eng hsub hT hlac)

/-! ## (L4) -/

theorem yNorm_two_sq {P : ℕ} [NeZero P] (F : ZMod P → ℂ) :
    yNorm 2 F ^ 2 = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ 2 := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  have e : ∀ y, ‖F y‖ ^ (2 : ℝ) = ‖F y‖ ^ 2 := fun y => by rw [Real.rpow_two]
  simp_rw [e]
  have h0 : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ 2 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem lacSym_eq_one_on_layerSupp (h𝔭 : 𝔭.Admissible) (hQ : IsRankOne J Qs) (hbox : ∀ R ∈ TA, R.box ∈ Qs)
    (hT : IsGoodTree TA t) (hlac : ∀ R ∈ TA, ¬ IsOvSlot t k R.box) {σ : ℤ} {R' : TriTile}
    (hR' : R' ∈ layer' TA σ) {ξ : ℝ} (hξ : ξ ∈ layerSupp 𝔭 (R'.box.centre k) σ) :
    lacSym (t.2 * freqDir k) σ ξ = 1 := by
  obtain ⟨hR'T, hs'⟩ := mem_layer'_iff.1 hR'
  subst hs'
  refine lacSym_eq_one_of_piece hQ (hbox R' hR'T) (hT.1 R' hR'T).2 (hlac R' hR'T) h𝔭 ?_
  have hh := hξ
  unfold layerSupp at hh
  rw [mem_Icc] at hh
  rw [abs_le]
  constructor <;> linarith [hh.1, hh.2]

theorem disjoint_layerSupp (h𝔭 : 𝔭.Admissible) (hJ : jFloor ≤ J) (hQ : IsRankOne J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) (hT : IsGoodTree TA t) (hlac : ∀ R ∈ TA, ¬ IsOvSlot t k R.box) {σ σ' : ℤ}
    (hne : σ ≠ σ') {R' R'' : TriTile} (hR' : R' ∈ layer' TA σ) (hR'' : R'' ∈ layer' TA σ') :
    Disjoint (layerSupp 𝔭 (R'.box.centre k) σ) (layerSupp 𝔭 (R''.box.centre k) σ') := by
  rw [Set.disjoint_left]
  intro ξ h1 h2
  have e1 := lacSym_eq_one_on_layerSupp h𝔭 hQ hbox hT hlac hR' h1
  have e2 := lacSym_eq_one_on_layerSupp h𝔭 hQ hbox hT hlac hR'' h2
  obtain ⟨hR'T, hs'⟩ := mem_layer'_iff.1 hR'
  obtain ⟨hR''T, hs''⟩ := mem_layer'_iff.1 hR''
  rcases lacSym_disjoint_scales hJ hQ (hbox R' hR'T) (hbox R'' hR''T) (by rw [hs', hs'']; exact hne)
    (t.2 * freqDir k) ξ with h | h
  · rw [hs'] at h; rw [e1] at h; exact one_ne_zero h
  · rw [hs''] at h; rw [e2] at h; exact one_ne_zero h

/-- **(L4)** (`s = 2`): `Σ_σ ‖treeOp (T(σ)) F‖²_{L²(H)} = ‖treeOp T_A F‖²_{L²(H)}` — the layers of the lacunary part are
orthogonal (disjoint Fourier supports, FS-1 `integral_norm_sq_sum`). -/
theorem lacunary_L4 {P : ℕ} [NeZero P] (h𝔭 : 𝔭.Admissible) (hJ : jFloor ≤ J) (hQ : IsRankOne J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) (hT : IsGoodTree TA t) (hlac : ∀ R ∈ TA, ¬ IsOvSlot t k R.box)
    (hd : LacData 𝔭 TA k η χ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) :
    ∑ σ ∈ treeScales TA, ∫ x, yNorm 2 (treeOp (layer' TA σ) (fun R x => (χ R x : ℂ)) (fun R => m R k) F x) ^ 2 =
      ∫ x, yNorm 2 (treeOp TA (fun R x => (χ R x : ℂ)) (fun R => m R k) F x) ^ 2 := by
  obtain ⟨B, hB⟩ := hFb
  set ψ : TriTile → ℝ → ℂ := fun R x => (χ R x : ℂ) with hψ
  set m' : TriTile → ℝ → ℂ := fun R => m R k with hm'
  have hlayer : ∀ y : ZMod P, ∀ σ' ∈ treeScales TA, ∃ R' ∈ layer' TA σ',
      IsBandLimited (fun z => treeOp (layer' TA σ') ψ m' F z y) (layerSupp 𝔭 (R'.box.centre k) σ') := by
    intro y σ' hσ'
    obtain ⟨R', hR'T, hs'⟩ := mem_treeScales_iff.1 hσ'
    have hR' : R' ∈ layer' TA σ' := mem_layer'_iff.2 ⟨hR'T, hs'⟩
    have hf : Measurable (fun z => F z y) := (measurable_pi_apply y).comp hF
    have hfB : ∀ z, ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z =>
      (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
        (mul_le_mul_of_nonneg_left (hB z) (by positivity))
    have := layer_bandLimited h𝔭 hT hd hR' hf hfB
    refine ⟨R', hR', ?_⟩
    have e : (fun z => treeOp (layer' TA σ') ψ m' F z y) =
        fun z => ∑ R ∈ layer' TA σ', gfun (fun x => (χ R x : ℂ)) (m R k) (fun z => F z y) z := by
      funext z; exact treeOp_apply_coord _ _ _ _ _ _
    rw [e]; exact this
  have hcoord : ∀ y z, treeOp TA ψ m' F z y = ∑ σ' ∈ treeScales TA, treeOp (layer' TA σ') ψ m' F z y := by
    intro y z
    rw [treeOp_apply_coord]
    simp_rw [treeOp_apply_coord]
    exact (Finset.sum_fiberwise_of_maps_to (s := TA) (t := treeScales TA) (g := fun R => R.box.scale)
      (fun R hR => mem_treeScales_iff.2 ⟨R, hR, rfl⟩)
      (fun R => gfun (ψ R) (m' R) (fun z => F z y) z)).symm
  have hkey : ∀ y : ZMod P, ∫ x, ‖treeOp TA ψ m' F x y‖ ^ 2 =
      ∑ σ ∈ treeScales TA, ∫ x, ‖treeOp (layer' TA σ) ψ m' F x y‖ ^ 2 := by
    intro y
    let S : ℤ → Set ℝ := fun σ => if h : σ ∈ treeScales TA then
      layerSupp 𝔭 ((hlayer y σ h).choose.box.centre k) σ else ∅
    have hbl : ∀ σ ∈ treeScales TA, IsBandLimited (fun z => treeOp (layer' TA σ) ψ m' F z y) (S σ) := by
      intro σ hσ
      simp only [S, dite_eq_left hσ]
      exact (hlayer y σ hσ).choose_spec.2
    have := IsBandLimited.integral_norm_sq_sum (treeScales TA) hbl (fun σ hσ σ' hσ' hne => by
      simp only [S, dite_eq_left hσ, dite_eq_left hσ']
      exact disjoint_layerSupp h𝔭 hJ hQ hbox hT hlac hne (hlayer y σ hσ).choose_spec.1
        (hlayer y σ' hσ').choose_spec.1)
    simp_rw [← hcoord y] at this
    exact this
  have hint_layer : ∀ (σ : ℤ), σ ∈ treeScales TA → ∀ y : ZMod P,
      Integrable (fun x => ‖treeOp (layer' TA σ) ψ m' F x y‖ ^ 2) := fun σ hσ y =>
    (hlayer y σ hσ).choose_spec.2.integrable_norm_sq
  have hint_G : ∀ y : ZMod P, Integrable (fun x => ‖treeOp TA ψ m' F x y‖ ^ 2) := by
    intro y
    have hb : ∀ σ ∈ treeScales TA, ∃ S, IsBandLimited (fun z => treeOp (layer' TA σ) ψ m' F z y) S :=
      fun σ hσ => ⟨_, (hlayer y σ hσ).choose_spec.2⟩
    choose Sf hSf using hb
    have := IsBandLimited.integrable_norm_sq (IsBandLimited.sum_biUnion (treeScales TA)
      (g := fun σ z => treeOp (layer' TA σ) ψ m' F z y)
      (S := fun σ => if h : σ ∈ treeScales TA then Sf σ h else ∅) (fun σ hσ => by
        simp only [dite_eq_left hσ]; exact hSf σ hσ))
    simp_rw [← hcoord y] at this
    exact this
  -- assemble over `y`
  have hL : ∀ σ ∈ treeScales TA, ∫ x, yNorm 2 (treeOp (layer' TA σ) ψ m' F x) ^ 2 =
      (P : ℝ)⁻¹ * ∑ y, ∫ x, ‖treeOp (layer' TA σ) ψ m' F x y‖ ^ 2 := by
    intro σ hσ
    simp_rw [yNorm_two_sq]
    rw [integral_const_mul, integral_finsetSum _ (fun y _ => hint_layer σ hσ y)]
  have hR : ∫ x, yNorm 2 (treeOp TA ψ m' F x) ^ 2 = (P : ℝ)⁻¹ * ∑ y, ∫ x, ‖treeOp TA ψ m' F x y‖ ^ 2 := by
    simp_rw [yNorm_two_sq]
    rw [integral_const_mul, integral_finsetSum _ (fun y _ => hint_G y)]
  rw [Finset.sum_congr rfl hL, hR, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun y _ => (hkey y).symm

end Layers

end PrimeBHT.TimeFrequency.X2
