module

public import PrimeBHT.TimeFrequency.X1.RealLine.ModelSum.Packet
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.DilAvgC
public import PrimeBHT.Frozen.TriValid
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.FreqNum
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.TimeFrequency.Interp.Hull.ModelForm
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The model-sum representation of `∑_s B_{2^s}(g_s, f₁, f₂)` (blueprint node R4 (d), `docs/x1-blueprint.md`)

## Final shape (the statements other files may use)

Notation: `ν = (a, b, s', α) ∈ ℤ⁴`, `𝒩 = nuSet = [21,30] × [-6,3] × [0,9] × [0,2]` (`3000` elements, `card_nuSet`),
`n ∈ ℤ²`, a tile `t = (s, v, ℓ) ∈ ℤ³`; `ψ^{(s)}_{v,ℓ} = scaledPacket ρ s v ℓ` (`2^{-s/2} ψ_{v,ℓ}(2^{-s} ·)`).

* `modelWeight M N n = (1 + |n₁| + |n₂|)^{-(M - 2 - 2N)}` (`w_n`).
* `modelPacket ρ M N g ν n t : Fin 3 → ℝ → ℂ` (the three packets `φ^n_{t,k}`, slots `k = 0, 1, 2` = blueprint's `1, 2, 3`):
  `(1+|n|)^{-N} ψ^{(s)}_{v+n₁,ℓ}`, `(1+|n|)^{-N} ψ^{(s)}_{v+n₂,ℓ-a}`,
  `(1+|n|)^{M-2} c_{n,v,ℓ,a,b}[g_s] ψ^{(s)}_{v,2ℓ-a-b}` with `c_{n,v,ℓ,a,b}[g_s] = coeffRep ρ (g s) a b n₁ n₂ v ℓ`.
* `modelTerm φ f₁ f₂ x t = |I_t|^{-1/2} ⟨f₁, φ_{t,0}⟩ ⟨f₂, φ_{t,1}⟩ φ_{t,2}(x)`, `|I_t|^{-1/2} = tileWeight t`
  (frozen `timeInt`, frozen `pairing`; `tileWeight`, `modelOp` are those of `Interp/Hull/ModelForm.lean`:
  `modelOp P φ f₁ f₂ x = ∑_{t ∈ P} modelTerm φ f₁ f₂ x t`, `modelOp_apply`, is `Π_P(f₁, f₂)(x)`).
* `tileSet S s' α = {t ∈ triIdx s' α | t.1 ∈ S}` and the infinite model sum
  `modelSum ρ M N g S ν n f₁ f₂ x = ∑'_{t ∈ tileSet S ν.s' ν.α} modelTerm (modelPacket ρ M N g ν n) f₁ f₂ x t`
  (this is `Π^{ν,n}(f₁,f₂)(x)`).

```
theorem hasSum_modelFamily {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) {M : ℕ} (hM : 3 < M) (N : ℕ)
    (S : Finset ℤ) (g : ℤ → ℝ → ℂ) (hgi : ∀ s ∈ S, Integrable (g s) volume)
    (hgF : ∀ s ∈ S, ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 (g s) ξ = 0)
    (hgD : ∀ s ∈ S, ∀ x : ℝ, ‖g s x‖ ≤ ((1 + |x|) ^ M)⁻¹) (f₁ f₂ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (modelFamily ρ M N g S f₁ f₂ x) (∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x)

theorem sum_dilAvgC_eq_modelSum (same hypotheses) :
    (∀ ν ∈ nuSet, ∀ n : ℤ × ℤ, Summable fun t : tileSet S ν.2.2.1 ν.2.2.2 =>
        ‖modelTerm (modelPacket ρ M N g ν n) f₁ f₂ x t‖) ∧
    ∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x =
      ∑ ν ∈ nuSet, ∑' n : ℤ × ℤ, (modelWeight M N n : ℂ) * modelSum ρ M N g S ν n f₁ f₂ x
```

`modelFamily` is the family over `ℤ⁴ × ℤ² × ℤ³` (`(ν, n, t)`), `w_n · modelTerm` on the support
`ν ∈ nuSet`, `t ∈ tileSet S ν.s' ν.α`, and `0` elsewhere; `hasSum_modelFamily` is *unconditional* (= absolute)
summability in `ℂ`.

Adaptedness (frozen `IsAdapted`, constant `1`): `exists_isAdapted_modelPacket`: there is `C = C(ρ, M, N) > 0` such
that for every `g` with `IsBandProfile M (g t.1)` and all `ν`, `n`, `t`, `k`, the normalised packet
`C⁻¹ φ^n_{t,k}` is `IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 k t)`. Consequently
`w_n · modelSum = w_n C³ · (the model sum of the normalised, adapted packets)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform Real SchwartzMap ContDiff

namespace PrimeBHT.TimeFrequency.RealLine

open PrimeBHT.Statements (TriValid triIdx timeInt freqNum freqInt IsAdapted)
open PrimeBHT.TimeFrequency.Interp.Hull (tileWeight modelOp toReal_volume_timeInt)

/-! ## Definitions -/

/-- `1 + |n₁| + |n₂|` (the `1 + |n|` of the blueprint, `|n| = |n₁| + |n₂|`). -/
def nrm (n : ℤ × ℤ) : ℝ := 1 + (|(n.1 : ℝ)| + |(n.2 : ℝ)|)

theorem one_le_nrm (n : ℤ × ℤ) : 1 ≤ nrm n := by
  unfold nrm; have := abs_nonneg (n.1 : ℝ); have := abs_nonneg (n.2 : ℝ); linarith

theorem nrm_pos (n : ℤ × ℤ) : 0 < nrm n := lt_of_lt_of_le one_pos (one_le_nrm n)

/-- The weight `w_n = (1 + |n|)^{-(M - 2 - 2N)}`. -/
def modelWeight (M N : ℕ) (n : ℤ × ℤ) : ℝ := nrm n ^ (-((M : ℝ) - 2 - 2 * N))

/-- The `3000` parameters `ν = (a, b, s', α)`: `21 ≤ a ≤ 30`, `-6 ≤ b ≤ 3`, `0 ≤ s' ≤ 9`, `0 ≤ α ≤ 2`. -/
def nuSet : Finset (ℤ × ℤ × ℤ × ℤ) :=
  Finset.Icc (21 : ℤ) 30 ×ˢ Finset.Icc (-6 : ℤ) 3 ×ˢ Finset.Ico (0 : ℤ) 10 ×ˢ Finset.Ico (0 : ℤ) 3

theorem card_nuSet : nuSet.card = 3000 := by
  simp [nuSet, Finset.card_product]

theorem triValid_of_mem_nuSet {ν : ℤ × ℤ × ℤ × ℤ} (h : ν ∈ nuSet) :
    TriValid ν.1 ν.2.1 ν.2.2.1 ν.2.2.2 := by
  simp only [nuSet, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico] at h
  unfold TriValid
  omega

/-- The summand `|I_t|^{-1/2} ⟨f₁, φ_{t,0}⟩ ⟨f₂, φ_{t,1}⟩ φ_{t,2}(x)` of the model sum (frozen `pairing`). -/
def modelTerm (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (f₁ f₂ : ℝ → ℂ) (x : ℝ) (t : ℤ × ℤ × ℤ) : ℂ :=
  (tileWeight t : ℂ) * (PrimeBHT.Statements.pairing f₁ (φ t 0) *
    PrimeBHT.Statements.pairing f₂ (φ t 1)) * φ t 2 x

theorem modelOp_apply (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (f₁ f₂ : ℝ → ℂ)
    (x : ℝ) : modelOp P φ f₁ f₂ x = ∑ t ∈ P, modelTerm φ f₁ f₂ x t := rfl

/-- The tiles of `P_ν` with scale in `S`: `{t ∈ triIdx s' α | s(t) ∈ S}`. -/
def tileSet (S : Finset ℤ) (s' α : ℤ) : Set (ℤ × ℤ × ℤ) := {t | t ∈ triIdx s' α ∧ t.1 ∈ S}

/-- The packets `φ^n_{t,k}` of R4 (d) (slot `k = 0, 1, 2` is the blueprint's `1, 2, 3`), at the scale `t.1`;
the dependence on `g` is through `c_{n,v,ℓ,a,b}[g_s]` in the third packet. -/
def modelPacket (ρ : 𝓢(ℝ, ℂ)) (M N : ℕ) (g : ℤ → ℝ → ℂ) (ν : ℤ × ℤ × ℤ × ℤ) (n : ℤ × ℤ)
    (t : ℤ × ℤ × ℤ) : Fin 3 → ℝ → ℂ :=
  ![fun x => ((nrm n ^ (-(N : ℝ)) : ℝ) : ℂ) * scaledPacket ρ t.1 (t.2.1 + n.1) t.2.2 x,
    fun x => ((nrm n ^ (-(N : ℝ)) : ℝ) : ℂ) * scaledPacket ρ t.1 (t.2.1 + n.2) (t.2.2 - ν.1) x,
    fun x => ((nrm n ^ ((M : ℝ) - 2) : ℝ) : ℂ) * coeffRep ρ (g t.1) ν.1 ν.2.1 n.1 n.2 t.2.1 t.2.2 *
      scaledPacket ρ t.1 t.2.1 (2 * t.2.2 - ν.1 - ν.2.1) x]

open Classical in
/-- The family over `(ν, n, t) ∈ ℤ⁴ × ℤ² × ℤ³` whose sum is `∑_s B_{2^s}(g_s, f₁, f₂)(x)`. -/
def modelFamily (ρ : 𝓢(ℝ, ℂ)) (M N : ℕ) (g : ℤ → ℝ → ℂ) (S : Finset ℤ) (f₁ f₂ : ℝ → ℂ) (x : ℝ)
    (q : (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ × ℤ)) : ℂ :=
  if q.1 ∈ nuSet ∧ q.2.2 ∈ tileSet S q.1.2.2.1 q.1.2.2.2 then
    (modelWeight M N q.2.1 : ℂ) * modelTerm (modelPacket ρ M N g q.1 q.2.1) f₁ f₂ x q.2.2
  else 0

/-! ## Dilation of the pairing; the scale-`s` term -/

/-- The scalar `|I|^{-1/2} = (2^s)^{-1/2}` of a scale-`s` tile. -/
def scaleWt (s : ℤ) : ℝ := ((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2)

theorem scaleWt_pos (s : ℤ) : 0 < scaleWt s := Real.rpow_pos_of_pos (zpow_pos (by norm_num) s) _

theorem tileWeight_eq (t : ℤ × ℤ × ℤ) : tileWeight t = scaleWt t.1 := by
  unfold PrimeBHT.TimeFrequency.Interp.Hull.tileWeight scaleWt
  rw [toReal_volume_timeInt]

theorem pairing_const_mul (c : ℂ) (f G : ℝ → ℂ) :
    pairing f (fun x => c * G x) = (starRingEnd ℂ) c * pairing f G := by
  unfold pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul]
  ring

/-- Dilation of the pairing: `⟨F(σ ·), G⟩ = σ^{-1/2} ⟨F, G^{(σ)}⟩` (`σ > 0`). -/
theorem pairing_comp_mul_dilPacket {σ : ℝ} (hσ : 0 < σ) (F G : ℝ → ℂ) :
    pairing (fun u => F (σ * u)) G = ((σ ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * pairing F (dilPacket σ G) := by
  have hδ2 : σ ^ (-(1 : ℝ) / 2) * σ ^ (-(1 : ℝ) / 2) = σ⁻¹ := by
    rw [← Real.rpow_add hσ, show -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
  have h1 : pairing (fun u => F (σ * u)) G =
      ((σ⁻¹ : ℝ) : ℂ) * ∫ x, F x * (starRingEnd ℂ) (G (σ⁻¹ * x)) := by
    unfold pairing
    have := Measure.integral_comp_mul_left (fun x : ℝ => F x * (starRingEnd ℂ) (G (σ⁻¹ * x))) σ
    simp only [inv_mul_cancel_left₀ hσ.ne'] at this
    rw [this, abs_of_pos (inv_pos.2 hσ), Complex.real_smul]
  have h2 : pairing F (dilPacket σ G) =
      ((σ ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * ∫ x, F x * (starRingEnd ℂ) (G (σ⁻¹ * x)) := by
    unfold pairing dilPacket
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul, hδ2]

theorem wavePacket_inv_mul_eq (ρ : ℝ → ℂ) (s v ℓ : ℤ) (x : ℝ) :
    wavePacket ρ v ℓ (((2 : ℝ) ^ s)⁻¹ * x) = ((scaleWt s : ℝ) : ℂ)⁻¹ * scaledPacket ρ s v ℓ x := by
  rw [scaledPacket_apply]
  have : ((scaleWt s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (scaleWt_pos s).ne'
  unfold scaleWt at this ⊢
  field_simp

/-- **The scale-`s` term of the representation.** With `σ = 2^s`, `F_i = f_i(σ ·)` and `y = σ⁻¹ x`:
`repTerm ρ ψ F₁ F₂ y a b n₁ n₂ v ℓ = σ^{-1/2} ⟨f₁,ψ^{(s)}_{v+n₁,ℓ}⟩ ⟨f₂,ψ^{(s)}_{v+n₂,ℓ-a}⟩ c ψ^{(s)}_{v,2ℓ-a-b}(x)`. -/
theorem repTerm_dilate (ρ : 𝓢(ℝ, ℂ)) (ψ f₁ f₂ : ℝ → ℂ) (s : ℤ) (x : ℝ) (a b n₁ n₂ v ℓ : ℤ) :
    repTerm ρ ψ (fun u => f₁ ((2 : ℝ) ^ s * u)) (fun u => f₂ ((2 : ℝ) ^ s * u))
        (((2 : ℝ) ^ s)⁻¹ * x) a b n₁ n₂ v ℓ =
      ((scaleWt s : ℝ) : ℂ) *
        (pairing f₁ (scaledPacket ρ s (v + n₁) ℓ) * pairing f₂ (scaledPacket ρ s (v + n₂) (ℓ - a)) *
          coeffRep ρ ψ a b n₁ n₂ v ℓ * scaledPacket ρ s v (2 * ℓ - a - b) x) := by
  have hσ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  unfold repTerm coeffRep
  rw [pairing_comp_mul_dilPacket hσ, pairing_comp_mul_dilPacket hσ, wavePacket_inv_mul_eq]
  have hne : ((scaleWt s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (scaleWt_pos s).ne'
  unfold scaledPacket
  unfold scaleWt at hne ⊢
  field_simp

theorem pairing_eq_frozen (f G : ℝ → ℂ) : pairing f G = PrimeBHT.Statements.pairing f G := rfl

theorem modelWeight_mul_prod (M N : ℕ) (n : ℤ × ℤ) :
    modelWeight M N n * (nrm n ^ (-(N : ℝ)) * nrm n ^ (-(N : ℝ)) * nrm n ^ ((M : ℝ) - 2)) = 1 := by
  unfold modelWeight
  rw [← Real.rpow_add (nrm_pos n), ← Real.rpow_add (nrm_pos n), ← Real.rpow_add (nrm_pos n)]
  rw [show -((M : ℝ) - 2 - 2 * N) + (-(N : ℝ) + -(N : ℝ) + ((M : ℝ) - 2)) = 0 by ring,
    Real.rpow_zero]

/-- `w_n · modelTerm` of the (unnormalised) packets is the scale-`s` term of the representation. -/
theorem modelWeight_mul_modelTerm (ρ : 𝓢(ℝ, ℂ)) (M N : ℕ) (g : ℤ → ℝ → ℂ) (f₁ f₂ : ℝ → ℂ) (x : ℝ)
    (s v ℓ a b s' α : ℤ) (n : ℤ × ℤ) :
    (modelWeight M N n : ℂ) * modelTerm (modelPacket ρ M N g (a, b, s', α) n) f₁ f₂ x (s, v, ℓ) =
      ((scaleWt s : ℝ) : ℂ) *
        (pairing f₁ (scaledPacket ρ s (v + n.1) ℓ) * pairing f₂ (scaledPacket ρ s (v + n.2) (ℓ - a)) *
          coeffRep ρ (g s) a b n.1 n.2 v ℓ * scaledPacket ρ s v (2 * ℓ - a - b) x) := by
  unfold modelTerm
  rw [tileWeight_eq]
  simp only [modelPacket, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ← pairing_eq_frozen]
  rw [pairing_const_mul, pairing_const_mul, Complex.conj_ofReal]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (modelWeight_mul_prod M N n)
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h
  linear_combination
    (((scaleWt s : ℝ) : ℂ) * pairing f₁ (scaledPacket ρ s (v + n.1) ℓ) *
      pairing f₂ (scaledPacket ρ s (v + n.2) (ℓ - a)) * coeffRep ρ (g s) a b n.1 n.2 v ℓ *
      scaledPacket ρ s v (2 * ℓ - a - b) x) * h

theorem isBandProfile_of_decay {M : ℕ} {ψ : ℝ → ℂ} (hi : Integrable ψ volume)
    (hF : ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 ψ ξ = 0)
    (hD : ∀ x : ℝ, ‖ψ x‖ ≤ ((1 + |x|) ^ M)⁻¹) : IsBandProfile (M : ℝ) ψ where
  aesm := hi.aestronglyMeasurable
  decay := fun x => by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    exact hD x
  fourier_supp := hF

/-- The injection of the `ℤ⁶` of the representation into the index of `modelFamily`, at scale `s`. -/
def famIdx (s : ℤ) (q : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :
    (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ × ℤ) :=
  ((q.1, q.2.1, s % 10, q.2.2.2.2.2 % 3), (q.2.2.1, q.2.2.2.1), (s, q.2.2.2.2.1, q.2.2.2.2.2))

theorem injective_famIdx (s : ℤ) : Function.Injective (famIdx s) := by
  rintro ⟨a, b, n₁, n₂, v, ℓ⟩ ⟨a', b', n₁', n₂', v', ℓ'⟩ h
  simp only [famIdx, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, -, -⟩, ⟨h3, h4⟩, -, h5, h6⟩ := h
  simp only [h1, h2, h3, h4, h5, h6]

open Classical in
theorem modelFamily_singleton_apply (ρ : 𝓢(ℝ, ℂ)) (M N : ℕ) (g : ℤ → ℝ → ℂ) (s : ℤ)
    (f₁ f₂ : ℝ → ℂ) (x : ℝ) (a b n₁ n₂ v ℓ : ℤ) :
    modelFamily ρ M N g {s} f₁ f₂ x (famIdx s (a, b, n₁, n₂, v, ℓ)) =
      if a ∈ Set.Icc (21 : ℤ) 30 ∧ b ∈ Set.Icc (-6 : ℤ) 3 then
        ((scaleWt s : ℝ) : ℂ) *
          (pairing f₁ (scaledPacket ρ s (v + n₁) ℓ) * pairing f₂ (scaledPacket ρ s (v + n₂) (ℓ - a)) *
            coeffRep ρ (g s) a b n₁ n₂ v ℓ * scaledPacket ρ s v (2 * ℓ - a - b) x)
      else 0 := by
  unfold modelFamily famIdx
  by_cases h : a ∈ Set.Icc (21 : ℤ) 30 ∧ b ∈ Set.Icc (-6 : ℤ) 3
  · rw [ite_eq_left h, ite_eq_left]
    · exact modelWeight_mul_modelTerm ρ M N g f₁ f₂ x s v ℓ a b (s % 10) (ℓ % 3) (n₁, n₂)
    · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
      refine ⟨?_, ?_, by simp⟩
      · simp only [nuSet, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico]
        omega
      · unfold triIdx
        exact ⟨(Int.mod_modEq s 10).symm, (Int.mod_modEq ℓ 3).symm⟩
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨hν, -⟩
    apply h
    simp only [nuSet, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico] at hν
    simp only [Set.mem_Icc]
    omega

theorem hasSum_modelFamily_singleton {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) {M : ℕ} (hM : 3 < M)
    (N : ℕ) (g : ℤ → ℝ → ℂ) (s : ℤ) (hgi : Integrable (g s) volume)
    (hgF : ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 (g s) ξ = 0)
    (hgD : ∀ x : ℝ, ‖g s x‖ ≤ ((1 + |x|) ^ M)⁻¹) (f₁ f₂ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (modelFamily ρ M N g {s} f₁ f₂ x) (dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x) := by
  have hσ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hψ : IsBandProfile (M : ℝ) (g s) := isBandProfile_of_decay hgi hgF hgD
  have hM' : (3 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  obtain ⟨F₁, hF₁⟩ := exists_schwartz_dilate f₁ hσ
  obtain ⟨F₂, hF₂⟩ := exists_schwartz_dilate f₂ hσ
  have hF₁' : (⇑F₁ : ℝ → ℂ) = fun u => f₁ ((2 : ℝ) ^ s * u) := funext hF₁
  have hF₂' : (⇑F₂ : ℝ → ℂ) = fun u => f₂ ((2 : ℝ) ^ s * u) := funext hF₂
  have hrep := hasSum_representation ρ hρ hM' hψ F₁ F₂ (((2 : ℝ) ^ s)⁻¹ * x)
  have hB : bilinB1 (g s) F₁ F₂ (((2 : ℝ) ^ s)⁻¹ * x) = dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x := by
    have h := dilAvgC_dilate (g s) hσ one_pos f₁ f₂ (((2 : ℝ) ^ s)⁻¹ * x)
    rw [one_mul, mul_inv_cancel_left₀ hσ.ne'] at h
    rw [← h, hF₁', hF₂']
    unfold bilinB1 dilAvgC
    simp
  rw [hB] at hrep
  have hzero : ∀ y, y ∉ Set.range (famIdx s) → modelFamily ρ M N g {s} f₁ f₂ x y = 0 := by
    rintro ⟨⟨a, b, s', α⟩, ⟨n₁, n₂⟩, ⟨s₀, v, ℓ⟩⟩ hy
    unfold modelFamily
    rw [ite_eq_right]
    rintro ⟨hν, ht⟩
    apply hy
    simp only [nuSet, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico] at hν
    simp only [tileSet, triIdx, Set.mem_ofPred_eq, Finset.mem_singleton] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    unfold Int.ModEq at h1 h2
    refine ⟨(a, b, n₁, n₂, v, ℓ), ?_⟩
    simp only [famIdx, Prod.mk.injEq]
    subst h3
    simp only [true_and, and_true]
    omega
  rw [← (injective_famIdx s).hasSum_iff hzero]
  convert hrep using 1
  funext q
  obtain ⟨a, b, n₁, n₂, v, ℓ⟩ := q
  simp only [Function.comp_apply]
  rw [modelFamily_singleton_apply]
  by_cases h : a ∈ Set.Icc (21 : ℤ) 30 ∧ b ∈ Set.Icc (-6 : ℤ) 3
  · rw [ite_eq_left h, hF₁', hF₂']
    have := repTerm_dilate ρ (g s) f₁ f₂ s x a b n₁ n₂ v ℓ
    exact this.symm
  · rw [ite_eq_right h]
    exact (repTerm_eq_zero ρ hρ (by linarith) hψ _ _ _ _ _ _ _ _ _
      (by simp only [Set.mem_Icc] at h ⊢; omega)).symm

theorem modelFamily_eq_sum_singleton (ρ : 𝓢(ℝ, ℂ)) (M N : ℕ) (g : ℤ → ℝ → ℂ) (S : Finset ℤ)
    (f₁ f₂ : ℝ → ℂ) (x : ℝ) (q : (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ × ℤ)) :
    modelFamily ρ M N g S f₁ f₂ x q = ∑ s ∈ S, modelFamily ρ M N g {s} f₁ f₂ x q := by
  classical
  by_cases h : q.1 ∈ nuSet ∧ q.2.2 ∈ tileSet S q.1.2.2.1 q.1.2.2.2
  · rw [Finset.sum_eq_single q.2.2.1]
    · have hc : q.1 ∈ nuSet ∧ q.2.2 ∈ tileSet {q.2.2.1} q.1.2.2.1 q.1.2.2.2 :=
        ⟨h.1, h.2.1, Finset.mem_singleton_self _⟩
      unfold modelFamily
      rw [ite_eq_left h, ite_eq_left hc]
    · intro s hs hne
      unfold modelFamily
      rw [ite_eq_right]
      rintro ⟨-, -, h3⟩
      exact hne (Finset.mem_singleton.1 h3).symm
    · intro hn
      exact absurd h.2.2 hn
  · rw [Finset.sum_eq_zero]
    · unfold modelFamily
      rw [ite_eq_right h]
    · intro s hs
      unfold modelFamily
      rw [ite_eq_right]
      rintro ⟨h1, h2, h3⟩
      refine h ⟨h1, h2, ?_⟩
      rw [Finset.mem_singleton.1 h3]
      exact hs

/-! ## Adaptedness of the model packets (frozen `IsAdapted`, exponent `N`) -/

theorem nrm_ge_one_add_abs_fst (n : ℤ × ℤ) : 1 + |(n.1 : ℝ)| ≤ nrm n := by
  unfold nrm; have := abs_nonneg (n.2 : ℝ); linarith

theorem nrm_ge_one_add_abs_snd (n : ℤ × ℤ) : 1 + |(n.2 : ℝ)| ≤ nrm n := by
  unfold nrm; have := abs_nonneg (n.1 : ℝ); linarith

/-- **R4 (d): the model packets are adapted, with exponent `N`, in the frozen sense.** There is `C = C(ρ, M, N)`
such that for every `g` with `g_{t.1}` a band profile, every `ν`, `n`, tile `t` and slot `k`, the normalised packet
`C⁻¹ φ^n_{t,k}` is `PrimeBHT.Statements.IsAdapted N (timeInt t) (freqInt a b k t)` (constant exactly `1`). -/
theorem exists_isAdapted_modelPacket {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) {M : ℕ} (hM : 3 < M)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℝ → ℂ) (ν : ℤ × ℤ × ℤ × ℤ) (n : ℤ × ℤ) (t : ℤ × ℤ × ℤ),
      IsBandProfile (M : ℝ) (g t.1) → ∀ k : Fin 3,
        IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 k t)
          (fun x => ((C⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t k x) := by
  have hM2 : (2 : ℝ) < (M : ℝ) := by
    have : (3 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    linarith
  obtain ⟨Cp, hCp, hAd⟩ := exists_isAdapted_scaledPacket hρ N
  obtain ⟨Cc, hCc0, hCc⟩ := exists_norm_coeffRep_le ρ (M := (M : ℝ)) hM2
  set Cc' : ℝ := max Cc 1 with hCc'
  have hCc'1 : 1 ≤ Cc' := le_max_right _ _
  have hCc'0 : 0 < Cc' := lt_of_lt_of_le one_pos hCc'1
  refine ⟨Cp * Cc', mul_pos hCp hCc'0, ?_⟩
  intro g ν n t hψ k
  have hCle : (Cp * Cc')⁻¹ ≤ Cp⁻¹ := by
    apply inv_anti₀ hCp
    nlinarith
  have hCpos : 0 < (Cp * Cc')⁻¹ := inv_pos.2 (mul_pos hCp hCc'0)
  -- slots 0 and 1
  have hslot : ∀ (m : ℤ), 1 + |(m : ℝ)| ≤ nrm n → ∀ (κ : ℂ) (j : ℤ),
      κ = (((Cp * Cc')⁻¹ * nrm n ^ (-(N : ℝ)) : ℝ) : ℂ) →
      IsAdapted N (timeInt t) (Set.Ico ((2 : ℝ) ^ (-t.1) * ((j : ℝ) / 3))
        ((2 : ℝ) ^ (-t.1) * ((j : ℝ) / 3 + 1))) (fun x => κ * scaledPacket ρ t.1 (t.2.1 + m) j x) := by
    intro m hm κ j hκ
    refine hAd t.1 t.2.1 m j κ ?_
    rw [hκ, Complex.norm_real, Real.norm_of_nonneg (by have := nrm_pos n; positivity)]
    have h1 : nrm n ^ (-(N : ℝ)) ≤ (1 + |(m : ℝ)|) ^ (-(N : ℝ)) :=
      rpow_neg_anti (by positivity) hm (Nat.cast_nonneg N)
    exact mul_le_mul hCle h1 (Real.rpow_nonneg (nrm_pos n).le _) (inv_pos.2 hCp).le
  fin_cases k
  · have := hslot n.1 (nrm_ge_one_add_abs_fst n) (((((Cp * Cc')⁻¹ * nrm n ^ (-(N : ℝ)) : ℝ)) : ℂ)) t.2.2
      rfl
    have e : (fun x => (((Cp * Cc')⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t 0 x) =
        fun x => ((((Cp * Cc')⁻¹ * nrm n ^ (-(N : ℝ)) : ℝ)) : ℂ) *
          scaledPacket ρ t.1 (t.2.1 + n.1) t.2.2 x := by
      funext x
      simp only [modelPacket, Matrix.cons_val_zero]
      push_cast
      ring
    show IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 0 t)
      (fun x => (((Cp * Cc')⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t 0 x)
    rw [e]
    exact this
  · have := hslot n.2 (nrm_ge_one_add_abs_snd n) (((((Cp * Cc')⁻¹ * nrm n ^ (-(N : ℝ)) : ℝ)) : ℂ))
      (t.2.2 - ν.1) rfl
    have e : (fun x => (((Cp * Cc')⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t 1 x) =
        fun x => ((((Cp * Cc')⁻¹ * nrm n ^ (-(N : ℝ)) : ℝ)) : ℂ) *
          scaledPacket ρ t.1 (t.2.1 + n.2) (t.2.2 - ν.1) x := by
      funext x
      simp only [modelPacket, Matrix.cons_val_one]
      push_cast
      ring
    show IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 1 t)
      (fun x => (((Cp * Cc')⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t 1 x)
    rw [e]
    exact this
  · set κ : ℂ := (((Cp * Cc')⁻¹ : ℝ) : ℂ) * ((nrm n ^ ((M : ℝ) - 2) : ℝ) : ℂ) *
      coeffRep ρ (g t.1) ν.1 ν.2.1 n.1 n.2 t.2.1 t.2.2 with hκdef
    have hκ : ‖κ‖ ≤ Cp⁻¹ * (1 + |((0 : ℤ) : ℝ)|) ^ (-(N : ℝ)) := by
      simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow, mul_one]
      have hc := hCc (g t.1) hψ ν.1 ν.2.1 n.1 n.2 t.2.1 t.2.2
      have hn : nrm n ^ ((M : ℝ) - 2) * (1 + (|(n.1 : ℝ)| + |(n.2 : ℝ)|)) ^ (-((M : ℝ) - 2)) = 1 := by
        change nrm n ^ ((M : ℝ) - 2) * nrm n ^ (-((M : ℝ) - 2)) = 1
        rw [← Real.rpow_add (nrm_pos n)]; simp
      rw [hκdef, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hCpos.le, Real.norm_of_nonneg (Real.rpow_nonneg (nrm_pos n).le _)]
      calc (Cp * Cc')⁻¹ * nrm n ^ ((M : ℝ) - 2) * ‖coeffRep ρ (g t.1) ν.1 ν.2.1 n.1 n.2 t.2.1 t.2.2‖
          ≤ (Cp * Cc')⁻¹ * nrm n ^ ((M : ℝ) - 2) *
              (Cc * (1 + (|(n.1 : ℝ)| + |(n.2 : ℝ)|)) ^ (-((M : ℝ) - 2))) :=
            mul_le_mul_of_nonneg_left hc
              (mul_nonneg hCpos.le (Real.rpow_nonneg (nrm_pos n).le _))
        _ = (Cp * Cc')⁻¹ * Cc * (nrm n ^ ((M : ℝ) - 2) *
              (1 + (|(n.1 : ℝ)| + |(n.2 : ℝ)|)) ^ (-((M : ℝ) - 2))) := by ring
        _ = (Cp * Cc')⁻¹ * Cc := by rw [hn, mul_one]
        _ ≤ Cp⁻¹ := by
            rw [mul_inv, mul_assoc]
            have : Cc * Cc'⁻¹ ≤ 1 := by
              rw [← div_eq_mul_inv, div_le_one hCc'0]; exact le_max_left _ _
            calc Cp⁻¹ * (Cc'⁻¹ * Cc) = Cp⁻¹ * (Cc * Cc'⁻¹) := by ring
              _ ≤ Cp⁻¹ * 1 := by gcongr
              _ = Cp⁻¹ := mul_one _
    have := hAd t.1 t.2.1 0 (freqNum ν.1 ν.2.1 t 2) κ hκ
    have e : (fun x => (((Cp * Cc')⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t 2 x) =
        fun x => κ * scaledPacket ρ t.1 (t.2.1 + 0) (freqNum ν.1 ν.2.1 t 2) x := by
      funext x
      simp only [modelPacket, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, hκdef, add_zero]
      have hf : freqNum ν.1 ν.2.1 t 2 = 2 * t.2.2 - ν.1 - ν.2.1 := rfl
      rw [hf]
      ring
    show IsAdapted N (timeInt t) (freqInt ν.1 ν.2.1 2 t)
      (fun x => (((Cp * Cc')⁻¹ : ℝ) : ℂ) * modelPacket ρ M N g ν n t 2 x)
    rw [e]
    exact this

theorem hasSum_modelFamily {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) {M : ℕ} (hM : 3 < M) (N : ℕ)
    (S : Finset ℤ) (g : ℤ → ℝ → ℂ) (hgi : ∀ s ∈ S, Integrable (g s) volume)
    (hgF : ∀ s ∈ S, ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 (g s) ξ = 0)
    (hgD : ∀ s ∈ S, ∀ x : ℝ, ‖g s x‖ ≤ ((1 + |x|) ^ M)⁻¹) (f₁ f₂ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (modelFamily ρ M N g S f₁ f₂ x)
      (∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x) := by
  have h := hasSum_sum (s := S) (f := fun s => modelFamily ρ M N g {s} f₁ f₂ x)
    (a := fun s => dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂ x)
    (fun s hs => hasSum_modelFamily_singleton hρ hM N g s (hgi s hs) (hgF s hs) (hgD s hs) f₁ f₂ x)
  convert h using 1
  funext q
  exact modelFamily_eq_sum_singleton ρ M N g S f₁ f₂ x q

end PrimeBHT.TimeFrequency.RealLine

end
