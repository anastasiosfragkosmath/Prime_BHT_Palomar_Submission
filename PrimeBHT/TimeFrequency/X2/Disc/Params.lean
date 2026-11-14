module

public import PrimeBHT.TimeFrequency.X2.Disc.TileCutoff

/-!
# X2, node V05 (parameters): the class `𝔭` of the discretization

`discPar N D = ⟨16, 16 (N + 400), D + 400, 2^{-32}, 11/4, C⟩` with `C = N' (3N'/δ)^{N'} (3/2)^{N'}` (`N' = 16 (N + 400)`).
`discretization_params_good`: it is admissible, `N ≤ 𝔭.N`, `D ≤ 𝔭.D`, `𝔭.N ≡ 0 (16)` (so `𝔭.N/8` is even), and it carries
the model profile `η` (`IsEtaCut 𝔭 η` with every tile cutoff in `X_I(𝔭)`) and the tree profile `η'` (`IsEtaCut 𝔭.tree η'`).
-/

@[expose] public noncomputable section

open Set

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- The decay order of the discretization class. -/
def discN (N : ℕ) : ℕ := 16 * (N + 400)

/-- The amplitude constant of the discretization class (`N (3N/δ)^N (3/2)^N`, `δ = 2^{-32}`). -/
def discC (N : ℕ) : ℝ :=
  (discN N : ℝ) * (3 * (discN N : ℝ) / (2 : ℝ) ^ (-32 : ℤ)) ^ discN N * (3 / 2) ^ discN N

/-- The class `𝔭` chosen by the discretization. -/
def discPar (N D : ℕ) : Params :=
  ⟨16, discN N, D + 400, (2 : ℝ) ^ (-32 : ℤ), 11 / 4, discC N⟩

theorem discPar_D (N D : ℕ) : (discPar N D).D = D + 400 := rfl

theorem discC_ge_one (N : ℕ) : 1 ≤ discC N := by
  have hN : (1 : ℝ) ≤ discN N := by
    have : 1 ≤ discN N := by unfold discN; omega
    exact_mod_cast this
  have hδ : (2 : ℝ) ^ (-32 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  have hδ0 : (0 : ℝ) < (2 : ℝ) ^ (-32 : ℤ) := zpow_pos (by norm_num) _
  have h1 : (1 : ℝ) ≤ 3 * (discN N : ℝ) / (2 : ℝ) ^ (-32 : ℤ) := by
    rw [le_div_iff₀ hδ0]; linarith
  unfold discC
  have h2 : (1 : ℝ) ≤ (3 * (discN N : ℝ) / (2 : ℝ) ^ (-32 : ℤ)) ^ discN N := one_le_pow₀ h1
  have h3 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ discN N := one_le_pow₀ (by norm_num)
  calc (1 : ℝ) ≤ (discN N : ℝ) * (1 * 1) := by linarith
    _ ≤ (discN N : ℝ) * ((3 * (discN N : ℝ) / (2 : ℝ) ^ (-32 : ℤ)) ^ discN N * (3 / 2) ^ discN N) := by
        gcongr
    _ = _ := by ring

theorem discPar_admissible (N D : ℕ) : (discPar N D).Admissible := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show jFloor ≤ 16; unfold jFloor; norm_num
  · show classFloor ≤ 16 * (N + 400); unfold classFloor; omega
  · show classFloor ≤ D + 400; unfold classFloor; omega
  · exact zpow_pos (by norm_num) _
  · show (2 : ℝ) ^ (-32 : ℤ) ≤ (2 : ℝ) ^ (-(3 * ((16 : ℕ) : ℝ) / 2))
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  · show (1 : ℝ) ≤ 11 / 4; norm_num
  · show (11 / 4 : ℝ) ≤ 11 / 4; exact le_rfl
  · exact discC_ge_one N

theorem discPar_N_even (N D : ℕ) : Even (discPar N D).N := ⟨8 * (N + 400), by simp [discPar, discN]; ring⟩

theorem discPar_N_div8 (N D : ℕ) : (discPar N D).N / 8 = 2 * (N + 400) := by
  show 16 * (N + 400) / 8 = 2 * (N + 400); omega

/-- **`discretization_params_good`.**  The class chosen by V05 satisfies the margins, is admissible, and carries both profiles. -/
theorem discretization_params_good (N D : ℕ) :
    (discPar N D).Admissible ∧ N ≤ (discPar N D).N ∧ D ≤ (discPar N D).D ∧ (discPar N D).J = 16 ∧
      (discPar N D).β = 11 / 4 ∧ (discPar N D).N % 16 = 0 ∧ Even ((discPar N D).N / 8) ∧
      (∃ η : ℝ → ℝ, IsEtaCut (discPar N D) η ∧ ∀ s v : ℤ, InX (discPar N D) s v (tileCutoff η s v)) ∧
      (∃ η' : ℝ → ℝ, IsEtaCut (discPar N D).tree η') := by
  have hδ : (0 : ℝ) < (2 : ℝ) ^ (-32 : ℤ) := zpow_pos (by norm_num) _
  have hδ1 : (2 : ℝ) ^ (-32 : ℤ) ≤ 1 / 4 := by
    have : (2 : ℝ) ^ (-32 : ℤ) ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    refine this.trans (by norm_num)
  have hN2 : 2 ≤ (discPar N D).N := by show 2 ≤ 16 * (N + 400); omega
  have hC : ((discPar N D).N : ℝ) * (3 * ((discPar N D).N : ℝ) / (discPar N D).δ) ^ (discPar N D).N *
      (3 / 2) ^ (discPar N D).N ≤ (discPar N D).C := le_rfl
  have hev8 : Even ((discPar N D).N / 8) := by rw [discPar_N_div8]; exact even_two_mul _
  refine ⟨discPar_admissible N D, ?_, ?_, rfl, rfl, ?_, hev8,
    exists_eta_inX (discPar N D) (discPar_N_even N D) hN2 hδ hδ1 hC, ?_⟩
  · show N ≤ 16 * (N + 400); omega
  · show D ≤ D + 400; omega
  · show 16 * (N + 400) % 16 = 0; omega
  · have hC' : ((discPar N D).N : ℝ) * (3 * ((discPar N D).N : ℝ) / (discPar N D).δ) ^ (discPar N D).N ≤
        (discPar N D).C := by
      have h3 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ discN N := one_le_pow₀ (by norm_num)
      have h0 : (0 : ℝ) ≤ (discN N : ℝ) * (3 * (discN N : ℝ) / (2 : ℝ) ^ (-32 : ℤ)) ^ discN N :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by positivity) hδ.le) _)
      exact le_mul_of_one_le_right h0 h3
    exact exists_etaCut_tree (discPar N D) hev8 (by rw [discPar_N_div8]; omega) hδ hδ1 hC'

end PrimeBHT.TimeFrequency.X2.Disc
