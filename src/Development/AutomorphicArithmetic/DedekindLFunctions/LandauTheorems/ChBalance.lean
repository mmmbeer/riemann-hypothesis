import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia

open Finset

noncomputable section

namespace Deduction

open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

namespace CharacterBalance

open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ}
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) (hdN : N < D.d) :
    askD D N a t w = 0 :=
  askD_zero_below D hw hN hdN

lemma cardI (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) : (Nat.card (D.inertia D.d) : ℂ) = 2 :=
  card_inertia_of_pair D hD.inertia_d

lemma ounram (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (p i : ℕ) (hp : p.Prime) (h2 : p ∉ S0)
    (hd : p ≠ D.d) (hi : 1 ≤ i) (g : E0 × H) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i)
      = if i • D.frob p = g then 2 else 0 := by
  classical
  have := orthogonality_ramified D p i hp hi g
  rw [this, hD.unram p hp h2 hd]
  by_cases he : i • D.frob p = g
  · rw [if_pos he, if_pos (by rw [he, sub_self]; exact AddSubgroup.zero_mem _), AddSubgroup.card_bot]
    norm_num
  · rw [if_neg he, if_neg (by rw [AddSubgroup.mem_bot, sub_eq_zero]; exact fun e => he e.symm)]

lemma lunram (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ∉ S0) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) :=
  local_unram_of_kernel D N a t w fun i hi g => ounram D hD p i hp h2 hd hi g

lemma lsplit (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ∈ S0) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = 0 :=
  local_split_of_inPhi D N a t w hp (hD.split_inertia p h2) (hD.split_frob p h2)

lemma ld (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (D.d ^ i) g * Fc a t w (D.d ^ i) g
      = ((Real.log D.d * askD D N a t w : ℝ) : ℂ) :=
  local_d_of_card_two D hD.d_prime (cardI D hD) N a t w

lemma askExp (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) :
    (ASK D N a t w : ℂ) = (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ) := by
  classical
  set S := univ.filter (fun g : E0 × H => ¬ InPhi g) with hS
  rw [primePower_expansion D a t w hw N hN]
  set P := (range (N + 1)).filter Nat.Prime with hP
  have hC : ∀ p ∈ P, (∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ S, Kc D (p ^ i) g * Fc a t w (p ^ i) g)
      = (if IsInert D p then ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) else 0)
        + (if p = D.d then ((Real.log D.d * askD D N a t w : ℝ) : ℂ) else 0) := by
    intro p hpP
    have hp : p.Prime := (Finset.mem_filter.1 hpP).2
    by_cases hd : p = D.d
    · subst hd
      rw [hS, ld D hD N a t w, if_neg (fun h => h.2.2.2.1 rfl), if_pos rfl, zero_add]
    · rw [if_neg hd, add_zero]
      by_cases h2 : p ∈ S0
      · rw [hS, lsplit D hD N a t w hp h2]
        rw [if_neg]
        rintro ⟨_, _, _, _, hc⟩
        exact hc (hD.split_frob p h2)
      · have h21 : p ≠ 2 := fun e => h2 (e ▸ hD.two_mem)
        have h22 : p ≠ D.q1 := fun e => h2 (e ▸ hD.q1_mem)
        rw [hS, lunram D hD N a t w hp h2 hd]
        by_cases hin : IsInert D p
        · rw [if_pos hin]
        · rw [if_neg hin]
          have hφ : InPhi (D.frob p) := by
            by_contra hc; exact hin ⟨hp, h21, h22, hd, hc⟩
          have : askP D N a t w p = 0 := by
            unfold askP
            rw [Finset.sum_eq_zero]
            intro i hi
            exact absurd (inPhi_nsmul hφ i) (Finset.mem_filter.1 hi).2
          rw [this]; simp
  rw [Finset.sum_congr rfl hC, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_ite_eq']
  have hfilt : (range (N + 1)).filter (IsInert D) = P.filter (IsInert D) := by
    rw [hP, Finset.filter_filter]
    exact Finset.filter_congr (fun p _ => ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩)
  unfold ASK
  rw [hfilt]
  push_cast
  congr 1
  by_cases hdP : D.d ∈ P
  · rw [if_pos hdP]
  · rw [if_neg hdP]
    have hdN : N < D.d := by
      by_contra hc
      exact hdP (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hD.d_prime⟩)
    rw [ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime D hD hw hN hdN]; simp

end CharacterBalance

theorem ch_balance {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) : (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w := by
  rw [CharacterBalance.askExp D hD a t w hw N hN]
  exact fourier_balance D ell a t w ha hw N hN

end Deduction

end
