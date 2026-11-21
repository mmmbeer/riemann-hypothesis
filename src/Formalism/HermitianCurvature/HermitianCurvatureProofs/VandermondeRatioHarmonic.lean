import Formalism.HermitianCurvature.StatementSz

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

lemma b_lt (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) :
    ∀ j' : ℕ, j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base =>
    intro h
    have := hc.hgap j hj (by omega)
    linarith
  | succ n hn ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hc.hgap n (by omega) (by omega)
    linarith

lemma b_ge_one (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.eq_or_lt_of_le hj with h | h
  · rw [← h]; exact hc.hb1
  · have := b_lt c hc 1 le_rfl j h hjm
    linarith [hc.hb1]

end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz

theorem interlacing : Formalism.FourierDecayAlt.Sz.Interlacing := by
  intro c de hc hw
  obtain ⟨hk, hm, hDel, hv0, hv1, hb1, hgap, ha, htop⟩ := hc
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · intro i hi1 hik
    have hl : c.lam i = c.v i := by simp [Cfg.lam, hik]
    rw [hl]
    constructor
    · by_cases h1 : i = 1
      · subst h1
        have : c.u de 1 = c.a := by simp [Cfg.u]
        rw [this]; nlinarith
      · have hne : i ≠ c.k := by omega
        have : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by simp [Cfg.u, h1, hne]
        rw [this]
        have hc1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub hi1]; simp
        unfold Cfg.v; rw [hc1]
        rcases hw.1 (i - 1) with h | h <;> rw [h] <;> nlinarith
    · have h1 : i + 1 ≠ 1 := by omega
      by_cases hlast : i + 1 = c.k
      · have : c.u de (i + 1) = c.ulast := by
          unfold Cfg.u; rw [if_neg h1, if_pos hlast]
        rw [this]
        have hiR : (i : ℝ) + 1 = c.k := by exact_mod_cast hlast
        have hvi : c.v i = c.vlast := by unfold Cfg.v; rw [← hiR]; ring
        rw [hvi]; unfold Cfg.ulast
        by_cases ht : c.top = true
        · have := htop ht; simp [ht]; linarith [this.1]
        · simp [ht]
      · have : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
          unfold Cfg.u; rw [if_neg h1, if_neg hlast]; simp
        rw [this]
        rcases hw.1 i with h | h <;> rw [h] <;> nlinarith
  · have hl : c.lam c.k = -c.b 1 := by simp [Cfg.lam]
    have hu : c.u de c.k = c.ulast := by
      have : c.k ≠ 1 := by omega
      simp [Cfg.u, this]
    rw [hl, hu]; unfold Cfg.ulast
    by_cases ht : c.top = true
    · have := htop ht; simp [ht]; linarith [this.2]
    · simp [ht]; linarith

theorem lamStrictAnti : Formalism.FourierDecayAlt.Sz.LamAnti := by
  intro c hc s t hs hst ht
  have hDel := hc.hDel
  have hstR : (s : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hst
  by_cases htk : t < c.k
  · have hsk : s < c.k := by omega
    have h1 : c.lam t = c.v t := by simp [Cfg.lam, htk]
    have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
    rw [h1, h2]; unfold Cfg.v
    nlinarith
  · have h1 : c.lam t = -c.b (t + 1 - c.k) := by simp [Cfg.lam, htk]
    rw [h1]
    by_cases hsk : s < c.k
    · have h2 : c.lam s = c.v s := by simp [Cfg.lam, hsk]
      rw [h2]
      have hb := Sz3.b_ge_one c hc (t + 1 - c.k) (by omega) (by omega)
      have hskR : (s : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hsk
      have hv0 := hc.hv0
      unfold Cfg.v
      nlinarith
    · have h2 : c.lam s = -c.b (s + 1 - c.k) := by simp [Cfg.lam, hsk]
      rw [h2]
      have := Sz3.b_lt c hc (s + 1 - c.k) (by omega) (t + 1 - c.k) (by omega) (by omega)
      linarith


end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz



noncomputable def NF (J : ℕ) (de : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 J, (∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)

lemma shift_sum (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 (J - d), de (i + d) = ∑ i ∈ Ioc d J, de i := by
  apply Finset.sum_nbij' (fun i => i + d) (fun i => i - d)
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
  · intro a ha; simp only [mem_Icc] at *; omega
  · intro a ha; simp only [mem_Ioc] at *; omega
  · intro a ha; rfl




end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P.Sz3

open Finset Formalism.FourierDecayAlt.Sz

noncomputable def hs (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, 1 / (d : ℝ)

lemma hs_succ (n : ℕ) : hs (n + 1) = hs n + 1 / ((n : ℝ) + 1) := by
  unfold hs
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  push_cast
  rfl

lemma hs_sub (p J : ℕ) (h : p ≤ J) : ∑ d ∈ Ioc p J, 1 / (d : ℝ) = hs J - hs p := by
  unfold hs
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) h]
  ring



lemma Icc_one_eq (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega




noncomputable def xx (de : ℕ → ℝ) (i i' : ℕ) : ℝ := (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ)))


end Formalism.FourierDecayAlt.P.Sz3

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Sz3


end Formalism.FourierDecayAlt.P
