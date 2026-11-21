import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartzStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement

section
noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

def lmajABump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

lemma lmajABump_bound (m : ℕ) : ∃ C, ∀ t : ℝ, ‖iteratedFDeriv ℝ m lmajABump t‖ ≤ C :=
  ((lmajABump.contDiff (n := ⊤)).continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
    (lmajABump.hasCompactSupport.iteratedFDeriv m)

lemma lmajABump_deriv_zero (m : ℕ) (t : ℝ) (ht : 2 < |t|) : iteratedFDeriv ℝ m lmajABump t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport (lmajABump : ℝ → ℝ) := support_iteratedFDeriv_subset m hne
  rw [lmajABump.tsupport_eq, mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  exact absurd h1 (by simp [lmajABump]; linarith)

theorem lmajASeqSchwartz (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ k : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ k)) :
    ∃ h : SchwartzMap ℝ ℂ, (∀ t, 0 ≤ (h t).re ∧ (h t).im = 0) ∧
      ∀ (n : ℕ) (t : ℝ), |t - n| ≤ 1 → b n ≤ (h t).re := by
  choose C hC using lmajABump_bound
  set φ : ℕ → ℝ → ℝ := fun n => b n • fun t => lmajABump (t - n) with hφ
  have hφc : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ n) := fun n =>
    ((lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)).const_smul (b n)
  have hD : ∀ m n t, iteratedFDeriv ℝ m (φ n) t = b n • iteratedFDeriv ℝ m lmajABump (t - n) := by
    intro m n t
    have hc : ContDiff ℝ m (fun t : ℝ => lmajABump (t - n)) :=
      (lmajABump.contDiff).comp (contDiff_id.sub contDiff_const)
    rw [hφ]
    simp only
    rw [iteratedFDeriv_const_smul_apply hc.contDiffAt, iteratedFDeriv_comp_sub]
  have hs0 : Summable b := by simpa using hb 0
  have hv : ∀ m : ℕ, ((m : ℕ∞)) ≤ (⊤ : ℕ∞) → Summable (fun n => b n * C m) :=
    fun m _ => hs0.mul_right _
  have hbd : ∀ (m : ℕ) (n : ℕ) (t : ℝ), ((m : ℕ∞)) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ m (φ n) t‖ ≤ b n * C m := by
    intro m n t _
    rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
    exact mul_le_mul_of_nonneg_left (hC m _) (hb0 n)
  set g : ℝ → ℝ := fun t => ∑' n, φ n t with hg
  have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := contDiff_tsum hφc hv hbd
  have hφv : ∀ n t, φ n t = b n * lmajABump (t - n) := fun n t => rfl
  have hφs : ∀ t, Summable (fun n => φ n t) := by
    intro t
    refine hs0.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
    · rw [hφv]; exact mul_le_of_le_one_right (hb0 n) (lmajABump.le_one)
  have hg0 : ∀ t, 0 ≤ g t := fun t => tsum_nonneg fun n => by
    rw [hφv]; exact mul_nonneg (hb0 n) (lmajABump.nonneg)
  have hdecay : ∀ k m : ℕ, ∀ t : ℝ, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m g t‖ ≤
      ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
    intro k m t
    rw [hg, iteratedFDeriv_tsum_apply hφc hv hbd (mod_cast le_top) t]
    have hsn : Summable (fun n => ‖iteratedFDeriv ℝ m (φ n) t‖) :=
      (hv m le_top).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd m n t le_top)
    calc ‖t‖ ^ k * ‖∑' n, iteratedFDeriv ℝ m (φ n) t‖
        ≤ ‖t‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ m (φ n) t‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (by positivity)
      _ = ∑' n, ‖t‖ ^ k * ‖iteratedFDeriv ℝ m (φ n) t‖ := (tsum_mul_left).symm
      _ ≤ ∑' n, b n * ((n : ℝ) + 2) ^ k * C m := by
          refine (hsn.mul_left _).tsum_le_tsum (fun n => ?_) ((hb k).mul_right _)
          rw [hD, norm_smul, Real.norm_of_nonneg (hb0 n)]
          by_cases htn : |t - n| ≤ 2
          · have h1 : ‖t‖ ≤ (n : ℝ) + 2 := by
              rw [Real.norm_eq_abs]
              have := abs_sub_abs_le_abs_sub t n
              rw [Nat.abs_cast] at this
              linarith
            have h2 : ‖t‖ ^ k ≤ ((n : ℝ) + 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            calc ‖t‖ ^ k * (b n * ‖iteratedFDeriv ℝ m (lmajABump : ℝ → ℝ) (t - n)‖)
                ≤ ((n : ℝ) + 2) ^ k * (b n * C m) :=
                  mul_le_mul h2 (mul_le_mul_of_nonneg_left (hC m _) (hb0 n)) (mul_nonneg (hb0 n) (norm_nonneg _))
                    (by positivity)
              _ = b n * ((n : ℝ) + 2) ^ k * C m := by ring
          · rw [lmajABump_deriv_zero m _ (not_le.mp htn), norm_zero, mul_zero, mul_zero]
            have hCm : 0 ≤ C m := (norm_nonneg _).trans (hC m 0)
            exact mul_nonneg (mul_nonneg (hb0 n) (by positivity)) hCm
  refine ⟨⟨Complex.ofRealLI ∘ g, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealLI.contDiff.comp hgc
  · intro k m
    refine ⟨∑' n, b n * ((n : ℝ) + 2) ^ k * C m, fun t => ?_⟩
    rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hgc.contDiffAt (mod_cast le_top)]
    exact hdecay k m t
  · intro t
    show 0 ≤ (Complex.ofRealLI (g t)).re ∧ (Complex.ofRealLI (g t)).im = 0
    simp [hg0 t]
  · intro n t ht
    have h1 : (t - n) ∈ closedBall (0 : ℝ) lmajABump.rIn := by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; simpa [lmajABump] using ht
    have h2 : φ n t = b n := by rw [hφv, lmajABump.one_of_mem_closedBall h1, mul_one]
    show b n ≤ (Complex.ofRealLI (g t)).re
    simp only [Complex.ofRealLI_apply, Complex.ofReal_re]
    rw [← h2]
    exact (hφs t).le_tsum n (fun j _ => by rw [hφv]; exact mul_nonneg (hb0 j) (lmajABump.nonneg))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

theorem lmajASeq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) (q : V → ℝ) (hq0 : ∀ y, 0 ≤ q y) (A : ℝ) (hA : 0 ≤ A)
    (hqA : ∀ y, q y ≤ A * ‖y‖ ^ 2) :
    ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ (∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i y, (N : ℝ) ≤ q y → ‖f i y‖ ≤ ε * b ⌊q y⌋₊ := by
  set S : ℕ → ℝ := fun j => ∑ i, (Finset.Iic (2 * j, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i) with hS
  set D : ℕ → ℝ := fun j => (1 + A) ^ j * (2 ^ (2 * j) * S j) with hDdef
  have hS0 : ∀ j, 0 ≤ S j := fun j => Finset.sum_nonneg fun i _ => apply_nonneg _ _
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by positivity) (hS0 j))
  have hD : ∀ j i y, (1 + q y) ^ j * ‖f i y‖ ≤ D j := by
    intro j i y
    have h1 : 1 + q y ≤ (1 + A) * (1 + ‖y‖) ^ 2 := by
      have := hqA y; have hy := norm_nonneg y; nlinarith [mul_nonneg hA hy]
    have h2 : (1 + ‖y‖) ^ (2 * j) * ‖f i y‖ ≤ 2 ^ (2 * j) * S j := by
      have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * j, 0)) (k := 2 * j)
        (n := 0) le_rfl le_rfl (f i) y
      rw [norm_iteratedFDeriv_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Finset.single_le_sum (f := fun i => (Finset.Iic (2 * j, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (f i)) (fun i _ => apply_nonneg _ _)
        (Finset.mem_univ i)
    calc (1 + q y) ^ j * ‖f i y‖ ≤ ((1 + A) * (1 + ‖y‖) ^ 2) ^ j * ‖f i y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith [hq0 y]) h1 j) (norm_nonneg _)
      _ = (1 + A) ^ j * ((1 + ‖y‖) ^ (2 * j) * ‖f i y‖) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ D j := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
  set m : ℕ → ℝ := fun n => ⨅ j : ℕ, D j / (1 + (n : ℝ)) ^ j with hm
  have hbdd : ∀ n : ℕ, BddBelow (Set.range fun j : ℕ => D j / (1 + (n : ℝ)) ^ j) :=
    fun n => ⟨0, by rintro _ ⟨j, rfl⟩; exact div_nonneg (hD0 j) (by positivity)⟩
  have hm0 : ∀ n, 0 ≤ m n := fun n => le_ciInf fun j => div_nonneg (hD0 j) (by positivity)
  have hmle : ∀ n j, m n ≤ D j / (1 + (n : ℝ)) ^ j := fun n j => ciInf_le (hbdd n) j
  have hfm : ∀ i y, ‖f i y‖ ≤ m ⌊q y⌋₊ := by
    intro i y
    refine le_ciInf fun j => ?_
    rw [le_div_iff₀ (by positivity)]
    have hn : (⌊q y⌋₊ : ℝ) ≤ q y := Nat.floor_le (hq0 y)
    calc ‖f i y‖ * (1 + (⌊q y⌋₊ : ℝ)) ^ j ≤ (1 + q y) ^ j * ‖f i y‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j)
            (norm_nonneg _)
      _ ≤ D j := hD j i y
  set b : ℕ → ℝ := fun n => Real.sqrt (m n) with hb
  have hbdec : ∀ j n, b n ≤ Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
    intro j n
    have hpos : 0 < (1 + (n : ℝ)) ^ j := by positivity
    calc b n ≤ Real.sqrt (D (2 * j) / (1 + (n : ℝ)) ^ (2 * j)) := Real.sqrt_le_sqrt (hmle n (2 * j))
      _ = Real.sqrt (D (2 * j)) / (1 + (n : ℝ)) ^ j := by
          rw [Real.sqrt_div (hD0 _), pow_mul', Real.sqrt_sq hpos.le]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    refine ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).congr
      fun n => ?_
    push_cast; ring
  have hbs : ∀ j : ℕ, Summable (fun n : ℕ => b n * ((n : ℝ) + 2) ^ j) := by
    intro j
    refine (hsum2.mul_left (Real.sqrt (D (2 * (j + 2))) * 2 ^ j)).of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (fun n => ?_)
    have hpos : 0 < (1 + (n : ℝ)) := by positivity
    have h1 := hbdec (j + 2) n
    have h2 : ((n : ℝ) + 2) ^ j ≤ 2 ^ j * (1 + (n : ℝ)) ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) j
    calc b n * ((n : ℝ) + 2) ^ j ≤ Real.sqrt (D (2 * (j + 2))) / (1 + (n : ℝ)) ^ (j + 2) *
          (2 ^ j * (1 + (n : ℝ)) ^ j) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.sqrt (D (2 * (j + 2))) * 2 ^ j * (1 / ((n : ℝ) + 1) ^ 2) := by
          field_simp; ring
  refine ⟨b, fun n => Real.sqrt_nonneg _, hbs, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (D (2 * 1)) / ε)
  refine ⟨N, fun i y hy => ?_⟩
  have hNn : N ≤ ⌊q y⌋₊ := Nat.le_floor hy
  have hbε : b ⌊q y⌋₊ ≤ ε := by
    have h1 := hbdec 1 ⌊q y⌋₊
    rw [pow_one] at h1
    have hNr : (N : ℝ) ≤ (⌊q y⌋₊ : ℝ) := by exact_mod_cast hNn
    have h3 := (div_lt_iff₀ hε).mp hN
    have h4 : Real.sqrt (D (2 * 1)) / (1 + (⌊q y⌋₊ : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  calc ‖f i y‖ ≤ m ⌊q y⌋₊ := hfm i y
    _ = b ⌊q y⌋₊ * b ⌊q y⌋₊ := (Real.mul_self_sqrt (hm0 _)).symm
    _ ≤ ε * b ⌊q y⌋₊ := mul_le_mul_of_nonneg_right hbε (Real.sqrt_nonneg _)

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

namespace PositivityTheory.Rg.Rsw.L.LMajor

open Metric
open scoped ContDiff

theorem schMajor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (f : Fin k → SchwartzMap V ℂ) :
    ∃ F₀ : SchwartzMap V ℂ, (∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : V → ℂ, c.HasTemperateGrowth ∧ HasCompactSupport c ∧
        ∀ i y, ‖f i y‖ * ‖1 - c y‖ ≤ ε * (F₀ y).re := by
  classical
  set e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean with he
  set q : V → ℝ := fun y => ‖e y‖ ^ 2 with hqdef
  have hqy : ∀ y, q y = ‖e y‖ ^ 2 := fun y => rfl
  have hq0 : ∀ y, 0 ≤ q y := fun y => by rw [hqy]; positivity
  have hq : q.HasTemperateGrowth :=
    (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).comp
      e.hasTemperateGrowth
  have hq_upper : ∃ (k : ℕ) (C : ℝ), ∀ y, ‖y‖ ≤ C * (1 + ‖q y‖) ^ k := by
    refine ⟨1, ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖, fun y => ?_⟩
    have h1 : ‖y‖ ≤ ‖(e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)‖ * ‖e y‖ := by
      have := (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V).le_opNorm (e y)
      simpa using this
    have h2 : ‖e y‖ ≤ 1 + ‖q y‖ := by
      rw [Real.norm_of_nonneg (hq0 y), hqy]
      nlinarith [sq_nonneg (‖e y‖ - 1), norm_nonneg (e y)]
    rw [pow_one]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hqA : ∀ y, q y ≤ ‖(e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖ ^ 2 * ‖y‖ ^ 2 := by
    intro y
    rw [hqy, ← mul_pow]
    have := (e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))).le_opNorm y
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using this) 2
  obtain ⟨b, hb0, hbs, hbε⟩ := lmajASeq f q hq0 _ (sq_nonneg _) hqA
  obtain ⟨h, hh0, hhb⟩ := lmajASeqSchwartz b hb0 hbs
  set F₀ : SchwartzMap V ℂ := SchwartzMap.compCLM ℝ hq hq_upper h with hF₀
  have hF : ∀ y, F₀ y = h (q y) := fun y => rfl
  refine ⟨F₀, fun y => by rw [hF]; exact hh0 _, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hbε ε hε
  let β : ContDiffBump (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    ⟨(N : ℝ) + 1, (N : ℝ) + 2, by positivity, by linarith⟩
  set c : V → ℂ := fun y => ((β (e y) : ℝ) : ℂ) with hc
  have hcd : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp ((β.contDiff).comp e.contDiff)
  have hcs : HasCompactSupport c :=
    (β.hasCompactSupport.comp_homeomorph e.toHomeomorph).comp_left Complex.ofReal_zero
  refine ⟨c, hcs.hasTemperateGrowth hcd, hcs, fun i y => ?_⟩
  have hF0 : 0 ≤ (F₀ y).re := by rw [hF]; exact (hh0 _).1
  by_cases hy : ‖e y‖ ≤ (N : ℝ) + 1
  · have hβ : β (e y) = 1 :=
      β.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hy)
    have hc1 : c y = 1 := by simp [hc, hβ]
    rw [hc1, sub_self, norm_zero, mul_zero]
    exact mul_nonneg hε.le hF0
  · push Not at hy
    have hqN : (N : ℝ) ≤ q y := by
      rw [hqy]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have h1c : ‖1 - c y‖ ≤ 1 := by
      have : (1 : ℂ) - c y = ((1 - β (e y) : ℝ) : ℂ) := by simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [β.nonneg (x := e y), β.le_one (x := e y)]
    have hqn : |q y - (⌊q y⌋₊ : ℝ)| ≤ 1 := by
      have h1 := Nat.floor_le (hq0 y)
      have h2 := Nat.lt_floor_add_one (q y)
      rw [abs_le]; constructor <;> linarith
    calc ‖f i y‖ * ‖1 - c y‖ ≤ ‖f i y‖ := mul_le_of_le_one_right (norm_nonneg _) h1c
      _ ≤ ε * b ⌊q y⌋₊ := hN i y hqN
      _ ≤ ε * (F₀ y).re := by rw [hF]; exact mul_le_mul_of_nonneg_left (hhb _ _ hqn) hε.le

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem repr_map {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem infPart_eq_of {e e' : AE D}
    (h : ∀ w, compInf D.host.F D.host.E w e = compInf D.host.F D.host.E w e') : infPart D e = infPart D e' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e =
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e'
  apply (Algebra.TensorProduct.basis (Ainf D.host.F) b).repr.injective
  refine Finsupp.ext fun k => ?_
  rw [repr_map, repr_map]
  funext w
  have h1 := repr_map (evInf D.host.F w) b e k
  have h2 := repr_map (evInf D.host.F w) b e' k
  have hw : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e' := h w
  rw [hw, h2] at h1
  exact h1.symm

theorem infPart_idem {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : infPart D e = 1 :=
  (infPart_eq_of (e' := 1) fun w => (he.1 w).trans (map_one _).symm).trans (map_one _)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem cv_eq (v : Pl D) (a : AE D) :
    cv D v a = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
      (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add, hx, hy, RingHom.map_add, map_add]
  | tmul x y =>
    show Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y))
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl

theorem cv_congr (v : Pl D) {a a' : AE D} (h : finPart D a = finPart D a') : cv D v a = cv D v a' := by
  rw [cv_eq, cv_eq, h]

def afF (D : D7) : AF D.host.F := (0, 1)

theorem fstA_afF : fstA D.host.F (afF D) = 0 := rfl

theorem sndA_afF : sndA D.host.F (afF D) = 1 := rfl

def sF (D : D7) : AE D := afF D ⊗ₜ[D.host.F] (1 : D.host.E)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem infPart_sF : infPart D (sF D) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul, fstA_afF, TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem finPart_sF : finPart D (sF D) = 1 := by
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul, sndA_afF]
  rfl

theorem compAt_smul (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (c : AE D) (x : Mx D m n) :
    compAt θ τ (c • x) = θ τ (infPart D c) • compAt θ τ x := by
  ext i j
  simp [compAt, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem prodSB {X : Type} [TopologicalSpace X] {a b : ℕ} (G : Fin a → (Fin 1 → Fin b → X) → ℂ)
    (hG : ∀ i, G i ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → X)) :
    (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → X) := by
  have hG' : ∀ i, IsLocallyConstant (G i) ∧ HasCompactSupport (G i) := hG
  have hrow : ∀ i : Fin a, Continuous fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j) :=
    fun i => continuous_pi fun _ => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)
  show IsLocallyConstant (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∧
    HasCompactSupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j))
  refine ⟨?_, ?_⟩
  · have hfun : (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) =
        ∏ i, (fun z : Fin a → Fin b → X => G i (fun _ j => z i j)) := by
      funext z
      rw [Finset.prod_apply]
    rw [hfun]
    exact Finset.prod_induction _ IsLocallyConstant (fun f g hf hg => hf.comp₂ hg (· * ·))
      (IsLocallyConstant.const 1) (fun i _ => (hG' i).1.comp_continuous (hrow i))
  · let S : Set (Fin a → Fin b → X) := ⋂ i, (fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j)) ⁻¹' tsupport (G i)
    let gm : (Fin a → Fin 1 → Fin b → X) → (Fin a → Fin b → X) := fun w i j => w i 0 j
    have hgm : Continuous gm :=
      continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply 0).comp (continuous_apply i))
    have hK : IsCompact (gm '' Set.univ.pi fun i => tsupport (G i)) :=
      (isCompact_univ_pi fun i => (hG' i).2).image hgm
    have hSc : IsClosed S := isClosed_iInter fun i => (isClosed_tsupport (G i)).preimage (hrow i)
    have hsub : tsupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro z hz
      have hz' : ∏ i, G i (fun _ j => z i j) ≠ 0 := hz
      rw [Finset.prod_ne_zero_iff] at hz'
      exact Set.mem_iInter.2 fun i => subset_tsupport _ (hz' i (Finset.mem_univ i))
    have hSK : S ⊆ gm '' Set.univ.pi fun i => tsupport (G i) := by
      intro z hz
      refine ⟨fun i _ j => z i j, fun i _ => Set.mem_iInter.1 hz i, rfl⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

theorem rowSB (θ : InfFam D) {m n : ℕ} (s : AE D) (hs : infPart D s = 0) (hs' : finPart D s = 1)
    (h : Mx D m n → ℂ) (hh : h ∈ schwartzA θ m n) :
    ∃ G ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E),
      ∀ y : Mx D m n, h (s • y) = G (fun i j => finPart D (y i j)) := by
  change h ∈ Submodule.span ℂ _ at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨f (fun _ _ _ => 0) • g, Submodule.smul_mem _ _ hg, fun y => ?_⟩
    have h1 : (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) = fun _ _ _ => (0 : ℂ) := by
      funext τ i j
      have hc : Formalism.IndefR.Datum.compAt θ τ (s • y) i j = θ τ (Formalism.L2.Theta.infPart D (s * y i j)) := rfl
      rw [hc, map_mul, hs, zero_mul, map_zero]
    have h2 : (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = fun i j => Formalism.L2.Theta.finPart D (y i j) := by
      funext i j
      have hc : Formalism.L2.Theta.finPart D ((s • y) i j) = Formalism.L2.Theta.finPart D (s * y i j) := rfl
      rw [hc, map_mul, hs', one_mul]
    show f (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) *
        g (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = _
    rw [h1, h2, Pi.smul_apply, smul_eq_mul]
  | zero => exact ⟨0, Submodule.zero_mem _, fun y => rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨G1, hG1, e1⟩ := hx
    obtain ⟨G2, hG2, e2⟩ := hz
    exact ⟨G1 + G2, Submodule.add_mem _ hG1 hG2, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨G1, hG1, e1⟩ := hx
    exact ⟨c • G1, Submodule.smul_mem _ _ hG1, fun y => by rw [Pi.smul_apply, Pi.smul_apply, e1]⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

abbrev cA (θ : InfFam D) (x : Mx D a b) : D.what₂.Tau → Fin a → Fin b → ℂ := fun τ i j => compAt θ τ x i j

abbrev row (i : Fin a) (x : Mx D a b) : Mx D 1 b := x.submatrix (fun _ => i) id

theorem cA_idem (θ : InfFam D) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (x : Mx D a b) :
    cA θ (e • x) = cA θ x := by
  funext τ i j
  rw [cA, compAt_smul, infPart_idem he, map_one, one_smul]

theorem cv_sF (v : Pl D) (z : AE D) : cv D v (sF D * z) = cv D v z :=
  cv_congr v (by rw [map_mul, finPart_sF, one_mul])

theorem good_mul (θ : InfFam D) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {Φ : Mx D a b → ℂ}
    (hG : Good S e Φ) (q : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ) : Good S e (fun x => q (cA θ x) * Φ x) := by
  intro x
  have h := hG x
  split_ifs at h ⊢ with hx
  · show q (cA θ x) * Φ x = q (cA θ (e • x)) * Φ (e • x)
    rw [h, cA_idem θ he]
  · show q (cA θ x) * Φ x = 0
    rw [h, mul_zero]

theorem re_im_mul {z w : ℂ} (hz : 0 ≤ z.re ∧ z.im = 0) (hw : 0 ≤ w.re ∧ w.im = 0) :
    0 ≤ (z * w).re ∧ (z * w).im = 0 := by
  rw [Complex.mul_re, Complex.mul_im, hz.2, hw.2]
  exact ⟨by simpa using mul_nonneg hz.1 hw.1, by simp⟩

theorem re_im_prod {ι : Type} (s : Finset ι) (u : ι → ℂ) (h : ∀ i, 0 ≤ (u i).re ∧ (u i).im = 0) :
    0 ≤ (∏ i ∈ s, u i).re ∧ (∏ i ∈ s, u i).im = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact re_im_mul (h i) ih

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

theorem row_smul (i : Fin a) (c : AE D) (x : Mx D a b) : row i (c • x) = c • row i x := by
  rfl

theorem intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) (i : Fin a) : IntOff S (row i (sF D • x)) := by
  intro v hv i' j
  show cv D v (sF D * x i j) ∈ _
  rw [cv_sF]
  exact hx v hv i j

theorem not_intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : ¬ IntOff S x) :
    ∃ i, ¬ IntOff S (row i (sF D • x)) := by
  by_contra hcon
  push Not at hcon
  apply hx
  intro v hv i j
  have e := hcon i v hv 0 j
  have e' : cv D v (sF D * x i j) ∈ GlobalTheory.AdelicU.intLoc (↥D.host.F) D.host.E v := e
  rwa [cv_sF] at e'

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in

theorem bumpMaj (hB : BumpEx) (θ : InfFam D) (hθ : IsInfFam θ) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (K : Set (Mx D a b)) (hK : IsCompact K) (F₀ : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (hF₀ : ∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) :
    ∃ Φ₀ ∈ schwartzA θ a b, Good S e Φ₀ ∧ (∀ x, 0 ≤ (Φ₀ x).re ∧ (Φ₀ x).im = 0) ∧
      ∀ x, IntOff S x → GlobalTheory.Unf.InBox K x → Φ₀ x = F₀ (cA θ x) := by
  have hCint : ∀ y ∈ (fun k => sF D • (e • k)) '' K, IntOff S y := by
    rintro _ ⟨k, -, rfl⟩ v hv i j
    show cv D v (sF D * (e * k i j)) ∈ _
    rw [cv_sF, map_mul, he.2 v, if_neg hv, zero_mul]
    exact (GlobalTheory.AdelicU.intLoc _ _ v).zero_mem
  obtain ⟨η, hη⟩ := hB D θ hθ a b S e he _
    (hK.image ((continuous_const_smul (sF D)).comp (continuous_const_smul e))) hCint
  have hG : ∀ i, ∃ G ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E),
      ∀ y : Mx D 1 b, η i (sF D • y) = G fun i' j => finPart D (y i' j) :=
    fun i => rowSB θ (sF D) infPart_sF finPart_sF (η i) (hη i).1
  choose G hGSB hGeq using hG
  set Ψ : Mx D a b → ℂ := fun x => ∏ i, η i (sF D • row i x) with hΨ
  have hΨG : ∀ x, Ψ x = (fun z => ∏ i, G i fun _ j => z i j) (fun i j => finPart D (x i j)) := by
    intro x
    exact Finset.prod_congr rfl fun i _ => hGeq i (row i x)
  have hΨgood : Good S e Ψ := by
    intro x
    by_cases hx : IntOff S x
    · rw [if_pos hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, ← row_smul, smul_comm e (sF D) x]
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_intOff_row hx
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [← row_smul, (hη i).2.2.1, if_neg hi]
  refine ⟨fun x => F₀ (cA θ x) * Ψ x, ?_, good_mul θ he hΨgood (fun z => F₀ z), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨F₀, fun z => ∏ i, G i fun _ j => z i j, prodSB G hGSB, ?_⟩
    funext x
    rw [hΨG x]
  · intro x
    exact re_im_mul (hF₀ _) (re_im_prod _ _ fun i => ⟨((hη i).2.2.2.1 _).1, ((hη i).2.2.2.1 _).2.2⟩)
  · rintro x hx ⟨k, hk, hxk⟩
    have hfin : ∀ i j, finPart D (x i j) = finPart D (k i j) := by
      intro i j
      have h0 := congrFun (congrFun hxk i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at h0
      exact sub_eq_zero.mp h0
    suffices h1 : Ψ x = 1 by
      show F₀ (cA θ x) * Ψ x = F₀ (cA θ x)
      rw [h1, mul_one]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, smul_comm e (sF D) x, row_smul, hGeq i]
    have hfun : (fun i' j => finPart D ((row i (e • x)) i' j)) = (fun i' j => finPart D ((row i (e • k)) i' j)) := by
      funext i' j
      show finPart D (e * x i j) = finPart D (e * k i j)
      rw [map_mul, map_mul, hfin]
    rw [hfun, ← hGeq i, ← row_smul]
    exact (hη i).2.2.2.2 _ ⟨k, hk, rfl⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem cutSupp (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (K : Set (Mx D a b)) (hK : IsCompact K)
    (Φ : Mx D a b → ℂ) (hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x) (c : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ)
    (hc : HasCompactSupport c) : HasCompactSupport (fun x => c (fun τ i j => compAt θ τ x i j) * Φ x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ)
  obtain ⟨hcl, hcont, -, hcpt⟩ := (GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 a b K hK
  set R' : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin a, ∑ _j : Fin b, R with hR'
  refine HasCompactSupport.intro' (hcpt R') (hcl.inter (isClosed_le hcont continuous_const)) fun x hx => ?_
  by_contra hne
  have hc0 : c (fun τ i j => compAt θ τ x i j) ≠ 0 := left_ne_zero_of_mul hne
  have hΦ : Φ x ≠ 0 := right_ne_zero_of_mul hne
  have hmem : (fun τ i j => compAt θ τ x i j) ∈ Metric.closedBall (0 : D.what₂.Tau → Fin a → Fin b → ℂ) R :=
    hR (subset_tsupport _ hc0)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  apply hx
  refine ⟨hbox x hΦ, ?_⟩
  show GlobalTheory.Unf.realSize θ x ≤ R'
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 := norm_le_pi_norm (fun τ i j => compAt θ τ x i j) τ
  have h2 := norm_le_pi_norm (fun i j => compAt θ τ x i j) i
  have h3 := norm_le_pi_norm (fun j => compAt θ τ x i j) j
  exact h3.trans (h2.trans (h1.trans hmem))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem domBound (θ : InfFam D) (hθ : IsInfFam θ) {a b : ℕ} (Φ : Mx D a b → ℂ) (hΦ : Φ ∈ schwartzA θ a b) :
    ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ) (M : ℝ), 0 ≤ M ∧
      ∀ x, ‖Φ x‖ ≤ M * ∑ i, ‖f i (fun τ i j => compAt θ τ x i j)‖ := by
  obtain ⟨-, k, f, g, hg, hb⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ a b Φ hΦ
  choose C hC using fun i => ((hg i).1.continuous).bounded_above_of_compact_support (hg i).2
  refine ⟨k, f, ∑ i, max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun x => ?_⟩
  have h1 : ‖Φ x‖ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ := by
    have h := hb x
    simp only [enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe] at h
    have h' : ((‖Φ x‖₊ : NNReal) : ℝ) ≤ ((∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) *
        g i (fun i' j => finPart D (x i' j))‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr h
    simpa only [coe_nnnorm, NNReal.coe_sum] using h'
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_comm (∑ i, max (C i) 0)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (hC i _).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun i => max (C i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ i)))

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LMajor in
theorem major : IdemEx → GoodEv → BumpEx → Major := by
  intro _ _ hB D θ hθ a b S e he Φ hΦ hG
  obtain ⟨k, f, M, hM, hdom⟩ := domBound θ hθ Φ hΦ
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ a b Φ (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ a b Φ hΦ)
  obtain ⟨C0, hC0⟩ := hmaj 0
  have hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x := by
    intro x hx
    by_contra hb
    have h := hC0 x
    rw [GlobalTheory.Unf.maj, if_neg hb, mul_zero] at h
    exact hx (norm_le_zero_iff.mp h)
  obtain ⟨F₀, hF₀, hcut⟩ := schMajor f
  obtain ⟨Φ₀, hΦ₀, hG₀, hpos, heq⟩ := bumpMaj hB θ hθ he K hK F₀ hF₀
  refine ⟨Φ₀, hΦ₀, hG₀, hpos, fun ε hε => ?_⟩
  have hMk : 0 < M * k + 1 := by have := mul_nonneg hM (Nat.cast_nonneg (α := ℝ) k); linarith
  obtain ⟨c, hct, hcc, hcb⟩ := hcut (ε / (M * k + 1)) (div_pos hε hMk)
  refine ⟨fun x => c (cA θ x) * Φ x, GlobalTheory.T.temperate_multiplier_preserves_schwartz D θ a b c hct Φ hΦ, good_mul θ he hG c,
    cutSupp θ hθ K hK Φ hbox c hcc, fun x => ?_⟩
  show ‖Φ x - c (cA θ x) * Φ x‖ ≤ ε * (Φ₀ x).re
  rw [show Φ x - c (cA θ x) * Φ x = (1 - c (cA θ x)) * Φ x by ring, norm_mul]
  by_cases h0 : Φ x = 0
  · rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hε.le (hpos x).1
  have hx : IntOff S x := by
    by_contra hx
    have h := hG x
    rw [if_neg hx] at h
    exact h0 h
  rw [heq x hx (hbox x h0)]
  have hF : 0 ≤ (F₀ (cA θ x)).re := (hF₀ _).1
  calc ‖1 - c (cA θ x)‖ * ‖Φ x‖ ≤ ‖1 - c (cA θ x)‖ * (M * ∑ i, ‖f i (cA θ x)‖) :=
        mul_le_mul_of_nonneg_left (hdom x) (norm_nonneg _)
    _ = M * ∑ i, ‖f i (cA θ x)‖ * ‖1 - c (cA θ x)‖ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ M * ∑ _i : Fin k, ε / (M * k + 1) * (F₀ (cA θ x)).re := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcb i _) hM
    _ = (M * k) / (M * k + 1) * (ε * (F₀ (cA θ x)).re) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 1 * (ε * (F₀ (cA θ x)).re) := by
        gcongr
        rw [div_le_one hMk]
        linarith
    _ = ε * (F₀ (cA θ x)).re := one_mul _

end PositivityTheory.Rg.Rsw.L

end
end
