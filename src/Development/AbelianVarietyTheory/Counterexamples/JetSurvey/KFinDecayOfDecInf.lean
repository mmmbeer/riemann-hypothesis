import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction

open Formalism.FourierDecayAlt.ThreeDimData

namespace GlobalTheory.GapSizeCheck


theorem thresholds (k r : ℕ) (h : ℝ) (hg : GapOK k r h) :
    AG k r < (aOf r h - 1) / 2 ∧ AS k r < (aOf r h - 1) / 2 ∧
      (2 * Mexp r * AS k r + 1) + AG k r + 1 ≤ aOf r h - 1 := by
  obtain ⟨hk, -, h3, -⟩ := hg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hG0 : 0 ≤ AG k r := by unfold AG; positivity
  have hd0 : 0 ≤ dN k r := by unfold dN; nlinarith [mul_nonneg hr hk0]
  have hS0 : 0 ≤ AS k r := by unfold AS; positivity
  have hM : 2 ≤ Mexp r := by unfold Mexp; nlinarith
  have e1 : 2 * AS k r ≤ Mexp r * AS k r := mul_le_mul_of_nonneg_right hM hS0
  have e2 : 2 * AG k r ≤ Mexp r * AG k r := mul_le_mul_of_nonneg_right hM hG0
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem decay_range (k r : ℕ) (h : ℝ) (h120 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : Real.sqrt ((r : ℝ) + 1) ≤ (r : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : (r : ℝ) + 1 ≤ n := by rw [hn]; push_cast; linarith
  have : ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) ≤ n * n :=
    mul_le_mul hn1 (hs.trans hn1) (Real.sqrt_nonneg _) (by linarith)
  nlinarith

open scoped InnerProductSpace in

def KFinDecay {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ u v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ u → PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
    ∃ C : ℝ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ x u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a)

open scoped InnerProductSpace in

def SmoothDecayOfKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (a : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → KFinDecay (k := k) (r := r) σ a →
    ∀ v0 : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v0 →
      ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
        ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          ‖⟪v0, σ x w⟫_ℂ‖ ≤
            C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a)

end GlobalTheory.GapSizeCheck
