import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open MeasureTheory GlobalTheory.SUVol
open scoped ENNReal

variable {ι : Type} {r : ℕ}

def lieBall (H : ι → Matrix (Fin r) (Fin r) ℂ) (ρ : ℝ) : Set (suLie H) := {X | ∀ i a b, ‖X.1 i a b‖ ≤ ρ}

def trVol [Fintype ι] {H : ι → Matrix (Fin r) (Fin r) ℂ} {n : ℕ} (b : Module.Basis (Fin n) ℝ (suLie H))
    (A : Set (suLie H)) : ℝ≥0∞ :=
  ENNReal.ofReal √|(Matrix.of fun k l => trForm (b k).1 (b l).1).det| * volume (b.equivFun '' A)

def IsSignMat (J : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ e : Fin r → ℂ, (∀ a, e a = 1 ∨ e a = -1) ∧ J = Matrix.diagonal e

end GlobalTheory.CompanionTheory.Ar.abelian₂
