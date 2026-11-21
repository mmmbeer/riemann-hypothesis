import Formalism.PeriodIntegrals.DSInfCharCap

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

abbrev Sm {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ

def QdetConjInv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit g → ∀ u : ℂ,
      Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (g c a * g⁻¹ b d) • E c d) u = Formalism.REAL.qdet E u

def CentralScalar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsDS ε lam σ →
    ∀ u : ℂ, ∃ c : ℂ, ∀ v ∈ Sm ε σ, actU ε σ (Formalism.REAL.qdet (Egl n) u) v = c • v

end PI.UnitaryGroupMassFormula.DSIC
