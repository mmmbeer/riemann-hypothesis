import Formalism.FormalDegreeBessel.StatementDS

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

def dimLowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
    (((lowK ε lam + rhoC ε) a - (lowK ε lam + rhoC ε) b) / (rhoC ε a - rhoC ε b))

def FdegFactorial : Prop :=
  ∀ n : ℕ, (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
    ∏ i ∈ range n, (i.factorial : ℝ)

def FdegDimV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)) /
      ∏ i ∈ range n, (i.factorial : ℝ)

def HolDimLowK : Prop :=
  ∀ (n : ℕ) (a b : ℝ), dimLowK (epsHol n) (lamHol n a b) = 1

end Formalism.QuantumDeterminants
