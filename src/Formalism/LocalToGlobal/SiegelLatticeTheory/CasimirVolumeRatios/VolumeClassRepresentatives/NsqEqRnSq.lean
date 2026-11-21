import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.SobTEqSobTM
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CasScalar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.GenApplyZero

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace Formalism.L2.S.S7.CasimirNormBounds

open Formalism.MainNotions.S Formalism.REAL Formalism.L2.SG.Pf.admitted

variable {n : ℕ}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def OmKg (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a : H) : H :=
  -∑ p : Fin n × Fin n, if ε p.1 = ε p.2 then
    ((wt p : ℝ) : ℂ) • dS σ (gen ε p) (dS σ (gen ε p) a) else 0

end Formalism.L2.S.S7.CasimirNormBounds

namespace Formalism.L2.S.S7.CasimirNormBounds

open Formalism.MainNotions.S Formalism.REAL Formalism.L2.SG.Pf.admitted

def KTypeShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∀ a ∈ S, ∀ E : Matrix (Fin n) (Fin n) ℂ, inG ε E →
      ∃ a' : H, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • E)) a) a' 0 ∧
        a' ∈ sSup {S' : Submodule ℂ H | ∃ μ', IsKTypeOf ε σ μ' S' ∧ nsq (μ' - μ) ≤ 2}

end Formalism.L2.S.S7.CasimirNormBounds
