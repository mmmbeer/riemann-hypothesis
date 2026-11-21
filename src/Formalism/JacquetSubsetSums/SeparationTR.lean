import Mathlib
import Formalism.QuotientMetricDivisors.Statement
import Formalism.JacquetSubsetSums.JacquetSubsetSum

open Module NumberField

noncomputable section

namespace Formalism.PacketSums

def SeparationTR : Prop :=
  ∀ (HH : Type) (r : ℕ) (Sg Pu : Type) [Fintype Sg] [Fintype Pu]
    (chr : Sg → HH → ℂ) (Ex : Pu → (Multiplicative (Fin r → ℤ) →* ℂ) →₀ ℂ)
    (trI : Pu → (Fin r → ℤ) → ℂ) (cst : (Fin r → ℤ) → ℂ) (m m' : Sg → Pu → ℕ),
    LinearIndependent ℂ chr → LinearIndependent ℂ Ex →
    (∀ a, StrictAnti a → cst a ≠ 0) →
    (∀ π a, StrictAnti a →
      trI π a = cst a * ((Ex π).sum fun χ z => z * χ (Multiplicative.ofAdd a))) →
    (∀ h a, StrictAnti a →
      (∑ σ, ∑ π, (m σ π : ℂ) * chr σ h * trI π a) = ∑ σ, ∑ π, (m' σ π : ℂ) * chr σ h * trI π a) →
    m = m'

end Formalism.PacketSums
