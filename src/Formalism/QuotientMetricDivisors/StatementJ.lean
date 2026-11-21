import Mathlib
import Formalism.QuotientMetricDivisors.StatementACE
import Formalism.LogFactorialIndices.StatementSize

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def DivAssembly : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Lpass logκ Fo Eb hu hP mlam e6 eP logOm logT kk : ℝ)
    (hK eK pq : J → ℝ) (a : Pl → ℝ) (w phν nν fa eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam - logκ →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, a t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then a ρ else 0) + kk * w j ρ + δ j ρ) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, ((Fintype.card J : ℝ) * (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - a t * logT) +
        (Lpass + Eb + ∑ j, eK j + e6 + eP + ∑ j, ∑ ρ, eE j ρ) +
        ∑ j, ∑ ρ, |pq j - kk| * |w j ρ| * |logOm| + ∑ j, ∑ ρ, |δ j ρ| * |logOm|

end Formalism.DivisionValues
