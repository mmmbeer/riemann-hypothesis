import Mathlib
import Formalism.LogFactorialIndices.StatementSize

open Finset
open scoped Real

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def SizeAtEmbedding : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (r g0 : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (Om : Pl → ℝ)
    (Ksq kc Msq Th0sq hh : ℝ),
    0 < Ksq → 0 < kc → 0 < Msq → 0 < Th0sq → 0 < hh → (∀ τ, 0 < Om τ) →
    Ksq ≤ hh * ((kc ^ 2 * Msq * Th0sq) * ∏ τ, ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))))) →
    Real.log Ksq ≤ (∑ τ, ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ))) + Real.log Th0sq +
      (Real.log Msq + 2 * Real.log kc + (∑ τ, (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2))) +
        Real.log hh)

def PeriodValue : Prop :=
  ∀ d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm : ℝ, 0 < d → 0 < v → rdE = 2 * v →
    Z = Real.log (2 / Real.sqrt d) + (A1 + Real.log π) →
    Z = Real.log (2 * π) + LL0 →
    LL0 = -p_power_smul_sub_sum - Real.log (d / π) + Real.eulerMascheroniConstant + Real.log 2 →
    logOmK = A1 →
    logOm = logOmK - Real.log rdE + Real.log (Real.sqrt d) →
    A1 = LL0 + Real.log d / 2 ∧
    logOmK = Real.eulerMascheroniConstant + Real.log (2 * π / Real.sqrt d) - p_power_smul_sub_sum ∧
    logOm = Real.eulerMascheroniConstant + Real.log (π / v) - p_power_smul_sub_sum

end Formalism.DimensionVariation
