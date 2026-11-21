import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

section Fun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Fun

section Scalar

end Scalar

section Good

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {φ : E →L[ℂ] ℂ}

end Good

section Central

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

end Central

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

end ReciprocityTheory.ChartRestriction.DS.G2
