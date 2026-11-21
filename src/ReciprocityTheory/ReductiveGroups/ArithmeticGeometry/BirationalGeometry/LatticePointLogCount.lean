import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial NumberField MeasureTheory

section Lattice

variable {r : ℕ}

end Lattice

section Sections

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {r : ℕ}

end Sections

section ChowForm

variable {o : Type*} [CommRing o] {e n : ℕ}

def IsChowForm (σ : o →+* ℂ) (I : Ideal (MvPolynomial (Fin n) o)) (e δ : ℕ)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) : Prop :=
  IsMultihomog f δ ∧ Squarefree f ∧
    ∀ u : Fin (e + 1) → Fin n → ℂ,
      eval (fun p => u p.1 p.2) f = 0 ↔ ∃ z ∈ conePts σ I, ∀ j, ∑ i, u j i * z i = 0

end ChowForm

end ReciprocityTheory.ChartRestriction.G.Geo
