import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Short

open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0

variable (F : Type) [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] (D : ℕ) {N : ℕ}

variable {F D} in

def InS (g : MvPolynomial (TVar D N) F) : Prop := ∀ p ∈ g.vars, p.1 ≠ 0

variable {F D} in

def IsGroupHomog (δ : ℕ) (G : MvPolynomial (TVar D N) F) : Prop :=
  ∀ i : Fin (D + 1), G.IsWeightedHomogeneous (fun p : TVar D N => if p.1 = i then 1 else 0) δ

example (c : F) : InS (C c : MvPolynomial (TVar D N) F) := fun p hp => by simp [vars_C] at hp

end GlobalTheory.CompanionTheory.Ar.Short
