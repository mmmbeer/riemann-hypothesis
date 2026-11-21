import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.FC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

abbrev Fam (E : Type) [Field E] [NumberField E] (a b : ℕ) : Type := ∀ w : Pl E, GLw a w × GLw b w → ℂ

def cvL (φ ψ : Fam E a b) : Fam E a b := fun w y => hint (K2 a b w) fun z => φ w z * ψ w (z⁻¹ * y)

def adL (φ : Fam E a b) : Fam E a b := fun w y => starRingEnd ℂ (φ w y⁻¹)

def FinTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ φ₁ φ₂ : Fam E a b, IsTestP φ₁ → IsTestP φ₂ → Continuous (finFn S φ₁ φ₂) ∧ HasCompactSupport (finFn S φ₁ φ₂) ∧
    ∃ U : Subgroup (Gf E a b), IsOpen (U : Set (Gf E a b)) ∧ IsCompact (U : Set (Gf E a b)) ∧
      ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u * y) = finFn S φ₁ φ₂ y ∧ finFn S φ₁ φ₂ (y * u) = finFn S φ₁ φ₂ y

def FinConv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ [MeasurableSpace (Gf E a b)] [BorelSpace (Gf E a b)] (ν : Measure (Gf E a b)) [ν.IsHaarMeasure]
    (φ₁ φ₂ ψ₁ ψ₂ : Fam E a b), IsTestP φ₁ → IsTestP φ₂ → IsTestP ψ₁ → IsTestP ψ₂ → ∀ g,
    ∫ h, finFn S φ₁ φ₂ h * finFn S ψ₁ ψ₂ (h⁻¹ * g) ∂ν =
      ((ν (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b))).toReal : ℂ) *
        finFn S (cvL φ₁ ψ₁) (cvL φ₂ ψ₂) g

end PositivityTheory.Rg.BcB.FC

end
