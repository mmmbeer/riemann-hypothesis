import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

def OverPair (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ) : Prop :=
  (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (x : E))‖ < 1) ∨
    (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (IsCMField.complexConj E (x : E)))‖ < 1)

end GlobalTheory.CongW
