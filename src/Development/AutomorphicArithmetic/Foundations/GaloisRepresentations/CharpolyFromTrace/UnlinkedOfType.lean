import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.OfVecFixedIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori

namespace UpperTheory.Gal.NearKilling

end UpperTheory.Gal.NearKilling
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong
open UpperTheory.Gal.CharacterCongruences (Ch PolyApproxAt)

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {Γ I : Type} [Group Γ] [Group I] {a c : ℕ}

end Abstract

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

end Global

def DenseFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite →
    Dense {g : G E Ω | ∃ u, IsSplitAt u ∧ u ∉ S ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ IsFrob A (normV u) g⁻¹}

def UnlinkedOfType : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = a) (θ : Fin c → (𝓀[w.adicCompletion E])ˣ →* ℂˣ), (∀ b, 0 < d b) →
      Function.Injective θ → HasTypeVec σ.ρ (stdBlocks d hd) θ →
      ∃ (ξ : Fin a → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
        HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ hξ) ∧ GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ) ∧
        ∀ j, IsTameLift (ξ j) (θ (blockOf d hd j))

def UnrField : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ f : ℕ, 0 < f → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∃ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → normV w' = normV w ^ f) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt u → ∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ τ ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K τ

def IneNorm : Prop :=
  ∀ (E M Ω : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω]
    [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] (h : IsPlaceOver A v) (h' : IsPlaceOver A w),
    (∀ t ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) M t) → ∀ art art', IsLocalArtin h art → IsLocalArtin h' art' →
    ∃ g : ↥(Ine (F := E) A) ≃* ↥(Ine (F := M) A), (∀ s, UpperTheory.V.Af.Bc.res E Ω M (g s : G M Ω) = s) ∧
      ∀ s, art (ineIncl h s) = GlobalTheory.BCChar.normU v w (art' (ineIncl h' (g s)))

end UpperTheory.Gal.NearKilling
end
end
