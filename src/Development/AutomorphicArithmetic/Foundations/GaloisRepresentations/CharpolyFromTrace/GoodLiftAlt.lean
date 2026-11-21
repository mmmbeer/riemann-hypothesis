import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleOfRestrictNormalFiniteIndex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem aeval_prodMap' {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : Module.End ℂ V) (g : Module.End ℂ V') (q : ℂ[X]) :
    aeval (f.prodMap g : Module.End ℂ (V × V')) q = (aeval f q).prodMap (aeval g q) := by
  have h2 : aeval ((f, g) : Module.End ℂ V × Module.End ℂ V') q = (aeval f q, aeval g q) := by
    induction q using Polynomial.induction_on' with
    | add p r hp hr => simp [hp, hr]
    | monomial n a => simp [aeval_monomial]
  have h := Polynomial.aeval_algHom_apply (LinearMap.prodMapAlgHom ℂ V V') (f, g) q
  rw [h2] at h
  exact h

structure UpperTheory.Gal.NearKilling.IneRelInv {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x y : WD h) : Prop where
  pol : ∀ s, x.charPol (ineIncl h s) = y.charPol (ineIncl h s)
  eig : ∀ ξ : ↥(Ine (F := E) A) → ℂ, (∀ (g : Weil h) s, ξ (ineConj g s) = ξ s) → EigZero y ξ → EigZero x ξ

end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

def TypeRel (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      TrSum r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun i s => ι.symm (η (blockOf d hd i) (art (ineIncl h s)))) ∧
      ∀ b₀, Kills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun s => ι.symm (η b₀ (art (ineIncl h s))))
        fun b s => ι.symm (η (b₀.succAbove b) (art (ineIncl h s)))

def GoodLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ w : HeightOneSpectrum (𝓞 E),
    ∃ (X : UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .good l P χ' ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Dec (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → IsSplitAt w') ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def AllLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ S : Set (HeightOneSpectrum (𝓞 E)), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) → ∀ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

end UpperTheory.Gal.NearKilling
end
end
