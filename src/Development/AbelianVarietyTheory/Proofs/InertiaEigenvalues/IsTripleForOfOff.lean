import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne

noncomputable section

namespace GlobalTheory.TripTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms
open Formalism.L2.Host (HChar CharFrame ValLL0 embLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.Triple
open GlobalTheory.EigTie
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW GaloisReps)
open GlobalTheory.LiftLeaf (CommG)
open GlobalTheory.SupLaw (OffRange)
open GlobalTheory.TwistAbove (twGL)

def MeetsP0 (D : D7) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  ∀ W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b), W ≠ ⊥ → GStable D.nexp i j b W →
    (∀ x ∈ W, eG D.nexp i j b x = x) → W ⊓ Fm0 D.nexp i j b ≠ ⊥

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* Gab D.host.E D.nd.Om}

end GlobalTheory.TripTie

end
