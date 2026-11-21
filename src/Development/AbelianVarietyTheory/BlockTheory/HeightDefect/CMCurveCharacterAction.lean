import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsConj {K : Type} [Field K] (a b : 𝓞 K) : Prop :=
  ∀ τ : K →+* ℂ, τ (b : K) = starRingEnd ℂ (τ (a : K))

section

variable {R : Type} [CommRing R]

def RosatiConj {K : Type} [Field K] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 K) P.A) : Prop :=
  ∀ a b : 𝓞 K, IsConj a b →
    LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act b] P.L)

def ActsThrough {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (act : OAct O P.A) (ρ : O →+* R)
    (v : epsR R ⟶ P.A) : Prop :=
  ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (ρ a)) ≫ v.left

end

example (M : Type) [Field M] [NumberField M] : Fintype.card (M →+* ℂ) = Module.finrank ℚ M :=
  Embeddings.card M ℂ

end GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves
