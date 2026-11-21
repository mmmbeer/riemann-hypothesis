import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def IsFinUnram (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] : Prop :=
  Function.Injective (algebraMap V W) ∧ Module.Finite V W ∧ Algebra.FormallyUnramified V W

theorem IsFinUnram.map_maximalIdeal {V W : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] (h : IsFinUnram V W) :
    IsLocalHom (algebraMap V W) ∧ (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by
  obtain ⟨hi, hf, hu⟩ := h
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).mpr hi
  have : IsLocalHom (algebraMap V W) := inferInstance
  exact ⟨this, Algebra.FormallyUnramified.map_maximalIdeal⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
