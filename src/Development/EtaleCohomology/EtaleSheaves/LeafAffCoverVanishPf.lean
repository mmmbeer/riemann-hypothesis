import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8

end LateralTheory.E.E8

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def relF (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (c : H R E F n),
  pull R f F n c = 0 ↔ ∃ e : Hrel R f F n, relF R f F n e = c

end LateralTheory.E.E8

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
end
