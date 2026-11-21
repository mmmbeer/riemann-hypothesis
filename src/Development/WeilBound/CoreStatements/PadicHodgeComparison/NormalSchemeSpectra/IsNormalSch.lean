import Development.WeilBound.CoreStatements.PadicHodgeComparison.TransferCocycles.TransferCocycle

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace PositivityTheory.AutomorphicGaloisHodgeTate.NormalSchemeSpectra

def IsNormalSch (X : Scheme.{0}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

abbrev pb (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (n i : ℤ) : Ht q (sch.obj X) n i →+ Ht q (sch.obj Y) n i :=
  pull (ZMod q) (sch.map f) (tw q i) n

def SpecIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A], SH A →
    IsAlgClosed (IsLocalRing.ResidueField A) → IsUnit (q : A) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing A) Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsProper p] [Smooth p] (n i : ℤ),
      Function.Bijective (pb q (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) n i) ∧
      Function.Bijective (pb q (pullback.fst p (Spec.map (CommRingCat.ofHom
        ((algebraMap (FractionRing A) Ω).comp (algebraMap A (FractionRing A)))))) n i)

end PositivityTheory.AutomorphicGaloisHodgeTate.NormalSchemeSpectra

end
