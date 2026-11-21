import Development.EtaleCohomology.EtaleSheaves.LeafLocStalkPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf

namespace LateralTheory.E.LocSurjPf

def bcMap {Y X V : Scheme.{0}} (f : Y ⟶ X) (v : V ⟶ X) : cech (pullback.snd f v) ⟶ cech f :=
  Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk (yoneda.map (pullback.snd f v))) (g := Arrow.mk (yoneda.map f))
    (yoneda.map (pullback.fst f v)) (yoneda.map v)
    (by simp only [Arrow.mk_hom, ← Functor.map_comp, pullback.condition]))

def EtLift (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (i m : ℤ) (y : Ht q (cech f) m i) : Prop :=
  ∃ (V : Scheme.{0}) (v : V ⟶ X), Etale v ∧ Surjective v ∧
    ∃ z : Ht q (sch.obj V) m i, pull (ZMod q) (cechAug (pullback.snd f v)) (tw q i) m z = pull (ZMod q) (bcMap f v) (tw q i) m y

end LateralTheory.E.LocSurjPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf LateralTheory.E.LocSurjPf

namespace LateralTheory.E.LocGlueEtPf

def GlueRel : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X),
  (∀ (W : Scheme.{0}) (w : W ⟶ X), Etale w → ∀ m' < n, RelZS (ZMod q) (tw q i) m' (cechAug (pullback.snd f w))) →
    ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i, EtLift q f i m y →
      y ∈ Set.range (pull (ZMod q) (cechAug f) (tw q i) m)

end LateralTheory.E.LocGlueEtPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf LateralTheory.E.LocSurjPf
  LateralTheory.E.LocGlueEtPf CochainComplex.HomComplex

namespace LateralTheory.E.GlueRelPf

def obs (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) : Ht q U m i →+ Hrel (ZMod q) u (tw q i) (m + 1) :=
  HK.pre (ZMod q) (CochainComplex.mappingCone.fst ((chains (ZMod q)).map u)) (tw q i) m (m + 1) (add_comm 1 m)

def ConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ),
  Function.Exact (HK.pull R φ F m) (HK.pre R (CochainComplex.mappingCone.fst φ) F m (m + 1) (add_comm 1 m))

def EdgeInj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X),
  (∀ (W : Scheme.{0}) (w : W ⟶ X), Etale w → ∀ m' < n, RelZS (ZMod q) (tw q i) m' (cechAug (pullback.snd f w))) →
  ∀ (V : Scheme.{0}) (v : V ⟶ X), Etale v → Surjective v → ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i,
    obs q (cechAug (pullback.snd f v)) i m (pull (ZMod q) (bcMap f v) (tw q i) m y) = 0 → obs q (cechAug f) i m y = 0


end LateralTheory.E.GlueRelPf
end
end
