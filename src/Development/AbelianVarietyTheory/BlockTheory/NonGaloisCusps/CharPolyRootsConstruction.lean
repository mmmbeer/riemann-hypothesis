import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

variable {N i N₁ i₁}

end Enlarge

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
