import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section One

variable (D : D7) (i : D.nd.Loc)

def IsRx (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i)) ∧
  IsSSRep (mapRep (toK D.nd i) r) ∧
  ∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i).charpoly = heckePol D.nd i x w

def DetInT (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ g : GE D.nd, ∃ P : Polynomial (D.nd.T i), ∀ x : D.nd.X i,
    P.map (evT D.nd i x) = ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i).charpolyRev

def RxConcl : Prop :=
  ∃ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), (∀ x, IsRx D i x (r x)) ∧ DetInT D i r

end One

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus

end
