import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

variable (D : D7)

def InertInK (l : ℕ) : Prop := D.host.cls l = .signal ∨ D.host.cls l = .inertClass

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def Matches (θ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, θ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Place

def window {n : ℕ} (W : WordData n) (k : ZMod n) : Set ℤ :=
  (if W.up k then Set.Icc (W.sz k) (W.sz k + W.S) else Set.Icc (-(W.sz k + W.S)) (-W.sz k)) ∪
    Set.Icc (-(W.η : ℤ)) W.η

section Concl

variable (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Concl

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineWindowLifts
