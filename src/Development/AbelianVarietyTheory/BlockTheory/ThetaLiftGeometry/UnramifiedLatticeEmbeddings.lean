import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

def window {n : ℕ} (W : WordData n) (a : ZMod n) : Set ℤ :=
  (if W.up a then Set.Icc (W.sz a) (W.sz a + W.S) else Set.Icc (-(W.sz a + W.S)) (-W.sz a)) ∪
    Set.Icc (-(W.η : ℤ)) W.η

def range {n : ℕ} (W : WordData n) (a : ZMod n) : Set ℤ :=
  Set.Icc (-(W.Mi a : ℤ)) (W.hi a : ℤ)

def InertInK {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  H.cls p = .signal ∨ H.cls p = .inertClass

section Place

variable (D : D7) (i : D.nd.Loc)

def liftIdx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def ChiConstituent (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∃ π ∈ D.nd.Z i, ∃ v : Fin D.R.nV → KK D.nd i, v ≠ 0 ∧
    ∀ g : GE D.nd, repK D.nd i r π g v = toK D.nd i ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) • v

variable (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

abbrev Lat : Type 1 :=
  LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)

def IsLetter (τ : Emb D i w hw) (g : D.R.GG) : Prop :=
  ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
    Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def CrysInput : Prop :=
  ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))

def JumpInput (ε : ℤˣ) : Prop :=
  ∀ (x : D.nd.X i) (τ : Emb D i w hw) (g : D.R.GG), IsLetter D i w hw τ g → ∀ u : ℤ,
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ u ↔
      u ∈ jR (hcAt D g) (liftIdx D i) (pos ε g)

end Place

def Inputs (D : D7) (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    (D.nd.Z i).Nonempty → ChiConstituent D i r ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
        JumpInput D i w hw r ε ∧
          (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → CrysInput D i w hw r)

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCrystallineInputs
