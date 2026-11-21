import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.UnramifiedLatticeEmbeddings
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineWindowLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

noncomputable section

namespace GlobalTheory.WordJumpsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW GlobalTheory.IndefiniteRowSideFullHecke

section Clauses

variable (D : D7)

theorem inert_iff (l : ℕ) : CrystallineWindowLifts.InertInK D l ↔ UnramifiedCrystallineInputs.InertInK D.host l := Iff.rfl

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Clauses

section Constituent

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_toLL : Continuous (D.nbr i w hw).toLL :=
  continuous_subtype_val.comp (D.nbr i w hw).eO_cont

theorem continuous_toGlobal :
    Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
  continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)

theorem loc_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : Br.loc D.nbr i w hw M g a b =
      (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) := rfl

theorem locChi_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    ((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
      (D.nbr i w hw).toLL ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) := rfl

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous (Br.loc D.nbr i w hw M) := by
  refine continuous_matrix fun a b => ?_
  simp only [loc_apply]
  exact (continuous_toLL D i w hw).comp
    ((hM.comp (continuous_toGlobal D i w hw)).matrix_elem a b)

theorem toLLK_toK (c : D.nd.O i) :
    Br.toLLK (D.nbr i w hw) (toK D.nd i c) = (D.nbr i w hw).toLL c :=
  Br.toLLK_alg (D.nbr i w hw) c

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Constituent

section At

variable (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end At

end GlobalTheory.WordJumpsCompare
