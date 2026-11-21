import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsKitWithKitWith
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad
open GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.ProjVar

namespace GlobalTheory.ShFam.DeKeyTrue

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

theorem divOf_neg_exOf {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp) (la : GlobalTheory.AllWt.Weight S.Dw) :
    divOf (Φ.C k) (fun z => -GlobalTheory.AllWt.exOf S.Dw la 0 (some z)) = (Φ.C k).Lw la := by
  simp only [divOf, FlagCpt.Lw, FlagCpt.LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk, neg_smul, Finset.sum_neg_distrib]

def hodgeLw {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ)
    (la : GlobalTheory.AllWt.Weight S.Dw) : (cxSt D.what₂.LL).Met (Φ.C k).Y σ ((Φ.C k).Lw la) :=
  divOf_neg_exOf Φ k la ▸ metsOf x Φ k none σ (fun z => -GlobalTheory.AllWt.exOf S.Dw la 0 (some z))

variable (s : FinalTheorems S κ)

end FinalTheorems

end GlobalTheory.ShFam.DeKeyTrue

namespace GlobalTheory.ShFam.DeKeyTrue

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

end FinalTheorems

end GlobalTheory.ShFam.DeKeyTrue

namespace GlobalTheory.ShFam.DeKeyTrue

variable {D : D7} {Q : KitClass D} {T : Top D} {h : LawsP T} {c : ℕ}

end GlobalTheory.ShFam.DeKeyTrue
