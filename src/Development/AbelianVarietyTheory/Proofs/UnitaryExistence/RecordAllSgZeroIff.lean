import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FlagSectionAction

noncomputable section

namespace GlobalTheory.RecBCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

variable {D : D7} (T : Core D)

def cuEquiv {j : ℕ} (hj : InR D j) : T.Cu j ≃ Cusps T j where
  toFun cu := cu.1
  invFun cu := ⟨cu, hj⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {T} (h : LawsCore T)

end GlobalTheory.RecBCompare
