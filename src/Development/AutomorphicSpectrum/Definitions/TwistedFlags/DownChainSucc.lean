import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HaarOrderData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup

namespace GlobalTheory.CompanionTheory.Sep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Objects

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

def per (φ : Fn G (.core 0)) (u : GA D (Yc D 0) → ℂ) : ℂ :=
  ∫ h in M.fd (.grid 0 0), φ (stabilizerEmbedding G.sp.dec0 h) * u h ∂M.ν (.grid 0 0)

structure IsCoreForm (i : ℕ) (φ : Fn G (.core i)) : Prop where
  cusp : GlobalTheory.Mem.Th.IsCuspForm W.θ (G.V (.core i)) φ
  listed : G.IsListed W.θ (.core i) φ
  level : ∀ k ∈ GfC (G.V (.core i)), Lev.finE (G.V (.core i)) k ∈ G.levCong (.core i) → ∀ g, φ (g * k) = φ g

end Objects

end GlobalTheory.CompanionTheory.Sep

end
