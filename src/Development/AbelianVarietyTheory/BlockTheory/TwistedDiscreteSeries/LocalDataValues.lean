import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalDataValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Stmt

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) := (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

variable {R}

end Stmt

end GlobalTheory.IndefiniteRowSideFullHecke.LocalDataValues

end
