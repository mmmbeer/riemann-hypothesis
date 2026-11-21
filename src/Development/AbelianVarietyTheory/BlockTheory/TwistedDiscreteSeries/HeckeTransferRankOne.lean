import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.KsHecke

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def sqrtQ (P : Pl D.host.E) : ℂ := ((Real.sqrt (Nat.card (kP P) : ℝ) : ℝ) : ℂ)

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T0) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) :=
  Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

def mu0At (i : Fin D.R.m) (P : Pl D.host.E) : ℂ := (((R.C.mu0 i).val P : ℂˣ) : ℂ)

def xiAt (t : T0) (P : Pl D.host.E) : ℂ := (((R.xiH t).val P : ℂˣ) : ℂ)

def cW (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ := (mu0At R i P ^ k)⁻¹ * (sqrtQ P ^ (k * D.R.nV))⁻¹

end Real

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
