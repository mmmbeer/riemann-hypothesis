import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FlatDeterminantSections

open Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable (D : D7) (i : Fin D.R.m)

abbrev qJ : ℕ := (D.R.sigW ((i : ℕ) + 1)).2
end

section Flat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} (T : Core D)

open Classical in

def detA (τ : D.host.E →+* ℂ) : (D.host.E →+* ℂ) × ℕ → ℕ := fun x => if x.1 = τ then 1 else 0

open Classical in

def laFlat (j : ℕ) (σ : T.Q.c.F →+* ℂ) (τ : D.host.E →+* ℂ) (k : (T.U j σ).Comp) : Wt ((T.U j σ).X k).Ψ D.R.r :=
  fun ρ _ => if ρ.1 = relab T.Q.c σ τ then 1 else 0

variable (D) in

def vd (l : ℕ) : ℝ := ((discr D.host.E).natAbs.factorization l : ℝ) / (finrank ℚ D.host.E : ℝ)

variable (D) in

def flDefect (i : Fin D.R.m) : ℝ :=
  (qJ D i : ℝ) * (vd D 2 * Real.log 2 + vd D D.host.q * Real.log D.host.q - vd D D.host.d * Real.log D.host.d)

end Flat

end GlobalTheory.CompanionTheory.Ar.Rec.FlatDeterminantSections
