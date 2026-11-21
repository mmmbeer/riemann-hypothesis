import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.MajIter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsOrthSplit (S0 S1 Z : HSp D) (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E)
    (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E) : Prop :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B1 * S0.gram * B1 = S1.gram ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) bz * S0.gram * bz = Z.gram ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B1 * S0.gram * bz = 0 ∧
    S0.rank = S1.rank + Z.rank

def SUp (D : D7) (ρ : ℕ) : AddSubgroup (Mx D ρ ρ) where
  carrier := {N | ∀ i j, j ≤ i → N i j = 0}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro a b ha hb i j h
    simp [Matrix.add_apply, ha i j h, hb i j h]
  neg_mem' := by
    intro a ha i j h
    simp [Matrix.neg_apply, ha i j h]

def ratSU (D : D7) (ρ : ℕ) : AddSubgroup (SUp D ρ) := (ratMx D ρ ρ).addSubgroupOf (SUp D ρ)

def IsCutoffB (S S1 : HSp D) {ρ' : ℕ} (e : Matrix (Fin S.rank) (Fin ρ') D.host.E) (s1 : GA D S1 →* GA D S)
    (μN : Measure (NFlag S e)) (μ1 : Measure (GA D S1)) (β : GA D S → ℝ) : Prop :=
  (∀ h, 0 ≤ β h) ∧ Measurable β ∧ ∀ h,
    Integrable (fun p : NFlag S e × GA D S1 => β ((p.1 : GA D S) * s1 p.2 * h)) (μN.prod μ1) ∧
      ∫ p, β ((p.1 : GA D S) * s1 p.2 * h) ∂(μN.prod μ1) = 1

end Formalism.IndefR.Mi

end
