import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SatakeDualWeyl.StatementF

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def bcPar (n : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  Multiset.map α Finset.univ.val + Multiset.map (fun l => (α l)⁻¹) Finset.univ.val + (if Odd n then {1} else 0)

def phPar (n n' : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  (bcPar n α).map fun z => ((-1 : ℂ) ^ n')⁻¹ * z

def strPar (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun k : ℕ => (q : ℂ) ^ (-((t : ℤ) - 1 - 2 * (k : ℤ)))

def ThetaPar (q a b t : ℕ) (α : Fin (a / 2) → ℂ) (α' : Fin (b / 2) → ℂ) : Prop :=
  phPar b a α' = phPar a b α + strPar q t

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

open Classical in

def divInd (σ : L →+* L) (n : ℕ) (ϖ : L) (d : List ℤ) (g : Formalism.UG.GU σ n) : ℂ :=
  if ∃ k₁ k₂ : GL (Fin n) (Formalism.UG.intL L),
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (k₁ : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)).map (Formalism.UG.intL L).subtype *
          Matrix.diagonal (fun i : Fin n => ϖ ^ (d.getD i.1 0)) *
          (k₂ : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)).map (Formalism.UG.intL L).subtype
  then 1 else 0

end Local

variable {D : D7}

def KAt (V : HSp D) (e : AE D) : Set (GA D V) := {k | k ∈ KsphC V ∅ ∧ SuppF V e k}

def IsVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun w => w = v), heisO ψ S T u f = f

example (q : ℕ) (z : ℂ) : ThetaPar q 2 3 1 (fun _ => z) (fun _ => -z) := by
  have h3 : Odd 3 := by decide
  have h2 : ¬ Odd 2 := by decide
  have e3 : ((-1 : ℂ) ^ 3)⁻¹ = -1 := by norm_num
  have e2 : ((-1 : ℂ) ^ 2)⁻¹ = 1 := by norm_num
  simp only [ThetaPar, phPar, bcPar, strPar, h3, h2, if_true, if_false, e3, e2]
  simp [inv_neg]

example (q : ℕ) : strPar q 2 = {(q : ℂ), (q : ℂ)⁻¹} := by
  simp [strPar, Multiset.range_succ]

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces

end
