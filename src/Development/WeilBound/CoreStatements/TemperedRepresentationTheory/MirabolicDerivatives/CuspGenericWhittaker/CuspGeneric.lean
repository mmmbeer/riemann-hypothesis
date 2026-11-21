import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
import GroundTheory.AutomorphicForms.LocallyConstantCompact
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.WhittakerCells
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import GroundTheory.AutomorphicForms.SmoothRepContragredient
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Matrix

namespace GlobalTheory.BZMir.Whit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def biAct (n : ℕ) : unipB k (Fin n) × unipB k (Fin n) → GL (Fin n) k → GL (Fin n) k :=
  fun p x => (p.1 : GL (Fin n) k) * x * (p.2 : GL (Fin n) k)⁻¹

abbrev sigma {n : ℕ} (g : GL (Fin n) k) : GL (Fin n) k := GroundTheory.Automorphic.Whittaker.sigma g

variable (k) in

def biActOn (n : ℕ) (S : Set (GL (Fin n) k)) (hS : ∀ p, ∀ x ∈ S, biAct k n p x ∈ S) :
    unipB k (Fin n) × unipB k (Fin n) → S → S :=
  fun p x => ⟨biAct k n p x, hS p x x.2⟩

def cell {n : ℕ} (w : Equiv.Perm (Fin n)) : Set (GL (Fin n) k) := {g | GroundTheory.Automorphic.Whittaker.bruhatCell g = w}

end GlobalTheory.BZMir.Whit

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Matrix

namespace GlobalTheory.BZMir.Whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def WhitLeOne : Prop :=
  ∀ (n : ℕ) (ψ : AddChar k Circle) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB k (Fin n)) (whitChar ψ n)) ≤ 1

def CuspGeneric : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsCuspidal π → 0 < n → IsGeneric π

end GlobalTheory.BZMir.Whit

end
end
