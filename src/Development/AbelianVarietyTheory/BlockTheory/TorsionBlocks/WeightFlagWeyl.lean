import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightFlagWeyl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Extremal

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsWeylK (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Prop := ∀ a, ε (s a) = ε a

def IsFlagWeyl (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Prop :=
  IsWeylK ε s ∧ (∀ a b, a < b → ε a = true → ε b = true → s a < s b) ∧
    ∀ a b, a < b → ε a = false → ε b = false → s b < s a

def IsExtremalUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧
    ∃ s : Equiv.Perm (Fin n), IsWeylK ε s ∧ IsWtOn (Formalism.REAL.Kset ε) σ (Formalism.QuantumDeterminants.lowK ε lam ∘ s) w

def IsFrameExtremalUnit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) :
    Prop :=
  ‖w‖ = 1 ∧ w ∈ lowKSub ε lam σ ∧
    ∃ s : Equiv.Perm (Fin n), IsFlagWeyl ε s ∧ IsWtOn (Formalism.REAL.Kset ε) σ (Formalism.QuantumDeterminants.lowK ε lam ∘ s) w

theorem IsFrameExtremalUnit.extremal {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H} (h : IsFrameExtremalUnit ε lam σ w) :
    IsExtremalUnit ε lam σ w :=
  ⟨h.1, h.2.1, h.2.2.imp fun _ hs => ⟨hs.1.1, hs.2⟩⟩

example : IsFlagWeyl ![true, false, false] (Equiv.swap (1 : Fin 3) 2) := by
  unfold IsFlagWeyl IsWeylK; decide

example : ¬ IsFlagWeyl ![true, false, false] (1 : Equiv.Perm (Fin 3)) := by
  unfold IsFlagWeyl IsWeylK; decide

end Extremal

variable {D : D7}

section Source

variable {V : HSp D} (θ : InfFam D) (c : CoefA V) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)

end Source

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def IoExtAt (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  ∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
    (∀ ρ, IsFrameExtremalUnit ((R.MW i (sg0 D A)).ε ρ) ((R.MW i (sg0 D A)).lam ρ) ((R.MW i (sg0 D A)).σ ρ)
      ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)) ∧
    ‖w‖ = 1 ∧ R.ioP i (PiTensorProduct.tprod ℂ v) w = RealDat.Delta i

def IoExtremal (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ i, IoExtAt R i

end GlobalTheory.IndefiniteRowSideFullHecke.WeightFlagWeyl

end
