import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting

noncomputable section

namespace GlobalTheory.RowModelRoad

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.BlockComplement GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

def twistRep (ψ : Γ →* Oˣ) (ρ : Γ →* GL (Fin n) O) : Γ →* GL (Fin n) O :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((ψ g : Oˣ) : O) • ((ρ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
      map_one' := by simp
      map_mul' := fun g h => by simp [smul_smul, mul_comm] }


end Twist

section Lift

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end Lift

section Eig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) (i : N.Loc)

theorem frobEig_block (θ : A.CG 1) (t : ℕ) (w : PlE H) (b : ℂ) (hu : A.unr (A.locG θ w))
    (hb : A.frobEig (A.locG θ w) = {b}) :
    A.unr (spehLoc N A ⟨1, θ, t⟩ w) ∧ A.frobEig (spehLoc N A ⟨1, θ, t⟩ w) =
      ((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => b * ((normV w : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ) := by
  unfold spehLoc
  dsimp only
  induction List.range t with
  | nil => exact ⟨A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    have h1 := (A.unr_tw _ (((t : ℝ) - 1) / 2 - k)).2 hu
    refine ⟨(A.unr_sum _ _).2 ⟨h1, ih.1⟩, ?_⟩
    refine (A.frobEig_sum _ _ h1 ih.1).trans ?_
    rw [ih.2, A.frobEig_tw _ _ hu, hb]
    simp

end Eig

variable {D : D7}

end GlobalTheory.RowModelRoad
