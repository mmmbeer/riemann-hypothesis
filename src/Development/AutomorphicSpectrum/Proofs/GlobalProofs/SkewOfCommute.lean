import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InfinitesimalEquivalenceUnitaryGroupPQ
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie GlobalTheory.CompanionTheory.GKClosure
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

variable [CompleteSpace H] (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ)

end GlobalTheory.CompanionTheory.Hypotheses₂

namespace GlobalTheory.CompanionTheory.Hypotheses₂

section Words

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def wordE (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (l : List (Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ M :=
  (l.map A).prod

@[simp] theorem wordE_nil (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) : wordE A [] = 1 := rfl

@[simp] theorem wordE_cons (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (Z : Matrix (Fin n) (Fin n) ℂ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : wordE A (Z :: l) = A Z * wordE A l := by
  simp [wordE]

end Words

section Parts

variable {n : ℕ}

def pPlusS (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := GlobalTheory.HolDS.pPlus ε
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

def pMinusS (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := GlobalTheory.HolDS.pMinus ε
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

def kS (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | Y * Jm ε = Jm ε * Y}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.smul_mul, Matrix.mul_smul, hx]

def upperC (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | ∀ a b, ¬ (a ≤ b ∧ ε a = ε b) → Y a b = 0}
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

def lowerC (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | ∀ a b, ¬ (b < a ∧ ε a = ε b) → Y a b = 0}
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

end Parts

end GlobalTheory.CompanionTheory.Hypotheses₂

end
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie GlobalTheory.CompanionTheory.GKClosure GlobalTheory.CompanionTheory.Hypotheses₂
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.KStable

variable {n : ℕ} {ε : Fin n → Bool}

theorem skew_of_commute {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) :
    Xᴴ = -X := by
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = (Xᴴ * Jm ε) * Jm ε := by rw [Matrix.mul_assoc]
    _ = -(X * (Jm ε * Jm ε)) := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]

theorem exp_mem_Kset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Kset ε := by
  have hs := skew_of_commute hX hc
  have hJ : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv (Formalism.REAL.Jm_mul_self ε)
  have hu : IsUnit (Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hs]
    have hneg : star t • -X = -(t • X) := by simp
    have hcm : Commute (t • X) (-(t • X)) := (Commute.refl _).neg_right
    rw [hneg, ← Matrix.exp_add_of_commute _ _ hcm]
    simp
  · have h1 : Jm ε * (t • X) * (Jm ε)⁻¹ = t • X := by
      rw [hJ, Matrix.mul_smul, Matrix.smul_mul, ← hc, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    have h2 := Matrix.exp_conj (Jm ε) (t • X) hu
    rw [h1, hJ] at h2
    calc NormedSpace.exp (t • X) * Jm ε = Jm ε * NormedSpace.exp (t • X) * Jm ε * Jm ε := by rw [← h2]
      _ = Jm ε * NormedSpace.exp (t • X) := by rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end GlobalTheory.CompanionTheory.Hypotheses₂.KStable

namespace GlobalTheory.CompanionTheory.Hypotheses₂

end GlobalTheory.CompanionTheory.Hypotheses₂

end
end
