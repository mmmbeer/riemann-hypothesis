import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.RealHermitianForms

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

section Form

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_add_l (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  unfold hJ; rw [star_add, add_dotProduct]

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [mulVec_add, dotProduct_add]

theorem hJ_sub_l (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_sub_r (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ; rw [mulVec_sub, dotProduct_sub]

theorem hJ_smul_l (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = conj c * hJ ε x y := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]; rfl

theorem hJ_smul_r (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]


theorem hJ_conj_sym (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  unfold hJ
  simp only [Formalism.REAL.Jm, mulVec_diagonal, dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def,
    Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hJ ε x (y i) := by
  unfold hJ
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem hJ_sum_l {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε (∑ i ∈ s, c i • y i) x = ∑ i ∈ s, conj (c i) * hJ ε (y i) x := by
  rw [hJ_conj_sym, hJ_sum_r, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hJ_conj_sym]

theorem hJ_uj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) : hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  have hg : Formalism.REAL.inUJ ε (uMat g) := g.2
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  simp [uMat]

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem hJ_inv_r (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g⁻¹ *ᵥ y) = hJ ε (uMat g *ᵥ x) y := by
  rw [← hJ_uj ε g x (uMat g⁻¹ *ᵥ y), mulVec_mulVec, uMat_mul_inv, one_mulVec]

theorem exists_of_hJ (E : Matrix (Fin n) (Fin n) ℂ) (hE : ∀ x y, hJ ε (E *ᵥ x) (E *ᵥ y) = hJ ε x y) :
    ∃ s : Formalism.REAL.UJ ε, uMat s = E := by
  have key : ∀ x y : Fin n → ℂ,
      star x ⬝ᵥ ((Eᴴ * Formalism.REAL.Jm ε * E) *ᵥ y) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
    intro x y
    have h := hE x y
    unfold hJ at h
    rw [← h, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h1 : Formalism.REAL.inUJ ε E := by
    unfold Formalism.REAL.inUJ
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    simpa [dotProduct, mulVec, Pi.single_apply] using h
  have hL : (Formalism.REAL.Jm ε * Eᴴ * Formalism.REAL.Jm ε) * E = 1 := by
    have : (Formalism.REAL.Jm ε * Eᴴ * Formalism.REAL.Jm ε) * E = Formalism.REAL.Jm ε * (Eᴴ * Formalism.REAL.Jm ε * E) := by
      simp only [Matrix.mul_assoc]
    rw [this, h1, Formalism.REAL.Jm_mul_self]
  exact ⟨⟨Matrix.nonsingInvUnit E (Matrix.isUnit_det_of_left_inverse hL), h1⟩, rfl⟩

end Form

section Eich

variable {n : ℕ} (ε : Fin n → Bool)

def eichL (u w : Fin n → ℂ) (κ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x := x + hJ ε w x • u - hJ ε u x • w + (κ * hJ ε u x) • u
  map_add' x y := by
    simp only [hJ_add_r, add_smul, mul_add]
    abel
  map_smul' c x := by
    simp only [hJ_smul_r, RingHom.id_apply]
    module

end Eich

section Frame

variable {n r : ℕ} (ε : Fin n → Bool)

end Frame

end Formalism.L2.SG.RealObj.InfCut.RealHermitianForms
