import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Obj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ff_psi (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℂ) • ∫ kk, d30f ε lam σ w X kk ∂(Formalism.REAL.muK ε)

def ff_IsPsi (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k X, k ∈ Formalism.REAL.Kset ε → Formalism.REAL.inP ε X → Ψ (k * NormedSpace.exp X) = σ k ∘L ff_psi ε lam σ w X

def ff_Data (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H)
    (h : ℝ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam lam ∧ IsDS ε lam σ ∧ IsOrthProjOnto E (lowKSub ε lam σ) ∧ IsHighestUnit ε lam σ w ∧
    Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h

def ff_Sph (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k₁ ∈ Formalism.REAL.Kset ε, ∀ k₂ ∈ Formalism.REAL.Kset ε, ∀ g ∈ UJset ε, Ψ (k₁ * g * k₂) = σ k₁ ∘L Ψ g ∘L σ k₂

def ff_Compr (ε : Fin n → Bool) (E : H →L[ℂ] H) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ g ∈ UJset ε, E ∘L Ψ g ∘L E = Ψ g

def ff_Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

def ff_DSSum (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ (N : ℕ) (φ : Fin N → Formalism.REAL.UJ ε → ℂ), (∀ i, IsDSCoef ε (φ i)) ∧
    ∀ g : Formalism.REAL.UJ ε, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i, φ i g

end Obj

def FPsiEig (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Eig ε (χ n lam) Ψ

end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ff_SigmaSum {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ (N : ℕ) (v w : Fin N → H), ∀ g : Formalism.REAL.UJ ε, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i, coefOn σ (v i) (w i) g

def FIdent (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ff_Eig ε (χ n lam) Ψ →
      ff_DSSum ε Ψ → ff_SigmaSum ε σ Ψ

def ff_HasInfChar {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (c : ℕ → ℂ) : Prop :=
  ∀ v w : H, IsKFin ε σ' v → ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪w, σ' g v⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

def QInfChar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Nontrivial H → IsURepOn (UJset ε) σ' → IsIrredOn (UJset ε) σ' →
    IsSqIntOn ε σ' → ∃ c : ℕ → ℂ, ff_HasInfChar ε σ' c

def QClass (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Nontrivial H' → IsURepOn (UJset ε) σ' → IsIrredOn (UJset ε) σ' →
    IsSqIntOn ε σ' → ff_HasInfChar ε σ' (χ n lam) → (∃ S : Submodule ℂ H', IsKTypeOf ε σ' (Formalism.QuantumDeterminants.lowK ε lam) S) →
    ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

theorem ff_det_exp {n : ℕ} (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inP ε X) :
    (NormedSpace.exp X).det = 1 := by
  have hJ2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJ2, hJ2⟩, rfl⟩
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hJ2
  have hc : Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε = -X := (Formalism.REAL.parabolic_character_holds n ε X).2 hX
  have h1 : NormedSpace.exp (-X) = Formalism.REAL.Jm ε * NormedSpace.exp X * Formalism.REAL.Jm ε := by
    have := Matrix.exp_conj (Formalism.REAL.Jm ε) X hJu
    rw [hJinv, hc] at this
    exact this
  have h2 : (NormedSpace.exp (-X)).det = (NormedSpace.exp X).det := by
    rw [h1, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hJ2, Matrix.det_one, one_mul]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute (-X) X ((Commute.refl X).neg_left)]
    simp
  have h4 : (NormedSpace.exp X).det * (NormedSpace.exp X).det = 1 := by
    have := congrArg Matrix.det h3
    rwa [Matrix.det_mul, h2, Matrix.det_one] at this
  have hpos := Formalism.REAL.leading_minors_positive n X (hermitian_of_mem_p ε X hX).1 (Fin.last n)
  have h5 : Formalism.REAL.lminor (NormedSpace.exp X) (Fin.last n) = (NormedSpace.exp X).det := by
    unfold Formalism.REAL.lminor
    congr 1
  rw [h5] at hpos
  obtain ⟨him, hre⟩ := hpos
  set d := (NormedSpace.exp X).det with hd
  have hdr : d = ((d.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have h6 : d.re * d.re = 1 := by
    have := congrArg Complex.re h4
    simpa [Complex.mul_re, him] using this
  have h7 : d.re = 1 := by nlinarith
  rw [hdr, h7]
  simp

end Formalism.MainNotions.LeviCoordinates

end
end
