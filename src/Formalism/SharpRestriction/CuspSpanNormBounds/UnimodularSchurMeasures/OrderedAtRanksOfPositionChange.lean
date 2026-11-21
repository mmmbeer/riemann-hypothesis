import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.FlagUnipotentLattices.ThirdHeightFromSecond
import Formalism.FormalDegreeBessel.FinalG

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions Formalism.BasicNotions.TH

def LocalOrderedConclusion (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∃ B : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B ∧ HasOrdLe k r (rk48 k r ^ 2 / 2 + 1) σ B ∧
    ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def OrderedAtRanks (D : D7) (C : ℝ) : Prop :=
  ∀ (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (c : Fin D.R.rS → ℂ) (u : Fin D.R.k → ℝ) (v : Fin (D.R.k - 1) → ℝ)
    (b : Fin (2 * D.R.rS + 2) → ℝ), RealPlaceNumericalSetting D.R.k D.R.rS z c u v b → GapC C D.R.k D.R.rS b →
    LocalOrderedConclusion D.R.k D.R.rS z c u v b

theorem two_rS_add_two_eq_m (D : D7) : 2 * D.R.rS + 2 = D.R.m := by
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := h1
  show 2 * (D.R.m / 2 - 1) + 2 = D.R.m
  omega






def gapCentre (m : ℕ) (g : ℤ) (b : ℕ → ℤ) (j : ℕ) : ℤ := if j + 1 < m then (b j + b (j + 1)) / 2 else b j + g



def towerOfIntegers (D : D7) (X : ThetaX D) (t : ℕ) (h1 : Odd t) (h2 : D.R.r + 5 ≤ t) (uZ : Fin D.R.k → ℤ)
    (vZ : Fin (D.R.k - 1) → ℤ) (bN : ℕ → ℤ) (g : ℤ) : TPar D where
  t := t
  t_odd := h1
  t_ge := h2
  u := fun _ i => (uZ i : ℚ) + 1 / 2
  v := fun _ i => (vZ i : ℚ)
  b := fun _ j => (bN j.1 : ℚ)
  e := fun _ j => (gapCentre D.R.m g bN j.1 : ℚ)
  eta := fun τ => -X.infTy X.etaT τ
  eta_half := by
    intro τ
    rcases X.etaT_inf τ with h | h
    · right; rw [h]
    · left; rw [h]; ring


def towerParamU {D : D7} (P : TPar D) (τ : D.what₂.Tau) : Fin D.R.k → ℝ := fun i => (P.u τ i : ℝ)

def towerParamV {D : D7} (P : TPar D) (τ : D.what₂.Tau) : Fin (D.R.k - 1) → ℝ := fun i => (P.v τ i : ℝ)

def towerParamB {D : D7} (P : TPar D) (τ : D.what₂.Tau) : Fin (2 * D.R.rS + 2) → ℝ :=
  fun j => (P.b τ (Fin.cast (two_rS_add_two_eq_m D) j) : ℝ)



theorem halfInt_of_integrality (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hu : Formalism.QuantumDeterminants.IsHCParam u) (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) : HalfIntegralDifference k r u v b := by
  intro i s
  obtain ⟨m1, e1⟩ := hu.2 i
  obtain ⟨m2, e2⟩ := hl.2 s
  refine ⟨m1 - m2 - r - 1, ?_⟩
  push_cast at e1 e2 ⊢
  linarith


def LocalOrderedSomeModel (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : CayleySignature.Mat k r → (H →L[ℂ] H)), IsDSHpk k r (eps48 k r) (lam48 k r v b) σ ∧
    ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp)
      (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π ∧
    ∃ B : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B ∧ HasOrdLe k r (rk48 k r ^ 2 / 2 + 1) σ B ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def LocalTransport : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) → LocalOrderedSomeModel k r u v b →
    ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
      LocalOrderedConclusion k r z c u v b

def Step4 (D : D7) (X : ThetaX D) : Prop :=
  ∀ P : TPar D, Hyp3 X P →
  ∀ (π : Submodule ℂ (X.AF (X.Xs P.t 0))) (φ : X.AF (X.Xs P.t 0)) (F : X.cusp (X.Ys P.t 0))
    (pos : X.Pos (X.Xs P.t 0) (X.Ys P.t 0) (X.iXYs P.t 0)),
    IsAutRep X _ π → π ≤ X.typeX P 0 → φ ∈ π → IsDv X P 0 (F : X.AF (X.Ys P.t 0)) → bB X P.t 0 pos 0 φ F ≠ 0 →
    ∀ τ, LocalOrderedSomeModel D.R.k D.R.rS (towerParamU P τ) (towerParamV P τ) (towerParamB P τ)


end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_lie_algebra_mem_unitary (k r : ℕ) (X : CayleySignature.Mat k r) (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨-, hH2, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
  set Hm := Formalism.QuantumDeterminants.Hpk k r with hHm
  set Y : CayleySignature.Mat k r := (t : ℂ) • X with hYdef
  have hY : Yᴴ * Hm + Hm * Y = 0 := by
    have h1 : Yᴴ = (t : ℂ) • Xᴴ := by simp [hYdef, Matrix.conjTranspose_smul]
    have h2 : Xᴴ * Hm + Hm * X = 0 := hX
    rw [h1, hYdef, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h2, smul_zero]
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hH2
  have hYh : Yᴴ = Hm * (-Y) * Hm⁻¹ := by
    rw [hinv]
    have h1 : Yᴴ * Hm = -(Hm * Y) := eq_neg_of_add_eq_zero_left hY
    calc Yᴴ = Yᴴ * (Hm * Hm) := by rw [hH2, Matrix.mul_one]
      _ = (Yᴴ * Hm) * Hm := by rw [Matrix.mul_assoc]
      _ = Hm * (-Y) * Hm := by rw [h1, Matrix.mul_neg]
  have hu : IsUnit Hm := ⟨⟨Hm, Hm, hH2, hH2⟩, rfl⟩
  have hdet : IsUnit (NormedSpace.exp Y).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp Y)
  show (NormedSpace.exp Y)ᴴ * Hm * NormedSpace.exp Y = Hm
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv, Matrix.exp_neg]
  calc Hm * (NormedSpace.exp Y)⁻¹ * Hm * Hm * NormedSpace.exp Y
      = Hm * (NormedSpace.exp Y)⁻¹ * (Hm * Hm) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = Hm * ((NormedSpace.exp Y)⁻¹ * NormedSpace.exp Y) := by rw [hH2, Matrix.mul_one, Matrix.mul_assoc]
    _ = Hm := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

theorem mat_mul_mem_UH_Hpk {k r : ℕ} {g h : CayleySignature.Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hh : h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = Formalism.QuantumDeterminants.Hpk k r
  calc (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hg', hh']

section Move

variable {k r : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H']







end Move

def DiscreteSeriesUniqueUpToUnitaryEquiv : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')),
    IsDSHpk k r ε lam σ' →
  ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

def HighestWeightUnique : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsHCParam u →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (Vp' : Type) [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] [FiniteDimensional ℂ Vp']
    (π' : CayleySignature.Mat k r → (Vp' →L[ℂ] Vp')), IsHCTypeW k r z u π' →
  ∃ A : Vp ≃ₗᵢ[ℂ] Vp', ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, A (π h x) = π' h (A x)

def PositionChange : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) →
  ∀ (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.inWb k r z' → 0 < Formalism.QuantumDeterminants.Tz k r z' → (∀ a, c' a ≠ 0) → (∃ g', IsFrameW k r z' g') →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ (B : H → Vp) (N : ℕ), IsBesselMapSm z (psiGen k r z c) σ π B → HasOrdLe k r N σ B →
    (∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0) →
  ∃ (π' : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z' u π' ∧
    ∃ B' : H → Vp, IsBesselMapSm z' (psiGen k r z' c') σ π' B' ∧ HasOrdLe k r N σ B' ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B' x ≠ 0



end Formalism.MainNotions.LeviCoordinates

end
end
