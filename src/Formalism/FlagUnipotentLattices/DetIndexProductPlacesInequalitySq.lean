import Mathlib
import Formalism.HyperbolicPlaceProducts.Statement
import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality

open Module NumberField nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def GramDetGen : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t t' : R),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -t else 0) W Z
        (Matrix.diagonal fun i => if i = Fin.last r then -t' else 0)).det =
      (-1) ^ (r + 1) *
        (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
          (W.submatrix Fin.castSucc Fin.castSucc).det)

def GramDet : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then (-(T : ℂ)) else 0)
        Z.conjTranspose Z
        (Matrix.diagonal fun i => if i = Fin.last r then (-(T' : ℂ)) else 0)).det =
      (-1) ^ (r + 1) *
        ((‖Z.det‖ ^ 2 - T * T' * ‖(Z.submatrix Fin.castSucc Fin.castSucc).det‖ ^ 2 : ℝ) : ℂ)

def GramNondeg : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (B : V →ₗ[K] V →ₛₗ[σ] K) (v : ι → V),
    (Matrix.of fun i j => B (v i) (v j)).det ≠ 0 →
    LinearIndependent K v ∧
      finrank K (Submodule.span K (Set.range v)) = Fintype.card ι ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B y x = 0) → x = 0) ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B x y = 0) → x = 0)

def DenomNormFrac : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : E) (J : FractionalIdeal (𝓞 E)⁰ E),
    α ≠ 0 → J ≠ 0 → (∀ x ∈ J, IsInt (α * x)) →
    1 ≤ |Algebra.norm ℚ α| * FractionalIdeal.absNorm J

def DetIndexProductInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g : ℝ) (e f : ℕ),
    0 < dPs₁ → 0 < dPs₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) →
    dLa₁ * i₁ ^ 2 ≤ G0₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dPs₁ * dPs₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂)

def DetIndexProductPlacesInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < K₁ → 0 < K₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT / (Nr₂ * K₂ ^ 2) ≤ P₁ → NT / (Nr₁ * K₁ ^ 2) ≤ P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
