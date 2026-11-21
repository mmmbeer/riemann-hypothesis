import Formalism.HermitianCurvature.StatementJF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

noncomputable section

namespace CompanionTheory.JfS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NilAlg {n : ℕ} (𝓡 : Set (Matrix (Fin n) (Fin n) ℂ)) (N : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (ξ : Fin n × Fin n → R),
    (∀ X ∈ 𝓡, ∑ i : Fin n × Fin n, X i.1 i.2 • ξ i = 0) →
    (∀ j < n, (Matrix.of fun a b : Fin n =>
      Polynomial.C (ξ (a, b)) + if a = b then (Polynomial.X : Polynomial R) else 0).det.coeff j = 0) →
    (Ideal.span (Set.range ξ)) ^ N = ⊥

def NN (k r : ℕ) : ℕ := 2 * (2 * r + k + 1) * (2 * r * (2 * r + k + 1) + 1)

def Tan {k r : ℕ} (S : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | B.inLie k r X ∧ ∃ γ : ℝ → B.Mat k r, HasDerivAt γ X 0 ∧ γ 0 = 1 ∧ ∀ t, γ t ∈ S}

def RelSet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Set (B.Mat k r) :=
  (Tan (Nset k r) ∪ Tan (UWset k r z')) ∪ (fun X => g⁻¹ * X * g) '' (Tan (Nset k r) ∪ Tan (UWset k r z))

def GlobalTheory (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def AlgNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k →
      Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (bigCell k r c μ *ᵥ z') z) →
      NilAlg (RelSet k r z z' (bigCell k r c μ)) (NN k r)

section flat

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

def dd (p q : Fin n × Fin n → V) (i : Fin n × Fin n) (f : V → E) : V → E :=
  fun y => fderiv ℝ f y (p i) + Complex.I • fderiv ℝ f y (q i)

end flat

def GrpReg : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (D : Set (B.Mat k r))
    (g₀ : B.Mat k r), IsOpen D → g₀ ∈ B.GV k r → g₀ ∈ D → ∀ (J : B.Mat k r → E) (m N : ℕ), N ≤ m →
    2 * r + k + 1 ≤ m → Q.CkLev k r 0 m D J →
    ∀ 𝓡 : Set (B.Mat k r),
    (∀ X ∈ 𝓡, ∃ a : B.Mat k r → B.Mat k r, ContDiffOn ℝ ∞ a {x | IsUnit x.det} ∧ a g₀ = X ∧
      ∃ T : E →L[ℂ] E, ∀ g ∈ B.GV k r, g ∈ D →
        ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), a g i.1 i.2 • Q.EH k r i.1 i.2 J g = T (J g)) →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ B.GV k r, g ∈ D → Q.CV k r (Y : ℂ) J g = c • J g) →
    NilAlg 𝓡 N →
    ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ g ∈ U, g ∈ B.GV k r → J g = F g

def RightRel : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (D : Set (B.Mat k r))
    (J : B.Mat k r → E) (S : Set (B.Mat k r)) (τ : B.Mat k r → (E →L[ℂ] E)), Q.CkLev k r 0 1 D J →
    S ⊆ B.GV k r → (∀ s ∈ S, ∀ g ∈ B.GV k r, J (g * s) = τ s (J g)) → ∀ X ∈ Tan S,
    ∃ T : E →L[ℂ] E, ∀ g ∈ B.GV k r, g ∈ D →
      ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), X i.1 i.2 • Q.EH k r i.1 i.2 J g = T (J g)

def LeftRel : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (D : Set (B.Mat k r))
    (J : B.Mat k r → E) (S : Set (B.Mat k r)) (τ : B.Mat k r → (E →L[ℂ] E)), Q.CkLev k r 0 1 D J →
    S ⊆ B.GV k r → (∀ s ∈ S, ∀ g ∈ B.GV k r, J (s * g) = τ s (J g)) → ∀ X ∈ Tan S,
    ∃ T : E →L[ℂ] E, ∀ g ∈ B.GV k r, g ∈ D →
      ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (g⁻¹ * X * g) i.1 i.2 • Q.EH k r i.1 i.2 J g = T (J g)

def BesselSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), JF.TransportedAlt k r A (NN k r) → B.InCC A (NN k r) F →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) F g = c • F g) →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') (B.JF D F)

def BesselSmoothOf : Prop := GrpReg → RightRel → LeftRel → AlgNil → BesselSmooth

end CompanionTheory.JfS
