import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.CuspDecay

noncomputable section

open MeasureTheory NumberField Set
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core
open scoped ENNReal NumberField.AdeleRing InnerProductSpace

namespace PositivityTheory.Rg.Tf.Adel

open PositivityTheory.Rg.Tf.IntegralApplyAeEq

variable {K : Type} [Field K] [NumberField K]

abbrev Eu (d : ℕ) : Type := EuclideanSpace ℂ (Fin d)

structure Line (μ : Measure (G1 K (2 + 2))) {μ₂ : Measure (G1 K 2)} (τ₁ τ₂ : Submodule ℂ (L2 μ₂))
    (D : TypeDat K (2 + 2)) (d : ℕ) where
  sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)
  inj : Function.Injective sec
  onto : ∀ f, f ∈ LinearMap.range sec ↔ IsSec τ₁ τ₂ f ∧ D.Fix f
  J : L (Eu d) →ₗᵢ[ℂ] L2 μ
  spec : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) →
    Reps μ (J u) (theta β (sec v))

def flat (z : ℂ) (f : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) : ℂ := Complex.exp ((z + 2) * (HP 2 2 x : ℂ)) * f x

def IsOrthogonalProjectionTwoLines {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint P ∧ P ∘L P = P ∧ ∀ h, P h = 0 ↔ (∀ u, ⟪J u, h⟫_ℂ = 0) ∧ ∀ v, ⟪J' v, h⟫_ℂ = 0

def IsGal {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (σ : K ≃+* K) (θ : Twist μ) : Prop :=
  ∃ s : 𝔸[K] ≃+* 𝔸[K], Continuous s ∧ (∀ x : K, s (algebraMap K 𝔸[K] x) = algebraMap K 𝔸[K] (σ x)) ∧
    ∀ g : G1 K n, ((θ.e g : G1 K n) : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map s.toRingHom (g : AdelicGLn.AdelicGL K n)

def Stable {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (D : TypeDat K n) (θ : Twist μ) : Prop :=
  (∀ k, θ.e k ∈ D.U ↔ k ∈ D.U) ∧ ∀ k ∈ D.U, D.e (θ.e k) = D.e k

structure Pair (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) : Prop where
  irr₁ : CuspIrr μ₂ τ₁
  irr₂ : CuspIrr μ₂ τ₂
  orth : τ₁ ⟂ τ₂

def LineEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure]
    (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ D : TypeDat K (2 + 2), ∃ d, Nonempty (Line μ τ₁ τ₂ D d)

section Steps

variable (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
  {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d d' : ℕ} (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')

def ShiftCausal (T₀ : ℝ) : Prop :=
  (∀ (t : ℝ) (u u' : L (Eu d)) (v v' : L (Eu d')), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
    ⟪A.J u', A'.J v⟫_ℂ = ⟪A.J u, A'.J v'⟫_ℂ) ∧
  ∀ (s : ℝ) (u : L (Eu d)) (v : L (Eu d')), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * T₀ - s → v x = 0) →
    ⟪A.J u, A'.J v⟫_ℂ = 0

def ActsBy (f : CC K (2 + 2)) (β : ℝ → Eu d →L[ℂ] Eu d) : Prop :=
  Ker β ∧ Conv A.J A.J (Rop μ f) β ∧
    ∀ (z : ℂ) (v : Eu d) (x : G1 K (2 + 2)), ∫ g, f g * flat z (A.sec v) (x * g) ∂μ = flat z (A.sec (symb β z v)) x

def Family (T₀ : ℝ) (P : L2 μ →L[ℂ] L2 μ) (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (C : ℝ) : Prop :=
  (∀ (f : CC K (2 + 2)) β β', ActsBy μ A f β → ActsBy μ A' f β' → ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
  ∀ (X Λ : L2 μ →L[ℂ] L2 μ) (κ : ℝ → Eu d →L[ℂ] Eu d') (T B : ℝ), Ker κ → Conv A.J A'.J X κ → X ∘L P = P ∘L X → T₀ ≤ T →
    IsTrunc A.J A'.J T Λ → IsTraceClass (Λ ∘L X ∘L P ∘L Λ) → (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ B / (1 + |z.im|)) →
    ‖trace (Λ ∘L X ∘L P ∘L Λ) -
        (1 / 2 : ℂ) * LinearMap.trace ℂ (Eu d) ((N.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d) ∘ₗ (symb κ 0 : Eu d →ₗ[ℂ] Eu d'))‖ ≤
      C * B * Real.exp (-2 * T)

end Steps

def ForAll (p : ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) (d d' : ℕ), Line μ τ₁ τ₂ D d → Line μ τ₂ τ₁ D d' → Prop) :
    Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ (D : TypeDat K (2 + 2)) (d d' : ℕ)
    (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), p K μ μ₂ τ₁ τ₂ D d d' A A'

def PairFacts : Prop := ForAll fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => ShiftCausal μ A A' 0

def CtZero : Prop := ForAll fun _ _ _ μ _ _ _ _ _ D _ _ A _ =>
  ∀ u, Pc μ (A.J u) = 0 ∧ D.FixedByTypeProjector μ (A.J u) ∧ constantTermL2 μ 1 (A.J u) =ᵐ[μ] 0 ∧ constantTermL2 μ 3 (A.J u) =ᵐ[μ] 0

def ProjEx : Prop := ForAll fun _ _ _ μ _ _ _ _ _ _ _ _ A A' =>
  ShiftCausal μ A A' 0 → (∃ P, IsOrthogonalProjectionTwoLines A.J A'.J P) ∧ ∀ T : ℝ, 0 ≤ T → ∃ Λ, IsTrunc A.J A'.J T Λ

end PositivityTheory.Rg.Tf.Adel
