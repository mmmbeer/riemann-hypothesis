import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

namespace GlobalTheory.SWC

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

def starM {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g.map (sigR R σ)).transpose

def hermCoord {n : ℕ} (S : HermR R σ n) : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
  (fun a => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a), fun p => S.1 p.1.1 p.1.2)

variable [TopologicalSpace R] {M n : ℕ}

def DensAt (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (κ : Measure (HermR R σ n))
    (S : HermR R σ n) (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
    ∃ (U : Set (HermR R σ n)) (D : HermR R σ n → ℝ), IsOpen U ∧ S ∈ U ∧ ContinuousOn D U ∧ (∀ t ∈ U, 0 ≤ D t) ∧
      (∀ A ⊆ U, MeasurableSet A → ∫⁻ X in gramR R σ J ⁻¹' (Subtype.val '' A), ENNReal.ofReal (φ X) ∂μ =
        ∫⁻ t in A, ENNReal.ofReal (D t) ∂κ) ∧ D S = ∫ X, φ X ∂m

def GF (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (κ : Measure (HermR R σ n))
    (S : HermR R σ n) (m : Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  m {X | gramR R σ J X ≠ S.1} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ DensAt R σ J μ κ S m

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {d : ℕ} {b : Module.Basis (Fin d) F E} {M n : ℕ}

def kap (cE cF : ℝ≥0) (n M : ℕ) : ℝ≥0 := cE ^ (n * M) / (cF ^ n * cE ^ n.choose 2)

end Global

end GlobalTheory.SWC

end
