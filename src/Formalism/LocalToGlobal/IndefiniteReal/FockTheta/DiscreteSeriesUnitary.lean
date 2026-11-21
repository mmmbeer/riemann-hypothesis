import Mathlib
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.FormalDegreeBessel.StatementRP

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

namespace Formalism.IndefR.Fock.SquareIntegrableRepresentations

abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

section Rep

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURepOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Formalism.QuantumDeterminants.IsCRepOn G σ ∧ (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧
    ∀ v : H, ContinuousOn (fun g => σ g v) G

def IsIrredOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤

def coefOn {ε : Fin n → Bool} (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H) :
    Formalism.REAL.UJ ε → ℂ :=
  fun g => ⟪w, σ (umat g) v⟫_ℂ

def IsSqIntOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (Formalism.REAL.muG ε)

def IsWtOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ G →
    σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v

def CDom (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
    Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b

def IsKStableOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Prop :=
  ∀ g ∈ Formalism.REAL.Kset ε, ∀ v ∈ S, σ g v ∈ S

def IsKTypeOf (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset ε) σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Formalism.REAL.Kset ε) σ μ v → CDom ε μ Λ

def vNormSq (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := Formalism.REAL.nsq (μ + (2 : ℝ) • Formalism.REAL.rhoC ε)

def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | Formalism.REAL.inUJ ε g}

def IsDS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ ∧
    (∃ S : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ vNormSq ε μ

end Rep

end Formalism.IndefR.Fock.SquareIntegrableRepresentations

end
