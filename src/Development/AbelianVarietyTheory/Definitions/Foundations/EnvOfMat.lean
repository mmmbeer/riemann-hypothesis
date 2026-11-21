import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.MainNotions.S

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def opn {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))‖

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

def CkOnH {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUH H g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ m F U ∧ ∀ g ∈ U, inUH H g → f g = F g

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def IsCC2 (k r : ℕ) (A : ℝ) (mm : ℕ) (F : Mx k r → V) : Prop :=
  CkOnH (Hpk k r) mm F ∧
    ∀ wl wr : List (Mx k r), wl.length + wr.length ≤ mm → (∀ X ∈ wl, InLieHpk k r X) →
      (∀ X ∈ wr, InLieHpk k r X) → ∃ C : ℝ, ∀ g ∈ UH (Hpk k r),
        ‖ldWord wl (rdWord wr F) g‖ ≤ C * opn g ^ (-A)

end GlobalTheory.SOrb
