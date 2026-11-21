import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith

open MeasureTheory NumberField Matrix
open scoped TensorProduct InnerProductSpace
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms

def perp {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (JA : Matrix (Fin n) (Fin n) A)
    (WA : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ x ∈ WA, Formalism.UG.hform s JA x y = 0}

variable (I : AutInst)

section Test

variable {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]

def dSigma (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def ph (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) : I.Ginf → ℂ :=
  fun g => (dSigma I σ w : ℂ) * star (∏ v, coefOn (ε := I.ε v) (σ v) (w v) (w v) (g v))

end Test

end GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms
