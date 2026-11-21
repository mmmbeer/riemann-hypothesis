import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace HCSS

variable {n : ℕ}

def centre (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | z ∈ G ∧ ∀ g ∈ G, z * g = g * z}

def lieOf (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G}

def centralTorus (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {d | ∃ C ∈ lieOf (maxCpt G), (∀ Y ∈ lieOf (maxCpt G), C * Y = Y * C) ∧ d = NormedSpace.exp C}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsPermissible (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ z ∈ centralTorus G ∩ centre G, ∃ c : ℂ, π z = c • (1 : H →L[ℂ] H)

end HCSS

namespace HCSS

variable {n : ℕ}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {G : Set (Matrix (Fin n) (Fin n) ℂ)}
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end HCSS

end GlobalTheory.CompanionTheory.Hypotheses₂

end
