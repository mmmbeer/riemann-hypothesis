import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.CrdcTemperate

noncomputable section

open MeasureTheory Matrix LineDeriv

namespace Ad3.K.LC

def crqc (a : Fin 2) (p : M23 × (Fin 2 → ℂ)) : ℂ := (starRingEnd ℂ) (p.2 a)


def gauK (k : ℕ) (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  (p.1 0 0 * p.1 1 1 - p.1 0 1 * p.1 1 0) ^ (2 * k - 2) *
    (starRingEnd ℂ) (p.2 0 * p.1 0 0 + p.2 1 * p.1 1 0) ^ (4 * k - 4) *
      Complex.exp (-(2 * Real.pi : ℂ) * ((∑ r, ∑ c, ‖p.1 r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 : ℝ) : ℂ))

def DGau : Prop := ∀ k : ℕ, ∃ Ψ : Sw, ∀ p, Ψ p = gauK k p

def DKfd : Prop := StLin → ∀ k : ℕ, 3 ≤ k → ∀ Ψ : Sw, (∀ p, Ψ p = gauK k p) →
  FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ U3, W' = fun g => sec k Ψ (g * o)})

end Ad3.K.LC
