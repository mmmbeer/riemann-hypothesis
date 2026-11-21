import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
import Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

noncomputable section

open MeasureTheory Filter Topology Matrix GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open PositivityTheory.Rg.Pc1 (IsProfile)

namespace PositivityTheory.RgTw

variable {n : ℕ}

def KU (n : ℕ) : Subgroup (G n) where
  carrier := {k | th k = k}
  one_mem' := th_one
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, th, star_mul, _root_.mul_inv_rev] at *
    rw [hx, hy]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, th, star_inv] at *
    rw [hx]

def RegN (d : G n) : Prop := IsRegSS (d * th d : G n).val

section

variable (n) [MeasurableSpace (G n)] [BorelSpace (G n)]

def HasTO (μ : Measure (G n)) (d : G n) (dt : Measure (twCent d)) (f : G n → ℂ) (c : ℂ) : Prop :=
  HasQuotInt (twCent d) dt μ (fun x => f (tw x d)) c

def IsThetaOp {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U) : Prop :=
  (∀ v, ‖A v‖ = ‖v‖) ∧ Function.Surjective A ∧ ∀ x, A ∘L π x = π (th x) ∘L A

end

def StTopClass : Prop := ∀ (n : ℕ), ∀ k ∈ KU n, ∀ s ∈ KU n, ev (tw k s).val (topP n) = ev s.val (topP n)

end PositivityTheory.RgTw
