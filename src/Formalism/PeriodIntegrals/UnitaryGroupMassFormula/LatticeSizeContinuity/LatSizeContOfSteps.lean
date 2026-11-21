import Mathlib
import Formalism.PeriodIntegrals.LatSizeCont

noncomputable section

open NumberField Matrix
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

def nsq {n : ℕ} (w : Fin n → ℂ) : ℝ := ∑ i, ‖w i‖ ^ 2

def LatIs : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ Λ : Submodule (𝓞 I.E) (Fin I.n → I.E), Λ.FG ∧
    Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤ ∧ Size.latSet I x = (Λ : Set (Fin I.n → I.E))

def DetMono : Prop :=
  ∀ (n j : ℕ) (C : Matrix (Fin n) (Fin j) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (κ : ℝ), 0 ≤ κ →
    (∀ w : Fin n → ℂ, nsq (M *ᵥ w) ≤ κ * nsq w) →
    0 ≤ ((Cᴴ * C).det).re ∧ (((M * C)ᴴ * (M * C)).det).re ≤ κ ^ j * ((Cᴴ * C).det).re

def SizeNear : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA) (δ : ℝ), 0 < δ → ∃ U ∈ nhds x, ∀ x' ∈ U,
    (∀ s : Size.Sub I x, ∃ s' : Size.Sub I x', Size.size I s' ≤ (1 + δ) * Size.size I s) ∧
    (∀ s' : Size.Sub I x', ∃ s : Size.Sub I x, Size.size I s ≤ (1 + δ) * Size.size I s')

def GramLow : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ c : ℝ, 0 < c ∧ ∀ (v : InfinitePlace I.F) (j : ℕ) (b : Fin j → Fin I.n → I.E)
    (ι : Fin j → Fin I.n), Function.Injective ι →
    c ^ j * ‖I.φ v (Matrix.of fun a d => b a (ι d)).det‖ ^ 2 ≤ ((Size.gramV I x v b).det).re

def GramLowOf : Prop := DetMono → GramLow

def NormProd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (m : I.E), ∏ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = |((Algebra.norm ℚ m : ℚ) : ℝ)|

def LowerBd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ c : ℝ, 0 < c ∧ ∀ s : Size.Sub I x, c ≤ Size.size I s

def SubEx : Prop := ∀ (I : Formalism.MainNotions.S.AutInst), 1 ≤ I.n → ∀ x : I.GA, Nonempty (Size.Sub I x)

def Assembly : Prop := SizeNear → LowerBd → SubEx → PI.LatSizeCont.LatSizeCont

end PI.UnitaryGroupMassFormula.LSC
