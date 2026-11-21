import Mathlib
import Formalism.RealPlaceAnalysis.StatementC
import Formalism.FormalDegreeBessel.StatementDS

open Finset MeasureTheory Filter Topology TensorProduct

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def sgnD (k m t j : ℕ) : List Bool :=
  List.replicate (k - 1 + (j + 1) + j * t) true ++
    (List.range (m - j - 1)).map (fun i => decide (i % 2 = 1))

def dimX (k t j : ℕ) : ℕ := k + j * (t + 1)

def blockP (c : ℝ) (len : ℕ) : List ℝ :=
  (List.range len).map (fun i : ℕ => c + ((len : ℝ) - 1) / 2 - (i : ℝ))

def alt : List ℝ → List ℝ → List ℝ
  | a :: as, b :: bs => a :: b :: alt as bs
  | as, [] => as
  | [], bs => bs

def Interlaces (A B : List ℝ) : Prop :=
  A.length = B.length + 1 ∧ (alt A B).IsChain (· > ·)

def ConjDual : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (G : Type) [Group G]
    (ρ : G →* (E →L[ℂ] E)), (∀ g, ρ g ∈ unitary (E →L[ℂ] E)) →
    ∀ (g : G) (v : E), InnerProductSpace.toDual ℂ E (ρ g v) = (InnerProductSpace.toDual ℂ E v).comp (ρ g⁻¹)

def AssemblyB : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : (T → E) → (T → E)) (χ : T → ℝ) (W : T → E),
    (∫ x, (inner ℂ (W x) (P (fun y => (χ y : ℂ) • W y) x) : ℂ) ∂μ) =
        ∫ x, (inner ℂ (W x) ((χ x : ℂ) • W x) : ℂ) ∂μ →
    0 < ∫ x, χ x * ‖W x‖ ^ 2 ∂μ →
    ¬ (P (fun y => (χ y : ℂ) • W y) =ᵐ[μ] 0)

def Residue : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] (n k : ℕ) (lam : Fin n → ℂ) (u : Fin k → ℂ) (a : Fin n → E)
    (K : E) (s₀ s₁ : ℂ),
    Function.Injective lam → K ≠ 0 →
    (∀ x : ℂ, (∀ s, x + s₀ - lam s ≠ 0) →
      ∑ i, (x - (lam i - s₀))⁻¹ • a i = ((∏ j, (x + s₁ - u j)) / ∏ s, (x + s₀ - lam s)) • K) →
    ∀ i, (a i = 0 ↔ ∃ j, u j = lam i + (s₁ - s₀))

def cas {n : ℕ} (lam : Fin n → ℝ) : ℝ := ∑ a, lam a ^ 2 - ∑ a, Formalism.QuantumDeterminants.rhoStd n a ^ 2

end Formalism.HermitianLatticeCounting.S8
