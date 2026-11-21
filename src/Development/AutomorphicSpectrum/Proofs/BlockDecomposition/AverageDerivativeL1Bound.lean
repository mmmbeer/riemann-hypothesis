import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def avg {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (h : ℝ → ℝ) (u : ℝ → Mat n → V) : Mat n → V :=
  fun x => ∫ t, (h t : ℂ) • u t x

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

def l1 (f : Mat n → V) : ℝ := ∫ y : G n, ‖f y.val‖ ∂μ

def l2 (f : Mat n → V) : ℝ := Real.sqrt (∫ y : G n, ‖f y.val‖ ^ 2 ∂μ)

def ip [InnerProductSpace ℂ V] (f h : Mat n → V) : ℂ := ∫ y : G n, ⟪f y.val, h y.val⟫_ℂ ∂μ

end Norms

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

def AverageDerivativeL1Bound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (h : ℝ → ℝ) (T : ℝ) (w : List (Bool × Fin n × Fin n)), ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) →
      ∃ C : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → ∀ x ∈ GLs n, ‖Rw w (avg h u) x‖ ≤ C * l1 μ (u 0)

def ApproxId : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V), (∀ j v, ψ j v ∈ CE E) ∧
      (∃ R, ∀ j v, ∀ y ∈ GLs n, R < lg y → ψ j v y = 0) ∧ (∃ C : ℝ, ∀ j v, l1 μ (ψ j v) ≤ C * ‖v‖) ∧
      (∀ j v, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, ψ j v (k.1 * y) = ψ j (E.ρ k⁻¹ v) y) ∧
      ∀ v, ∀ f ∈ CE E, Cpt f → Tendsto (fun j => ip μ (ψ j v) f) atTop (𝓝 ⟪v, f 1⟫_ℂ)

end GlobalTheory.CompanionTheory.WaveK
