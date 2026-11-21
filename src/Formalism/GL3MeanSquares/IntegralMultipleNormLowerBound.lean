import Formalism.GL3MeanSquares.InverseNormLeOfIntegerInner

namespace Formalism.HermitianLattices.ExplicitEstimates

open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len Iset ev sep)
open scoped NumberField

def Ms_count_mean : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ρ : ℝ), 0 ≤ ρ →
    {x : 𝓞 K | (∑ φ : K →+* ℂ, ‖φ (x : K)‖) / (Module.finrank ℚ K : ℝ) ≤ ρ}.Finite ∧
    (({x : 𝓞 K | (∑ φ : K →+* ℂ, ‖φ (x : K)‖) / (Module.finrank ℚ K : ℝ) ≤ ρ}.ncard : ℕ) : ℝ)
      ≤ (2 * ρ + 1) ^ Module.finrank ℚ K

def wG (K s : ℕ) (e : ℕ → ℤ) (j : ℕ) : ℤ := e j - K - (2 * j + 1) * (s + 1)

def colW (K : ℕ) (U : ℕ → ℤ) {k : ℕ} : Fin k → ℤ := fun i => U i - K + i + 1

def nuRow (K s : ℕ) (U e : ℕ → ℤ) (j i : ℕ) : ℤ :=
  if i < 2 * K then (U i - K + i + 1) + wG K s e j else wG K s e j - wG K s e ((i - 2 * K) / (2 * s + 2))

def IntegralMultipleNormLowerBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V) (c z : ℤ),
    (c : ℂ) • x ≠ 0 → ‖(c : ℂ) • x‖ ^ 2 = (z : ℝ) → 1 / ‖x‖ ≤ |(c : ℝ)|

def parL (k s : ℕ) (U e : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i < k then U i else -e ((i - k) / (2 * s + 2)) + s - (((i - k) % (2 * s + 2) : ℕ) : ℤ)

def parR (k s : ℕ) (v b e : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i + 1 < k then v i
  else if (i + 1 - k) % (2 * s + 2) = 0 then -b ((i + 1 - k) / (2 * s + 2))
  else -e ((i + 1 - k) / (2 * s + 2)) + s + 1 - (((i + 1 - k) % (2 * s + 2) : ℕ) : ℤ)

def lamT (k s : ℕ) (U e : ℕ → ℤ) (h : ℤ) {n : ℕ} : Fin (n + 1) → ℤ := fun i => parL k s U e i - h + i + 1

def sgT (k s : ℕ) (v b e : ℕ → ℤ) (h : ℤ) {n : ℕ} : Fin n → ℤ := fun i => parR k s v b e i - h + i + 1

structure Layout (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) : Prop where
  one_le_K : 1 ≤ K
  one_le_m : 1 ≤ m
  chain : ∀ i, i + 1 < 2 * K → v i ≤ U i ∧ U (i + 1) + 1 ≤ v i
  last : -b 0 ≤ U (2 * K - 1)
  gap_eb : ∀ j, j < m → (s : ℤ) + 2 ≤ e j - b j
  gap_be : ∀ j, j + 1 < m → (s : ℤ) + 2 ≤ b (j + 1) - e j
  spread : e (m - 1) - b 0 ≤ eta
  cloud_v : ∀ i, i + 1 < 2 * K → 0 ≤ v i ∧ v i ≤ S
  cloud_u : ∀ i, 1 ≤ i → i + 1 < 2 * K → 0 ≤ U i ∧ U i + 1 ≤ S

def IsTop (K : ℕ) (U : ℕ → ℤ) (A bt : ℤ) : Prop := U 0 = A + K - 1 ∧ U (2 * K - 1) = -bt - K

def IsOff (K : ℕ) (U v : ℕ → ℤ) (S C₁ : ℤ) : Prop :=
  S ≤ U 0 - v 0 ∧ U 0 - v 0 + 1 ≤ C₁ * S ∧ U (2 * K - 1) = v (2 * K - 2) - 1 ∧ 2 * (K : ℤ) ≤ S

def LemC_bounds : Prop :=
  ∀ (N : ℕ) (nu : Fin (N + 1) → ℕ), Antitone nu →
    ∏ i, ((nu i).factorial : ℝ) ≤ hookF nu ∧
    hookF nu ≤ (∏ i, ((nu i).factorial : ℝ)) * ((nu 0 : ℝ) + N + 1) ^ ((N + 1) * N / 2)

def MeanLogExplicit : Prop :=
  ∀ (d k : ℕ) (h : Fin d → Fin k → ℝ) (v : ℝ), 1 ≤ d → 1 ≤ k → 0 < v → (∀ τ c, 0 < h τ c) →
    (∀ c, (∑ τ, h τ c) / d ≤ (k : ℝ) ^ 2 * (2 * v) ^ 2) →
    (∑ τ, Real.log (∑ c, h τ c)) / d ≤ Real.log ((k : ℝ) ^ 3 * (2 * v) ^ 2)

def AntitoneWeightLogBoundExplicit : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (v logT logB logc muB mu : ℝ), 2 ≤ v → Antitone lam →
    logB ≤ Real.log (4 * ((κ : ℝ) + 1) ^ 3 * v ^ 2) →
    logc ≤ (((κ : ℝ) + 1) * κ / 2) * Real.log ((plus lam 0 : ℝ) + κ + 1) →
    muB ≤ (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1) →
    mu ≤ muB + (wt (plus lam) : ℝ) * logB + logc - (lam (Fin.last κ) : ℝ) * logT →
    mu ≤ (wt (plus lam) : ℝ) * (4 * Real.log (((κ : ℝ) + 1) * v))
        + (((κ : ℝ) + 1) * κ / 2) * Real.log ((plus lam 0 : ℝ) + κ + 1) - (lam (Fin.last κ) : ℝ) * logT

def ColumnParameterMaximalCondition : Prop :=
  ∀ (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta A bt : ℤ), Layout K m s U v b e S eta → IsTop K U A bt →
    κ + 1 = 2 * K →
    Antitone (colW K U (k := κ + 1)) ∧ colW K U (k := κ + 1) 0 = A ∧
    colW K U (k := κ + 1) (Fin.last κ) = -bt ∧
    ∀ i : Fin (κ + 1), i ≠ 0 → i ≠ Fin.last κ → 0 ≤ colW K U i ∧ colW K U i ≤ S

def Col_param_off : Prop :=
  ∀ (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ), Layout K m s U v b e S eta → IsOff K U v S 2 →
    κ + 1 = 2 * K →
    Antitone (colW K U (k := κ + 1)) ∧
    (∀ i : Fin (κ + 1), 0 ≤ colW K U i ∧ colW K U i ≤ 3 * S) ∧
    (∀ i : Fin (κ + 1), i ≠ 0 → colW K U i - colW K U (Fin.last κ) ≤ S) ∧
    wt (plus (colW K U (k := κ + 1))) ≤ (κ + 1 + 2) * S ∧
    0 ≤ wt (colW K U (k := κ + 1)) ∧ wt (colW K U (k := κ + 1)) ≤ 2 * (κ + 1) * S

end Formalism.HermitianLattices.ExplicitEstimates
