import Formalism.FlagUnipotentLattices.CoveringRadius2

open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def NearTotalAbs : Prop :=
  ∀ c : ℝ, 0 < c → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ C Cg : ℝ, 1 ≤ C → 1 ≤ Cg → ∃ n₀ : ℕ,
    ∀ (n q J a f : ℕ) (rd g b : ℝ), n₀ ≤ n → q ^ 2 ≤ n → 1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f →
    Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 1 ≤ rd →
    Real.log (Real.log rd) ≤ n → Real.log (Real.log b) ≤ c₁ * n * f * Real.log n →
    (2 : ℝ) ^ q * (2 * Real.exp (-(c * J * n * f * Real.log n)))
        * (C * f * (q : ℝ) ^ 2 * Real.log (Ydat n f rd g b)) ^ a ≤
      Real.exp (-(c₂ * n * f * Real.log n))

def CuspidalityThreshold : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 1 ≤ q → 2 * q ≤ n → 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    2 * (n : ℝ) * Real.sqrt (2 * (q : ℝ)) + 2 * (n : ℝ) ^ 2 < h / 8 / Real.sqrt (2 * (q : ℝ))

def ThreshCuspOp : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 1 ≤ q →
    (16 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) < h ↔ 2 * (n : ℝ) * q < h / 8 / Real.sqrt q) ∧
    (q ≤ n → 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
      2 * (n : ℝ) ^ 2 + 2 * (n : ℝ) * q < h / 8 / Real.sqrt q ∧
        16 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) < h)

open Classical in

def AllSumOp : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A h : ℝ) (n q : ℕ),
    1 ≤ q → 1 ≤ n → 0 ≤ A → 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (2 * (n : ℝ) ^ 2 * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(h / 8 * min (2 * d γ v ^ 2) (d γ v / Real.sqrt q))) ≤
      A * (2 * Real.exp (2 * (n : ℝ) ^ 2)) ^ Fintype.card ι

open scoped Matrix.Norms.L2Operator in

def OpNormPsd : Prop :=
  ∀ (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ) (ρ : ℝ), 0 ≤ ρ →
    (((ρ ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ) - W.conjTranspose * W).PosSemidef ↔ ‖W‖ ≤ ρ)

open scoped Matrix.Norms.L2Operator in

def OpHSNorm : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ep a = ep b → X a b = 0) →
    Real.sqrt 2 * ‖X‖ ≤ hs X ∧ hs X ≤ Real.sqrt (2 * (q0 ep : ℝ)) * ‖X‖

def PZero : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), q0 ep = 0 →
    (∀ a b, ep a = ep b → X a b = 0) → X = 0

def CubeMult : Prop :=
  ∀ (C : ℝ) (n f : ℕ) (b₁ τ : ℝ), 1 ≤ C → 0 ≤ b₁ → 0 < τ →
    (4 / (1 / (C * n * b₁))) ^ (n ^ 2 * f) * (C * Real.sqrt n / τ ^ 2) ^ (2 * n ^ 2 * f) ≤
      (4 * C * (n : ℝ) ^ 2 * b₁) ^ (n ^ 2 * f) * (4 * C / τ) ^ (4 * n ^ 2 * f)

def LevelIndex : Prop :=
  ∀ (R : Type) [CommRing R] [Finite R] (n : ℕ),
    Nat.card (Matrix (Fin n) (Fin n) R)ˣ ≤ Nat.card R ^ (n ^ 2)

def VolLevel : Prop :=
  ∀ (C : ℝ) (n f : ℕ) (rd g b volG volK : ℝ), 1 ≤ n → 1 ≤ f → 1 ≤ rd → 1 ≤ g → 2 ≤ b →
    0 < volK → volG ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) → volK⁻¹ ≤ g ^ (2 * n ^ 2 * f) →
    volG / volK ≤ Ydat n f rd g b ^ ((C + 2) * (n : ℝ) ^ 2 * f)

def DeepChainV : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n q f : ℕ) (rd g b τ₁ τs ρ Kxx Bs D volG volK : ℝ), 1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f →
    1 ≤ rd → 1 ≤ g → 2 ≤ b → 0 < τ₁ → τ₁ < τs → 0 ≤ D → 0 < volK → 0 ≤ volG → 0 ≤ ρ →
    ρ ≤ C * (n : ℝ) ^ 2 * f * g * rd * (2 * τ₁) ^ ((1 : ℝ) / q) →
    Kxx ≤ (C * ρ * (n : ℝ) ^ 2 * f * b1 n q f b) ^ (2 * P0 n q f) * Bs →
    Bs ≤ D * volK⁻¹ * (C * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (C / τ₁) ^ (4 * n ^ 2 * f) →
    volG / volK ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) →
    volG * Kxx ≤ D * Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * f)
      * (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
      * τs ^ (12 * n ^ 2 * f)

end Formalism.HermitianLatticeCounting.S7
