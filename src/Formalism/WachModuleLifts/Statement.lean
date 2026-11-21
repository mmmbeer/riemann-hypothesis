import Mathlib

open Finset

noncomputable section

namespace Formalism.CL

variable (p : ℕ) [Fact p.Prime]

def phiPoly : Polynomial ℚ_[p] :=
  Polynomial.X ^ p - Polynomial.C (p : ℚ_[p]) * Polynomial.X ^ (p - 1) + Polynomial.C (p : ℚ_[p])

def phiIter (g : ℕ) : Polynomial ℚ_[p] := (fun f => (phiPoly p).comp f)^[g] Polynomial.X

def uu (g : ℕ) : PowerSeries ℚ_[p] :=
  (p : ℚ_[p])⁻¹ • ((phiIter p g : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

def Content (g : ℕ) (f : PowerSeries ℚ_[p]) : Prop :=
  ∀ j : ℕ, ‖PowerSeries.coeff j f‖ ≤ (p : ℝ) ^ (j / p ^ g)

def LemmaCSharp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y r : ℕ), r ≤ y → padicValNat p (y.choose r) < p - 1 →
    ‖PowerSeries.coeff (p * r) (uu p 1 ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), r ≤ y →
    padicValNat p (y.choose r) < p - 1 →
    ‖PowerSeries.coeff (p ^ g * r) (uu p g ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaCSharpOddG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (g : ℕ), 1 ≤ g → ∀ (y r : ℕ), r ≤ y →
    ‖PowerSeries.coeff (p ^ g * r) (uu p g ^ y)‖ = (p : ℝ) ^ ((r : ℤ) - padicValNat p (y.choose r))

def LemmaHLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
    [IsUltrametricDist V] (u : ℚ_[p]) (x : ℕ → V) (c : ℕ → ℕ → V →L[ℚ_[p]] V) (gg : ℕ → V),
    (∀ m : ℕ, 1 ≤ m → ‖u ^ m - 1‖ = (p : ℝ) ^ (-(1 + (padicValNat p m : ℤ)))) →
    (∀ m i, ‖c m i‖ ≤ 1) → (∀ m, ‖gg m‖ ≤ 1) → ‖x 0‖ ≤ 1 →
    (∀ m : ℕ, 1 ≤ m → (u ^ m - 1) • x m = (∑ i ∈ range m, c m i (x i)) + gg m) →
    ∀ m : ℕ, ‖x m‖ ≤ (p : ℝ) ^ (m + padicValNat p m.factorial)

def Legendre : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ),
    ((m : ℝ) + padicValNat p m.factorial) ≤ (m : ℝ) * p / (p - 1)

end Formalism.CL
