import Formalism.TorsionNormIteration.InvIntegralOfClass

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT

open Formalism.G

def LTSetting (K : Type u) [NormedField K] (p q : ℕ) (π : K) : Prop :=
  p.Prime ∧ (∃ h : ℕ, 0 < h ∧ q = p ^ h) ∧ 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ‖(p : K)‖ ≤ ‖π‖ ∧
    ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ ≤ ‖π‖

def IsLTSeries {K : Type u} [NormedField K] (q : ℕ) (π : K) (e : PowerSeries K) : Prop :=
  IntegralPS e ∧ constantCoeff e = 0 ∧ coeff 1 e = π ∧ DivBy π (e - X ^ q)

abbrev toK {K : Type u} [NormedField K] [IsUltrametricDist K] (F : FormalGroup (unitBall K)) :
    FormalGroup K :=
  F.map (unitBall K).subtype

def IsLTPoly {K : Type u} [NormedField K] (q : ℕ) (π : K) (e : Polynomial K) : Prop :=
  e.coeff 0 = 0 ∧ e.coeff 1 = π ∧ ‖e.coeff q‖ = 1 ∧ ∀ i : ℕ, i ≠ 1 → i ≠ q → ‖e.coeff i‖ ≤ ‖π‖

def TorsionExample : Prop :=
  IsLTPoly 2 (2 : ℚ_[2]) (Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2) ∧
    ((Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ_[2]).eval (-2) = 0) ∧
    ‖(-2 : ℚ_[2])‖ < 1 ∧ (-2 : ℚ_[2]) ≠ 0

def ExpIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ < 1 → ∀ c : K, ‖c‖ ^ (p - 1) ≤ ‖(p : K)‖ →
      ∀ n : ℕ, ‖c ^ n / (n.factorial : K)‖ ≤ 1

def QuasiLogShift : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (p : ℕ), p.Prime → ‖(p : K)‖ < 1 →
    ∀ z : PowerSeries K, constantCoeff z = 0 → IntegralPS (PowerSeries.derivative K z) →
      DivByMv (p : K)
        (z.subst (MvPowerSeries.X (0 : Fin 2) + (p : K) • MvPowerSeries.X (1 : Fin 2)) - atX z)

end Formalism.LT
