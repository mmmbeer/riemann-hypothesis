import Formalism.StatementCM
import Formalism.StatementU

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.B

open Formalism

def Lcm (a : ℝ) (l : ℕ) : ℝ := Real.log (a * l)

open Classical in

def AΨ (l : ℕ) (Bad : Finset ℕ) (Ψ : Finset (ZMod l)ˣ) (x : ℝ) : ℝ :=
  2 * ∑ n ∈ Icc 1 ⌊x⌋₊,
    if n.minFac ∉ Bad then
      (if h : IsUnit (n : ZMod l) then (if h.unit ∉ Ψ then Λ n * (x / n - 1) else 0) else 0)
    else 0

open Classical in

def gainCM (l : ℕ) (Ψ : Finset (ZMod l)ˣ) (x a a1 w k m L0 : ℝ) (p : ℕ) : ℝ :=
  (∑ i ∈ Icc 1 ⌊x⌋₊,
      if h : IsUnit (((p ^ i : ℕ)) : ZMod l) then
        (if h.unit ∉ Ψ then max (a1 / (p : ℝ) ^ i - w) 0 else 0) else 0)
    - a * Lcm a l / x ^ 2 - (k + 2 * m) * Real.log a / Real.log p - 1 - L0 / ((p : ℝ) - 1)

def GoodAway (l : ℕ) (Bad : Finset ℕ) (x : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ Bad → ∀ i : ℕ, 1 ≤ i → (p : ℝ) ^ i ≤ x →
    (((p ^ i : ℕ)) : ZMod l) ≠ 1 ∧ (((p ^ i : ℕ)) : ZMod l) ≠ -1

structure TypeParams (l : ℕ) (Ψ : Finset (ZMod l)ˣ) (Bad : Finset ℕ)
    (x a a1 b w L0 C r η v : ℝ) (m k f : ℕ) where

  logOm : ℝ

  T0 : ℕ
  d : ℝ
  rho : ℝ
  degN : ℝ
  degKr : ℝ
  muQ : ℝ
  muMaxR : ℝ
  hInf : ℝ
  hFin : ℝ

  sK : ℕ → ℝ

  sP : ℝ

  S : Finset ℕ

  vt : ℕ → ℝ
  vK : ℕ → ℕ → ℝ
  vP : ℕ → ℝ
  vKN : ℝ
  examplePrime_prime : T0.Prime
  topModOneCondition : ((T0 : ℕ) : ZMod l) = 1
  d_pos : 0 < d
  rho_pos : 0 < rho

  rank : r * d ≤ rho
  muQ_eq : muQ = (degN - degKr) / rho

  degN_ge : -(d * (C * m * (a / k + b) * Real.log T0)) ≤ degN

  degKr_le : degKr ≤ d * (C * a * Real.log k)

  slope : muQ ≤ muMaxR + hInf + hFin

  muMaxR_le : muMaxR ≤ C * f * k * b * Lcm a l
  hInf_le : hInf ≤ (∑ j ∈ range m, sK j) + sP

  sK_le : ∀ j < m, sK j ≤ a * Real.log a - a - a * logOm + C * k * f * b * Lcm a l
    + C * f * (k : ℝ) ^ 2 * Lcm a l

  exists_primePowerSum_le_mul_log : sP ≤ Real.log (2 * l) - a * Real.log T0
  S_prime : ∀ p ∈ S, p.Prime
  hFin_eq : hFin = -∑ p ∈ S, 2 * Real.log p * vt p
  vt_off : ∀ p : ℕ, p.Prime → p ∉ S → vt p = 0

  comp : ∀ p : ℕ, p.Prime → (∑ j ∈ range m, vK j p) + vP p ≤ vt p
  valuationTopComparison : vKN + vP T0 ≤ vt T0

  CardSubmodulesOfIndexLePow : ∀ j < m, ∀ p : ℕ, p.Prime → p ≠ l → p ≠ T0 → 0 ≤ vK j p

  CardSubmodulesAndLinearEquivBounds : ∀ j < m, ∀ p : ℕ, p.Prime → p ∉ Bad → (p : ℝ) ≤ x → p ≠ l → p ≠ T0 →
    gainCM l Ψ x a a1 w k m L0 p ≤ vK j p

  C7 : ∀ j < m, -(C * (a + L0) / ((l : ℝ) - 1)) ≤ vK j l

  primeValuation_nonneg : ∀ p : ℕ, p.Prime → 0 ≤ vP p

  C5 : -(C * m * f * b) ≤ vKN

  C6 : m * Real.log (b * v / Real.pi) - η
      - C * (m * Lcm a l / f + Lcm a l + (m : ℝ) ^ 2 * Lcm a l / k) ≤ Real.log T0

  integral_span_le_stable : Real.log T0 ≤ C * m * Lcm a l

def Params (C : ℝ) (l f m k : ℕ) (x a a1 b w L0 r η v : ℝ) : Prop :=
  1 ≤ C ∧ 2 * f + 1 = l ∧ 3 ≤ l ∧ 1 ≤ m ∧ m ≤ k ∧ f ≤ k ∧ 2 ≤ x ∧ (k : ℝ) ≤ x ∧ (k : ℝ) ^ 8 ≤ b ∧
    a = x * b ∧ a - C * b / (m : ℝ) ^ 2 ≤ a1 ∧ w ≤ b + C * (m * l + k) + C * b / (m : ℝ) ^ 2 ∧
    0 ≤ L0 ∧ L0 ≤ 2 * (k + 2 * m) * f * b ∧ 0 < r ∧ r ≤ 1 ∧ 0 ≤ η ∧ 0 < v

def ProductFormula : Prop :=
  ∀ Δ : ℤ, Δ ≠ 0 →
    Real.log |(Δ : ℝ)| = ∑ p ∈ Δ.natAbs.primeFactors, (Δ.natAbs.factorization p : ℝ) * Real.log p

end Formalism.B
