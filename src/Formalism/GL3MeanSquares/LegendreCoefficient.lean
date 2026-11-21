import Mathlib
import Formalism.FormalGroupWitt.ShiftSOneLetter

noncomputable section

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

def expS {σ K : Type} [Field K] [Algebra ℚ K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f (PowerSeries.exp K)

def InLam {σ K : Type} [NormedField K] [Algebra ℚ K] (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ Formalism.G.IntegralMv (expS f)

def IntegralInverse : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (T : σ → MvPowerSeries σ K) (J' : Matrix σ σ K),
    (∀ i, MvPowerSeries.constantCoeff (T i) = 0) → (∀ i, Formalism.G.IntegralMv (T i)) →
    (∀ i j, ‖J' i j‖ ≤ 1) →
    (Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i)) * J' = 1 →
    ∃ X' : σ → MvPowerSeries σ K, (∀ i, MvPowerSeries.constantCoeff (X' i) = 0) ∧
      (∀ i, Formalism.G.IntegralMv (X' i)) ∧ (∀ i, MvPowerSeries.subst X' (T i) = MvPowerSeries.X i) ∧
      ∀ i, MvPowerSeries.subst T (X' i) = MvPowerSeries.X i

open Classical in

def HomFormTrace : Prop :=
  ∀ (E L L' ι : Type) [Field E] [StarRing E] [AddCommGroup L] [Module E L] [AddCommGroup L']
    [Module E L'] [Fintype ι] (hL : L → L → E) (hL' : L' → L' → E),
    (∀ x x' y, hL (x + x') y = hL x y + hL x' y) → (∀ (a : E) x y, hL (a • x) y = a * hL x y) →
    (∀ x y, hL x y = star (hL y x)) → (∀ x y, hL' x y = star (hL' y x)) →
    ∀ (b : Module.Basis ι E L) (bs : ι → L), (∀ a a', hL (b a) (bs a') = if a = a' then 1 else 0) →
    ∀ (A B : L →ₗ[E] L') (Bs : L' →ₗ[E] L), (∀ x y, hL' (B x) y = hL x (Bs y)) →
      LinearMap.trace E L (Bs ∘ₗ A) = ∑ a, hL' (A (b a)) (B (bs a))

open Classical in

def SplitOrthonormal : Prop :=
  ∀ (B L ι : Type) [CommRing B] [StarRing B] [AddCommGroup L] [Module B L] (e : B) (h : L → L → B),
    e + star e = 1 → e * star e = 0 →
    (∀ x x' y, h (x + x') y = h x y + h x' y) → (∀ (a : B) x y, h (a • x) y = a * h x y) →
    (∀ x y, h x y = star (h y x)) →
    ∀ (l ls : ι → L), (∀ a, e • l a = l a) → (∀ a, star e • ls a = ls a) →
      (∀ a a', h (l a) (ls a') = if a = a' then e else 0) →
      (∀ a a', h (l a) (l a') = 0) ∧ (∀ a a', h (ls a) (ls a') = 0) ∧
      ∀ a a', h (l a + ls a) (l a' + ls a') = if a = a' then 1 else 0

open Classical in

def AdjointMatrix : Prop :=
  ∀ (O P P' ι : Type) [CommRing O] [StarRing O] [AddCommGroup P] [Module O P] [AddCommGroup P']
    [Module O P'] [Fintype ι] (h₁ : P → P' → O),
    (∀ p q p', h₁ (p + q) p' = h₁ p p' + h₁ q p') → (∀ (c : O) p p', h₁ (c • p) p' = c * h₁ p p') →
    (∀ p p' q', h₁ p (p' + q') = h₁ p p' + h₁ p q') →
    (∀ (c : O) p p', h₁ p (c • p') = star c * h₁ p p') →
    ∀ (ω : ι → P) (ωv : ι → P'), (∀ r r', h₁ (ω r) (ωv r') = if r = r' then 1 else 0) →
    ∀ (a : P → P) (abar : P' → P'), (∀ p p', h₁ (a p) p' = h₁ p (abar p')) →
    ∀ (am cm : ι → ι → O), (∀ r, a (ω r) = ∑ r', am r' r • ω r') →
      (∀ r', abar (ωv r') = ∑ r, cm r r' • ωv r) →
      ∀ r r', cm r r' = star (am r' r)

open Complex in

def Hf (A : ℝ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (A : ℂ)

def EF (A : ℝ) (z w : ℂ) : ℝ := (Hf A z w).im

def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

def Uop (A : ℝ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F (z + x) * Complex.exp (-Real.pi * Hf A z x - Real.pi * Hf A x x / 2)

def Fq (A : ℝ) (S : ℂ → ℂ) (y : ℂ) : ℂ → ℂ := fun z => Uop A y S z / S z

def LegendreCoefficient : Prop :=
  ∀ (a b ω₁ ω₂ : ℂ) (A : ℝ), A = (ω₁ * (starRingEnd ℂ) ω₂).im → A ≠ 0 →
    (a * ω₂ + b * (starRingEnd ℂ) ω₂) * ω₁ - (a * ω₁ + b * (starRingEnd ℂ) ω₁) * ω₂ =
      2 * Real.pi * Complex.I →
    b = Real.pi / A

def Wop (A d : ℝ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ee (EF A ((1 + Real.sqrt d * Complex.I) / 2 * x) x / 2) * Uop A x F z

def FockTranslate : Prop :=
  ∀ (A : ℝ) (x z : ℂ) (G φ : ℂ → ℂ),
    Uop A x G z * (starRingEnd ℂ) (Uop A x φ z) * Complex.exp (-Real.pi * Hf A z z) =
      G (z + x) * (starRingEnd ℂ) (φ (z + x)) * Complex.exp (-Real.pi * Hf A (z + x) (z + x))

end Formalism.HermitianLattices.ExpSeriesBivariate
