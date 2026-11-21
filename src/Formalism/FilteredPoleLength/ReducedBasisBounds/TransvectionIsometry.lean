import Mathlib

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

def GammaL : Prop :=
  ∀ (T D r nW n' ap am : ℝ), 0 ≤ D → 0 ≤ r → r ≤ nW → 0 ≤ n' → n' ≤ nW →
    (D + 2) * nW + 2 * r ≤ T → 40 * (D + 2) ≤ T → 1.9 * T ≤ ap → 1.9 * T ≤ am →
      max T (2 * r + n' + 2 * (T + D + 2)) ≤ ap + am + nW - r + 1

def OrderSharp : Prop :=
  ∀ (lamQ lamQs lam1 lB d' rd f : ℝ), 0 < f → 0 < rd → 0 ≤ d' → 0 ≤ lB → 0 ≤ lamQs → 0 < lam1 →
    lamQ ^ 2 ≤ (1 / 2) * lB * lamQs ^ 2 → lamQs * lam1 ≤ d' → 2 * f / rd ^ 2 ≤ lam1 ^ 2 →
      lamQ ^ 2 ≤ lB * d' ^ 2 * rd ^ 2 / (4 * f)

def NearestPlane : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (v : Fin n → V),
    LinearIndependent ℝ v → ∀ x ∈ Submodule.span ℝ (Set.range v),
      ∃ c : Fin n → ℤ, ‖x - ∑ i, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖v i‖ ^ 2

def GaussianTailBound : Prop :=
  ∀ (ι : Type) (h : ι → ℝ) (g : ℕ) (R0 : ℝ), 0 < R0 → 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2 →
    (∀ i, R0 ≤ h i) →
    (∀ R : ℝ, R0 ≤ R → ∀ S : Finset ι, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g)) →
      Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) ∧
        ∑' i, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)

def TransvectionIsometry : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, h w v = starRingEnd ℂ (h v w)) → ∀ x : V, h x x = 0 →
      (∀ (β : ℂ) (v w : V), β + starRingEnd ℂ β = 0 →
        h (v + (β * h v x) • x) (w + (β * h w x) • x) = h v w) ∧
      ∀ (β β' : ℂ) (v : V),
        let u := v + (β' * h v x) • x
        u + (β * h u x) • x = v + ((β + β') * h v x) • x

def BallVolume : Prop :=
  ∀ (D : ℕ) (rr : ℝ), 0 < rr →
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * D))) rr) =
      ENNReal.ofReal (Real.pi ^ D * rr ^ (2 * D) / (D.factorial : ℝ))

end Formalism.LatticeBaseChangeAlt
