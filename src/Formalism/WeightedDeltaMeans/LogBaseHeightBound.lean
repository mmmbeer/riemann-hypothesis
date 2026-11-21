import Mathlib

section
open Finset MvPolynomial Filter Topology

noncomputable section

namespace Formalism.ShimuraLimitIdentity

abbrev Pol (Ψ : Type) (N : ℕ) := MvPolynomial (Ψ × Fin N) ℝ

def top (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => i.val < j)

def psumAt {Ψ : Type} {N : ℕ} (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i : Fin N, X (τ, i) ^ k

def Sh {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (j : ℕ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i ∈ top N j, pderiv (τ, i) F)

def Tot {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i : Fin N, pderiv (τ, i) F)

def lin {Ψ : Type} [Fintype Ψ] {N : ℕ} (u : Ψ → Fin N → ℝ) : Pol Ψ N :=
  -(∑ τ : Ψ, ∑ i : Fin N, C (u τ i) * X (τ, i))

def Kills {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) : Prop :=
  ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → ∀ G : Pol Ψ N, I (psumAt τ k * G) = 0

end Formalism.ShimuraLimitIdentity
end
end

section
open Finset

noncomputable section

namespace Formalism.ShimuraLimitIdentity

def LowerBoundAtBase : Prop :=
  ∀ (B0 r0 tail A0 : ℝ) (bad : Finset ℕ), 2 ≤ B0 → (∀ p ∈ bad, p.Prime) →
    (bad.card : ℝ) ≤ B0 → 0 ≤ tail →
    A0 = r0 - 1 / 2
        - (∑ p ∈ (Finset.range (⌊B0⌋₊ + 1)).filter Nat.Prime ∪ bad,
            (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)) + tail →
    r0 - 1 / 2 - 20 * Real.log B0 ≤ A0 ∧
    ∀ rd Lchi : ℝ, 1 ≤ rd → 0 ≤ Lchi →
      -((20 + 2 * |r0 - 1 / 2|) * (Real.log (B0 * rd) + Lchi)) ≤ A0

def LogBaseHeightBound : Prop :=
  ∀ (f N H b h0 B0 : ℝ), 1 ≤ f → 1 ≤ N → 0 ≤ H → H ≤ 8 * b / h0 → 8 ≤ h0 → 4 * f * N ^ 2 ≤ b →
    2 ≤ b → B0 = 4 * f * N ^ 2 * (1 + H) →
    4 ≤ B0 ∧ Real.log B0 ≤ 3 * Real.log b

end Formalism.ShimuraLimitIdentity
end
end
