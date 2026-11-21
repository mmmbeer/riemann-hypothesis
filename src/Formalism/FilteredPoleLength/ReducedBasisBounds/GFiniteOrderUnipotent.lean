import Mathlib

open scoped BigOperators
open Polynomial Finset

namespace Formalism.LatticeBaseChangeAlt

noncomputable def GAdjVec {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (h : V →ₗ[R] V → R) (e e' g : Fin N → V) (b : Fin N) : V :=
  (Matrix.of fun a' a => h (e' a') (e a)).det • g b -
    ∑ a, ∑ a', ((Matrix.of fun a' a => h (e' a') (e a)).adjugate a a' * h (g b) (e a)) • e' a'

def GAdjugateNormBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (N : ℕ)
    (h : V →ₗ[ℂ] V → ℂ) (e e' g : Fin N → V) (ρ' : ℝ),
    (∀ x y, ‖h x y‖ ≤ ‖x‖ * ‖y‖) →
    (∀ a, ‖e a‖ ≤ ρ') → (∀ a, ‖e' a‖ ≤ ρ') → (∀ a, ‖g a‖ ≤ ρ') →
    ∀ b, ‖GAdjVec h e e' g b‖ ≤ (N + 1).factorial * ρ' ^ (2 * N + 1)

def GFiniteOrderUnipotent : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (k : ℕ), 0 < k → A ^ k = 1 →
    A.charpoly = (X - 1) ^ Fintype.card n → A = 1

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

end Formalism.LatticeBaseChangeAlt
