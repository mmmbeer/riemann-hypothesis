import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def HeckeOneLift : Prop :=
  ∀ (K X X' Fn V V' : Type) [Field K] [AddCommGroup Fn] [Module K Fn] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (Q N g : ℕ) (up dn : ℕ → X → Finset X)
    (dn' : ℕ → X' → Finset X') (kk : X → X' → Fn) (sv : X → X' → K) (abelian₂ : Fn →ₗ[K] (V →ₗ[K] V'))
    (ε : X → K) (ε' : X' → K) (a b : K) (cs : (X → V') →ₗ[K] V') (Forms : Set (X → V)),
    (Q : K) ≠ 0 → b ≠ 0 →
    (∀ L L' j, ∑ L1 ∈ dn' j L', kk L L1 = ∑ l ∈ range (j + 1),
      (((Q ^ 2) ^ ((j - l) * (g - l)) * Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) •
        ∑ L1 ∈ up (j - l) L, kk L1 L') →
    (∀ L L' j, ∀ L1 ∈ dn' j L', sv L L1 = (Q : K) ^ (j * N) * sv L L' ∧ ε' L1 = a ^ j * ε' L') →
    (∀ L L' i, ∀ L1 ∈ up i L, sv L1 L' = (Q : K) ^ (i * (N + g)) * sv L L' ∧ ε L1 = b ^ i * ε L) →
    (∀ i L', ∀ F ∈ Forms,
      cs (fun L => ∑ L1 ∈ up i L, (ε L1 * ε' L' * sv L1 L') • abelian₂ (kk L1 L') (F L)) =
        cs (fun L1 => (ε L1 * ε' L' * sv L1 L') • abelian₂ (kk L1 L') (∑ L ∈ dn i L1, F L))) →
    ∀ F ∈ Forms, ∀ (i : ℕ) (L' : X'),
      ((Q : K) ^ (-((i : ℤ) * ((N : ℤ) + g - i)))) •
          ∑ L1 ∈ dn' i L', cs (fun L => (ε L * ε' L1 * sv L L1) • abelian₂ (kk L L1) (F L)) =
        (a / b) ^ i • ∑ l ∈ range (i + 1), eF (fun x => b * beFam (Q : K) g x) l •
          cs (fun L => (ε L * ε' L' * sv L L') • abelian₂ (kk L L')
            (((Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ))))) • ∑ L0 ∈ dn (i - l) L, F L0))

end Formalism.InvariantFactorPaths.G7
