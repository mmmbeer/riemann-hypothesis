import Mathlib

section
open Finset

noncomputable section

namespace Formalism.A

structure SmithData {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (y : M →ₗ[R] M) (d : ℕ) where
  b : Module.Basis (Fin d) R M
  b' : Module.Basis (Fin d) R M
  a : Fin d → R
  hy : ∀ i, y (b i) = a i • b' i

open Classical in

def SmithData.nAbove {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {y : M →ₗ[R] M} {d : ℕ} (S : SmithData y d) (ϖ : R) (t : ℕ) : ℕ :=
  (univ.filter fun i => ¬ S.a i ∣ ϖ ^ t).card

open Classical in

def SmithData.nBetween {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {y : M →ₗ[R] M} {d : ℕ} (S : SmithData y d) (ϖ : R) (t E : ℕ) : ℕ :=
  (univ.filter fun i => ¬ S.a i ∣ ϖ ^ t ∧ S.a i ∣ ϖ ^ E).card

def chain {K : Type*} [Field K] {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (θ : ∀ i, V i →ₗ[K] V (i + 1)) : ∀ m, V 0 →ₗ[K] V m
  | 0 => LinearMap.id
  | m + 1 => (θ m).comp (chain θ m)

def SmithExists : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M),
    Nonempty (SmithData y (Module.finrank R M))

end Formalism.A
end
end

section
namespace Formalism.A

end Formalism.A
end
