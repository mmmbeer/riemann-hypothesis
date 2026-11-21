import Formalism.FlagUnipotentLattices.MemLpTwoOfOneTop

open Finset TensorProduct

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def InterlaceBlocksW : Prop :=
  ∀ (m : ℕ) (t : ℕ → ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    Interlaces u v → (∀ x ∈ u, -b 0 < x) →
    (∀ j < m, b j < e j) → (∀ j, j + 1 < m → e j < b (j + 1)) →
    (∀ i < m, ∀ j < m, ((t j : ℝ) + 1) / 2 ≤ |b i - e j|) →
    Interlaces (u ++ (List.range m).flatMap (fun j => blockP (-e j) (t j + 1)))
      (v ++ (List.range m).flatMap (fun j => -b j :: blockP (-e j) (t j)))

def LLmap {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] {n : ℕ}
    (ℓ : V →ₗ[ℂ] U) (a : Fin n) : V ⊗[ℂ] (Fin n → ℂ) →ₗ[ℂ] U :=
  (TensorProduct.rid ℂ U).toLinearMap ∘ₗ TensorProduct.map ℓ (LinearMap.proj a)

end Formalism.HermitianLatticeCounting.S8
