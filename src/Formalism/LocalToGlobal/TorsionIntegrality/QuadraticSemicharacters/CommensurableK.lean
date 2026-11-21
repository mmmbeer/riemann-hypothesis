import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.InterIntegral

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Objects

variable {n k : Type*}

def prodLat (Λ₁ : AddSubgroup (n → ℂ)) (Λ₂ : AddSubgroup (k → ℂ)) : AddSubgroup (n ⊕ k → ℂ) where
  carrier := {z | (fun i => z (Sum.inl i)) ∈ Λ₁ ∧ (fun j => z (Sum.inr j)) ∈ Λ₂}
  zero_mem' := ⟨Λ₁.zero_mem, Λ₂.zero_mem⟩
  add_mem' := fun ha hb => ⟨Λ₁.add_mem ha.1 hb.1, Λ₂.add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨Λ₁.neg_mem ha.1, Λ₂.neg_mem ha.2⟩

end Objects

def CommensurableK : Prop :=
  ∀ (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n]
    [DecidableEq n] (Λ : AddSubgroup (n → ℂ)),
    relIdx (stdLat (cmL a b d ha hd lam hlam) n) Λ ≠ 0 → relIdx Λ (stdLat (cmL a b d ha hd lam hlam) n) ≠ 0 →
    ∀ g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
      (∀ w w', InK d (g (Pi.single w' 1) w)) → (∀ w w', InK d (g.symm (Pi.single w' 1) w)) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
          (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 ∧
        relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
          (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0

end Formalism.L2.Th1.H
