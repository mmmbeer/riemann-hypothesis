import Mathlib
import Formalism.PeriodIntegrals.GoodLatCM

section
open NumberField

namespace PI.GoodLatCMWork

open PI.GoodLatCM

def Setup (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    {S : Type} [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ) : Prop :=
  (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) ∧
  Module.finrank ℚ K = 2 ∧ NumberField.discr K = -(d : ℤ) ∧ d % 4 = 3 ∧
  Function.Injective emb ∧ (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) ∧
  Fintype.card S = Module.finrank K E ∧
  MM.FG ∧ MM ≠ ⊥ ∧
  (∀ x : E, x ∈ MM ↔ ∀ y ∈ MM, Algebra.trace K E (x * star y) ∈ (algebraMap (𝓞 K) K).range) ∧
  cc ≠ ⊥ ∧ δ ≠ 0

def lam {E : Type} [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ) :
    AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}

end PI.GoodLatCMWork
end

section
open NumberField
namespace PI.GoodLatCMWork
open PI.GoodLatCM

section Defs
variable {E : Type} [Field E] [NumberField E]

def embM {S : Type} (emb : S → E →+* ℂ) (δ : ℂ) {N N' : ℕ} (X : Matrix (Fin N') (Fin N) E) : S → Fin N' → Fin N → ℂ :=
  fun s i j => δ * emb s (X i j)

noncomputable def hh [StarRing E] (K : IntermediateField ℚ E) {N N' : ℕ} (X Y : Matrix (Fin N') (Fin N) E) : K :=
  Algebra.trace K E (∑ i, ∑ j, X i j * star (Y i j))

def matO (E : Type) [Field E] [NumberField E] (N N' : ℕ) : AddSubgroup (Matrix (Fin N') (Fin N) E) where
  carrier := {X | ∀ i j, X i j ∈ (algebraMap (𝓞 E) E).range}
  add_mem' := fun {X Y} hX hY i j => by
    rw [Matrix.add_apply]; exact add_mem (hX i j) (hY i j)
  zero_mem' := fun i j => by
    rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' := fun {X} hX i j => by
    rw [Matrix.neg_apply]; exact neg_mem (hX i j)

end Defs

def AreaFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    area (lam K φ₀ cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt d / 2)

end PI.GoodLatCMWork
end
