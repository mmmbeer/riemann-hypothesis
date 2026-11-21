import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.IsLowUnitH

open scoped InnerProductSpace
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible

def KRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (D : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → D a b * D c d - D c d * D a b =
    (if b = c then D a d else 0) - (if d = a then D c b else 0)

def KAdj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (D : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ

def CAR {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (p m : Fin n → Fin n → A) : Prop :=
  (∀ a b, ε a = ε b → p a b = 0 ∧ m a b = 0) ∧
  (∀ a b c d, m a b * p c d + p c d * m a b = if a = c ∧ b = d ∧ ε a ≠ ε b then 1 else 0) ∧
  (∀ a b c d, p a b * p c d + p c d * p a b = 0) ∧
  (∀ a b c d, m a b * m c d + m c d * m a b = 0)

def kap {A : Type*} [Ring A] {n : ℕ} (p m : Fin n → Fin n → A) (a b : Fin n) : A :=
  ∑ d, p a d * m b d - ∑ c, p c b * m c a

def Base {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E p m : Fin n → Fin n → Module.End ℂ W) : Prop :=
  Formalism.REAL.GlRel E ∧ (∀ a b x y, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ) ∧ CAR ε p m ∧
  (∀ a b x y, ⟪p a b x, y⟫_ℂ = ⟪x, m a b y⟫_ℂ) ∧
  ∀ a b c d, Commute (E a b) (p c d) ∧ Commute (E a b) (m c d)

def KMap {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {n : ℕ}
    (ε : Fin n → Bool) (D : Fin n → Fin n → Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ X)
    (ω : W →ₗ[ℂ] X) : Prop :=
  ∀ a b, ε a = ε b → ∀ w, ω (D a b w) = E a b (ω w)

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible

end
