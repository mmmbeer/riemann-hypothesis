import Mathlib
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtDescentAff

variable {X U Y : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U)
  (θ : ∀ (T : Scheme.{0}) (a b : T ⟶ U), a ≫ u = b ≫ u →
    {y : T ⟶ Y // y ≫ p = a} → {y : T ⟶ Y // y ≫ p = b})

def Rel {T : Scheme.{0}} (y₁ y₂ : T ⟶ Y) : Prop :=
  ∃ h : (y₁ ≫ p) ≫ u = (y₂ ≫ p) ≫ u, (θ T (y₁ ≫ p) (y₂ ≫ p) h ⟨y₁, rfl⟩).1 = y₂

variable {u p θ}

end GlobalTheory.EtDescentAff

namespace GlobalTheory.EtDescentAff

variable {X U Y : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U)
  (θ : ∀ (T : Scheme.{0}) (a b : T ⟶ U), a ≫ u = b ≫ u →
    {y : T ⟶ Y // y ≫ p = a} → {y : T ⟶ Y // y ≫ p = b})

variable {u p θ}

end GlobalTheory.EtDescentAff

namespace GlobalTheory.EtDescentAff

end GlobalTheory.EtDescentAff
