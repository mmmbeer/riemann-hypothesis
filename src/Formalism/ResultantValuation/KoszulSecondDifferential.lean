import Mathlib

open Polynomial

noncomputable section

namespace Formalism.ResultantValuation

def koszulSecondDifferential {A : Type} [CommRing A] (r : ℕ) (x y : A) :
    (Fin r → A) × (Fin r → A) →ₗ[A] (Fin r → A) :=
  y • LinearMap.fst A (Fin r → A) (Fin r → A) - x • LinearMap.snd A (Fin r → A) (Fin r → A)

abbrev truncPoly (k : Type) [Field k] (n : ℕ) : Type := k[X] ⧸ Ideal.span {(X : k[X]) ^ n}

open Classical in

def ComplementCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (r t : ℕ), Module.finrank F V = r + t → ∀ v : Fin r → V,
    Nat.card {U : Submodule F V //
        Module.finrank F U = t ∧ Submodule.span F (Set.range v) ⊔ U = ⊤} =
      if LinearIndependent F v then Fintype.card F ^ (r * t) else 0

def parabolicSet (F : Type) [Field F] (r t : ℕ) : Set (GL (Fin (r + t)) F) :=
  {g | ∀ i j : Fin (r + t), r ≤ (i : ℕ) → (j : ℕ) < r → (g : Matrix (Fin (r + t)) (Fin (r + t)) F) i j = 0}

end Formalism.ResultantValuation
