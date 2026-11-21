import Mathlib

section
noncomputable section

namespace Formalism.LogFactorialBounds

open Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def blockUpper {F : Type} [Field F] (a t : ℕ) (J' : Set (GL (Fin a) F)) :
    Set (GL (Fin a ⊕ Fin t) F) :=
  {A | (∀ i j, (A : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F) (Sum.inr i) (Sum.inl j) = 0) ∧
       ∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = (A : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F).toBlocks₁₁}

def ParabolicIndex : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (r s : ℕ),
    (Nat.card (GL (Fin r ⊕ Fin s) F) : ℝ) / (Nat.card (blockUpper (F := F) r s Set.univ) : ℝ) =
      (Fintype.card F : ℝ) ^ (r * s) * qE (Fintype.card F) 1 (r + s) /
        (qE (Fintype.card F) 1 r * qE (Fintype.card F) 1 s)

end Formalism.LogFactorialBounds
end
end

section
noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

def LocalFactorSplitDv : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    let q : ℝ := Fintype.card F
    ((Nat.card (GL (Fin a ⊕ Fin t) F) : ℝ) /
        (Nat.card (blockUpper (F := F) a t (J' : Set (GL (Fin a) F))) : ℝ)) *
      ((Nat.card J' : ℝ) * q ^ (-((a * a : ℕ) : ℤ)) * q ^ (-((a * t : ℕ) : ℤ))) =
    qE q (t + 1) (a + t)

end Formalism.LogFactorialBounds
end
end
