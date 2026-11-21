import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii

section
universe u

namespace PI.KEX

open PI.KoszulExact

def P {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) : Prop :=
  ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) →
    dK s x = 0 → ∃ y ∈ Li R D i ^ (j + 2), dK s y = x

def F1 : Prop :=
  ∀ (R : Type u) [CommRing R] (D j : ℕ), ⋀[R]^j (Fin D → R) = Li R D D ^ j

def F3 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b

def F4 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (m n : ℕ)
    (u v : ExteriorAlgebra R (Fin D → R)), u ∈ Li R D i ^ m → v ∈ Li R D i ^ n →
      u + eb R i * v = 0 → v = 0

def W : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ (i : Fin D) (r : R), s i * r ∈ Ii s i → r ∈ Ii s i

def Step : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ i : Fin D, P s i → P s ((i : ℕ) + 1)

def Sec : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (r : R),
    (∃ y ∈ ⋀[R]^1 (Fin D → R), dK s y = algebraMap R _ r) ↔ r ∈ Ideal.span (Set.range s)

end PI.KEX
end

section
universe u

namespace PI.KEX

open PI.KoszulExact

section Lemmas

variable {R : Type u} [CommRing R] {D : ℕ}

theorem form_single (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by
  simp [form, Pi.single_apply]

end Lemmas

end PI.KEX
end
