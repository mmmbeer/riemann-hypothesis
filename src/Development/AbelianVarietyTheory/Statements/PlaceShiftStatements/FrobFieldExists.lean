import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial

set_option autoImplicit false

noncomputable section

open CategoryTheory Polynomial NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.HT

def frobMin {k : Type} [Field k] [Fintype k] (A : AbVar k) : ℚ[X] := minpoly ℚ (toEnd0 A (frob A))

def IsFrobField {k : Type} [Field k] [Fintype k] (A : AbVar k) (F : Type) [Field F] [CharZero F]
    [Algebra F (End0 A)] (π : F) : Prop :=
  algebraMap F (End0 A) π = toEnd0 A (frob A) ∧ Algebra.adjoin ℚ {π} = ⊤

def FrobFieldExists : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A : AbVar k), IsSimple A →
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra F (End0 A)) (π : F), IsFrobField A F π

def Injective : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A B : AbVar k), IsSimple A → IsSimple B →
    (Isog A B ↔ frobMin A = frobMin B)

end GlobalTheory.HT
