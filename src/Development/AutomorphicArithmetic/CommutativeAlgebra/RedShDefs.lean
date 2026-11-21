import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.RedSh

def Conn {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) (m : ℤ) : Prop :=
  (∀ n, n < m → Function.Bijective (pull R f F n)) ∧ Function.Injective (pull R f F m)

end UpperTheory.RedSh
