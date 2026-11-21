import Mathlib
import Formalism.GelfandTransference.EnergyIdentity

namespace Formalism.SA.D

open NumberField Matrix
open scoped ComplexOrder

def kap {E : Type} [Field E] (σ : E →+* E) (T T' : ℚ) (ζ : E) : E :=
  ζ * σ ζ - ((T * T' : ℚ) : E)

def oo {E : Type} [Field E] (σ : E →+* E) (T T' : ℚ) (u u' ζ₁ ζ₂ : E) : E :=
  ζ₁ / kap σ T T' ζ₁ - σ u * u' * ζ₂ / kap σ T T' ζ₂

end Formalism.SA.D
