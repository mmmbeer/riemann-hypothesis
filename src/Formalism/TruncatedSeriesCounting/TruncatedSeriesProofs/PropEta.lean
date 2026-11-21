import Formalism.TruncatedSeriesCounting.LemmaDetPoly
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

open Formalism.NG Formalism.NG.QuotientPowerLengths Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Module IsDiscreteValuationRing

noncomputable section

universe u v w

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.EtaCongruenceSeparation

section
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type*} [Finite X]
  {T : Subalgebra O (X → O)} {V : Type*} [AddCommGroup V] [Module (FractionRing O) V]
  [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
  {act : T →+* Module.End (FractionRing O) V}

end

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.EtaCongruenceSeparation

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
