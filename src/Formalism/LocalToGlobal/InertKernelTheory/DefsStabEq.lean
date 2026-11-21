import Formalism.SharpRestriction.GrowthBounds.ChartComparison

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms

namespace Formalism.L2.KerInert.SecondKernelStabilizers

def Level.dbl {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {P : Places p O Kf} (C : Level P) : Level P where
  Γ := C.Γ × Multiplicative (ZMod 2)
  act v := (C.act v).comp (MonoidHom.fst _ _)
  χ := C.χ.comp (MonoidHom.fst _ _)

end Formalism.L2.KerInert.SecondKernelStabilizers
