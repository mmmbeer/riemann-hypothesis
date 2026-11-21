import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroSecondCoordinate

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleIdentity

open PartialDerivEval

section Slice

variable {C : Type} [Field C] {V : VF C} {dd : ℕ}

end Slice

section Geo

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

def lift (a : Pt C 2 dd) : Pt C 3 dd := fun j => ev (n := 3) ![pt C dd 0, pt C dd 1] (a j)

abbrev S3 : Pt C 3 dd := addOf Y.B.G.F (pt C dd 0) (pt C dd 1)

abbrev L3 : Pt C 3 dd := comp1 (Y.nmul V.l) (pt C dd 2)

abbrev hx (a b : Pt C 3 dd) : PS C 3 dd := ev ![a, b] Y.h

abbrev G1 : PS C 3 dd := hx Y (pt C dd 0) (pt C dd 2) + hx Y (pt C dd 1) (pt C dd 2) - hx Y (S3 Y) (pt C dd 2)

end Geo

section Closed

end Closed

end CocycleIdentity

end Formalism.L2.FormalSeriesBounds
