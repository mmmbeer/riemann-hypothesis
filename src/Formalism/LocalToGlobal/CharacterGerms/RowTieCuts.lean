import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

structure IsMapFB {K C : Type} [Field K] [Field C] (φ : K →+* C) {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (B : FB K dd O) (B' : FB C dd O) : Prop where
  F : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j)
  act : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)
  ph1 : B'.ph1 = MvPowerSeries.map φ B.ph1
  ph2 : B'.ph2 = MvPowerSeries.map φ B.ph2
  sy : B'.sy = MvPowerSeries.map φ B.sy
  ad : ∀ a, B'.ad a = MvPowerSeries.map φ (B.ad a)

def EmbIntSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ t : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr t))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Formalism.L2.FormalSeriesBounds
