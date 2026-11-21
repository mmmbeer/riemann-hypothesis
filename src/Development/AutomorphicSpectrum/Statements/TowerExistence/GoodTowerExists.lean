import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GoodTowerExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)],
    IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q →
      ∃ T : RootTower (CMType H) (D.p + D.q), Nonempty (GoodOrigin Y T)

end GlobalTheory.CompanionTheory.Ar.Top
