import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IwSemistable

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

def ChainFibFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ)
    (i : Fin D.a) (w : Ideal (𝓞 D.F)), D.a = 1 → IsPlaceOf b i w →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s),
      Finite (Quot (fun C C' : HTIw o w => Nonempty (ChainMap C C' (𝟙 _) (𝟙 _))))

end GlobalTheory.IwLevel
