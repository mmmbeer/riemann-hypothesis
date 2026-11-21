import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

structure IsStableFlag {T : Scheme.{0}} {O : Type} [Ring O] {A : Over T} [GrpObj A] (ρ : RingAct A O) {n : ℕ}
    (r : Fin (n + 1) → ℕ) (K : Fin (n + 1) → Over T) (_ : ∀ j, GrpObj (K j)) (i : ∀ j, K j ⟶ A) : Prop where
  hom : ∀ j, IsMonHom (i j)
  mono : ∀ j, Mono (i j)
  rank : ∀ j, IsIsogDeg (toUnit (K j)) (r j)
  stable : ∀ j, IsStable ρ (i j)
  incr : ∀ (j : Fin n) (T' : Over T) (x : T' ⟶ A), InSub (i j.castSucc) x → InSub (i j.succ) x

end GlobalTheory.IwLevel

end
