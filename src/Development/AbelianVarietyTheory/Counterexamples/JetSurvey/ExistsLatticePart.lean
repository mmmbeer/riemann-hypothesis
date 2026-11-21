import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.RigidAndInjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelMove

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)

section Identification

variable (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
  (oP : letI := H.starRing; P.toPre.OAct (𝓞 E))

end Identification

theorem exists_lattice_part {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 0 < n) (y : D.X) : ∃ p : QkPt D F n, p.y = y :=
  exists_qkPt GlobalTheory.abelianSchemeLaws_all.1.mulN (Or.inr GlobalTheory.abelianSchemeLaws_all.1.polBaseChange) hB hn.ne' y

end GlobalTheory.LevelMove
