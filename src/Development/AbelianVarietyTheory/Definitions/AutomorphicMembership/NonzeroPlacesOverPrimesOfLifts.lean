import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.IrrationalRotationBk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StateChecks

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI





variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Wt : Set B.places.Pl}





section Types

variable {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T₀ : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m}
  {R : RealDat a.D A Ks} (F : Face a.D A) (y : Hd R) (y' : HdB b R) (E : Hs)

abbrev chB : ChainReal b.D := letI := alg b iK; y'.C (face b F)

abbrev lfB : LiftReal b.D (chB b F y') := letI := alg b iK; y'.L (face b F)






end Types

def copyR {Z : w.Lt} (Z' : w.Lt) {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt) :
    @RealDat3 (w.st Z').toD7 _ _ _ _ _ _ (famR (w.st Z') w.I hX (usedOf w.I T Wt) z.Xg z.tr) (coreJ (a := Z) Z' z.core).Q.c.F _ _
      ((by exact @alg B (@ColW.C B f T w) Z Z' (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instField (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instNF (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (Formalism.L2.Pj.instCMHost (@ColW.st B f T w Z).toD7) (@Formalism.L2.Pj.Par.H (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instField (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instNF (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (Formalism.L2.Pj.instCMHost (@ColW.st B f T w Z).toD7) (@Formalism.L2.Pj.Par.H (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))))) (@Dat.alg (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 (a := Z) Z' (iK := z.alg) z.R) :))






def St.rowsAre {P : Pre2 K w} (x : St P) (h : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) :
    RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0 where
  z := x.m.z
  intersectionNumber_baseChange := x.m.intersectionNumber_baseChange
  Y := x.r.Y
  Z := x.r.Z.full fun j v a b => (h j v a b).trans (x.m.eta j v).symm
  tup_ix t := (congrFun x.r.tup t).trans (x.m.tup t)

section Std

variable {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

set_option maxHeartbeats 2000000 in

theorem std_cpR (z : Dat a.st I hX T Wt) (h : z.Std) :
    @BrgStd b.st px I hX (usedOf I T Wt) z.Xg z.tr (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z)))
      (@RealDat3.toRealDat _ _ _ _ _ _ _ _ _ _ _ (kc% (alg b z.alg)) (cpR b z)) := by
  kexactB h

set_option maxHeartbeats 2000000 in

theorem std_of_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (h : z₀.Std) : z.Std := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact std_cpR b z₀ h

end Std

section StdState

theorem St.std {P : Pre2 K w} (x : St P) : x.m.z.Std :=
  std_of_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.std

theorem Pre2.vStd (P : Pre2 K w) (i) : FWT.VStd (w.st P.Z₀).toD7 i := (P.z.geo.pins i).2.lift.std

theorem gram_X (Z : w.Lt) : (w.st Z).toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h, -⟩ := w.ok.spaces
  change B.sp.X'.gram = 1
  rw [h]
  refine Matrix.ext fun (i j : Fin B.R.rankX') => ?_
  show Examples₂.diagForm (E := B.host.E) B.R.rankX' (fun _ => false) ((Pi.basisFun B.host.E (Fin B.R.rankX')) i) ((Pi.basisFun B.host.E (Fin B.R.rankX')) j) =
    (1 : Matrix (Fin B.R.rankX') (Fin B.R.rankX') B.host.E) i j
  rw [Pi.basisFun_apply, Pi.basisFun_apply, Examples₂.diagForm_single, Matrix.one_apply]
  simp [Examples₂.sgn]

theorem Pre2.std_row (P : Pre2 K w) : (w.st P.Z₀).toD7.sp.X'.rank = B.R.N B.R.m - 1 ∧ (w.st P.Z₀).toD7.sp.X'.gram = 1 ∧
    P.z.R.βX = 1 :=
  ⟨by rw [(w.st P.Z₀).toD7.sp.X'_rank, Formalism.L2.Col.rank_X'_eq]; rfl, gram_X _, P.z.lev.beta.2⟩


end StdState

end GlobalTheory.Mem.R3.Rw.StateChecks

end
