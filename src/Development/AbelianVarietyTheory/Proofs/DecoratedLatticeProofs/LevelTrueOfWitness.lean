import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CornerCoordinateAutomatic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest
open GlobalTheory.Fam

section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {a : GeoAll W u}

variable {k : Cst a} {row : ∀ t, RowCh (pk W) (lvP W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}
  {w₀ w : ∀ t, VTup ((a.fam row col).t t)} {F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)}

theorem places (h : ColOut k w₀ w F) (t) (p) : p ∈ (w t).Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 D.host.F) := by
  obtain ⟨pl, hp⟩ := (h.lev t).places
  rw [(h.same t).1, (h.pins t).places]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pl i).1, (pl i).2, (hp i).2⟩
  · rintro ⟨PP, hP, rfl⟩
    refine ⟨pl.symm ⟨PP, hP⟩, ?_⟩
    rw [(hp _).2, Equiv.apply_symm_apply]

end Gen

section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True
end GlobalTheory.Fam.ColTest
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest

theorem isTypePlaces_vGs {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (h : I.Ok) :
    GlobalTheory.Core.Mi.IsTypePlaces (D := I.rec7 l Z) (B.primes X).vGs := by
  classical
  obtain ⟨L, hC, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit (I.rec7 l Z) (TC.cf I l Z)
  have hP : L.Pg = (B.primes X).vGs := by
    ext w
    rw [hL.Pg w, hC]
    have hv : w ∈ (B.primes X).vGs ↔ (I.C.P.Div 0 w ∨ I.C.P.Div 1 w) := by
      rw [← h.pibar 0 w, ← h.pibar 1 w]
      exact @Finset.mem_union _ (_) _ _ _
    exact (hv.trans (Fin.exists_fin_two (p := fun k => I.C.P.Div k w)).symm).symm
  rw [← hP]
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh hL

end GlobalTheory.Fam.ColTest

end
end

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.BundleLev

theorem lev_of_btw {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) (x : R3.TwIn O.ex) (y : Bl.BTw b x) :
    (pk (packB b)).Pg = x.R.Pg ∧ ∀ t, (pk (packB b)).xiH t = x.R.toLevCh.xiH (x.Y.tupT ((packB b).P.I.tup t)) := by
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y →
      k.B.Q.Rl.toRealDat.Pg = x.R.Pg ∧ ∀ t, k.B.Q.Rl.toRealDat.xiH t = x.R.toLevCh.xiH (x.Y.tupT (k.P.I.tup t)) := by
    intro k hk
    subst hk
    refine ⟨rfl, fun t => ?_⟩
    exact (congrArg x.R.toLevCh.xiH (x.Y.tupT_tup t)).symm
  exact key (Bl.rpkB b) y.eq

set_option maxHeartbeats 1000000 in

theorem lev_of_args {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) :
    x.R.Pg = (q.B.primes q.w.px).vGs ∧
      ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → x.R.toLevCh.xiH (x.Y.tupT μ) = q.w.I.xi μ := by
  have h := GlobalTheory.Mem.R3.twArgs_lev K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have e : a.x = x := eq_of_heq ax
  subst e
  exact ⟨eq_of_heq h.2.1, fun μ hμ => eq_of_heq (h.2.2.1 μ hμ).2⟩

set_option maxHeartbeats 1000000 in

theorem levTrue_packB : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → LevTrue (packB b) := by
  intro hL p K q c b hw
  have h1 := lev_of_btw b hw.x hw.y
  have h2 := lev_of_args q hw.x hw.a hw.ax
  have hPg : (pk (packB b)).Pg = (q.B.primes q.w.px).vGs := h1.1.trans h2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hPg]
    exact ColTest.isTypePlaces_vGs q.w.I q.w.l q.Z q.w.ok
  · intro PP
    rw [hPg]
    exact Iff.rfl
  · intro t
    exact (h1.2 t).trans (h2.2 _ (GlobalTheory.MiS.Check.used_all (packB b) t))

end GlobalTheory.Fam.BundleLev
end
