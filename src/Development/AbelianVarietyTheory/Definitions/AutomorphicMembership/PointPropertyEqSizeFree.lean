import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

structure Obj2 (D : D7) : Type 1 where

  gatT : GatTies D

  th : ThetaX D

  cmp : LatCmp D

  tw : TwForms D

  Gy : G.LatInst D

  errX : ErrX D

  nch : NChoice D

  xd : ThData D

  lev : LevelData D

  X : DivX D

  p0 : BaseLevelRowSide D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)

  amb : AmbForm D (RowSide.sharp D)

  amb0 : AmbForm D p0.s

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig

def layObj {D : D7} (Y : Lay D) : Obj2 D := { Y with }

def divXtr {D : D7} (X : DivX D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : DivX (setDiv D N h) :=
  divTr N h X

def Obj2.tr {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : Obj2 (setDiv D N h) where
  gatT := gatTr N h O.gatT
  th := thTr N h O.th
  cmp := cmpTr N h O.cmp
  tw := twTr N h O.tw
  Gy := latTr N h O.Gy
  errX := errTr N h O.errX
  nch := nchTr N h O.nch
  xd := xdTr N h O.xd
  lev := O.lev
  X := divTr N h O.X
  p0 := ⟨sideTr N h O.p0.s⟩
  ker := fun u w g => { O.ker u w g with }
  amb := { O.amb with }
  amb0 := { O.amb0 with }
  gauge := O.gauge

def pointPropertyOfObjects (QO : ∀ D : D7, Obj2 D → Prop) : PtProp := fun D _ gatT _ Gy _ X _ ex =>
  QO D { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
         lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def allDiv (QO : ∀ D : D7, Obj2 D → Prop) (D : D7) (Y : Lay D) : Prop := ∀ N h, QO (setDiv D N h) ((layObj Y).tr N h)

def extraObj {D : D7} {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D}
    {cX : ExtraC} (ex : Extra D L gatT Gx Gy K X cX) : Obj2 D :=
  { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
    lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def ofObj {D : D7} (O : Obj D) : Obj2 D := extraObj O.ex

def pointObj {C : FC} (p : Pt C) : Obj2 p.D := extraObj p.xa.ex




theorem ofObj_obj {C : FC} {D : D7} (Y : Lay D) (p : LedPart C Y) : ofObj (Y.obj p) = layObj Y := rfl




theorem pointObj_pt {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y) : pointObj p.pt = (layObj Y).tr (nPrime p.L) p.ht := rfl




example {C : FC} (p : Pt C) (N : ∀ u, Submodule (𝓞 p.D.what₂.LL) (p.D.div.Nu u).V) (h : p.D.what₂.Word → ℝ) :
    Nonempty (Obj2 p.D) ∧ Nonempty (Obj2 (setDiv p.D N h)) :=
  ⟨⟨pointObj p⟩, ⟨(pointObj p).tr N h⟩⟩

example {C : FC} (p : Pt C) : (pointObj p).amb = p.xa.ex.amb ∧ (pointObj p).amb0 = p.xa.ex.amb0 ∧
    (pointObj p).gauge = p.xa.ex.gauge := ⟨rfl, rfl, rfl⟩

example {C : FC} (p : Pt C) :
    p.Has (pointPropertyOfObjects fun D O => LocalQuadraticParts.PeterssonBoundAllEmbeddings D O.X O.amb) ↔ LocalQuadraticParts.PeterssonBoundAllEmbeddings p.D p.xa.X p.xa.ex.amb := Iff.rfl

example {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) :
    (O.tr N h).amb.MtH = O.amb.MtH ∧ (O.tr N h).amb0.MtH = O.amb0.MtH ∧ (O.tr N h).gauge = O.gauge ∧
      (O.tr N h).X.kapR = O.X.kapR := ⟨rfl, rfl, rfl, rfl⟩

example (D : D7) (Y : Lay D) : allDiv (fun D O => letI := D.host.cmStar; O.gauge.IsGauge) D Y := fun _ _ => Y.gauge_def

example (D : D7) (Y : Lay D) : ¬ allDiv (fun D _ => D.div.h D.u₀ = 0) D Y := fun H =>
  one_ne_zero (H (fun u => (D.div.Nu u).L) (fun _ => 1))

end GlobalTheory.Mem.Top

end
