import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.FinrankISupLeSum
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage
import Formalism.LocalToGlobal.IndefiniteReal.CxCutPO
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.EigSumLeComapSemi
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.LatticeGeometry.FormsK
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure CxPrims (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (cv : CrdV A.fam.amb) (s : ℕ)
    (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop)
    (ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  kerStabR : X.KerStabR

  kerStabL : X.KerStabL

  adjClosedR : X.AdjClosedR

  adjClosedL : X.AdjClosedL

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  jIsoR : X.JIsoR cv

  jIsoL : X.JIsoL cv

  ok : A.fam.Ok s

  sep : A.fam.TypesSep

  heckeR : HeckeRatR A

  heckeL : HeckeRatL A

  eig0 : LiftsEig A X P0 ψ0 C0

  eig1 : LiftsEig A X P1 ψ1 C1

  typ0 : LiftsTyp A C0

  typ1 : LiftsTyp A C1

  pos : ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  w1 : ∀ w, X.W1 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  h4pos : X.H4pos

  isoR : ∀ b, X.IsoR (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  crdZ : ∀ b, X.CrdZ (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  coordinates_in_good_part : ∀ b, X.CoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  ratLev : ∀ b, X.RatLev (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  dnLev : ∀ b, X.DnLev cv b

  upLev : ∀ b, X.UpLev cv b

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  ratMu : ∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  h3 : ∀ b, X.H3 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  isoL : ∀ b, X.IsoL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  crdZL : ∀ b, X.CrdZL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  lift_coordinates_in_good_part : ∀ b, X.LiftCoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  ratLevL : ∀ b, X.RatLevL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  dnLevL : ∀ b, X.DnLevL cv b

  upLevL : ∀ b, X.UpLevL cv b

  thmAop : ∀ b, X.ThmAop b

  partsW : ∀ b, X.PartsW b

  ratTh : ∀ b, X.RATth (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  h3W : ∀ b, X.H3W (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  galD : ∀ b, X.GalD (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  dimParts : ∀ b, X.DimParts b

  l3 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  btVanish : X.BtVanish (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

  mi0 : X.MatrixIdentityOffBase (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ

  zetaOK : X.ZetaOK ζ

  l1e : (X.colOf (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

  passage : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
    (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

  fun0 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

section All

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {X : CxData A.fam.amb} {cv : CrdV A.fam.amb} {s : ℕ}
  {C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop}
  {ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH}
  {C CH : ℝ}

theorem CxPrims.stable (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) : X.zs.Stable :=
  CxData.cutStable X hP.kFormR hP.kFormL hP.kerStabR hP.kerStabL hP.adjClosedR hP.adjClosedL

theorem CxPrims.wf (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A.side_WF hP.ok P0 ψ0 X.zs hP.stable hP.inBlock hP.sep
  | true => A.side_WF hP.ok P1 ψ1 X.zs hP.stable hP.inBlock hP.sep

theorem links_of_prims (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE) C CH := by
  have hW := hP.wf
  have hst := hP.stable
  have what₂ := fun b => cutRows (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b (hW b) hP.h4pos (hP.isoR b) (hP.crdZ b)
    (hP.coordinates_in_good_part b) (hP.ratLev b) (hP.dnLev b) (hP.upLev b) (hP.thmBop b) (hP.partsE b)
  have lifts := fun b => CxData.cutLifts X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b (hW b) hP.h4pos (hP.kForm b)
    (hP.isoL b) (hP.crdZL b) (hP.lift_coordinates_in_good_part b) (hP.ratLevL b) (hP.dnLevL b) (hP.upLevL b) (hP.thmAop b) (hP.partsW b)
  have types := cutTypes A X P0 ψ0 P1 ψ1 Dc Sp Zsc s C0 C1 hP.ok hP.sep hst hP.eig0 hP.eig1 hP.typ0 hP.typ1
  exact
    { stable := hst
      inBlock := hP.inBlock
      ratZ := hP.ratZ
      pos := hP.pos
      proviso := cutProviso A X P0 ψ0 P1 ψ1 Dc Sp Zsc s C0 C1 hP.ok hP.heckeL hP.eig0 hP.eig1
      types := types
      partsOrth := cutPartsOrth A X P0 ψ0 P1 ψ1 Dc Sp Zsc s hP.ok hP.heckeR hst
      h0 := hP.h0
      h2 := fun b => (what₂ b).1
      ratMu := hP.ratMu
      h3 := hP.h3
      h4pos := hP.h4pos
      h4 := fun b => (what₂ b).2
      kForm := hP.kForm
      mLat := hP.mLat
      ewNorm := hP.ewNorm
      h5 := fun b => (lifts b).1
      ratTh := hP.ratTh
      h3W := hP.h3W
      thmA := fun b => (lifts b).2
      galD := hP.galD
      l1d := fun b => CxData.cutDims X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b (hW b) hP.h4pos (hP.kForm b) (hP.ewNorm b)
        (types b) (what₂ b).1 (hP.ratMu b) (hP.h3 b) (lifts b).1 (hP.ratTh b) (hP.h3W b) (hP.partsE b) (hP.partsW b)
        (hP.dimParts b)
      l3 := hP.l3
      on := hP.on
      l6 := hP.l6
      l1b := CxData.cutPairing X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ sEE (hW true) (what₂ true).1 hP.btVanish hP.mi0 hP.zetaOK
      l1e := hP.l1e
      untw := CxData.cutTuples2 X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH hP.h0 hP.w1
      passage := hP.passage
      fun0 := hP.fun0 }

end All

end Formalism.IndefR.Cx
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure CxCore (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (s : ℕ)
    (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop)
    (ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE)
    (hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  jIsoR : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)

  jIsoL : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)

  npTie : NPTie X P0 P1

  ok : A.fam.Ok s

  sep : A.fam.TypesSep

  heckeR : HeckeRatAllR A

  heckeL : HeckeRatAllL A

  thetaR : HeckeThetaR A X hE

  thetaL : HeckeThetaL A X hW

  gUnit : Formalism.IndefR.CxPass.GUnit A X gE

  gEquiv : Formalism.IndefR.CxPass.GEquiv A X gE

  lev0 : Formalism.IndefR.CxPass.LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0

  lev1 : Formalism.IndefR.CxPass.LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1

  h2P : Formalism.IndefR.CxPass.PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc)

  gUnitL : Formalism.IndefR.CxPass.GUnitL A X gW

  gEquivL : Formalism.IndefR.CxPass.GEquivL A X gW

  lower_level_lift_type : Formalism.IndefR.CxPass.LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0

  upper_level_lift_type : Formalism.IndefR.CxPass.LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW true P1 ψ1

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  eig0 : LiftsEig A X P0 ψ0 C0

  eig1 : LiftsEig A X P1 ψ1 C1

  typ0 : LiftsTyp A C0

  typ1 : LiftsTyp A C1

  pos : ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  w1 : ∀ w, X.W1 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  h4pos : X.H4pos

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  ratMu : ∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  thmAop : ∀ b, X.ThmAop b

  partsW : ∀ b, X.PartsW b

  ratTh : ∀ b, X.RATth (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  galD : ∀ b, X.GalD (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  dimParts : ∀ b, X.DimParts b

  l3 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  btVanish : X.BtVanish (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

  mi0 : X.MatrixIdentityOffBase (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ

  zetaOK : X.ZetaOK ζ

  l1e : (X.colOf (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

  fun0 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

section Core

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {X : CxData A.fam.amb} {s : ℕ}
  {C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop}
  {ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH}
  {C CH : ℝ}
  {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

theorem CxCore.stable (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) : X.zs.Stable :=
  CxData.cutStable X hC.kFormR hC.kFormL
    (Formalism.IndefR.CxPass.kerStabR_of hC.kFormR hC.gEquiv (kerStabR_hecke hC.thetaR))
    (Formalism.IndefR.CxPass.kerStabL_of hC.kFormL hC.gEquivL (kerStabL_hecke hC.thetaL))
    (adjClosedR_of hC.ok hC.heckeR hC.kFormR hC.jIsoR) (adjClosedL_of hC.ok hC.heckeL hC.kFormL hC.jIsoL)

theorem CxCore.wf (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) :
    ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A.side_WF hC.ok P0 ψ0 X.zs hC.stable hC.inBlock hC.sep
  | true => A.side_WF hC.ok P1 ψ1 X.zs hC.stable hC.inBlock hC.sep

theorem CxCore.h2 (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW) (b : Bool) :
    X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  (cutRows (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b (hC.wf b) hC.h4pos
    (isoR_of hC.ok hC.jIsoR hC.npTie b) (crdZ_of X b) (coordinates_in_good_part_of_definite X b)
    (Formalism.IndefR.CxPass.ratLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv b)
    (Formalism.IndefR.CxPass.dnLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1 b)
    (Formalism.IndefR.CxPass.upLev_of hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1 b)
    (hC.thmBop b) (hC.partsE b)).1

theorem prims_of_core (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW)
    (hPass : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)) :
    CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X (cvOf A P0 ψ0 P1 ψ1) s C0 C1 ζ sEE C CH := by
  have kR : X.KerStabR := Formalism.IndefR.CxPass.kerStabR_of hC.kFormR hC.gEquiv (kerStabR_hecke hC.thetaR)
  have kL : X.KerStabL := Formalism.IndefR.CxPass.kerStabL_of hC.kFormL hC.gEquivL (kerStabL_hecke hC.thetaL)
  have aR : X.AdjClosedR := adjClosedR_of hC.ok hC.heckeR hC.kFormR hC.jIsoR
  have aL : X.AdjClosedL := adjClosedL_of hC.ok hC.heckeL hC.kFormL hC.jIsoL
  have hst : X.zs.Stable := CxData.cutStable X hC.kFormR hC.kFormL kR kL aR aL
  exact
    { kFormR := hC.kFormR, kFormL := hC.kFormL, kerStabR := kR, kerStabL := kL, adjClosedR := aR, adjClosedL := aL
      inBlock := hC.inBlock, ratZ := hC.ratZ, jIsoR := hC.jIsoR, jIsoL := hC.jIsoL, ok := hC.ok, sep := hC.sep
      heckeR := hC.heckeR A.fam.μ0, heckeL := fun j => hC.heckeL j A.fam.μ0
      eig0 := hC.eig0, eig1 := hC.eig1, typ0 := hC.typ0, typ1 := hC.typ1, pos := hC.pos, h0 := hC.h0, w1 := hC.w1
      h4pos := hC.h4pos, isoR := isoR_of hC.ok hC.jIsoR hC.npTie, crdZ := crdZ_of X, coordinates_in_good_part := coordinates_in_good_part_of_definite X
      ratLev := Formalism.IndefR.CxPass.ratLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv
      dnLev := Formalism.IndefR.CxPass.dnLev_of hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1
      upLev := Formalism.IndefR.CxPass.upLev_of hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1
      thmBop := hC.thmBop, partsE := hC.partsE
      ratMu := hC.ratMu, h3 := equivRows_of P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormR hst hC.ok hC.thetaR
      kForm := hC.kForm, mLat := hC.mLat, ewNorm := hC.ewNorm, isoL := isoL_of hC.ok hC.jIsoL hC.npTie
      crdZL := crdZL_of X, lift_coordinates_in_good_part := lift_coordinates_in_good_part_of_definite X
      ratLevL := Formalism.IndefR.CxPass.ratLevL_of hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL
      dnLevL := Formalism.IndefR.CxPass.dnLevL_of hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL hC.lower_level_lift_type hC.upper_level_lift_type
      upLevL := Formalism.IndefR.CxPass.upLevL_of hC.ok hC.kFormL hC.jIsoL hC.gUnitL hC.gEquivL hC.lower_level_lift_type hC.upper_level_lift_type
      thmAop := hC.thmAop, partsW := hC.partsW, ratTh := hC.ratTh
      h3W := equivLifts_of P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormL hst hC.ok hC.thetaL
      galD := hC.galD, dimParts := hC.dimParts, l3 := hC.l3, on := hC.on, l6 := hC.l6, btVanish := hC.btVanish
      mi0 := hC.mi0, zetaOK := hC.zetaOK, l1e := hC.l1e, passage := hPass, fun0 := hC.fun0 }

theorem links_of_core (hC : CxCore A P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 C1 ζ sEE C CH hE hW gE gW)
    (hPass : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)) :
    X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE) C CH :=
  links_of_prims (prims_of_core hC hPass)

end Core

end Formalism.IndefR.Cx
end
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo

namespace Formalism.IndefR.Arith

section Comparison₂

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
variable (P : FormsPkg D G NW CompW algW PtY) [Algebra P.KO D.what₂.LL]
variable {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module P.KO WL] [IsScalarTower P.KO D.what₂.LL WL]
  [Module (𝓞 P.KO) WL] [IsScalarTower (𝓞 P.KO) P.KO WL]
variable {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0]

def TiedTo (j : ℕ) (w : WeightFamilies.Wt D j) (A : FormsL D.what₂.LL P.KO WL W G0) (ι : P.Cusp j w →ₗ[P.KO] WL) : Prop :=
  w.n = D.R.nV ∧ wtOf w = DV.kapW D j ∧ (∀ a : P.KO, algebraMap P.KO D.what₂.LL a = P.kL a) ∧
    Function.Injective ι ∧ (∀ x, x ∈ A.WK ↔ x ∈ LinearMap.range ι) ∧ ∀ F, ι F ∈ A.MK ↔ F ∈ P.Mlat j w

def NormTie (pos : (D.what₂.LL →+* ℂ) → Prop) (c : ℝ) {j : ℕ} {w : WeightFamilies.Wt D j} (A : FormsL D.what₂.LL P.KO WL W G0)
    (ι : P.Cusp j w →ₗ[P.KO] WL) : Prop :=
  ∀ σ, pos σ → ∀ F, A.nrmAt σ (ι F) = c * P.l2NormAlt j w (σ.comp P.kL) F

theorem NormTie.rigid {pos : (D.what₂.LL →+* ℂ) → Prop} {c : ℝ} (hc : 0 < c) {j : ℕ} {w : WeightFamilies.Wt D j}
    {A : FormsL D.what₂.LL P.KO WL W G0} {ι : P.Cusp j w →ₗ[P.KO] WL} (h : NormTie P pos c A ι) {a : D.what₂.LL}
    (h' : ∀ σ, pos σ → ∀ F, ‖A.j σ (a • ι F)‖ = c * P.l2NormAlt j w (σ.comp P.kL) F)
    {F : P.Cusp j w} (hF : F ≠ 0) {σ : D.what₂.LL →+* ℂ} (hσ : pos σ) : ‖σ a‖ = 1 := by
  have h1 := h σ hσ F
  have h2 := h' σ hσ F
  rw [map_smulₛₗ, norm_smul] at h2
  unfold FormsL.nrmAt at h1
  have h3 : c * P.l2NormAlt j w (σ.comp P.kL) F ≠ 0 :=
    mul_ne_zero hc.ne' fun e => hF ((P.l2Norm_eq_zero_iff _ _ _ _).1 e)
  rw [h1] at h2
  exact mul_right_cancel₀ h3 (h2.trans (one_mul _).symm)

end Comparison₂

section Fam

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type} {Fam : ShimFam D G Lev} (K : FormsKPkg Fam)
variable [Algebra K.fs.KO D.what₂.LL]
variable {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module K.fs.KO WL]
  [IsScalarTower K.fs.KO D.what₂.LL WL] [Module (𝓞 K.fs.KO) WL] [IsScalarTower (𝓞 K.fs.KO) K.fs.KO WL]
variable {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0]

def ActTie (e : G0 ≃* K.Hb) (j : ℕ) (w : WeightFamilies.Wt D j) (A : FormsL D.what₂.LL K.fs.KO WL W G0)
    (ι : K.fs.Cusp j w →ₗ[K.fs.KO] WL) : Prop :=
  ∀ g (F F' : K.fs.Cusp j w), e g • K.fs.inc j w F = K.fs.inc j w F' → A.ρ g (ι F) = ι F'

def CompatibleAtCompactLevel (e : G0 ≃* K.Hb) (pos : (D.what₂.LL →+* ℂ) → Prop) (volRec : ℝ) (j : ℕ) (w : WeightFamilies.Wt D j)
    (A : FormsL D.what₂.LL K.fs.KO WL W G0) (ι : K.fs.Cusp j w →ₗ[K.fs.KO] WL) : Prop :=
  K.κs = Fam.κg ∧ 1 ≤ j ∧ j ≤ D.R.m ∧ TiedTo K.fs j w A ι ∧ ActTie K e j w A ι ∧
    NormTie K.fs pos (Real.sqrt (volRec * dimKap D j)) A ι

end Fam

end Formalism.IndefR.Arith
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

namespace Tw

variable {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem adjoint_map [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (Tw.map s f) = Tw.map s (LinearMap.adjoint f) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  show cj s (inner ℂ (LinearMap.adjoint f (out x)) (out y)) = cj s (inner ℂ (out x) (f (out y)))
  rw [LinearMap.adjoint_inner_left]

theorem linInd' (s : Bool) {ι : Type} {v : ι → E} (h : LinearIndependent ℂ v) :
    LinearIndependent ℂ fun i => mk s (v i) := by
  rw [linearIndependent_iff'] at h ⊢
  intro u g hg i hi
  have h1 : ∑ i ∈ u, cj s (g i) • v i = 0 := hg
  have := congrArg (cj s) (h u (fun i => cj s (g i)) h1 i hi)
  rwa [cj_cj, map_zero] at this

theorem mk_smul (s : Bool) (c : ℂ) (y : E) : mk s (c • y) = cj s c • mk s y := by
  show c • y = cj s (cj s c) • y
  rw [cj_cj]

theorem span_top' (s : Bool) {ι : Type} {v : ι → E} (h : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  change mk s (out x) ∈ _
  generalize out x = y at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [mk_smul]
    exact Submodule.smul_mem _ _ hy

end Tw

section Semi

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem span_semi (f : V →ₛₗ[σ] W) {κ : Type} (c : Module.Basis κ K V) :
    Submodule.span ℂ (Set.range fun i => f (c i)) = Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨c i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span K (Set.range c) := c.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem linInd_semi (f : V →ₛₗ[σ] W) {ι ι' : Type} [Finite ι] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V)
    (h : LinearIndependent ℂ fun i => f (b i)) : LinearIndependent ℂ fun i => f (b' i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have : Finite ι' := Module.Finite.finite_basis b'
  have : Fintype ι' := Fintype.ofFinite ι'
  rw [linearIndependent_iff_card_eq_finrank_span] at h ⊢
  unfold Set.finrank at h ⊢
  rw [span_semi f b']
  rw [span_semi f b] at h
  rw [← h]
  exact (Module.finrank_eq_card_basis b').symm.trans (Module.finrank_eq_card_basis b)

theorem kForm_semi {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (g : V →ₛₗ[σ] H)
    (e : H →ₗ[ℂ] X) (f : V →ₛₗ[σ] X) (hj : ∀ x, e (g x) = f x) (hinj : Function.Injective e)
    (hrange : LinearMap.range e = Submodule.span ℂ (Set.range f)) {ι ι' : Type} [Finite ι] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V)
    (h : LinearIndependent ℂ fun i => f (b i)) :
    LinearIndependent ℂ (fun i => g (b' i)) ∧ Submodule.span ℂ (Set.range fun i => g (b' i)) = ⊤ := by
  refine ⟨LinearIndependent.of_comp e ?_, ?_⟩
  · have e1 : (e ∘ fun i => g (b' i)) = fun i => f (b' i) := funext fun i => hj _
    rw [e1]
    exact linInd_semi f b b' h
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, hrange]
    have e1 : (e ∘ fun i => g (b' i)) = fun i => f (b' i) := funext fun i => hj _
    rw [e1, span_semi f b']

end Semi


theorem vw_root {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) (hn : 0 < n)
    (h : a ^ n = 1) : Formalism.DivisionValues.vw w a = 0 := by
  have h1 : (n : ℤ) * Formalism.DivisionValues.vw w a = 0 := by
    unfold Formalism.DivisionValues.vw
    rw [← FractionalIdeal.count_pow, FractionalIdeal.spanSingleton_pow, h, FractionalIdeal.spanSingleton_one,
      FractionalIdeal.count_one]
  exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Links

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

set_option maxHeartbeats 1000000 in
theorem kFormR_of (hM : R.IsModels) : (R.toCx F).KFormR := by
  intro t
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX t
  have h := kForm_semi (R.jX t) (R.HX t).e (R.B.R t).pres.extL (fun x => hM.jX t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact ⟨Tw.linInd' (E := (R.HX t).H) _ h.1, Tw.span_top' (E := (R.HX t).H) _ h.2⟩

set_option maxHeartbeats 1000000 in
theorem kFormL_of (hM : R.IsModels) : (R.toCx F).KFormL := by
  intro i t
  have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L i t).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HV i t
  have h := kForm_semi (R.jV i t) (R.HV i t).e (R.B.L i t).pres.extL (fun x => hM.jV i t x) hinj (hrange.trans hB.2.symm)
    (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hB.1
  exact ⟨Tw.linInd' (E := (R.HV i t).H) _ h.1, Tw.span_top' (E := (R.HV i t).H) _ h.2⟩

set_option maxHeartbeats 1000000 in

theorem jIsoR_gen (hM : R.IsModels) (cv : CrdV A.fam.amb)
    (hcv : ∀ t x y, cv.hR t x y = (A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) :
    (R.toCx F).JIsoR cv := by
  intro t x y
  have key : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jX t x) (R.jX t y)) =
      A.v0.embedding ((A.fam.R t).S.csum ((x : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V) ((y : (A.fam.R t).S.Forms) : (A.fam.R t).S.Cl → (A.fam.R t).S.V)) := by
    rw [(hM.HX t).2.2, hM.jX, hM.jX, R.emb0]
    congr 1
    exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.R t).pres x y
  rw [hcv]
  exact key

theorem jIsoR_of (hM : R.IsModels) : (R.toCx F).JIsoR (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) :=
  jIsoR_gen hM _ fun _ _ _ => rfl

set_option maxHeartbeats 1000000 in

theorem jIsoL_gen (hM : R.IsModels) (cv : CrdV A.fam.amb)
    (hcv : ∀ i t x y, cv.hL i t x y = (A.fam.L i t).S.csum ((x : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V) ((y : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V)) :
    (R.toCx F).JIsoL cv := by
  intro i t x y
  have key : cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jV i t x) (R.jV i t y)) =
      A.v0.embedding ((A.fam.L i t).S.csum ((x : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V) ((y : (A.fam.L i t).S.Forms) : (A.fam.L i t).S.Cl → (A.fam.L i t).S.V)) := by
    rw [(hM.HV i t).2.2, hM.jV, hM.jV, R.emb0]
    congr 1
    exact Formalism.IndefR.Bridge.ClassPres.isom_holds (R.B.L i t).pres x y
  rw [hcv]
  exact key

theorem jIsoL_of (hM : R.IsModels) : (R.toCx F).JIsoL (cvOf A F.P0 F.ψ0 F.P1 F.ψ1) :=
  jIsoL_gen hM _ fun _ _ _ _ => rfl

theorem prod_lamN (t : T) (p : A.fam.base.Ix) :
    ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j : Fin D.R.m, R.lam j t p A.v0 := by
  have h1 : ∀ n : ℕ, ∀ g : ℕ → ℝ, ∏ j ∈ Finset.Icc 1 n, g j = ∏ j ∈ Finset.range n, g (j + 1) := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]
  rw [h1, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold lamN
  rw [dif_pos (by simp)]
  exact congrArg (fun k => R.lam k t p A.v0) (Fin.ext (Nat.add_sub_cancel _ _))

set_option maxHeartbeats 1000000 in
theorem thmAop_of (h : ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp i) fun p => R.lam i t p A.v0)
    (b : Bool) : (R.toCx F).ThmAop b := by
  intro j t p w hw
  have hw1 : Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) w ∈ R.Wp j p := hw.1
  have key : Tw.map (twAt D.what₂.embLL A.v0) (R.thG j t) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.thG j t)) w) =
      ((R.lam j t p A.v0 : ℝ) : ℂ) • w := by
    rw [Tw.adjoint_map]
    show Tw.mk _ (R.thG j t (LinearMap.adjoint (R.thG j t) (Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) w))) = _
    rw [h j t p _ hw1, Tw.mk_smul, cj_ofReal]
    rfl
  exact key

set_option maxHeartbeats 1000000 in
theorem thmBop_of (h : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp R.lamN R.kap) (b : Bool) :
    (R.toCx F).ThmBop b := by
  intro t p e he
  have he1 : Tw.out (s := twAt D.what₂.embLL A.v0) (E := R.HE.H) e ∈ R.EEp p := he.1
  have key : Tw.map (twAt D.what₂.embLL A.v0) (R.Th t) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)) e) =
      ((R.kap * ∏ j : Fin D.R.m, R.lam j t p A.v0 : ℝ) : ℂ) • e := by
    rw [Tw.adjoint_map]
    show Tw.mk _ (R.Th t (LinearMap.adjoint (R.Th t) (Tw.out (s := twAt D.what₂.embLL A.v0) (E := R.HE.H) e))) = _
    have h2 := h t p (Tw.out (s := twAt D.what₂.embLL A.v0) (E := R.HE.H) e) he1
    rw [LinearMap.comp_apply] at h2
    rw [h2, Tw.mk_smul, cj_ofReal, prod_lamN]
    rfl
  exact key

theorem zetaOK_of (Y : RealCol R F) (hY : Y.Char) : (R.toCx F).ZetaOK (fc := F.fc) Y.ζ := by
  refine ⟨hY.zeta0, fun u t h0 => ?_, fun u w => ?_⟩
  · obtain ⟨n, hn, h⟩ := hY.zeta u t
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  · obtain ⟨n, hn, h⟩ := hY.zeta u ((R.toCx F).μ w)
    exact vw_root w _ n hn h

end RealDat

end Links

section Prim

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

abbrev cv : CrdV A.fam.amb := cvOf A F.P0 F.ψ0 F.P1 F.ψ1

def PThmA : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp i) fun p => R.lam i t p A.v0

def PThmB : Prop := Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp R.lamN R.kap

def TopMult : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
    MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

def PConj : Prop := ∀ i, (R.FW i).GalA

def PEig : Prop :=
  ∃ C0 C1, LiftsEig A (R.toCx F) F.P0 F.ψ0 C0 ∧ LiftsEig A (R.toCx F) F.P1 F.ψ1 C1 ∧ LiftsTyp A C0 ∧ LiftsTyp A C1

def PHecke : Prop := (∃ hE, HeckeThetaR A (R.toCx F) hE) ∧ ∃ hW, HeckeThetaL A (R.toCx F) hW

def PGUnit : Prop := CxPass.GUnit A (R.toCx F) (R.gEx F) ∧ CxPass.GUnitL A (R.toCx F) (R.gWx F)

def PGEquiv : Prop := CxPass.GEquiv A (R.toCx F) (R.gEx F) ∧ CxPass.GEquivL A (R.toCx F) (R.gWx F)

def PLevE : Prop :=
  CxPass.LevType A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) false F.P0 F.ψ0 ∧
    CxPass.LevType A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) true F.P1 F.ψ1 ∧
    CxPass.PrincipalInjectiveCommonRange A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)

def PLevW : Prop :=
  CxPass.LevTypeL A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0 ∧
    CxPass.LevTypeL A (R.toCx F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) true F.P1 F.ψ1

variable {R F}

theorem inNonzeroPlaces_recursive_iff (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : R.NonzeroIndexPlace F w ↔ (R.toCx F).W1 F.cr (R.num F C CH) w := by
  constructor
  · rintro ⟨w', hw | hw, i, h⟩
    · subst hw
      rcases h with h | h | h | h | h
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr (Or.inl h)⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    · subst hw
      rw [ValuationRepresentative.conjPl_conjPl] at h
      rcases h with h | h | h | h | h
      · exact ⟨i, Or.inr (Or.inl h)⟩
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
      · exact ⟨i, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · rintro ⟨i, h | h | h | h | h | h⟩
    · exact ⟨w, Or.inl rfl, i, Or.inl h⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inl h)⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨conjPl w, Or.inr rfl, i, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨w, Or.inl rfl, i, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩

end RealDat

open RealDat in

structure PrimLinks (R : RealDat D A Ks) (F : Face D A) (Y : RealDat.RealCol R F) (C CH : ℝ) : Prop where
  heckeR : HeckeRatAllR A
  heckeL : HeckeRatAllL A
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : R.LBlock F
  ratZ : R.LRatZ F
  eig : R.PEig F
  pos : R.LPos F
  posScal : R.LPosScal
  levE : R.PLevE F
  thmB : R.PThmB
  sumE : ∀ b, (R.toCx F).PartsE b
  ratMu : R.LRatMu F
  unif : R.LUnif
  conj : R.PConj
  levelW : R.LLevelW F
  integral : R.LIntegral
  mLat : R.LMLat F
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : ∀ b, (R.toCx F).PartsW b
  ratTh : R.LRatTh F
  scalConj : R.LScalConj F
  dimParts : ∀ b, (R.toCx F).DimParts b
  covol : R.LCovol F C CH
  onto : R.LOnto F C CH
  lamLow : R.LLamLow F C CH
  btVanish : (R.toCx F).BtVanish (fc := F.fc)
  mi0 : (R.toCx F).MatrixIdentityOffBase F.cr Y.ζ
  period : LPeriod Y
  passage : R.LPassage F C CH
  fun0 : R.LFun F C CH

theorem cxLinks_of_prims {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) {R : RealDat D A Ks} {F : Face D A}
    {Y : RealDat.RealCol R F} {C CH : ℝ} (hC : R.Char F) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    (R.toCx F).CxLinks F.cr Y.toCol C CH := by
  obtain ⟨C0, C1, e0, e1, t0, t1⟩ := hP.eig
  obtain ⟨⟨hE, hhE⟩, ⟨hW, hhW⟩⟩ := hP.hecke
  have kR := RealDat.kFormR_of (F := F) hC.models
  have kL := RealDat.kFormL_of (F := F) hC.models
  have jR := RealDat.jIsoR_of (F := F) hC.models
  have jL := RealDat.jIsoL_of (F := F) hC.models
  exact links_of_core (s := s) (C0 := C0) (C1 := C1) (hE := hE) (hW := hW) (gE := R.gEx F) (gW := R.gWx F)
    { kFormR := kR
      kFormL := kL
      jIsoR := jR
      jIsoL := jL
      npTie := ⟨rfl, rfl⟩
      ok := hOk
      sep := hsep
      heckeR := hP.heckeR
      heckeL := hP.heckeL
      thetaR := hhE
      thetaL := hhW
      gUnit := hP.gUnit.1
      gEquiv := hP.gEquiv.1
      lev0 := hP.levE.1
      lev1 := hP.levE.2.1
      h2P := hP.levE.2.2
      gUnitL := hP.gUnit.2
      gEquivL := hP.gEquiv.2
      lower_level_lift_type := hP.levW.1
      upper_level_lift_type := hP.levW.2
      inBlock := hP.block
      ratZ := hP.ratZ
      eig0 := e0
      eig1 := e1
      typ0 := t0
      typ1 := t1
      pos := hP.pos
      h0 := RealDat.h0 hC.tup
      w1 := fun w hw => hC.tup.tw w ((RealDat.inNonzeroPlaces_recursive_iff C CH w).2 hw)
      h4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
      thmBop := RealDat.thmBop_of hP.thmB
      partsE := hP.sumE
      ratMu := hP.ratMu
      kForm := RealDat.kForm hP.unif
      mLat := hP.mLat
      ewNorm := RealDat.ewNorm
      thmAop := RealDat.thmAop_of hP.thmA
      partsW := hP.sumW
      ratTh := hP.ratTh
      galD := hP.scalConj
      dimParts := hP.dimParts
      l3 := hP.covol
      on := hP.onto
      l6 := hP.lamLow
      btVanish := hP.btVanish
      mi0 := hP.mi0
      zetaOK := RealDat.zetaOK_of Y hY
      l1e := hP.period
      fun0 := hP.fun0 } hP.passage

def primPkg {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (R : RealDat D A Ks) (F : Face D A) (Y : RealDat.RealCol R F)
    (C CH : ℝ) (hC : R.Char F) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    IndefPkg A.fam.amb (faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) C CH :=
  cxPkgF A hOk hsep F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx F) Y.toCol C CH (cxLinks_of_prims hOk hsep hC hY hP)


end Prim

section Geo

open Formalism.L2.Geo Formalism.MainNotions

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Gm : DV.Geo D.what₂.LL} {Lv : Type} {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL]

def posEmb (σ : D.what₂.LL →+* ℂ) : Prop := ∀ ρ, labE σ (lab σ ρ) = tauE D ρ

def GeoTied (R : RealDat D A Kp.fs.KO) (e : G ≃* Kp.Hb) : Prop :=
  Arith.FormsL.PosOK posEmb D.what₂.embLL ∧ ∀ i : Fin D.R.m, ∃ (w : WeightFamilies.Wt D ((i : ℕ) + 1)) (ι : Kp.fs.Cusp ((i : ℕ) + 1) w →ₗ[Kp.fs.KO] (Fin (R.nW i) → D.what₂.LL)),
    Arith.CompatibleAtCompactLevel Kp e posEmb (R.νW i (R.fdW i)).toReal ((i : ℕ) + 1) w (R.FW i) ι

def CharG (R : RealDat D A Kp.fs.KO) (F : Face D A) (e : G ≃* Kp.Hb) : Prop := R.Char F ∧ GeoTied Kp R e

end Geo

section Exist

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable (D) in

def WeilExists : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsStdChar D ψ (-1) → IsHeckeChar D χS →
    IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ ω, IsWeilDatumO ψ S T χS χT ω

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

def Base : Prop := R.toLevCh.Is A.μ0 ∧ R.IsGrp F ∧ R.IsFam ∧ R.IsModels

end RealDat

variable (D A Ks) in

def BaseExists (F : Face D A) : Prop := ∃ R : RealDat D A Ks, R.Base F

end Exist

section Host

variable (D) in

structure HostHyp : Prop where
  interlace : (Ptw D).Interlace
  gap : ∀ (τ : D.what₂.Tau) (j : Fin D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).e j - (D.hc τ).b j ∧
    ∀ h : (j : ℕ) + 1 < D.R.m, ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨(j : ℕ) + 1, h⟩ - (D.hc τ).e j
  gapR : ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)
  cloudGap : ∀ τ : D.what₂.Tau, 100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 2) - Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k - 1)
  nodeGap : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)
  nodeGapR : D.NodeGap (256 * (D.R.r : ℝ) ^ 4)

open Formalism.L2.Geo Formalism.MainNotions Formalism.IndefR.Cx in

def geoPkg {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Gm : DV.Geo D.what₂.LL} {Lv : Type}
    {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL] {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (R : RealDat D A Kp.fs.KO) (F : Face D A) (e : G ≃* Kp.Hb) (Y : RealDat.RealCol R F) (C CH : ℝ) (_hH : HostHyp D)
    (hG : CharG Kp R F e) (hY : Y.Char) (hP : PrimLinks R F Y C CH) :
    IndefPkg A.fam.amb (faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) C CH :=
  primPkg hOk hsep R F Y C CH hG.1 hY hP

end Host

end Formalism.IndefR.Links

end
end
