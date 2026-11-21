import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

section
noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FreeSingleHomotopyEquivDiscreteChains

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MidData (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc) : Prop :=
  (R.toCx3 F).MIUnit d ∧ (R.toCx3 F).MIid (F.eV (R.toCx3 F).zs) sEE d

open scoped InnerProductSpace in

def PairZeroAt (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc)
    (u : (F.fc (R.toCx3 F).zs).Dc.Mem) : Prop :=
  ∀ t (φ : Fin ((F.fc (R.toCx3 F).zs).Dc.a u) → D.what₂.LL) (v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL),
    ⟪sEE (d.V ((R.toCx3 F).Θ t ((R.toCx3 F).jR t (F.eV (R.toCx3 F).zs t v)))),
      (F.fc (R.toCx3 F).zs).Sp.Pu u ((d.U u).mulVec (cpt A3.fam3.F.v0.embedding φ))⟫_ℂ = 0

end FreeSingleHomotopyEquivDiscreteChains

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def OpsUnit (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  (∀ e ∈ X.EEl true, V e ∈ X.EEl true ∧ ‖V e‖ = ‖e‖) ∧
    ∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x

def CxTies (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) : Prop :=
  (fc X.zs).Df1.WF ∧ X.H2 cr true ∧ X.RATmu cr true ∧ X.JIsoR cv ∧ X.RatLev cr cv true ∧ X.DnLev cv true ∧
    X.UpLev cv true ∧ X.CoordinatesInGoodPart cr cv true ∧ X.EVTie cr cv eV

variable {X cr cv}

end Gen

end GlobalTheory.MiS

end
end

section
noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}

def DcPtG {ex : Extra D L hT Gi Gl Kc Yd cX} (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

structure RealPack (ex : Extra D L hT Gi Gl Kc Yd cX) where

  R : Formalism.L2.RecT ex

  S : Formalism.L2.SG.SpectralTiesReal.STiesR R

  P : RowSideFamily ex

  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)

  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)

  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3

  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]

  Q : RealT R P Dcf Spf Zscf S Ks

attribute [instance] RealPack.fKs RealPack.nKs RealPack.aKs

variable {ex : Extra D L hT Gi Gl Kc Yd cX}

def HypAt (W : RealPack ex) : Prop :=
  Nonempty (Formalism.L2.SG.JoinSI.JoinSI W.R W.S W.Q) ∧
    (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) ∧ DcPtG W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl

abbrev cxW (W : RealPack ex) := W.Q.Rl.toCx3 W.Q.F

def LevHyp (W : RealPack ex) : Prop :=
  (∃ s, W.P.A3.fam3.Ok3 s) ∧ (cxW W).RatZ ∧
    ∃ gE : Representation ℂ W.P.Gp (cxW W).EE, GUnit3 (cxW W) gE ∧ GEquiv3 W.P.A3 (cxW W) gE ∧
      PrincipalLevelBijectivity W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) ∧
      LevType3 W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE false W.P.P0 W.P.ψ0 ∧
      LevType3 W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE true W.P.Ps W.P.ψs

def TiesRest (W : RealPack ex) : Prop :=
  (W.Q.F.fc (cxW W).zs).Df1.WF ∧ (cxW W).H2 W.Q.F.cr true ∧ (cxW W).RATmu W.Q.F.cr true ∧ (cxW W).CoordinatesInGoodPart W.Q.F.cr W.Q.F.cv true


end GlobalTheory.MiS

end
end
