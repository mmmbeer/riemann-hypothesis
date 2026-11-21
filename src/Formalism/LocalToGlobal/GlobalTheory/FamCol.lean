import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.GlobalTheory.FamRec
import Formalism.SizeWindowBrackets.TranslateWordBoundHypotheses
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamCol

open Formalism Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.DIV

structure PlDat (K : Type) (I : Type) where
  N : NumDatum
  Cs : Arith.Cst
  Lv : Arith.Lev N
  sd : K
  code : I → Code N

structure RowArg {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I) where
  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]
  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]
  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ
  cc : Submodule (𝓞 K) Wd
  B : ∀ u, (C.M u).V →ₗ[K] Wd
  v : InfinitePlace K
  Y : ∀ u, Matrix (C.M u).ι (C.M u).ι ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ u, Matrix (κ ⊕ κ₁) (C.M u).ι ℂ
  γ : I → ℝ
  Bf : ∀ u, Matrix (κ ⊕ κ₁) (C.Mf u).ι ℂ
  h : I → ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] RowArg.indexWFirst RowArg.indexWSecond RowArg.indexWThird RowArg.indexWFourth RowArg.firstRealIndex RowArg.secondRealIndex RowArg.firstRationalIndex RowArg.secondRationalIndex

section Fam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

def famC [IsTotallyComplex K] (m : ℕ) (C : ColObj K I) (P : PlDat K I) (R : RowArg C) : LChain2.Fam I m where
  K := K
  Wd := R.Wd
  κ := R.κ
  κ₁ := R.κ₁
  V := fun u => (C.M u).V
  ι := fun u => (C.M u).ι
  Vf := fun u => (C.Mf u).V
  ιf := fun u => (C.Mf u).ι
  b' := R.b'
  X' := R.X'
  cc := R.cc
  b := fun u => (C.M u).b
  X := fun u => (C.M u).X
  M := fun u => (C.M u).L
  N0 := C.Nu
  bf := fun u => (C.Mf u).b
  Xf := fun u => (C.Mf u).X
  Mf := fun u => (C.Mf u).L
  σ := C.sgExp
  τ := C.tauExp
  B := R.B
  v := R.v
  Y := R.Y
  Y' := R.Y'
  Ball := R.Ball
  γ := R.γ
  Bf := R.Bf
  Vr := fun u => C.Vr u R.v
  S := C.S
  gain := fun j w => Arith.gainD P.N P.Cs P.Lv (Arith.pOf (Arith.hs w)) (j.1 + 1)
  Fj := fun j w => P.N.FjP (j.1 + 1) (Arith.pOf (Arith.hs w))
  Ej := fun u j w => Arith.E P.N P.Cs P.Lv P.sd (P.code u) (j.1 + 1) (Arith.hs w)
  iop := Arith.io P.N P.Cs
  T := C.T
  h := R.h
  lam := C.lamT
  Dstar := C.Dstar
  η0 := R.η0
  η1 := R.η1
  e0 := R.e0


def ColFacts (C : ColObj K I) : Prop := ∃ J : ColIface K I, J.toColObj = C

structure PlaceDataCompatible (C : ColObj K I) (P : PlDat K I) : Prop where
  f : C.f = P.N.R.f
  k : C.k = P.N.R.k
  m : C.m = P.N.R.m
  sd : Arith.SdOk P.N P.sd
  code : ∀ u, P.code u ∈ P.Lv.Ws
  T : ∀ u, C.T u = P.Lv.T (P.code u)
  overPi : ∀ u w, prW w = C.T u → (C.overPi u w ↔ 0 < vAdd w (Arith.elt P.sd (P.Lv.piT (P.code u))))
  supp : C.supp = Arith.supp P.N P.Lv K
  tau : C.tau = fun w => Arith.tau P.N P.Cs (Arith.pOf w)
  sg : ∀ u, C.sg u = Arith.sg P.N P.Cs P.Lv P.sd (P.code u)

structure Service (C : ColObj K I) (P : PlDat K I) : Prop where
  len : ∀ u, ∀ w ∈ C.supp, prW w ≠ C.T u →
    ((C.lenMN u w : ℚ) : ℝ) ≤ (C.dM u : ℝ) * (Arith.tau P.N P.Cs (Arith.pOf w) + Arith.io P.N P.Cs (Arith.pOf w))

structure DatWin (P : PlDat K I) : Prop where
  d_le : (P.N.d : ℝ) ≤ P.N.sc.X'' P.N.R.n
  dgam : ∀ p : ℕ, p.Prime → p ∣ P.Lv.DGam → (p : ℝ) ≤ P.N.sc.X'' P.N.R.n

structure PlSizes (C : ColObj K I) (P : PlDat K I) (bb : ℝ) : Prop where
  Ta : ∑ w ∈ C.supp, Arith.sz w (Arith.tau P.N P.Cs (Arith.pOf w)) ≤ bb ^ 2
  level : ∀ u, 4 * (C.f : ℝ) / (C.T u : ℝ) * bb ^ 2
    + (C.f : ℝ) * Real.log ((C.T u : ℝ) - 1) / ((C.T u : ℝ) - 2) ≤ 1

structure RowHyp [Fintype I] (C : ColObj K I) (R : RowArg C) (sg : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  what₂ : 0 < Fintype.card R.κ
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  sg_pos : 0 < sg
  sg_le : sg ≤ 1 / 20
  proviso : C.Dstar / sg ≤ ∑ u, (Fintype.card (C.Mf u).ι : ℝ)
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ sg / 2
  η1_le : R.η1 ≤ sg / 2
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ sg / 2
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0

end Fam

structure Pt (I : Type) where
  K : Type
  [i1 : Field K]
  [i2 : NumberField K]
  [i3 : StarRing K]
  [i4 : IsTotallyComplex K]
  C : ColObj K I
  P : PlDat K I
  R : RowArg C

attribute [instance] Pt.i1 Pt.i2 Pt.i3 Pt.i4

def Pt.fam {I : Type} (m : ℕ) (Q : Pt I) : LChain2.Fam I m := famC m Q.C Q.P Q.R

structure Pt.OkIn {I : Type} (Q : Pt I) (m f g₁ g₂ : ℕ) (Xpp : ℝ) : Prop where
  m : Q.P.N.R.m = m
  f : Q.C.f = f
  g0 : Q.P.N.g 0 = g₁
  g1 : Q.P.N.g 1 = g₂
  Xpp : Q.P.N.sc.X'' Q.P.N.R.n = Xpp
  facts : ColFacts Q.C
  tied : PlaceDataCompatible Q.C Q.P
  cst : Q.P.Cs.admitted
  service : Service Q.C Q.P
  win : DatWin Q.P

structure Pt.Ok {I : Type} (Q : Pt I) (m f : ℕ) (bb : ℝ) : Prop where
  m : Q.P.N.R.m = m
  f : Q.C.f = f
  facts : ColFacts Q.C
  tied : PlaceDataCompatible Q.C Q.P
  cst : Q.P.Cs.admitted
  service : Service Q.C Q.P
  sizes : PlSizes Q.C Q.P bb
  above : ∀ δ ∈ Q.P.Lv.Ws, Q.P.N.sc.X'' Q.P.N.R.n < (Q.P.Lv.T δ : ℝ)

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

structure SameNumbers {I : Type} [Fintype I] {m : ℕ} (F F' : Fam I m) : Prop where
  du : ∀ u, F.du u = F'.du u
  dM : ∀ u, F.dM u = F'.dM u
  T : ∀ u, F.T u = F'.T u
  muN : ∀ u, muDef (F.b u) (F.X u) (F.N' u) = muDef (F'.b u) (F'.X u) (F'.N' u)
  muMaxN : ∀ u, muMaxDef (F.b u) (F.X u) (F.N' u) = muMaxDef (F'.b u) (F'.X u) (F'.N' u)
  h : ∀ u, F.h u = F'.h u
  muM : ∀ u, muDef (F.bf u) (F.Xf u) (F.Mf u) = muDef (F'.bf u) (F'.Xf u) (F'.Mf u)
  muMaxM : ∀ u, muMaxDef (F.bf u) (F.Xf u) (F.Mf u) = muMaxDef (F'.bf u) (F'.Xf u) (F'.Mf u)
  EeJ : ∀ u j, F.EeJ u j = F'.EeJ u j
  muCC : muDef F.b' F.X' F.cc = muDef F'.b' F'.X' F'.cc
  muMinCC : muMinDef F.b' F.X' F.cc = muMinDef F'.b' F'.X' F'.cc
  Fo : F.Fo = F'.Fo
  Ga : F.Ga = F'.Ga
  Ta : F.Ta = F'.Ta
  IO : F.IO = F'.IO
  del : F.del = F'.del
  e0 : F.e0 = F'.e0

end Family

section Rec

structure RowJoint {D : D7} {C : ColObj D.what₂.LL D.what₂.Word} (R : RowArg C) : Prop where
  h : ∀ u, R.h u = D.div.h u
  muCC : muDef R.b' R.X' R.cc = D.div.RR.muDual
  muMinCC : muMinDef R.b' R.X' R.cc = D.div.RR.muMinDual
  del : 1 - (Fintype.card R.κ : ℝ) / (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) = D.what₂.delp

structure PlJoint {D : D7} (L : SizeData₂ D) (P : PlDat D.what₂.LL D.what₂.Word) : Prop where
  Ga : L.Ga = Arith.Ga P.N P.Cs P.Lv D.what₂.LL
  Fo : L.Fo = Arith.Fo P.N P.Lv D.what₂.LL
  E : ∀ u, ∀ j ∈ P.N.lifts, ∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w) =
    ∑ w ∈ Arith.supp P.N P.Lv D.what₂.LL, Arith.sz w (Arith.E P.N P.Cs P.Lv P.sd (P.code u) j w)
  Ta : ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) =
    ∑ w ∈ Arith.supp P.N P.Lv D.what₂.LL, Arith.sz w (Arith.tau P.N P.Cs (Arith.pOf w))
  IO : ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.io w = Arith.IOsum P.N P.Cs P.Lv D.what₂.LL

open Formalism.MainNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost in

def CompatibleOfLocal : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ), Fm.x1 < x →
    ∀ (M : Lnk.Mod Fm x) (F : ∀ u0 : M.e.A, LChain2.Fam ((Fm.D x (M.pt u0)).what₂.Word) M.m)
      (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (C : Consts) (cT : ℝ) (N : ℕ) (η θ etaB eB : ℝ),
      C.eDiv ≤ eD → C.eLoss ≤ eL → C.cHH ≤ cHH →
      TieArith Fm x M.pt M.av M.AD ell M.TT M.T2 M.a M.w →
      (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re → η = (Fm.L x M.i0).etaSz →
      (∀ u0, FamRec.LocalTie (Fm.L x (M.pt u0)) M.m (F u0)) →
      LChain2.Inputs2 M.AD ell (FamRec.globM M etaB eB) C cT N M.TT M.T2 M.a M.w F η θ eK K CL →
      ChainTied Fm eD eL K cHH eK CL x

open Formalism.MainNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost in

def ColumnsToCompatible : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ), Fm.x1 < x →
    ∀ (M : Lnk.Mod Fm x)
      (C : ∀ u0 : M.e.A, ColObj (Fm.D x (M.pt u0)).what₂.LL (Fm.D x (M.pt u0)).what₂.Word)
      (P : ∀ u0 : M.e.A, PlDat (Fm.D x (M.pt u0)).what₂.LL (Fm.D x (M.pt u0)).what₂.Word)
      (R : ∀ u0 : M.e.A, RowArg (C u0))
      (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (Cn : Consts) (cT : ℝ) (N : ℕ) (η θ etaB eB : ℝ),
      Cn.eDiv ≤ eD → Cn.eLoss ≤ eL → Cn.cHH ≤ cHH →
      TieArith Fm x M.pt M.av M.AD ell M.TT M.T2 M.a M.w →
      (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re → η = (Fm.L x M.i0).etaSz →
      (∀ u0, (C u0).RecJoint (Fm.D x (M.pt u0))) → (∀ u0, (P u0).N.R.m = M.m) → (∀ u0, PlaceDataCompatible (C u0) (P u0)) →
      (∀ u0, (Fm.D x (M.pt u0)).NuFull) → (∀ u0, RowJoint (R u0)) → (∀ u0, PlJoint (Fm.L x (M.pt u0)) (P u0)) →
      LChain2.Inputs2 M.AD ell (FamRec.globM M etaB eB) Cn cT N M.TT M.T2 M.a M.w
        (fun u0 => famC M.m (C u0) (P u0) (R u0)) η θ eK K CL →
      ChainTied Fm eD eL K cHH eK CL x

end Rec

section Conc

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

def argPl (A : ColArg W Ch) (P : PlDat X.K Pr.Word) : ColArg W Ch :=
  ColArg.ofTau W Ch A.num (Arith.supp P.N P.Lv X.K) (fun u => Arith.sg P.N P.Cs P.Lv P.sd (P.code u))
    (Arith.tau P.N P.Cs) A.yM A.sel A.Sq

def ptC (hX : X.Ok) (A : ColArg W Ch) (P : PlDat X.K Pr.Word) (Rw : RowArg (colObj W Ch hX (argPl A P))) : Pt Pr.Word :=
  { K := X.K, i4 := hX.cplxK, C := colObj W Ch hX (argPl A P), P := P, R := Rw }

end Conc

section Dat

structure DataCompatible {X : Fields} {Pr : Primes X} (P : PlDat X.K Pr.Word) (W : Wts X Pr.Word P.N.R) (num : ScNum) where
  ρ : X.Tau ≃ RPl P.N.R
  sd : Arith.SdOk P.N P.sd
  code : ∀ u, P.code u ∈ P.Lv.Ws
  T : ∀ u, Pr.T u = P.Lv.T (P.code u)
  g : ∀ i, Pr.g i = P.N.g i
  cond : Pr.cond = P.N.cond
  piT : ∀ u τ, ((X.embO τ (Pr.piT u) : 𝓞 X.K) : X.K) = Arith.elt P.sd (P.Lv.piT (P.code u))
  piG : ∀ i τ, ((X.embO τ (Pr.piG i) : 𝓞 X.K) : X.K) = Arith.elt P.sd (P.Lv.piG i)
  tops : ∀ τ, τ ∈ W.tops ↔ ((ρ τ).1 = false ∧ (ρ τ).2 ∈ P.N.TT)
  hc_u : ∀ u τ i, (W.hc u τ).u i = P.N.uW (P.code u) (ρ τ) i
  hc_v : ∀ u τ, (W.hc u τ).v = (P.N.hc (ρ τ)).v
  hc_b : ∀ u τ, (W.hc u τ).b = (P.N.hc (ρ τ)).b
  hc_e : ∀ u τ, (W.hc u τ).e = (P.N.hc (ρ τ)).e
  sc : num.sc = P.N.sc
  Sc : num.Sc = P.N.Sc
  eta : num.eta = P.N.eta
  v : vC X = P.N.v

end Dat

section ConcNum

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

structure GlobTied {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (num : ScNum) (G : Glob) (TT : Finset H)
    (a : H → ℝ) (w : Fin R.m → E0 × H → ℝ) where
  σ : X.Tau ≃ ↥(PhiSet (H := H))
  x : num.sc.x = G.x
  ε : num.sc.eps = G.ε
  k : (R.k : ℝ) = G.k
  v : vC X = G.v
  lg : ∑ i, Real.log (Pr.g i : ℝ) = G.lg
  tops : W.tops = TT.map ((LChain6.topPhi H).trans σ.symm.toEmbedding)
  aTop : ∀ u, ∀ t ∈ TT, (W.aTop u (σ.symm (LChain6.topPhi H t)) : ℝ) = a t
  row : ∀ j τ, (((W.row τ).e j : ℚ) : ℝ) = w j (σ τ).1

end ConcNum

end Formalism.L2.GlobalTheoryTheory.FamCol

end
