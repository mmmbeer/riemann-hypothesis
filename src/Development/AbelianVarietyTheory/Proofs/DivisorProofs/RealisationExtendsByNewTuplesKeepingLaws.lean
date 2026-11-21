import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasY
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelsWith
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideRealMoreLevel

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type}

structure NewLev (D : D7) (N : Type) where
  xiH : N → Formalism.L2.Host.HChar D.host.E
  xi : N → (AE D)ˣ →* Circle
  Q : N → Finset (Pl D.host.E)
  xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ

def extL (L : LevCh D T) (V : NewLev D N) : LevCh D (T ⊕ N) :=
  { L with
    xiH := Sum.elim L.xiH V.xiH
    xi := Sum.elim L.xi V.xi
    Q := Sum.elim L.Q V.Q
    xiR := Sum.elim L.xiR V.xiR }

structure NewFam {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (N : Type) where
  ok : N → Set Pl0
  muVal : Fin m → N → Pl0 → Kˣ
  SR : N → CSD K
  actR : ∀ n, Representation K G (SR n).Forms
  opR : ∀ n, ok n × ℕ → Module.End K (SR n).Forms
  SL : Fin m → N → CSD K
  actL : ∀ j n, Representation K G (SL j n).Forms
  opL : ∀ j n, ok n × ℕ → Module.End K (SL j n).Forms

def extA {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (X : NewFam A N) :
    FamIn K G Pl0 (T ⊕ N) m where
  v0 := A.v0
  μ0 := .inl A.μ0
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j := Sum.elim (A.muVal j) (X.muVal j)
  etaVal := A.etaVal
  ok := Sum.elim A.ok X.ok
  MtildeCSD := Sum.elim A.MtildeCSD X.SR
  leftGroupActionRight τ := Sum.rec A.leftGroupActionRight X.actR τ
  heckeR τ := Sum.rec A.heckeR X.opR τ
  MtCSD j := Sum.elim (A.MtCSD j) (X.SL j)
  leftGroupActionLift j τ := Sum.rec (A.leftGroupActionLift j) (X.actL j) τ
  heckeL j τ := Sum.rec (A.heckeL j) (X.opL j) τ


variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure NewReal (R : RealDat D A Ks) (V : NewLev D N) (X : NewFam A N) where
  BR : ∀ n, Bridge.SideReal D D.sp.X'
    (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n)) R.pl (X.ok n)))
    (X.SR n) (X.actR n) (X.opR n) (fun i => i.2)
  BL : ∀ i n, Bridge.SideReal D (Vc D i)
    (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) R.pl (X.ok n)))
    (X.SL i n) (X.actL i n) (X.opL i n) (fun i => i.2)
  HX : N → HMod (Bridge.Gf D.sp.X' → R.cX.W)
  HV : ∀ i, N → HMod (Bridge.Gf (Vc D i) → (R.cV i).W)
  jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H
  jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H
  νY : N → ∀ j, Measure (GA D (Yc D j))
  fdY : N → ∀ j, Set (GA D (Yc D j))
  νX : N → Measure (GA D D.sp.X')
  fdX : N → Set (GA D D.sp.X')
  νV : ∀ i, N → Measure (GA D (Vc D i))
  fdV : ∀ i, N → Set (GA D (Vc D i))
  ωY : N → ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)
  ωX : N → GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)
  ωP : ∀ i, N → GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)
  vY : N → ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : N → WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ
  vP : ∀ i, N → WO (Vc D i) (Wc D i) → ℂ
  ioY : ∀ n k, MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) ((extL R.toLevCh V).datYt (.inr n) (k + 1) R.triv))
      (Lev.levChi _ (R.βY (k + 1)) ((extL R.toLevCh V).datYt (.inr n) (k + 1) R.triv)) →ₗ[ℂ]
    MultT R.θ (R.MY k) (levS _ (R.βY k) ((extL R.toLevCh V).datYt (.inr n) k R.triv))
      (Lev.levChi _ (R.βY k) ((extL R.toLevCh V).datYt (.inr n) k R.triv))
  ioX : ∀ n, LinearMap.range (R.cX.toMap R.prX ∘ₗ (HX n).e) →ₗ[ℂ]
    MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) ((extL R.toLevCh V).datYt (.inr n) (D.R.m - 1) R.triv))
      (Lev.levChi _ (R.βY (D.R.m - 1)) ((extL R.toLevCh V).datYt (.inr n) (D.R.m - 1) R.triv))
  Th : ∀ n, (HX n).H →ₗ[ℂ] R.HE.H
  thF : ∀ i n, (HV i n).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))
  thG : ∀ i n, (HV i n).H →ₗ[ℂ] (R.HW i (sg0 D A)).H

set_option maxHeartbeats 4000000 in

def extR (R : RealDat D A Ks) {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X) : RealDat D (extA A X) Ks where
  toLevCh := extL R.toLevCh V
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := { R := fun τ => Sum.rec R.B.R Y.BR τ, L := fun i τ => Sum.rec (R.B.L i) (Y.BL i) τ, rankR := R.B.rankR,
         rankL := R.B.rankL }
  prX := R.prX
  HX := Sum.elim R.HX Y.HX
  HV i := Sum.elim (R.HV i) (Y.HV i)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX τ := Sum.rec R.jX Y.jX τ
  jV i τ := Sum.rec (R.jV i) (Y.jV i) τ
  νY := Sum.elim R.νY Y.νY
  fdY := Sum.elim R.fdY Y.fdY
  ν0 := R.ν0
  fd0 := R.fd0
  νX := Sum.elim R.νX Y.νX
  fdX := Sum.elim R.fdX Y.fdX
  νV i := Sum.elim (R.νV i) (Y.νV i)
  fdV i := Sum.elim (R.fdV i) (Y.fdV i)
  νW := R.νW
  fdW := R.fdW
  ωY := Sum.elim R.ωY Y.ωY
  ωX := Sum.elim R.ωX Y.ωX
  ωP i := Sum.elim (R.ωP i) (Y.ωP i)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY := Sum.elim R.vY Y.vY
  vX := Sum.elim R.vX Y.vX
  vP i := Sum.elim (R.vP i) (Y.vP i)
  ItY := R.ItY
  ItX := R.ItX
  ioY τ := Sum.rec R.ioY Y.ioY τ
  ioX τ := Sum.rec R.ioX Y.ioX τ
  Th τ := Sum.rec R.Th Y.Th τ
  BV := R.BV
  ioP := R.ioP
  thF i τ := Sum.rec (R.thF i) (Y.thF i) τ
  thG i τ := Sum.rec (R.thG i) (Y.thG i) τ
  nW := R.nW
  FW := R.FW
  mu w := .inl (R.mu w)
  twPl := R.twPl
  kap := R.kap
  lam _ _ _ _ := 0
  err0 := R.err0

set_option maxHeartbeats 4000000 in
theorem extR_comap (R : RealDat D A Ks) {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X) :
    (extR R Y).comap Sum.inl A.μ0 R.mu R.twPl R.FW R.kap R.lam R.err0 = R := rfl

section Ties

variable {T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def extF (F : Face D A) (X : NewFam A N) : Face D (extA A X) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def TieExt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {V : NewLev D N}
    {X : NewFam A N} (Y : NewReal R V X) : Prop :=
  ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    Bridge.FamTie (extR R Y).B R.pl (R.Sb : Set (Pl D.host.E)) (extR R Y).Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

theorem ioExt_ext {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {V : NewLev D N}
    {X : NewFam A N} (Y : NewReal R V X) (h : IoExt R) : IoExt (extR R Y) := h

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {V : NewLev D N} {X : NewFam A N}
  (Y : NewReal R V X) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 2000000 in

def fwExt (t : FWTie T R κ v₀) : FWTie T (extR R Y) κ v₀ where
  alg_eq := t.alg_eq
  e := t.e
  ks := t.ks
  kap := t.kap
  pt := t.pt
  nrm_eq := t.nrm_eq
  laws := t.laws
  chiR := t.chiR
  hv₀ := t.hv₀
  x0 := t.x0
  ev0 := t.ev0
  ev := t.ev

set_option maxHeartbeats 2000000 in

def omExt {i : Fin D.R.m} (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    OMDat T.toCore (extR R Y) i Unit (fun _ => (extA A X).μ0) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := O.dδ
  Cl' := O.Cl'
  fCl := O.fCl
  bad := O.bad
  Lh := O.Lh
  La := O.La
  Nc := O.Nc
  gam := O.gam
  vol := O.vol
  ep := O.ep
  B := O.B
  epF := O.epF
  io := O.io
  hw := O.hw
  φ := O.φ
  w := O.w
  U₂ := O.U₂
  dict₂ := O.dict₂
  xi := O.xi
  thAd := O.thAd
  Plc := O.Plc

variable {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 4000000 in
theorem omPins_ext (hT : TieExt R Y) {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) :
    OMPins T (extR R Y) κ v₀ (fun i => omExt Y (O i)) i := by
  have hP := h.2
  have h1 := hP.lift
  have h2 := hP.tuple
  refine ⟨h.1, ⟨h1.field, h1.std, h1.v0, ?_, h1.lev⟩,
    fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩
  obtain ⟨g, c, c', h3, h4⟩ := h1.c0
  exact ⟨g, c, c', hT _ _ _ h3, h4⟩

set_option maxHeartbeats 4000000 in
theorem oneMapOf_ext {i : Fin D.R.m} (cc ph) :
    (omExt Y (O i)).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph ↔ (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem phaseTie_ext {ph : Fin D.R.m → ℂ} {i : Fin D.R.m} (h : PhaseTie T R κ v₀ O ph i) :
    PhaseTie T (extR R Y) κ v₀ (fun i => omExt Y (O i)) ph i :=
  fun ⟨cc, p, h'⟩ => (oneMapOf_ext Y _ _).2 (h ⟨cc, p, (oneMapOf_ext Y _ _).1 h'⟩)

set_option maxHeartbeats 4000000 in
theorem fixBase_ext (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) : GlobalTheory.ConjTwist.FixBase T (extR R Y) i τ ↔ GlobalTheory.ConjTwist.FixBase T R i τ :=
  ⟨fun h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩, fun h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩⟩

end Ties

end GlobalTheory.TupExt

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ModC (R : RealDat D A Ks) : Prop :=
  R.models_HX ∧ R.models_HV ∧ R.models_jX ∧ R.models_jV ∧ R.models_νY ∧ R.models_νY' ∧ R.models_νX ∧ R.models_νV

def KerC (R : RealDat D A Ks) : Prop :=
  R.chain_ωY ∧ R.chain_ωX ∧ R.chain_vY ∧ R.chain_vX ∧ R.thP_ωP ∧ R.thP_vP

variable {R : RealDat D A Ks} {V : NewLev D N} {X : NewFam A N}

def FamC (Y : NewReal R V X) : Prop :=
  (extR R Y).grp_red_R ∧ (extR R Y).grp_red_L ∧ TieExt R Y ∧ (extR R Y).fam_roots ∧ RealDat.fam_degR (A := extA A X) ∧
    RealDat.fam_degL (A := extA A X) ∧ (extR R Y).fam_muVal

set_option maxHeartbeats 2000000 in

def updM (Y : NewReal R V X) (HX : type_of% Y.HX) (HV : type_of% Y.HV)
    (jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H)
    (jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H)
    (νY : type_of% Y.νY) (fdY : type_of% Y.fdY) (νX : type_of% Y.νX) (fdX : type_of% Y.fdX) (νV : type_of% Y.νV)
    (fdV : type_of% Y.fdV) : NewReal R V X :=
  { Y with
    HX := HX, HV := HV, jX := jX, jV := jV, νY := νY, fdY := fdY, νX := νX, fdX := fdX, νV := νV, fdV := fdV,
    ioX := fun _ => 0, Th := fun _ => 0, thF := fun _ _ => 0, thG := fun _ _ => 0 }

set_option maxHeartbeats 2000000 in

def updK (Y : NewReal R V X) (ωY : type_of% Y.ωY) (ωX : type_of% Y.ωX) (ωP : type_of% Y.ωP) (vY : type_of% Y.vY)
    (vX : type_of% Y.vX) (vP : type_of% Y.vP) : NewReal R V X :=
  { Y with ωY := ωY, ωX := ωX, ωP := ωP, vY := vY, vX := vX, vP := vP }

set_option maxHeartbeats 2000000 in

def updL (Y : NewReal R V X) (ioY : type_of% (extR R Y).ioY) (ioX : type_of% (extR R Y).ioX) (Th : type_of% (extR R Y).Th)
    (thF : type_of% (extR R Y).thF) (thG : type_of% (extR R Y).thG) : NewReal R V X :=
  { Y with
    ioY := fun n => ioY (.inr n), ioX := fun n => ioX (.inr n), Th := fun n => Th (.inr n),
    thF := fun i n => thF i (.inr n), thG := fun i n => thG i (.inr n) }

set_option maxHeartbeats 2000000 in
theorem isModels_ext (hM : R.IsModels) (Y : NewReal R V X) (h : ModC (extR R Y)) : (extR R Y).IsModels := by
  refine ⟨?_, hM.vpos, ?_, ?_, ?_, h.1, h.2.1, ?_, ?_, ?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hM.inf :))
  · exact (by with_unfolding_all exact (hM.cX :))
  · exact (by with_unfolding_all exact (hM.cV :))
  · exact (by with_unfolding_all exact (hM.prX :))
  · exact (by with_unfolding_all exact (hM.HE :))
  · exact (by with_unfolding_all exact (hM.HW :))
  · exact (by with_unfolding_all exact (hM.gE :))
  · exact (by with_unfolding_all exact (hM.gW :))
  · exact (by with_unfolding_all exact (hM.ν0 :))
  · exact (by with_unfolding_all exact (hM.νW :))
  · exact (by with_unfolding_all exact (hM.BV :))
  · exact (by with_unfolding_all exact (hM.order :))

set_option maxHeartbeats 2000000 in
theorem isFam_ext (hF : R.IsFam) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsFam := by
  refine ⟨?_, ?_, h.2.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  · obt ⟨g, c, c', ht⟩ := hF.tie
    have h1 := h.2.2.1 g c c' ht
    refine ⟨g, ?_, ?_, ?_⟩
    · exact (by with_unfolding_all exact (c :))
    · exact (by with_unfolding_all exact (c' :))
    · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (hF.Sb :))
  · exact (by with_unfolding_all exact (hF.pl_onto :))
  · exact (by with_unfolding_all exact (hF.etaVal :))

set_option maxHeartbeats 2000000 in
theorem isGrp_ext {F : Face D A} (hG : R.IsGrp F) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsGrp (extF F X) := by
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hG.levels :))
  · exact (by with_unfolding_all exact (hG.record :))
  · exact (by with_unfolding_all exact (hG.chiW :))

set_option maxHeartbeats 2000000 in

theorem models_stage (hM : R.IsModels) (Y : NewReal R V X) (h : FamC Y) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') := by
  choose HX jX h1 h2 using fun n => exists_modX (extR R Y) (.inr n)
  choose HV jV h3 h4 using fun i n => exists_modV (extR R Y) i (.inr n)
  choose νY fdY h5 h6 using fun n j => exists_measY (extR R Y) (.inr n) j
  choose νX fdX h7 using fun n => exists_measX (extR R Y) (.inr n)
  choose νV fdV h8 using fun i n => exists_measV (extR R Y) hM.vpos i (.inr n)
  refine ⟨updM Y HX HV jX jV νY fdY νX fdX νV fdV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB h
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.HX t :))
    · exact (by with_unfolding_all exact (h1 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.HV i t :))
    · exact (by with_unfolding_all exact (h3 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.jX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.jV i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY t :))
    · exact (by with_unfolding_all exact (h5 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY' t :))
    · exact (by with_unfolding_all exact (h6 n _ rfl :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νX t :))
    · exact (by with_unfolding_all exact (h7 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.νV i t :))
    · exact (by with_unfolding_all exact (h8 i n :))

set_option maxHeartbeats 2000000 in

theorem ker_stage (hc : R.IsChain) (hp : R.IsThP) (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y)
    (hm : ModC (extR R Y)) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') ∧ KerC (extR R Y') := by
  have hψ : IsStdChar D (extR R Y).ψ (-1) := (hc.ωX A.μ0).std
  choose ωY vY h1 using fun n k => exists_kerY (R := extR R Y) hL hψ (.inr n) k ((by with_unfolding_all exact (fun hk => (hc.vY A.μ0 k hk).1 :)))
  choose ωX vX h2 h3 using fun n => exists_kerX (R := extR R Y) hL hψ (.inr n) ((by with_unfolding_all exact ((hc.vX A.μ0).1 :)))
  choose ωP vP h4 h5 using fun i n => exists_kerP (R := extR R Y) hL hψ i (.inr n) ((by with_unfolding_all exact ((hp.vP i A.μ0).1 :)))
  refine ⟨updK Y ωY ωX ωP vY vX vP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · exact (by with_unfolding_all exact (hm :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).1 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).2 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vX t :))
    · exact (by with_unfolding_all exact (h3 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.ωP i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.vP i t :))
    · exact (by with_unfolding_all exact (h5 i n :))

set_option maxHeartbeats 2000000 in
theorem isChain_updL (hc : R.IsChain) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with ioY := ioY, ioX := ioX, Th := Th } : RealDat D (extA A X) Ks).IsChain) :
    (extR R (updL Y ioY ioX Th thF thG)).IsChain := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB h.ωY
  · exact (by with_unfolding_all exact (h.ωX :))
  · exact (by with_unfolding_all exact (h.vY :))
  · exact (by with_unfolding_all exact (h.vX :))
  · exact (by with_unfolding_all exact (h.ptY :))
  · exact (by with_unfolding_all exact (h.ptX :))
  · exact (by with_unfolding_all exact (h.ItY :))
  · exact (by with_unfolding_all exact (h.ItX :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioY t :))
    · exact (by with_unfolding_all exact (h.ioY (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioX t :))
    · exact (by with_unfolding_all exact (h.ioX (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.Th t :))
    · exact (by with_unfolding_all exact (h.Th (.inr n) :))

set_option maxHeartbeats 2000000 in
theorem isThP_updL (hp : R.IsThP) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with thF := thF, thG := thG } : RealDat D (extA A X) Ks).IsThP) :
    (extR R (updL Y ioY ioX Th thF thG)).IsThP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.ωP :))
  · exact (by with_unfolding_all exact (h.vP :))
  · exact (by with_unfolding_all exact (h.pt_theta :))
  · exact (by with_unfolding_all exact (h.ioP :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF_mem i t :))
    · exact (by with_unfolding_all exact (h.thF_mem i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF i t :))
    · exact (by with_unfolding_all exact (h.thF i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thG i t :))
    · exact (by with_unfolding_all exact (h.thG i (.inr n) :))

set_option maxHeartbeats 2000000 in

theorem core_ext (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y) :
    ∃ Y' : NewReal R V X, GlobalTheory.Hk3.Core (extR R Y') (extF F X) ∧ TieExt R Y' := by
  obt ⟨Y1, f1, m1⟩ := models_stage hC.models Y h
  obt ⟨Y2, f2, m2, k2⟩ := ker_stage hC.chain hC.thP hL Y1 f1 m1
  have hF := isFam_ext hC.fam Y2 f2
  have hM := isModels_ext hC.models Y2 m2
  have e1 := GlobalTheory.ConjExt.exists_chain (R := extR R Y2) h₁ h₂ h₃ h₄ hP hL (isGrp_ext hC.grp Y2 f2).record hF hM k2.1 k2.2.1 k2.2.2.1
    k2.2.2.2.1 (.inl A.μ0) ((by with_unfolding_all exact (hC.chain.ItY A.μ0 :))) ((by with_unfolding_all exact (hC.chain.ItX A.μ0 :)))
  have e2 := GlobalTheory.ConjExt.exists_thP (R := extR R Y2) h₃ hL hF hM k2.2.2.2.2.1 k2.2.2.2.2.2 (.inl A.μ0)
    ((by with_unfolding_all exact (fun i => hC.thP.ioP i A.μ0 :)))
  obt ⟨ioY, ioX, Th, c3⟩ := e1
  obt ⟨thF, thG, p3⟩ := e2
  have f3 : FamC (updL Y2 ioY ioX Th thF thG) := (by with_unfolding_all exact (f2 :))
  have m3 : ModC (extR R (updL Y2 ioY ioX Th thF thG)) := (by with_unfolding_all exact (m2 :))
  exact ⟨updL Y2 ioY ioX Th thF thG, ⟨hL, isGrp_ext hC.grp _ f3, isFam_ext hC.fam _ f3, isModels_ext hC.models _ m3,
    isChain_updL hC.chain Y2 _ _ _ _ _ c3, isThP_updL hC.thP Y2 _ _ _ _ _ p3⟩, f3.2.2.1⟩

end GlobalTheory.TupExt

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open GlobalTheory.BigOn.Exp.TwConj

def SideLev : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {V : NewLev D N}

theorem extL_is (hL : R.toLevCh.Is A.μ0) (hV : ∀ n, TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) (hi : Function.Injective V.xiH)
    (hn : ∀ n t, V.xiH n ≠ R.xiH t)
    (hQ : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
      (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
        ∀ n, ∀ PP ∈ V.Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) :
    (extL R.toLevCh V).Is (.inl A.μ0) where
  mu0 := hL.mu0
  eta := hL.eta
  xi := Sum.rec hL.xi fun n => (hV n).xi
  xi_inj := by
    rintro (t | n) (t' | n') h
    · exact congrArg _ (hL.xi_inj h)
    · exact absurd h.symm (hn n' t)
    · exact absurd h (hn n t')
    · exact congrArg _ (hi h)
  xi_base := hL.xi_base
  xi_fin := Sum.rec hL.xi_fin fun n => (hV n).xi_fin
  xi_triv := Sum.rec hL.xi_triv fun n => (hV n).xi_triv
  xi_tame := Sum.rec hL.xi_tame fun n => (hV n).xi_tame
  Pg := hL.Pg
  Q_pl := Sum.rec hL.Q_pl fun n => (hV n).Q_pl
  Q_off := Sum.rec hL.Q_off fun n => (hV n).Q_off
  Q_de p hp := (hQ p hp).imp fun _ h => Sum.rec h.1 h.2
  Q_ram := Sum.rec hL.Q_ram fun n => (hV n).Q_ram
  chi := hL.chi
  xiR := Sum.rec hL.xiR fun n => (hV n).xiR
  βY := hL.βY
  βX := hL.βX
  βV := hL.βV
  βW := hL.βW

theorem Q_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem fun PP hP => (hL.Q_ram A.μ0 PP).2 (Or.inl hP) (by
    show (R.xiH A.μ0).UnrAt PP
    rw [hL.xi_base]
    exact fun _ _ => rfl)

open Formalism.L2.Host Formalism.L2.Col GlobalTheory.RationalValues in

theorem xiR_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) {χ xi Q xiR} (h : TwLev R χ xi Q xiR) :
    ∀ PP ∈ Q, ∀ x, ((xiR PP x : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  intro PP hPP x
  have i : Fin D.R.m := ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩
  obtain ⟨g, c, c', ht⟩ := hF.tie
  have hok := ht.ok A.μ0
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ Q ∪ R.Q A.μ0
  have hQ : ∀ v ∈ Q, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → χ.UnrAt v := fun v hv => by
    by_contra hn
    rcases (h.Q_ram v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → χ.val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : ((χ.val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm h.xi_triv (hu v hv) hc, Units.val_one]
      show ((χ.val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hF.pl_onto v (hs _ hS)
      have h1 : (R.C.mu0 i * χ).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange := by
        obtain ⟨a, ha⟩ := h.muVal i P (hs _ fun w hw => hw.elim (hS w) (hQ w))
        exact ⟨_, ha⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hF.muVal i A.μ0 P ((hok P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := h.xi_fin
  obtain ⟨a, k, hk, hx, hm⟩ := TypeValues.exists_lift_mem χ _ (T ∪ T.image conjPrime₂) h.xi_tame
    (TypeValues.inf_eq_one _ hn ho) hu hv (Finset.mem_union_left _ (hQ PP hPP)) x
  rw [h.xiR PP hPP a k x hk hx]
  exact hm

variable (R V) in

def okOf (n : N) : Set Pl0 := {P | Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (V.Q n : Set (Pl D.host.E)))}

theorem okOf_subset (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (n : N) : okOf R V n ⊆ A.ok A.μ0 := by
  obtain ⟨g, c, c', ht⟩ := hF.tie
  intro P hP
  refine (ht.ok A.μ0 P).2 ?_
  rw [Q_base hL, Finset.coe_empty, Set.union_empty]
  exact ⟨hP.1, fun h => hP.2.1 (Or.inl h), fun w hw => hP.2.2 w (Or.inl hw)⟩

theorem sep_new (hL' : (extL R.toLevCh V).Is (.inl A.μ0)) (n : N) : ∀ PP ∈ R.Pg, ∀ PP' ∈ V.Q n,
    PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP := fun PP h PP' h' =>
  ⟨fun e => Finset.disjoint_left.1 (idem_of_is hL' (.inr n)).1 h (e ▸ h'),
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL' (.inr n) (Or.inl h) (Or.inr h'),
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL' (.inr n) (Or.inr h') (Or.inl h)⟩

set_option maxHeartbeats 2000000 in

theorem exists_sideX (hS : SideLev) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hL' : (extL R.toLevCh V).Is (.inl A.μ0)) (n : N)
    (hV : TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) :
    ∃ (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : okOf R V n × ℕ → Module.End D.what₂.LL S.Forms)
      (B : Bridge.SideReal D D.sp.X' (Bridge.envOf R.cX.coef
        (levEnvOf D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n)) R.pl (okOf R V n))) S act op (fun i => i.2)),
      (∀ q : (levEnv D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n))).Q, R.eG (B.act_tie.red q) =
        rTup R.βX ((extL R.toLevCh V).datXt (.inr n)) (Formalism.UG.bc (Lev.swapAE D) ((q : Bridge.Gf D.sp.X') : GL _ _))) ∧
      (∀ (lam : D.what₂.Tau → DomWeight D.sp.X'.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] R.cX.coef.W) pair nab del,
        Bridge.CoefTie D.sp.X' R.cX.coef (R.B.R A.μ0).pres lam c0 pair nab del → Bridge.CoefTie D.sp.X' R.cX.coef B.pres lam c0 pair nab del) ∧
      ∀ P, op (P, 0) = 1 ∧ ∀ k, D.sp.X'.rank < k → op (P, k) = 0 := by
  have hχ := GlobalTheory.RationalValues.chiVal_of_chiW R hC.grp.chiW
  have hξ := xiR_mem hC.lev hC.fam hV
  obt ⟨g, c, c', ht⟩ := hC.fam.tie
  have key := hS D G D.sp.X' R.βX R.ΛX hC.lev.βX (R.datXt A.μ0) (V.Q n) ((extL R.toLevCh V).datXt (.inr n)).xq Pl0 R.pl (A.ok A.μ0)
    (okOf R V n) ((R.Sb : Set (Pl D.host.E)) ∪ (V.Q n : Set (Pl D.host.E)))
    (by show R.Q A.μ0 ⊆ _; rw [Q_base hC.lev]; exact Finset.empty_subset _) (okOf_subset hC.lev hC.fam n) (sep_new hL' n)
    (fun P hP => hP) (fun PP h => h.elim (fun h => Or.inl (hC.fam.Sb h)) Or.inr)
    (fun j hj PP hP x => hχ ⟨j, hj⟩ PP hP x)
    (fun PP hP x => by
      have e : ((extL R.toLevCh V).datXt (.inr n)).xq PP x = (V.xiR n PP x)⁻¹ := rfl
      rw [e, Units.val_inv_eq_inv_val]
      exact Subfield.inv_mem _ (hξ PP hP x))
    R.cX.coef _ _ _ (R.B.R A.μ0) ⟨_, c, _, _, _, _, ht.mapR, ht.coefR A.μ0⟩
  obt ⟨S, act, op, B, h1, h2, h3⟩ := key
  refine ⟨S, act, op, B, fun q => ?_, h2, h3⟩
  obt ⟨hq, e⟩ := h1 q
  exact (congrArg R.eG e).trans (hC.grp.red_R A.μ0 ⟨q, hq⟩)

set_option maxHeartbeats 2000000 in

theorem exists_sideV (hS : SideLev) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hL' : (extL R.toLevCh V).Is (.inl A.μ0)) (i : Fin D.R.m)
    (n : N) (hV : TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) :
    ∃ (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : okOf R V n × ℕ → Module.End D.what₂.LL S.Forms)
      (B : Bridge.SideReal D (Vc D i) (Bridge.envOf (R.cV i).coef
        (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) R.pl (okOf R V n))) S act op (fun i => i.2)),
      (∀ q : (levEnv (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n))).Q, R.eG (B.act_tie.red q) =
        rTup (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) (Formalism.UG.bc (Lev.swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _))) ∧
      (∀ (lam : D.what₂.Tau → DomWeight (Vc D i).rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] (R.cV i).coef.W) pair nab del,
        Bridge.CoefTie (Vc D i) (R.cV i).coef (R.B.L i A.μ0).pres lam c0 pair nab del →
          Bridge.CoefTie (Vc D i) (R.cV i).coef B.pres lam c0 pair nab del) ∧
      ∀ P, op (P, 0) = 1 ∧ ∀ k, (Vc D i).rank < k → op (P, k) = 0 := by
  have hχ := GlobalTheory.RationalValues.chiVal_of_chiW R hC.grp.chiW
  have hξ := xiR_mem hC.lev hC.fam hV
  obt ⟨g, c, c', ht⟩ := hC.fam.tie
  have key := hS D G (Vc D i) (R.βV i) (R.ΛV i) (hC.lev.βV i) (R.datVt i A.μ0) (V.Q n) ((extL R.toLevCh V).datVt i (.inr n)).xq Pl0 R.pl
    (A.ok A.μ0) (okOf R V n) ((R.Sb : Set (Pl D.host.E)) ∪ (V.Q n : Set (Pl D.host.E)))
    (by show R.Q A.μ0 ⊆ _; rw [Q_base hC.lev]; exact Finset.empty_subset _) (okOf_subset hC.lev hC.fam n) (sep_new hL' n)
    (fun P hP => hP) (fun PP h => h.elim (fun h => Or.inl (hC.fam.Sb h)) Or.inr)
    (fun j _ PP hP x => by
      have e : (R.datVt i A.μ0).cg (j + 1) PP x = (R.chi ((i : ℕ) + 1) PP x)⁻¹ := rfl
      rw [e, Units.val_inv_eq_inv_val]
      exact Subfield.inv_mem _ (hχ i PP hP x))
    (fun PP hP x => hξ PP hP x)
    (R.cV i).coef _ _ _ (R.B.L i A.μ0) ⟨_, c' i, _, _, _, _, ht.mapL i, ht.coefL i A.μ0⟩
  obt ⟨S, act, op, B, h1, h2, h3⟩ := key
  refine ⟨S, act, op, B, fun q => ?_, h2, h3⟩
  obt ⟨hq, e⟩ := h1 q
  exact (congrArg R.eG e).trans (hC.grp.red_L i A.μ0 ⟨q, hq⟩)

set_option maxHeartbeats 2000000 in

def newRealOfSideData {X : NewFam A N}
    (BR : ∀ n, Bridge.SideReal D D.sp.X'
      (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh V).datXt (.inr n)) R.pl (X.ok n)))
      (X.SR n) (X.actR n) (X.opR n) (fun i => i.2))
    (BL : ∀ i n, Bridge.SideReal D (Vc D i)
      (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh V).datVt i (.inr n)) R.pl (X.ok n)))
      (X.SL i n) (X.actL i n) (X.opL i n) (fun i => i.2)) : NewReal R V X where
  BR := BR
  BL := BL
  HX _ := R.HX A.μ0
  HV i _ := R.HV i A.μ0
  jX _ := 0
  jV _ _ := 0
  νY _ := R.νY A.μ0
  fdY _ := R.fdY A.μ0
  νX _ := R.νX A.μ0
  fdX _ := R.fdX A.μ0
  νV i _ := R.νV i A.μ0
  fdV i _ := R.fdV i A.μ0
  ωY _ := R.ωY A.μ0
  ωX _ := R.ωX A.μ0
  ωP i _ := R.ωP i A.μ0
  vY _ := R.vY A.μ0
  vX _ := R.vX A.μ0
  vP i _ := R.vP i A.μ0
  ioY _ _ := 0
  ioX _ := 0
  Th _ := 0
  thF _ _ := 0
  thG _ _ := 0

set_option maxHeartbeats 2000000 in

theorem fam_stage (hS : SideLev) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hL' : (extL R.toLevCh V).Is (.inl A.μ0))
    (hV : ∀ n, TwLev R (V.xiH n) (V.xi n) (V.Q n) (V.xiR n)) : ∃ (X : NewFam A N) (Y : NewReal R V X), FamC Y := by
  choose SR actR opR BR a1 a2 a3 using fun n => exists_sideX hS hC hL' n (hV n)
  choose SL actL opL BL b1 b2 b3 using fun i n => exists_sideV hS hC hL' i n (hV n)
  choose mu hmu using fun i n P => exists_cond (1 : D.what₂.LLˣ) ((hV n).muVal i P)
  refine ⟨⟨okOf R V, mu, SR, actR, opR, SL, actL, opL⟩, newRealOfSideData BR BL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hC.grp.red_R t :))
    · exact (by with_unfolding_all exact (a1 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hC.grp.red_L i t :))
    · exact (by with_unfolding_all exact (b1 i n :))
  · intro g c c' ht
    refine ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ?_, ht.gramR_eq, ht.mapR, ht.mapL, ?_, ?_⟩
    · rintro (t | n)
      · exact (by with_unfolding_all exact (ht.ok t :))
      · exact fun _ => Iff.rfl
    · rintro (t | n)
      · exact (by with_unfolding_all exact (ht.coefR t :))
      · exact (by with_unfolding_all exact (a2 n _ _ _ _ _ (ht.coefR A.μ0) :))
    · rintro i (t | n)
      · exact (by with_unfolding_all exact (ht.coefL i t :))
      · exact (by with_unfolding_all exact (b2 i n _ _ _ _ _ (ht.coefL i A.μ0) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hC.fam.roots t :))
    · exact fun PP h => h.elim (fun h => hC.fam.roots A.μ0 PP (Or.inl h)) ((hV n).roots PP)
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hC.fam.degR t :))
    · exact (by with_unfolding_all exact (a3 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hC.fam.degL i t :))
    · exact (by with_unfolding_all exact (b3 i n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hC.fam.muVal i t :))
    · exact (by with_unfolding_all exact (hmu i n :))

end GlobalTheory.TupExt

end
end

section
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open GlobalTheory.BigOn.Exp.TwConj

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 N : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
  {j : Fin D.R.m} {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X)

set_option maxHeartbeats 2000000 in

theorem baseOf_ext {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (extR R Y) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩

set_option maxHeartbeats 2000000 in

theorem ext_ext : Ext T R κ v₀ O j (extR R Y) v₀ (fun i => omExt Y (O i)) := by
  refine ⟨fun τ h => (fixBase_ext Y j τ).2 h, fun τ ζ Φ Φ' h => ?_, ?_⟩
  · exact (h)
  · exact (by with_unfolding_all exact ((Ext.refl (T := T) (R := R) (κ := κ) (v₀ := v₀) (O := O) (j := j)).2.2 :))

end

set_option maxHeartbeats 2000000 in

theorem extend_tuples : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  intro h1 _ _ h4 h5 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL N _ χ xi Q xiR hV hi hn hQ
  obt ⟨hC, hfin, ⟨hfw⟩, hio, hg, hp, hph, hB⟩ := hL
  let V : NewLev D N := ⟨χ, xi, Q, xiR⟩
  have hL' : (extL R.toLevCh V).Is (.inl A.μ0) := extL_is hC.lev hV hi hn hQ
  obt ⟨X, Y0, h0⟩ := fam_stage (GlobalTheory.SideLevel.sideReal_moreLevel) hC hL' hV
  obt ⟨Y, hC', hT⟩ := core_ext h4 GlobalTheory.HcPort.print_harishChandraModules h1 h5 (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hC hL' Y0 h0
  have hg' : QGuard (extR R Y) := ⟨Sum.rec hg.1 fun n => (hV n).half, Sum.rec hg.2 fun n => (hV n).guard⟩
  exact ⟨T0 ⊕ N, extA A X, extR R Y, extF F X, v₀, fun i => omExt Y (O i),
    ⟨hC', inferInstance, ⟨fwExt Y hfw⟩, ioExt_ext R Y hio, hg', omPins_ext Y hT hp, phaseTie_ext Y hph, baseOf_ext Y hB⟩,
    ext_ext Y, fun n => ⟨.inr n, rfl, rfl⟩⟩

end GlobalTheory.TupExt

end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  atlas_forward_decl GlobalTheory.TupExt.extend_tuples
end
