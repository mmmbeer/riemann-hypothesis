import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictToBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Formalism.LocalToGlobal.IndefiniteReal.LinksComap
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixBaseOfFixingField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type}

def extL (L : LevCh D T) (s : N → T) (a : N → ℕ) : LevCh D (T ⊕ N) :=
  { L with
    xiH := Sum.elim L.xiH fun n => L.xiH (s n) ^ a n
    xi := Sum.elim L.xi fun n => L.xi (s n) ^ a n
    Q := Sum.elim L.Q fun n => L.Q (s n)
    xiR := Sum.elim L.xiR fun n PP => L.xiR (s n) PP ^ a n }

structure NewFam {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) (s : N → T) where
  muVal : Fin m → N → Pl0 → Kˣ
  SR : N → CSD K
  actR : ∀ n, Representation K G (SR n).Forms
  opR : ∀ n, A.ok (s n) × ℕ → Module.End K (SR n).Forms
  SL : Fin m → N → CSD K
  actL : ∀ j n, Representation K G (SL j n).Forms
  opL : ∀ j n, A.ok (s n) × ℕ → Module.End K (SL j n).Forms

def extA {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A : FamIn K G Pl0 T m) {s : N → T} (X : NewFam A s) :
    FamIn K G Pl0 (T ⊕ N) m where
  v0 := A.v0
  μ0 := .inl A.μ0
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j := Sum.elim (A.muVal j) (X.muVal j)
  etaVal := A.etaVal
  ok := Sum.elim A.ok fun n => A.ok (s n)
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

structure NewReal (R : RealDat D A Ks) {s : N → T} (a : N → ℕ) (X : NewFam A s) where
  BR : ∀ n, Bridge.SideReal D D.sp.X'
    (Bridge.envOf R.cX.coef (levEnvOf D.sp.X' R.βX ((extL R.toLevCh s a).datXt (.inr n)) R.pl (A.ok (s n))))
    (X.SR n) (X.actR n) (X.opR n) (fun i => i.2)
  BL : ∀ i n, Bridge.SideReal D (Vc D i)
    (Bridge.envOf (R.cV i).coef (levEnvOf (Vc D i) (R.βV i) ((extL R.toLevCh s a).datVt i (.inr n)) R.pl (A.ok (s n))))
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
  ioY : ∀ n k, MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) ((extL R.toLevCh s a).datYt (.inr n) (k + 1) R.triv))
      (Lev.levChi _ (R.βY (k + 1)) ((extL R.toLevCh s a).datYt (.inr n) (k + 1) R.triv)) →ₗ[ℂ]
    MultT R.θ (R.MY k) (levS _ (R.βY k) ((extL R.toLevCh s a).datYt (.inr n) k R.triv))
      (Lev.levChi _ (R.βY k) ((extL R.toLevCh s a).datYt (.inr n) k R.triv))
  ioX : ∀ n, LinearMap.range (R.cX.toMap R.prX ∘ₗ (HX n).e) →ₗ[ℂ]
    MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) ((extL R.toLevCh s a).datYt (.inr n) (D.R.m - 1) R.triv))
      (Lev.levChi _ (R.βY (D.R.m - 1)) ((extL R.toLevCh s a).datYt (.inr n) (D.R.m - 1) R.triv))
  Th : ∀ n, (HX n).H →ₗ[ℂ] R.HE.H
  thF : ∀ i n, (HV i n).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))
  thG : ∀ i n, (HV i n).H →ₗ[ℂ] (R.HW i (sg0 D A)).H

set_option maxHeartbeats 4000000 in

def extR (R : RealDat D A Ks) {s : N → T} {a : N → ℕ} {X : NewFam A s} (Y : NewReal R a X) : RealDat D (extA A X) Ks where
  toLevCh := extL R.toLevCh s a
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
theorem extR_comap (R : RealDat D A Ks) {s : N → T} {a : N → ℕ} {X : NewFam A s} (Y : NewReal R a X) :
    (extR R Y).comap Sum.inl A.μ0 R.mu R.twPl R.FW R.kap R.lam R.err0 = R := rfl

end GlobalTheory.ConjExt

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

open Formalism.L2.Host

variable {D : D7} {T N : Type}

theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

theorem trivOn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : HChar E}
    (h : χ.TrivOn F) (a : ℕ) : (χ ^ a).TrivOn F := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h1 := h.1 v k
    simp only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [locK_pow]
    rw [Finset.prod_pow, h1, one_pow]
  · have h1 := h.2 w k
    simp only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [pow_apply']
    rw [Finset.prod_pow, h1, one_pow]

theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) : (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) : ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : χ.OrderDvd n) :
    c ^ n = 1 := by
  have h1 := chrEq_pow h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem exists_pow_aut (τ : ℂ ≃+* ℂ) {n : ℕ} (hn : 0 < n) : ∃ a, a < n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨a, ha, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n)))
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a, ha, fun z hz => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]

theorem exists_conj_pow {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ n : ℕ, ∀ τ : ℂ ≃+* ℂ, ∃ a, a < n ∧
    (∀ x, (((L.xi t ^ a) x : Circle) : ℂ) = τ ((L.xi t x : Circle) : ℂ)) ∧ ∃ b, (L.xiH t ^ a) ^ b = L.xiH t := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1 := fun x => by
    have := DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a := fun a x => by
    rw [MonoidHom.pow_apply]; exact map_pow Circle.coeHom _ _
  refine ⟨n, fun τ => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_pow_aut τ hn
  obtain ⟨b, -, h'⟩ := exists_pow_aut τ.symm hn
  refine ⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩
  have e : (L.xi t ^ a) ^ b = L.xi t := MonoidHom.ext fun x => Circle.ext (by
    rw [← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])
  exact GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)

end GlobalTheory.ConjExt

end
end

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwLevPow

theorem val_pow {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (a : ℕ) (v) :
    (χ ^ a).val v = χ.val v ^ a :=
  GlobalTheory.ConjExt.locK_pow χ a v _

theorem twLev_pow : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → ∀ a b : ℕ, (χ ^ a) ^ b = χ →
      GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ ^ a) (xi ^ a) Q (fun PP => xiR PP ^ a) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC χ xi Q xiR h a b hab

  have hQ0 : ∀ PP, PP ∉ R.Q A.μ0 := fun PP hPP =>
    ((hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP)) (by rw [hC.lev.xi_base]; intro x _; rfl)
  refine
    { xi := GlobalTheory.ConjExt.chrEq_pow h.xi a
      xi_fin := ?_
      xi_triv := GlobalTheory.ConjExt.trivOn_pow h.xi_triv a
      xi_tame := fun v x h1 h2 => by
        rw [GlobalTheory.ConjExt.loc_pow, h.xi_tame v x h1 h2, one_pow]
      Q_pl := h.Q_pl
      Q_off := h.Q_off
      Q_de := h.Q_de
      Q_ram := fun PP => Iff.trans
        (not_congr ⟨fun hu => hab ▸ GlobalTheory.ConjExt.unrAt_pow hu b, fun hu => GlobalTheory.ConjExt.unrAt_pow hu a⟩) (h.Q_ram PP)
      xiR := fun PP hP c k u h1 h2 => by
        show (xiR PP ^ a) u = (χ ^ a).locK PP k
        rw [GlobalTheory.ConjExt.locK_pow, MonoidHom.pow_apply, h.xiR PP hP c k u h1 h2]
      roots := h.roots
      muVal := ?_
      half := h.half
      guard := h.guard }
  · obtain ⟨n, hn, ho⟩ := h.xi_fin
    refine ⟨n, hn, ?_⟩
    show (χ ^ a) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, show χ ^ n = 1 from ho, one_pow]
  · intro i P hP
    obtain ⟨x, hx⟩ := h.muVal i P hP
    have hP0 : Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A.μ0 : Set (Pl D.host.E))) := by
      refine ⟨hP.1, fun hm => ?_, fun Q' hQ' => ?_⟩
      · rcases hm with hm | hm
        · exact hP.2.1 (Or.inl hm)
        · exact hQ0 _ hm
      · rcases hQ' with hQ' | hQ'
        · exact hP.2.2 Q' (Or.inl hQ')
        · exact absurd hQ' (hQ0 _)
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    have hy := hC.fam.muVal i A.μ0 P ((ht.ok A.μ0 P).2 hP0)
    rw [hC.lev.xi_base, mul_one] at hy
    set y : D.what₂.LLˣ := A.muVal i A.μ0 P
    refine ⟨y * (y⁻¹ * x) ^ a, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, map_mul, map_pow, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hx, hy, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, val_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.TwLevPow
end
end

section
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open Classical in

theorem hasTuples_of_conj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  intro hDS hCW h1 h2 h3 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL ψ ψ' t τ ht hc hf
  have hC := hL.1
  obtain ⟨n, hn⟩ := GlobalTheory.ConjExt.exists_conj_pow hC.lev t
  obtain ⟨a, -, ha, b, hb⟩ := hn τ
  have hxi' : B.de.chi * ψ'.chi = R.xi t ^ a := by
    refine MonoidHom.ext fun x => Circle.ext ?_
    rw [ha x, ht.1]
    simp only [MonoidHom.mul_apply, Circle.coe_mul, map_mul, hf.1, hc.2]
  have hQ' : R.Q t = B.de.Q ∪ ψ'.Q := by rw [hc.1, ht.2]
  by_cases hχ : R.xiH t ^ a = R.xiH t
  · have e : R.xi t ^ a = R.xi t :=
      GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (GlobalTheory.ConjExt.chrEq_pow (hC.lev.xi t) a) (by rw [hχ]; exact hC.lev.xi t)
    exact hasTuples_of_laws hL Ext.refl ht ⟨by rw [hxi', e], hQ'⟩
  · have h0 : R.xiH t ≠ 1 := fun h => hχ (by rw [h, one_pow])
    have h0a : R.xiH t ^ a ≠ 1 := fun h => h0 (by rw [← hb, h, one_pow])
    have hlev := twLev_of_core hC hL.2.2.2.2.1 t
    have hleva := GlobalTheory.TwLevPow.twLev_pow R F hC _ _ _ _ hlev a b hb
    obtain ⟨A0, R0, F0, v0, O0, hL0, hE0, hxi0, htr⟩ := GlobalTheory.BaseRestrict.restrict_to_base T R F κ v₀ O ph j B hL
    have hT0 := htr _ _ _ _ hlev
    have hT0a := htr _ _ _ _ hleva
    obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 hDS hCW T R0 F0 κ v0 O0 ph j B hH hL0 Bool
      (fun b => if b then R.xiH t ^ a else R.xiH t) (fun b => if b then R.xi t ^ a else R.xi t) (fun _ => R.Q t)
      (fun b => if b then (fun PP => R.xiR t PP ^ a) else R.xiR t)
      (fun b => by cases b <;> assumption)
      (fun x y hxy => by
        cases x <;> cases y
        · rfl
        · exact absurd hxy.symm hχ
        · exact absurd hxy hχ
        · rfl)
      (fun b t0 => by rw [hxi0]; cases b; exacts [h0, h0a])
      (fun p hp => by
        obtain ⟨𝔭, h𝔭, h𝔭'⟩ := hT0.Q_de p hp
        exact ⟨𝔭, h𝔭, fun _ => h𝔭'⟩)
    obtain ⟨s, hs1, hs2⟩ := htup false
    obtain ⟨s', hs1', hs2'⟩ := htup true
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := s) (t' := s')
      ⟨hs1.trans ht.1, hs2.trans ht.2⟩ ⟨hs1'.trans hxi'.symm, hs2'.trans hQ'⟩

end GlobalTheory.BigOn.Exp.TwConj
end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (ψ ψ' : Twist D Circle) (t : T0) (τ : ℂ ≃+* ℂ), IsTupOf R B ψ t → ConjChar τ ψ ψ' → FixDat B τ →
      GlobalTheory.BigOn.Exp.TwConj.HasTuples T R κ v₀ O ph j B ψ ψ' := by
  atlas_forward_decl GlobalTheory.BigOn.Exp.TwConj.hasTuples_of_conj
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceTup

theorem hasTuples_at_place : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ' : Twist D Circle, ψ'.Good → ConjChar τ (twVia Z.ρ ι) ψ' →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) (twVia Z.ρ ι) ψ' := by
  intro hDS hCW _ hP D X X0 Y S YS Z c w j H ι hι τ hτ ψ' hψ' hC
  have hC0 := X.char
  have hL : GlobalTheory.BigOn.Exp.TwConj.Laws X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j (baseOf Z c w j) :=
    ⟨⟨hC0.lev, hC0.grp, hC0.fam, hC0.models, hC0.chain, hC0.thP⟩, X.finT, ⟨X.geo.fw⟩,
      GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC0.lev hC0.fam hC0.models hC0.thP, X.guard, X.geo.pins j,
      by
        convert X.geo.phase j X.unif using 2
        all_goals (rename_i k; rw [X.phs k]; try simp),
      GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hC0.lev Z.good Z.pin (c.twI w) j (c.sd w)⟩
  exact GlobalTheory.T.twist_conjugate_tuples_same_realisation_extension hDS hCW hP.decay hP.what₂.art hP.ray X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j
    (baseOf Z c w j) X.host hL (twVia Z.ρ ι) ψ' (Y.tupT (D.what₂.muTw w)) τ (H.tup ι hι) hC
    (GlobalTheory.PlaceFix.fix_at_place hP D X X0 Y S YS Z c w j H τ hτ).2

end GlobalTheory.PlaceTup
end
