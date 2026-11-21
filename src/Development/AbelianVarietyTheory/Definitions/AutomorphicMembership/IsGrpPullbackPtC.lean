import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTranslatedPullOfIsTransPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommPairing (tval translT_fst)
open GlobalTheory.ThetaAct (sv sv_ext sv_add sv_smul translT_translT translT_one translT_snd translPt_one)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLaw

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

section Twist

variable {L : LB A.left} (hL : L.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} (hm : ψ ≫ snd T A = m)
  (hψ : ψ ≫ fst T A = fst T A) {a b : ℤ}
  (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (hα : α.IsGen)

def twistFun (v : SecM A L b T) : SecM A L a T :=
  SecM.ofSec A (VVRank.exists_isTwistPull A (hm := hm) hL hα (SecM.toSec A v)).choose

theorem sv_twistFun (v : SecM A L b T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sv (twistFun hL hm α hα v) r z J = (val α r z J).val * sv v (r ≫ ψ.left) z J :=
  VVRank.sv_of_isTwistPull A (VVRank.exists_isTwistPull A (hm := hm) hL hα (SecM.toSec A v)).choose_spec r z hJ

def twist : SecM A L b T →ₗ[Γ(T.left, ⊤)] SecM A L a T where
  toFun := twistFun hL hm α hα
  map_add' v w := sv_ext hL fun y J hJ => by
    rw [sv_add _ _ _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ,
      sv_add _ _ _ _ hJ, mul_add]
  map_smul' c v := sv_ext hL fun y J hJ => by
    have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
    rw [RingHom.id_apply, sv_smul _ (twistFun hL hm α hα v) _ _ hJ, sv_twistFun _ _ _ _ _ _ _ hJ,
      sv_twistFun _ _ _ _ _ _ _ hJ, sv_smul _ v _ _ hJ, Category.assoc, e, mul_left_comm]

theorem sv_twist (v : SecM A L b T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sv (twist hL hm hψ α hα v) r z J = (val α r z J).val * sv v (r ≫ ψ.left) z J :=
  sv_twistFun hL hm α hα v r z hJ

end Twist

section Group

variable {k : ℤ} {T : Over S}

theorem gen_ext {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (𝟙 _) y J = val u' (𝟙 _) y J) : u = u' := by
  have e := sec_ext_val hM (s := genSec u hu) (s' := genSec u' hu') fun y J hJ => by
    rw [sval_genSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ, h y J hJ]
  cases u; cases u'
  exact congrArg _ (funext fun j => Units.ext (e j))

theorem ext {L : LB A.left} (hL : L.IsLB) {θ θ' : ThetaGrp A L k T} (h : θ.pt = θ'.pt)
    (hv : ∀ y J, Good L y J → tval θ (𝟙 _) y J = tval θ' (𝟙 _) y J) : θ = θ' := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  obtain rfl : u = u' := gen_ext hL hu hu' hv
  rfl

theorem exists_scalar {L : LB A.left} (hL : L.IsLB) (k : ℤ) (c : Γ(T.left, ⊤)ˣ) :
    ∃ θ : ThetaGrp A L k T, θ.pt = 1 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine (Fintype.prod_empty _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, translPt_one, mul_inv_cancel])
    (constGen A L c) (isGen_of_gm _ fun y j j' h h' => by
      obtain rfl : j = j' := Subsingleton.elim _ _
      rw [trF, Fintype.prod_empty, _root_.one_mul])
  exact ⟨⟨1, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (H1.val_constGen L c r z J)⟩

variable {L : RigLB A}

instance : One (ThetaGrp A L.L k T) := ⟨(exists_scalar L.isLB k 1).choose⟩

instance : Mul (ThetaGrp A L.L k T) := ⟨fun θ θ' => (ThetaAct.exists_mul L.isLB θ θ').choose⟩

instance : Inv (ThetaGrp A L.L k T) := ⟨fun θ => (ThetaAct.exists_inv L.isLB θ).choose⟩

theorem pt_one : (1 : ThetaGrp A L.L k T).pt = 1 := (exists_scalar L.isLB k 1).choose_spec.1

theorem pt_mul' (θ θ' : ThetaGrp A L.L k T) : (θ * θ').pt = θ'.pt * θ.pt :=
  (ThetaAct.exists_mul L.isLB θ θ').choose_spec.1

theorem pt_inv (θ : ThetaGrp A L.L k T) : θ⁻¹.pt = θ.pt⁻¹ := (ThetaAct.exists_inv L.isLB θ).choose_spec.1

section Val

variable {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.L.ι} (hJ : Good L.L z J)
include hJ

theorem tval_one : tval (1 : ThetaGrp A L.L k T) r z J = 1 :=
  ((exists_scalar L.isLB k 1).choose_spec.2 Z r z J hJ).trans (map_one _)

theorem tval_mul (θ θ' : ThetaGrp A L.L k T) :
    tval (θ * θ') r z J = tval θ r z J * tval θ' (r ≫ (translT A θ.pt).left) z J :=
  (ThetaAct.exists_mul L.isLB θ θ').choose_spec.2 Z r z J hJ

theorem tval_inv (θ : ThetaGrp A L.L k T) : tval θ⁻¹ r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹ :=
  (ThetaAct.exists_inv L.isLB θ).choose_spec.2 Z r z J hJ

end Val

instance group : Group (ThetaGrp A L.L k T) :=
  Group.ofLeftAxioms
    (fun a b c => ext L.isLB (by simp only [pt_mul', _root_.mul_assoc]) fun y J hJ => by
      simp only [tval_mul _ _ hJ, pt_mul', Category.assoc, translT_translT, _root_.mul_assoc])
    (fun a => ext L.isLB (by rw [pt_mul', pt_one, _root_.mul_one]) fun y J hJ => by
      rw [tval_mul _ _ hJ, tval_one _ _ hJ, pt_one, translT_one, Category.comp_id, _root_.one_mul])
    (fun a => ext L.isLB (by rw [pt_mul', pt_inv, pt_one, mul_inv_cancel]) fun y J hJ => by
      rw [tval_mul _ _ hJ, tval_inv _ _ hJ, tval_one _ _ hJ, pt_inv, inv_mul_cancel])

variable (L k T)

def scalar : Γ(T.left, ⊤)ˣ →* ThetaGrp A L.L k T :=
  MonoidHom.mk' (fun c => (exists_scalar L.isLB k c).choose) fun c d => by
    have p := fun c => (exists_scalar (T := T) L.isLB k c).choose_spec
    refine ext L.isLB (by rw [pt_mul', (p _).1, (p _).1, (p _).1, _root_.mul_one]) fun y J hJ => ?_
    rw [tval_mul _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, Category.assoc, translT_fst, map_mul]

def op {L : RigLB A} {k : ℤ} {T : Over S} (θ : ThetaGrp A L.L k T) : Module.End Γ(T.left, ⊤) (SecM A L.L k T) :=
  twist L.isLB (ψ := translT A θ.pt) (lift_snd _ _) (lift_fst _ _) θ.φ θ.isGen

theorem sv_op {L : RigLB A} {k : ℤ} {T : Over S} (θ : ThetaGrp A L.L k T) (v : SecM A L.L k T) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    sv (op θ v) r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J :=
  sv_twist L.isLB _ _ θ.φ θ.isGen v r z hJ

def action : ThetaGrp A L.L k T →* Module.End Γ(T.left, ⊤) (SecM A L.L k T) where
  toFun := op
  map_one' := LinearMap.ext fun v => sv_ext L.isLB fun y J hJ => by
    rw [sv_op _ _ _ _ hJ, tval_one _ _ hJ, pt_one, translT_one, Category.comp_id, Units.val_one, _root_.one_mul]; rfl
  map_mul' a b := LinearMap.ext fun v => sv_ext L.isLB fun y J hJ => by
    rw [Module.End.mul_apply, sv_op _ _ _ _ hJ, sv_op _ _ _ _ hJ, sv_op _ _ _ _ hJ, tval_mul _ _ hJ, pt_mul', Category.assoc,
      translT_translT, Units.val_mul, _root_.mul_assoc]

variable {L k T}

theorem pt_scalar (c : Γ(T.left, ⊤)ˣ) : (scalar k T L c).pt = 1 := (exists_scalar L.isLB k c).choose_spec.1

theorem tval_scalar (c : Γ(T.left, ⊤)ˣ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    tval (scalar k T L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := (exists_scalar L.isLB k c).choose_spec.2 Z r z J hJ

theorem scalar_comm (c : Γ(T.left, ⊤)ˣ) (θ : ThetaGrp A L.L k T) : scalar k T L c * θ = θ * scalar k T L c :=
  ext L.isLB (by rw [pt_mul', pt_mul', pt_scalar, _root_.mul_one, _root_.one_mul]) fun y J hJ => by
    rw [tval_mul _ _ hJ, tval_mul _ _ hJ, tval_scalar _ _ _ hJ, tval_scalar _ _ _ hJ, pt_scalar, translT_one,
      Category.comp_id, Category.assoc, translT_fst, mul_comm]

theorem scalar_injective : Function.Injective (scalar k T L) := fun c d h => by
  refine unit_ext fun y _ => ?_
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart L.isLB (χ y)
  have e : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have a := tval_scalar (k := k) c (ptSecT A (1 : T ⟶ A)).left y hJ
  have b := tval_scalar (k := k) d (ptSecT A (1 : T ⟶ A)).left y hJ
  rw [e] at a b
  rw [← a, ← b, h]

theorem action_scalar (c : Γ(T.left, ⊤)ˣ) (v : SecM A L.L k T) : action k T L (scalar k T L c) v = c.val • v :=
  sv_ext L.isLB fun y J hJ => by
    refine (sv_op _ _ _ _ hJ).trans ?_
    rw [sv_smul _ _ _ _ hJ, tval_scalar _ _ _ hJ, pt_scalar, translT_one, Category.comp_id, gs_unit _ _ ⊤ trivial]

theorem exists_scalar_eq (hp : Function.Surjective (fst T A).left.appTop.hom) {θ : ThetaGrp A L.L k T} (h : θ.pt = 1) :
    ∃ c, scalar k T L c = θ := by
  obtain ⟨c, hc⟩ := SymLiftConst.exists_constT hp L.isLB (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, h, translPt_one, mul_inv_cancel])
    θ.isGen
  refine ⟨c, ext L.isLB ((pt_scalar c).trans h.symm) fun y J hJ => ?_⟩
  have e := hc (snd T A) y J hJ
  rw [lift_fst_snd] at e
  rw [tval_scalar _ _ _ hJ, Category.id_comp]
  exact e.symm

variable [IsCommMonObj A]

theorem pt_mul (θ θ' : ThetaGrp A L.L k T) : (θ * θ').pt = θ.pt * θ'.pt := (pt_mul' θ θ').trans (mul_comm _ _)

variable (L k T) in

def ptHom : ThetaGrp A L.L k T →* (T ⟶ A) := MonoidHom.mk' ThetaGrp.pt pt_mul

def nval (ν : LB.Gen (negLB A L.L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J

omit [IsCommMonObj A] in

theorem negT_snd : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
  rw [← Over.comp_left, negT, lift_snd]

omit [IsCommMonObj A] in

theorem negT_fst : (negT A T).left ≫ (fst T A).left = (fst T A).left := by
  rw [← Over.comp_left, negT, lift_fst]

omit [IsCommMonObj A] in

theorem negT_negT : (negT A T).left ≫ (negT A T).left = 𝟙 _ := by
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [← Over.comp_left, negT, comp_lift, lift_fst, e, GrpObj.comp_inv, lift_snd, inv_inv, lift_fst_snd]; rfl

theorem translT_negT (x : T ⟶ A) : (translT A x).left ≫ (negT A T).left = (negT A T).left ≫ (translT A x⁻¹).left := by
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [← Over.comp_left, ← Over.comp_left, negT, e, lift_transl, comp_lift, translT, lift_fst, GrpObj.comp_inv, lift_snd,
    translPt_eq, mul_inv, GrpObj.comp_inv]

theorem exists_conj (ν : LB.Gen (negLB A L.L k T)) (hν : ν.IsGen) (θ : ThetaGrp A L.L k T) :
    ∃ θ' : ThetaGrp A L.L k T, θ'.pt = θ.pt⁻¹ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L.L z J →
      tval θ' r z J = nval ν r z J * (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  have e₁ : (negT A T).left ≫ (translPt A θ.pt).left =
      (translT A θ.pt⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← negT_snd, ← Category.assoc, translT_negT, inv_inv, Category.assoc, translT_snd]
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (translPt A θ.pt⁻¹).left]) (ε' := ![k, -k])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, negT_snd, translT_snd, e₁]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] _ _ ν (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (negT A T).left)
      (LB.invGen L.L _ _ (LB.pullGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν
        (translT A θ.pt⁻¹).left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hν (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _))))
  exact ⟨⟨_, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))))⟩

def conj (ν : LB.Gen (negLB A L.L k T)) (hν : ν.IsGen) : ThetaGrp A L.L k T →* ThetaGrp A L.L k T :=
  MonoidHom.mk' (fun θ => (exists_conj ν hν θ).choose) fun a b => by
    have p := fun θ => (exists_conj ν hν θ).choose_spec
    refine ext L.isLB ((p _).1.trans (Eq.trans ?_ (pt_mul _ _).symm)) fun y J hJ => ?_
    · rw [(p _).1, (p _).1, pt_mul, mul_inv]
    rw [tval_mul _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).2 _ _ _ _ hJ, (p _).1, tval_mul _ _ hJ, pt_mul]
    simp only [Category.assoc, translT_negT, translT_translT, inv_inv, mul_inv_rev]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

section Conj

variable (ν : LB.Gen (negLB A L.L k T)) (hν : ν.IsGen)

theorem pt_conj (θ : ThetaGrp A L.L k T) : (conj ν hν θ).pt = θ.pt⁻¹ := (exists_conj ν hν θ).choose_spec.1

theorem tval_conj (θ : ThetaGrp A L.L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L.L z J) :
    tval (conj ν hν θ) r z J =
      nval ν r z J * (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (exists_conj ν hν θ).choose_spec.2 Z r z J hJ

theorem conj_scalar (c : Γ(T.left, ⊤)ˣ) : conj ν hν (scalar k T L c) = scalar k T L c :=
  ext L.isLB (by rw [pt_conj, pt_scalar, inv_one]) fun y J hJ => by
    rw [tval_conj _ _ _ _ _ hJ, tval_scalar _ _ _ hJ, tval_scalar _ _ _ hJ, pt_scalar, inv_one, translT_one,
      Category.comp_id, Category.assoc, negT_fst, mul_inv_cancel_comm_assoc]

def negOp : Module.End Γ(T.left, ⊤) (SecM A L.L k T) :=
  twist L.isLB (ψ := negT A T) (lift_snd _ _) (lift_fst _ _) ν hν

variable (hp : Function.Surjective (fst T A).left.appTop.hom)
include hp

theorem conj_conj (θ : ThetaGrp A L.L k T) : conj ν hν (conj ν hν θ) = θ :=
  ext L.isLB (by rw [pt_conj, pt_conj, inv_inv]) fun y J hJ => by
    have e₁ : (negT A T).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T A).left := by
      rw [← negT_snd, ← Category.assoc, negT_negT, Category.id_comp]
    obtain ⟨a, ha⟩ := H1.exists_const L.L L.isLB (fst T A).left hp
      (LB.mulGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] _ _ ν
        (LB.pullGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν (negT A T).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ hν (DVR.pullGen_isGen _ _ _ _ hν _)) (fun U _ f => by
        simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one, negT_snd, e₁]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    have v : ∀ r : (T ⊗ A).left ⟶ (T ⊗ A).left,
        (nval ν r y J * nval ν (r ≫ (negT A T).left) y J).val = gs (r ≫ (fst T A).left) y ⊤ a := fun r =>
      (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))).symm.trans (ha _ r y J hJ)
    have e : nval ν (𝟙 _) y J * nval ν (𝟙 _ ≫ (negT A T).left) y J = nval ν (𝟙 _ ≫ (translT A θ.pt).left) y J *
        nval ν ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (negT A T).left) y J :=
      Units.ext (by rw [v, v, Category.assoc, translT_fst])
    rw [tval_conj _ _ _ _ _ hJ, tval_conj _ _ _ _ _ hJ, pt_conj, inv_inv]
    simp only [Category.assoc, negT_negT, translT_negT, Category.comp_id] at e ⊢
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e ⊢
    linear_combination (norm := abel) e

end Conj

def delta (hs : L.IsSymmetric) (hp : Function.Surjective (fst T A).left.appTop.hom) :
    ThetaGrp A L.L k T ≃* ThetaGrp A L.L k T :=
  have h := (SymLiftConst.exists_gen_neg L hs k T).choose_spec
  { conj _ h with
    invFun := conj _ h
    left_inv := conj_conj _ h hp
    right_inv := conj_conj _ h hp }

section Delta

variable (hs : L.IsSymmetric) (hp : Function.Surjective (fst T A).left.appTop.hom)

theorem pt_delta (θ : ThetaGrp A L.L k T) : (delta hs hp θ).pt = θ.pt⁻¹ :=
  pt_conj _ (SymLiftConst.exists_gen_neg L hs k T).choose_spec θ

theorem delta_scalar (c : Γ(T.left, ⊤)ˣ) : delta hs hp (scalar k T L c) = scalar k T L c :=
  conj_scalar _ (SymLiftConst.exists_gen_neg L hs k T).choose_spec c

theorem delta_delta (θ : ThetaGrp A L.L k T) : delta hs hp (delta hs hp θ) = θ :=
  conj_conj _ (SymLiftConst.exists_gen_neg L hs k T).choose_spec hp θ

end Delta

theorem exists_lift (c : CubicalStr A L) {V : Type} [CommRing V] [IsLocalRing V] (t : Sp V ⟶ S) {n : ℕ}
    {x : Over.mk t ⟶ A} (hx : x ^ n = 1) : ∃ θ : ThetaGrp A L.L n (Over.mk t), θ.pt = x := by
  obtain ⟨v, hv⟩ := DVR.exists_gen_of_local (V := V) L.L L.isLB (K := Fin 2) ![(1 : Over.mk t ⟶ A).left, x.left]
    ![(n : ℤ), -(n : ℤ)]
  exact exists_theta c hx v hv fun U _ h => Fin.prod_univ_two _

end Group

section EndPull

variable [IsCommMonObj A] {L : RigLB A} {φ : A ⟶ A} {a b : ℤ}
  (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (h₀ : α₀.IsGen) (T : Over S)

def endPull : SecM A L.L b T →ₗ[Γ(T.left, ⊤)] SecM A L.L a T :=
  twist L.isLB (ψ := PullbackSections.endT A T φ) (lift_snd _ _) (lift_fst _ _) _
    (TransPullCompare.exists_pull_gen L.isLB α₀ h₀ T).choose_spec.1

variable {T}

end EndPull

end GlobalTheory.ThetaLaw
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.ThetaLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

namespace Thg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}

section Ring

variable (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)

def fn (R : Type) [CommRing R] : R ≃+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

def torsSub (n : ℕ) : Subgroup (Over.mk x ⟶ t.G) where
  carrier := {a | a ^ n = 1 ∧ (n = 0 → a = 1)}
  one_mem' := ⟨one_pow n, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [mul_pow, ha.1, hb.1, _root_.mul_one], fun h => by rw [ha.2 h, hb.2 h, _root_.mul_one]⟩
  inv_mem' := fun {a} ha => ⟨by rw [inv_pow, ha.1, inv_one], fun h => by rw [ha.2 h, inv_one]⟩

theorem mem_torsSub {n : ℕ} (hn : n ≠ 0) (a : Over.mk x ⟶ t.G) : a ∈ torsSub t x n ↔ a ^ n = 1 :=
  ⟨fun h => h.1, fun h => ⟨h, fun e => absurd e hn⟩⟩

abbrev Tors (n : ℕ) : Type := Additive (torsSub t x n)

def thSub (n : ℕ) : Subgroup (ThetaGrp t.G t.PP.L n (Over.mk x)) := (torsSub t x n).comap (ptHom (n : ℤ) (Over.mk x) t.PP)

theorem mem_thSub {n : ℕ} (θ : ThetaGrp t.G t.PP.L n (Over.mk x)) : θ ∈ thSub t x n ↔ θ.pt ∈ torsSub t x n := Iff.rfl

def ovr (n : ℕ) : thSub t x n →* Multiplicative (Tors t x n) :=
  MonoidHom.mk' (fun θ => Multiplicative.ofAdd (Additive.ofMul ⟨θ.1.pt, θ.2⟩)) fun a b => Subtype.ext (pt_mul a.1 b.1)

theorem ovr_surjective [IsLocalRing R] (n : ℕ) : Function.Surjective (ovr t x n) := fun a => by
  obtain ⟨θ, h⟩ := exists_lift t.cub x a.toAdd.toMul.2.1
  exact ⟨⟨θ, (mem_thSub t x θ).2 (h ▸ a.toAdd.toMul.2)⟩, Subtype.ext h⟩

def scal (n : ℕ) : Rˣ →* thSub t x n :=
  ((scalar (n : ℤ) (Over.mk x) t.PP).comp (Units.map (fn R).toMonoidHom)).codRestrict _ fun a =>
    (mem_thSub t x _).2 (by rw [MonoidHom.comp_apply, pt_scalar]; exact (torsSub t x n).one_mem)

theorem scal_injective (n : ℕ) : Function.Injective (scal t x n) := fun _ _ h =>
  Units.map_injective (f := (fn R).toMonoidHom) (fn R).injective
    (scalar_injective (k := (n : ℤ)) (T := Over.mk x) (L := t.PP) (congrArg (fun q : thSub t x n => q.1) h))

theorem scal_comm (n : ℕ) (a : Rˣ) (g : thSub t x n) : scal t x n a * g = g * scal t x n a :=
  Subtype.ext (scalar_comm _ _)

abbrev ConstFn : Prop := Function.Surjective (fst (Over.mk x) t.G).left.appTop.hom

def Sec (k : ℤ) : Type := SecM t.G t.PP.L k (Over.mk x)

instance (k : ℤ) : AddCommGroup (Sec t x k) := inferInstanceAs (AddCommGroup (SecM t.G t.PP.L k (Over.mk x)))

instance (k : ℤ) : Module R (Sec t x k) :=
  Module.compHom (SecM t.G t.PP.L k (Over.mk x)) (show R →+* Γ((Over.mk x).left, ⊤) from (fn R).toRingHom)

variable {t x}

def Sec.toM {k : ℤ} (s : Sec t x k) : SecM t.G t.PP.L k (Over.mk x) := s

def Sec.toSec {k : ℤ} (s : Sec t x k) : LB.Sec (LPow t.G t.PP.L k (Over.mk x)) := SecM.toSec t.G s.toM

def Sec.ofSec {k : ℤ} (s : LB.Sec (LPow t.G t.PP.L k (Over.mk x))) : Sec t x k := SecM.ofSec t.G s

def Sec.lin {k k' : ℤ} (f : SecM t.G t.PP.L k (Over.mk x) →ₗ[Γ((Over.mk x).left, ⊤)] SecM t.G t.PP.L k' (Over.mk x)) :
    Sec t x k →ₗ[R] Sec t x k' where
  toFun := f
  map_add' := f.map_add
  map_smul' c s := f.map_smul (show Γ((Over.mk x).left, ⊤) from fn R c) s

def ptMap {R' : Type} [CommRing R'] (f : R →+* R') {x' : Sp R' ⟶ X} (h : spMap f ≫ x = x') : Over.mk x' ⟶ Over.mk x :=
  Over.homMk (spMap f) h

def Sec.pull {R' : Type} [CommRing R'] (f : R →+* R') {x' : Sp R' ⟶ X} (h : spMap f ≫ x = x') (k : ℤ) :
    Sec t x k →ₛₗ[f] Sec t x' k where
  toFun := VVRank.pullM t.G t.PP.L k (ptMap f h)
  map_add' := map_add _
  map_smul' c s := ((VVRank.pullM t.G t.PP.L k (ptMap f h)).map_smulₛₗ (show Γ((Over.mk x).left, ⊤) from fn R c) s).trans
    (congrArg (fun a : Γ((Over.mk x').left, ⊤) => a • VVRank.pullM t.G t.PP.L k (ptMap f h) s)
      (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm)

def Sec.IsBasis {k : ℤ} (θ : Sec t x k) : Prop := ∀ s : Sec t x k, ∃! c : R, s = c • θ

theorem Sec.IsBasis.exists_unit {k : ℤ} {θ θ' : Sec t x k} (h : θ.IsBasis) (h' : θ'.IsBasis) : ∃ u : Rˣ, θ' = u • θ := by
  obtain ⟨a, ha, -⟩ := h θ'
  obtain ⟨b, hb, -⟩ := h' θ
  have e : b * a = 1 := (h θ).unique (by rw [mul_smul, ← ha, ← hb]) (one_smul _ _).symm
  exact ⟨⟨a, b, by rw [mul_comm, e], e⟩, ha⟩

theorem Sec.IsBasis.ne_zero [Nontrivial R] {k : ℤ} {θ : Sec t x k} (h : θ.IsBasis) : θ ≠ 0 := fun e =>
  zero_ne_one ((h θ).unique (by rw [zero_smul, e]) (one_smul _ _).symm)

variable (t x)

open Classical in

def gen : Sec t x ((1 : ℕ) : ℤ) := if h : ∃ θ : Sec t x ((1 : ℕ) : ℤ), θ.IsBasis then h.choose else 0

def act (n : ℕ) : thSub t x n →* Module.End R (Sec t x n) where
  toFun θ := Sec.lin (action (n : ℤ) (Over.mk x) t.PP θ.1)
  map_one' := LinearMap.ext fun s => DFunLike.congr_fun (map_one (action (n : ℤ) (Over.mk x) t.PP)) s
  map_mul' a b := LinearMap.ext fun s => DFunLike.congr_fun (map_mul (action (n : ℤ) (Over.mk x) t.PP) a.1 b.1) s

theorem act_scal (n : ℕ) (a : Rˣ) (s : Sec t x n) : act t x n (scal t x n a) s = (a : R) • s := action_scalar _ s

variable {t x}

theorem ovr_eq_one_iff (hp : ConstFn t x) (n : ℕ) (g : thSub t x n) : ovr t x n g = 1 ↔ ∃ a, scal t x n a = g := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := exists_scalar_eq hp (θ := g.1) (congrArg (fun q => q.toAdd.toMul.1) h)
    refine ⟨Units.map (fn R).symm.toMonoidHom c, Subtype.ext (Eq.trans (congrArg (scalar (n : ℤ) (Over.mk x) t.PP) ?_) hc)⟩
    exact Units.ext ((fn R).apply_symm_apply _)
  · rintro ⟨a, rfl⟩
    exact Subtype.ext (pt_scalar _)

def dl (hp : ConstFn t x) (n : ℕ) : thSub t x n ≃* thSub t x n :=
  have m : ∀ θ : thSub t x n, delta t.sym hp θ.1 ∈ thSub t x n := fun θ =>
    (mem_thSub t x _).2 (by rw [pt_delta]; exact (torsSub t x n).inv_mem θ.2)
  { toFun := fun θ => ⟨_, m θ⟩
    invFun := fun θ => ⟨_, m θ⟩
    left_inv := fun _ => Subtype.ext (delta_delta _ _ _)
    right_inv := fun _ => Subtype.ext (delta_delta _ _ _)
    map_mul' := fun _ _ => Subtype.ext (map_mul (delta t.sym hp) _ _) }

variable (t)

theorem exists_normGen {α : 𝓞 E} {n : ℕ} (h : α * H.bar α = n) :
    ∃ u : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![𝟙 t.G.left, (t.act.act α).left] ![(n : ℤ), -((1 : ℕ) : ℤ)]),
      u.IsGen ∧ PullbackSections.IsNormEnd t.G t.PP (t.act.act α) n ((1 : ℕ) : ℤ) u := by
  letI := H.starRing
  have := t.act.hom α
  have g := PullGenG.hasGen_pull t.PP t.cub t.act.toRingAct H.w0 α n h (t.adj α) t.prim 1
  rw [Nat.one_mul] at g
  obtain ⟨β, hβ⟩ := g.gen t.PP.isLB (K' := Fin 2) ![𝟙 t.G.left, (t.act.act α).left] ![(n : ℤ), -((1 : ℕ) : ℤ)] rfl
  exact TransPullCompare.exists_norm_gen _ _ _ β hβ

variable (x)

def pb {α : 𝓞 E} {n : ℕ} (h : α * H.bar α = n) : Sec t x ((1 : ℕ) : ℤ) →ₗ[R] Sec t x n :=
  Sec.lin (endPull _ (exists_normGen t h).choose_spec.1 (Over.mk x))

variable {t x}

end Ring

section Fibre

variable (t : SAB H X) {Z : Scheme.{0}} (x : Z ⟶ X)

structure AbFibre (g : ℕ) : Prop where
  proper : IsProper (pullback.snd t.G.hom x)
  dim : SmoothOfRelativeDimension g (pullback.snd t.G.hom x)

variable {t x} {g : ℕ}

theorem abFibre_iff {B : Scheme.{0}} {φ : B ⟶ t.G.left} {q : B ⟶ Z} (h : IsPullback φ q t.G.hom x) :
    AbFibre t x g ↔ IsProper q ∧ SmoothOfRelativeDimension g q := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [← h.isoPullback_hom_snd]
    exact ⟨inferInstance, by simpa using (inferInstance : SmoothOfRelativeDimension (0 + g)
      (h.isoPullback.hom ≫ pullback.snd t.G.hom x))⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩ <;> rw [← h.isoPullback_inv_snd]
    · infer_instance
    · simpa using (inferInstance : SmoothOfRelativeDimension (0 + g) (h.isoPullback.inv ≫ q))

theorem AbFibre.tens (h : AbFibre t x g) (Λ : Unim E) : AbFibre (tens t Λ) x (Λ.n * g) := by
  obtain ⟨t', ⟨m⟩⟩ := exists_sab x t
  obtain ⟨h₁, h₂⟩ := (abFibre_iff m.cart.1).1 h
  exact (abFibre_iff (tens.map Λ m).cart.1).2 ⟨tens.isProper t' Λ, tens.smoothOfRelativeDimension t' Λ h₂⟩

theorem AbFibre.isAbelianScheme (h : AbFibre t x g) : IsAbelianScheme ((Over.pullback x).obj t.G) where
  comm := inferInstance
  smooth := by have := t.semi.smooth; show Smooth (pullback.snd _ _); infer_instance
  proper := h.proper
  geomConnected := by have := t.semi.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance

theorem AbFibre.constFn {R : Type} [CommRing R] {x : Sp R ⟶ X} (h : AbFibre t x g) : ConstFn t x := by
  have hb : Function.Surjective (pullback.snd t.G.hom x).appTop.hom :=
    (GlobalTheory.firstFiveLaws.1.globalFns _ _ h.isAbelianScheme).2
  have e : (fst (Over.mk x) t.G).left = (pullbackSymmetry x t.G.hom).hom ≫ pullback.snd t.G.hom x :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  have : IsIso (pullbackSymmetry x t.G.hom).hom.appTop := inferInstanceAs (IsIso ((pullbackSymmetry x t.G.hom).hom.app ⊤))
  rw [ConstFn, e]
  exact surj_comp (ConcreteCategory.bijective_of_isIso (pullbackSymmetry x t.G.hom).hom.appTop).2 hb

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {x : Sp K ⟶ X}

theorem AbFibre.card_tors (h : AbFibre t x g) {n : ℕ} (hn : n ≠ 0) : Nat.card (Tors t x n) = n ^ (2 * g) := by
  obtain ⟨e, -⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_pullback t.G x) (𝟙_ (Over (Sp K))) x (Category.id_comp _).symm
  refine Eq.trans (Nat.card_congr (Additive.toMul.trans (e.toEquiv.subtypeEquiv fun a => ?_).symm))
    (GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional K _ g n h.isAbelianScheme h.dim (Nat.cast_ne_zero.2 hn))
  rw [mem_torsSub t x hn, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]

theorem AbFibre.finite_tors (h : AbFibre t x g) (n : ℕ) : Finite (Tors t x n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (Tors t x 0) := ⟨fun a b => Subtype.ext ((a.toMul.2.2 rfl).trans (b.toMul.2.2 rfl).symm)⟩
    infer_instance
  · exact Nat.finite_of_card_ne_zero (by rw [h.card_tors hn]; exact pow_ne_zero _ hn)

end Fibre

section Data

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P)

def ptO : Sp ↥(intO ↥C.S) ⟶ Sp A.R := spMap A.f

def ptC : Sp ↥C.S ⟶ Sp A.R := spMap ((algebraMap ↥(intO ↥C.S) ↥C.S).comp A.f)

theorem gen_ptO : spMap (algebraMap ↥(intO ↥C.S) ↥C.S) ≫ ptO A = ptC A :=
  (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (algebraMap ↥(intO ↥C.S) ↥C.S))).symm

theorem ptO_ι : ptO A ≫ A.ι = P.yt := A.fac

theorem ptC_ι : ptC A ≫ A.ι = P.y ≫ Y.j := dat_fac A

theorem isGrpPullback_ptC : IsGrpPullback (abVar P).A A.t.G (ptC A) (abToDat A) := isGrpPullback_abToDat A

theorem abFibre_ptC : AbFibre A.t (ptC A) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) :=
  (abFibre_iff (isGrpPullback_ptC A).1).2 ⟨(abVar P).isAb.proper, (abVar P).smoothDim⟩

end Data

end Thg

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam

theorem exists_alp {D : D7} {p n : ℕ} (h : NHyp D p n) : ∃ α : 𝓞 D.host.E,
    (α : D.host.E) * D.host.conj (α : D.host.E) = (n : D.host.E) ∧
      ((∃ mm : ℕ, n = mm ^ 2 ∧ α = (mm : 𝓞 D.host.E)) ∨ (α : D.host.E) ∈ D.host.K) := by
  obtain ⟨-, -, ⟨m, rfl⟩ | ⟨π, h₁, h₂⟩⟩ := h
  · refine ⟨m, ?_, Or.inl ⟨m, rfl, rfl⟩⟩
    change algebraMap (𝓞 D.host.E) D.host.E m * D.host.conj (algebraMap (𝓞 D.host.E) D.host.E m) = _
    rw [map_natCast, map_natCast, Nat.cast_pow, sq]
  · exact ⟨π, h₂, Or.inr h₁⟩

open Classical in

def alpOf (D : D7) (p n : ℕ) : 𝓞 D.host.E := if h : NHyp D p n then (exists_alp h).choose else 0

theorem alpOf_spec {D : D7} {p n : ℕ} (h : NHyp D p n) :
    (alpOf D p n : D.host.E) * D.host.conj (alpOf D p n : D.host.E) = (n : D.host.E) ∧
      ((∃ mm : ℕ, n = mm ^ 2 ∧ alpOf D p n = (mm : 𝓞 D.host.E)) ∨ (alpOf D p n : D.host.E) ∈ D.host.K) := by
  rw [alpOf, dif_pos h]
  exact (exists_alp h).choose_spec

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem alpOf_mul_bar (A : Amb D) {n : ℕ} (h : NHyp D p n) : alpOf D p n * A.H.bar (alpOf D p n) = n :=
  RingOfIntegers.ext (by
    have e := (alpOf_spec h).1
    rw [← complexConj_eq_conj, ← A.H.bar_eq] at e
    exact (map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (e.trans (map_natCast _ n).symm))

namespace At

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z) (Λ : Unim D.host.E)

abbrev tensAt : SAB A.H (Sp (ct.dat y).R) := tens (ct.dat y).t Λ

abbrev ptC : Sp ↥y.C.S ⟶ Sp (ct.dat y).R := Thg.ptC (ct.dat y)

abbrev ptO : Sp ↥(intO ↥y.C.S) ⟶ Sp (ct.dat y).R := Thg.ptO (ct.dat y)

theorem abFibre_tensAt : Thg.AbFibre (ct.tensAt y Λ) (ct.ptC y) (D.R.f * N * Λ.n) := by
  have h := (Thg.abFibre_ptC (ct.dat y)).tens Λ
  rwa [S.rank_eq, finrank_host_eq, Nat.mul_div_cancel_left _ two_pos, mul_comm] at h

abbrev SecC (n : ℕ) : Type := Thg.Sec (ct.tensAt y Λ) (ct.ptC y) n

abbrev SecO (n : ℕ) : Type := Thg.Sec (ct.tensAt y Λ) (ct.ptO y) n

def secGen (n : ℕ) : ct.SecO y Λ n →ₛₗ[algebraMap ↥(intO ↥y.C.S) ↥y.C.S] ct.SecC y Λ n :=
  Thg.Sec.pull _ (Thg.gen_ptO (ct.dat y)) n

def thetaO : ct.SecO y Λ 1 := Thg.gen (ct.tensAt y Λ) (ct.ptO y)

def thetaC : ct.SecC y Λ 1 := ct.secGen y Λ 1 (ct.thetaO y Λ)

open Classical in

def pbAlp (n : ℕ) : ct.SecC y Λ 1 →ₗ[↥y.C.S] ct.SecC y Λ n :=
  if h : NHyp D p n then Thg.pb (ct.tensAt y Λ) (ct.ptC y) (alpOf_mul_bar A h) else 0

end At

def thgTrue (ct : At S κ p) : ThgSt ct (uniTrue ct) where
  Tors y Λ n := Thg.Tors (ct.tensAt y Λ) (ct.ptC y) n
  atAdd _ _ _ := inferInstance
  atFin y Λ n := @Fintype.ofFinite _ ((ct.abFibre_tensAt y Λ).finite_tors n)
  at_tors _ _ _ a := Subtype.ext a.toMul.2.1
  at_card y nW _ hn := (@Nat.card_eq_fintype_card _ (_)).symm.trans ((ct.abFibre_tensAt y (Unim.std _ nW)).card_tors hn.ne')
  Th y Λ n := Thg.thSub (ct.tensAt y Λ) (ct.ptC y) n
  thGrp _ _ _ := inferInstance
  ovr y Λ n := Thg.ovr (ct.tensAt y Λ) (ct.ptC y) n
  ovr_surj y Λ n := Thg.ovr_surjective (ct.tensAt y Λ) (ct.ptC y) n
  scal y Λ n := Thg.scal (ct.tensAt y Λ) (ct.ptC y) n
  scal_inj y Λ n := Thg.scal_injective (ct.tensAt y Λ) (ct.ptC y) n
  scal_central y Λ n := Thg.scal_comm (ct.tensAt y Λ) (ct.ptC y) n
  ker_ovr y Λ n := Thg.ovr_eq_one_iff (ct.abFibre_tensAt y Λ).constFn n
  dl y Λ n := Thg.dl (ct.abFibre_tensAt y Λ).constFn n
  dl_ovr y Λ _ g := Subtype.ext (pt_delta (ct.tensAt y Λ).sym (ct.abFibre_tensAt y Λ).constFn g.1)
  dl_scal y Λ _ _ := Subtype.ext (delta_scalar (ct.tensAt y Λ).sym (ct.abFibre_tensAt y Λ).constFn _)
  dl_dl y Λ _ g := Subtype.ext (delta_delta (ct.tensAt y Λ).sym (ct.abFibre_tensAt y Λ).constFn g.1)
  Sn y Λ n := ct.SecC y Λ n
  snAdd _ _ _ := inferInstance
  snMod y Λ n := (inferInstance : Module ↥y.C.S (ct.SecC y Λ n))
  act y Λ n := Thg.act (ct.tensAt y Λ) (ct.ptC y) n
  act_scal y Λ n := Thg.act_scal (ct.tensAt y Λ) (ct.ptC y) n
  vth y Λ n := ct.pbAlp y Λ n (ct.thetaC y Λ)
  alp := alpOf D p
  alp_spec _ := alpOf_spec
  th1 y nW := ct.thetaC y (Unim.std _ nW)
  pbAl y nW n := ct.pbAlp y (Unim.std _ nW) n
  vth_def _ _ _ _ := rfl

namespace Thg

variable (ct : At S κ p) (y : ct.Pt ct.Xm) (Λ : (uniTrue ct).Unim)

theorem card_Tors {n : ℕ} (hn : 0 < n) : Nat.card ((thgTrue ct).Tors y Λ n) = n ^ (2 * (D.R.f * N * Unim.n Λ)) :=
  (ct.abFibre_tensAt y Λ).card_tors hn.ne'

example (g : (thgTrue ct).Th y Λ 1) : ∃ a, (thgTrue ct).scal y Λ 1 a = g :=
  ((thgTrue ct).ker_ovr y Λ 1 g).1 (Subtype.ext ((pow_one _).symm.trans (Subtype.property g).1))

example : Nat.card ((thgTrue ct).Tors y (Unim.std _ 1) 3) = 3 ^ (2 * (D.R.f * N)) :=
  (card_Tors ct y _ three_pos).trans (by rw [show (Unim.std D.host.E 1).n = 1 from rfl, Nat.mul_one])

example (n : ℕ) (s : (thgTrue ct).Sn y Λ n) : (thgTrue ct).scal y Λ n (-1) ≠ 1 ∧
    (thgTrue ct).dl y Λ n ((thgTrue ct).scal y Λ n (-1)) = (thgTrue ct).scal y Λ n (-1) ∧
    (thgTrue ct).act y Λ n ((thgTrue ct).scal y Λ n (-1)) s = -s := by
  refine ⟨fun h => ?_, (thgTrue ct).dl_scal y Λ n _, ?_⟩
  · have e := congrArg Units.val ((thgTrue ct).scal_inj y Λ n (h.trans (map_one _).symm))
    norm_num at e
  · rw [(thgTrue ct).act_scal, Units.val_neg, Units.val_one, neg_one_smul]

example (D : D7) (p : ℕ) : (alpOf D p 1 : D.host.E) * D.host.conj (alpOf D p 1 : D.host.E) = 1 :=
  (alpOf_spec ⟨odd_one, Nat.coprime_one_left p, Or.inl ⟨1, rfl⟩⟩).1.trans Nat.cast_one

end Thg

end Record

end GlobalTheory.LocM
end
end
