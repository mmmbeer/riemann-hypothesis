import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointMemAbLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOfAbSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingOfMinimal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTowerHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCocycleHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameMoveHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameOfFlagAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FibLatPreSubSpanSubLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

namespace Cht

open FamPf

theorem exists_fam : FamSt := by
  intro D A N j S κ p ct Z C y K w hw
  have hE : ExtendSt := extendSt
  have hF : FlagBaseSt := FlagBase.flagBase
  have hM : FrameMoveSt := frameMove
  have hC : CocycleSt := Cocycle.cocycle
  have hT : TowerSt := Tower.tower
  have hN : N2 ct.Y := (S.sys.clauses p ct.W ct.hp ct.hW).1
  have h1 : 1 ≤ S.Dw.p + S.Dw.q := by
    rw [S.rank_eq]; exact one_le_two.trans S.two_le
  obtain ⟨P, hP1, hP⟩ := hT _ _ _ _ _ _ ct.Y ct.hp ct.hW h1 C Z.i y.P
  have hyg : y.gen ≫ Z.π = (P Z.i).x0 := by
    have e : (P Z.i).x0 = spMap (intO ↥C.S).subtype ≫ (P Z.i).yt := (P Z.i).ext.symm
    rw [e, hP1, ← y.z_π, PtAt.gen, Category.assoc]
  have hr : Set.range w ⊆ Z.opn := by
    refine range_of_base K.subtype _ ?_
    rw [hw]
    rintro _ ⟨s, rfl⟩
    refine ⟨(P Z.i).y s, ?_⟩
    exact (congrArg (fun f => f s) hyg).symm
  obtain ⟨u₁, hu₁⟩ := ((hF _ _ _ _ _ _ ct.Y _ Z ↥K w).1 hr)
  have hu : Z.FlagAt y.gen (u₁.bc K.subtype) := by
    rw [← hw]
    exact (hF _ _ _ _ _ _ ct.Y _ Z ↥K w).2 ↥C.S K.subtype _ hu₁
  obtain ⟨fam, hfam, hall⟩ := fam_core hE hM hC hN P hP Z y hP1.symm _ hu
  refine ⟨fam, hfam, ?_⟩
  have hi : ct.YY.i = idx0 ct := ct.isYY.1.trans (ct.B.lvl none)
  have hd : ct.YY.i.l.Dvd Z.i.l := hi ▸ Z.dvd
  have hc : ct.YY.i.c.F ≤ Z.i.c.F := hi ▸ Z.le
  obtain ⟨mu, ht⟩ := exists_isTrans hN ct.YY.i Z.i hd hc
  obtain ⟨hg, hf⟩ := hall ct.YY _ mu hd ht
  exact rat_core hE hF hM K Z ct.YY hc ht (P Z.i) (P ct.YY.i) (hP _ _ _ _ hd ht) w (by rw [hw]; exact hyg) u₁ hu₁ _ hg hf

end Cht

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem Cht.goodIff (ct : At S κ p) : Cht.GoodIff ct := Cht.goodIff_of Cht.GoodOfZero.abOfTriv Cht.trivOfAbSt ct

theorem Cht.genEx (ct : At S κ p) : Cht.GenEx ct :=
  Cht.genEx_of GlobalTheory.SpecialStalk.stalkSt Cht.CompletedClosure.fieldSt Cht.extendSt Cht.exists_fam ct

def chtTrue (ct : At S κ p) : ChtSt ct := Cht.chtOf ct (Cht.goodIff ct) (Cht.genEx ct)




example {ct : At S κ p} {y : Cht.DVP ct} (e : Cht.Ext y) (h : e.π = p) : Cht.vpi e = 1 := by
  have h1 : ((e.π : ↥e.L) : ↥y.C.S) = p := by rw [h]; simp
  have hp : (1 : ℝ) < p := by exact_mod_cast ct.hp.one_lt
  rw [Cht.vpi, h1, y.C.norm_p, Real.logb_inv, neg_neg, Real.logb_self_eq_one hp]

example {ct : At S κ p} {y : Cht.DVP ct} {e : Cht.Ext y} {Z : ct.Mdl} (χ : Cht.Chart Z y e) (F : ct.Sh Z)
    (f : ct.Sec F) : Cht.ordGe χ F f 0 :=
  fun _ _ _ _ _ _ _ n hn => absurd hn (not_lt.2 n.cast_nonneg)

example {ct : At S κ p} {y : Cht.DVP ct} {e : Cht.Ext y} {Z : ct.Mdl} (χ : Cht.Chart Z y e) (h : Cht.chAt χ)
    (h' : Cht.chAbExact χ) : 0 < Cht.dvRho y := by
  rw [Cht.dvRho_pos_iff (Cht.goodIff ct) Z, ← Cht.chAt_imgM χ h]
  intro hab
  refine (h' (closedPoint e.R)).1 hab ?_
  change PowerSeries.X ∈ maximalIdeal e.R
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

end GlobalTheory.LocM
end
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Algebra

variable (R : Type) [CommRing R] [IsDomain R]

abbrev intUnits : Subgroup (FractionRing R)ˣ := (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev Cls : Type := (FractionRing R)ˣ ⧸ intUnits R

variable {R}

def toK (r : R) (h : r ≠ 0) : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R _ r) ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h)

theorem cls_eq_iff {x y : (FractionRing R)ˣ} : (x : Cls R) = y ↔
    ∃ u : Rˣ, (x : FractionRing R) * algebraMap R _ (u : R) = y := by
  rw [show ((x : Cls R) = y) ↔ QuotientGroup.mk' (intUnits R) x = QuotientGroup.mk' (intUnits R) y from Iff.rfl,
    QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, h⟩
    exact ⟨u, congrArg Units.val h⟩
  · rintro ⟨u, h⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext h⟩

theorem cls_pow_eq_one [IsIntegrallyClosed R] {n : ℕ} (hn : n ≠ 0) (c : Cls R) (h : c ^ n = 1) : c = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have h' : x ^ n ∈ intUnits R := (QuotientGroup.eq_one_iff _).1 ((QuotientGroup.mk_pow _ _ _).trans h)
  obtain ⟨u, hu⟩ := h'
  have key : ∀ (y : (FractionRing R)ˣ) (v : Rˣ), Units.map (algebraMap R (FractionRing R)).toMonoidHom v = y ^ n →
      ∃ a : R, algebraMap R _ a = (y : FractionRing R) := fun y v hv => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_)
    have := congrArg Units.val hv
    rw [Units.val_pow_eq_pow_val] at this
    rw [← this]
    exact isIntegral_algebraMap
  obtain ⟨a, ha⟩ := key x u hu
  obtain ⟨b, hb⟩ := key x⁻¹ u⁻¹ (by rw [map_inv, hu, inv_pow])
  have hab : a * b = 1 := IsFractionRing.injective R (FractionRing R) (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact (QuotientGroup.eq_one_iff _).2 ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

instance [IsIntegrallyClosed R] : IsMulTorsionFree (Cls R) where
  pow_left_injective n hn a b h := by
    have : (a * b⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, show a ^ n = b ^ n from h, mul_inv_cancel]
    exact mul_inv_eq_one.1 (cls_pow_eq_one hn _ this)

theorem exists_lift [IsIntegrallyClosed R] {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (b : X → X → Cls R)
    (h₁ : ∀ a a' c, b (a + a') c = b a c * b a' c) (h₂ : ∀ a c, b a c = b c a) :
    ∃ t : X → X → (FractionRing R)ˣ, (∀ a c, (t a c : Cls R) = b a c) ∧ (∀ a a' c, t (a + a') c = t a c * t a' c) ∧
      ∀ a c a' c', b a c = b a' c' → t a c = t a' c' := by
  let B₀ : X →+ X →+ Additive (Cls R) := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun c => Additive.ofMul (b a c))
    (fun c c' => by rw [h₂, h₁, h₂ c, h₂ c']; rfl)) (fun a a' => AddMonoidHom.ext fun c => by
      show Additive.ofMul (b (a + a') c) = Additive.ofMul (b a c) + Additive.ofMul (b a' c)
      rw [h₁]; rfl)
  let B : TensorProduct ℤ X X →ₗ[ℤ] Additive (Cls R) := TensorProduct.lift
    ((AddMonoidHom.toIntLinearMap ((addMonoidHomLequivInt ℤ).toAddEquiv.toAddMonoidHom.comp B₀)))
  have hB : ∀ a c, B (a ⊗ₜ c) = Additive.ofMul (b a c) := fun a c => rfl
  let q : Additive (FractionRing R)ˣ →ₗ[ℤ] Additive (Cls R) :=
    (MonoidHom.toAdditive (QuotientGroup.mk' (intUnits R))).toIntLinearMap
  have hq : Function.Surjective q := fun c => QuotientGroup.mk_surjective (Additive.toMul c)
  have : Module.Finite ℤ (TensorProduct ℤ X X) := Module.Finite.tensorProduct ℤ X X
  have : Module.Finite ℤ (LinearMap.range B) := Module.Finite.range B
  have : Module.Free ℤ (LinearMap.range B) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.range B).subtype hq
  refine ⟨fun a c => Additive.toMul (s (B.rangeRestrict (a ⊗ₜ c))), fun a c => ?_, fun a a' c => ?_, fun a c a' c' h => ?_⟩
  · exact congrArg Additive.toMul (LinearMap.congr_fun hs (B.rangeRestrict (a ⊗ₜ c)))
  · beta_reduce
    rw [TensorProduct.add_tmul, map_add, map_add]; rfl
  · have : B.rangeRestrict (a ⊗ₜ c) = B.rangeRestrict (a' ⊗ₜ c') := Subtype.ext (by
      show B _ = B _
      rw [hB, hB, h])
    simp only [this]

end Algebra

section Coord

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

open GlobalTheory.BetaAdd in

theorem coord_rel (Dg : DegData R (maximalIdeal R)) (r : Dg.toPre.X → R) (hr : ∀ χ, PsiCoord Dg.toPre χ (r χ)) :
    (∀ a a' b, ∃ u : Rˣ, r (a + a' + b) * r a * r a' * r b * u = r (a + b) * r (a' + b) * r (a + a')) ∧
      ∀ a, ∃ u : Rˣ, r (-a) * u = r a := by
  set D := Dg.toPre with hD
  let z : (TK R).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ, hI⟩ := exists_good_int D z
  choose u hu hur using fun χ => coord_val hI hJ (hr χ)
  let Q := QuotientGroup.mk' (intU z)
  have hQ : ∀ w ∈ intU z, Q w = 1 := fun w hw => (QuotientGroup.eq_one_iff w).2 hw
  let P : D.X → _ := fun χ => Q (val (D.psi χ) (𝟙 _) z J)
  have hP : ∀ χ, Q (u χ * val (D.psi χ) (𝟙 _) z J) = P χ := fun χ => by rw [map_mul, hQ _ (hu χ), _root_.one_mul]
  have fin : ∀ {x y : R} {X Y : ((TK R).left.presheaf.stalk z)ˣ}, toGen z x = X.val → toGen z y = Y.val →
      Q X = Q Y → ∃ v : Rˣ, x * v = y := fun {x y X Y} hX hY h => by
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (QuotientGroup.mk'_eq_mk' (intU z)).1 h
    exact ⟨v, toGen_injective z (by rw [map_mul, hX, hY, ← hv]; rfl)⟩
  have vρ : Q (val D.rigK (𝟙 _) z J) = 1 := by
    refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.rig (𝟙 _) (fun _ => ?_) _ ?_))
    · rw [Category.id_comp]; exact Over.w η[D.P.A]
    · rw [Category.id_comp, Category.comp_id]; rfl
  have vτ : ∀ a b : D.X, Q (val (D.tau a b) (𝟙 _) z J) = P (a + b) * (P a)⁻¹ * (P b)⁻¹ := fun a b => by
    refine (congrArg Q ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _)))).trans ?_
    simp only [map_mul, map_inv]
    erw [vρ]
    rw [inv_one, _root_.mul_one]
  refine ⟨fun a a' b => ?_, fun a => ?_⟩
  · have e := congrArg Q ((val_mul hJ _ _ _).symm.trans ((val_corr hJ (Dg.tau_bimult a a' b) (𝟙 _)).trans
      (val_mul hJ _ _ _)))
    have vc : Q (val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J) = 1 := by
      refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.cub.t
        (lift (D.c a) (lift (D.c a') (D.c b))).left (fun _ => over_sec _ _) _ ?_))
      simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
    rw [map_mul, map_mul, vc, vτ, vτ, vτ] at e
    refine fin
      (X := u (a + a' + b) * val (D.psi (a + a' + b)) (𝟙 _) z J * (u a * val (D.psi a) (𝟙 _) z J) *
        (u a' * val (D.psi a') (𝟙 _) z J) * (u b * val (D.psi b) (𝟙 _) z J))
      (Y := u (a + b) * val (D.psi (a + b)) (𝟙 _) z J * (u (a' + b) * val (D.psi (a' + b)) (𝟙 _) z J) *
        (u (a + a') * val (D.psi (a + a')) (𝟙 _) z J)) ?_ ?_ ?_
    · simp only [map_mul, hur, Units.val_mul]
    · simp only [map_mul, hur, Units.val_mul]
    · rw [map_mul Q, map_mul Q, map_mul Q, hP, hP, hP, hP, map_mul Q, map_mul Q, hP, hP, hP]
      have E := congrArg Additive.ofMul e
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at E ⊢
      rw [← sub_eq_zero] at E ⊢
      refine Eq.trans ?_ E
      abel
  · have e := congrArg Q ((val_mul hJ _ _ _).symm.trans (val_corr hJ (Dg.psi_even a) (𝟙 _)))
    have vs : Q (val (LB.pullGen D.P.L _ _ D.sym (D.xK a)) (𝟙 _) z J) = 1 := by
      refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.sym (D.c a).left (fun k => ?_) _ ?_))
      · fin_cases k
        · exact over_sec _ _
        · exact over_sec (D.c a) (𝟙 _)
      · simp [ptK]
    rw [map_mul, vs, _root_.mul_one] at e
    exact fin (hur (-a)) (hur a) ((hP _).trans (e.trans (hP _).symm))

variable (Dg : DegData R (maximalIdeal R))

def coord (χ : Dg.toPre.X) : R := (GlobalTheory.BetaAdd.exists_coord Dg χ).choose

theorem coord_spec (χ : Dg.toPre.X) : PsiCoord Dg.toPre χ (coord Dg χ) := (GlobalTheory.BetaAdd.exists_coord Dg χ).choose_spec

theorem coord_ne (χ : Dg.toPre.X) : coord Dg χ ≠ 0 := GlobalTheory.PsiCoordLocal.ne_zero_of_coord (coord_spec Dg χ)

def psiCls (χ : Dg.toPre.X) : Cls R := (toK (coord Dg χ) (coord_ne Dg χ) : (FractionRing R)ˣ)

def tauCls (a b : Dg.toPre.X) : Cls R := psiCls Dg (a + b) * (psiCls Dg a)⁻¹ * (psiCls Dg b)⁻¹

omit [IsLocalRing R] in
theorem toK_cls_eq {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (h : ∃ u : Rˣ, x * u = y) : (toK x hx : Cls R) = toK y hy := by
  obtain ⟨u, rfl⟩ := h
  exact cls_eq_iff.2 ⟨u, (map_mul _ _ _).symm⟩

omit [IsLocalRing R] in
theorem toK_mul {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) : toK (x * y) (mul_ne_zero hx hy) = toK x hx * toK y hy :=
  Units.ext (map_mul _ _ _)

theorem psiCls_eq {χ : Dg.toPre.X} {r : R} (hr : PsiCoord Dg.toPre χ r) :
    psiCls Dg χ = toK r (GlobalTheory.PsiCoordLocal.ne_zero_of_coord hr) := by
  obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord (coord_spec Dg χ) hr
  exact toK_cls_eq _ _ ⟨u, by rw [hu, mul_comm]⟩

theorem tauCls_symm (a b : Dg.toPre.X) : tauCls Dg a b = tauCls Dg b a := by
  rw [tauCls, tauCls, add_comm a b, mul_right_comm]

theorem tauCls_add (a a' b : Dg.toPre.X) : tauCls Dg (a + a') b = tauCls Dg a b * tauCls Dg a' b := by
  have n := coord_ne Dg
  have h := toK_cls_eq (mul_ne_zero (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) (n _))
    (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) ((coord_rel Dg _ (coord_spec Dg)).1 a a' b)
  rw [toK_mul (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) (n _), toK_mul (mul_ne_zero (n _) (n _)) (n _),
    toK_mul (n _) (n _), toK_mul (mul_ne_zero (n _) (n _)) (n _), toK_mul (n _) (n _)] at h
  have h' : psiCls Dg (a + a' + b) * psiCls Dg a * psiCls Dg a' * psiCls Dg b =
    psiCls Dg (a + b) * psiCls Dg (a' + b) * psiCls Dg (a + a') := h
  have E := congrArg Additive.ofMul h'
  apply Additive.ofMul.injective
  simp only [tauCls, ofMul_mul, ofMul_inv] at E ⊢
  rw [← sub_eq_zero] at E ⊢
  refine Eq.trans ?_ E
  abel

theorem psiCls_neg (a : Dg.toPre.X) : psiCls Dg (-a) = psiCls Dg a :=
  toK_cls_eq _ _ ((coord_rel Dg _ (coord_spec Dg)).2 a)

theorem tauCls_self (a : Dg.toPre.X) : tauCls Dg a a = psiCls Dg a ^ 2 := by
  have h0 := congrArg Additive.ofMul (tauCls_add Dg 0 0 0)
  have h1 := congrArg Additive.ofMul (tauCls_add Dg a (-a) a)
  apply Additive.ofMul.injective
  simp only [tauCls, ofMul_mul, ofMul_inv, add_zero, zero_add, add_neg_cancel, neg_add_cancel, psiCls_neg, ofMul_pow] at h0 h1 ⊢
  rw [← sub_eq_zero] at h0 h1 ⊢
  have : ∀ {x y z : Additive (Cls R)}, x = 0 → y = 0 → z = -y - x - x → z = 0 := fun hx hy hz => by rw [hz, hx, hy]; simp
  refine this h0 h1 ?_
  rw [two_nsmul]
  abel

theorem tauCls_bal {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] (ρ : Dg.toPre.OAct O) (x : O) (a b : Dg.toPre.X) :
    tauCls Dg (x • a) b = tauCls Dg a (star x • b) := by
  have n := coord_ne Dg
  have s := coord_spec Dg
  obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance Dg.toPre ρ x a b (s _) (s _) (s _) (s _) (s _) (s _)
  have h := toK_cls_eq (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _))
    (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) ⟨u, (mul_comm _ _).trans hu⟩
  rw [toK_mul (mul_ne_zero (n _) (n _)) (n _), toK_mul (n _) (n _), toK_mul (mul_ne_zero (n _) (n _)) (n _),
    toK_mul (n _) (n _)] at h
  have h' : psiCls Dg (x • a + b) * psiCls Dg a * psiCls Dg (star x • b) =
    psiCls Dg (a + star x • b) * psiCls Dg (x • a) * psiCls Dg b := h
  have E := congrArg Additive.ofMul h'
  apply Additive.ofMul.injective
  simp only [tauCls, ofMul_mul, ofMul_inv] at E ⊢
  rw [← sub_eq_zero] at E ⊢
  refine Eq.trans ?_ E
  abel

theorem tauCls_half [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] (ρ : Dg.toPre.OAct O)
    {w : O} (hw : w + star w = 1) (a : Dg.toPre.X) : tauCls Dg a (w • a) = psiCls Dg a := by
  refine pow_left_injective (n := 2) two_ne_zero ?_
  show _ ^ 2 = _ ^ 2
  rw [← tauCls_self, sq]
  nth_rewrite 2 [tauCls_symm]
  rw [tauCls_bal Dg ρ, tauCls_symm Dg a, tauCls_symm Dg a, ← tauCls_add, ← add_smul, hw, one_smul]

structure IsReading (O : Type) [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (t : Dg.toPre.X → Dg.toPre.X → (FractionRing R)ˣ) : Prop where
  add_left : ∀ a a' b, t (a + a') b = t a b * t a' b
  symm : ∀ a b, t a b = t b a
  bal : ∀ (x : O) a b, t (x • a) b = t a (star x • b)
  coord : ∀ a b ra rb rab, PsiCoord Dg.toPre a ra → PsiCoord Dg.toPre b rb → PsiCoord Dg.toPre (a + b) rab →
    ∃ u : Rˣ, (t a b : FractionRing R) * algebraMap R _ (ra * rb * u) = algebraMap R _ rab

theorem exists_reading [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (ρ : Dg.toPre.OAct O) : ∃ t, IsReading Dg O t := by
  obtain ⟨t, h₀, h₁, h₂⟩ := exists_lift (tauCls Dg) (tauCls_add Dg) (tauCls_symm Dg)
  refine ⟨t, h₁, fun a b => h₂ _ _ _ _ (tauCls_symm Dg a b), fun x a b => h₂ _ _ _ _ (tauCls_bal Dg ρ x a b),
    fun a b ra rb rab ha hb hab => ?_⟩
  have h := h₀ a b
  rw [tauCls, psiCls_eq Dg ha, psiCls_eq Dg hb, psiCls_eq Dg hab, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq] at h
  obtain ⟨u, hu⟩ := cls_eq_iff.1 (show ((t a b * toK rb _ * toK ra _ : (FractionRing R)ˣ) : Cls R) = toK rab _ from h)
  refine ⟨u, Eq.trans ?_ hu⟩
  simp only [map_mul, Units.val_mul, toK, Units.val_mk0]
  ring

variable {Dg}

theorem IsReading.cls {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] {t} (h : IsReading Dg O t) (a b : Dg.toPre.X) :
    (t a b : Cls R) = tauCls Dg a b := by
  obtain ⟨u, hu⟩ := h.coord a b _ _ _ (coord_spec Dg _) (coord_spec Dg _) (coord_spec Dg _)
  rw [tauCls, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq]
  refine (cls_eq_iff (x := t a b * toK _ (coord_ne Dg b) * toK _ (coord_ne Dg a)) (y := toK _ (coord_ne Dg (a + b)))).2 ⟨u, Eq.trans ?_ hu⟩
  simp only [map_mul, Units.val_mul, toK, Units.val_mk0]
  ring

omit [IsLocalRing R] in
theorem mem_range_of_cls {x : (FractionRing R)ˣ} {r : R} (hr : r ≠ 0) (h : (x : Cls R) = toK r hr) :
    (x : FractionRing R) ∈ (algebraMap R (FractionRing R)).range := by
  obtain ⟨u, hu⟩ := cls_eq_iff.1 h.symm
  exact ⟨r * u, (map_mul _ _ _).trans hu⟩

theorem IsReading.pos {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] {t} (h : IsReading Dg O t) (a : Dg.toPre.X) :
    (t a a : FractionRing R) ∈ (algebraMap R (FractionRing R)).range :=
  mem_range_of_cls (mul_ne_zero (coord_ne Dg a) (coord_ne Dg a)) (by
    rw [h.cls, tauCls_self, toK_mul (coord_ne Dg a) (coord_ne Dg a), sq]; rfl)

theorem IsReading.pos_max [CharZero R] [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] {t}
    (h : IsReading Dg O t) {a : Dg.toPre.X} (ha : a ≠ 0) :
    ∃ r ∈ maximalIdeal R, algebraMap R (FractionRing R) r = t a a := by
  obtain ⟨r, hr, h0, hm, -⟩ := (GlobalTheory.PsiCoordLocal.main R Dg inferInstance a).1
  have e : (t a a : Cls R) = toK (r * r) (mul_ne_zero h0 h0) := by
    rw [h.cls, tauCls_self, psiCls_eq Dg hr, toK_mul h0 h0, sq]; rfl
  obtain ⟨u, hu⟩ := cls_eq_iff.1 e.symm
  exact ⟨r * r * u, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hm ha)), (map_mul _ _ _).trans hu⟩

end Coord

end GlobalTheory.LocM.Bdy
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Transl

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def FERel (mu α : D.X) (s : SecFMod D (FractionRing R) 1 α) (t : SecFMod D (FractionRing R) 1 (α + 1 • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) 1 α mu) (DegPre.deltaε 1)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
      (DegPre.famMult D (FractionRing R) 1 mu α) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D (FractionRing R) (α + 1 • mu)) (DegPre.famε 1) t
      (DegPre.famφ D (FractionRing R) α) (DegPre.famε 1) s (DegPre.trF D (FractionRing R) mu).left
      (DegPre.deltaφ D (FractionRing R) 1 α mu) (DegPre.deltaε 1) u

variable {D}

theorem feRel_iff {mu α : D.X} {s : SecFMod D (FractionRing R) 1 α} {t : SecFMod D (FractionRing R) 1 (α + 1 • mu)} :
    FERel D mu α s t ↔ ∀ y J, Good D.P.L y J → sval t (𝟙 _) y J =
      sval s (𝟙 _ ≫ (DegPre.trF D (FractionRing R) mu).left) y J *
        (uVal D (FractionRing R) 1 α (cP D _ mu) (𝟙 _) y J *
          val (DegPre.famMult D (FractionRing R) 1 mu α) (𝟙 _ ≫ fst (TF (R := R) (FractionRing R)) D.P.A).left y J).val := by
  obtain ⟨⟨u₀, hu₀, hc₀⟩, hv⟩ := gen_fe (D := D) (F := FractionRing R) GlobalTheory.globalFns_holds 1 mu α
  constructor
  · intro H y J hJ
    rw [← hv u₀ hu₀ hc₀ _ (𝟙 _) y J hJ]
    exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u₀).1 (H u₀ hu₀ hc₀) _ _ y J hJ
  · intro H u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have := H y J hJ
    rw [← hv u hu hc _ (𝟙 _) y J hJ] at this
    exact this

theorem FERel.unique {mu α : D.X} {s : SecFMod D (FractionRing R) 1 α} {t t' : SecFMod D (FractionRing R) 1 (α + 1 • mu)}
    (h : FERel D mu α s t) (h' : FERel D mu α s t') : t = t' :=
  sec_ext' D.P.isLB fun y J hJ => (feRel_iff.1 h y J hJ).trans (feRel_iff.1 h' y J hJ).symm

theorem FERel.smul {mu α : D.X} {s : SecFMod D (FractionRing R) 1 α} {t : SecFMod D (FractionRing R) 1 (α + 1 • mu)}
    (h : FERel D mu α s t) (c : FractionRing R) : FERel D mu α (c • s) (c • t) := by
  refine feRel_iff.2 fun y J hJ => ?_
  have e : (DegPre.trF D (FractionRing R) mu).left ≫ strF D (FractionRing R) = strF D (FractionRing R) := by
    rw [← Over.comp_left, DegPre.trF, lift_fst]
  rw [sval_smul' hJ, sval_smul' hJ, feRel_iff.1 h y J hJ, Category.assoc, e, _root_.mul_assoc]

theorem exists_psi_val [IsLocalRing R] (D : DegPre R) (χ : D.X) {a₀ : R} (h : PsiCoord D χ a₀) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧ ∃ b : Rˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = constVal (r ≫ jK R) z (a₀ * b) * (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj, le', hψ⟩ := h
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let φ := RingEquiv.ofBijective _ (GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := R))
  let b : Rˣ := Units.map φ.symm.toMonoidHom (res le (e.s j))⁻¹
  have hb : DegPre.toOpen (R := R) ⊤ b = (res le (e.s j))⁻¹.val := φ.apply_symm_apply _
  refine ⟨e, he, b, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e (r ≫ jK R) z J = _ := gen_trans he (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = constVal (r ≫ jK R) z a₀ := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : constVal (r ≫ jK R) z b *
      (gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) (e.s j)).val = 1 := by
    rw [constVal, ← hto, hb, gs_unit _ z ⊤ trivial, map_inv]
    exact (congrArg₂ (fun q c => q⁻¹.val * c) (gm_res (r ≫ jK R) z le trivial (e.s j)) rfl).trans (Units.inv_mul _)
  have e₆ : constVal (r ≫ jK R) z (a₀ * b) = constVal (r ≫ jK R) z a₀ * constVal (r ≫ jK R) z b := by
    rw [constVal, map_mul, gs_mul _ z ⊤ trivial]; rfl
  rw [e₁, e₂, e₆, Units.val_mul, Units.val_mul]
  erw [e₃, e₄]
  linear_combination (-(constVal (r ≫ jK R) z a₀ * (trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j).val)) * e₅

theorem trB_comp (a b : D.X) (h : a + b = 0) : (trB D a).left ≫ (trB D b).left = 𝟙 _ := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, comp_cP, trB, _root_.mul_assoc, ← cPoint_add, h, cPoint_zero,
    _root_.mul_one, Over.id_left]

theorem exists_equiv (mu α : D.X) (eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + 1 • mu))
        (fun i => (trB D mu).left ≫ D.famφB α i)) (DegPre.deltaε 1))) (heB : eB.IsGen) :
    ∃ Θ : SecBMod D 1 α ≃ₗ[R] SecBMod D 1 (α + 1 • mu), ∀ s (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval (Θ s) ρ z J = sval s (ρ ≫ (trB D mu).left) z J * (val eB ρ z J).val := by
  have hL := D.P.isLB
  have h₁ : ∀ s : SecBMod D 1 α, ∃ t : SecBMod D 1 (α + 1 • mu), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval t ρ z J = sval s (ρ ≫ (trB D mu).left) z J * (val eB ρ z J).val := fun s => by
    obtain ⟨t, ht⟩ := exists_sec hL (φ' := D.famφB (α + 1 • mu)) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec s (trB D mu).left eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ _ ρ z hJ)⟩
  have i₁ := trB_comp (D := D) (-mu) mu (neg_add_cancel mu)
  have i₂ := trB_comp (D := D) mu (-mu) (add_neg_cancel mu)
  have h₂ : ∀ t : SecBMod D 1 (α + 1 • mu), ∃ s : SecBMod D 1 α, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval s ρ z J = sval t (ρ ≫ (trB D (-mu)).left) z J * (val eB (ρ ≫ (trB D (-mu)).left) z J)⁻¹.val :=
    fun t => by
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := D.famφB α) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, neg_neg,
        Finset.prod_inv_distrib, reassoc_of% i₁]
      rw [mul_inv, inv_inv, mul_inv_cancel_left])
      (pullMulSec t (trB D (-mu)).left (LB.pullGen D.P.L _ _ (LB.invGen D.P.L _ _ eB) (trB D (-mu)).left)
        (pullGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ heB) _))
    refine ⟨s, fun Z ρ z J hJ => (hs Z ρ z J hJ).trans ((sval_pullMulSec _ _ _ _ ρ z hJ).trans ?_)⟩
    rw [val_pull hJ, val_inv]
  choose f hf using h₁
  choose g hg using h₂
  have w : (trB D mu).left ≫ D.P.A.hom = D.P.A.hom := Over.w _
  refine ⟨⟨⟨⟨f, fun s t => sec_ext' hL fun y J hJ => ?_⟩, fun c s => sec_ext' hL fun y J hJ => ?_⟩, g,
    fun s => sec_ext' hL fun y J hJ => ?_, fun t => sec_ext' hL fun y J hJ => ?_⟩, hf⟩
  · rw [sval_add' hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, sval_add' hJ, add_mul]
  · show sval (f (c • s)) _ _ _ = sval (c • f s : SecBMod D 1 _) _ _ _
    rw [sval_smul' hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, sval_smul' hJ, Category.assoc, w, _root_.mul_assoc]
  · show sval (g (f s)) _ _ _ = _
    rw [hg _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, Category.assoc, i₁, Category.comp_id, Units.mul_inv_cancel_right]
  · show sval (f (g t)) _ _ _ = _
    rw [hf _ _ _ _ _ hJ, hg _ _ _ _ _ hJ, Category.assoc, i₂, Category.comp_id, Units.inv_mul_cancel_right]

theorem constVal_mul {S : Type} [CommRing S] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of S)) (z : Z) (a b : S) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul _ z ⊤ trivial]; rfl

theorem unit_calc {S : Type} [CommRing S] {P₁ P₂ E₁ E₂ : Sˣ} {κ c₁ c₂ : S} (p₁ : P₁.val = c₁ * E₁.val)
    (p₂ : P₂.val = c₂ * E₂.val) (k : κ * c₂ = c₁) : κ * (E₁ * E₂⁻¹).val = (P₁ * P₂⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, Units.eq_mul_inv_iff_mul_eq, p₁, p₂, ← k]
  linear_combination (κ * c₂ * E₁.val) * Units.inv_mul E₂

theorem exists_transl [IsLocalRing R] (Dg : DegData R (maximalIdeal R)) (mu α : Dg.toPre.X) :
    ∃ (Θ : SecBMod Dg.toPre 1 α ≃ₗ[R] SecBMod Dg.toPre 1 (α + 1 • mu)) (κ : (FractionRing R)ˣ),
      (κ : Cls R) = psiCls Dg (mu + α) * (psiCls Dg α)⁻¹ ∧
      ∀ s, FERel Dg.toPre mu α (resF Dg.toPre (FractionRing R) 1 α s)
        ((κ : FractionRing R) • resF Dg.toPre (FractionRing R) 1 _ (Θ s)) := by
  let D := Dg.toPre
  obtain ⟨e₁, he₁, b₁, h₁⟩ := exists_psi_val D (mu + α) (coord_spec Dg _)
  obtain ⟨e₂, he₂, b₂, h₂⟩ := exists_psi_val D α (coord_spec Dg _)
  have c₁ : ∀ χ, D.P.A.hom ≫ (D.c χ).left = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by simp [SectionScalarValuation.cQ]
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D 1 α mu (LB.mulGen D.P.L _ _ _ _ e₁ (LB.invGen D.P.L _ _ e₂))
    (mulGen_isGen _ _ _ _ _ _ _ he₁ (invGen_isGen _ _ _ _ he₂)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁]
      rw [add_comm mu α, SectionScalarValuation.cQ_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, neg_neg]
      module)
  obtain ⟨Θ, hΘ⟩ := exists_equiv mu α eB heB
  have n₁ : coord Dg (mu + α) * b₁ ≠ 0 := mul_ne_zero (coord_ne Dg _) b₁.ne_zero
  have n₂ : coord Dg α * b₂ ≠ 0 := mul_ne_zero (coord_ne Dg _) b₂.ne_zero
  refine ⟨Θ, toK _ n₁ * (toK _ n₂)⁻¹, ?_, fun s => feRel_iff.2 fun y J hJ => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← toK_cls_eq (coord_ne Dg _) n₁ ⟨b₁, rfl⟩,
      ← toK_cls_eq (coord_ne Dg _) n₂ ⟨b₂, rfl⟩]
    rfl
  · rw [sval_smul' hJ, sval_resF _ _ _ _ hJ, sval_resF _ _ _ _ hJ, hΘ _ _ _ _ _ hJ]
    simp only [Category.id_comp]
    rw [← Over.comp_left, ← Over.comp_left, trF_prB, mul_left_comm]
    congr 1
    have w₁ : ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R =
        (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom :=
      (Category.assoc _ _ _).trans
        ((Over.w (fst (TF (R := R) (FractionRing R)) D.P.A)).trans (Over.w (DegPre.prB D (FractionRing R))).symm)
    have w₂ : (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom = strF D (FractionRing R) ≫
      Spec.map (CommRingCat.ofHom (toF (R := R) (FractionRing R))) := (isPullback_prB D (FractionRing R)).w
    have v₁ := veB _ (DegPre.prB D (FractionRing R)) y J hJ
    have p₁ := h₁ _ ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
    have p₂ := h₂ _ ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
    rw [w₁] at p₁ p₂
    have fm : val (DegPre.famMult D (FractionRing R) 1 mu α) (fst (TF (R := R) (FractionRing R)) D.P.A).left y J =
        val (D.psi (mu + α)) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J *
        (val (D.psi α) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J)⁻¹ := by
      rw [val_famMult _ hJ, UUA.val_powGen', UUA.val_powGen']
      refine (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))) rfl).trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, pow_one]
      abel
    have k : constVal (strF D (FractionRing R)) y ((toK _ n₁ * (toK _ n₂)⁻¹ : (FractionRing R)ˣ) : FractionRing R) *
        constVal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y (coord Dg α * b₂) =
        constVal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y (coord Dg (mu + α) * b₁) := by
      rw [w₂, constVal_specMap, constVal_specMap, ← constVal_mul]
      congr 1
      exact congrArg Units.val (inv_mul_cancel_right (toK _ n₁) (toK _ n₂))
    rw [val_mul hJ, val_inv] at v₁
    rw [fm, uVal_id, comp_cP]
    erw [v₁]
    have q : constVal (strF D (FractionRing R)) y ((toK _ n₁ * (toK _ n₂)⁻¹ : (FractionRing R)ˣ) : FractionRing R) *
        (val e₁ ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y J *
          (val e₂ ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y J)⁻¹).val =
        (val (D.psi (mu + α)) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J *
        (val (D.psi α) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J)⁻¹).val := by
      exact unit_calc p₁ p₂ k
    rw [Units.val_mul _ (_ * _), Units.val_mul _ (_ * _), ← q, mul_left_comm]
    rfl

end Transl

section Gen

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Dg : DegData R (maximalIdeal R))

theorem exists_secGen (χ : Dg.toPre.X) : ∃ e : SecBMod Dg.toPre 1 χ, ∀ s, ∃! a : R, s = a • e := by
  suffices H : ∃ e : SecBMod Dg.toPre 1 (0 + 1 • χ), ∀ s, ∃! a : R, s = a • e by rwa [zero_add, one_smul] at H
  obtain ⟨b, hb⟩ := GlobalTheory.IndivisibleSection.exists_generator Dg.toPre GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨Θ, -⟩ := exists_transl Dg χ 0
  let b' : SecBMod Dg.toPre 1 0 := b
  have hb' : ∀ (a : R) (s : SecBMod Dg.toPre 1 0), SecIsMul Dg.toPre.P.A.hom a s b ↔ s = a • b' := fun a s =>
    ⟨fun h => SecOver.ext _ _ h, fun h _ => by rw [h]; rfl⟩
  refine ⟨Θ b', fun s => ?_⟩
  refine (existsUnique_congr fun a => ?_).1 (hb (Θ.symm s))
  rw [hb', LinearEquiv.symm_apply_eq, map_smul]

def secGen (χ : Dg.toPre.X) : SecBMod Dg.toPre 1 χ := (exists_secGen Dg χ).choose

theorem secGen_spec (χ : Dg.toPre.X) (s : SecBMod Dg.toPre 1 χ) : ∃! a : R, s = a • secGen Dg χ :=
  (exists_secGen Dg χ).choose_spec s

def secGenK (χ : Dg.toPre.X) : SecFMod Dg.toPre (FractionRing R) 1 χ := resF Dg.toPre (FractionRing R) 1 χ (secGen Dg χ)

theorem secGenK_ne (χ : Dg.toPre.X) : secGenK Dg χ ≠ 0 := fun h => by
  have h0 : secGen Dg χ = 0 := resF_injective Dg.toPre (FractionRing R) 1 χ (h.trans (map_zero _).symm)
  exact one_ne_zero ((secGen_spec Dg χ 0).unique (y₁ := (1 : R)) (y₂ := 0) (by rw [h0, smul_zero]) (by rw [zero_smul]))

theorem resF_smul_secGen (χ : Dg.toPre.X) (a : R) :
    resF Dg.toPre (FractionRing R) 1 χ (a • secGen Dg χ) = algebraMap R (FractionRing R) a • secGenK Dg χ :=
  map_smulₛₗ _ _ _

variable {Dg}

def IsTransUnit {O : Type} [Ring O] [Module O Dg.toPre.X] (t : Dg.toPre.X → Dg.toPre.X → (FractionRing R)ˣ) (w : O)
    (mu α : Dg.toPre.X) (u : Rˣ) : Prop :=
  FERel Dg.toPre mu α (secGenK Dg α)
    ((algebraMap R (FractionRing R) u * (t mu (w • mu) : FractionRing R) * (t mu α : FractionRing R)) • secGenK Dg (α + 1 • mu))

theorem existsUnique_transUnit [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (ρ : Dg.toPre.OAct O) {t} (ht : IsReading Dg O t) {w : O} (hw : w + star w = 1) (mu α : Dg.toPre.X) :
    ∃! u, IsTransUnit t w mu α u := by
  refine existsUnique_of_exists_of_unique ?_ fun u u' h h' => ?_
  · obtain ⟨Θ, κ, hκ, hΘ⟩ := exists_transl Dg mu α
    obtain ⟨v, hv, -⟩ := secGen_spec Dg _ (Θ (secGen Dg α))
    obtain ⟨c, hc, -⟩ := secGen_spec Dg _ (Θ.symm (secGen Dg (α + 1 • mu)))
    rw [LinearEquiv.symm_apply_eq, map_smul, hv, smul_smul] at hc
    have hcv : c * v = 1 := (secGen_spec Dg _ _).unique hc (one_smul _ _).symm
    have e : ((t mu (w • mu) * t mu α : (FractionRing R)ˣ) : Cls R) = κ := by
      rw [QuotientGroup.mk_mul, ht.cls, ht.cls, tauCls_half Dg ρ hw, hκ, tauCls]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    obtain ⟨u₀, hu₀⟩ := cls_eq_iff.1 e
    refine ⟨u₀ * ⟨v, c, (mul_comm _ _).trans hcv, hcv⟩, ?_⟩
    have H := hΘ (secGen Dg α)
    rw [hv, resF_smul_secGen, smul_smul, ← hu₀] at H
    unfold IsTransUnit
    refine (congrArg (fun x : FractionRing R => FERel Dg.toPre mu α (secGenK Dg α) (x • secGenK Dg (α + 1 • mu))) ?_).mp H
    simp only [Units.val_mul, map_mul]
    ring
  · have e := smul_left_injective _ (secGenK_ne Dg _) (FERel.unique h h')
    have e' := mul_right_cancel₀ (Units.ne_zero _) (mul_right_cancel₀ (Units.ne_zero _) e)
    exact Units.ext (IsFractionRing.injective R _ e')

end Gen

section Sec

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I D A G)

abbrev SecG : Type :=
  SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)))

def SecGK : Type :=
  SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)))

instance : AddCommGroup (SecGK U) := inferInstanceAs (AddCommGroup (SecOver _ _))
instance : Module (FractionRing R) (SecGK U) := inferInstanceAs (Module (FractionRing R) (SecOver _ _))
instance : Module R (SecGK U) := Module.compHom _ (algebraMap R (FractionRing R))
instance : IsScalarTower R (FractionRing R) (SecGK U) :=
  ⟨fun a b s => by rw [Algebra.smul_def, mul_smul]; rfl⟩

def resG : SecG U →ₗ[R] SecGK U where
  toFun s := pullOver U.LG.L _ (f := algebraMap R (FractionRing R)) (pullback.condition (f := G.hom) (g := jK R))
    (fun _ => (Category.comp_id _).symm) s
  map_add' s t := map_add _ s t
  map_smul' c s := map_smulₛₗ (pullOver U.LG.L _ (f := algebraMap R (FractionRing R))
    (pullback.condition (f := G.hom) (g := jK R)) (fun _ => (Category.comp_id _).symm)) c s

def secReg : Submodule R (SecGK U) := LinearMap.range (resG U)

def expandFun (s : SecGK U) : Fam D.toPre (FractionRing R) 1 := ((U.expand 1 le_rfl).1 s).choose

theorem expands_iff (s : SecGK U) (F : Fam D.toPre (FractionRing R) 1) : U.Expands 1 s F ↔ F = expandFun U s :=
  ⟨((U.expand 1 le_rfl).1 s).choose_spec.2 F, fun h => h ▸ ((U.expand 1 le_rfl).1 s).choose_spec.1⟩

def expand (hR : AdmBase R I) [GeometricallyConnected G.hom] : SecGK U →ₗ[FractionRing R] Fam D.toPre (FractionRing R) 1 where
  toFun := expandFun U
  map_add' s t := by
    have := GlobalTheory.expands_linear R I hR D A G U.toUnifPre 1 2 ![s, t] ![expandFun U s, expandFun U t] ![1, 1] (s + t : SecGK U)
      (fun i => by fin_cases i <;> exact (expands_iff U _ _).2 rfl) (fun j => by
        have e : s + t = (1 : FractionRing R) • s + (1 : FractionRing R) • t := by rw [one_smul, one_smul]
        rw [e, Fin.sum_univ_two]; rfl)
    rw [← (expands_iff U _ _).1 this, Fin.sum_univ_two]
    simp
  map_smul' c s := by
    have := GlobalTheory.expands_linear R I hR D A G U.toUnifPre 1 1 ![s] ![expandFun U s] ![c] (c • s : SecGK U)
      (fun i => by fin_cases i; exact (expands_iff U _ _).2 rfl) (fun j => by rw [Fin.sum_univ_one]; rfl)
    rw [← (expands_iff U _ _).1 this, Fin.sum_univ_one]
    simp

theorem expand_bijective (hR : AdmBase R I) [GeometricallyConnected G.hom] : Function.Bijective (expand U hR) :=
  (Function.bijective_iff_existsUnique _).2 fun F =>
    (existsUnique_congr fun s => (expands_iff U s F).trans eq_comm).1 ((U.expand 1 le_rfl).2 F)

end Sec

section Coef

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G) (hR : AdmBase R (maximalIdeal R)) [GeometricallyConnected G.hom]

theorem existsUnique_coef (s : SecGK U) (χ : D.toPre.X) :
    ∃! x : FractionRing R, famComp D.toPre (FractionRing R) 1 χ (expand U hR s) = x • secGenK D χ := by
  refine existsUnique_of_exists_of_unique ?_ fun x y hx hy => smul_left_injective _ (secGenK_ne D χ) (hx.symm.trans hy)
  obtain ⟨r, hr, σ, f, -, hf, -⟩ := (expands_iff U s _).2 rfl
  obtain ⟨a, ha, -⟩ := secGen_spec D χ (f χ)
  have h := (secScal_iff_resF D.toPre (FractionRing R) _ (f χ) r).1 (hf χ)
  rw [ha, resF_smul_secGen] at h
  have h0 : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  refine ⟨(algebraMap R (FractionRing R) r)⁻¹ * algebraMap R _ a, ?_⟩
  rw [mul_smul, h]
  exact (inv_smul_smul₀ h0 _).symm

def coef : SecGK U →ₗ[FractionRing R] (D.toPre.X → FractionRing R) where
  toFun s χ := (existsUnique_coef U hR s χ).choose
  map_add' s t := funext fun χ => ((existsUnique_coef U hR (s + t) χ).choose_spec.2 _ (by
    rw [map_add, map_add, (existsUnique_coef U hR s χ).choose_spec.1, (existsUnique_coef U hR t χ).choose_spec.1,
      Pi.add_apply]
    exact (add_smul _ _ _).symm)).symm
  map_smul' c s := funext fun χ => ((existsUnique_coef U hR (c • s) χ).choose_spec.2 _ (by
    rw [map_smul, map_smul, (existsUnique_coef U hR s χ).choose_spec.1, smul_smul]; rfl)).symm

theorem coef_spec (s : SecGK U) (χ : D.toPre.X) :
    famComp D.toPre (FractionRing R) 1 χ (expand U hR s) = coef U hR s χ • secGenK D χ :=
  (existsUnique_coef U hR s χ).choose_spec.1

end Coef

end GlobalTheory.LocM.Bdy
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

namespace GlobalTheory.LocM

namespace Bdy

section Reg

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G) (hR : AdmBase R (maximalIdeal R)) [GeometricallyConnected G.hom]

theorem exists_coef_zero (x : FractionRing R) : ∃ s, coef U hR s 0 = x := by
  obtain ⟨Φ, hΦ, -⟩ := FamFree.exists_fam_single (F := FractionRing R) GlobalTheory.globalFns_holds D.tau_bimult le_rfl 0
    (x • secGenK D 0)
  obtain ⟨s, rfl⟩ := (expand_bijective U hR).2 Φ
  exact ⟨s, smul_left_injective _ (secGenK_ne D 0) ((coef_spec U hR s 0).symm.trans hΦ)⟩

end Reg

namespace BDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t₀ : SAB H X} {x : X} (B : BDat t₀ x)

abbrev Ylat : Type := B.U.D.toPre.X

def chX : Type := B.Ylat
instance : AddCommGroup B.chX := inferInstanceAs (AddCommGroup B.Ylat)
instance : Module (𝓞 E) B.chX := Module.compHom B.Ylat (H.bar : 𝓞 E →+* 𝓞 E)

def phi : B.Ylat ≃+ B.chX := AddEquiv.refl _

def tau : B.Ylat → B.Ylat → (FractionRing B.R)ˣ :=
  letI := H.starRing
  (exists_reading B.U.D B.U.oD).choose

theorem tau_spec : letI := H.starRing; IsReading B.U.D (𝓞 E) B.tau :=
  letI := H.starRing
  (exists_reading B.U.D B.U.oD).choose_spec

theorem adm : AdmBase B.R (maximalIdeal B.R) := ⟨B.noeth, B.dom, B.normal, B.complete⟩

instance : GeometricallyConnected B.t.G.hom := B.t.semi.geomConnected

def fc : SecGK B.U.U →ₗ[FractionRing B.R] (B.chX → FractionRing B.R) := coef B.U.U B.adm

def trU {w : 𝓞 E} (hw : w + H.bar w = 1) (a : B.Ylat) (χ : B.chX) : B.Rˣ :=
  letI := H.starRing
  (existsUnique_transUnit B.U.oD B.tau_spec hw a χ).choose

end BDat

end Bdy

open Bdy

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem bar_eq_of_conj (A : Amb D) {c c' : 𝓞 D.host.E} (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) :
    c' = A.H.bar c := by
  apply RingOfIntegers.ext
  rw [hc, A.H.bar_eq]
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem cmHostUnit_add_conj_eq_one (A : Amb D) : w0 D + A.H.bar (w0 D) = 1 := by
  rw [← bar_eq_of_conj A (one_sub_halfSqrt_eq_conj D), add_sub_cancel]

namespace At

variable (ct : At S κ p)

def BPt : Type :=
  {x : ct.Xm.X // IsClosed ({x} : Set ct.Xm.X) ∧ ¬ ct.Xm.abP x ∧ IsDomain (Cpl ct.Xm.X x) ∧ IsIntegrallyClosed (Cpl ct.Xm.X x)}

theorem nonempty_bdat (z : ct.BPt) : Nonempty (BDat ct.Xm.t z.1) :=
  haveI := z.2.2.2.1
  haveI := z.2.2.2.2
  Bdy.nonempty_bdat ct.hp.ne_zero ct.hW ct.Xm ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).1
    ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).2.1 z.1

def bdat (z : ct.BPt) : BDat ct.Xm.t z.1 := pick (ct.nonempty_bdat z)

end At

def bdyTrue (ct : At S κ p) : BdySt ct where
  BPt := ct.BPt
  Rl z := (ct.bdat z).R
  Yb z := (ct.bdat z).Ylat
  Xb z := (ct.bdat z).chX
  phib z := (ct.bdat z).phi
  phib_conj z c c' hc a := by
    obtain rfl := bar_eq_of_conj A hc
    rfl
  taub z := (ct.bdat z).tau
  taub_add_left z := letI := A.H.starRing; (ct.bdat z).tau_spec.add_left
  taub_add_right z a χ χ' := by
    letI := A.H.starRing
    have h := (ct.bdat z).tau_spec
    exact (h.symm _ _).trans ((h.add_left χ χ' a).trans (congrArg₂ (· * ·) (h.symm _ _) (h.symm _ _)))
  taub_symm z := letI := A.H.starRing; (ct.bdat z).tau_spec.symm
  taub_smul z := letI := A.H.starRing; (ct.bdat z).tau_spec.bal
  taub_pos z := letI := A.H.starRing; (ct.bdat z).tau_spec.pos
  Sg z := SecGK (ct.bdat z).U.U
  Sreg z := secReg (ct.bdat z).U.U
  fc z := (ct.bdat z).fc
  trU z := (ct.bdat z).trU (cmHostUnit_add_conj_eq_one A)

example (A : Amb D) : w0 D = A.H.w0 := by
  apply RingOfIntegers.ext
  have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) A.H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, map_ofNat] at h
  have h' : algebraMap (𝓞 D.host.E) D.host.E A.H.rt = D.host.sqrtMinusD := A.rt_eq
  change (1 + D.host.sqrtMinusD) / 2 = algebraMap (𝓞 D.host.E) D.host.E A.H.w0
  rw [← h', ← h]
  ring

example (ct : At S κ p) (z : (bdyTrue ct).BPt) (a : (bdyTrue ct).Yb z) (ha : a ≠ 0) :
    ∃ r ∈ maximalIdeal ((bdyTrue ct).Rl z), algebraMap _ (FractionRing ((bdyTrue ct).Rl z)) r =
      (bdyTrue ct).taub z a ((bdyTrue ct).phib z a) :=
  letI := A.H.starRing
  (ct.bdat z).tau_spec.pos_max ha

example (ct : At S κ p) (z : (bdyTrue ct).BPt) : ∃ s, (bdyTrue ct).fc z s 0 = 1 :=
  exists_coef_zero (ct.bdat z).U.U (ct.bdat z).adm 1

end GlobalTheory.LocM
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

variable (D) in

def sideEmb (σ : PsiT D × Bool) : D.host.E →+* ℂ :=
  if σ.2 then conjEmb (DV.tauEmb D (D.eTau.symm σ.1)) else DV.tauEmb D (D.eTau.symm σ.1)

example (t : D.what₂.Tau) : sideEmb D (D.eTau t, false) = DV.tauEmb D t ∧
    sideEmb D (D.eTau t, true) = conjEmb (DV.tauEmb D t) := by
  simp [sideEmb]

open Classical in

def evlTrue (ct : At S κ p) : EvlSt ct :=
  letI : Fintype (PsiT D) := Fintype.ofEquiv _ D.eTau
  { LieGt := fun y σ => RayEv.LieGt (ct.dat y) (sideEmb D σ)
    LieB := fun y σ => RayEv.LieB (ct.dat y) (sideEmb D σ)
    LieT := fun y σ => RayEv.LieT (ct.dat y) (sideEmb D σ)
    lgAdd := fun _ _ => inferInstance
    lbAdd := fun _ _ => inferInstance
    ltAdd := fun _ _ => inferInstance
    resB := fun y σ => (RayEv.resB (ct.dat y) (sideEmb D σ)).toAddMonoidHom
    incT := fun y σ => (RayEv.incT (ct.dat y) (sideEmb D σ)).toAddMonoidHom
    kapGt := fun y σ => RayEv.kapGt (ct.dat y) (sideEmb D σ)
    kapB := fun y σ => RayEv.kapB (ct.dat y) (sideEmb D σ)
    Harm := fun y => RayEv.HarmAt (ct.dat y) (sideEmb D)
    SecP := fun y => RayEv.SecAt (ct.dat y)
    evA := fun _ Q s => Q.evA s
    evGt := fun _ Q s => Q.evGt s }

section Fields

attribute [local irreducible] RayEv.kapGt RayEv.kapB RayEv.resB RayEv.incT RayEv.LieGt RayEv.LieB RayEv.LieT At.dat sideEmb

variable (ct : At S κ p) (y : ct.Pt ct.Xm) (σ : PsiT D × Bool)








end Fields

end GlobalTheory.LocM
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def IsHTLatOf {ct : At S κ p} (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (B : ct.Mdl) (L : Lat B) : Prop :=
  (∃ n, 3 ≤ n ∧ hm.IsHTBlowup B (ct.Xn n)) ∧ ∀ y : ct.Pt B,
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing
    hm.omPat y = (GlobalTheory.HTSheaf.fibLat (ct.isGrpPullback_htToMdl y) L.N).toAddSubgroup

def stagesOf (ct : At S κ p) (hm : HTmSt ct (shfTrue ct) (htpTrue ct)) (jt : JetSt ct (uniTrue ct) (thgTrue ct)) : Stages ct where
  lw := SharedLaws.lawSt _ _ _ _ _ _ _ ct
  mo := motTrue ct
  sh := shfTrue ct
  fg := flgOf ct (IsHTLatOf hm)
  fr := frmTrue ct
  ch := chtTrue ct
  tr := torTrue ct
  fj := fjTrue ct
  un := uniTrue ct
  tb := thbTrue ct
  ky := keyTrue ct
  bd := bdyTrue ct
  tg := thgTrue ct
  jt := jt
  ev := evlTrue ct
  hq := htpTrue ct
  hm := hm
  cd := crdTrue ct
  cr := crhOf ct (IsHTLatOf hm) (classFam (IsHTLatOf hm))

abbrev HTmFam (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  HTmSt ct (shfTrue ct) (htpTrue ct)

abbrev JetFam (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  JetSt ct (uniTrue ct) (thgTrue ct)

end GlobalTheory.LocM
end
end
