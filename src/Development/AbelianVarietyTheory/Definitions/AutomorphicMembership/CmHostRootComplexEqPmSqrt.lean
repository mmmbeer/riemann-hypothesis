import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.MapRingEquivTransApply
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsometryOfConjSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLatOfOneOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType
open scoped CategoryTheory.Obj
open GlobalTheory.CompRat (Curve wC wE IsSplit FixesCurve CurveOver SplitLat)

namespace GlobalTheory.ShFam.GeomComp

open GlobalTheory.AnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem actsBy_of_dvd {C : Curve H} {τ : ℂ ≃+* ℂ} {io : C.P.A.left ⟶ C.P.A.left} {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n)
    {s : ℤ × ℤ} (hC : C.ActsBy τ io n s) : C.ActsBy τ io m s := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨hC.1, fun a => ?_⟩
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hn)
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul hn)
  have e : wC H (k * a.1, k * a.2) = k * wC H a := by
    simp only [wC]
    push_cast
    ring
  have := hC.2 (k * a.1, k * a.2)
  rw [e] at this
  convert this using 3
  · push_cast
    field_simp
  · push_cast
    field_simp

theorem splitLat_all (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (D : Datum H) : SplitLat D := by
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact GlobalTheory.CompRat.splitLat_of_definite E H D h0
  · by_cases h3 : 3 ≤ D.p + D.q
    · exact GlobalTheory.SplitGenus.splitLat_of_indefinite E H D h1 h3 (by omega) (by omega)
    · exact splitLat_of_one_one E H D h1 (by omega) (by omega)

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem congr_of_section (F : FamilyUnif Xo σ ty) (τ : ℂ ≃+* ℂ) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    {P' : (F.Di i').La →+ (Fin g → ℂ)} (hP' : IsPeriod (F.Di i') ty P')
    (hu : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P') {n : ℕ} (hn : 0 < n) (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G)
    {x : (F.Di i).La} {x' w : (F.Di i').La} (h1 : toUnit _ ≫ s = F.ex i P ((n : ℂ)⁻¹ • P x))
    (h2 : toUnit _ ≫ s = F.ex i' P' ((n : ℂ)⁻¹ • P' x'))
    (key : spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' w)).left) :
    ∃ e, w = x' + n • e := by
  have hM' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have tu : ∀ y : Sp ℂ ⟶ Xo.X, (toUnit (Over.mk y) ≫ s).left = y ≫ s.left := by
    intro y
    rw [Over.comp_left]
    congr 1
  rw [← h1, tu, ← Category.assoc, hu, ← tu, h2] at key
  have e : F.ex i' P' ((n : ℂ)⁻¹ • P' x') = F.ex i' P' ((n : ℂ)⁻¹ • P' w) := Over.OverMorphism.ext key
  have e' := F.ex_add i' P' hP' ((n : ℂ)⁻¹ • P' (w - x')) ((n : ℂ)⁻¹ • P' x')
  rw [← smul_add, ← map_add, sub_add_cancel, e] at e'
  obtain ⟨y, hy⟩ := (F.ex_ker i' P' hP' _).1 (mul_eq_right.1 e'.symm)
  refine ⟨y, ?_⟩
  rw [← sub_eq_iff_eq_add']
  apply hP'.2.1
  rw [map_nsmul, hy, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hM', one_smul]

theorem conj_point_eq (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (τ : ℂ ≃+* ℂ) (hτσ : (τ : ℂ →+* ℂ).comp σ = σ) (hfix : FixesCurve H τ l.M')
    (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) :
    spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτ : τ H.rt0 = H.rt0 := by
    rw [← hσ]
    exact RingHom.congr_fun hτσ _
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM.ne' l.A_pos.ne'
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hact⟩ := exists_isometry_of_conj_split E H D l Xo σ g ty F hD hσ hty τ hτ C io hC.1 i P hP
    i' P' hP' hs hu.symm
  obtain ⟨L, hL⟩ := GlobalTheory.CompRat.exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs
    (fun a ha => (hp a).2 ha) (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have key : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ x, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P x)).left =
      (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ x))).left := by
    intro n hn hd x
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    have := hact n (1, 0) hn (actsBy_of_dvd hM' hd hC) a ha b hb
    rwa [hw, map_one, one_smul, one_smul] at this
  exact hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, GlobalTheory.CompRat.isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', GlobalTheory.CompRat.isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2
      ⟨Φ, L, hE, fun v hv => congr_of_section F τ hP' hu.symm hM _ (F.ex_eta i P hP v hv) (F.ex_eta i' P' hP' v hv)
          (key _ hM (Nat.dvd_lcm_left _ _) _),
        fun v => congr_of_section F τ hP' hu.symm l.A_pos _ (F.ex_etaA i P hP v) (F.ex_etaA i' P' hP' v)
          (key _ l.A_pos (Nat.dvd_lcm_right _ _) _), hL⟩).symm

open Polynomial GlobalTheory.CompRat.FixedConst in

theorem fnAlgClosed_of_fixed_points (F : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (h1 : 1 ≤ D.p + D.q)
    (hty : IsTypeFn H D.p D.q ty) (c : Coeff l)
    (hfix : ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ∀ i, ∃ P, IsPeriod (F.Di i) ty P ∧
      spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P) : FnAlgClosed Xo c := by
  intro Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  have hs : spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom = spMap (algebraMap (KA l) ℂ) := by
    rw [← Spec.map_comp]
    rfl
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, hs])
  obtain ⟨P', hP', hu'⟩ := hfix τ (fun z hz => hτ ⟨z, hz⟩) i
  let x' : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P') (spMap j) ((F.over_σ i P' hP').trans hs.symm)
  have hx1 : x' ≫ pullback.fst _ _ = F.u i P' := pullback.lift_fst _ _ _
  have hx2 : x' ≫ pullback.snd _ _ = spMap j := pullback.lift_snd _ _ _
  have hx' : spMap (τ : ℂ →+* ℂ) ≫ x' = x' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hx1, hu']
    · rw [Category.assoc, hx2, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k
  have key := valAt_eq_of_finite_values E H D l Xo _ g ty F h1 rfl hty c j f _ ((rootSet_finite _ _).insert 0) hS i
    P' P hP' hP x' x hx1 hx2 hu.symm hx
  rw [valAt'_top, valAt'_top, hev, hf] at key
  rw [← key]
  exact (ev_conj x' (τ : ℂ →+* ℂ) f).symm.trans (by rw [hx'])

theorem fnAlgClosed_of_curveOver (Xo : Moduli D l) (c : Coeff l) (hD : 1 ≤ D.p + D.q)
    (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (hC : CurveOver H c.F l.M') : FnAlgClosed Xo c := by
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine fnAlgClosed_of_fixed_points F hD hty c fun τ hτ i => ?_
  obtain ⟨P, hP, hs⟩ := GlobalTheory.CompRat.exists_isSplit_of_splitLat E H (F.Di i) g ty
    (by rw [(F.sig i).1, (F.sig i).2]; exact hty) (splitLat_all h1 _)
  exact ⟨P, hP, conj_point_eq F hD rfl hty τ (RingHom.ext fun x => hτ _ (c.le x.2)) (hC τ hτ) i P hP hs⟩

end GlobalTheory.ShFam.GeomComp
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal

namespace GlobalTheory.ShFam

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

structure TwMap (σ : 𝓞 E ≃+* 𝓞 E) {S' S : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) where

  cm : CubeMap t'.G t.G

  cart : IsGrpPullback t'.G t.G f cm.F

  base : cm.e = f

  act : ∀ a, (t'.act.act a).left ≫ cm.F = cm.F ≫ (t.act.act (σ a)).left

  lin : cm.IsPullCubical t'.cub t.cub

def TwMap.reflEquiv {S' S : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) :
    TwMap (RingEquiv.refl (𝓞 E)) t' t f ≃ SABMap t' t f where
  toFun m := ⟨m.cm, m.cart, m.base, m.act, m.lin⟩
  invFun m := ⟨m.cm, m.cart, m.base, m.act, m.lin⟩
  left_inv _ := rfl
  right_inv _ := rfl

section OneLevel

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

def polLB (T : TorModel Y) : LB T.Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm T.Z) T.m0) (GlobalTheory.CechPic.dual T.BD.lb)

def IsHoriz (T : TorModel Y) : Prop :=
  (T.BD.idealSheaf.support : Set T.Z.X) ⊆ closure (genι T.Z '' (genBd T.Z : Set (gen T.Z)))

def IsStable (T : TorModel Y) : Prop :=
  ∀ (σ : 𝓞 E ≃+* 𝓞 E) (γ : c.F ≃+* c.F) (γ₀ : O ≃+* O) (r : Xo.XF c ≅ Xo.XF c)
    (ν : TwMap σ T.Z.oF.t T.Z.oF.t r.hom),
    σ H.w0 = H.w0 → (∀ x : c.F, (x : ℂ) = H.rt0 → γ x = x) → (∀ x, β (γ₀ x) = γ (β x)) →
    r.hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap γ.toRingHom →
    ∃ (ρ : T.Z.X ≅ T.Z.X) (mu : TwMap σ T.Z.t T.Z.t ρ.hom),
      ρ.hom ≫ T.Z.s = T.Z.s ≫ spMap γ₀.toRingHom ∧ T.Z.j ≫ ρ.hom = r.hom ≫ T.Z.j ∧
      T.Z.m.φ ≫ mu.cm.F = ν.cm.F ≫ T.Z.m.φ ∧ T.BD.idealSheaf.comap ρ.hom = T.BD.idealSheaf

structure IsRecTor (T : TorModel Y) : Prop where

  ample : GlobalTheory.IsAmpleLB (polLB T)

  horiz : IsHoriz T

  stable : IsStable T

theorem IsHoriz.support_eq {T : TorModel Y} (h : IsHoriz T) :
    (T.BD.idealSheaf.support : Set T.Z.X) = closure (genι T.Z '' (genBd T.Z : Set (gen T.Z))) :=
  h.antisymm (closure_minimal (by rintro _ ⟨x, hx, rfl⟩; exact T.BD_pos x hx) T.BD.idealSheaf.support.isClosed)


theorem IsRecTor.isLB_detOm {T : TorModel Y} (h : IsRecTor T) : (GlobalTheory.FlagMod.detOm T.Z).IsLB := by
  refine GlobalTheory.CechPic.isLB_dual (GlobalTheory.FlagMod.isLB_of_ev _ (eq_top_iff.2 fun x _ => ?_)
    fun i j k _ _ z => GlobalTheory.FlagMod.ev_detChg_mul i j k z)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (h.ample.isLB.cover.ge (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i.1 PUnit.unit, LB.wchart_le _ _ _ PUnit.unit hi.1⟩

example (Y : Model Xo c β) (h : Function.Surjective Y.jQ) : IsHoriz (TorModel.ofNoBoundary Y h) := fun x hx =>
  (((GlobalTheory.EffCartierData.zero Y.X).mem_support_iff PUnit.unit (x := x) trivial).1 hx (by
    change x ∈ Y.X.basicOpen (1 : Γ(Y.X, ⊤))
    simp [Scheme.basicOpen_one]; trivial)).elim

end OneLevel

def IsTorTrans {l l₂ : Level H} {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} {c : Coeff l} {c₂ : Coeff l₂} {O O₂ : Type}
    [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c₂.F} {Y : Model Xo c β} {Y₂ : Model Xo₂ c₂ β₂}
    (T : TorModel Y) (T₂ : TorModel Y₂) (b : O →+* O₂) : Prop :=
  T₂.m0 = T.m0 ∧ ∃ π : T₂.Z.X ⟶ T.Z.X, IsTransition T.Z T₂.Z b π ∧ T₂.BD.idealSheaf = T.BD.idealSheaf.comap π

abbrev LocFam (Xo : ∀ l : Level H, Moduli Dw l) : Type 1 :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W

def IsGlob {Xo : ∀ l : Level H, Moduli Dw l} (Y : LocFam Xo) {l : Level H} {c : Coeff l}
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) : Prop :=
  (l.A = 1 → Ygl.Descends) ∧ (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) →
      Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b) ∧ Ygl.N4

structure Sys (Xo : ∀ l : Level H, Moduli Dw l) : Type 1 where

  Y : LocFam Xo

  clauses : ∀ p W hp hW, N2 (Y p W hp hW) ∧
    ∀ i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3 ∧ (Y p W hp hW i).N4


structure TorSys {Xo : ∀ l : Level H, Moduli Dw l} (s : Sys Xo) : Type 1 where

  Ygl : ∀ (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) → Model (Xo l) c (algebraMap (𝓞 c.F) c.F)

  glob : ∀ l c hg, IsGlob s.Y hg (Ygl l c hg)

  T : ∀ l c hg, TorModel (Ygl l c hg)

  isRec : ∀ l c hg, IsRecTor (T l c hg)

  trans : ∀ l c hg l₂ c₂ hg₂ (b : 𝓞 c.F →+* 𝓞 c₂.F), l.Dvd l₂ →
    (∀ x, (((b x : 𝓞 c₂.F) : c₂.F) : ℂ) = ((x : c.F) : ℂ)) → IsTorTrans (T l c hg) (T l₂ c₂ hg₂) b

def SysEx (Xo : ∀ l : Level H, Moduli Dw l) : Prop := ∃ s : Sys Xo, Nonempty (TorSys s)

section Unif

variable {l : Level H}

structure UnfFam (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ) (ξ : E) : Type 1 where

  good : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.Unf Xo c σ N

  law : ∀ σ h, Formalism.L2.PjFree.IsUnf (good σ h)

  chi : ∀ σ h k la γ, ((good σ h).X k).χ la γ = 1

  xi : ∀ σ h k, ((good σ h).X k).ξ0 = ξ

variable {Xo : Moduli Dw l} {c : Coeff l} {N : ℕ} {ξ : E}

def noUnf (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) : Formalism.L2.PjFree.Unf Xo c σ N where
  Comp := PEmpty
  X := PEmpty.elim
  un := fun k => k.elim

open Classical in

def UnfFam.U (u : UnfFam Xo c N ξ) (σ : c.F →+* ℂ) : Formalism.L2.PjFree.Unf Xo c σ N :=
  if h : Formalism.L2.PjFree.GoodEmb c σ then u.good σ h else noUnf Xo c σ N

theorem UnfFam.U_eq (u : UnfFam Xo c N ξ) {σ : c.F →+* ℂ} (h : Formalism.L2.PjFree.GoodEmb c σ) : u.U σ = u.good σ h :=
  dif_pos h

theorem UnfFam.isEmpty_comp (u : UnfFam Xo c N ξ) {σ : c.F →+* ℂ} (h : ¬ Formalism.L2.PjFree.GoodEmb c σ) :
    IsEmpty (u.U σ).Comp := by
  rw [UnfFam.U, dif_neg h]
  exact inferInstanceAs (IsEmpty PEmpty)

theorem nonempty_comp_of_isUnf {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {U : Formalism.L2.PjFree.Unf Xo c σ N}
    (h : Formalism.L2.PjFree.IsUnf U) (hN : 1 ≤ N) : Nonempty U.Comp := by
  obtain ⟨U', hU, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H Dw l Xo c (h.1 ▸ hN)
  obtain ⟨-, ⟨k⟩, hd, -⟩ := hU σ hσ
  obtain ⟨x, hx⟩ := hd k
  obtain ⟨k', -⟩ := h.2.2.1 ((U' σ).un k ⟨x, hx⟩)
  exact ⟨k'⟩

theorem UnfFam.unf (u : UnfFam Xo c N ξ) (hN : 1 ≤ N) (σ : c.F →+* ℂ) (h : Formalism.L2.PjFree.GoodEmb c σ) :
    Formalism.L2.PjFree.IsUnf (u.U σ) ∧ Nonempty (u.U σ).Comp ∧ (∀ k la γ, ((u.U σ).X k).χ la γ = 1) ∧
      ∀ k x, FromTest (K := c.F) (fun R _ _ => FrPt Xo c R) (fun φ y z => FrMap φ y z) ((u.U σ).un k x) := by
  rw [u.U_eq h]
  exact ⟨u.law σ h, nonempty_comp_of_isUnf h (u.law σ h) hN, u.chi σ h, fun k x =>
    @GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E _ _ _ H Dw l Xo c (CAt σ) _
      (inferInstanceAs (_root_.IsReduced ℂ)) _ _⟩

theorem UnfFam.xi_eq (u : UnfFam Xo c N ξ) (σ : c.F →+* ℂ) (k : (u.U σ).Comp) : ((u.U σ).X k).ξ0 = ξ := by
  by_cases h : Formalism.L2.PjFree.GoodEmb c σ
  · revert k
    rw [u.U_eq h]
    exact u.xi σ h
  · exact (u.isEmpty_comp h).elim k

theorem nonempty_unfFam (Xo : Moduli Dw l) (c : Coeff l) (hN : Dw.p + Dw.q = N) (h1 : 1 ≤ N)
    (hξ : ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ) (h0 : ξ ≠ 0)
    (him : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0) : Nonempty (UnfFam Xo c N ξ) := by
  have hξ' : ReciprocityTheory.ChartRestriction.G.FD.cc (-ξ) = -(-ξ) := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.cc at hξ ⊢
    rw [map_neg, hξ]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ) hξ' (neg_ne_zero.2 h0) N hN.symm
  have key := fun σ hσ => GlobalTheory.T.exists_frameUniformisation_prescribedSpace GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.QNorm.hasseNormSt
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ N ξ Gm φ
    (hN ▸ h1) hσ hξ him hφ
  choose U hU using key
  exact ⟨⟨U, fun σ h => (hU σ h).1, fun σ h => (hU σ h).2.2.1, fun σ h k => ((hU σ h).2.2.2.1 k).2⟩⟩

end Unif

end Free

def SysExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H),
    1 ≤ Dw.p + Dw.q → ∀ Xo : ∀ l : Level H, Moduli Dw l, SysEx Xo

structure Amb (D : D7) : Type where

  H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E

  d_eq : H.d = D.host.d

  rt_eq : (H.rt : D.host.E) = D.host.sqrtMinusD

  cmHost_rootComplex_eq_pm_sqrt : H.rt0 = D.host.φ₀ D.host.sqrtMinusD

def ambD (D : D7) : Amb D := ⟨hostOfRecord D, rfl, rfl, rfl⟩

variable {D : D7}

theorem Amb.cm (A : Amb D) (t : D.what₂.Tau) : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0 := by
  rw [A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt, tauEmb_sqrt]

theorem Amb.eq_ambD (A : Amb D) : A = ambD D := by
  obtain ⟨H, h1, h2, h3⟩ := A
  obtain rfl : H = hostOfRecord D := host_ext h1 (RingOfIntegers.ext h2) h3
  rfl

theorem Amb.im_neg_xi_neg (A : Amb D) (τ : D.host.E →+* ℂ) (hτ : τ (A.H.rt : D.host.E) = A.H.rt0) :
    (τ (-D.host.xi0)).im < 0 := by
  rw [A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt] at hτ
  have h := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
  rw [if_pos (GlobalTheory.Member.Inhab.sqrt_im_pos D), Int.cast_one, one_mul] at h
  simpa using h

theorem norm_embedding_xi_zero (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem Amb.nonempty_unfFam (A : Amb D) {Dw : Datum A.H} {l : Level A.H} (Xo : Moduli Dw l) (c : Coeff l) {N : ℕ}
    (hN : Dw.p + Dw.q = N) (h1 : 1 ≤ N) : Nonempty (UnfFam Xo c N (-D.host.xi0)) :=
  GlobalTheory.ShFam.nonempty_unfFam Xo c hN h1
    (by unfold ReciprocityTheory.ChartRestriction.G.FD.cc; rw [map_neg, conj_xi0_alt])
    (neg_ne_zero.2 (cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)) A.im_neg_xi_neg

structure Lv (A : Amb D) : Type where

  l : Level A.H

  good : ∀ p : ℕ, p.Prime → l.GoodAt p

  c : Coeff l

  e : D.what₂.LL ≃+* c.F

  e_emb : ∀ x, ((e x : c.F) : ℂ) = D.what₂.embLL x

  curve : GlobalTheory.CompRat.CurveOver A.H c.F l.M'

def Lv.primes {A : Amb D} (κ : Lv A) : Finset ℕ := κ.l.M'.primeFactors

def Lv.inK {A : Amb D} (κ : Lv A) (M : ℕ) : Prop := M ∣ κ.l.M'

def Lv.σ₀ {A : Amb D} (κ : Lv A) : κ.c.F →+* ℂ := κ.c.F.val.toRingHom

def fieldLL (D : D7) : IntermediateField ℚ ℂ := D.what₂.embLL.toRatAlgHom.fieldRange

theorem Lv.F_eq {A : Amb D} (κ : Lv A) : κ.c.F = fieldLL D := by
  ext z
  constructor
  · intro hz
    exact ⟨κ.e.symm ⟨z, hz⟩, (κ.e_emb _).symm.trans (congrArg Subtype.val (κ.e.apply_symm_apply ⟨z, hz⟩))⟩
  · rintro ⟨x, rfl⟩
    exact (κ.e_emb x) ▸ (κ.e x).2

def IsLargeFor (A : Amb D) (n : ℕ) : Prop := zeta n ∈ fieldLL D ∧ GlobalTheory.CompRat.CurveOver A.H (fieldLL D) n

def coeffOf (A : Amb D) (l : Level A.H) (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K) (hle : FO D ≤ K)
    (hz : zeta l.M' ∈ K) : Coeff l where
  F := K
  fin := hK
  conj τ a := hle (conj_mem_FO D τ a)
  zeta_mem := hz
  le := by
    rw [KA, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨A.cmHost_rootComplex_eq_pm_sqrt ▸ hle (phi0_mem_coeff_field D _), ?_⟩
    obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    have hM : l.M' ≠ 0 := (Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos).ne'
    have hk0 : (k : ℂ) ≠ 0 := by
      rintro h
      rw [Nat.cast_eq_zero.1 h] at hk
      exact hM hk
    have : zeta l.A = zeta l.M' ^ k := by
      rw [zeta, zeta, ← Complex.exp_nat_mul, hk, Nat.cast_mul]
      congr 1
      field_simp
    exact this ▸ pow_mem hz k

theorem exists_lv_iff (A : Amb D) (l : Level A.H) :
    (∃ κ : Lv A, κ.l = l) ↔ (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ IsLargeFor A l.M' := by
  constructor
  · rintro ⟨κ, rfl⟩
    exact ⟨κ.good, κ.F_eq ▸ κ.c.zeta_mem, κ.F_eq ▸ κ.curve⟩
  · rintro ⟨hg, hz, hc⟩
    let e := AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom
    exact ⟨⟨l, hg, coeffOf A l (fieldLL D) (LinearEquiv.finiteDimensional e.toLinearEquiv) (FO_le D) hz,
      e.toRingEquiv, fun _ => rfl, hc⟩, rfl⟩

structure Sig (A : Amb D) (N j : ℕ) : Type 1 where

  Dw : Datum A.H

  p_eq : Dw.p = j

  rank_eq : Dw.p + Dw.q = N

  two_le : 2 ≤ N

  Xo : ∀ l : Level A.H, Moduli Dw l

  sys : Sys Xo

  tor : TorSys sys

theorem exists_sig (A : Amb D) {N j : ℕ} (hN : 2 ≤ N) (Dw : Datum A.H) (hp : Dw.p = j) (hq : Dw.p + Dw.q = N)
    (h : ∀ Xo : ∀ l : Level A.H, Moduli Dw l, SysEx Xo) : ∃ S : Sig A N j, S.Dw = Dw := by
  have hX := fun l => GlobalTheory.Moduli.moduli_scheme_exists _ A.H Dw l (by omega)
  obtain ⟨s, ⟨t⟩⟩ := h fun l => (hX l).some
  exact ⟨⟨Dw, hp, hq, hN, _, s, t⟩, rfl⟩

theorem Amb.exists_datum (A : Amb D) (p q : ℕ) : ∃ Dw : Datum A.H, Dw.p = p ∧ Dw.q = q :=
  (GlobalTheory.CompRat.exists_splitLat_of_signature _ A.H p q
    (GlobalTheory.RankOneDatum.exists_datum_of_rt D A.H A.rt_eq A.cmHost_rootComplex_eq_pm_sqrt)).imp fun _ h => ⟨h.1, h.2.1⟩

structure FinalTheorems {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : Type 1 where

  unif : UnfFam (S.Xo κ.l) κ.c N (-D.host.xi0)

theorem nonempty_src_of_sig {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : Nonempty (FinalTheorems S κ) :=
  (A.nonempty_unfFam (S.Xo κ.l) κ.c S.rank_eq (one_le_two.trans S.two_le)).map FinalTheorems.mk

namespace FinalTheorems

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

abbrev Xo (_s : FinalTheorems S κ) : Moduli S.Dw κ.l := S.Xo κ.l

def Ygl (_s : FinalTheorems S κ) : Model (S.Xo κ.l) κ.c (algebraMap (𝓞 κ.c.F) κ.c.F) := S.tor.Ygl κ.l κ.c κ.good

def T (s : FinalTheorems S κ) : TorModel s.Ygl := S.tor.T κ.l κ.c κ.good

def U (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) : Formalism.L2.PjFree.Unf (S.Xo κ.l) κ.c σ N := s.unif.U σ

variable (s : FinalTheorems S κ)

abbrev Comp : Type := (s.U κ.σ₀).Comp

theorem glob : IsGlob S.sys.Y κ.good s.Ygl := S.tor.glob κ.l κ.c κ.good

theorem isRec : IsRecTor s.T := S.tor.isRec κ.l κ.c κ.good

theorem unf (σ : κ.c.F →+* ℂ) (h : Formalism.L2.PjFree.GoodEmb κ.c σ) :
    Formalism.L2.PjFree.IsUnf (s.U σ) ∧ Nonempty (s.U σ).Comp ∧ (∀ k la γ, ((s.U σ).X k).χ la γ = 1) ∧
      ∀ k x, FromTest (K := κ.c.F) (fun R _ _ => FrPt (S.Xo κ.l) κ.c R) (fun φ y z => FrMap φ y z) ((s.U σ).un k x) :=
  s.unif.unf (one_le_two.trans S.two_le) σ h

theorem xi_eq (σ : κ.c.F →+* ℂ) (k : (s.U σ).Comp) : ((s.U σ).X k).ξ0 = -D.host.xi0 := s.unif.xi_eq σ k

theorem xiAbs (σ : κ.c.F →+* ℂ) (k : (s.U σ).Comp) (τ : D.host.E →+* ℂ) : ‖τ ((s.U σ).X k).ξ0‖ = xiR D := by
  rw [s.xi_eq, map_neg, norm_neg, norm_embedding_xi_zero]

theorem gen : GenFrEx s.Xo κ.c := (GlobalTheory.Reg.genFrEx_and_genFromTest _ A.H S.Dw κ.l (S.Xo κ.l) κ.c).1

theorem geo : FnAlgClosed s.Xo κ.c :=
  GeomComp.fnAlgClosed_of_curveOver _ _ ((one_le_two.trans S.two_le).trans S.rank_eq.ge)
    (GlobalTheory.RankOneDatum.exists_datum_of_rt D A.H A.rt_eq A.cmHost_rootComplex_eq_pm_sqrt) κ.curve

theorem trans {κ₂ : Lv A} (s₂ : FinalTheorems S κ₂) (h : κ.l.Dvd κ₂.l) (b : 𝓞 κ.c.F →+* 𝓞 κ₂.c.F)
    (hb : ∀ x, (((b x : 𝓞 κ₂.c.F) : κ₂.c.F) : ℂ) = ((x : κ.c.F) : ℂ)) : IsTorTrans s.T s₂.T b :=
  S.tor.trans _ _ _ _ _ _ b h hb

end FinalTheorems

def IsDatOf {A : Amb D} (S : letI := D.host.cmStar; HSpace D.host.E) (Dw : Datum A.H) : Prop :=
  letI := D.host.cmStar
  ∃ φ : Dw.La →ₗ[𝓞 D.host.E] S.V, Function.Injective φ ∧
    LinearMap.range φ = Submodule.span (𝓞 D.host.E)
      {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ S.L0, v = a • x} ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = -Algebra.trace ℚ D.host.E (D.host.xi0 * S.hD (φ x) (φ y))

theorem neg_trace_hD (S : letI := D.host.cmStar; HSpace D.host.E) :
    letI := D.host.cmStar
    ∀ x y : S.V, -Algebra.trace ℚ D.host.E (D.host.xi0 * S.hD x y) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * S.hT x y) := by
  letI := D.host.cmStar
  intro x y
  have hh : IsCMField.complexConj D.host.E (S.hT x y) = S.hT y x := LinearMap.isSymm_def.1 S.herm x y
  rw [← Formalism.L2.Pj.trace_cc D (D.host.xi0 * S.hT x y), map_mul (IsCMField.complexConj D.host.E), conj_xi0_alt, hh, neg_mul, map_neg]
  rfl

theorem IsDatOf.isDatW {A : Amb D} {j : ℕ} {Dw : Datum A.H} (h : IsDatOf (letI := D.host.cmStar; D.sp.W j) Dw)
    (hp : Dw.p = (D.R.sigW j).1) (hq : Dw.q = (D.R.sigW j).2) : IsDatW D j Dw := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  refine ⟨hp, hq, φ, 1, h1, h2, fun x y => ?_⟩
  rw [h3, neg_trace_hD]
  simp

theorem exists_isDatOf_of_inR (A : Amb D) {j : ℕ} (hj : InR D j) :
    ∃ Dw : Datum A.H, IsDatOf (letI := D.host.cmStar; D.sp.W j) Dw ∧ Dw.p = (D.R.sigW j).1 ∧ Dw.q = (D.R.sigW j).2 := by
  rw [A.eq_ambD]
  have hI := datInt_holds D j
  refine ⟨datumOf D j hI ⟨efW_unimod_holds D j _, latW_rank D j hj, datDom_holds D j hj _⟩,
    ⟨(latW D j).subtype, Submodule.injective_subtype _, Submodule.range_subtype _, fun x y => ?_⟩, rfl, rfl⟩
  rw [neg_trace_hD]
  show ((sgnW D j * intForm (efQ D j) hI x y : ℤ) : ℚ) = _
  rw [GlobalTheory.Member.Inhab.sgnW_eq_one D j hj, one_mul]
  exact intForm_cast (efQ D j) hI x y

open Formalism.L2.Geo (datW datW_N datW_j) in

structure SrcFam (A : Amb D) : Type 1 where

  sig : ∀ N j : ℕ, 2 ≤ N → j ≤ N → Sig A N j

  src : ∀ N j hN hj (κ : Lv A), FinalTheorems (sig N j hN hj) κ

  κg : Lv A

  κg_M : κg.l.M = D.host.g 0 * D.host.g 1

  κg_A : κg.l.A = 1

  κs : Lv A

  κs_M : κs.l.M = κg.l.M ∧ κs.l.Mb = κg.l.Mb

  κs_A : ∃ c : ℕ, 0 < c ∧ κs.l.A = 15 ^ c

  dat : ∀ j, InR D j → IsDatW D j (sig _ _ (datW D κg j).two_le (datW D κg j).j_le).Dw

  cs : Coeff κg.l

  eO : 𝓞 cs.F ≃+* D.what₂.O

  eO_emb : ∀ x : 𝓞 cs.F, D.what₂.embLL (D.what₂.OtoLL (eO x)) = ((x : cs.F) : ℂ)

  Us : ∀ j, UnfFam ((sig _ _ (datW D κg j).two_le (datW D κg j).j_le).Xo κg.l) cs D.R.r (-D.host.xi0)

namespace SrcFam

open Formalism.L2.Geo (datW datW_N datW_j)

variable {A : Amb D} (F : SrcFam A)

abbrev «at» (w : Formalism.L2.Geo.Dat D (Lv A)) : FinalTheorems (F.sig w.N w.j w.two_le w.j_le) w.κ :=
  F.src w.N w.j w.two_le w.j_le w.κ

def Pinned (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) (c : ℕ) : Prop :=
  F.κg.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ∧ F.κs.l.A = 15 ^ c

theorem κg_dvd_κs : F.κg.l.Dvd F.κs.l := ⟨F.κs_M.1 ▸ dvd_rfl, F.κs_M.2.le, F.κg_A ▸ one_dvd _⟩

abbrev sigW (j : ℕ) : Sig A (datW D F.κg j).N (datW D F.κg j).j :=
  F.sig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le

def par : Par D where
  H := A.H
  l := F.κg.l
  c := F.cs
  Dw j := (F.sigW j).Dw
  Xo j := (F.sigW j).Xo F.κg.l
  eO := F.eO

theorem pins : F.par.Pins := ⟨⟨A.d_eq, A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt, A.cm⟩, ⟨F.κg_M, F.κg_A⟩, F.eO_emb, F.dat⟩

theorem cs_le (κ : Lv A) : F.cs.F ≤ κ.c.F := by
  intro z hz
  haveI := F.cs.fin
  haveI : NumberField F.cs.F := {}
  obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 F.cs.F) (⟨z, hz⟩ : F.cs.F)
  have key : ∀ x : 𝓞 F.cs.F, ((x : F.cs.F) : ℂ) ∈ κ.c.F := fun x => by
    rw [κ.F_eq, ← F.eO_emb]
    exact ⟨_, rfl⟩
  have e : z = ((x : F.cs.F) : ℂ) / ((y : F.cs.F) : ℂ) := (congrArg Subtype.val h).symm
  exact e ▸ div_mem (key x) (key y)

def Ts (N j : ℕ) (hN : 2 ≤ N) (hj : j ≤ N) : TorModel ((F.sig N j hN hj).tor.Ygl F.κg.l F.cs F.κg.good) :=
  (F.sig N j hN hj).tor.T F.κg.l F.cs F.κg.good


def Upar (j : ℕ) (σ : F.par.c.F →+* ℂ) : Unf (F.par.Xo j) F.par.c σ D.R.r :=
  { Comp := ((F.Us j).U σ).Comp, fin := ((F.Us j).U σ).fin, X := ((F.Us j).U σ).X, un := ((F.Us j).U σ).un }


end SrcFam

theorem exists_datum_tied (A : Amb D) {N i : ℕ} (hi : i ≤ N) : ∃ Dw : Datum A.H, Dw.p = i ∧ Dw.p + Dw.q = N ∧
    ∀ j, InR D j → N = D.R.r → i = (D.R.sigW j).1 → IsDatW D j Dw := by
  by_cases h : ∃ j, InR D j ∧ N = D.R.r ∧ i = (D.R.sigW j).1
  · obtain ⟨j, hj, rfl, rfl⟩ := h
    obtain ⟨Dw, h1, h2, h3⟩ := exists_isDatOf_of_inR A hj
    refine ⟨Dw, h2, by rw [h2, h3, Formalism.L2.Geo.sigW_sum D hj.1 hj.2], fun j' hj' _ e => ?_⟩
    obtain rfl : j = j' := by
      have := hj.1
      have := hj'.1
      simp only [Ranks.sigW] at e
      omega
    exact h1.isDatW h2 h3
  · obtain ⟨Dw, h1, h2⟩ := A.exists_datum i (N - i)
    exact ⟨Dw, h1, by omega, fun j hj e e' => (h ⟨j, hj, e, e'⟩).elim⟩

open Formalism.L2.Geo (datW datW_N datW_j) in

theorem exists_srcFam (A : Amb D)
    (hS : ∀ Dw : Datum A.H, 2 ≤ Dw.p + Dw.q → ∀ Xo : ∀ l : Level A.H, Moduli Dw l, SysEx Xo)
    (hF : OFull D) (hz : OZeta D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hpb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) (ex : ℕ) (hex : 0 < ex)
    (hg : IsLargeFor A (D.host.g 0 * D.host.g 1)) (hs : IsLargeFor A (Nat.lcm (D.host.g 0 * D.host.g 1) (15 ^ ex))) :
    ∃ F : SrcFam A, F.Pinned pb ex := by
  obtain ⟨l, ⟨hM, hA⟩, hMb⟩ : ∃ l : Level A.H, (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
      l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
    rw [A.eq_ambD]
    exact levelPb_exists D pb hpb
  have good : ∀ l' : Level A.H, l'.M = D.host.g 0 * D.host.g 1 → ∀ p : ℕ, p.Prime → l'.GoodAt p := fun l' h p _ =>
    GlobalTheory.PinNum.goodAt_of_two_primes l' (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne h p
  have hM' : l.M' = D.host.g 0 * D.host.g 1 := by rw [Level.M', hM, hA, Nat.lcm_one_right]
  obtain ⟨κg, rfl⟩ := (exists_lv_iff A l).2 ⟨good l hM, hM' ▸ hg⟩
  obtain ⟨κs, hκs⟩ := (exists_lv_iff A { κg.l with A := 15 ^ ex, A_pos := by positivity }).2
    ⟨good _ hM, by rw [Level.M']; exact hM ▸ hs⟩
  have hsig : ∀ N i : ℕ, 2 ≤ N → i ≤ N → ∃ S : Sig A N i,
      ∀ j, InR D j → N = D.R.r → i = (D.R.sigW j).1 → IsDatW D j S.Dw := by
    intro N i hN hi
    obtain ⟨Dw, h1, h2, h3⟩ := exists_datum_tied A hi
    obtain ⟨S, rfl⟩ := exists_sig A hN Dw h1 h2 (hS Dw (h2 ▸ hN))
    exact ⟨S, h3⟩
  choose sig hsig using hsig
  let cs : Coeff κg.l := coeffOf A κg.l (FO D) inferInstance le_rfl (by
    obtain ⟨y, hy⟩ := hz
    rw [hM', ← hy]
    exact phiO_mem_FO D y)
  exact ⟨{ sig := sig, src := fun N j hN hj κ => (nonempty_src_of_sig _ κ).some
           κg := κg, κg_M := hM, κg_A := hA
           κs := κs, κs_M := by rw [hκs]; exact ⟨rfl, rfl⟩
           κs_A := ⟨ex, hex, by rw [hκs]⟩
           dat := fun j hj => hsig _ _ _ _ j hj (datW_N D κg j) (datW_j D κg hj.1 hj.2)
           cs := cs, eO := eOf D hF, eO_emb := eOf_spec D hF
           Us := fun j => (A.nonempty_unfFam _ cs ((sig _ _ _ _).rank_eq.trans (datW_N D κg j))
             (one_le_two.trans (Formalism.L2.Geo.two_le_r D))).some }, hMb, congrArg Level.A hκs⟩

end GlobalTheory.ShFam
end
end
