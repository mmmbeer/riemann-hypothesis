import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicWedgeNormPeriods
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PolarizationCorrespondence
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence

namespace GlobalTheory.KeyInputCompare

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem epsScaleR_eq (c : R) : epsScaleR c = epsHom (RingHom.id R) c := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

theorem epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := by
  rw [epsScaleR_eq]; rfl

end Dual

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ v ∈ lieSub G := by
  change _ ↔ epsZero R ≫ v = η[G]
  constructor
  · intro h; ext1; exact h
  · intro h; exact congrArg CommaMorphism.left h

theorem linComb_val {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) :
    (linComb c v).1 = (List.ofFn fun i => epsScale (c i) ≫ (v i).1).prod := by
  rw [linComb, Subgroup.val_list_prod, List.map_ofFn]
  rfl

theorem isLieComb_iff_prod {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => epsScale (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => epsScale (c i) ≫ v i := by
      funext i; ext1; rw [hu, Over.comp_left, epsScale_left]
    rw [this]
  · rintro rfl
    exact ⟨_, fun i => by rw [Over.comp_left, epsScale_left], rfl⟩

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) (w : epsR R ⟶ G) :
    IsLieComb c (fun i => (v i).1) w ↔ w = (linComb c v).1 := by
  rw [isLieComb_iff_prod, linComb_val]

theorem isLieBasis_val_iff {n : ℕ} (v : Fin n → Tan G) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis (fun i => (v i).1) ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence.IsLieBasis v := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence.IsLieBasis, Function.bijective_iff_existsUnique]
  constructor
  · rintro ⟨-, h⟩ w
    have := h w.1 ((isTangent_iff _).2 w.2)
    simp only [isLieComb_iff] at this
    simpa only [Subtype.ext_iff, eq_comm (b := w.1)] using this
  · intro h
    refine ⟨fun i => (isTangent_iff _).2 (v i).2, fun w hw => ?_⟩
    have := h ⟨w, (isTangent_iff _).1 hw⟩
    simp only [isLieComb_iff]
    simpa only [Subtype.ext_iff, eq_comm (b := w)] using this

end Lie

section Input

variable {R R' : Type} [CommRing R] [CommRing R']

def keyInEquiv (R : Type) [CommRing R] : KeyIn R ≃ KeyInput R where
  toFun x :=
    { P := x.P, dim_pos := x.g_pos, rig := x.rig, rig_gen := x.rig_gen, th := x.th, th_ne := x.th_ne
      b := fun i => ⟨x.v i, (isTangent_iff _).1 (x.basis.1 i)⟩
      b_basis := (isLieBasis_val_iff _).1 x.basis }
  invFun y :=
    { P := y.P, g_pos := y.dim_pos, rig := y.rig, rig_gen := y.rig_gen, th := y.th, th_ne := y.th_ne
      v := fun i => (y.b i).1
      basis := (isLieBasis_val_iff _).2 y.b_basis }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem keyInEquiv_P (x : KeyIn R) : (keyInEquiv R x).P = x.P := rfl
@[simp] theorem keyInEquiv_rig (x : KeyIn R) : (keyInEquiv R x).rig = x.rig := rfl
@[simp] theorem keyInEquiv_th (x : KeyIn R) : (keyInEquiv R x).th = x.th := rfl
@[simp] theorem keyInEquiv_b (x : KeyIn R) (i : Fin x.P.g) : ((keyInEquiv R x).b i).1 = x.v i := rfl
@[simp] theorem keyInEquiv_symm_P (y : KeyInput R) : ((keyInEquiv R).symm y).P = y.P := rfl
@[simp] theorem keyInEquiv_symm_rig (y : KeyInput R) : ((keyInEquiv R).symm y).rig = y.rig := rfl
@[simp] theorem keyInEquiv_symm_th (y : KeyInput R) : ((keyInEquiv R).symm y).th = y.th := rfl
@[simp] theorem keyInEquiv_symm_v (y : KeyInput R) (i : Fin y.P.g) :
    ((keyInEquiv R).symm y).v i = (y.b i).1 := rfl

end Input

end GlobalTheory.KeyInputCompare
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence GlobalTheory.IndefiniteRowSideFullHecke.CubicWedgeNormPeriods GlobalTheory.KeyInputCompare

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyFormulaCompare

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def Same (u : HolUnif A L g) (F : Unif A L g) : Prop :=
  F.exp = u.ex ∧ ∀ i z h, F.fr i z h = u.fr i z

namespace Same

variable {u : HolUnif A L g} {F : Unif A L g} (h : Same u F)
include h

end Same

end Unif

section Analytic

end Analytic

section Principal

theorem tangent_bijective (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) :
    (∀ v, Geo.Tor.IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, Geo.Tor.IsTangent v ∧ u.IsDiff w v := by
  obtain ⟨u₀, H₀, χ₀, E₀, -, -, hv, hw, -⟩ := thetaUnifAV_closed x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex
    u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    UnifCompare.isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨fun v hv' => ?_, fun w => ?_⟩
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

theorem det_ne_zero (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) : W.det ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := tangent_bijective x u
  refine ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 fun w => ?_)).ne_zero
  obtain ⟨v, hv, hd⟩ := (h₂ w).exists
  obtain ⟨c, hc⟩ := (x.basis.2 v hv).exists
  exact ⟨c, (Matrix.vecMul_eq_sum c W).trans ((h₁ v hv).unique
    (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W x.v c v x.basis.1 hW hc) hd)⟩

end Principal

section Clauses

abbrev RuleIn : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

def ruleEquiv : RuleIn ≃ Rule where
  toFun κ := fun K _ _ y => κ K ((keyInEquiv K).symm y)
  invFun ka := fun K _ _ x => ka K (keyInEquiv K x)
  left_inv _ := rfl
  right_inv _ := rfl

variable (κ : RuleIn)

end Clauses

end GlobalTheory.KeyFormulaCompare
end
end
