import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped TensorProduct

namespace GlobalTheory.ProjVar

variable {F : Type} [Field F]

def CxExt (σ : F →+* ℂ) (A : Type) [CommRing A] [Algebra F A] : Type :=
  letI := σ.toAlgebra
  ℂ ⊗[F] A

namespace CxExt

variable (σ : F →+* ℂ) {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

def Tensor (F : Type) [Field F] [Algebra F ℂ] (A : Type) [CommRing A] [Algebra F A] : Type := ℂ ⊗[F] A

instance {_ : Algebra F ℂ} : CommRing (Tensor F A) := inferInstanceAs (CommRing (ℂ ⊗[F] A))

instance {_ : Algebra F ℂ} : Algebra ℂ (Tensor F A) := inferInstanceAs (Algebra ℂ (ℂ ⊗[F] A))

instance : CommRing (CxExt σ A) :=
  inferInstanceAs (CommRing (@Tensor F _ σ.toAlgebra A _ _))

instance : Algebra ℂ (CxExt σ A) :=
  inferInstanceAs (Algebra ℂ (@Tensor F _ σ.toAlgebra A _ _))

def of : A →+* CxExt σ A :=
  letI := σ.toAlgebra
  (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := A)).toRingHom

theorem of_algebraMap (a : F) : of σ (algebraMap F A a) = algebraMap ℂ (CxExt σ A) (σ a) := by
  letI := σ.toAlgebra
  first
  | exact (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := A)).commutes a
  | (show (1 : ℂ) ⊗ₜ[F] algebraMap F A a = σ a ⊗ₜ[F] (1 : A)
     rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
     rfl)

theorem of_smul (a : F) (x : A) : of σ (a • x) = σ a • of σ x := by
  rw [Algebra.smul_def, map_mul, of_algebraMap, ← Algebra.smul_def]

theorem of_injective : Function.Injective (of σ : A → CxExt σ A) := by
  letI := σ.toAlgebra
  exact Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := A) σ.injective

private theorem complex_smul_of_eq (c : ℂ) (a : A) :
    c • of σ a = (letI := σ.toAlgebra; (c ⊗ₜ[F] a : ℂ ⊗[F] A) : CxExt σ A) := by
  letI := σ.toAlgebra
  first
  | (show c • ((1 : ℂ) ⊗ₜ[F] a) = c ⊗ₜ[F] a
     rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  | (show c • ((1 : ℂ) ⊗ₜ[F] a) = c ⊗ₜ[F] a
     simp [TensorProduct.smul_tmul'])

variable {σ} in

@[elab_as_elim] theorem induction {P : CxExt σ A → Prop} (x : CxExt σ A)
    (smul : ∀ (c : ℂ) (a : A), P (c • of σ a)) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  letI := σ.toAlgebra
  refine TensorProduct.induction_on (R := F) (M := ℂ) (N := A) (motive := P) x ?_ ?_ ?_
  · have h := smul 0 0
    rw [zero_smul] at h
    exact h
  · intro c a
    exact (complex_smul_of_eq σ c a) ▸ smul c a
  · intro x y hx hy
    exact add x y hx hy

variable {σ} in

def lift {B : Type} [CommRing B] [Algebra ℂ B] (φ : A →+* B)
    (h : ∀ a, φ (algebraMap F A a) = algebraMap ℂ B (σ a)) : CxExt σ A →ₐ[ℂ] B :=
  letI := σ.toAlgebra
  letI : Algebra F B := ((algebraMap ℂ B).comp σ).toAlgebra
  haveI : IsScalarTower F ℂ B := .of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId ℂ B) ({ φ with commutes' := h } : A →ₐ[F] B)
    fun _ _ => Commute.all _ _

variable {σ} in

@[simp] theorem lift_of {B : Type} [CommRing B] [Algebra ℂ B] (φ : A →+* B)
    (h : ∀ a, φ (algebraMap F A a) = algebraMap ℂ B (σ a)) (a : A) : lift φ h (of σ a) = φ a := by
  first
  | (change (Algebra.ofId ℂ B) 1 * φ a = φ a
     rw [map_one, one_mul])
  | (simp only [lift, of]
     erw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
     simp)

def map (f : A →ₐ[F] A') : CxExt σ A →ₐ[ℂ] CxExt σ A' :=
  lift ((of σ).comp f.toRingHom) fun a => (congrArg (of σ) (f.commutes a)).trans (of_algebraMap σ a)

@[simp] theorem map_of (f : A →ₐ[F] A') (a : A) : map σ f (of σ a) = of σ (f a) := by
  first
  | exact lift_of _ _ a
  | simp [map, lift_of]

theorem map_injective {f : A →ₐ[F] A'} (hf : Function.Injective f) :
    Function.Injective (map σ f) := by
  letI := σ.toAlgebra
  have hk : ∀ x : CxExt σ A,
      map σ f x = (LinearMap.lTensor ℂ f.toLinearMap : ℂ ⊗[F] A →ₗ[F] ℂ ⊗[F] A') x := by
    intro x
    refine CxExt.induction (P := fun x =>
      map σ f x = (LinearMap.lTensor ℂ f.toLinearMap : ℂ ⊗[F] A →ₗ[F] ℂ ⊗[F] A') x) x
      (fun c a => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, map_of, complex_smul_of_eq, complex_smul_of_eq, LinearMap.lTensor_tmul]
      rfl
    · rw [map_add, hx, hy]
      exact (map_add (LinearMap.lTensor ℂ f.toLinearMap : ℂ ⊗[F] A →ₗ[F] ℂ ⊗[F] A') x y).symm
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) f.toLinearMap hf
  intro x y hxy
  exact hinj (by rw [← hk, ← hk]; exact hxy)

theorem exists_components (f : A →ₐ[F] A') (x : CxExt σ A) :
    ∃ (ι : Type) (s : Finset ι) (e : ι → ℂ) (π : ι → CxExt σ A → A) (π' : ι → CxExt σ A' → A'),
      x = ∑ i ∈ s, e i • of σ (π i x) ∧ (∀ i y, π' i (map σ f y) = f (π i y)) ∧
      ∀ i y a, π' i (y * of σ a) = π' i y * a := by
  letI := σ.toAlgebra
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Basis.ofVectorSpaceIndex F ℂ) F ℂ) := ⟨Module.Basis.ofVectorSpace F ℂ⟩
  refine ⟨Module.Basis.ofVectorSpaceIndex F ℂ, (TensorProduct.equivFinsuppOfBasisLeft (N := A) b x).support,
    fun i => b i, fun i y => TensorProduct.equivFinsuppOfBasisLeft (N := A) b y i,
    fun i y => TensorProduct.equivFinsuppOfBasisLeft (N := A') b y i, ?_, ?_, ?_⟩
  · have h2 : ∀ v : Module.Basis.ofVectorSpaceIndex F ℂ →₀ A,
        (TensorProduct.equivFinsuppOfBasisLeft (N := A) b).symm v = v.sum fun i n => b i ⊗ₜ[F] n := by
      intro v
      exact TensorProduct.equivFinsuppOfBasisLeft_symm_apply b v
    have h3 := LinearEquiv.symm_apply_apply (TensorProduct.equivFinsuppOfBasisLeft (N := A) b) x
    rw [h2, Finsupp.sum] at h3
    simp only [complex_smul_of_eq]
    exact h3.symm
  · intro i y
    refine CxExt.induction (P := fun y => TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft (N := A) b y i)) y (fun c a => ?_) (fun y z hy hz => ?_)
    · rw [map_smul, map_of, complex_smul_of_eq, complex_smul_of_eq, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      first
      | exact (map_smul f _ _).symm
      | simp
    · have e1 : TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f (y + z)) = TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f y) + TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f z) := by
        rw [map_add]
        exact map_add _ _ _
      have e2 : TensorProduct.equivFinsuppOfBasisLeft (N := A) b (y + z) = TensorProduct.equivFinsuppOfBasisLeft (N := A) b y + TensorProduct.equivFinsuppOfBasisLeft (N := A) b z := map_add _ _ _
      rw [e1, e2, Finsupp.add_apply, Finsupp.add_apply, hy, hz, map_add]
  · intro i y a
    refine CxExt.induction (P := fun y => TensorProduct.equivFinsuppOfBasisLeft (N := A') b (y * of σ a : CxExt σ A') i =
      TensorProduct.equivFinsuppOfBasisLeft (N := A') b y i * a) y (fun c a' => ?_) (fun y z hy hz => ?_)
    · rw [smul_mul_assoc, ← map_mul, complex_smul_of_eq, complex_smul_of_eq,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, smul_mul_assoc]
    · have e1 : TensorProduct.equivFinsuppOfBasisLeft (N := A') b ((y + z) * of σ a : CxExt σ A') = TensorProduct.equivFinsuppOfBasisLeft (N := A') b (y * of σ a : CxExt σ A') + TensorProduct.equivFinsuppOfBasisLeft (N := A') b (z * of σ a : CxExt σ A') := by
        rw [add_mul]
        exact map_add _ _ _
      have e2 : TensorProduct.equivFinsuppOfBasisLeft (N := A') b (y + z) = TensorProduct.equivFinsuppOfBasisLeft (N := A') b y + TensorProduct.equivFinsuppOfBasisLeft (N := A') b z := map_add _ _ _
      rw [e1, e2, Finsupp.add_apply, Finsupp.add_apply, hy, hz, add_mul]

end CxExt

namespace Var

variable (Y : Var F) (σ : F →+* ℂ)

abbrev pts : Type := CxPts Y.str σ

instance compactSpace_pts : CompactSpace (Y.pts σ) := CxPts.compactSpace σ Y.isProjOver

instance secondCountable_pts : SecondCountableTopology (Y.pts σ) :=
  CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver

instance t2Space_complexPointsOfProjVariety : T2Space (Y.pts σ) := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver

abbrev an : AnRead Y.str σ Y.dim := AnRead.all Y.str σ Y.dim

abbrev FnC : Type := CxExt σ Y.Fn

def cx : Y.Fn →+* Y.FnC σ := CxExt.of σ

theorem cx_smul (a : F) (f : Y.Fn) : Y.cx σ (a • f) = σ a • Y.cx σ f :=
  CxExt.of_smul σ a f

theorem cx_injective : Function.Injective (Y.cx σ) :=
  CxExt.of_injective σ

instance nontrivial_FnC : Nontrivial (Y.FnC σ) := (Y.cx_injective σ).nontrivial

instance algebraStalk (x : Y.X) : Algebra F (Y.X.presheaf.stalk x) :=
  ((Y.X.presheaf.germ ⊤ x trivial).hom.comp (algX Y.str ⊤)).toAlgebra

def stalkIncl (x : Y.X) : Y.X.presheaf.stalk x →ₐ[F] Y.Fn :=
  { algebraMap (Y.X.presheaf.stalk x) Y.X.functionField with
    commutes' := fun a => algebraMap_germ (U := ⊤) trivial (algX Y.str ⊤ a) }

variable {Y σ}

def base (y : Y.pts σ) : Y.X := y.1 (IsLocalRing.closedPoint ℂ)

theorem mem_ptsIn_iff {y : Y.pts σ} {U : Y.X.Opens} : y ∈ ptsIn Y.str σ U ↔ base y ∈ U :=
  CxPts.mem_ptsIn

def evStalk (y : Y.pts σ) : Y.X.presheaf.stalk (base y) →+* ℂ := (Scheme.stalkClosedPointTo y.1).hom

theorem evStalk_germ {y : Y.pts σ} {U : Y.X.Opens} (h : base y ∈ U) (a : Γ(Y.X, U)) :
    evStalk y (Y.X.presheaf.germ U _ h a) = ev Y.str σ U a y := by
  have hy : ⊤ ≤ y.1 ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y.1 h).ge
  have e := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U h)
  refine e.trans ?_
  show _ = valR y.1 U a
  rw [valR, dif_pos hy]
  rfl

theorem evStalk_ne_zero_iff {y : Y.pts σ} (a : Y.X.presheaf.stalk (base y)) :
    evStalk y a ≠ 0 ↔ IsUnit a := by
  haveI : IsLocalHom (evStalk y) := Scheme.isLocalHom_stalkClosedPointTo y.1
  rw [← isUnit_iff_ne_zero]
  exact isUnit_map_iff (evStalk y) a

def germIncl (y : Y.pts σ) : CxExt σ (Y.X.presheaf.stalk (base y)) →ₐ[ℂ] Y.FnC σ :=
  CxExt.map σ (Y.stalkIncl (base y))

def germEv (y : Y.pts σ) : CxExt σ (Y.X.presheaf.stalk (base y)) →ₐ[ℂ] ℂ :=
  CxExt.lift (evStalk y) fun a => (evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top a)

theorem germIncl_injective (y : Y.pts σ) : Function.Injective (germIncl y) :=
  CxExt.map_injective σ (IsFractionRing.injective (Y.X.presheaf.stalk (base y)) Y.X.functionField)

def HasVal (y : Y.pts σ) (f : Y.FnC σ) (c : ℂ) : Prop :=
  ∃ a b, germEv y b ≠ 0 ∧ germIncl y b * f = germIncl y a ∧ germEv y a = germEv y b * c

def RegC (y : Y.pts σ) (f : Y.FnC σ) : Prop := ∃ c, HasVal y f c

open Classical in

def val (y : Y.pts σ) (f : Y.FnC σ) : ℂ := if h : RegC y f then h.choose else 0

variable {y : Y.pts σ} {f f' : Y.FnC σ} {c c' : ℂ}

theorem HasVal.unique (h : HasVal y f c) (h' : HasVal y f c') : c = c' := by
  obtain ⟨a, b, hb, hf, ha⟩ := h
  obtain ⟨a', b', hb', hf', ha'⟩ := h'
  have key : germIncl y (b * a') = germIncl y (b' * a) := by
    simp only [map_mul]
    linear_combination (germIncl y b') * hf - (germIncl y b) * hf'
  have e := congrArg (germEv y) (germIncl_injective y key)
  simp only [map_mul] at e
  rw [ha, ha'] at e
  apply mul_left_cancel₀ (mul_ne_zero hb hb')
  linear_combination -e

theorem HasVal.regC (h : HasVal y f c) : RegC y f := ⟨c, h⟩

theorem RegC.hasVal (h : RegC y f) : HasVal y f (val y f) := by
  rw [val, dif_pos h]
  exact h.choose_spec

theorem HasVal.val_eq (h : HasVal y f c) : val y f = c := h.regC.hasVal.unique h

theorem val_of_not_regC (h : ¬ RegC y f) : val y f = 0 := by
  rw [val, dif_neg h]

theorem regC_of_val_ne_zero (h : val y f ≠ 0) : RegC y f := by
  by_contra h'
  exact h (val_of_not_regC h')

theorem hasVal_germIncl (a) : HasVal y (germIncl y a) (germEv y a) := ⟨a, 1, by simp, by simp, by simp⟩

theorem hasVal_algebraMap (c : ℂ) : HasVal y (algebraMap ℂ _ c) c := ⟨algebraMap ℂ _ c, 1, by simp, by simp, by simp⟩

theorem hasVal_one : HasVal y 1 1 := ⟨1, 1, by simp, by simp, by simp⟩

theorem hasVal_zero : HasVal y 0 0 := ⟨0, 1, by simp, by simp, by simp⟩

theorem HasVal.add (h : HasVal y f c) (h' : HasVal y f' c') : HasVal y (f + f') (c + c') := by
  obtain ⟨a, b, hb, hf, ha⟩ := h
  obtain ⟨a', b', hb', hf', ha'⟩ := h'
  refine ⟨a * b' + a' * b, b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [map_mul, map_add]
    linear_combination (germIncl y b') * hf + (germIncl y b) * hf'
  · simp only [map_mul, map_add]
    linear_combination (germEv y b') * ha + (germEv y b) * ha'

theorem HasVal.mul (h : HasVal y f c) (h' : HasVal y f' c') : HasVal y (f * f') (c * c') := by
  obtain ⟨a, b, hb, hf, ha⟩ := h
  obtain ⟨a', b', hb', hf', ha'⟩ := h'
  refine ⟨a * a', b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [map_mul]
    linear_combination (germIncl y b' * f') * hf + (germIncl y a) * hf'
  · simp only [map_mul]
    linear_combination (germEv y a') * ha + (germEv y b * c) * ha'

theorem HasVal.smul (a : ℂ) (h : HasVal y f c) : HasVal y (a • f) (a * c) := by
  rw [Algebra.smul_def]
  exact (hasVal_algebraMap (y := y) a).mul h

theorem HasVal.neg (h : HasVal y f c) : HasVal y (-f) (-c) := by
  have e := h.smul (-1)
  rwa [neg_one_smul, neg_one_mul] at e

theorem HasVal.sub (h : HasVal y f c) (h' : HasVal y f' c') : HasVal y (f - f') (c - c') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add h'.neg

theorem HasVal.pow (h : HasVal y f c) (n : ℕ) : HasVal y (f ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact hasVal_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem HasVal.sum {ι : Type*} {s : Finset ι} {f : ι → Y.FnC σ} {c : ι → ℂ}
    (h : ∀ i ∈ s, HasVal y (f i) (c i)) : HasVal y (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hasVal_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HasVal.of_mul {u : Y.FnC σ} {d : ℂ} (hu : HasVal y u d) (hd : d ≠ 0)
    (h : HasVal y (u * f) c) : HasVal y f (c / d) := by
  obtain ⟨p, q, hq, hu1, hp⟩ := hu
  obtain ⟨a, b, hb, h1, ha⟩ := h
  refine ⟨a * q, b * p, ?_, ?_, ?_⟩
  · rw [map_mul, hp]
    exact mul_ne_zero hb (mul_ne_zero hq hd)
  · simp only [map_mul]
    linear_combination (germIncl y q) * h1 - (germIncl y b * f) * hu1
  · simp only [map_mul]
    rw [hp, ha, div_eq_mul_inv]
    linear_combination (germEv y b * germEv y q * c) * (mul_inv_cancel₀ hd).symm

theorem regC_mul_iff {u : Y.FnC σ} (hu : val y u ≠ 0) : RegC y (u * f) ↔ RegC y f := by
  have hU : HasVal y u (val y u) := (regC_of_val_ne_zero hu).hasVal
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c / val y u, hU.of_mul hu h⟩
  · rintro ⟨c, h⟩
    exact ⟨val y u * c, hU.mul h⟩

theorem val_mul (h : RegC y f) (h' : RegC y f') : val y (f * f') = val y f * val y f' := (h.hasVal.mul h'.hasVal).val_eq

theorem val_unit_mul {u : Y.FnC σ} (hu : val y u ≠ 0) (f : Y.FnC σ) :
    val y (u * f) = val y u * val y f := by
  by_cases hf : RegC y f
  · exact val_mul (regC_of_val_ne_zero hu) hf
  · rw [val_of_not_regC hf, mul_zero]
    exact val_of_not_regC fun h => hf ((regC_mul_iff hu).1 h)

theorem hasVal_cx_stalk (a : Y.X.presheaf.stalk (base y)) :
    HasVal y (Y.cx σ (algebraMap _ Y.X.functionField a)) (evStalk y a) := by
  have h := hasVal_germIncl (y := y) (CxExt.of σ a)
  simp only [germIncl, germEv, CxExt.map_of, CxExt.lift_of] at h
  exact h

theorem hasVal_cx_fnOf {U : Y.X.Opens} (h : base y ∈ U) (h' : genericPoint Y.X ∈ U)
    (a : Γ(Y.X, U)) : HasVal y (Y.cx σ (fnOf U h' a)) (ev Y.str σ U a y) := by
  have h₁ := hasVal_cx_stalk (y := y) (Y.X.presheaf.germ U _ h a)
  rw [algebraMap_germ, evStalk_germ h] at h₁
  exact h₁

theorem val_cx_fnOf {U : Y.X.Opens} (h : base y ∈ U) (h' : genericPoint Y.X ∈ U)
    (a : Γ(Y.X, U)) : val y (Y.cx σ (fnOf U h' a)) = ev Y.str σ U a y :=
  (hasVal_cx_fnOf h h' a).val_eq

theorem regC_cx_iff {g : Y.Fn} : RegC y (Y.cx σ g) ↔ RegAt (base y) g := by
  constructor
  · rintro ⟨c, a, b, hb, hab, -⟩
    obtain ⟨ι, s, e, p, p', hx, h₁, h₂⟩ := CxExt.exists_components σ (Y.stalkIncl (base y)) b
    have e₁ : ∀ t, Y.stalkIncl (base y) t = algebraMap _ Y.Fn t := fun _ => rfl
    have key : ∀ i, algebraMap _ Y.Fn (p i b) * g = algebraMap _ Y.Fn (p i a) := by
      intro i
      have hi := congrArg (p' i) hab
      simp only [germIncl, Var.cx] at hi
      rw [h₂, h₁, h₁, e₁, e₁] at hi
      exact hi
    by_contra hg
    apply hb
    have hz : ∀ i, evStalk y (p i b) = 0 := by
      intro i
      by_contra hne
      obtain ⟨u, hu⟩ := (evStalk_ne_zero_iff (p i b)).1 hne
      apply hg
      refine ⟨(↑u⁻¹ : Y.X.presheaf.stalk (base y)) * p i a, ?_⟩
      have hk := key i
      rw [← hu] at hk
      rw [map_mul, ← hk, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    rw [hx, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul]
    simp only [germEv, CxExt.lift_of]
    rw [hz i, smul_zero]
  · rintro ⟨a, rfl⟩
    exact (hasVal_cx_stalk (y := y) a).regC

theorem val_cx_ne_zero_iff {g : Y.Fn} : val y (Y.cx σ g) ≠ 0 ↔ UnitAt (base y) g := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (regC_cx_iff (y := y)).1 (regC_of_val_ne_zero h)
    rw [(hasVal_cx_stalk (y := y) a).val_eq] at h
    exact ⟨a, (evStalk_ne_zero_iff a).1 h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [(hasVal_cx_stalk (y := y) a).val_eq]
    exact (evStalk_ne_zero_iff a).2 ha

theorem exists_spread {x : Y.X} (a : CxExt σ (Y.X.presheaf.stalk x)) :
    ∃ (U : Y.X.Opens) (A : Y.pts σ → ℂ), x ∈ U ∧ (Y.an σ).HoloOn (ptsIn Y.str σ U) A ∧
      ∀ z ∈ ptsIn Y.str σ U, ∃ a', germIncl z a' = CxExt.map σ (Y.stalkIncl x) a ∧
        germEv z a' = A z := by
  refine CxExt.induction a (fun c s => ?_) (fun a₁ a₂ h₁ h₂ => ?_)
  · obtain ⟨U, hx, g, rfl⟩ := Y.X.presheaf.germ_exist s
    refine ⟨U, fun z => c * ev Y.str σ U g z, hx, ?_, fun z hz => ?_⟩
    · exact (show (Y.an σ).HoloOn (ptsIn Y.str σ U) (fun _ => c) from
        fun _ => differentiableOn_const c).mul ((Y.an σ).holoOn_ev U g)
    · have hz' : base z ∈ U := Var.mem_ptsIn_iff.mp hz
      have e : Y.stalkIncl (base z) (Y.X.presheaf.germ U (base z) hz' g) =
          Y.stalkIncl x (Y.X.presheaf.germ U x hx g) :=
        (algebraMap_germ hz' g).trans (algebraMap_germ hx g).symm
      refine ⟨c • CxExt.of σ (Y.X.presheaf.germ U (base z) hz' g), ?_, ?_⟩
      · simp only [germIncl, map_smul, CxExt.map_of, e]
      · simp only [germEv, map_smul, CxExt.lift_of, smul_eq_mul, evStalk_germ hz']
  · obtain ⟨U₁, A₁, hx₁, hA₁, e₁⟩ := h₁
    obtain ⟨U₂, A₂, hx₂, hA₂, e₂⟩ := h₂
    have s₁ : ptsIn Y.str σ (U₁ ⊓ U₂) ⊆ ptsIn Y.str σ U₁ :=
      fun z hz => Var.mem_ptsIn_iff.mpr (Var.mem_ptsIn_iff.mp hz).1
    have s₂ : ptsIn Y.str σ (U₁ ⊓ U₂) ⊆ ptsIn Y.str σ U₂ :=
      fun z hz => Var.mem_ptsIn_iff.mpr (Var.mem_ptsIn_iff.mp hz).2
    refine ⟨U₁ ⊓ U₂, fun z => A₁ z + A₂ z, ⟨hx₁, hx₂⟩, ?_, fun z hz => ?_⟩
    · intro i
      exact ((hA₁.mono s₁) i).add ((hA₂.mono s₂) i)
    · obtain ⟨b₁, f₁, g₁⟩ := e₁ z (s₁ hz)
      obtain ⟨b₂, f₂, g₂⟩ := e₂ z (s₂ hz)
      exact ⟨b₁ + b₂, by rw [map_add, map_add, f₁, f₂], by rw [map_add, g₁, g₂]⟩

def regSet (f : Y.FnC σ) : Set (Y.pts σ) := {y | RegC y f}

theorem RegC.exists_nhds (h : RegC y f) : ∃ N : Set (Y.pts σ), IsOpen N ∧ y ∈ N ∧
    N ⊆ regSet f ∧ (Y.an σ).HoloOn N fun z => val z f := by
  obtain ⟨c, a, b, hb, hab, -⟩ := h
  obtain ⟨U, A, hU, hA, eA⟩ := exists_spread a
  obtain ⟨V, B, hV, hB, eB⟩ := exists_spread b
  have key : ∀ z, z ∈ ptsIn Y.str σ U → z ∈ ptsIn Y.str σ V → B z ≠ 0 →
      HasVal z f (A z / B z) := by
    intro z zU zV hz
    obtain ⟨a', ha', ha''⟩ := eA z zU
    obtain ⟨b', hb', hb''⟩ := eB z zV
    refine ⟨a', b', by rw [hb'']; exact hz, ?_, ?_⟩
    · rw [ha', hb']; exact hab
    · rw [ha'', hb'']; field_simp
  have yV : y ∈ ptsIn Y.str σ V := Var.mem_ptsIn_iff.mpr hV
  have hBy : B y ≠ 0 := by
    obtain ⟨b', hb', hb''⟩ := eB y yV
    have e : b' = b := germIncl_injective y hb'
    rw [← hb'', e]; exact hb
  refine ⟨ptsIn Y.str σ U ∩ (ptsIn Y.str σ V ∩ B ⁻¹' {0}ᶜ),
    (isOpen_ptsIn U).inter ((hB.continuousOn (isOpen_ptsIn V)).isOpen_inter_preimage
      (isOpen_ptsIn V) isOpen_compl_singleton),
    ⟨Var.mem_ptsIn_iff.mpr hU, yV, hBy⟩, fun z hz => ⟨_, key z hz.1 hz.2.1 hz.2.2⟩, ?_⟩
  refine ((hA.mono fun z hz => hz.1).mul ((hB.mono fun z hz => hz.2.1).inv
    fun z hz => hz.2.2)).congr ?_
  intro z hz
  rw [(key z hz.1 hz.2.1 hz.2.2).val_eq, div_eq_mul_inv]

theorem isOpen_regSet (f : Y.FnC σ) : IsOpen (regSet f) := by
  refine isOpen_iff_forall_mem_open.mpr fun z hz => ?_
  obtain ⟨N, hN, hzN, hNs, -⟩ := (show RegC z f from hz).exists_nhds
  exact ⟨N, hNs, hN, hzN⟩

theorem holoOn_val (f : Y.FnC σ) : (Y.an σ).HoloOn (regSet f) fun z => val z f := by
  choose N hN hyN hNs hNh using fun z : regSet f => (show RegC z.1 f from z.2).exists_nhds
  exact AnRead.holoOn_of_cover (R := Y.an σ) hN (fun z hz => ⟨⟨z, hz⟩, hyN ⟨z, hz⟩⟩)
    fun j => (hNh j).mono Set.inter_subset_right



end Var

end GlobalTheory.ProjVar
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open MeasureTheory
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv} {g g' : Y.Fnˣ}
  {y : Y.pts σ} {f f' : Y.FnC σ}

theorem exists_mem_ptsIn {U : Y.X.Opens} (h : genericPoint Y.X ∈ U) :
    ∃ y : Y.pts σ, y ∈ ptsIn Y.str σ U :=
  have := ComplexPoints.surjective_specMap_field σ
  have : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim _
  have ⟨x, hx, hU⟩ := ComplexPoints.exists_geomPoint_mem Y.str (Spec.map (CommRingCat.ofHom σ))
    U.isOpen.isLocallyClosed ⟨_, h⟩
  ⟨⟨x, hx⟩, mem_ptsIn_iff.2 (hU _)⟩

instance nonempty_pts : Nonempty (Y.pts σ) := ⟨(exists_mem_ptsIn (U := ⊤) trivial).choose⟩

theorem val_cx (a : Y.Fn) (y : Y.pts σ) : val y (Y.cx σ a) = ratVal a y := by
  by_cases h : RegAt (base y) a
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    rw [val_cx_fnOf hU, ratVal_fnOf (mem_ptsIn_iff.2 hU)]
  · rw [val_of_not_regC (mt regC_cx_iff.1 h)]; rw [ratVal, dif_neg (show ¬ RegAt (under y) a from h)]

variable (σ) in

def eqnSet (Δ : Y.Dv) (g : Y.Fnˣ) : Set (Y.pts σ) := {y | Δ.IsEqn (base y) g}

theorem isOpen_eqnSet (Δ : Y.Dv) (g : Y.Fnˣ) : IsOpen (eqnSet σ Δ g) :=
  isOpen_iff_forall_mem_open.2 fun _ hy =>
    have ⟨U, hU, h⟩ := IsEqn.exists_nhds hy
    ⟨ptsIn Y.str σ U, fun _ hz => h _ (mem_ptsIn_iff.1 hz), isOpen_ptsIn U, mem_ptsIn_iff.2 hU⟩

def eqn (Δ : Y.Dv) (y : Y.pts σ) : Y.Fnˣ := (Δ.exists_isEqn (base y)).choose

theorem mem_eqnSet (Δ : Y.Dv) (y : Y.pts σ) : y ∈ eqnSet σ Δ (eqn Δ y) :=
  (Δ.exists_isEqn (base y)).choose_spec


def fval (g : Y.Fnˣ) (f : Y.FnC σ) (y : Y.pts σ) : ℂ := val y (f * Y.cx σ g)

def tv (g g' : Y.Fnˣ) (y : Y.pts σ) : ℂ := val y (Y.cx σ (g' / g))

theorem fval_one (f : Y.FnC σ) (y : Y.pts σ) : fval 1 f y = val y f := by simp [fval]

theorem fval_cx (a : Y.Fn) (y : Y.pts σ) : fval g (Y.cx σ a) y = ratVal (a * (g : Y.Fn)) y := by
  rw [fval, ← map_mul, val_cx]

theorem tv_ne_zero (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') : tv g g' y ≠ 0 :=
  val_cx_ne_zero_iff.2 ((IsEqn.iff_unitAt h).1 h')

theorem mul_cx_eq (f : Y.FnC σ) (g g' : Y.Fnˣ) :
    f * Y.cx σ g' = Y.cx σ (g' / g) * (f * Y.cx σ g) := by
  rw [mul_left_comm, ← map_mul, div_mul_cancel₀ _ g.ne_zero]

theorem fval_trans (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') (f : Y.FnC σ) :
    fval g' f y = tv g g' y * fval g f y := by
  rw [fval, mul_cx_eq f g g', val_unit_mul (tv_ne_zero h h')]; rfl

theorem tv_mul_mul {g₁ g₁' : Y.Fnˣ} (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') :
    tv (g * g₁) (g' * g₁') y = tv g g' y * tv g₁ g₁' y := by
  rw [tv, Units.val_mul, Units.val_mul, mul_div_mul_comm, map_mul, val_unit_mul (tv_ne_zero h h')]
  rfl

theorem tv_mul {g'' : Y.Fnˣ} (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') :
    tv g g' y * tv g' g'' y = tv g g'' y := by
  rw [← tv_mul_mul h h', tv, tv, Units.val_mul, Units.val_mul, mul_comm (g : Y.Fn),
    mul_div_mul_left _ _ g'.ne_zero]

theorem tv_pow (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') (k : ℕ) :
    tv (g ^ k) (g' ^ k) y = tv g g' y ^ k := by
  rw [tv, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← div_pow, map_pow]
  exact ((regC_of_val_ne_zero (tv_ne_zero h h')).hasVal.pow k).val_eq

theorem holoOn_tv (Δ : Y.Dv) (g g' : Y.Fnˣ) :
    (Y.an σ).HoloOn (eqnSet σ Δ g ∩ eqnSet σ Δ g') (tv g g') :=
  (holoOn_val _).mono fun _ hz => regC_of_val_ne_zero (tv_ne_zero hz.1 hz.2)

def SecReg (Δ : Y.Dv) (f : Y.FnC σ) (y : Y.pts σ) : Prop :=
  ∃ g, y ∈ eqnSet σ Δ g ∧ RegC y (f * Y.cx σ g)

def SecZero (Δ : Y.Dv) (f : Y.FnC σ) (y : Y.pts σ) : Prop :=
  ∃ g, y ∈ eqnSet σ Δ g ∧ HasVal y (f * Y.cx σ g) 0

theorem secReg_iff (h : y ∈ eqnSet σ Δ g) : SecReg Δ f y ↔ RegC y (f * Y.cx σ g) :=
  ⟨fun ⟨g', h', hf⟩ => mul_cx_eq f g' g ▸ (regC_mul_iff (tv_ne_zero h' h)).2 hf, fun hf => ⟨g, h, hf⟩⟩

theorem secZero_iff (h : y ∈ eqnSet σ Δ g) : SecZero Δ f y ↔ SecReg Δ f y ∧ fval g f y = 0 :=
  ⟨fun ⟨g', h', hf⟩ => ⟨⟨g', h', hf.regC⟩, by rw [fval_trans h' h, fval, hf.val_eq, mul_zero]⟩,
    fun hf => ⟨g, h, hf.2 ▸ ((secReg_iff h).1 hf.1).hasVal⟩⟩

theorem secReg_cx_iff {a : Y.Fn} : SecReg Δ (Y.cx σ a) y ↔ Δ.RegularAt (base y) a :=
  exists_congr fun _ => and_congr_right fun _ => by rw [← map_mul, regC_cx_iff]

theorem secZero_cx_iff {a : Y.Fn} : SecZero Δ (Y.cx σ a) y ↔ Δ.VanishesAt (base y) a := by
  have h := mem_eqnSet Δ y
  rw [secZero_iff h, secReg_cx_iff, vanishesAt_iff, IsEqn.generatesAt_iff h, fval, ← map_mul,
    ← val_cx_ne_zero_iff, not_not]

theorem secReg_cx_of_mem {a : Y.Fn} (h : a ∈ Y.H0 Δ) (y : Y.pts σ) : SecReg Δ (Y.cx σ a) y :=
  secReg_cx_iff.2 (mem_riemannRochSpace_iff_regularAt_everywhere.1 h _)

theorem hasVal_sum_smul {ι : Type*} [Fintype ι] {e : ι → Y.FnC σ} (h : y ∈ eqnSet σ Δ g)
    (he : ∀ i, SecReg Δ (e i) y) (c : ι → ℂ) :
    HasVal y ((∑ i, c i • e i) * Y.cx σ g) (∑ i, c i * fval g (e i) y) := by
  rw [Finset.sum_mul]
  exact HasVal.sum fun i _ => smul_mul_assoc (c i) (e i) _ ▸ ((secReg_iff h).1 (he i)).hasVal.smul _

theorem SecReg.mul (h : SecReg Δ f y) (h' : SecReg Δ' f' y) : SecReg (Δ + Δ') (f * f') y :=
  have ⟨g, hg, hf⟩ := h; have ⟨g', hg', hf'⟩ := h'
  ⟨g * g', IsEqn.add hg hg', by
    rw [Units.val_mul, map_mul, mul_mul_mul_comm]; exact (hf.hasVal.mul hf'.hasVal).regC⟩

theorem fval_mul (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ' g') (h : SecReg Δ f y)
    (h' : SecReg Δ' f' y) : fval (g * g') (f * f') y = fval g f y * fval g' f' y := by
  rw [fval, Units.val_mul, map_mul, mul_mul_mul_comm,
    val_mul ((secReg_iff hg).1 h) ((secReg_iff hg').1 h')]
  rfl

theorem fval_pow (hg : y ∈ eqnSet σ Δ g) (h : SecReg Δ f y) (k : ℕ) :
    fval (g ^ k) (f ^ k) y = fval g f y ^ k := by
  rw [fval, Units.val_pow_eq_pow_val, map_pow, ← mul_pow]
  exact (((secReg_iff hg).1 h).hasVal.pow k).val_eq

theorem isOpen_secReg (Δ : Y.Dv) (f : Y.FnC σ) : IsOpen {y | SecReg Δ f y} := by
  simp only [SecReg, setOf_exists]
  exact isOpen_iUnion fun g => (isOpen_eqnSet Δ g).inter (isOpen_regSet _)

theorem holoOn_fval (Δ : Y.Dv) (g : Y.Fnˣ) (f : Y.FnC σ) :
    (Y.an σ).HoloOn ({y | SecReg Δ f y} ∩ eqnSet σ Δ g) (fval g f) :=
  (holoOn_val _).mono fun _ hz => (secReg_iff hz.2).1 hz.1

variable (Y σ) in

structure Met (Δ : Y.Dv) where

  h : Y.Fnˣ → Y.pts σ → ℝ

  nonneg : ∀ g y, 0 ≤ h g y

  trans : ∀ g g' y, y ∈ eqnSet σ Δ g → y ∈ eqnSet σ Δ g' → h g y = ‖tv g g' y‖ ^ 2 * h g' y

namespace Met

variable (m : Met Y σ Δ) (m' : Met Y σ Δ')

def wt (g : Y.Fnˣ) (y : Y.pts σ) : ℝ := -Real.log (m.h g y)

def posSet : Set (Y.pts σ) := {y | 0 < m.h (eqn Δ y) y}

variable {m} in

theorem mem_posSet_iff (hg : y ∈ eqnSet σ Δ g) : y ∈ m.posSet ↔ 0 < m.h g y := by
  have := tv_ne_zero (mem_eqnSet Δ y) hg
  rw [posSet, mem_setOf_eq, m.trans _ g y (mem_eqnSet Δ y) hg, mul_pos_iff_of_pos_left (by positivity)]

variable {m} in

theorem h_eq_exp (hy : y ∈ m.posSet) (hg : y ∈ eqnSet σ Δ g) : m.h g y = Real.exp (-m.wt g y) := by
  rw [wt, neg_neg, Real.exp_log ((mem_posSet_iff hg).1 hy)]

variable {m} in

theorem wt_trans (hy : y ∈ m.posSet) (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ g') :
    m.wt g' y = m.wt g y + Real.log (‖tv g g' y‖ ^ 2) := by
  have := tv_ne_zero hg hg'
  rw [wt, wt, m.trans g g' y hg hg',
    Real.log_mul (by positivity) ((mem_posSet_iff hg').1 hy).ne']
  ring

section Cover

variable {ι : Type} (S : ι → Set (Y.pts σ)) (e : ι → Y.Fnˣ) (sub : ∀ i, S i ⊆ eqnSet σ Δ (e i))
  (cover : ∀ y, ∃ i, y ∈ S i) (w : ι → Y.pts σ → ℝ) (hw : ∀ i y, 0 ≤ w i y)
  (compat : ∀ i j y, y ∈ S i → y ∈ S j → w i y = ‖tv (e i) (e j) y‖ ^ 2 * w j y)

def ofCover : Met Y σ Δ where
  h g y := ‖tv g (e (cover y).choose) y‖ ^ 2 * w (cover y).choose y
  nonneg _ _ := mul_nonneg (sq_nonneg _) (hw _ _)
  trans g g' y hg hg' := by rw [← mul_assoc, ← mul_pow, ← norm_mul, tv_mul hg hg']

include sub compat in

theorem ofCover_h {i : ι} (hi : y ∈ S i) : (ofCover (Δ := Δ) S e cover w hw).h (e i) y = w i y :=
  (compat i _ y hi (cover y).choose_spec).symm

end Cover

variable {m} in

def SmoothOn (m : Met Y σ Δ) (S : Set (Y.pts σ)) : Prop :=
  S ⊆ m.posSet ∧ ∀ g, (Y.an σ).SmoothOn (S ∩ eqnSet σ Δ g) (m.wt g)

variable {m} in

theorem smoothOn_of_cover {S : Set (Y.pts σ)} (hS : IsOpen S) (h0 : S ⊆ m.posSet) {ι : Type}
    {T : ι → Set (Y.pts σ)} (hT : ∀ i, IsOpen (T i)) (hc : ∀ y, ∃ i, y ∈ T i) {e : ι → Y.Fnˣ}
    (sub : ∀ i, T i ⊆ eqnSet σ Δ (e i)) (h : ∀ i, (Y.an σ).SmoothOn (S ∩ T i) (m.wt (e i))) :
    m.SmoothOn S := ⟨h0, fun g => AnRead.smoothOn_of_cover hT (fun y _ => hc y) fun i =>
  AnRead.SmoothOn.congr (f := fun y => m.wt (e i) y + Real.log (‖tv (e i) g y‖ ^ 2))
    (fun c => ((h i).mono (fun _ hz => ⟨hz.1.1, hz.2⟩) c).add
      (((holoOn_tv Δ (e i) g).mono fun _ hz => ⟨sub i hz.2, hz.1.2⟩).smoothOn_log
        ((hS.inter (isOpen_eqnSet Δ g)).inter (hT i))
        (fun _ hz => tv_ne_zero (sub i hz.2) hz.1.2) c))
    fun _ hz => wt_trans (h0 hz.1.1) (sub i hz.2) hz.1.2⟩

end Met

open Met

theorem cover_pair (Δ Δ' : Y.Dv) (y : Y.pts σ) :
    ∃ i : Y.Fnˣ × Y.Fnˣ, y ∈ eqnSet σ Δ i.1 ∩ eqnSet σ Δ' i.2 :=
  ⟨(_, _), mem_eqnSet Δ y, mem_eqnSet Δ' y⟩

variable (Y σ Δ Δ') in

def mAdd (m : Met Y σ Δ) (m' : Met Y σ Δ') : Met Y σ (Δ + Δ') :=
  ofCover _ (fun i => i.1 * i.2) (cover_pair Δ Δ') (fun i y => m.h i.1 y * m'.h i.2 y)
    fun _ _ => mul_nonneg (m.nonneg _ _) (m'.nonneg _ _)

variable (Y σ Δ) in

def mPow (k : ℕ) (m : Met Y σ Δ) : Met Y σ (k • Δ) :=
  ofCover _ (· ^ k) (fun y => ⟨_, mem_eqnSet Δ y⟩) (fun g y => m.h g y ^ k)
    fun _ _ => pow_nonneg (m.nonneg _ _) _

open Classical in
variable (Y σ Δ) in

def fsMet {κ : Type} [Fintype κ] (e : κ → Y.FnC σ) : Met Y σ Δ where
  h g y := if ∀ k, SecReg Δ (e k) y then (∑ k, ‖fval g (e k) y‖ ^ 2)⁻¹ else 0
  nonneg g y := by split_ifs <;> positivity
  trans g g' y hg hg' := by
    have := tv_ne_zero hg hg'
    split_ifs
    · simp only [fval_trans hg hg', norm_mul, mul_pow, ← Finset.mul_sum, mul_inv]
      rw [mul_inv_cancel_left₀ (by positivity)]
    · rw [mul_zero]

section OfWeight

variable {L : LB Y.X} {r : L.ι → Y.Fnˣ}

theorem tv_eq_gv (hp : Presents Δ L r) {i j : L.ι} (hi : y ∈ ptsIn Y.str σ (L.U i))
    (hj : y ∈ ptsIn Y.str σ (L.U j)) : tv (r j) (r i) y = gv Y.str σ L i j y := by
  have h : base y ∈ L.U i ⊓ L.U j := ⟨mem_ptsIn_iff.1 hi, mem_ptsIn_iff.1 hj⟩
  rw [tv, hp.isRatSec i j (gen_mem h), mul_div_cancel_right₀ _ (r j).ne_zero, val_cx_fnOf h]
  rfl

theorem ptsIn_subset_eqnSet (hp : Presents Δ L r) (i : L.ι) :
    ptsIn Y.str σ (L.U i) ⊆ eqnSet σ Δ (r i) := fun _ h => hp.isEqn i _ (mem_ptsIn_iff.1 h)

variable (Y σ Δ L r) in

def ofWeight (_ : Presents Δ L r) (φ : Weight Y.str σ L) : Met Y σ Δ :=
  ofCover (fun i => ptsIn Y.str σ (L.U i)) r (fun y => ⟨_, mem_pick φ.isLB y⟩)
    (fun i y => Real.exp (-φ.φ i y)) fun _ _ => (Real.exp_pos _).le

theorem ofWeight_h (hp : Presents Δ L r) (φ : Weight Y.str σ L) {i : L.ι}
    (hi : y ∈ ptsIn Y.str σ (L.U i)) :
    (ofWeight Y σ Δ L r hp φ).h (r i) y = Real.exp (-φ.φ i y) :=
  ofCover_h _ _ (ptsIn_subset_eqnSet hp) _ _ _ (fun i j y hi hj => by
    have := normSq_mul_exp (gv_ne_zero hj hi) 1 (φ.φ i y)
    rw [φ.trans j i y hj hi, sub_add_cancel, mul_one, norm_one, one_pow, one_mul] at this
    rw [tv_eq_gv hp hj hi, φ.trans j i y hj hi, this]) hi

def Met.toWeight (m : Met Y σ Δ) (hm : m.posSet = univ) (hp : Presents Δ L r) :
    Weight Y.str σ L where
  isLB := hp.isLB
  φ i := m.wt (r i)
  trans i j y hi hj := by
    rw [wt_trans (hm ▸ mem_univ y) (ptsIn_subset_eqnSet hp j hj) (ptsIn_subset_eqnSet hp i hi),
      tv_eq_gv hp hi hj, add_sub_cancel_right]

end OfWeight

variable {m : Met Y σ Δ} {m' : Met Y σ Δ'}

theorem mAdd_h (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ' g') :
    (mAdd Y σ Δ Δ' m m').h (g * g') y = m.h g y * m'.h g' y :=
  ofCover_h (Δ := Δ + Δ') _ (fun i : Y.Fnˣ × Y.Fnˣ => i.1 * i.2) (fun _ _ h => IsEqn.add h.1 h.2) _ _ _
    (fun i j y hi hj => by
      rw [m.trans _ _ y hi.1 hj.1, m'.trans _ _ y hi.2 hj.2, tv_mul_mul hi.1 hj.1, norm_mul]; ring)
    (i := (g, g')) ⟨hg, hg'⟩

theorem mPow_h (hg : y ∈ eqnSet σ Δ g) (k : ℕ) : (mPow Y σ Δ k m).h (g ^ k) y = m.h g y ^ k :=
  ofCover_h (Δ := k • Δ) _ (· ^ k) (fun _ _ h => IsEqn.nsmul h k) _ _ _
    (fun i j y hi hj => by rw [m.trans _ _ y hi hj, tv_pow hi hj, norm_pow]; ring) hg

theorem fsMet_h {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} (he : ∀ k, SecReg Δ (e k) y) (g : Y.Fnˣ) :
    (fsMet Y σ Δ e).h g y = (∑ k, ‖fval g (e k) y‖ ^ 2)⁻¹ := if_pos he

theorem mem_posSet_fsMet {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} : y ∈ (fsMet Y σ Δ e).posSet ↔
    (∀ k, SecReg Δ (e k) y) ∧ ∃ k, ¬ SecZero Δ (e k) y := by
  by_cases he : ∀ k, SecReg Δ (e k) y
  · simp only [posSet, mem_setOf_eq, fsMet_h he, inv_pos, secZero_iff (mem_eqnSet Δ y), he,
      implies_true, true_and]
    rw [Finset.sum_pos_iff_of_nonneg fun _ _ => sq_nonneg _]
    simp [sq_pos_iff]
  · simp [posSet, fsMet, he]

theorem posSet_mAdd : (mAdd Y σ Δ Δ' m m').posSet = m.posSet ∩ m'.posSet := by
  ext y
  have h := mem_eqnSet Δ y
  have h' := mem_eqnSet Δ' y
  rw [mem_posSet_iff (IsEqn.add h h'), mAdd_h h h', mem_inter_iff, mem_posSet_iff h, mem_posSet_iff h']
  exact ⟨fun e => ⟨pos_of_mul_pos_left e (m'.nonneg _ _), pos_of_mul_pos_right e (m.nonneg _ _)⟩, fun e => mul_pos e.1 e.2⟩

theorem posSet_subset_mPow (k : ℕ) : m.posSet ⊆ (mPow Y σ Δ k m).posSet := fun y hy => by
  have h := mem_eqnSet Δ y
  rw [mem_posSet_iff (IsEqn.nsmul h k), mPow_h h]
  exact pow_pos hy k

theorem wt_mAdd (hy : y ∈ m.posSet) (hy' : y ∈ m'.posSet) (hg : y ∈ eqnSet σ Δ g)
    (hg' : y ∈ eqnSet σ Δ' g') : (mAdd Y σ Δ Δ' m m').wt (g * g') y = m.wt g y + m'.wt g' y := by
  rw [wt, mAdd_h hg hg', Real.log_mul ((mem_posSet_iff hg).1 hy).ne' ((mem_posSet_iff hg').1 hy').ne',
    neg_add, wt, wt]

theorem wt_mPow (hg : y ∈ eqnSet σ Δ g) (k : ℕ) :
    (mPow Y σ Δ k m).wt (g ^ k) y = k * m.wt g y := by
  rw [wt, mPow_h hg, Real.log_pow, wt, mul_neg]

theorem wt_fsMet {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} (he : ∀ k, SecReg Δ (e k) y) (g : Y.Fnˣ) :
    (fsMet Y σ Δ e).wt g y = Real.log (∑ k, ‖fval g (e k) y‖ ^ 2) := by
  rw [wt, fsMet_h he, Real.log_inv, neg_neg]

variable (Y σ Δ) in

def pn (m : Met Y σ Δ) (f : Y.FnC σ) (y : Y.pts σ) : ℝ :=
  ‖fval (eqn Δ y) f y‖ ^ 2 * m.h (eqn Δ y) y

variable (Y σ Δ) in

def pnK (m : Met Y σ Δ) (f : Y.FnC σ) (y : Y.pts σ) : ℝ := pn Y σ Δ m f y

theorem pn_eq (hg : y ∈ eqnSet σ Δ g) : pn Y σ Δ m f y = ‖fval g f y‖ ^ 2 * m.h g y := by
  rw [pn, fval_trans hg (mem_eqnSet Δ y), m.trans g _ y hg (mem_eqnSet Δ y), norm_mul]; ring

theorem pn_eq_exp (hy : y ∈ m.posSet) (hg : y ∈ eqnSet σ Δ g) :
    pn Y σ Δ m f y = ‖fval g f y‖ ^ 2 * Real.exp (-m.wt g y) := by rw [pn_eq hg, h_eq_exp hy hg]



theorem pn_nonneg : 0 ≤ pn Y σ Δ m f y := mul_nonneg (sq_nonneg _) (m.nonneg _ _)

theorem pn_frame (hg : y ∈ eqnSet σ Δ g) : pn Y σ Δ m (Y.cx σ (g⁻¹ : Y.Fnˣ)) y = m.h g y := by
  rw [pn_eq hg, fval, ← map_mul, Units.inv_mul, map_one, hasVal_one.val_eq]; simp

theorem pn_eq_zero_iff (hy : y ∈ m.posSet) (hf : SecReg Δ f y) :
    pn Y σ Δ m f y = 0 ↔ SecZero Δ f y := by
  simp [pn, secZero_iff (mem_eqnSet Δ y), hf, (show 0 < m.h (eqn Δ y) y from hy).ne']

theorem pn_mul {a : Y.FnC σ} (ha : RegC y a) (hf : SecReg Δ f y) :
    pn Y σ Δ m (a * f) y = ‖val y a‖ ^ 2 * pn Y σ Δ m f y := by
  rw [pn, pn, fval, mul_assoc, val_mul ha ((secReg_iff (mem_eqnSet Δ y)).1 hf), norm_mul, fval]
  ring


theorem pn_mAdd (hf : SecReg Δ f y) (hf' : SecReg Δ' f' y) :
    pn Y σ _ (mAdd Y σ Δ Δ' m m') (f * f') y = pn Y σ Δ m f y * pn Y σ Δ' m' f' y := by
  have h := mem_eqnSet Δ y
  have h' := mem_eqnSet Δ' y
  rw [pn_eq (IsEqn.add h h'), mAdd_h h h', fval_mul h h' hf hf', pn, pn, norm_mul]; ring

theorem pn_mPow (hf : SecReg Δ f y) (k : ℕ) :
    pn Y σ _ (mPow Y σ Δ k m) (f ^ k) y = pn Y σ Δ m f y ^ k := by
  have h := mem_eqnSet Δ y
  rw [pn_eq (IsEqn.nsmul h k), mPow_h h, fval_pow h hf, pn, norm_pow]; ring

theorem pn_fsMet {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} (he : ∀ k, SecReg Δ (e k) y)
    (hg : y ∈ eqnSet σ Δ g) :
    pn Y σ Δ (fsMet Y σ Δ e) f y = ‖fval g f y‖ ^ 2 / ∑ k, ‖fval g (e k) y‖ ^ 2 := by
  rw [pn_eq hg, fsMet_h he, div_eq_mul_inv]


theorem sum_pn_fsMet {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} (hy : y ∈ (fsMet Y σ Δ e).posSet) :
    ∑ k, pn Y σ Δ (fsMet Y σ Δ e) (e k) y = 1 := by
  have he := (mem_posSet_fsMet.1 hy).1
  have h : 0 < (fsMet Y σ Δ e).h (eqn Δ y) y := hy
  rw [fsMet_h he, inv_pos] at h
  simp only [pn_fsMet he (mem_eqnSet Δ y), ← Finset.sum_div, div_self h.ne']

theorem pn_ofWeight {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r) (φ : Weight Y.str σ L)
    {i : L.ι} (hi : y ∈ ptsIn Y.str σ (L.U i)) : pn Y σ Δ (ofWeight Y σ Δ L r hp φ) f y =
      ‖fval (r i) f y‖ ^ 2 * Real.exp (-φ.φ i y) := by
  rw [pn_eq (ptsIn_subset_eqnSet hp i hi), ofWeight_h hp φ hi]


variable (Y σ Δ) in

def mSmooth (m : Met Y σ Δ) : Prop := m.SmoothOn univ

theorem mSmooth.posSet_eq (h : mSmooth Y σ Δ m) : m.posSet = univ := univ_subset_iff.1 h.1

theorem Met.SmoothOn.mAdd {S : Set (Y.pts σ)} (hS : IsOpen S) (h : m.SmoothOn S) (h' : m'.SmoothOn S) :
    (mAdd Y σ Δ Δ' m m').SmoothOn S :=
  smoothOn_of_cover hS ((subset_inter h.1 h'.1).trans posSet_mAdd.ge)
    (fun _ => (isOpen_eqnSet _ _).inter (isOpen_eqnSet _ _)) (cover_pair Δ Δ')
    (e := fun i => i.1 * i.2) (fun _ _ hz => IsEqn.add hz.1 hz.2) fun i =>
    AnRead.SmoothOn.congr (f := fun y => m.wt i.1 y + m'.wt i.2 y)
      (fun c => ((h.2 i.1).mono (fun _ hz => ⟨hz.1, hz.2.1⟩) c).add
        ((h'.2 i.2).mono (fun _ hz => ⟨hz.1, hz.2.2⟩) c))
      fun _ hz => wt_mAdd (h.1 hz.1) (h'.1 hz.1) hz.2.1 hz.2.2

theorem Met.SmoothOn.mPow {S : Set (Y.pts σ)} (hS : IsOpen S) (h : m.SmoothOn S) (k : ℕ) :
    (mPow Y σ Δ k m).SmoothOn S :=
  smoothOn_of_cover hS (h.1.trans (posSet_subset_mPow k)) (isOpen_eqnSet Δ)
    (fun y => ⟨_, mem_eqnSet Δ y⟩) (e := (· ^ k)) (fun _ _ hz => IsEqn.nsmul hz k) fun g =>
    AnRead.SmoothOn.congr (f := fun y => k * m.wt g y) (fun c => contDiffOn_const.mul (h.2 g c))
      fun _ hz => wt_mPow hz.2 k

theorem smoothOn_fsMet {κ : Type} [Fintype κ] (e : κ → Y.FnC σ) {S : Set (Y.pts σ)} (hS : IsOpen S)
    (h : S ⊆ (fsMet Y σ Δ e).posSet) : (fsMet Y σ Δ e).SmoothOn S := ⟨h, fun g =>
  have he (z) (hz : z ∈ S) := (mem_posSet_fsMet.1 (h hz)).1
  AnRead.SmoothOn.congr (f := fun y => Real.log (∑ k, ‖fval g (e k) y‖ ^ 2))
    (fun c => (ContDiffOn.sum (f := fun k v => ‖fval g (e k) (((Y.an σ).chart c).e.symm v)‖ ^ 2)
      fun k _ => (contDiffOn_real (isOpen_over _ (hS.inter (isOpen_eqnSet Δ g)))
        ((holoOn_fval Δ g (e k)).mono (fun z hz => ⟨he z hz.1 k, hz.2⟩) c)).norm_sq ℂ).log
      fun _ hv => by
        have := (mem_posSet_iff hv.2.2).1 (h hv.2.1)
        rw [fsMet_h (he _ hv.2.1), inv_pos] at this
        exact this.ne')
    fun z hz => wt_fsMet (he z hz.1) g⟩

theorem mSmooth_fsMet_iff {κ : Type} [Fintype κ] {e : κ → Y.FnC σ} : mSmooth Y σ Δ (fsMet Y σ Δ e) ↔
    ∀ y, (∀ k, SecReg Δ (e k) y) ∧ ∃ k, ¬ SecZero Δ (e k) y :=
  ⟨fun h y => mem_posSet_fsMet.1 (h.1 (mem_univ y)),
    fun h => smoothOn_fsMet e isOpen_univ fun y _ => mem_posSet_fsMet.2 (h y)⟩

theorem mSmooth_fsMet_cx {κ : Type} [Fintype κ] {b : κ → Y.Fn} (h : Y.bpf Δ (range b)) :
    mSmooth Y σ Δ (fsMet Y σ Δ fun k => Y.cx σ (b k)) := by
  have h' : Δ.BasePointFree (range b) := h
  rw [mSmooth_fsMet_iff]
  intro y
  simp only [secReg_cx_iff, secZero_cx_iff, vanishesAt_iff]
  refine ⟨fun k => mem_sections.1 (h'.mem _ ⟨k, rfl⟩) _, by_contra fun H => h'.not_isBasePoint (base y) ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (not_not.1 fun h => H ⟨k, h⟩).2

theorem mSmooth_ofWeight_iff {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r)
    (φ : Weight Y.str σ L) : mSmooth Y σ Δ (ofWeight Y σ Δ L r hp φ) ↔ φ.IsSmooth (Y.an σ) := by
  have e (i) (y) (hi : y ∈ ptsIn Y.str σ (L.U i)) : (ofWeight Y σ Δ L r hp φ).wt (r i) y = φ.φ i y := by
    rw [wt, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
  refine ⟨fun h i => ((h.2 (r i)).mono fun y hy => ⟨trivial, ptsIn_subset_eqnSet hp i hy⟩).congr
    fun y hy => (e i y hy).symm, fun h => smoothOn_of_cover isOpen_univ (fun y _ => ?_)
      (fun i => isOpen_ptsIn (L.U i)) (fun y => ⟨_, mem_pick φ.isLB y⟩) (ptsIn_subset_eqnSet hp)
      fun i => ((h i).mono inter_subset_right).congr fun y hy => e i y hy.2⟩
  have hi := mem_pick φ.isLB y
  rw [mem_posSet_iff (ptsIn_subset_eqnSet hp _ hi), ofWeight_h hp φ hi]
  exact Real.exp_pos _

theorem mSmooth.isSmooth_toWeight (h : mSmooth Y σ Δ m) {L : LB Y.X} {r : L.ι → Y.Fnˣ}
    (hp : Presents Δ L r) : (m.toWeight h.posSet_eq hp).IsSmooth (Y.an σ) := fun i =>
  (h.2 (r i)).mono fun _ hy => ⟨trivial, ptsIn_subset_eqnSet hp i hy⟩

theorem pn_ofWeight_toWeight (hm : m.posSet = univ) {L : LB Y.X} {r : L.ι → Y.Fnˣ}
    (hp : Presents Δ L r) : pn Y σ Δ (ofWeight Y σ Δ L r hp (m.toWeight hm hp)) = pn Y σ Δ m := by
  funext f y
  have hi := mem_pick hp.isLB y
  rw [pn_ofWeight hp _ hi, pn_eq_exp (hm ▸ mem_univ y) (ptsIn_subset_eqnSet hp _ hi)]
  rfl

theorem Met.SmoothOn.continuousOn_pn {S : Set (Y.pts σ)} (hS : IsOpen S) (h : m.SmoothOn S)
    (hf : ∀ y ∈ S, SecReg Δ f y) : ContinuousOn (pn Y σ Δ m f) S := fun y hy => by
  have ho := hS.inter (isOpen_eqnSet Δ (eqn Δ y))
  have h₁ := ((holoOn_fval Δ (eqn Δ y) f).mono fun z hz => ⟨hf z hz.1, hz.2⟩).continuousOn ho
  refine ((((h₁.norm.pow 2).mul ((h.2 _).continuousOn ho).neg.rexp).congr fun z hz =>
    pn_eq_exp (h.1 hz.1) hz.2).continuousAt (ho.mem_nhds ⟨hy, mem_eqnSet Δ y⟩)).continuousWithinAt

def omegaCoeff (c : AlgChart Y.str σ Y.dim) : Y.Fnˣ :=
  frameRat (CanonLB.all Y.str Y.dim).bundle (baseChart _ _) (gen_mem_baseOpen _ _) ⟨c.U, _, c.isFrame⟩


theorem mem_eqnSet_omegaCoeff (c : AlgChart Y.str σ Y.dim) (hy : y ∈ c.e.source) :
    y ∈ eqnSet σ Y.KY (omegaCoeff c) :=
  ptsIn_subset_eqnSet (presents_canonical Y.str Y.dim) ⟨c.U, _, c.isFrame⟩ (c.source_subset hy)

theorem tv_omegaCoeff (c c' : AlgChart Y.str σ Y.dim) (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    tv (omegaCoeff c') (omegaCoeff c) y = transDet c.e c'.e y :=
  (tv_eq_gv (presents_canonical Y.str Y.dim) (i := ⟨c.U, _, c.isFrame⟩) (j := ⟨c'.U, _, c'.isFrame⟩)
    (c.source_subset hy) (c'.source_subset hy')).trans
    ((congrFun (gv_canon _ _ _) y).trans (rv_chart c c' hy hy'))

variable (Y σ) in

def vol : Measure (Y.pts σ) :=
  (Y.an σ).topMeasure (CanonLB.all Y.str Y.dim) (Weight.ofFun fun _ => 0) fun a =>
    fval (frameRat _ (baseChart _ _) (gen_mem_baseOpen _ _) a.1) 1

def _root_.GlobalTheory.ProjVar.PosCurrent {D : ℕ} (O : Set (V D)) (u : V D → ℝ) : Prop :=
  LocallyIntegrableOn u O ∧ ∀ χ : V D → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
    (∀ v, 0 ≤ χ v) → ∀ ξ, 0 ≤ ∫ v, u v * (leviV D (fun w => (χ w : ℂ)) v ξ).re

def chartDom (c : AlgChart Y.str σ Y.dim) (Δ : Y.Dv) (g : Y.Fnˣ) : Set (V Y.dim) :=
  c.e.target ∩ c.e.symm ⁻¹' eqnSet σ Δ g

variable (Y σ Δ) in

def mPsh (m : Met Y σ Δ) (ψ : Y.pts σ → ℝ) : Prop :=
  ∀ (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ),
    (∀ᵐ v, v ∈ chartDom c Δ g → c.e.symm v ∈ m.posSet) ∧
      PosCurrent (chartDom c Δ g) fun v => m.wt g (c.e.symm v) + ψ (c.e.symm v)

theorem _root_.GlobalTheory.ProjVar.PosCurrent.congr {D : ℕ} {O : Set (V D)} {u u' : V D → ℝ} (hO : IsOpen O)
    (h : PosCurrent O u) (e : ∀ᵐ v, v ∈ O → u v = u' v) : PosCurrent O u' := by
  refine ⟨fun v hv => ?_, fun χ h₁ h₂ h₃ h₄ ξ => (h.2 χ h₁ h₂ h₃ h₄ ξ).trans_eq (integral_congr_ae ?_)⟩
  · obtain ⟨s, hs, hi⟩ := h.1 v hv
    refine ⟨s ∩ O, inter_mem hs self_mem_nhdsWithin, (hi.mono_set inter_subset_left).congr ?_⟩
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_right
      ((ae_restrict_iff' hO.measurableSet).2 e)
  · filter_upwards [e] with v hv
    by_cases hvO : v ∈ O
    · rw [hv hvO]
    · have : (fun w => (χ w : ℂ)) =ᶠ[𝓝 v] fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.1 fun h => hvO (h₃ h)).mono fun w hw => by simp [hw]
      rw [ReciprocityTheory.L2DbarEstimates.leviV_congr this]
      have h0 (k) : ReciprocityTheory.L2DbarEstimates.wdb D k (fun _ => 0) = fun _ => 0 :=
        funext fun _ => by simp [ReciprocityTheory.L2DbarEstimates.wdb]
      simp [leviV, h0, ReciprocityTheory.L2DbarEstimates.wd]

theorem mPsh.congr {ψ ψ' : Y.pts σ → ℝ} (h : mPsh Y σ Δ m ψ)
    (e : ∀ c : AlgChart Y.str σ Y.dim, ∀ᵐ v, v ∈ c.e.target → ψ (c.e.symm v) = ψ' (c.e.symm v)) :
    mPsh Y σ Δ m ψ' := fun c g => ⟨(h c g).1, (h c g).2.congr (isOpen_over _ (isOpen_eqnSet Δ g))
      ((e c).mono fun _ hv hv' => by rw [hv hv'.1])⟩

def jac (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (s : Fin Y.dim → Y.FnC σ) (y : Y.pts σ) : ℂ :=
  (fderiv ℂ (fun v => (WithLp.toLp 2 fun i => fval g (s i) (c.e.symm v) : V Y.dim)) (c.e y)).det

def chartAt (y : Y.pts σ) : AlgChart Y.str σ Y.dim := (AlgChart.exists_mem_source y).choose

theorem mem_chartAt (y : Y.pts σ) : y ∈ (chartAt y).e.source :=
  (AlgChart.exists_mem_source y).choose_spec

variable {s : Fin Y.dim → Y.FnC σ} {c c' : AlgChart Y.str σ Y.dim}

theorem differentiableAt_fval (hc : y ∈ c.e.source) (hg : y ∈ eqnSet σ Δ g)
    (hs : ∀ i, SecReg Δ (s i) y) : DifferentiableAt ℂ
      (fun v => (WithLp.toLp 2 fun i => fval g (s i) (c.e.symm v) : V Y.dim)) (c.e y) :=
  differentiableAt_euclidean.2 fun i =>
    have hS := (isOpen_secReg Δ (s i)).inter (isOpen_eqnSet Δ g)
    ((holoOn_fval Δ g (s i)).chart hS c).differentiableAt
      ((isOpen_over _ hS).mem_nhds (mem_over _ hc ⟨hs i, hg⟩))

theorem jac_chart (hc : y ∈ c.e.source) (hc' : y ∈ c'.e.source) (hg : y ∈ eqnSet σ Δ g)
    (hs : ∀ i, SecReg Δ (s i) y) : jac c g s y = transDet c.e c'.e y * jac c' g s y := by
  have hn := (isOpen_over c.e c'.e.open_source).mem_nhds (mem_over c.e hc hc')
  have e : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hc)
  have h₁ := (e ▸ differentiableAt_fval hc' hg hs).hasFDerivAt.comp _
    ((c.holo_trans c').differentiableAt hn).hasFDerivAt
  rw [jac, (h₁.congr_of_eventuallyEq (eventually_of_mem hn fun v hv => by
    simp only [Function.comp_apply, c'.e.left_inv hv.2])).fderiv, e, mul_comm]
  exact LinearMap.det_comp _ _

theorem jac_frame (hc : y ∈ c.e.source) (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ g')
    (hs : ∀ i, SecZero Δ (s i) y) : jac c g' s y = tv g g' y ^ Y.dim * jac c g s y := by
  have hS := (isOpen_eqnSet (σ := σ) Δ g).inter (isOpen_eqnSet Δ g')
  have hn := (isOpen_over c.e hS).mem_nhds (mem_over c.e hc ⟨hg, hg'⟩)
  have h₁ := (((holoOn_tv Δ g g').chart hS c).differentiableAt hn).hasFDerivAt.smul
    (differentiableAt_fval hc hg fun i => ((secZero_iff hg).1 (hs i)).1).hasFDerivAt
  have h0 : (WithLp.toLp 2 fun i => fval g (s i) (c.e.symm (c.e y)) : V Y.dim) = 0 := by
    ext i; rw [c.e.left_inv hc]; exact ((secZero_iff hg).1 (hs i)).2
  rw [h0, ContinuousLinearMap.smulRight_zero, add_zero, Function.comp_apply, c.e.left_inv hc] at h₁
  rw [jac, (h₁.congr_of_eventuallyEq (eventually_of_mem hn fun v hv => by
    ext i; exact fval_trans hv.2.1 hv.2.2 _)).fderiv]
  exact (LinearMap.det_smul _ _).trans (by rw [finrank_euclideanSpace_fin]; rfl)

variable (Y σ Δ) in

def redZero (s : Fin Y.dim → Y.FnC σ) (S : Set (Y.pts σ)) : Prop :=
  (∀ i y, SecReg Δ (s i) y) ∧ S = {y | ∀ i, SecZero Δ (s i) y} ∧
    ∀ y ∈ S, jac (chartAt y) (eqn Δ y) s y ≠ 0

variable (Y σ Δ) in

def regOn (G : Y.FnC σ) (S : Set (Y.pts σ)) : Prop := ∀ y ∈ S, SecReg (Y.KY + Δ) G y

variable (Y σ Δ) in

def agreeOn (G G' : Y.FnC σ) (S : Set (Y.pts σ)) : Prop := ∀ y ∈ S, SecZero (Y.KY + Δ) (G - G') y


variable (Y σ Δ) in

def resNorm (m : Met Y σ Δ) (Δ' : Y.Dv) (m' : Met Y σ Δ') (s : Fin Y.dim → Y.FnC σ) (G : Y.FnC σ)
    (y : Y.pts σ) : ℝ :=
  ‖fval (omegaCoeff (chartAt y) * eqn Δ y) G y‖ ^ 2 * m.h (eqn Δ y) y /
    (‖jac (chartAt y) (eqn Δ' y) s y‖ ^ 2 * m'.h (eqn Δ' y) y ^ Y.dim)

theorem resNorm_eq (hc : y ∈ c.e.source) (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ' g')
    (hs : ∀ i, SecZero Δ' (s i) y) (G : Y.FnC σ) : resNorm Y σ Δ m Δ' m' s G y =
      ‖fval (omegaCoeff c * g) G y‖ ^ 2 * m.h g y / (‖jac c g' s y‖ ^ 2 * m'.h g' y ^ Y.dim) := by
  have h := mem_eqnSet_omegaCoeff c hc
  have h' := mem_eqnSet_omegaCoeff _ (mem_chartAt y)
  have h₁ := tv_ne_zero h h'
  rw [resNorm, jac_frame (mem_chartAt y) hg' (mem_eqnSet Δ' y) hs,
    jac_chart (mem_chartAt y) hc hg' fun i => ((secZero_iff hg').1 (hs i)).1,
    ← tv_omegaCoeff _ _ (mem_chartAt y) hc,
    fval_trans (IsEqn.add h hg) (IsEqn.add h' (mem_eqnSet Δ y)), tv_mul_mul h h',
    m.trans g _ y hg (mem_eqnSet Δ y), m'.trans g' _ y hg' (mem_eqnSet Δ' y)]
  refine Eq.trans ?_ (mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 h₁)))
  simp only [norm_mul, norm_pow]
  congr 1 <;> ring


end GlobalTheory.ProjVar.Var

namespace GlobalTheory.ProjVar

open Var

variable (F : Type) [Field F] (σ : F →+* ℂ) (n : ℕ)

def projMet : (proj F n).Met σ (projHyp F n) :=
  fsMet _ σ _ fun j => (proj F n).cx σ ((proj F n).coordFn (proj_gen_mem F n 0) j)

theorem mSmooth_projMet : mSmooth _ σ _ (projMet F σ n) := mSmooth_fsMet_cx ((proj F n).bpf_hyp _)

example (y : (proj F n).pts σ) :
    ∑ j, pn _ σ _ (projMet F σ n) ((proj F n).cx σ ((proj F n).coordFn (proj_gen_mem F n 0) j)) y = 1 ∧
    (pn _ σ _ (projMet F σ n) 1 y = 0 ↔ base y ∈ (proj F n).supp (projHyp F n)) := by
  have hy := (mSmooth_projMet F σ n).1 (mem_univ y)
  have he : (projHyp F n).Eff := (proj F n).eff_hyp _
  refine ⟨sum_pn_fsMet hy, ?_⟩
  rw [← map_one ((proj F n).cx σ), pn_eq_zero_iff hy (secReg_cx_iff.2 (he _)), secZero_cx_iff]
  exact he.mem_supp_iff.symm

example (Y : Var F) (Δ : Y.Dv) (ψ : Y.pts σ → ℝ) : ¬ mSmooth Y σ Δ (fsMet Y σ Δ fun _ : Unit => 0) ∧
    ¬ mPsh Y σ Δ (fsMet Y σ Δ fun _ : Unit => 0) ψ := by
  obtain ⟨y⟩ := nonempty_pts (Y := Y) (σ := σ)
  have key (z) : z ∉ (fsMet Y σ Δ fun _ : Unit => 0).posSet := fun h =>
    have ⟨_, hk⟩ := (mem_posSet_fsMet.1 h).2
    hk ⟨_, mem_eqnSet Δ z, by rw [zero_mul]; exact hasVal_zero⟩
  refine ⟨fun h => key y (h.1 trivial), fun h => ?_⟩
  have ho : IsOpen (chartDom (chartAt y) Δ (eqn Δ y)) := isOpen_over _ (isOpen_eqnSet _ _)
  exact (ho.measure_pos volume ⟨_, mem_over _ (mem_chartAt y) (mem_eqnSet Δ y)⟩).ne'
    (measure_eq_zero_iff_ae_notMem.2 ((h _ _).1.mono fun v hv hv' => key _ (hv hv')))

example (Δ Δ' : (proj F 0).Dv) (m : (proj F 0).Met σ Δ) (m' : (proj F 0).Met σ Δ')
    (s : Fin 0 → (proj F 0).FnC σ) (G : (proj F 0).FnC σ) (y : (proj F 0).pts σ) :
    redZero _ σ Δ' s univ ∧ Var.resNorm _ σ Δ m Δ' m' s G y =
      ‖fval (omegaCoeff (chartAt y) * eqn Δ y) G y‖ ^ 2 * m.h (eqn Δ y) y := by
  have hj (c g z) : Var.jac (Y := proj F 0) (σ := σ) c g s z = 1 :=
    have : Subsingleton (V (proj F 0).dim) := inferInstanceAs (Subsingleton (V 0))
    LinearMap.det_eq_one_of_subsingleton _
  refine ⟨⟨fun i => i.elim0, (eq_univ_of_forall fun _ i => i.elim0).symm,
    fun z _ => hj _ _ z ▸ one_ne_zero⟩, ?_⟩
  refine (congrArg (fun j => _ / (‖j‖ ^ 2 * _)) (hj _ _ y)).trans ?_
  simp [proj_dim]

example (Δ : (proj F 0).Dv) (m : (proj F 0).Met σ Δ) (hm : m.posSet = univ)
    (ψ : (proj F 0).pts σ → ℝ) : mPsh _ σ Δ m ψ := fun c g => by
  have : Subsingleton (V (proj F 0).dim) := inferInstanceAs (Subsingleton (V 0))
  have : IsEmpty (Fin (proj F 0).dim) := inferInstanceAs (IsEmpty (Fin 0))
  exact ⟨.of_forall fun _ _ => hm ▸ mem_univ _,
    (continuous_of_discreteTopology.locallyIntegrable).locallyIntegrableOn _,
    fun _ _ _ _ _ _ => by simp [leviV]⟩


end GlobalTheory.ProjVar
end
end
