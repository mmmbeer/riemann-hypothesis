import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfIsLocalizedModuleRes

section
open CategoryTheory Limits TopologicalSpace Opposite

universe w v u

noncomputable section

namespace GlobalTheory

section Opens

variable {T : Type w} [TopologicalSpace T] {ι κ : Type}

def cechOpen (V : Opens T) (U : ι → Opens T) (s : Finset ι) : Opens T := V ⊓ ⨅ i ∈ s, U i

variable (V : Opens T) (U : ι → Opens T)


theorem cechOpen_eq_inf (s : Finset ι) : cechOpen V U s = V ⊓ s.inf U := by
  rw [cechOpen, Finset.inf_eq_iInf]

variable {V U} in

theorem le_cechOpen_iff {W : Opens T} {s : Finset ι} :
    W ≤ cechOpen V U s ↔ W ≤ V ∧ ∀ i ∈ s, W ≤ U i := by
  simp [cechOpen]

variable {V U} in

theorem mem_cechOpen {x : T} {s : Finset ι} :
    x ∈ cechOpen V U s ↔ x ∈ V ∧ ∀ i ∈ s, x ∈ U i := by
  classical
  rw [cechOpen_eq_inf, Opens.mem_inf]
  refine and_congr Iff.rfl ?_
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => simp [ih]

theorem cechOpen_le (s : Finset ι) : cechOpen V U s ≤ V := inf_le_left

theorem cechOpen_le_of_mem {s : Finset ι} {i : ι} (h : i ∈ s) : cechOpen V U s ≤ U i :=
  (le_cechOpen_iff.1 le_rfl).2 i h

theorem cechOpen_anti {s t : Finset ι} (h : s ⊆ t) : cechOpen V U t ≤ cechOpen V U s :=
  le_cechOpen_iff.2 ⟨cechOpen_le V U t, fun _ hi => cechOpen_le_of_mem V U (h hi)⟩

@[simp]
theorem cechOpen_empty : cechOpen V U ∅ = V := by simp [cechOpen]

@[simp]
theorem cechOpen_singleton (i : ι) : cechOpen V U {i} = V ⊓ U i := by simp [cechOpen]

theorem cechOpen_insert [DecidableEq ι] (i : ι) (s : Finset ι) :
    cechOpen V U (insert i s) = U i ⊓ cechOpen V U s := by
  rw [cechOpen, cechOpen, Finset.iInf_insert, inf_left_comm]

theorem cechOpen_pair [DecidableEq ι] (i j : ι) : cechOpen V U {i, j} = V ⊓ (U i ⊓ U j) := by
  rw [cechOpen_insert, cechOpen_singleton, inf_left_comm]

theorem cechOpen_union [DecidableEq ι] (s t : Finset ι) :
    cechOpen V U (s ∪ t) = cechOpen V U s ⊓ cechOpen V U t := by
  ext x
  simp only [SetLike.mem_coe, mem_cechOpen, Opens.mem_inf, Finset.mem_union, or_imp, forall_and]
  tauto

theorem cechOpen_top (s : Finset ι) : cechOpen ⊤ U s = ⨅ i ∈ s, U i := top_inf_eq _

variable {V U} in

theorem cechOpen_of_nonempty (h : ∀ i, U i ≤ V) {s : Finset ι} (hs : s.Nonempty) :
    cechOpen V U s = ⨅ i ∈ s, U i := by
  obtain ⟨i, hi⟩ := hs
  exact inf_eq_right.2 ((biInf_le U hi).trans (h i))

variable {V U} in

theorem cechOpen_mono {V' : Opens T} {U' : ι → Opens T} (hV : V' ≤ V) (hU : ∀ i, U' i ≤ U i)
    (s : Finset ι) : cechOpen V' U' s ≤ cechOpen V U s :=
  le_cechOpen_iff.2 ⟨(cechOpen_le _ _ s).trans hV,
    fun i hi => (cechOpen_le_of_mem _ _ hi).trans (hU i)⟩

theorem cechOpen_inf_family (s : Finset ι) :
    cechOpen V (fun i => V ⊓ U i) s = cechOpen V U s := by
  ext x
  simp only [SetLike.mem_coe, mem_cechOpen, Opens.mem_inf]
  exact and_congr_right fun h => by simp [h]

theorem cechOpen_inf_left (W : Opens T) (s : Finset ι) :
    cechOpen (W ⊓ V) U s = W ⊓ cechOpen V U s := inf_assoc _ _ _

theorem cechOpen_map (e : κ ↪ ι) (s : Finset κ) :
    cechOpen V U (s.map e) = cechOpen V (fun k => U (e k)) s := by
  ext x
  simp [mem_cechOpen]

theorem cechOpen_insert_map [DecidableEq ι] (e : κ ↪ ι) (i : ι) (s : Finset κ) :
    cechOpen V U (insert i (s.map e)) = cechOpen (V ⊓ U i) (fun k => U (e k)) s := by
  rw [cechOpen_insert, cechOpen_map, inf_comm V, cechOpen_inf_left]

variable {V U} in

theorem cechOpen_empty_le_iSup (h : V ≤ ⨆ i, U i) :
    cechOpen V U ∅ ≤ ⨆ i, cechOpen V U {i} := by
  simp only [cechOpen_empty, cechOpen_singleton, ← inf_iSup_eq]
  exact le_inf le_rfl h

@[simps obj]
def cechOpenFunctor : Finset ι ⥤ (Opens T)ᵒᵖ where
  obj s := op (cechOpen V U s)
  map f := (homOfLE (cechOpen_anti V U (leOfHom f))).op

end Opens

section Presheaf

variable {T : Type w} [TopologicalSpace T] {ι κ : Type} {R : Type u} [Ring R]

def presheafRes (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) {W W' : Opens T} (h : W' ≤ W) :
    P.obj (op W) →ₗ[R] P.obj (op W') :=
  (P.map (homOfLE h).op).hom

variable (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) {Q Q' : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R}

@[simp]
theorem presheafRes_self {W : Opens T} (h : W ≤ W) (x : P.obj (op W)) : presheafRes P h x = x := by
  have : (homOfLE h).op = 𝟙 (op W) := rfl
  simp [presheafRes, this]

@[simp]
theorem presheafRes_presheafRes {W W' W'' : Opens T} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : P.obj (op W)) : presheafRes P h' (presheafRes P h x) = presheafRes P (h'.trans h) x := by
  have : (homOfLE (h'.trans h)).op = (homOfLE h).op ≫ (homOfLE h').op := rfl
  simp only [presheafRes, this, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem presheafRes_bijective {W W' : Opens T} (h : W' ≤ W) (h' : W ≤ W') :
    Function.Bijective (presheafRes P h) :=
  Function.bijective_iff_has_inverse.2 ⟨presheafRes P h', fun x => by simp, fun x => by simp⟩

def presheafCongr {W W' : Opens T} (h : W = W') : P.obj (op W) ≃ₗ[R] P.obj (op W') :=
  { presheafRes P h.ge with
    invFun := presheafRes P h.le
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

@[simp]
theorem presheafCongr_apply {W W' : Opens T} (h : W = W') (x : P.obj (op W)) :
    presheafCongr P h x = presheafRes P h.ge x := rfl

@[simp]
theorem presheafCongr_symm_apply {W W' : Opens T} (h : W = W') (x : P.obj (op W')) :
    (presheafCongr P h).symm x = presheafRes P h.le x := rfl

variable {P} in

theorem app_presheafRes (φ : P ⟶ Q) {W W' : Opens T} (h : W' ≤ W) (x : P.obj (op W)) :
    (φ.app (op W')).hom (presheafRes P h x) = presheafRes Q h ((φ.app (op W)).hom x) :=
  congr(($(φ.naturality (homOfLE h).op)).hom x)

variable (V : Opens T) (U : ι → Opens T)

def presheafCube : Cube.{v} ι R := cechOpenFunctor V U ⋙ P



variable {P} in

def presheafCubeMap (φ : P ⟶ Q) : presheafCube P V U ⟶ presheafCube Q V U :=
  Functor.whiskerLeft (cechOpenFunctor V U) φ

variable {P} in

@[simp]
theorem presheafCubeMap_app (φ : P ⟶ Q) (s : Finset ι) :
    (presheafCubeMap V U φ).app s = φ.app (op (cechOpen V U s)) := rfl

variable (R) in

@[simps]
def presheafCubeFunctor : ((Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) ⥤ Cube.{v} ι R where
  obj P := presheafCube P V U
  map := presheafCubeMap V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheafCubeFunctor_additive : (presheafCubeFunctor.{w, v} R V U).Additive where
  map_add := rfl

section Restrict

variable {V U} {V' V'' : Opens T} {U' U'' : ι → Opens T}

def presheafCubeRes (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    presheafCube P V U ⟶ presheafCube P V' U' :=
  Cube.homMk (fun s => presheafRes P (h s)) fun hst x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_anti V' U' hst) x).symm

@[simp]
theorem presheafCubeRes_app (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (s : Finset ι) :
    ((presheafCubeRes P h).app s).hom = presheafRes P (h s) := rfl

theorem presheafCubeRes_self (h : ∀ s, cechOpen V U s ≤ cechOpen V U s) :
    presheafCubeRes P h = 𝟙 _ :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (presheafRes_self P (h s))))

@[reassoc]
theorem presheafCubeRes_comp (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s)
    (h' : ∀ s, cechOpen V'' U'' s ≤ cechOpen V' U' s) :
    presheafCubeRes P h ≫ presheafCubeRes P h' = presheafCubeRes P fun s => (h' s).trans (h s) :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext
    (LinearMap.ext (presheafRes_presheafRes P (h s) (h' s))))

variable {P} in

@[reassoc]
theorem presheafCubeRes_naturality (φ : P ⟶ Q) (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    presheafCubeMap V U φ ≫ presheafCubeRes Q h = presheafCubeRes P h ≫ presheafCubeMap V' U' φ :=
  NatTrans.ext (funext fun s => (φ.naturality (homOfLE (h s)).op).symm)

def presheafCubeCongr (h : ∀ s, cechOpen V U s = cechOpen V' U' s) :
    presheafCube P V U ≅ presheafCube P V' U' where
  hom := presheafCubeRes P fun s => (h s).ge
  inv := presheafCubeRes P fun s => (h s).le
  hom_inv_id := (presheafCubeRes_comp P _ _).trans (presheafCubeRes_self P _)
  inv_hom_id := (presheafCubeRes_comp P _ _).trans (presheafCubeRes_self P _)

end Restrict

def presheafCubeEmptyEquiv : P.obj (op V) ≃ₗ[R] (presheafCube P V U).obj ∅ :=
  presheafCongr P (cechOpen_empty V U).symm


variable [LinearOrder ι]

section Faces

variable [LinearOrder κ] (e : κ ↪o ι) (i : ι)

def presheafCubeLowerFaceIso :
    Cube.lowerFace e (presheafCube P V U) ≅ presheafCube P V fun k => U (e k) :=
  Cube.isoMk (fun s => presheafCongr P (cechOpen_map V U e.toEmbedding s)) fun hst x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_anti V _ hst) x).symm

def presheafCubeUpperFaceIso :
    Cube.upperFace e i (presheafCube P V U) ≅ presheafCube P (V ⊓ U i) fun k => U (e k) :=
  Cube.isoMk (fun s => presheafCongr P (cechOpen_insert_map V U e.toEmbedding i s)) fun hst x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_anti (V ⊓ U i) _ hst) x).symm



@[reassoc]
theorem faceMap_presheafCube :
    Cube.faceMap e i (presheafCube P V U) ≫ (presheafCubeUpperFaceIso P V U e i).hom =
      (presheafCubeLowerFaceIso P V U e).hom ≫
        presheafCubeRes P (cechOpen_mono inf_le_left fun _ => le_rfl) :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext fun x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_mono inf_le_left (fun _ => le_rfl) s) x).symm))

end Faces

def presheafCech : CochainComplex (ModuleCat.{v} R) ℕ := cechComplex (presheafCube P V U)

def presheafCechH (n : ℕ) : ModuleCat.{v} R := (presheafCech P V U).homology n



variable {V U} in

theorem isIso_cechComplexMap_presheafCubeRes {V' : Opens T} {U' : ι → Opens T}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s)
    (h' : ∀ s, s.Nonempty → cechOpen V U s ≤ cechOpen V' U' s) :
    IsIso (cechComplexMap (presheafCubeRes P h)) :=
  isIso_cechComplexMap _ fun s hs => presheafRes_bijective P (h s) (h' s hs)

variable {V U} in

def presheafCechTopIso (h : ∀ i, U i ≤ V) : presheafCech P ⊤ U ≅ presheafCech P V U :=
  @asIso _ _ _ _
    (cechComplexMap (presheafCubeRes P (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)))
    (isIso_cechComplexMap_presheafCubeRes P _
      fun _ hs => ((cechOpen_top U _).trans (cechOpen_of_nonempty h hs).symm).le)

variable {V U} in

theorem presheafCechTopIso_hom (h : ∀ i, U i ≤ V) : (presheafCechTopIso P h).hom =
    cechComplexMap (presheafCubeRes P (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)) := rfl

omit [LinearOrder ι] in

def presheafCechAug : P.obj (op V) →ₗ[R] Cube.Term (presheafCube P V U) 1 :=
  LinearMap.pi fun s => presheafRes P (cechOpen_le V U s.1)

omit [LinearOrder ι] in

@[simp]
theorem presheafCechAug_apply (x : P.obj (op V)) (s : {s : Finset ι // s.card = 1}) :
    presheafCechAug P V U x s = presheafRes P (cechOpen_le V U s.1) x := rfl

omit [LinearOrder ι] in

theorem aug_presheafCubeEmptyEquiv (x : P.obj (op V)) :
    Cube.aug (presheafCube P V U) (presheafCubeEmptyEquiv P V U x) = presheafCechAug P V U x :=
  funext fun _ => presheafRes_presheafRes P _ _ x

@[simp]
theorem d_presheafCechAug (x : P.obj (op V)) :
    Cube.d (presheafCube P V U) 1 (presheafCechAug P V U x) = 0 := by
  rw [← aug_presheafCubeEmptyEquiv, Cube.d_aug]

def presheafToCechH : P.obj (op V) →ₗ[R] presheafCechH P V U 0 :=
  (cechAugHomology (presheafCube P V U)).hom ∘ₗ (presheafCubeEmptyEquiv P V U).toLinearMap

theorem presheafToCechH_apply (x : P.obj (op V)) :
    presheafToCechH P V U x =
      cechClass (presheafCube P V U) 0 ⟨presheafCechAug P V U x, d_presheafCechAug P V U x⟩ :=
  (cechAugHomology_apply _ _).trans
    (congrArg _ (Subtype.ext (aug_presheafCubeEmptyEquiv P V U x)))

variable {P} in

theorem homologyMap_presheafToCechH (φ : P ⟶ Q) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeMap V U φ)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH Q V U ((φ.app (op V)).hom x) := by
  rw [presheafToCechH_apply, presheafToCechH_apply]
  exact homologyMap_cechClass _ 0 _ _ (funext fun _ => app_presheafRes φ _ x)

variable {V U} in

theorem homologyMap_res_presheafToCechH {V' : Opens T} {U' : ι → Opens T}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (hV : V' ≤ V) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeRes P h)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH P V' U' (presheafRes P hV x) := by
  rw [presheafToCechH_apply, presheafToCechH_apply]
  exact homologyMap_cechClass _ 0 _ _ (funext fun s =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P hV (cechOpen_le V' U' s.1) x).symm)

theorem presheafRes_eq_of_d_eq_zero (x : Cube.Term (presheafCube P V U) 1)
    (hx : Cube.d (presheafCube P V U) 1 x = 0) (i j : ι) {W : Opens T}
    (hi : W ≤ cechOpen V U {i}) (hj : W ≤ cechOpen V U {j}) :
    presheafRes P hi (x ⟨{i}, Finset.card_singleton i⟩) =
      presheafRes P hj (x ⟨{j}, Finset.card_singleton j⟩) := by
  wlog hij : i < j generalizing i j
  · rcases (not_lt.1 hij).eq_or_lt with rfl | h
    · rfl
    · exact (this j i hj hi h).symm
  have hW : W ≤ cechOpen V U {i, j} :=
    (le_inf hi hj).trans (cechOpen_union V U {i} {j}).ge
  have h := (Cube.d_one_apply_pair _ x hij).symm.trans (congrFun hx _)
  have h' := congrArg (presheafRes P hW) (sub_eq_zero.1 h)
  exact (presheafRes_presheafRes P _ hW _).symm.trans
    (h'.symm.trans (presheafRes_presheafRes P _ hW _))

end Presheaf

section Sheaf

variable {T : TopCat.{w}} {ι : Type} {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  {V : Opens T} {U : ι → Opens T} (hc : V ≤ ⨆ i, U i)

include hP hc

theorem presheafCechAug_injective : Function.Injective (presheafCechAug P V U) := fun x y h =>
  TopCat.Sheaf.eq_of_locally_eq' (C := ModuleCat.{w} R) ⟨P, hP⟩ (fun i => cechOpen V U {i}) V
    (fun i => homOfLE (cechOpen_le V U {i}))
    ((cechOpen_empty V U).ge.trans (cechOpen_empty_le_iSup hc)) x y
    fun i => congrFun h ⟨{i}, Finset.card_singleton i⟩

variable [LinearOrder ι]

theorem presheafCechAug_exact :
    Function.Exact (presheafCechAug P V U) (Cube.d (presheafCube P V U) 1) := by
  intro x
  refine ⟨fun hx => ?_, by rintro ⟨y, rfl⟩; exact d_presheafCechAug P V U y⟩
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := ModuleCat.{w} R) ⟨P, hP⟩
    (fun i => cechOpen V U {i}) V (fun i => homOfLE (cechOpen_le V U {i}))
    ((cechOpen_empty V U).ge.trans (cechOpen_empty_le_iSup hc))
    (fun i => x ⟨{i}, Finset.card_singleton i⟩)
    fun i j => presheafRes_eq_of_d_eq_zero P V U x hx i j inf_le_left inf_le_right
  exact ⟨y, (Cube.termOneEquiv _).symm.injective (funext hy)⟩

theorem presheafToCechH_bijective : Function.Bijective (presheafToCechH P V U) := by
  constructor
  · intro x y h
    rw [presheafToCechH_apply, presheafToCechH_apply] at h
    exact presheafCechAug_injective hP hc
      (congrArg Subtype.val ((cechClass_zero_bijective _).1 h))
  · intro z
    obtain ⟨⟨x, hx⟩, rfl⟩ := cechClass_surjective (presheafCube P V U) 0 z
    obtain ⟨y, rfl⟩ := (presheafCechAug_exact hP hc x).1 hx
    exact ⟨y, presheafToCechH_apply P V U y⟩

theorem isIso_cechAugHomology_presheafCube : IsIso (cechAugHomology (presheafCube P V U)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ (presheafCubeEmptyEquiv P V U).bijective).1
    (presheafToCechH_bijective hP hc)

theorem presheafCube_exactAt_zero_one :
    (cubeComplex (presheafCube P V U)).ExactAt 0 ∧ (cubeComplex (presheafCube P V U)).ExactAt 1 :=
  (isIso_cechAugHomology_iff _).1 (isIso_cechAugHomology_presheafCube hP hc)

def presheafCechHZeroEquiv : presheafCechH P V U 0 ≃ₗ[R] P.obj (op V) :=
  (LinearEquiv.ofBijective _ (presheafToCechH_bijective hP hc)).symm

@[simp]
theorem presheafCechHZeroEquiv_symm_apply (x : P.obj (op V)) :
    (presheafCechHZeroEquiv hP hc).symm x = presheafToCechH P V U x := rfl

end Sheaf

@[simps]
def abToIntModule : AddCommGrpCat.{v} ⥤ ModuleCat.{v} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

instance abToIntModule_additive : abToIntModule.{v}.Additive where
  map_add := rfl

section Ab

variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)

def cechAbCube : Cube.{v} ι ℤ := presheafCube (P ⋙ abToIntModule) V U



variable {P} in

def cechAbCubeMap (φ : P ⟶ Q) : cechAbCube P V U ⟶ cechAbCube Q V U :=
  presheafCubeMap V U (Functor.whiskerRight φ abToIntModule)

variable {P} in

@[simp]
theorem cechAbCubeMap_app_apply (φ : P ⟶ Q) (s : Finset ι) (x : P.obj (op (cechOpen V U s))) :
    ((cechAbCubeMap V U φ).app s).hom x = φ.app (op (cechOpen V U s)) x := rfl

@[simps]
def cechAbCubeFunctor : ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ Cube.{v} ι ℤ where
  obj P := cechAbCube P V U
  map := cechAbCubeMap V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechAbCubeFunctor_additive : (cechAbCubeFunctor.{w, v} V U).Additive where
  map_add := rfl

variable [LinearOrder ι]

def cechAb : CochainComplex (ModuleCat.{v} ℤ) ℕ := cechComplex (cechAbCube P V U)

def cechAbH (n : ℕ) : ModuleCat.{v} ℤ := (cechAb P V U).homology n



variable {P} in

def cechAbMap (φ : P ⟶ Q) : cechAb P V U ⟶ cechAb Q V U := cechComplexMap (cechAbCubeMap V U φ)

variable {P} in

def cechAbHMap (φ : P ⟶ Q) (n : ℕ) : cechAbH P V U n ⟶ cechAbH Q V U n :=
  HomologicalComplex.homologyMap (cechAbMap V U φ) n

@[simps]
def cechAbFunctor : ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex (ModuleCat.{v} ℤ) ℕ where
  obj P := cechAb P V U
  map := cechAbMap V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechAbFunctor_additive : (cechAbFunctor.{w, v} V U).Additive where
  map_add := rfl

@[simps]
def cechAbHFunctor (n : ℕ) : ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ ModuleCat.{v} ℤ where
  obj P := cechAbH P V U n
  map φ := cechAbHMap V U φ n
  map_id P := (cechAbFunctor V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_id P
  map_comp := (cechAbFunctor V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_comp

instance cechAbHFunctor_additive (n : ℕ) : (cechAbHFunctor.{w, v} V U n).Additive where
  map_add := (cechAbFunctor V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add

@[simp]
theorem cechAbHMap_id (n : ℕ) : cechAbHMap V U (𝟙 P) n = 𝟙 _ := (cechAbHFunctor V U n).map_id P

variable {P} in

@[reassoc]
theorem cechAbHMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ Q') (n : ℕ) :
    cechAbHMap V U (φ ≫ ψ) n = cechAbHMap V U φ n ≫ cechAbHMap V U ψ n :=
  (cechAbHFunctor V U n).map_comp φ ψ

variable {P} in

theorem cechAbHMap_add (φ ψ : P ⟶ Q) (n : ℕ) :
    cechAbHMap V U (φ + ψ) n = cechAbHMap V U φ n + cechAbHMap V U ψ n :=
  (cechAbHFunctor V U n).map_add

theorem cechAbFunctor_shortExact (S : ShortComplex ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}))
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (op (cechOpen V U s))) ∧
      Function.Exact (S.f.app (op (cechOpen V U s))) (S.g.app (op (cechOpen V U s))) ∧
      Function.Surjective (S.g.app (op (cechOpen V U s)))) :
    (S.map (cechAbFunctor V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechAbCubeFunctor V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2




variable {V U} in

def cechAbTopIso (h : ∀ i, U i ≤ V) : cechAb P ⊤ U ≅ cechAb P V U :=
  presheafCechTopIso (P ⋙ abToIntModule) h

def toCechAbH : P.obj (op V) →ₗ[ℤ] cechAbH P V U 0 := presheafToCechH (P ⋙ abToIntModule) V U

variable {P} in

theorem cechAbHMap_toCechAbH (φ : P ⟶ Q) (x : P.obj (op V)) :
    (cechAbHMap V U φ 0).hom (toCechAbH P V U x) = toCechAbH Q V U (φ.app (op V) x) :=
  homologyMap_presheafToCechH V U (Functor.whiskerRight φ abToIntModule) x

end Ab

section AbSheaf

variable {T : TopCat.{w}} {ι : Type} {P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w}}
  {V : Opens T} {U : ι → Opens T}

theorem isSheaf_comp_abToIntModule (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P) :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) (P ⋙ abToIntModule) :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := ModuleCat.{w} ℤ) (X := T)
    (P ⋙ abToIntModule)).2
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{w}) (X := T) P).1 hP)

variable [LinearOrder ι]


def cechAbHZeroEquiv (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hc : V ≤ ⨆ i, U i) : cechAbH P V U 0 ≃ₗ[ℤ] P.obj (op V) :=
  presheafCechHZeroEquiv (isSheaf_comp_abToIntModule hP) hc

@[simp]
theorem cechAbHZeroEquiv_symm_apply (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hc : V ≤ ⨆ i, U i) (x : P.obj (op V)) :
    (cechAbHZeroEquiv hP hc).symm x = toCechAbH P V U x := rfl

theorem cechAbHZeroEquiv_map (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hQ : Presheaf.IsSheaf (Opens.grothendieckTopology T) Q) (hc : V ≤ ⨆ i, U i) (φ : P ⟶ Q)
    (x : cechAbH P V U 0) :
    cechAbHZeroEquiv hQ hc ((cechAbHMap V U φ 0).hom x) =
      φ.app (op V) (cechAbHZeroEquiv hP hc x) := by
  obtain ⟨y, rfl⟩ := (cechAbHZeroEquiv hP hc).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, cechAbHZeroEquiv_symm_apply, cechAbHMap_toCechAbH,
    ← cechAbHZeroEquiv_symm_apply hQ hc, LinearEquiv.apply_symm_apply]

end AbSheaf

end GlobalTheory
end
end

section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe t v u

noncomputable section

namespace GlobalTheory

variable {X Y : Scheme.{u}} {ι : Type}

section Basic

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

@[simps]
def sectionsPresheafMap {F G : X.Modules} (φ : F ⟶ G) :
    sectionsPresheaf R F ⟶ sectionsPresheaf R G where
  app W := ModuleCat.ofHom (sectionsOn.map R φ W.unop)
  naturality _ _ i := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (sectionsOn.res_map R φ i.unop.le x).symm)


theorem isSheaf_sectionsPresheaf (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (sectionsPresheaf R F) :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := ModuleCat.{u} R)
    (X := X.toPresheafedSpace.carrier) (sectionsPresheaf R F)).2
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{u}) F.presheaf).1
      F.isSheaf)

@[simp]
theorem sectionsOn.res_res (F : X.Modules) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : sectionsOn F W) :
    sectionsOn.res R F h' (sectionsOn.res R F h x) = sectionsOn.res R F (h'.trans h) x :=
  LinearMap.congr_fun (sectionsOn.res_comp_res R F h h') x

def sectionsOn.congrOpens (F : X.Modules) {W W' : X.Opens} (h : W = W') :
    sectionsOn F W ≃ₗ[R] sectionsOn F W' :=
  presheafCongr (sectionsPresheaf R F) h

@[simp]
theorem sectionsOn.congrOpens_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W) : sectionsOn.congrOpens R F h x = sectionsOn.res R F h.ge x := rfl

@[simp]
theorem sectionsOn.congrOpens_symm_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W') :
    (sectionsOn.congrOpens R F h).symm x = sectionsOn.res R F h.le x := rfl

variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)

def cechCube : Cube.{u} ι R := presheafCube (sectionsPresheaf R F) V U





variable {F} in

def cechCubeMap (φ : F ⟶ G) : cechCube R F V U ⟶ cechCube R G V U :=
  presheafCubeMap V U (sectionsPresheafMap R φ)

variable {F} in

@[simp]
theorem cechCubeMap_app (φ : F ⟶ G) (s : Finset ι) :
    ((cechCubeMap R V U φ).app s).hom = sectionsOn.map R φ (cechOpen V U s) := rfl

@[simps]
def cechCubeFunctor : X.Modules ⥤ Cube.{u} ι R where
  obj F := cechCube R F V U
  map := cechCubeMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechCubeFunctor_additive : (cechCubeFunctor R V U).Additive where
  map_add := rfl


def cechCubeEmptyEquiv : sectionsOn F V ≃ₗ[R] (cechCube R F V U).obj ∅ :=
  presheafCubeEmptyEquiv (sectionsPresheaf R F) V U


variable {V U} in

def cechCubeRes {V' : X.Opens} {U' : ι → X.Opens} (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    cechCube R F V U ⟶ cechCube R F V' U' :=
  presheafCubeRes (sectionsPresheaf R F) h

variable {V U} in

@[simp]
theorem cechCubeRes_app {V' : X.Opens} {U' : ι → X.Opens}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (s : Finset ι) :
    ((cechCubeRes R F h).app s).hom = sectionsOn.res R F (h s) := rfl

def cechRestrictions : sectionsOn F V →ₗ[R] Cube.Term (cechCube R F V U) 1 :=
  presheafCechAug (sectionsPresheaf R F) V U

@[simp]
theorem cechRestrictions_apply (x : sectionsOn F V) (s : {s : Finset ι // s.card = 1}) :
    cechRestrictions R F V U x s = sectionsOn.res R F (cechOpen_le V U s.1) x := rfl

variable [LinearOrder ι]

def cech : CochainComplex (ModuleCat.{u} R) ℕ := cechComplex (cechCube R F V U)

def cechH (n : ℕ) : ModuleCat.{u} R := (cech R F V U).homology n

theorem cech_def : cech R F V U = cechComplex (cechCube R F V U) := rfl

theorem cechH_def (n : ℕ) : cechH R F V U n = (cech R F V U).homology n := rfl

theorem cech_X (p : ℕ) : (cech R F V U).X p = ModuleCat.of R
    (∀ s : {s : Finset ι // s.card = p + 1}, sectionsOn F (V ⊓ ⨅ i ∈ s.1, U i)) := rfl

theorem cech_d (p : ℕ) :
    (cech R F V U).d p (p + 1) = ModuleCat.ofHom (Cube.d (cechCube R F V U) (p + 1)) :=
  cechComplex_d _ p

variable {F} in

def cechMap (φ : F ⟶ G) : cech R F V U ⟶ cech R G V U := cechComplexMap (cechCubeMap R V U φ)

variable {F} in

def cechHMap (φ : F ⟶ G) (n : ℕ) : cechH R F V U n ⟶ cechH R G V U n :=
  HomologicalComplex.homologyMap (cechMap R V U φ) n

@[simps]
def cechModulesFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj F := cech R F V U
  map := cechMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechModulesFunctor_additive : (cechModulesFunctor R V U).Additive where
  map_add := rfl

@[simps]
def cechHFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := cechH R F V U n
  map φ := cechHMap R V U φ n
  map_id F := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_id F
  map_comp := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_comp

instance cechHFunctor_additive (n : ℕ) : (cechHFunctor R V U n).Additive where
  map_add := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add

@[simp]
theorem cechMap_id : cechMap R V U (𝟙 F) = 𝟙 _ := rfl

variable {F} in

@[reassoc]
theorem cechMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    cechMap R V U (φ ≫ ψ) = cechMap R V U φ ≫ cechMap R V U ψ := rfl

@[simp]
theorem cechHMap_id (n : ℕ) : cechHMap R V U (𝟙 F) n = 𝟙 _ := (cechHFunctor R V U n).map_id F

variable {F} in

@[reassoc]
theorem cechHMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    cechHMap R V U (φ ≫ ψ) n = cechHMap R V U φ n ≫ cechHMap R V U ψ n :=
  (cechHFunctor R V U n).map_comp φ ψ

variable {F} in

theorem cechHMap_add (φ ψ : F ⟶ G) (n : ℕ) :
    cechHMap R V U (φ + ψ) n = cechHMap R V U φ n + cechHMap R V U ψ n :=
  (cechHFunctor R V U n).map_add

variable {F} in

def cechMapIso (e : F ≅ G) : cech R F V U ≅ cech R G V U := (cechModulesFunctor R V U).mapIso e

variable {F} in

def cechHMapIso (e : F ≅ G) (n : ℕ) : cechH R F V U n ≅ cechH R G V U n :=
  (cechHFunctor R V U n).mapIso e

variable {F} in

theorem cechHMap_cechClass (φ : F ⟶ G) (n : ℕ)
    (x : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    (cechHMap R V U φ n).hom (cechClass (cechCube R F V U) n x) =
      cechClass (cechCube R G V U) n ⟨_, Cube.termMap_mem_ker (cechCubeMap R V U φ) x.2⟩ :=
  homologyMap_cechClass (cechCubeMap R V U φ) n x _ rfl

theorem cechHMap_smulHom_apply (r : R) (n : ℕ) (x : cechH R F V U n) :
    (cechHMap R V U (smulHom F (algebraMap R Γ(X, ⊤) r)) n).hom x = r • x := by
  obtain ⟨x, rfl⟩ := cechClass_surjective (cechCube R F V U) n x
  exact (homologyMap_cechClass (cechCubeMap R V U _) n x (r • x) rfl).trans
    (map_smul (cechClass (cechCube R F V U) n) r x)

theorem cechModulesFunctor_shortExact (S : ShortComplex X.Modules)
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (cechOpen V U s)) ∧
      Function.Exact (S.f.app (cechOpen V U s)) (S.g.app (cechOpen V U s)) ∧
      Function.Surjective (S.g.app (cechOpen V U s))) :
    (S.map (cechModulesFunctor R V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechCubeFunctor R V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2


theorem isZero_cechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero (cechH R F V U n) := isZero_cechComplex_homology _ h

theorem subsingleton_cechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    Subsingleton (cechH R F V U n) := ModuleCat.isZero_iff_subsingleton.1 (isZero_cechH R F V U h)

variable {V U} in

def cechTopIso (h : ∀ i, U i ≤ V) : cech R F ⊤ U ≅ cech R F V U :=
  presheafCechTopIso (sectionsPresheaf R F) h

variable {V U} in

theorem cechTopIso_hom (h : ∀ i, U i ≤ V) : (cechTopIso R F h).hom =
    cechComplexMap (cechCubeRes R F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)) := rfl

variable {F V U} in

@[reassoc]
theorem cechTopIso_naturality (h : ∀ i, U i ≤ V) (φ : F ⟶ G) :
    cechMap R ⊤ U φ ≫ (cechTopIso R G h).hom = (cechTopIso R F h).hom ≫ cechMap R V U φ :=
  congrArg cechComplexMap (presheafCubeRes_naturality (sectionsPresheafMap R φ)
    (cechOpen_mono (le_top (a := V)) fun _ => le_rfl))

@[simp]
theorem d_cechRestrictions (x : sectionsOn F V) :
    Cube.d (cechCube R F V U) 1 (cechRestrictions R F V U x) = 0 :=
  d_presheafCechAug (sectionsPresheaf R F) V U x

def toCechH : sectionsOn F V →ₗ[R] cechH R F V U 0 := presheafToCechH (sectionsPresheaf R F) V U


variable {F} in

theorem cechHMap_toCechH (φ : F ⟶ G) (x : sectionsOn F V) :
    (cechHMap R V U φ 0).hom (toCechH R F V U x) = toCechH R G V U (sectionsOn.map R φ V x) :=
  homologyMap_presheafToCechH V U (sectionsPresheafMap R φ) x

variable {V U} (hc : V ≤ ⨆ i, U i)

omit [LinearOrder ι] in
include hc in

theorem cechRestrictions_injective : Function.Injective (cechRestrictions R F V U) :=
  presheafCechAug_injective (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem cechRestrictions_exact :
    Function.Exact (cechRestrictions R F V U) (Cube.d (cechCube R F V U) 1) :=
  presheafCechAug_exact (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem cechCube_exactAt_zero_one :
    (cubeComplex (cechCube R F V U)).ExactAt 0 ∧ (cubeComplex (cechCube R F V U)).ExactAt 1 :=
  presheafCube_exactAt_zero_one (T := X.toPresheafedSpace.carrier)
    (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem toCechH_bijective : Function.Bijective (toCechH R F V U) :=
  presheafToCechH_bijective (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

def cechHZeroEquiv : cechH R F V U 0 ≃ₗ[R] sectionsOn F V :=
  (LinearEquiv.ofBijective _ (toCechH_bijective R F hc)).symm

@[simp]
theorem cechHZeroEquiv_symm_apply (x : sectionsOn F V) :
    (cechHZeroEquiv R F hc).symm x = toCechH R F V U x := rfl

@[simp]
theorem cechHZeroEquiv_toCechH (x : sectionsOn F V) :
    cechHZeroEquiv R F hc (toCechH R F V U x) = x := (cechHZeroEquiv R F hc).apply_symm_apply x

variable {F} in

theorem cechHZeroEquiv_map (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquiv R G hc ((cechHMap R V U φ 0).hom x) =
      sectionsOn.map R φ V (cechHZeroEquiv R F hc x) := by
  obtain ⟨y, rfl⟩ := (toCechH_bijective R F hc).2 x
  rw [cechHMap_toCechH, cechHZeroEquiv_toCechH, cechHZeroEquiv_toCechH]

def cechHZeroEquivCohOn : cechH R F V U 0 ≃ₗ[R] cohOn F V 0 :=
  (cechHZeroEquiv R F hc).trans (cohOn.zeroEquiv R F V).symm

variable {F} in

theorem cechHZeroEquivCohOn_map (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquivCohOn R G hc ((cechHMap R V U φ 0).hom x) =
      cohOn.map R φ V 0 (cechHZeroEquivCohOn R F hc x) := by
  apply (cohOn.zeroEquiv R G V).injective
  simp only [cechHZeroEquivCohOn, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    cohOn.zeroEquiv_map, cechHZeroEquiv_map]

end Basic

section Scalars

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) {G : X.Modules} (V : X.Opens) (U : ι → X.Opens)

def cechAbCubeToCube :
    Cube.SemiHom (Int.castRingHom R) (cechAbCube F.presheaf V U) (cechCube R F V U) where
  app s :=
    { toFun := (sectionsOn.toΓ F (cechOpen V U s)).symm
      map_add' := map_add _
      map_smul' := fun n x => (map_zsmul (sectionsOn.toΓ F (cechOpen V U s)).symm n x).trans
        (Int.cast_smul_eq_zsmul R n _).symm }
  app_res _ _ := rfl

variable (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S] [IsScalarTower R S Γ(X, ⊤)]

def cechCubeScalars : Cube.SemiHom (algebraMap R S) (cechCube R F V U) (cechCube S F V U) where
  app s :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r (x : sectionsOn F (cechOpen V U s)) => (algebraMap_smul S r x).symm }
  app_res _ _ := rfl

def cechCubeRestrictScalarsIso :
    cechCube R F V U ≅ cechCube S F V U ⋙ ModuleCat.restrictScalars (algebraMap R S) :=
  Cube.isoMk (fun s =>
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r (x : sectionsOn F (cechOpen V U s)) => (algebraMap_smul S r x).symm })
    fun _ _ => rfl

variable [LinearOrder ι]

def cechRestrictIso : cech R F V U ≅
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj (cech S F V U) :=
  (cechFunctor ι R).mapIso (cechCubeRestrictScalarsIso R F V U S) ≪≫
    (cechRestrictScalarsIso (algebraMap R S) (cechCube S F V U)).symm

def cechHScalarsEquiv (n : ℕ) : cechH R F V U n ≃+ cechH S F V U n :=
  AddEquiv.ofBijective ((cechCubeScalars R F V U S).homology n).toAddMonoidHom
    ((cechCubeScalars R F V U S).homology_bijective (fun _ _ => Function.bijective_id) n)



variable {F} in

theorem cechHScalarsEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHScalarsEquiv R G V U S n ((cechHMap R V U φ n).hom x) =
      (cechHMap S V U φ n).hom (cechHScalarsEquiv R F V U S n x) :=
  (cechCubeScalars R F V U S).homology_naturality (cechCubeScalars R G V U S)
    (cechCubeMap R V U φ) (cechCubeMap S V U φ) (fun _ _ _ => rfl) n x

def cechAbHEquiv (n : ℕ) : cechAbH F.presheaf V U n ≃+ cechH R F V U n :=
  AddEquiv.ofBijective ((cechAbCubeToCube R F V U).homology n).toAddMonoidHom
    ((cechAbCubeToCube R F V U).homology_bijective (fun _ _ => Function.bijective_id) n)


variable {F} in

theorem cechAbHEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cechAbHEquiv R G V U n ((cechAbHMap V U φ.mapPresheaf n).hom x) =
      (cechHMap R V U φ n).hom (cechAbHEquiv R F V U n x) :=
  (cechAbCubeToCube R F V U).homology_naturality (cechAbCubeToCube R G V U)
    (cechAbCubeMap V U φ.mapPresheaf) (cechCubeMap R V U φ) (fun _ _ _ => rfl) n x


theorem cechAbHEquiv_toCechAbH (x : sectionsOn F V) :
    cechAbHEquiv R F V U 0 (toCechAbH F.presheaf V U (sectionsOn.toΓ F V x)) =
      toCechH R F V U x :=
  (cechAbCubeToCube R F V U).homology_cechAugHomology _

end Scalars

section Morphism

variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)

theorem preimage_cechOpen (s : Finset ι) :
    g ⁻¹ᵁ cechOpen V U s = cechOpen (g ⁻¹ᵁ V) (fun i => g ⁻¹ᵁ U i) s := by
  ext x
  exact mem_cechOpen.trans (mem_cechOpen (V := g ⁻¹ᵁ V) (U := fun i => g ⁻¹ᵁ U i)).symm

variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)

def sectionsOn.mapOver (W : X.Opens) : sectionsOn F W →ₛₗ[σ] sectionsOn G (g ⁻¹ᵁ W) where
  toFun x := (sectionsOn.toΓ G (g ⁻¹ᵁ W)).symm (φ.app W (sectionsOn.toΓ F W x))
  map_add' x y := map_add (φ.app W).hom x y
  map_smul' r x := by
    have h : g.app W (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) =
        restrictGlobal Y (g ⁻¹ᵁ W) (algebraMap S Γ(Y, ⊤) (σ r)) := by
      rw [← hσ]
      exact ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) _
    refine (φ.app_smul (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) x).trans ?_
    exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) =>
      (a • (show Γ(G, g ⁻¹ᵁ W) from φ.app W (sectionsOn.toΓ F W x)) : Γ(G, g ⁻¹ᵁ W))) h

theorem sectionsOn.toΓ_mapOver (W : X.Opens) (x : sectionsOn F W) :
    sectionsOn.toΓ G (g ⁻¹ᵁ W) (sectionsOn.mapOver hσ φ W x) = φ.app W (sectionsOn.toΓ F W x) :=
  rfl

theorem sectionsOn.mapOver_res {W W' : X.Opens} (h : W' ≤ W) (x : sectionsOn F W) :
    sectionsOn.mapOver hσ φ W' (sectionsOn.res R F h x) =
      sectionsOn.res S G (g.preimage_mono h) (sectionsOn.mapOver hσ φ W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

def cechCubeMapOver :
    Cube.SemiHom σ (cechCube R F V U) (cechCube S G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i) where
  app s := (sectionsOn.res S G (preimage_cechOpen g V U s).ge).comp
    (sectionsOn.mapOver hσ φ (cechOpen V U s))
  app_res {s t} h x :=
    (congrArg (sectionsOn.res S G (preimage_cechOpen g V U t).ge)
      (sectionsOn.mapOver_res hσ φ (cechOpen_anti V U h) x)).trans
      ((sectionsOn.res_res S G _ _ _).trans
        (sectionsOn.res_res S G _ (cechOpen_anti _ _ h) _).symm)


theorem cechCubeMapOver_id_bijective (s : Finset ι) : Function.Bijective
    ((cechCubeMapOver V U hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))).app s) :=
  (sectionsOn.congrOpens S G (preimage_cechOpen g V U s)).bijective

variable [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

variable (G) in

def cechCubePushforwardIso : cechCube R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cechCube R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  Cube.isoMk (fun s => LinearEquiv.ofBijective _
    (cechCubeMapOver_id_bijective (σ := RingHom.id R) V U hg s))
    (cechCubeMapOver (σ := RingHom.id R) V U hg (𝟙 _)).app_res


@[reassoc]
theorem cechCubePushforwardIso_naturality {G' : Y.Modules} (ψ : G ⟶ G') :
    cechCubeMap R V U ((Scheme.Modules.pushforward g).map ψ) ≫
        (cechCubePushforwardIso V U G' hg).hom =
      (cechCubePushforwardIso V U G hg).hom ≫ cechCubeMap R _ _ ψ :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext fun x =>
    sectionsOn.res_map R ψ (preimage_cechOpen g V U s).ge x))

variable (G) in

def cechPushforwardIso [LinearOrder ι] : cech R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cech R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  (cechFunctor ι R).mapIso (cechCubePushforwardIso V U G hg)

end Morphism

section Two

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules) (V : X.Opens)
  (U : Fin 2 → X.Opens)

def cechTwoXZero :
    (cech R F V U).X 0 ≃ₗ[R] sectionsOn F (V ⊓ U 0) × sectionsOn F (V ⊓ U 1) :=
  Cube.termOneFinTwo (cechCube R F V U) ≪≫ₗ
    (sectionsOn.congrOpens R F (cechOpen_singleton V U 0)).prodCongr
      (sectionsOn.congrOpens R F (cechOpen_singleton V U 1))

def cechTwoXOne : (cech R F V U).X 1 ≃ₗ[R] sectionsOn F (V ⊓ (U 0 ⊓ U 1)) :=
  Cube.termTwoFinTwo (cechCube R F V U) ≪≫ₗ sectionsOn.congrOpens R F (cechOpen_pair V U 0 1)

theorem cechTwo_d (x : (cech R F V U).X 0) :
    cechTwoXOne R F V U (((cech R F V U).d 0 1).hom x) =
      sectionsOn.res R F (inf_le_inf_left V inf_le_right) (cechTwoXZero R F V U x).2 -
        sectionsOn.res R F (inf_le_inf_left V inf_le_left) (cechTwoXZero R F V U x).1 := by
  rw [cech_d R F V U 0]
  refine (congrArg (sectionsOn.congrOpens R F (cechOpen_pair V U 0 1))
    (Cube.d_one_finTwo (cechCube R F V U) x)).trans ((map_sub _ _ _).trans ?_)
  exact congrArg₂ (· - ·)
    ((sectionsOn.res_res R F _ _ _).trans
      (sectionsOn.res_res R F (cechOpen_singleton V U 1).ge _ _).symm)
    ((sectionsOn.res_res R F _ _ _).trans
      (sectionsOn.res_res R F (cechOpen_singleton V U 0).ge _ _).symm)



theorem isZero_cechH_one_iff_surjective :
    IsZero (cechH R F V U 1) ↔ Function.Surjective ((cech R F V U).d 0 1).hom := by
  haveI := Cube.subsingleton_term (cechCube R F V U) (p := 0 + 2 + 1) (by simp)
  rw [cech_d R F V U 0]
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).symm.trans
    ((cechComplex_exactAt_succ_iff (cechCube R F V U) 0).trans (forall_congr' fun x => ?_))
  exact ⟨fun h => h.1 (Subsingleton.elim _ _), fun h => ⟨fun _ => h, fun _ => Subsingleton.elim _ _⟩⟩

end Two

section Affine

variable {A : CommRingCat.{u}} (M : ModuleCat.{u} A)

def tildeToSections (W : (Spec A).Opens) : M →ₗ[A] sectionsOn (tilde M) W :=
  (sectionsOn.specEquiv (tilde M) W).symm.toLinearMap ∘ₗ (tilde.toOpen M W).hom

@[simp]
theorem res_tildeToSections {W W' : (Spec A).Opens} (h : W' ≤ W) (m : M) :
    sectionsOn.res A (tilde M) h (tildeToSections M W m) = tildeToSections M W' m := rfl

def basicOpenFamily (f : ι → A) : ι → (Spec A).Opens := fun i => PrimeSpectrum.basicOpen (f i)


theorem isLocalizedModule_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) : IsLocalizedModule.Away f (tildeToSections M W) := by
  have h₀ : IsLocalizedModule.Away f (tilde.toOpen M W).hom := by
    subst h
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (tilde.toOpen M W).hom (sectionsOn.specEquiv (tilde M) W).symm

theorem cechOpen_basicOpenFamily (f : ι → A) (s : Finset ι) :
    cechOpen ⊤ (basicOpenFamily f) s = PrimeSpectrum.basicOpen (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [cechOpen_empty, Finset.prod_empty]
    exact PrimeSpectrum.basicOpen_one.symm
  | insert a s ha ih =>
    rw [cechOpen_insert, ih, Finset.prod_insert ha]
    exact (PrimeSpectrum.basicOpen_mul _ _).symm

theorem iSup_basicOpenFamily_eq_top_iff (f : ι → A) :
    ⨆ i, basicOpenFamily f i = ⊤ ↔ Ideal.span (Set.range f) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff

theorem cechCube_tilde_exactAt [LinearOrder ι] [Finite ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    (cubeComplex (cechCube A (tilde M) ⊤ (basicOpenFamily f))).ExactAt p :=
  cubeComplex_exactAt_of_isLocalizedModule _ f
    (fun s => tildeToSections M (cechOpen ⊤ (basicOpenFamily f) s))
    (fun s => isLocalizedModule_tildeToSections M _ (cechOpen_basicOpenFamily f s))
    (fun h m => res_tildeToSections M (cechOpen_anti _ _ h) m) hf p

theorem isZero_cechH_tilde_succ [LinearOrder ι] [Finite ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    IsZero (cechH A (tilde M) ⊤ (basicOpenFamily f) (p + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff_cube _ p).2 (cechCube_tilde_exactAt M hf (p + 2)))

def cechHZeroTildeEquiv [LinearOrder ι] {f : ι → A} (hf : Ideal.span (Set.range f) = ⊤) :
    cechH A (tilde M) ⊤ (basicOpenFamily f) 0 ≃ₗ[A] M :=
  cechHZeroEquiv A (tilde M) ((iSup_basicOpenFamily_eq_top_iff f).2 hf).ge ≪≫ₗ
    sectionsOn.specEquiv (tilde M) ⊤ ≪≫ₗ (tilde.isoTop M).toLinearEquiv.symm


def awayTransition {a b : A} (h : a ∣ b) :
    LocalizedModule (.powers a) M →ₗ[A] LocalizedModule (.powers b) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M)
    (isUnit_powers_of_dvd h (LocalizedModule.mkLinearMap _ M))

@[simp]
theorem awayTransition_mk_one {a b : A} (h : a ∣ b) (m : M) :
    awayTransition M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m

def sectionsAwayEquiv (f : A) {W : (Spec A).Opens} (h : W = PrimeSpectrum.basicOpen f) :
    sectionsOn (tilde M) W ≃ₗ[A] LocalizedModule (.powers f) M :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv (.powers f) (tildeToSections M W) (LocalizedModule.mkLinearMap _ M)

@[simp]
theorem sectionsAwayEquiv_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) (m : M) :
    sectionsAwayEquiv M f h (tildeToSections M W m) = LocalizedModule.mk m 1 :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv_apply (.powers f) _ _ m

theorem sectionsAwayEquiv_res {a b : A} (hab : a ∣ b) {W W' : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen a) (h' : W' = PrimeSpectrum.basicOpen b) (hW : W' ≤ W)
    (x : sectionsOn (tilde M) W) :
    sectionsAwayEquiv M b h' (sectionsOn.res A (tilde M) hW x) =
      awayTransition M hab (sectionsAwayEquiv M a h x) := by
  haveI := isLocalizedModule_tildeToSections M a h
  have := IsLocalizedModule.ext (.powers a) (tildeToSections M W)
    (isUnit_powers_of_dvd hab (LocalizedModule.mkLinearMap _ M))
    (j := (sectionsAwayEquiv M b h').toLinearMap ∘ₗ sectionsOn.res A (tilde M) hW)
    (k := awayTransition M hab ∘ₗ (sectionsAwayEquiv M a h).toLinearMap) (by ext m; simp)
  exact congr($this x)

variable (f g : A)

abbrev twoCharts : Fin 2 → (Spec A).Opens := basicOpenFamily ![f, g]



theorem twoCharts_inf : ⊤ ⊓ (twoCharts f g 0 ⊓ twoCharts f g 1) = PrimeSpectrum.basicOpen (f * g) :=
  (top_inf_eq _).trans (PrimeSpectrum.basicOpen_mul f g).symm

def twoChartsXZero : (cech A (tilde M) ⊤ (twoCharts f g)).X 0 ≃ₗ[A]
    LocalizedModule (.powers f) M × LocalizedModule (.powers g) M :=
  cechTwoXZero A (tilde M) ⊤ (twoCharts f g) ≪≫ₗ
    (sectionsAwayEquiv M f (top_inf_eq _)).prodCongr (sectionsAwayEquiv M g (top_inf_eq _))

def twoChartsXOne :
    (cech A (tilde M) ⊤ (twoCharts f g)).X 1 ≃ₗ[A] LocalizedModule (.powers (f * g)) M :=
  cechTwoXOne A (tilde M) ⊤ (twoCharts f g) ≪≫ₗ sectionsAwayEquiv M (f * g) (twoCharts_inf f g)

theorem twoCharts_d (x : (cech A (tilde M) ⊤ (twoCharts f g)).X 0) :
    twoChartsXOne M f g (((cech A (tilde M) ⊤ (twoCharts f g)).d 0 1).hom x) =
      awayTransition M (dvd_mul_left g f) (twoChartsXZero M f g x).2 -
        awayTransition M (dvd_mul_right f g) (twoChartsXZero M f g x).1 :=
  (congrArg (sectionsAwayEquiv M (f * g) (twoCharts_inf f g))
    (cechTwo_d A (tilde M) ⊤ (twoCharts f g) x)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·)
      (sectionsAwayEquiv_res M _ (top_inf_eq _) _ _ _)
      (sectionsAwayEquiv_res M _ (top_inf_eq _) _ _ _)))


theorem isZero_cechH_twoCharts_one_iff : IsZero (cechH A (tilde M) ⊤ (twoCharts f g) 1) ↔
    ∀ z, ∃ a b, awayTransition M (dvd_mul_left g f) b - awayTransition M (dvd_mul_right f g) a =
      z := by
  rw [isZero_cechH_one_iff_surjective]
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := h ((twoChartsXOne M f g).symm z)
    exact ⟨_, _, by rw [← twoCharts_d, hx, LinearEquiv.apply_symm_apply]⟩
  · intro h z
    obtain ⟨a, b, hab⟩ := h (twoChartsXOne M f g z)
    refine ⟨(twoChartsXZero M f g).symm (a, b), (twoChartsXOne M f g).injective ?_⟩
    rw [twoCharts_d, LinearEquiv.apply_symm_apply, hab]

theorem span_range_pair_one_sub : Ideal.span (Set.range ![f, 1 - f]) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (by
    simpa using Ideal.add_mem _ (Ideal.subset_span (s := Set.range ![f, 1 - f]) ⟨0, rfl⟩)
      (Ideal.subset_span ⟨1, rfl⟩))


def cechHZeroTwoChartsEquiv : cechH A (tilde M) ⊤ (twoCharts f (1 - f)) 0 ≃ₗ[A] M :=
  cechHZeroTildeEquiv M (span_range_pair_one_sub f)

theorem isZero_cechH_twoCharts_succ (p : ℕ) :
    IsZero (cechH A (tilde M) ⊤ (twoCharts f (1 - f)) (p + 1)) :=
  isZero_cechH_tilde_succ M (span_range_pair_one_sub f) p

def cechHZeroStructureTwoChartsEquiv :
    cechH A (structureModule (Spec A)) ⊤ (twoCharts f (1 - f)) 0 ≃ₗ[A] A :=
  (cechHMapIso A ⊤ (twoCharts f (1 - f)) tildeSelf 0).toLinearEquiv.symm ≪≫ₗ
    cechHZeroTwoChartsEquiv (ModuleCat.of A A) f

theorem isZero_cechH_structure_twoCharts_succ (p : ℕ) :
    IsZero (cechH A (structureModule (Spec A)) ⊤ (twoCharts f (1 - f)) (p + 1)) :=
  (isZero_cechH_twoCharts_succ (ModuleCat.of A A) f p).of_iso
    (cechHMapIso A ⊤ (twoCharts f (1 - f)) tildeSelf (p + 1)).symm

theorem exists_pow_mul_pow_eq_of_isZero_cechH
    (h : IsZero (cechH A (structureModule (Spec A)) ⊤ (twoCharts f g) 1)) :
    ∃ (n k : ℕ) (a b : A), f ^ n * g ^ k = f ^ (n + 1) * b + g ^ (k + 1) * a := by
  obtain ⟨a, b, hab⟩ := (isZero_cechH_twoCharts_one_iff (ModuleCat.of A A) f g).1
    (h.of_iso (cechHMapIso A ⊤ (twoCharts f g) tildeSelf 1))
    (LocalizedModule.mk (1 : A) ⟨f * g, 1, pow_one _⟩)
  obtain ⟨n, a', ha⟩ := IsLocalizedModule.Away.surj (LocalizedModule.mkLinearMap _ _) f a
  obtain ⟨k, b', hb⟩ := IsLocalizedModule.Away.surj (LocalizedModule.mkLinearMap _ _) g b
  let l : A →ₗ[A] LocalizedModule (.powers (f * g)) A := LocalizedModule.mkLinearMap _ _
  have h₁ : f ^ n • awayTransition (ModuleCat.of A A) (dvd_mul_right f g) a = l a' := by
    rw [← map_smul, ha]; exact awayTransition_mk_one (ModuleCat.of A A) _ a'
  have h₂ : g ^ k • awayTransition (ModuleCat.of A A) (dvd_mul_left g f) b = l b' := by
    rw [← map_smul, hb]; exact awayTransition_mk_one (ModuleCat.of A A) _ b'
  have h₃ : (f * g) • LocalizedModule.mk (1 : A) (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g)) =
      l 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g)) (1 : A)
  have h₄ : l ((f ^ n * g ^ k) • (1 : A)) =
      l ((f ^ n * (f * g)) • b' - (g ^ k * (f * g)) • a') := by
    rw [map_sub, map_smul, map_smul, map_smul, ← h₁, ← h₂, ← h₃, ← hab]
    simp only [smul_sub, smul_smul]
    congr 2 <;> ring
  obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq (f * g) h₄
  refine ⟨n + m, k + m, -(f ^ (m + 1) * a'), g ^ (m + 1) * b', ?_⟩
  simp only [smul_eq_mul, mul_pow] at hm
  linear_combination hm

end Affine

example :
    letI := algebraΓSpec (.of ℤ)
    Nontrivial (cechH (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
      (twoCharts (A := .of ℤ) 3 (1 - 3)) 0) ∧
    IsZero (cechH (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
      (twoCharts (A := .of ℤ) 3 (1 - 3)) 1) :=
  ⟨(cechHZeroStructureTwoChartsEquiv (A := .of ℤ) 3).toEquiv.nontrivial,
    isZero_cechH_structure_twoCharts_succ (A := .of ℤ) 3 0⟩

example : Nontrivial (cechAbH (structureModule (Spec (.of ℤ))).presheaf ⊤
    (twoCharts (A := .of ℤ) 3 (1 - 3)) 0) :=
  letI := algebraΓSpec (.of ℤ)
  haveI := (cechHZeroStructureTwoChartsEquiv (A := .of ℤ) 3).toEquiv.nontrivial
  (cechAbHEquiv (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
    (twoCharts (A := .of ℤ) 3 (1 - 3)) 0).toEquiv.nontrivial

example {A : CommRingCat.{u}} (M : ModuleCat.{u} A) (f g : A) (m : M) :
    twoChartsXOne M f g (((cech A (tilde M) ⊤ (twoCharts f g)).d 0 1).hom
      ((twoChartsXZero M f g).symm (LocalizedModule.mk m 1, 0))) = -LocalizedModule.mk m 1 := by
  rw [twoCharts_d, LinearEquiv.apply_symm_apply, map_zero, awayTransition_mk_one, zero_sub]

example :
    letI := algebraΓSpec (.of (Polynomial ℤ))
    ¬ IsZero (cechH (CommRingCat.of (Polynomial ℤ)) (structureModule (Spec (.of (Polynomial ℤ)))) ⊤
      (twoCharts (A := .of (Polynomial ℤ)) (Polynomial.C 2) Polynomial.X) 1) := by
  intro h
  obtain ⟨n, k, a, b, hab⟩ := exists_pow_mul_pow_eq_of_isZero_cechH (A := .of (Polynomial ℤ))
    (Polynomial.C 2) Polynomial.X h
  have h₁ : (Polynomial.C (2 : ℤ) ^ n * Polynomial.X ^ k).coeff k =
      (Polynomial.C (2 : ℤ) ^ (n + 1) * b + Polynomial.X ^ (k + 1) * a).coeff k :=
    congrArg (fun p : Polynomial ℤ => p.coeff k) hab
  rw [← map_pow, ← map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self, Polynomial.coeff_X_pow_mul', if_neg (by omega), add_zero,
    pow_succ, mul_assoc] at h₁
  have h₂ := mul_left_cancel₀ (by positivity : (2 : ℤ) ^ n ≠ 0) h₁
  omega

end GlobalTheory
end
end
