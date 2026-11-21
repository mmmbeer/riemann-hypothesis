import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrGeneric

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusCot

open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.Conormal GlobalTheory.SS.TorusSlice

theorem isFrame_append {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : IsFrame e₁) (he₂ : IsFrame e₂) :
    IsFrame (Fin.append (fun i => p₁.app U (e₁ i)) fun j => p₂.app U (e₂ j)) := by
  let ψ (V : S.Opens) : (Γ(F₁, V) × Γ(F₂, V)) ≃ₗ[Γ(S, V)] Γ(F, V) :=
    LinearEquiv.ofBijective ((QCoh.appLinear p₁ V).coprod (QCoh.appLinear p₂ V)) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ hab
      change p₁.app V a + p₂.app V b = 0 at hab
      have a₁ := congrArg (i₁.app V) hab
      have a₂ := congrArg (i₂.app V) hab
      rw [map_add, map_zero, QCoh.app_app, QCoh.app_app] at a₁ a₂
      rw [h₁, h₄] at a₁
      rw [h₃, h₂] at a₂
      ext
      · simpa using a₁
      · simpa using a₂, fun c => ⟨(i₁.app V c, i₂.app V c), congr(($h).app V c)⟩⟩
  refine isFrame_of_basis (fun V k => (((he₁.basis k).prod (he₂.basis k)).map (ψ V)).reindex finSumFinEquiv)
    fun V k i => ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
  rcases i with i | i
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]

section Geo

variable {S : Scheme.{0}} {T G B Y : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
  [IsMonHom u] {j : Y ⟶ G} {σ : Y ⟶ T}

end Geo

end GlobalTheory.TorusCot

namespace GlobalTheory.TorusPart

open GlobalTheory.TorusCot GlobalTheory.QCoh

end GlobalTheory.TorusPart
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeProd

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_resM app_resM)

section Split

variable {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U V : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : VB.IsFrame e₁) (he₂ : VB.IsFrame e₂)

include h h₁ h₂ h₃ h₄ in

theorem repr_left (hV : V ≤ U) (y : Γ(F, V)) (i : Fin n) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.castAdd m i) =
      (he₁.basis hV).repr (i₁.app V y) i := by
  have key : (Finsupp.lapply (Fin.castAdd m i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₁.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₁ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₁]
      change _ = ((he₁.basis hV).repr ((resM F₁ hV) (e₁ j))) i
      rw [← IsFrame.basis_apply he₁ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.castAdd_inj]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₄]
      change _ = ((he₁.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
  exact LinearMap.congr_fun key y

include h h₁ h₂ h₃ h₄ in

theorem repr_right (hV : V ≤ U) (y : Γ(F, V)) (i : Fin m) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.natAdd n i) =
      (he₂.basis hV).repr (i₂.app V y) i := by
  have key : (Finsupp.lapply (Fin.natAdd n i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₂.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₂ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₃]
      change _ = ((he₂.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₂]
      change _ = ((he₂.basis hV).repr ((resM F₂ hV) (e₂ j))) i
      rw [← IsFrame.basis_apply he₂ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.natAdd_inj]
  exact LinearMap.congr_fun key y

include h h₁ h₂ h₃ h₄ in

theorem detUnit_append {U' : S.Opens} {e₁' : Fin n → Γ(F₁, U')} {e₂' : Fin m → Γ(F₂, U')}
    (he₁' : VB.IsFrame e₁') (he₂' : VB.IsFrame e₂') (hV : V ≤ U) (hV' : V ≤ U') :
    (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).detUnit
                 (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁' he₂') hV hV' =
      he₁.detUnit he₁' hV hV' * he₂.detUnit he₂' hV hV' := by
  refine Units.ext ?_
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).toMatrix
      (fun k => resM F hV' (Fin.append (fun i => p₁.app U' (e₁' i)) (fun j => p₂.app U' (e₂' j)) k)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
        ((he₁.basis hV).toMatrix fun i => resM F₁ hV' (e₁' i)) 0 0
        ((he₂.basis hV).toMatrix fun i => resM F₂ hV' (e₂' i))) := by
    ext k l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      simp only [Module.Basis.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fin.append_left,
        Fin.append_right, Matrix.zero_apply]
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₁]; rfl
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₄]
      change ((he₁.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₃]
      change ((he₂.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₂]; rfl
  rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Split

section Prod

open GlobalTheory.Conormal

variable {S : Scheme.{0}} (G H : Over S) [GrpObj G] [GrpObj H]

theorem lbIso_det_conormal_prod [QuasiSeparated G.hom] [QuasiSeparated H.hom] (g h : ℕ)
    (hG : IsVB (omega G) g) (hH : IsVB (omega H) h) (t : 𝟙_ (Over S) ⟶ G ⊗ H) (ht : t = lift η[G] η[H]) :
    LBIso (VB.det (conormal (sec t)) (g + h)) (CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)) := by
  subst ht
  have i₁ : η[G] ≫ lift (𝟙 G) (toUnit G ≫ η[H]) = lift η[G] η[H] := by simp
  have i₂ : η[H] ≫ lift (toUnit H ≫ η[G]) (𝟙 H) = lift η[G] η[H] := by simp
  have p₁ := lift_fst η[G] η[H]
  have p₂ := lift_snd η[G] η[H]
  have c₁ : η[H] ≫ toUnit H ≫ η[G] = η[G] := by simp
  have c₂ : η[G] ≫ toUnit G ≫ η[H] = η[H] := by simp
  have H₀ := cotMap_prod i₁ i₂ p₁ p₂
  have H₁ := (cotMap_comp p₁ i₁ (lift_fst _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₂ := (cotMap_comp p₂ i₂ (lift_snd _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₃ := (cotMap_comp p₁ i₂ (lift_fst _ _) c₁).trans (cotMap_eq_zero rfl _)
  have H₄ := (cotMap_comp p₂ i₁ (lift_snd _ _) c₂).trans (cotMap_eq_zero rfl _)
  let L := CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)
  have hL : L.IsLB := CechPic.isLB_tens hG.isLB_det hH.isLB_det
  have he : ∀ p : L.ι, IsFrame (Fin.append
      (fun i => (cotMap (fst G H) p₁).app (L.U p) (resM (omega G) inf_le_left (p.1.e i)))
      (fun j => (cotMap (snd G H) p₂).app (L.U p) (resM (omega H) inf_le_right (p.2.e j)))) := fun p =>
    GlobalTheory.TorusCot.isFrame_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
  refine LBIso.symm (lbIso_det_of_frames hL _ he fun p q => ?_).2
  refine Eq.trans ?_ (detUnit_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
    (q.1.isFrame.res inf_le_left) (q.2.isFrame.res inf_le_right) inf_le_left inf_le_right).symm
  exact congrArg₂ (· * ·) ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)
    ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)

end Prod

end GlobalTheory.HodgeProd
end
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgePow

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CechPic

theorem lbIso_hodge_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B)
    (he : η[A] ≫ e.hom = η[B]) (r : ℕ) (hA : IsVB (omega A) r) :
    IsVB (omega B) r ∧ LBIso (GlobalTheory.SiegelTor.hodge A r) (GlobalTheory.SiegelTor.hodge B r) := by
  have he' : η[B] ≫ e.inv = η[A] := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  let φ : omega A ≅ omega B :=
    { hom := cotMap e.inv he'
      inv := cotMap e.hom he
      hom_inv_id := (cotMap_comp he' he e.hom_inv_id (Category.comp_id _)).trans (cotMap_id rfl _)
      inv_hom_id := (cotMap_comp he he' e.inv_hom_id (Category.comp_id _)).trans (cotMap_id rfl _) }
  exact ⟨hA.of_iso φ, hA.lbIso_det_of_iso φ⟩

def prodUnitIso {S : Scheme.{0}} (G : Over S) : G ⊗ 𝟙_ (Over S) ≅ G where
  hom := fst _ _
  inv := lift (𝟙 G) (toUnit G)
  hom_inv_id := by ext1 <;> simp <;> exact toUnit_unique _ _
  inv_hom_id := by simp

section Pow

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [QuasiSeparated G.hom] (g : ℕ)

theorem cls_hodge_powObj [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    (hs : SmoothOfRelativeDimension g G.hom) (hG : IsVB (omega G) g) (n : ℕ) :
    ∃ h : IsVB (omega (powObj G (n + 1))) ((n + 1) * g),
      cls _ h.isLB_det = (n + 1) • cls _ hG.isLB_det := by
  have hV : ∀ m, IsVB (omega (powObj G m)) (m * g) := fun m => by
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G m).2.1
    haveI := smoothOfRelativeDimension_powObj G g hs m
    exact isVB_omega _ _
  refine ⟨hV (n + 1), ?_⟩
  induction n with
  | zero =>
    have hE : η[G ⊗ 𝟙_ (Over S)] ≫ (prodUnitIso G).hom = η[G] := by simp [prodUnitIso]
    have h1 := hV 1
    rw [Nat.one_mul] at h1
    have := (lbIso_hodge_of_iso (prodUnitIso G) hE g h1).2
    rw [Nat.zero_add, one_smul]
    have hh : ∀ (r : ℕ) (hr : r = 1 * g) (h₁ : IsVB (omega (powObj G 1)) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det := by
      intro r hr h₁
      rw [Nat.one_mul] at hr
      subst hr
      exact (cls_eq_iff _ _).2 this
    exact hh _ rfl (hV 1)
  | succ n ih =>
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G (n + 1)).2.1
    have key := GlobalTheory.HodgeProd.lbIso_det_conormal_prod G (powObj G (n + 1)) g ((n + 1) * g) hG (hV (n + 1))
      η[G ⊗ powObj G (n + 1)] (by ext1 <;> simp)
    have hT := isLB_tens hG.isLB_det (hV (n + 1)).isLB_det
    have hh : ∀ (r : ℕ) (hr : r = g + (n + 1) * g) (h₁ : IsVB (omega (powObj G (n + 1 + 1))) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det + cls _ (hV (n + 1)).isLB_det := by
      intro r hr h₁
      subst hr
      rw [← cls_tens _ _ hT]
      exact (cls_eq_iff _ _).2 key
    rw [hh _ (by ring) (hV _), ih, succ_nsmul' _ (n + 1)]

theorem one_powPr {n : ℕ} (i : Fin n) : η[powObj G n] ≫ powPr G i = η[G] := by
  haveI := powPr.isMonHom G i
  exact IsMonHom.one_hom _

end Pow

theorem hodge_eight_mul_iso_hodge_pow_eight : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)),
    (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) →
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  intro S G H _ _ g pr hpr hU hG hs
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : SmoothOfRelativeDimension g G.hom := hs
  have hVG : IsVB (omega G) g := isVB_omega G g
  obtain ⟨hP, hc⟩ := cls_hodge_powObj G g hs hVG 7
  let lim : IsLimit (Fan.mk H pr) := mkFanLimit _ (fun s => (hU s.pt s.proj).exists.choose)
    (fun s i => (hU s.pt s.proj).exists.choose_spec i)
    (fun s m hm => (hU s.pt s.proj).unique hm (hU s.pt s.proj).exists.choose_spec)
  let e : H ≅ powObj G 8 := lim.conePointUniqueUpToIso (powIsLimit G 8)
  have he : ∀ i, e.hom ≫ powPr G i = pr i := fun i =>
    lim.conePointUniqueUpToIso_hom_comp (powIsLimit G 8) ⟨i⟩
  have hη : η[powObj G 8] ≫ e.inv = η[H] := by
    refine lim.hom_ext fun ⟨i⟩ => ?_
    have h1 : e.inv ≫ pr i = powPr G i := by rw [← he, Iso.inv_hom_id_assoc]
    haveI := hpr i
    simp only [Fan.mk_π_app, Category.assoc, h1]
    exact (one_powPr G i).trans (IsMonHom.one_hom (pr i)).symm
  obtain ⟨hH, hiso⟩ := lbIso_hodge_of_iso e.symm hη (8 * g) hP
  have hL := hVG.isLB_det
  refine (cls_eq_iff hH.isLB_det (isLB_lbPow hL 8)).1 ?_
  rw [cls_lbPow hL, ← (cls_eq_iff hP.isLB_det hH.isLB_det).2 hiso]
  exact hc

end GlobalTheory.HodgePow
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLineBundle_eighthPower_iso_pow : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  atlas_forward_decl GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight
end
