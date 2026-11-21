import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurve
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.NeronLieSeminegative
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.NeronModelExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonpos

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiNegative_descends_fieldExtension_curve : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  first | exact @GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange | exact GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange | (intros; apply GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite TensorProduct

universe u

noncomputable section

namespace GlobalTheory.StalkProd

variable {X : Scheme.{u}}

def homMk {F G : X.Modules} (φ : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U))
    (hφ : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)),
      φ V (F.presheaf.map i.op s) = G.presheaf.map i.op (φ U s)) : F ⟶ G :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (φ U.unop).toAddMonoidHom
      naturality := fun _ _ i => by
        ext s
        exact hφ i.unop s }
    (fun U r m => (φ U.unop).map_smul r m)

@[simp] theorem homMk_app {F G : X.Modules} (φ : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U))
    (hφ : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)),
      φ V (F.presheaf.map i.op s) = G.presheaf.map i.op (φ U s)) (U : X.Opens) (s : Γ(F, U)) :
    (homMk φ hφ).app U s = φ U s := rfl

section Pi

variable (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module (X.presheaf.stalk x) (E x)]

def presheafAb : TopCat.Presheaf Ab.{u} X where
  obj U := AddCommGrpCat.of (∀ x : U.unop, E x)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, i.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem isSheaf_presheafAb : (presheafAb E).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget Ab.{u})]
  exact TopCat.Presheaf.toTypes_isSheaf X E

abbrev secModule (U : X.Opens) : Module Γ(X, U) (∀ x : U, E x) :=
  @Pi.module U (fun x : U => E x.1) Γ(X, U) _ _ fun x => Module.compHom (E x.1) (X.presheaf.germ U x.1 x.2).hom

def pi : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((presheafAb E).obj U) :=
    fun U => secModule E U.unop
  { val := PresheafOfModules.ofPresheaf (presheafAb E) fun U V i r s => by
      funext x
      show X.presheaf.germ U.unop x.1 _ r • s ⟨x.1, i.unop.le x.2⟩ =
        X.presheaf.germ V.unop x.1 x.2 (X.presheaf.map i r) • s ⟨x.1, i.unop.le x.2⟩
      rw [← Quiver.Hom.op_unop i, X.presheaf.germ_res_apply i.unop x.1 x.2 r]
    isSheaf := isSheaf_presheafAb E }

variable {E}

def fam {U : X.Opens} (s : Γ(pi E, U)) : ∀ x : U, E x := s

def mk {U : X.Opens} (s : ∀ x : U, E x) : Γ(pi E, U) := s

@[simp] theorem fam_mk {U : X.Opens} (s : ∀ x : U, E x) : fam (mk s) = s := rfl

@[simp] theorem fam_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(pi E, U)) (x : U) :
    fam (r • s) x = X.presheaf.germ U x.1 x.2 r • fam s x := rfl

@[simp] theorem fam_add {U : X.Opens} (s t : Γ(pi E, U)) (x : U) :
    fam (s + t) x = fam s x + fam t x := rfl

@[simp] theorem fam_zero {U : X.Opens} (x : U) : fam (0 : Γ(pi E, U)) x = 0 := rfl

@[simp] theorem fam_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(pi E, U)) (x : V) :
    fam ((pi E).presheaf.map i.op s) x = fam s ⟨x.1, i.le x.2⟩ := rfl

variable {E' : X → Type u} [∀ x, AddCommGroup (E' x)] [∀ x, Module (X.presheaf.stalk x) (E' x)]

def piMap (L : ∀ x, E x →ₗ[X.presheaf.stalk x] E' x) : pi E ⟶ pi E' :=
  homMk (fun U =>
    { toFun := fun s => mk fun x => L x.1 (fam s x)
      map_add' := fun s t => funext fun x => map_add (L x.1) _ _
      map_smul' := fun r s => funext fun x => (L x.1).map_smul _ _ })
    fun _ _ => rfl

@[simp] theorem fam_piMap_app (L : ∀ x, E x →ₗ[X.presheaf.stalk x] E' x) {U : X.Opens}
    (s : Γ(pi E, U)) (x : U) : fam ((piMap L).app U s) x = L x.1 (fam s x) := rfl

end Pi

def germs (F : X.Modules) : F ⟶ pi (fun x => (F.presheaf.stalk x : Type u)) :=
  homMk (fun U =>
    { toFun := fun s => mk fun x => F.presheaf.germ U x.1 x.2 s
      map_add' := fun s t => funext fun x => map_add _ _ _
      map_smul' := fun r s => funext fun x => QCoh.germ_smul F x.1 x.2 r s })
    fun i s => funext fun x => F.presheaf.germ_res_apply i x.1 x.2 s

@[simp] theorem fam_germs_app (F : X.Modules) {U : X.Opens} (s : Γ(F, U)) (x : U) :
    fam ((germs F).app U s) x = F.presheaf.germ U x.1 x.2 s := rfl

section Tensor

variable {Y : Scheme.{u}} (f : X ⟶ Y)

abbrev stalkAlgebra (x : X) : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

attribute [local instance] stalkAlgebra

variable (M : Y.Modules)

def tensorStalk (x : X) : Type u :=
  X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] (M.presheaf.stalk (f x) : Type u)

instance (x : X) : AddCommGroup (tensorStalk f M x) :=
  inferInstanceAs (AddCommGroup (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
    (M.presheaf.stalk (f x) : Type u)))

instance (x : X) : Module (X.presheaf.stalk x) (tensorStalk f M x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
    (M.presheaf.stalk (f x) : Type u)))

def oneTmul (x : X) (m : (M.presheaf.stalk (f x) : Type u)) : tensorStalk f M x :=
  (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m

theorem oneTmul_add (x : X) (m n : (M.presheaf.stalk (f x) : Type u)) :
    oneTmul f M x (m + n) = oneTmul f M x m + oneTmul f M x n :=
  TensorProduct.tmul_add _ _ _

theorem oneTmul_smul (x : X) (a : Y.presheaf.stalk (f x)) (m : (M.presheaf.stalk (f x) : Type u)) :
    oneTmul f M x (a • m) = f.stalkMap x a • oneTmul f M x m := by
  change (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] (a • m) =
    (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) a) •
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m)
  rw [algebraMap_smul, TensorProduct.tmul_smul]

theorem oneTmul_germ_smul {V : Y.Opens} (r : Γ(Y, V)) (s : Γ(M, V)) (x : X) (hx : f x ∈ V) :
    oneTmul f M x (M.presheaf.germ V (f x) hx (r • s)) =
      X.presheaf.germ (f ⁻¹ᵁ V) x hx (f.app V r) • oneTmul f M x (M.presheaf.germ V (f x) hx s) := by
  rw [QCoh.germ_smul, oneTmul_smul, Scheme.Hom.germ_stalkMap_apply]

theorem oneTmul_germ_res {U V : Y.Opens} (i : V ⟶ U) (s : Γ(M, U)) (x : X) (hx : f x ∈ V) :
    oneTmul f M x (M.presheaf.germ V (f x) hx (M.presheaf.map i.op s)) =
      oneTmul f M x (M.presheaf.germ U (f x) (i.le hx) s) := by
  rw [M.presheaf.germ_res_apply]

def toPi : M ⟶ (Scheme.Modules.pushforward f).obj (pi (tensorStalk f M)) :=
  homMk (fun V =>
    { toFun := fun s => (mk fun x => oneTmul f M x.1 (M.presheaf.germ V (f x.1) x.2 s) :
        Γ(pi (tensorStalk f M), f ⁻¹ᵁ V))
      map_add' := fun s t => funext fun x => by
        show oneTmul f M x.1 (M.presheaf.germ V (f x.1) x.2 (s + t)) = _
        rw [map_add, oneTmul_add]; rfl
      map_smul' := fun r s => funext fun x => by
        exact oneTmul_germ_smul f M r s x.1 x.2 })
    fun i s => funext fun x => oneTmul_germ_res f M i s x.1 x.2

def stalkUnit (x : X) : (M.presheaf.stalk (f x) : Type u) →+
    (((Scheme.Modules.pullback f).obj M).presheaf.stalk x : Type u) :=
  ((TopCat.Presheaf.stalkFunctor Ab.{u} (f x)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf ≫
    TopCat.Presheaf.stalkPushforward Ab.{u} f.base ((Scheme.Modules.pullback f).obj M).presheaf x).hom

variable {M} {M' : Y.Modules}

end Tensor

end GlobalTheory.StalkProd
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

theorem exists_torus_hom_extension : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i₀ : splitTorus (Sp K) X ⟶ (Over.pullback x).obj G) [IsMonHom i₀],
    ∃ (i : splitTorus C X ⟶ G) (ψ : (splitTorus (Sp K) X).left ⟶ (splitTorus C X).left), IsMonHom i ∧
      IsGrpPullback (splitTorus (Sp K) X) (splitTorus C X) x ψ ∧ ψ ≫ i.left = i₀.left ≫ pullback.fst G.hom x := by
  intro k _ C _ hC K _ x hx G _ hG X _ _ _ i₀ _
  obtain ⟨hs, -, hc⟩ := hC
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  have hN : Geo.Tor.IsNormalScheme C :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension (Sp k) C (strHom k C) 1
      (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec k)
  obtain ⟨hxd, hxp⟩ := hx
  have hj : IsGenericPointHom x := IsGenericPointHom.of_isPreimmersion x
  have hT := GlobalTheory.Diag.isSemiAbelian C X
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian (splitTorus C X) hT
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have := hT.quasiCompact
  have := hG.smooth
  have hφ := GlobalTheory.Diag.isGrpPullback X x
  obtain ⟨V, hV, -, g, hg, w, h₁, h₂⟩ :=
    spread_hom_generic_of_isGrpPullback hj hφ (isGrpPullback_pullback G x) i₀
  have : IsDominant V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact V.isOpen.dense ⟨_, hV⟩⟩
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.homExtNormal C V V.ι hN inferInstance inferInstance (splitTorus C X) G hT hG g hg
  refine ⟨F, _, hF, hφ, ?_⟩
  rw [← h₂, ← hF', GlobalTheory.ExtUnique.pullback_map_left_fst, ← h₁]
  exact Category.assoc _ _ _

end GlobalTheory.NeronCurve
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusLieRetraction

open IsLocalRing GlobalTheory.HodgeTateCompare GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem lieEquiv_add' {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (v w : Lie G) :
    lieEquiv G (v + w) = lieAdd G (lieEquiv G v) (lieEquiv G w) :=
  Subtype.ext (lieEquiv_add v w)

theorem lieEquiv_smul' {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (a : R) (v : Lie G) :
    lieEquiv G (a • v) = lieScale G a (lieEquiv G v) :=
  Subtype.ext (lieEquiv_smul a v)

def lieLin {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] :
    Lie T →ₗ[R] Lie G where
  toFun v := (lieEquiv G).symm (lieMap u (lieEquiv T v))
  map_add' v w := by
    apply (lieEquiv G).injective
    rw [Equiv.apply_symm_apply, lieEquiv_add', lieEquiv_add', Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).1 _ _
  map_smul' a v := by
    apply (lieEquiv G).injective
    rw [Equiv.apply_symm_apply, lieEquiv_smul', RingHom.id_apply, lieEquiv_smul',
      Equiv.apply_symm_apply]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).2 _ _

theorem lieEquiv_lieLin {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G)
    [IsMonHom u] (v : Lie T) : lieEquiv G (lieLin u v) = lieMap u (lieEquiv T v) :=
  Equiv.apply_symm_apply _ _

theorem res_comp_of_mem {M : Type} [AddCommGroup M] [Module R M] {v : Module.Dual R M}
    (hv : v ∈ (maximalIdeal R) • (⊤ : Submodule R (Module.Dual R M))) :
    (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0 := by
  refine Submodule.smul_induction_on (p := fun v : Module.Dual R M =>
    (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) hv ?_ ?_
  · intro a ha w _
    ext c
    simp [IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha]
  · intro x y hx hy
    rw [LinearMap.comp_add, hx, hy, add_zero]

theorem mem_of_res_comp {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {v : Module.Dual R M}
    (hv : (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) :
    v ∈ (maximalIdeal R) • (⊤ : Submodule R (Module.Dual R M)) := by
  let b := Module.Free.chooseBasis R M
  rw [← b.sum_dual_apply_smul_coord v]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
  have := LinearMap.congr_fun hv (b i)
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa [IsLocalRing.ResidueField.algebraMap_eq] using this

theorem tangentPt_inj {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {A : Type} [CommRing A]
    [Algebra R A] {v w : Cotangent G →ₗ[R] A}
    (h : (tangentPt v : specO R (DualNumber A) ⟶ G) = tangentPt w) : v = w := by
  have h1 : tangentAlg v = tangentAlg w := ptMap_locIncl_injective h
  refine GlobalTheory.AugCot.hom_ext (ε := aug G) fun a => ?_
  exact (tangentAlg_snd v a).symm.trans
    ((congrArg (fun φ => (φ a).snd) h1).trans (tangentAlg_snd w a))

theorem comp_cancel {T G : Over (Spec (CommRingCat.of R))} (u : T ⟶ G)
    (hu : IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (ResidueField R)).map u).left)
    {p q : specO R (DualNumber (ResidueField R)) ⟶ T} (h : p ≫ u = q ≫ u) : p = q := by
  let k := ResidueField R
  let f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let Y : Over (Spec (CommRingCat.of k)) := specO k (DualNumber k)
  let e : specO R (DualNumber k) ≅ (Over.map f).obj Y := Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom, Y, f, specO, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  let adj := Over.mapPullbackAdj f
  haveI : Mono ((Over.pullback f).map u) := by
    haveI : Mono ((Over.pullback f).map u).left := inferInstanceAs (Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map u).left)
    exact Over.mono_of_mono_left _
  have h1 : adj.homEquiv _ _ (e.inv ≫ p) = adj.homEquiv _ _ (e.inv ≫ q) := by
    apply (cancel_mono ((Over.pullback f).map u)).1
    rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right, Category.assoc,
      Category.assoc, h]
  have h2 := (adj.homEquiv _ _).injective h1
  exact (cancel_epi e.inv).1 h2

theorem lTensor_injective_of {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (l : M →ₗ[R] N)
    (h : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R N) →
      x ∈ (maximalIdeal R) • (⊤ : Submodule R M)) :
    Function.Injective (l.lTensor (R ⧸ maximalIdeal R)) := by
  let eM := TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal R)
  let eN := TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)
  have hle : (maximalIdeal R) • (⊤ : Submodule R M) ≤
      ((maximalIdeal R) • (⊤ : Submodule R N)).comap l :=
    Submodule.smul_le.2 fun r hr n _ => by
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr trivial
  let q := Submodule.mapQ _ _ l hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero q).2 fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 (h x hx)
  have hcomm : ∀ t, eN (l.lTensor (R ⧸ maximalIdeal R) t) = q (eM t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul a x =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.mapQ_apply, map_smul]
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  intro s t hst
  apply eM.injective
  apply hq
  rw [← hcomm, ← hcomm, hst]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G], Smooth G.hom → ∀ (r : ℕ) (u : torus R r ⟶ G) [IsMonHom u],
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left →
    ∃ ρ : LieG G → LieG (torus R r), IsLieLinear ρ ∧ ∀ x, ρ (lieMap u x) = x := by
  intro R _ _ G _ hG r u _ hu
  haveI := hG
  obtain ⟨_, _⟩ := finite_projective_of_smooth (G := G)
  obtain ⟨_, _⟩ := finite_projective_of_smooth (G := torus R r)
  haveI : Module.FinitePresentation R (Cotangent G) := Module.finitePresentation_of_projective _ _
  haveI : Module.Free R (Cotangent G) := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R (Cotangent (torus R r)) :=
    Module.finitePresentation_of_projective _ _
  haveI : Module.Free R (Cotangent (torus R r)) := Module.free_of_flat_of_isLocalRing
  let l := lieLin u
  let φ := Algebra.ofId R (ResidueField R)
  have key : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie G)) →
      x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie (torus R r))) := by
    intro x hx
    have h1 := res_comp_of_mem hx
    have a1 : ∀ y, (lieEquiv (torus R r) y).1 ≫ u = (lieEquiv G (l y)).1 := fun y => by
      rw [lieEquiv_lieLin]; rfl
    have h2 : (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) x).1) ≫ u =
        (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) 0).1) ≫ u := by
      rw [Category.assoc, Category.assoc, a1, a1, map_zero, lieEquiv_val, lieEquiv_val,
        dualBC_tangentPt, dualBC_tangentPt]
      exact congrArg tangentPt (h1.trans (LinearMap.comp_zero _).symm)
    have h3 := comp_cancel u hu h2
    rw [lieEquiv_val, lieEquiv_val, dualBC_tangentPt, dualBC_tangentPt, LinearMap.comp_zero] at h3
    exact mem_of_res_comp (tangentPt_inj h3)
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).2
    (lTensor_injective_of l key)
  refine ⟨fun y => lieEquiv (torus R r) (l' ((lieEquiv G).symm y)), ⟨fun x y => ?_, fun a x => ?_⟩,
    fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := (lieEquiv G).surjective x
    obtain ⟨y, rfl⟩ := (lieEquiv G).surjective y
    dsimp only
    rw [← lieEquiv_add', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      map_add, lieEquiv_add']
  · obtain ⟨x, rfl⟩ := (lieEquiv G).surjective x
    dsimp only
    rw [← lieEquiv_smul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, map_smul, lieEquiv_smul']
  · obtain ⟨x, rfl⟩ := (lieEquiv (torus R r)).surjective x
    dsimp only
    rw [← lieEquiv_lieLin, Equiv.symm_apply_apply]
    exact congrArg _ (LinearMap.congr_fun hl' x)

end GlobalTheory.TorusLieRetraction
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_of_free_stalks : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (r : ℕ), (∀ x : X, Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x :))) → IsVB F r := by
  first | exact @GlobalTheory.VB.isVB_of_basis_stalk | exact GlobalTheory.VB.isVB_of_basis_stalk | (intros; apply GlobalTheory.VB.isVB_of_basis_stalk <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM germ_resM)

namespace GlobalTheory.VB

variable {X : Scheme.{0}} [IsIntegral X] {F : X.Modules}

theorem IsTorsionFree.isTorsionFree_stalk (h : IsTorsionFree F) (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x :) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a t hat => ?_
  obtain ⟨V, hV, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem hV t
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hT) x hxT a] at hat ⊢
  generalize X.presheaf.map (homOfLE hT).op a = b at hat ⊢
  by_cases hb : b = 0
  · exact Or.inl (by rw [hb, map_zero])
  · right
    rw [← QCoh.germ_smul, ← map_zero (ConcreteCategory.hom (F.presheaf.germ T x hxT))] at hat
    obtain ⟨W, hxW, i₁, i₂, e⟩ := F.presheaf.germ_eq x hxT hxT _ _ hat
    rw [map_zero, Scheme.Modules.map_smul] at e
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hb' : X.presheaf.map i₁.op b ≠ 0 := fun h0 =>
      hb (map_injective_of_isIntegral X i₁ (h0.trans (map_zero _).symm))
    have := h.eq_zero_of_smul hb' e
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf i₁ x hxW t, this, map_zero]

theorem finrank_stalk_eq_genRank [F.IsQuasicoherent] (x : X) :
    Module.finrank (X.presheaf.stalk x) (F.presheaf.stalk x :) = genRank F := by
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem x
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact (key ⟨x, hx⟩).trans (key ⟨_, genericPoint_mem hx⟩).symm

theorem IsSmoothProjCurve.isPrincipalIdealRing_stalk {k : Type} [Field k] [Algebra k Γ(X, ⊤)]
    (hC : IsSmoothProjCurve k X) (x : X) : IsPrincipalIdealRing (X.presheaf.stalk x) := by
  have := hC.smooth
  have := hC.toIsProjCurve.isNoetherian
  have hn := (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strHom k X) (fun y => by
    have hf : IsField ((Sp k).presheaf.stalk y) := by
      have : Ring.KrullDimLE 0 ((Sp k).presheaf.stalk y) :=
        krullDimLE_of_coheight_le (by
          have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
          exact (Order.coheight_eq_zero.2 (fun b _ => (Subsingleton.elim b y).le)).le)
      have : IsIntegral (Sp k) := inferInstanceAs (IsIntegral (Spec (.of k)))
      exact Ring.KrullDimLE.isField_of_isDomain
    letI := hf.toField
    exact ⟨inferInstance, inferInstance⟩) x).2
  have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
    refine krullDimLE_of_coheight_le ?_
    have e : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have := Order.coheight_le_krullDim x
    rw [← e, hC.dim_eq] at this
    exact_mod_cast this
  have h3 : IsIntegrallyClosed (X.presheaf.stalk x) ∧ ∀ P : Ideal (X.presheaf.stalk x),
      P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _ :=
    ⟨hn, fun P h0 hP => IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 0 3).mpr h3

theorem isVB_of_isTorsionFree_and_isSubbundle_satι : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → (∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F)) ∧ ∀ (F G : C.Modules) (i : G ⟶ F) [GlobalTheory.QCoh.IsFiniteQC F], IsSubbundle (satι i) := by
  intro k _ C _ _ hC
  have := hC.toIsProjCurve.isNoetherian
  have H : ∀ (F : C.Modules) [GlobalTheory.QCoh.IsFiniteQC F], IsTorsionFree F → IsVB F (genRank F) := by
    intro F _ hF
    refine GlobalTheory.T.vector_bundle_of_free_stalks C F _ fun x => ?_
    have := hC.isPrincipalIdealRing_stalk x
    have := hF.isTorsionFree_stalk x
    exact ⟨Module.finBasisOfFinrankEq _ _ (finrank_stalk_eq_genRank x)⟩
  exact ⟨H, fun F G i _ => ⟨inferInstance, _, H _ (isSaturated_satι i)⟩⟩

end GlobalTheory.VB
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  atlas_forward_decl GlobalTheory.Nef.exists_frame_locFrames
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem centre_place : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
    ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  intro k K _ _ _ _ _ C _ x hx c hc
  obtain ⟨hC, hg, hstr⟩ := hx
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  haveI := hC.1
  haveI : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  haveI := hg.2
  set p : Sp K := IsLocalRing.closedPoint K with hp
  have hη : x p = genericPoint C := by
    have hd : Dense (Set.range x) := hg.1.denseRange
    have hr : Set.range x = {x p} := by
      ext y
      exact ⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩
    rw [hr] at hd
    exact (IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))
  have hco : Order.coheight c = 1 := by
    have hne : Order.coheight c ≠ 0 := by
      intro h0
      have hm : IsMax c := Order.coheight_eq_zero.1 h0
      have h3 : genericPoint C ⤳ c := genericPoint_specializes c
      apply hc
      rw [hη]
      exact ((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq
    have hle : (Order.coheight c : WithBot ℕ∞) ≤ 1 := by
      haveI : Nonempty C := ⟨c⟩
      have hd := GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1
      have h1 := (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
      rw [topologicalKrullDim] at hd
      rw [hd] at h1
      exact h1
    have hle' : Order.coheight c ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)
  haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco

  set A := C.presheaf.stalk c
  let P : IsDedekindDomain.HeightOneSpectrum A := IsDiscreteValuationRing.maximalIdeal A
  let ic := C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  let ψ : C.functionField →+* K := (ic.hom ≫ Scheme.stalkClosedPointTo x).hom
  have hψ : Function.Bijective ψ := by
    refine ⟨RingHom.injective ψ, ?_⟩
    have h1 : Function.Surjective ic.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2
    have h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
      have h3 := x.stalkMap_surjective p
      have h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom :=
        ((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2
      exact h4.comp h3
    exact h2.comp h1
  let e : C.functionField ≃+* K := RingEquiv.ofBijective ψ hψ
  let φ : A →+* K := ψ.comp (algebraMap A C.functionField)
  have hφ : spMap φ ≫ C.fromSpecStalk c = x := by
    have h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom := by
      show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _
      change (C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _
      rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
      erw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [h1]
    change Spec.map (CommRingCat.ofHom _) ≫ _ = x
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a := by
    intro a
    have : e.symm (φ a) = algebraMap A C.functionField a := e.symm_apply_apply _
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a

  have hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t)) := by
    have h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤))) := by
      rw [← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    have h2 := Spec.map_injective (hstr.symm.trans h1)
    intro t
    exact congrArg (fun f => f.hom t) h2
  let vK : Valuation K (WithZero (Multiplicative ℤ)) := (P.valuation C.functionField).comap e.symm.toRingHom
  have hvφ : ∀ a, vK (φ a) = P.intValuation a := fun a => hval a
  have hunit : ∀ a : A, IsUnit a → P.intValuation a = 1 := by
    intro a ha
    refine le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)
  let v : Place k K := ⟨vK, fun g => by
      obtain ⟨y, hy⟩ := P.valuation_surjective C.functionField g
      exact ⟨e y, by
        change P.valuation C.functionField (e.symm (e y)) = g
        rw [e.symm_apply_apply]; exact hy⟩,
    fun t ht => by
      rw [hk, hvφ]
      exact hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩
  have hle : ∀ a : A, φ a ∈ v.O := fun a => by
    show vK (φ a) ≤ 1
    rw [hvφ]; exact P.intValuation_le_one a
  let ψO : A →+* v.O := φ.codRestrict v.O hle
  have hPm : P.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI : IsLocalHom ψO := ⟨fun a ha => by
    by_contra hna
    have hm : a ∈ P.asIdeal := by rw [hPm]; exact hna
    have hlt : vK (φ a) < 1 := by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm
    obtain ⟨u, hu⟩ := ha
    let w : v.O := ((u⁻¹ : v.Oˣ) : v.O)
    have hinv : vK (w : K) ≤ 1 := w.2
    have h1 : φ a * (w : K) = 1 := by
      have := congrArg (fun z : v.O => (z : K)) u.mul_inv
      have e1 : φ a = ((u : v.O) : K) := by rw [hu]; rfl
      rw [e1]
      exact this
    have h2 := congrArg vK h1
    rw [map_mul, map_one] at h2
    have : vK (φ a) * vK (w : K) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt
    exact absurd h2 this.ne⟩
  refine ⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← hφ]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · have : spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint ψO
    change C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c
    rw [this, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.Nef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_closedPoint_isCentreOfPlace : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  atlas_forward_decl GlobalTheory.Nef.centre_place
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_sec_lbPow_vanishing_of_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB →
      0 < interNum k (GlobalTheory.structureModule C) ![L] →
      ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  intro k _ C _ hC L hL hpos
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hC.1
  obtain ⟨hprop, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k C)).1 hC.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  set O := GlobalTheory.structureModule C with hO
  set d := interNum k O ![L] with hdd
  set f := chiPic k O with hf

  have hdeg : ∀ (M : LB C) (hM : M.IsLB), interNum k O ![M] = f 0 - f (-cls M hM) := by
    intro M hM
    rw [interNum_one k O hM, chi_twistZ k O hM, hf, chiPic_zero, neg_one_zsmul]

  have hchi : ∀ m : ℕ, f ((m : ℤ) • cls L hL) = f 0 + m * d := by
    intro m
    obtain ⟨N, hN, hc⟩ := cls_surj (-((m : ℤ) • cls L hL))
    have hLm := isLB_lbPow hL m
    have e : cls _ (LB.isLB_triv C) = cls N hN + cls _ hLm := by
      rw [hc, cls_lbPow hL m hLm, cls_triv, natCast_zsmul, neg_add_cancel]
    have hadd := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hN hLm e
    rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m, hdeg _ (LB.isLB_triv C), hdeg N hN, hc,
      cls_triv, neg_zero, neg_neg] at hadd
    have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
    linarith
  set m : ℕ := (f 0).natAbs + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hLm := isLB_lbPow hL m
  have hqc := Twist.isQuasicoherent_twist (F := O) hLm
  have hvan : ∀ n, 2 ≤ n → Subsingleton (coh (twist O (lbPow L m)) n) := by
    intro n hn
    refine hH.subsingleton_coh_of_dim_lt _ ?_
    rw [hd]
    exact_mod_cast (show (1 : ℕ) < n by omega)
  have hχ : chi k (twist O (lbPow L m)) = f 0 + m * d := by
    rw [← chiPic_cls k O hLm, cls_lbPow hL m hLm, ← natCast_zsmul, ← hf, hchi m]
  have hχpos : 0 < chi k (twist O (lbPow L m)) := by
    rw [hχ]
    have h1 : (1 : ℤ) ≤ d := hpos
    have h2 : -(f 0) ≤ ((f 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs (f 0)
    have h3 : (m : ℤ) = (f 0).natAbs + 1 := by rw [hm]; push_cast; ring
    nlinarith
  have hh0 : 0 < hdim k (twist O (lbPow L m)) 0 := by
    have := chi_eq_hdim_zero_sub_hdim_one k hvan
    omega
  have hnt : Nontrivial (coh (twist O (lbPow L m)) 0) := Module.nontrivial_of_finrank_pos hh0
  obtain ⟨σ, hσ⟩ := hasNonzeroSec_iff_nontrivial.2 hnt
  refine ⟨m, σ, ?_⟩
  by_contra! hall
  have htop : Out.nonzeroLocus σ = ⊤ := top_unique fun c _ ↦ (hall c hm0 hσ)
  have h0 : cls _ hLm = 0 := (cls_eq_zero_iff hLm).2 (exists_isGen_of_nonzeroLocus_eq_top σ htop)
  have hz := interNum_eq_zero_of_cls_eq_zero k O (isLB_vecOne hLm) 0 h0
  rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m] at hz
  have : (0 : ℤ) < m * d := mul_pos (by exact_mod_cast hm0) hpos
  have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
  rw [hd'] at hz
  omega

end GlobalTheory.Nef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB → 0 < interNum k (GlobalTheory.structureModule C) ![L] → ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  atlas_forward_decl GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.SecRat

theorem isIntegral_of_isGenOver (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C) (hx : IsGenOver k x) : IsIntegral C := by
  have : SmoothOfRelativeDimension 1 (strHom k C) := hx.1.1
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have hred : IsReduced C := isReduced_of_smooth_of_isReduced (strHom k C)
  have hd : IsDominant x := hx.2.1.1
  have hden : DenseRange x.base := hd.denseRange
  have hcl : closure {x.base default} = (Set.univ : Set C) := by
    have hr : Set.range x.base = {x.base default} := by
      ext y; constructor
      · rintro ⟨p, rfl⟩; rw [Subsingleton.elim p default]; rfl
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]; exact hden.closure_range
  have hirr : IsIrreducible (Set.univ : Set C) := hcl ▸ isIrreducible_singleton.closure
  have : IrreducibleSpace C := { isPreirreducible_univ := hirr.2, toNonempty := ⟨x.base default⟩ }
  exact (isIntegral_iff_irreducibleSpace_and_isReduced C).2 ⟨this, hred⟩

theorem not_isUnit_evAt {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X)
    {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) (hf : b (IsLocalRing.closedPoint R) ∉ X.basicOpen f) :
    ¬ IsUnit (evAt b h f) := by
  intro hu
  apply hf
  have h1 : (b.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (.of R)).inv.hom (evAt b h f) := by
    simp [evAt]
  have h2 : (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) = ⊤ ⊓ (Sp R).basicOpen ((b.app U).hom f) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
  have h3 : IsLocalRing.closedPoint R ∈ (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) := by
    rw [h1, basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hu
  rw [h2, ← Scheme.preimage_basicOpen] at h3
  exact h3.2

theorem evAt_coord {R : Type} [CommRing R] {C : Scheme.{0}} (x : Sp R ⟶ C) {W : C.Modules} {r m : ℕ}
    (σ : (lbPow (det W r) m).Sec) (c₀ c : Chart W r) (V' : C.Opens) (h₀ : V' ≤ c₀.U) (h₁ : V' ≤ c.U)
    (hx' : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V'))
    (hM : ∀ j, resM W h₀ (c₀.e j) = ∑ i, M i j • resM W h₁ (c.e i))
    (h0 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c₀)) (h1 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c)) :
    evAt x h1 (σ.f (fun _ => c)) = (M.map (evAt x hx')).det ^ m * evAt x h0 (σ.f (fun _ => c₀)) := by
  have hV : V' ≤ (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => h₁ hy, Set.mem_iInter.2 fun _ => h₀ hy⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ ((lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀)) :=
    hx'.trans (x.preimage_mono hV)
  have hcc : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c₀.U) := hx'.trans (x.preimage_mono (le_inf h₁ h₀))
  have e := congrArg (evAt x hxV) (σ.compat (fun _ => c) (fun _ => c₀))
  rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h1 hxV, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h0 hxV] at e
  rw [e]
  congr 1
  have hd : evAt x hcc (c.isFrame.detUnit c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right).val =
      (M.map (evAt x hx')).det := by
    rw [← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (le_inf h₁ h₀) hcc hx']
    have hr := IsFrame.res_detUnit c.isFrame c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right (le_inf h₁ h₀)
    refine (congrArg (evAt x hx') (congrArg Units.val hr)).trans ?_
    rw [IsFrame.val_detUnit, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, hM]
    simp only [← IsFrame.basis_apply c.isFrame h₁]
    rw [Module.Basis.repr_sum_self]
  rw [← hd, ← map_pow, ← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) ≤ c.U ⊓ c₀.U) hcc hxV]
  congr 1
  dsimp only [lbPow, LB.LinComb]
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  erw [map_pow]
  congr 1

theorem val_lt_one {k K : Type} [Field k] [Field K] [Algebra k K] (v : Place k K) (a : v.O) (ha : ¬ IsUnit a) :
    v.1 (a : K) < 1 := by
  have h1 : v.1 (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2
  refine lt_of_le_of_ne h1 fun h => ha ?_
  have h0 : (a : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hi : (a : K)⁻¹ ∈ v.O := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem sec_eq_zero {X : Scheme.{0}} {L : LB X} (σ : L.Sec) (h : ∀ j, σ.f j = 0) : σ = 0 := by
  obtain ⟨f, hc⟩ := σ
  have : f = fun _ => 0 := funext h
  subst this
  rfl

end GlobalTheory.Nef.SecRat

open GlobalTheory.Nef.SecRat in

theorem GlobalTheory.Nef.sec_detPow_rational : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s hV₀ hs m σ hσ
  haveI := isIntegral_of_isGenOver k K C x hx
  let c₀ : Chart W r := ⟨V₀, s, hs⟩
  have hUeq : ∀ c : Chart W r, (((lbPow (det W r) m).U (fun _ => c) : C.Opens) : Set C) = c.U := fun c =>
    Set.ext fun y => ⟨fun hy => Set.mem_iInter.1 hy PUnit.unit, fun hy => Set.mem_iInter.2 fun _ => hy⟩
  have hle : ∀ c : Chart W r, c.U ≤ (lbPow (det W r) m).U (fun _ => c) := fun c y hy =>
    Set.mem_iInter.2 fun _ => hy
  obtain ⟨hx0, hinj0, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 ((lbPow (det W r) m).U fun _ => c₀)
    (by rw [hUeq]; exact hV₀)
  refine ⟨evAt x hx0 (σ.f fun _ => c₀), ?_, ?_⟩
  · intro hf
    apply hσ
    have h0 : σ.f (fun _ => c₀) = 0 := hinj0 (by rw [hf, map_zero])
    refine sec_eq_zero σ fun j => ?_
    have hj : j = fun _ => j PUnit.unit := funext fun _ => rfl
    rw [hj]
    generalize j PUnit.unit = c
    by_cases hne : (((lbPow (det W r) m).U fun _ => c : C.Opens) : Set C).Nonempty
    · have hne2 : ((((lbPow (det W r) m).U fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :
          C.Opens) : Set C).Nonempty :=
        nonempty_preirreducible_inter (Opens.isOpen _) (Opens.isOpen _) hne (by rw [hUeq]; exact hV₀)
      obtain ⟨hxj, hinjj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne
      obtain ⟨hx2, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne2
      apply hinjj
      have e := congrArg (evAt x hx2) (σ.compat (fun _ => c) (fun _ => c₀))
      rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hxj hx2, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hx0 hx2, h0,
        map_zero, mul_zero] at e
      rw [e, map_zero]
    · exact eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => hne ⟨y, C.basicOpen_le _ hy⟩)
  · rintro v g ⟨b, V, t, V', h₀, h₁, hx', M, hb, hbV, ht, hM, rfl⟩
    let c : Chart W r := ⟨V, t, ht⟩
    have hbj : ⊤ ≤ b ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hbV.trans (b.preimage_mono (hle c))
    have hxj : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hx'.trans (x.preimage_mono (h₁.trans (hle c)))
    have key := evAt_coord x σ c₀ c V' h₀ h₁ hx' M hM hx0 hxj
    have hval : v.1 (evAt x hx0 (σ.f fun _ => c₀) * (M.map (evAt x hx')).det ^ m) =
        v.1 ((evAt b hbj (σ.f fun _ => c) : v.O) : K) := by
      rw [mul_comm, ← key]
      congr 1
      subst hb
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 v.O K C v.O.subtype b _ hbj hxj _
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact (Valuation.mem_valuationSubring_iff _ _).1 (evAt b hbj _).2
    · intro b' hb' hout
      have e : spMap (algebraMap K K) ≫ x = x := by
        rw [Algebra.algebraMap_self, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      obtain ⟨b₀, -, huniq⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
      have hbb : b' = b := (huniq b' (hb'.trans e.symm)).trans (huniq b (hb.trans e.symm)).symm
      subst hbb
      have hnu := not_isUnit_evAt b' hbj (σ.f fun _ => c) (fun hm => hout (Opens.mem_iSup.2 ⟨_, hm⟩))
      rw [hval]
      exact val_lt_one v _ hnu
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detPowSection_rational_genericPoint : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  atlas_forward_decl GlobalTheory.Nef.sec_detPow_rational
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem closedPoint_mem_nonzeroLocus {K : Type} [Field K] {C : Scheme.{0}} [IsIntegral C] (x : Sp K ⟶ C)
    [IsDominant x] {L : LB C} {σ : L.Sec} (hσ : σ ≠ 0) : x (IsLocalRing.closedPoint K) ∈ Out.nonzeroLocus σ := by
  have h : ∃ i, σ.f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    obtain ⟨f, hf⟩ := σ
    obtain rfl : f = fun _ => 0 := funext h
    rfl
  obtain ⟨i, hi⟩ := h
  have hne : ((C.basicOpen (σ.f i) : C.Opens) : Set C).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hi ((basicOpen_eq_bot_iff _).1 (Opens.ext e))
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open (C.basicOpen (σ.f i)).isOpen hne
  obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact Opens.mem_iSup.2 ⟨i, hy⟩

theorem deg_pos_of_integral {k K : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {r : ℕ}
    {g : Place k K → Matrix (Fin r) (Fin r) K} (hg : admitted g) {f : K} (hf : f ≠ 0)
    (hfin : {v : Place k K | v.1 f ≠ 1}.Finite) (hsum : ∑ᶠ v : Place k K, ord v f = 0) {m : ℕ}
    (hle : ∀ v : Place k K, v.1 (f * (g v).det ^ m) ≤ 1) {w : Place k K} (hlt : w.1 (f * (g w).det ^ m) < 1) :
    0 < deg g := by
  have hne : ∀ v, f * (g v).det ^ m ≠ 0 := fun v => mul_ne_zero hf (pow_ne_zero _ (hg.1 v))
  have hadd : ∀ v : Place k K, ord v (f * (g v).det ^ m) = ord v f + m * ord v (g v).det := fun v => by
    rw [(ord_calculus k K v).1 _ _ hf (pow_ne_zero _ (hg.1 v)), ← (ord_calculus k K v).2.1 _ (hg.1 v), zpow_natCast]
  have f₁ : (Function.support fun v : Place k K => ord v f).Finite :=
    hfin.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ hf).1 e)
  have f₂ : (Function.support fun v : Place k K => ord v (g v).det).Finite :=
    hg.2.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ (hg.1 v)).1 e.2)
  have f₃ : (Function.support fun v : Place k K => (m : ℤ) * ord v (g v).det).Finite :=
    f₂.subset fun v hv e => hv (by simp only [e, mul_zero])
  have hs : ∑ᶠ v : Place k K, ord v (f * (g v).det ^ m) = m * deg g := by
    simp only [hadd]
    rw [finsum_add_distrib f₁ f₃, hsum, zero_add, deg, mul_finsum' _ _ f₂]
  have h0 : ∀ v : Place k K, 0 ≤ ord v (f * (g v).det ^ m) := fun v =>
    ((ord_calculus k K v).2.2.1 _ (hne v)).1 (hle v)
  have hw : 0 < ord w (f * (g w).det ^ m) :=
    (h0 w).lt_of_ne fun e => hlt.ne (((ord_calculus k K w).2.2.2.1 _ (hne w)).2 e.symm)
  have f₄ : (Function.support fun v : Place k K => ord v (f * (g v).det ^ m)).Finite := by
    refine (f₁.union f₃).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hv (by simp only [hadd, h.1, h.2, add_zero])
  have hpos : 0 < (m : ℤ) * deg g := by
    rw [← hs]
    exact hw.trans_le (single_le_finsum w f₄ h0)
  by_contra h
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) (not_lt.1 h)))

theorem interNum_det_nonpos_of_deg_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s g hV hs hg hloc hdeg
  by_contra hpos
  have := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  have := hx.2.1.1
  obtain ⟨m, σ, c, -, hσ, hc⟩ := GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos k C hx.1 (det W r) hW.isLB_det (not_le.1 hpos)
  obtain ⟨w, b, hb, hbc⟩ := GlobalTheory.T.curve_closedPoint_isCentreOfPlace k K C x hx c fun e => hc (e ▸ closedPoint_mem_nonzeroLocus x hσ)
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.detPowSection_rational_genericPoint k K C x hx W r hW V₀ s hV hs m σ hσ
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) f hf
  exact (deg_pos_of_integral hg hf hfin hsum (fun v => (H v _ (hloc v)).1)
    ((H w _ (hloc w)).2 b hb (hbc ▸ hc))).not_ge hdeg

end GlobalTheory.Nef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detDegree_nonpos_of_adelicDegree_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  atlas_forward_decl GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem exists_isGenOver (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (h : IsCurve k C) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (x : Sp K ⟶ C), IsGenOver k x := by
  have := LieSemineg.isIntegral_curve h.1 h.2.2
  let x : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)
  let φ : CommRingCat.of k ⟶ CommRingCat.of C.functionField := Spec.preimage (x ≫ strHom k C)
  refine ⟨C.functionField, inferInstance, φ.hom.toAlgebra, x, h, isGen_fromSpecStalk C, ?_⟩
  exact (Spec.map_preimage (x ≫ strHom k C)).symm

theorem semiNeg_lie_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  intro k _ _ _ C _ h G _ hG W r hW i hi
  obtain ⟨K, _, _, x, hx⟩ := exists_isGenOver k C h
  obtain ⟨V₀, s, g, hV, hs, hg, hl⟩ := GlobalTheory.T.exists_genericFrame_and_localFrames_allPlaces k K C x hx W r hW
  have hL := GlobalTheory.T.lie_subsheaf_lines_degree_nonpos k K C x hx G hG W r i hi V₀ s g hV hs hg hl
  have hd := GlobalTheory.T.adelicMatrixFamilyDegree_le_rank_mul_line_bound r k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) g hg 0 hL
  rw [mul_zero] at hd
  exact GlobalTheory.T.detDegree_nonpos_of_adelicDegree_nonpos k K C x hx W r hW V₀ s g hV hs hg hl (by exact_mod_cast hd)

end GlobalTheory.Nef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  atlas_forward_decl GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem semiAbelianLieSeminegative : GlobalTheory.Published.SemiAbelianLieSeminegative := by
  intro k _ _ C _ hs hp hc G _ hG W r hW i hi
  obtain ⟨C', _, π, hC', hdesc⟩ := GlobalTheory.T.semiNegative_descends_fieldExtension_curve k C ⟨hs, hp, hc⟩ (AlgebraicClosure k)
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  refine hdesc (Lie G) ?_ W r hW i hi
  exact GlobalTheory.NeronCurve.LieDescent.semiNeg_of_iso (GlobalTheory.NeronCurve.LieDescent.lieBaseIso π G).symm
    (GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed (AlgebraicClosure k) C' hC' _ (IsSemiAbelian.pullback π G hG))

end GlobalTheory.Nef
end
end
