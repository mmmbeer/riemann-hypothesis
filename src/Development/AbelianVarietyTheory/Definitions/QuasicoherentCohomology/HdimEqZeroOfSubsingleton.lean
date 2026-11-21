import Mathlib

section
open CategoryTheory Opposite Limits Abelian

universe w v u

noncomputable section

namespace GlobalTheory.SiteCoh

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

abbrev freeSheaf : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf _ _

def tautSection (U : C) : ((freeSheaf J).obj U).obj.obj (op U) :=
  (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U))

variable {J}

def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeSheaf J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj).trans yonedaEquiv)
  map_add' _ _ := rfl

lemma freeSheafHomEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) (f : F ⟶ G) :
    freeSheafHomEquiv U G (φ ≫ f) = f.hom.app (op U) (freeSheafHomEquiv U F φ) := rfl



def freePresheafIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents
    (fun V ↦
      letI : Unique (V.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ ↦ hT.hom_ext _ _⟩
      ((FreeAbelianGroup.uniqueEquiv (V.unop ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {V W} f ↦ by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro x
      rfl)

def freeSheafIsoConst {T : C} (hT : IsTerminal T) :
    (freeSheaf J).obj T ≅ (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf J _).mapIso (freePresheafIsoConst hT)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

def extEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    F.H' n U ≃+ Ext.{w} ((freeSheaf J).obj U) F n :=
  AddEquiv.refl _

abbrev map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C) :
    F.H' n U ⟶ G.H' n U :=
  ((Sheaf.cohomologyPresheafFunctor J n).map f).app (op U)

abbrev res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U) :
    F.H' n U ⟶ F.H' n V :=
  (F.cohomologyPresheaf n).map i.op

lemma extEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C)
    (x : F.H' n U) :
    extEquiv G n U (map f n U x) = (extEquiv F n U x).comp (Ext.mk₀ f) (add_zero n) := rfl


instance cohomologyPresheafFunctor_additive (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor.{w} J n).Additive where
  map_add {F G f g} := by
    ext U x
    apply (extEquiv G n U.unop).injective
    change (extEquiv F n U.unop x).comp (Ext.mk₀ (f + g)) (add_zero n) =
      (extEquiv F n U.unop x).comp (Ext.mk₀ f) (add_zero n) +
        (extEquiv F n U.unop x).comp (Ext.mk₀ g) (add_zero n)
    rw [Ext.mk₀_add, Ext.comp_add]

def zeroEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) : F.H' 0 U ≃+ F.obj.obj (op U) :=
  (extEquiv F 0 U).trans (Ext.addEquiv₀.trans (freeSheafHomEquiv U F))

lemma zeroEquiv_mk₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) (φ : (freeSheaf J).obj U ⟶ F) :
    zeroEquiv F U ((extEquiv F 0 U).symm (Ext.mk₀ φ)) = freeSheafHomEquiv U F φ := by
  simp only [zeroEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  congr 1
  exact Ext.addEquiv₀.apply_symm_apply φ

lemma zeroEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    zeroEquiv G U (map f 0 U x) = f.hom.app (op U) (zeroEquiv F U x) := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 U).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, ← freeSheafHomEquiv_comp, ← zeroEquiv_mk₀]
  congr 1
  apply (extEquiv G 0 U).injective
  rw [extEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]


def terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T) :
    F.H' n T ≃+ F.H n :=
  (extEquiv F n T).trans
    (((extFunctor n).mapIso (freeSheafIsoConst (J := J) hT).symm.op).app F).addCommGroupIsoToAddEquiv

lemma terminalEquiv_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T)
    (x : F.H' n T) :
    terminalEquiv F n hT x =
      (Ext.mk₀ (freeSheafIsoConst hT).inv).comp (extEquiv F n T x) (zero_add n) := rfl

lemma terminalEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) {T : C}
    (hT : IsTerminal T) (x : F.H' n T) :
    terminalEquiv G n hT (map f n T x) = Sheaf.H.map f n (terminalEquiv F n hT x) := by
  rw [terminalEquiv_apply, terminalEquiv_apply, extEquiv_map, Sheaf.H.map_apply]
  symm
  apply Ext.comp_assoc
  all_goals omega

lemma equiv₀_terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T)
    (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (terminalEquiv F 0 hT x) = zeroEquiv F T x := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 T).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, terminalEquiv_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]
  obtain ⟨ψ, rfl⟩ : ∃ ψ, (freeSheafIsoConst hT).hom ≫ ψ = φ :=
    ⟨(freeSheafIsoConst hT).inv ≫ φ, by simp⟩
  rw [Iso.inv_hom_id_assoc, freeSheafHomEquiv_comp]
  have h : (Ext.addEquiv₀ (Ext.mk₀.{w} ψ)) = ψ := Ext.addEquiv₀.apply_symm_apply ψ
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h]
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (freePresheafIsoConst hT).hom) (op T))
    (FreeAbelianGroup.of (𝟙 T))
  exact congrArg (ψ.hom.app (op T)) h₁

instance subsingleton_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ) (U : C) :
    Subsingleton (F.H' (n + 1) U) :=
  subsingleton_of_forall_eq 0 fun _ ↦
    (extEquiv F (n + 1) U).injective ((Ext.eq_zero_of_injective _).trans (map_zero _).symm)

lemma subsingleton_of_subsingleton_freeSheaf (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    [Subsingleton (((freeSheaf J).obj U).obj.obj (op U))] : Subsingleton (F.H' n U) := by
  have h : 𝟙 ((freeSheaf J).obj U) = 0 :=
    (freeSheafHomEquiv U _).injective (Subsingleton.elim _ _)
  refine subsingleton_of_forall_eq 0 fun x ↦ (extEquiv F n U).injective ?_
  rw [← Ext.mk₀_id_comp (extEquiv F n U x), h, Ext.mk₀_zero, Ext.zero_comp, map_zero]

end GlobalTheory.SiteCoh
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

universe w v u

noncomputable section

namespace GlobalTheory

variable {X : Scheme.{u}}

variable (X) in

def toAbSheaf : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance toAbSheaf_additive : (toAbSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance toAbSheaf_faithful : (toAbSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

instance toAbSheaf_reflectsIsomorphisms : (toAbSheaf X).ReflectsIsomorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms

instance toAbSheaf_preservesFiniteLimits : PreservesFiniteLimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

@[simp] lemma toAbSheaf_obj_obj (F : X.Modules) : ((toAbSheaf X).obj F).obj = F.presheaf := rfl

@[simp] lemma toAbSheaf_map_hom_app {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) :
    ((toAbSheaf X).map φ).hom.app (op U) = φ.app U := rfl

abbrev restrictGlobal (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

lemma restrictGlobal_top (r : Γ(X, ⊤)) : restrictGlobal X ⊤ r = r := by
  have : (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := rfl
  rw [restrictGlobal, this, op_id, X.presheaf.map_id]
  rfl

lemma map_restrictGlobal {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictGlobal X U r) = restrictGlobal X V r := by
  rw [restrictGlobal, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def smulHom (F : X.Modules) (r : Γ(X, ⊤)) : F ⟶ F :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U ↦ F.smul (restrictGlobal X U.unop r)
      naturality := fun U V i ↦ by
        have := F.map_comp_smul i.unop (restrictGlobal X U.unop r)
        rw [map_restrictGlobal] at this
        exact this.symm }
    (fun U a m ↦ smul_comm (restrictGlobal X U.unop r) (show Γ(X, U.unop) from a) (show Γ(F, U.unop) from m))

@[simp] lemma smulHom_app_apply (F : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    (smulHom F r).app U x = restrictGlobal X U r • x := rfl

@[simp] lemma smulHom_one (F : X.Modules) : smulHom F 1 = 𝟙 F := by
  ext U x; rw [smulHom_app_apply, map_one, one_smul]; rfl

@[simp] lemma smulHom_zero (F : X.Modules) : smulHom F 0 = 0 := by
  ext U x; rw [smulHom_app_apply, map_zero, zero_smul]; rfl

lemma smulHom_add (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F (r + s) = smulHom F r + smulHom F s := by
  ext U x; rw [smulHom_app_apply, map_add, add_smul]; rfl

lemma smulHom_mul (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F (r * s) = smulHom F s ≫ smulHom F r := by
  ext U x; rw [smulHom_app_apply, map_mul, mul_smul]; rfl

@[reassoc] lemma smulHom_comp {F G : X.Modules} (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    smulHom F r ≫ φ = φ ≫ smulHom G r := by
  ext U x
  exact φ.app_smul (restrictGlobal X U r) x

@[simps] def smulEnd (F : X.Modules) : Γ(X, ⊤) →+* End F where
  toFun := smulHom F
  map_one' := smulHom_one F
  map_mul' := smulHom_mul F
  map_zero' := smulHom_zero F
  map_add' := smulHom_add F

instance linearModules : Linear Γ(X, ⊤) X.Modules where
  homModule F G :=
    { smul r φ := φ ≫ smulHom G r
      one_smul φ := by change φ ≫ _ = _; rw [smulHom_one, Category.comp_id]
      mul_smul r s φ := by change φ ≫ _ = (φ ≫ _) ≫ _; rw [smulHom_mul, Category.assoc]
      smul_zero r := zero_comp
      smul_add r φ ψ := Preadditive.add_comp _ _ _ _ _ _
      add_smul r s φ := by
        change φ ≫ _ = φ ≫ _ + φ ≫ _; rw [smulHom_add, Preadditive.comp_add]
      zero_smul φ := by change φ ≫ _ = _; rw [smulHom_zero, comp_zero] }
  smul_comp F G H r φ ψ := by
    change (φ ≫ _) ≫ ψ = (φ ≫ ψ) ≫ _
    rw [Category.assoc, Category.assoc, smulHom_comp]
  comp_smul F G H φ r ψ := (Category.assoc _ _ _).symm

lemma smul_hom_def {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) : r • φ = φ ≫ smulHom G r := rfl

lemma smulHom_eq_smul_id (F : X.Modules) (r : Γ(X, ⊤)) : smulHom F r = r • 𝟙 F :=
  (Category.id_comp _).symm

@[simp] lemma smul_app_apply {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) (U : X.Opens)
    (x : Γ(F, U)) : (r • φ).app U x = restrictGlobal X U r • φ.app U x := rfl

@[reducible] def addCommGroupOfAction {A M : Type*} [CommRing A] (inst : AddCommGroup M)
    (ρ : A →+* AddMonoid.End M) : AddCommGroup M :=
  { inst with
    zsmul := fun n x ↦ ρ (algebraMap ℤ A n) x
    zsmul_zero' := fun x ↦ by
      change ρ (algebraMap ℤ A 0) x = 0
      rw [map_zero, map_zero]; rfl
    zsmul_succ' := fun n x ↦ by
      change ρ (algebraMap ℤ A (n + 1 : ℕ)) x = ρ (algebraMap ℤ A n) x + x
      rw [Nat.cast_succ, map_add, map_add, map_one, map_one]; rfl
    zsmul_neg' := fun n x ↦ by
      change ρ (algebraMap ℤ A (Int.negSucc n)) x = -ρ (algebraMap ℤ A (n + 1 : ℕ)) x
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) from rfl, map_neg, map_neg]; rfl }

def WithAction {A M : Type*} [CommRing A] [AddCommGroup M] (_ρ : A →+* AddMonoid.End M) := M

namespace WithAction

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  (ρ : A →+* AddMonoid.End M) (σ : A →+* AddMonoid.End N)

instance instAddCommGroup : AddCommGroup (WithAction ρ) := addCommGroupOfAction (M := M) ‹_› ρ

def toBase : WithAction ρ ≃+ M where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl

variable (R : Type*) [CommRing R] [Algebra R A]

instance instModule : Module R (WithAction ρ) where
  smul r x := ρ (algebraMap R A r) x
  one_smul x := by
    change ρ (algebraMap R A 1) x = x
    rw [map_one, map_one]; rfl
  mul_smul r s x := by
    change ρ (algebraMap R A (r * s)) x = _
    rw [map_mul, map_mul]; rfl
  smul_zero r := map_zero (ρ (algebraMap R A r))
  smul_add r := map_add (ρ (algebraMap R A r))
  add_smul r s x := by
    change ρ (algebraMap R A (r + s)) x = _
    rw [map_add, map_add]; rfl
  zero_smul x := by
    change ρ (algebraMap R A 0) x = _
    rw [map_zero, map_zero]; rfl

example : instModule ρ ℤ = AddCommGroup.toIntModule (WithAction ρ) := by
  with_reducible_and_instances rfl

variable {R} in

lemma toBase_smul (r : R) (x : WithAction ρ) :
    toBase ρ (r • x) = ρ (algebraMap R A r) (toBase ρ x) := rfl

instance instIsScalarTower (S : Type*) [CommRing S] [Algebra S A] [Algebra R S]
    [IsScalarTower R S A] : IsScalarTower R S (WithAction ρ) :=
  .of_algebraMap_smul fun r x ↦ by
    apply (toBase ρ).injective
    rw [toBase_smul, toBase_smul, ← IsScalarTower.algebraMap_apply]

instance instSMulCommClass (S : Type*) [CommRing S] [Algebra S A] :
    SMulCommClass R S (WithAction ρ) where
  smul_comm r s x := by
    rw [← algebraMap_smul A r, ← algebraMap_smul A s, ← algebraMap_smul A r,
      ← algebraMap_smul A s (_ • x), smul_smul, smul_smul, mul_comm]

def linearMap (f : M →+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) :
    WithAction ρ →ₗ[R] WithAction σ where
  toFun := f
  map_add' := f.map_add
  map_smul' _ x := h _ x

lemma toBase_linearMap (f : M →+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) (x : WithAction ρ) :
    toBase σ (linearMap ρ σ R f h x) = f (toBase ρ x) := rfl

def linearEquiv (f : M ≃+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) :
    WithAction ρ ≃ₗ[R] WithAction σ where
  toFun := f
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_add' := f.map_add
  map_smul' _ x := h _ x


end WithAction

@[simps] def functorEndRingHom {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] (Y : C) : End Y →+* End (G.obj Y) where
  toFun f := G.map f
  map_one' := G.map_id Y
  map_mul' f g := G.map_comp g f
  map_zero' := G.map_zero Y Y
  map_add' _ _ := G.map_add

namespace SiteCoh

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {F G H : Sheaf J AddCommGrpCat.{v}} {n : ℕ} {U V W : C}

lemma map_id_apply (x : F.H' n U) : map (𝟙 F) n U x = x := by
  simp only [map, CategoryTheory.Functor.map_id]; rfl

lemma map_comp_apply (f : F ⟶ G) (g : G ⟶ H) (x : F.H' n U) :
    map (f ≫ g) n U x = map g n U (map f n U x) := by
  simp only [map, Functor.map_comp]; rfl

lemma map_add_apply (f g : F ⟶ G) (x : F.H' n U) :
    map (f + g) n U x = map f n U x + map g n U x := by
  simp only [map, Functor.map_add]; rfl

lemma map_zero_apply (x : F.H' n U) : map (0 : F ⟶ G) n U x = 0 := by
  simp only [map, Functor.map_zero]; rfl

lemma res_id_apply (x : F.H' n U) : res F n (𝟙 U) x = x := by
  simp only [res, op_id, CategoryTheory.Functor.map_id]; rfl

lemma res_comp_apply (i : V ⟶ U) (j : W ⟶ V) (x : F.H' n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by
  simp only [res, op_comp, Functor.map_comp]; rfl

lemma res_map_apply (f : F ⟶ G) (i : V ⟶ U) (x : F.H' n U) :
    res G n i (map f n U x) = map f n V (res F n i x) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor J n).map f).naturality i.op) x).symm

variable (F n U) in

def endAction : End F →+* AddMonoid.End (F.H' n U) where
  toFun f := (map f n U).hom
  map_one' := AddMonoidHom.ext map_id_apply
  map_mul' f g := AddMonoidHom.ext (map_comp_apply g f)
  map_zero' := AddMonoidHom.ext map_zero_apply
  map_add' f g := AddMonoidHom.ext (map_add_apply f g)

lemma endAction_apply (f : End F) (x : F.H' n U) : endAction F n U f x = map f n U x := rfl

end SiteCoh

end GlobalTheory
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

universe t v u

noncomputable section

namespace GlobalTheory

variable {X : Scheme.{u}}

instance hasSheafify_topCat (T : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u} := inferInstance

instance hasExt_sheaf_topCat (T : TopCat.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := inferInstance

instance hasSheafify_scheme (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

instance hasExt_sheaf_scheme (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance

def cohOn (F : X.Modules) (U : X.Opens) (n : ℕ) : Type u :=
  Sheaf.H'.{u} ((toAbSheaf X).obj F) n U

abbrev coh (F : X.Modules) (n : ℕ) : Type u := cohOn F ⊤ n

namespace cohOn

def action (F : X.Modules) (U : X.Opens) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H'.{u} ((toAbSheaf X).obj F) n U) :=
  (SiteCoh.endAction ((toAbSheaf X).obj F) n U).comp
    ((functorEndRingHom (toAbSheaf X) F).comp (smulEnd F))

lemma action_apply (F : X.Modules) (U : X.Opens) (n : ℕ) (r : Γ(X, ⊤))
    (x : Sheaf.H'.{u} ((toAbSheaf X).obj F) n U) :
    action F U n r x = SiteCoh.map ((toAbSheaf X).map (smulHom F r)) n U x :=
  SiteCoh.endAction_apply _ x

instance instAddCommGroup (F : X.Modules) (U : X.Opens) (n : ℕ) : AddCommGroup (cohOn F U n) :=
  addCommGroupOfAction (M := Sheaf.H'.{u} ((toAbSheaf X).obj F) n U) inferInstance (action F U n)

def toH' (F : X.Modules) (U : X.Opens) (n : ℕ) :
    cohOn F U n ≃+ Sheaf.H'.{u} ((toAbSheaf X).obj F) n U :=
  WithAction.toBase (action F U n)

section Module

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

instance instModule (F : X.Modules) (U : X.Opens) (n : ℕ) : Module R (cohOn F U n) :=
  { WithAction.instModule (action F U n) R with
    smul := fun r x ↦ action F U n (algebraMap R Γ(X, ⊤) r) x }

example (F : X.Modules) (U : X.Opens) (n : ℕ) :
    instModule ℤ F U n = AddCommGroup.toIntModule (cohOn F U n) := by
  with_reducible_and_instances rfl

variable {R} in

lemma toH'_smul {F : X.Modules} {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    toH' F U n (r • x) =
      SiteCoh.map ((toAbSheaf X).map (smulHom F (algebraMap R Γ(X, ⊤) r))) n U (toH' F U n x) :=
  (WithAction.toBase_smul (action F U n) r x).trans (action_apply F U n _ _)

instance instIsScalarTower (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S]
    [IsScalarTower R S Γ(X, ⊤)] (F : X.Modules) (U : X.Opens) (n : ℕ) :
    IsScalarTower R S (cohOn F U n) :=
  WithAction.instIsScalarTower (action F U n) R S

instance instSMulCommClass (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)]
    (F : X.Modules) (U : X.Opens) (n : ℕ) : SMulCommClass R S (cohOn F U n) :=
  WithAction.instSMulCommClass (action F U n) R S

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (n : ℕ) : cohOn F U n →ₗ[R] cohOn G U n :=
  WithAction.linearMap (action F U n) (action G U n) R
    (SiteCoh.map ((toAbSheaf X).map φ) n U).hom fun r x ↦ by
      rw [action_apply, action_apply, ← SiteCoh.map_comp_apply, ← SiteCoh.map_comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, smulHom_comp]

def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (n : ℕ) : cohOn F U n →ₗ[R] cohOn F V n :=
  WithAction.linearMap (action F U n) (action F V n) R
    (SiteCoh.res ((toAbSheaf X).obj F) n (homOfLE h)).hom fun r x ↦ by
      rw [action_apply, action_apply, SiteCoh.res_map_apply]

variable {F G H : X.Modules} {U V W : X.Opens} {n : ℕ}

lemma toH'_map (φ : F ⟶ G) (x : cohOn F U n) :
    toH' G U n (map R φ U n x) = SiteCoh.map ((toAbSheaf X).map φ) n U (toH' F U n x) := rfl

lemma toH'_res (h : V ≤ U) (x : cohOn F U n) :
    toH' F V n (res R F h n x) =
      SiteCoh.res ((toAbSheaf X).obj F) n (homOfLE h) (toH' F U n x) := rfl

lemma smul_eq_map (r : R) (x : cohOn F U n) :
    r • x = map R (smulHom F (algebraMap R Γ(X, ⊤) r)) U n x := rfl

@[simp] lemma map_smulHom_apply (r : Γ(X, ⊤)) (x : cohOn F U n) :
    map R (smulHom F r) U n x = r • x := rfl

variable (F U n) in

@[simp] lemma map_id : map R (𝟙 F) U n = LinearMap.id := by
  ext x
  apply (toH' F U n).injective
  rw [toH'_map, CategoryTheory.Functor.map_id, SiteCoh.map_id_apply, LinearMap.id_apply]

variable (U n) in

lemma map_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    map R (φ ≫ ψ) U n = map R ψ U n ∘ₗ map R φ U n := by
  ext x
  apply (toH' H U n).injective
  rw [LinearMap.comp_apply, toH'_map, toH'_map, toH'_map, Functor.map_comp,
    SiteCoh.map_comp_apply]

lemma map_map (φ : F ⟶ G) (ψ : G ⟶ H) (x : cohOn F U n) :
    map R ψ U n (map R φ U n x) = map R (φ ≫ ψ) U n x := by
  rw [map_comp]; rfl

variable (U n) in

lemma map_add_hom (φ ψ : F ⟶ G) : map R (φ + ψ) U n = map R φ U n + map R ψ U n := by
  ext x
  apply (toH' G U n).injective
  rw [LinearMap.add_apply, map_add, toH'_map, toH'_map, toH'_map, Functor.map_add,
    SiteCoh.map_add_apply]

variable (F G U n) in

@[simps! apply] def mapAddHom : (F ⟶ G) →+ (cohOn F U n →ₗ[R] cohOn G U n) :=
  AddMonoidHom.mk' (fun φ ↦ map R φ U n) (map_add_hom R U n)

variable (F G U n) in

@[simp] lemma map_zero_hom : map R (0 : F ⟶ G) U n = 0 := map_zero (mapAddHom R F G U n)

variable (U n) in

lemma map_neg_hom (φ : F ⟶ G) : map R (-φ) U n = -map R φ U n := map_neg (mapAddHom R F G U n) φ

variable (U n) in

lemma map_sub_hom (φ ψ : F ⟶ G) : map R (φ - ψ) U n = map R φ U n - map R ψ U n :=
  map_sub (mapAddHom R F G U n) φ ψ

variable (U n) in

lemma map_sum_hom {ι : Type t} (s : Finset ι) (φ : ι → (F ⟶ G)) :
    map R (∑ i ∈ s, φ i) U n = ∑ i ∈ s, map R (φ i) U n :=
  map_sum (mapAddHom R F G U n) φ s

variable (U n) in

lemma map_smul_hom (r : Γ(X, ⊤)) (φ : F ⟶ G) : map R (r • φ) U n = r • map R φ U n := by
  rw [smul_hom_def, map_comp]; rfl

variable (F U n) in

@[simp] lemma res_refl : res R F (le_refl U) n = LinearMap.id := by
  ext x
  apply (toH' F U n).injective
  rw [toH'_res, show homOfLE (le_refl U) = 𝟙 U from rfl, SiteCoh.res_id_apply,
    LinearMap.id_apply]

variable (F n) in

lemma res_comp_res (h : V ≤ U) (h' : W ≤ V) :
    res R F h' n ∘ₗ res R F h n = res R F (h'.trans h) n := by
  ext x
  apply (toH' F W n).injective
  rw [LinearMap.comp_apply, toH'_res, toH'_res, toH'_res, ← SiteCoh.res_comp_apply,
    homOfLE_comp]

@[simp] lemma res_res (h : V ≤ U) (h' : W ≤ V) (x : cohOn F U n) :
    res R F h' n (res R F h n x) = res R F (h'.trans h) n x :=
  LinearMap.congr_fun (res_comp_res R F n h h') x

lemma res_map (φ : F ⟶ G) (h : V ≤ U) (x : cohOn F U n) :
    res R G h n (map R φ U n x) = map R φ V n (res R F h n x) := by
  apply (toH' G V n).injective
  rw [toH'_res, toH'_map, toH'_map, toH'_res, SiteCoh.res_map_apply]

variable (n) in

lemma res_comp_map (φ : F ⟶ G) (h : V ≤ U) :
    res R G h n ∘ₗ map R φ U n = map R φ V n ∘ₗ res R F h n :=
  LinearMap.ext (res_map R φ h)

variable (U n) in

@[simps! apply symm_apply] def mapIso (e : F ≅ G) : cohOn F U n ≃ₗ[R] cohOn G U n :=
  LinearEquiv.ofLinearMap (map R e.hom U n) (map R e.inv U n)
    (by rw [← map_comp, e.inv_hom_id, map_id]) (by rw [← map_comp, e.hom_inv_id, map_id])

variable (U n) in

lemma map_bijective (φ : F ⟶ G) [IsIso φ] : Function.Bijective (map R φ U n) :=
  (mapIso R U n (asIso φ)).bijective

variable (F n) in

@[simps! apply symm_apply] def congrOpens (h : U = V) : cohOn F U n ≃ₗ[R] cohOn F V n :=
  LinearEquiv.ofLinearMap (res R F h.ge n) (res R F h.le n)
    (by rw [res_comp_res, res_refl]) (by rw [res_comp_res, res_refl])

end Module

abbrev moduleOfRingHom {R : Type v} [CommRing R] (f : R →+* Γ(X, ⊤)) (F : X.Modules)
    (U : X.Opens) (n : ℕ) : Module R (cohOn F U n) :=
  letI := f.toAlgebra
  instModule R F U n


lemma subsingleton_of_isZero {F : X.Modules} (h : IsZero F) (U : X.Opens) (n : ℕ) :
    Subsingleton (cohOn F U n) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    have h₁ : map ℤ (𝟙 F) U n x = x := by rw [map_id]; rfl
    rw [← h₁, h.eq_of_src (𝟙 F) 0, map_zero_hom]; rfl

open ZeroObject in

instance subsingleton_zero (U : X.Opens) (n : ℕ) : Subsingleton (cohOn (0 : X.Modules) U n) :=
  subsingleton_of_isZero (isZero_zero _) U n

instance subsingleton_bot (F : X.Modules) (n : ℕ) : Subsingleton (cohOn F ⊥ n) :=
  haveI : Subsingleton (((SiteCoh.freeSheaf (Opens.grothendieckTopology X)).obj
      (⊥ : X.Opens)).obj.obj (op ⊥)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (TopCat.Sheaf.isTerminalOfEmpty (X := X.toPresheafedSpace.carrier) _).isZero
  SiteCoh.subsingleton_of_subsingleton_freeSheaf ((toAbSheaf X).obj F) n ⊥

lemma subsingleton_of_injective (F : X.Modules) [Injective ((toAbSheaf X).obj F)] (U : X.Opens)
    (n : ℕ) : Subsingleton (cohOn F U (n + 1)) :=
  SiteCoh.subsingleton_of_injective ((toAbSheaf X).obj F) n U

section Products

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type t} (U : X.Opens) (n : ℕ)

@[simps! apply symm_apply] def biconeEquiv [Fintype ι] {F : ι → X.Modules} {c : Bicone F}
    (hc : c.IsBilimit) : cohOn c.pt U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  LinearEquiv.ofLinearMap (LinearMap.pi fun i ↦ map R (c.π i) U n)
    (∑ i, map R (c.ι i) U n ∘ₗ LinearMap.proj i)
    (by
      classical
      refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        LinearMap.proj_apply, LinearMap.id_apply, map_map]
      rw [Finset.sum_eq_single i]
      · rw [bicone_ι_π_self, map_id, LinearMap.id_apply]
      · intro j _ hj
        rw [bicone_ι_π_ne _ hj, map_zero_hom, LinearMap.zero_apply]
      · simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, LinearMap.id_apply, map_map]
      rw [← LinearMap.sum_apply, ← map_sum_hom, IsBilimit.total hc, map_id, LinearMap.id_apply])

lemma pi_map_bijective [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c) :
    Function.Bijective (LinearMap.pi fun i ↦ map R (c.proj i) U n) := by
  cases nonempty_fintype ι
  exact (biconeEquiv R U n (biconeIsBilimitOfLimitConeOfIsLimit hc)).bijective

def fanEquiv [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c) :
    cohOn c.pt U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  LinearEquiv.ofBijective _ (pi_map_bijective R U n hc)

@[simp] lemma fanEquiv_apply [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c)
    (x : cohOn c.pt U n) (i : ι) : fanEquiv R U n hc x i = map R (c.proj i) U n x := rfl

def piEquiv [Finite ι] (F : ι → X.Modules) : cohOn (∏ᶜ F) U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  fanEquiv R U n (productIsProduct F)

@[simp] lemma piEquiv_apply [Finite ι] (F : ι → X.Modules) (x : cohOn (∏ᶜ F) U n) (i : ι) :
    piEquiv R U n F x i = map R (Pi.π F i) U n x := rfl

attribute [local instance] Abelian.hasFiniteBiproducts

def biproductEquiv [Finite ι] (F : ι → X.Modules) :
    cohOn (⨁ F) U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  fanEquiv R U n (c := Fan.mk (⨁ F) (biproduct.π F)) (biproduct.isLimit F)

@[simp] lemma biproductEquiv_apply [Finite ι] (F : ι → X.Modules) (x : cohOn (⨁ F) U n) (i : ι) :
    biproductEquiv R U n F x i = map R (biproduct.π F i) U n x := rfl

@[simps! apply symm_apply] def biprodEquiv (F G : X.Modules) :
    cohOn (F ⊞ G) U n ≃ₗ[R] cohOn F U n × cohOn G U n :=
  LinearEquiv.ofLinearMap ((map R biprod.fst U n).prod (map R biprod.snd U n))
    ((map R biprod.inl U n).coprod (map R biprod.inr U n))
    (by
      refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_ <;>
      simp [map_map])
    (by
      rw [LinearMap.coprod_comp_prod, ← map_comp, ← map_comp, ← map_add_hom, biprod.total,
        map_id])

end Products
end cohOn

def sectionsOn (F : X.Modules) (U : X.Opens) : Type u := Γ(F, U)

namespace sectionsOn

def action (F : X.Modules) (U : X.Opens) : Γ(X, ⊤) →+* AddMonoid.End Γ(F, U) :=
  (Module.toAddMonoidEnd Γ(X, U) Γ(F, U)).comp (restrictGlobal X U)

lemma action_apply (F : X.Modules) (U : X.Opens) (r : Γ(X, ⊤)) (x : Γ(F, U)) :
    action F U r x = restrictGlobal X U r • x := rfl

instance instAddCommGroup (F : X.Modules) (U : X.Opens) : AddCommGroup (sectionsOn F U) :=
  addCommGroupOfAction (M := Γ(F, U)) inferInstance (action F U)

def toΓ (F : X.Modules) (U : X.Opens) : sectionsOn F U ≃+ Γ(F, U) := WithAction.toBase (action F U)

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

instance instModule (F : X.Modules) (U : X.Opens) : Module R (sectionsOn F U) :=
  { WithAction.instModule (action F U) R with
    smul := fun r x ↦ action F U (algebraMap R Γ(X, ⊤) r) x }

example (F : X.Modules) (U : X.Opens) :
    instModule ℤ F U = AddCommGroup.toIntModule (sectionsOn F U) := by
  with_reducible_and_instances rfl

variable {R} in

lemma toΓ_smul {F : X.Modules} {U : X.Opens} (r : R) (x : sectionsOn F U) :
    toΓ F U (r • x) = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • toΓ F U x := rfl

instance instIsScalarTower (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S]
    [IsScalarTower R S Γ(X, ⊤)] (F : X.Modules) (U : X.Opens) : IsScalarTower R S (sectionsOn F U) :=
  WithAction.instIsScalarTower (action F U) R S

instance instSMulCommClass (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)]
    (F : X.Modules) (U : X.Opens) : SMulCommClass R S (sectionsOn F U) :=
  WithAction.instSMulCommClass (action F U) R S

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : sectionsOn F U →ₗ[R] sectionsOn G U :=
  WithAction.linearMap (action F U) (action G U) R (φ.app U).hom
    fun r x ↦ φ.app_smul (restrictGlobal X U r) x

def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : sectionsOn F U →ₗ[R] sectionsOn F V :=
  WithAction.linearMap (action F U) (action F V) R (F.presheaf.map (homOfLE h).op).hom
    fun r x ↦ by rw [action_apply, action_apply, F.map_smul, map_restrictGlobal]

variable {F G H : X.Modules} {U V W : X.Opens}

@[simp] lemma toΓ_map (φ : F ⟶ G) (x : sectionsOn F U) :
    toΓ G U (map R φ U x) = φ.app U (toΓ F U x) := rfl

@[simp] lemma toΓ_res (h : V ≤ U) (x : sectionsOn F U) :
    toΓ F V (res R F h x) = F.presheaf.map (homOfLE h).op (toΓ F U x) := rfl

variable (F U) in

@[simp] lemma map_id : map R (𝟙 F) U = LinearMap.id := rfl

variable (U) in

lemma map_comp (φ : F ⟶ G) (ψ : G ⟶ H) : map R (φ ≫ ψ) U = map R ψ U ∘ₗ map R φ U := rfl

variable (U) in

lemma map_add_hom (φ ψ : F ⟶ G) : map R (φ + ψ) U = map R φ U + map R ψ U := rfl

variable (F U) in

@[simp] lemma res_refl : res R F (le_refl U) = LinearMap.id := by
  ext x
  apply (toΓ F U).injective
  rw [toΓ_res, show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

variable (F) in

lemma res_comp_res (h : V ≤ U) (h' : W ≤ V) : res R F h' ∘ₗ res R F h = res R F (h'.trans h) := by
  ext x
  apply (toΓ F W).injective
  rw [LinearMap.comp_apply, toΓ_res, toΓ_res, toΓ_res, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

lemma res_map (φ : F ⟶ G) (h : V ≤ U) (x : sectionsOn F U) :
    res R G h (map R φ U x) = map R φ V (res R F h x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x).symm

variable (F U) in

def equivOfSMul [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x) :
    sectionsOn F U ≃ₗ[R] Γ(F, U) :=
  { toΓ F U with map_smul' := fun r x ↦ (toΓ_smul r x).trans (h r _).symm }

@[simp] lemma equivOfSMul_apply [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x)
    (x : sectionsOn F U) : equivOfSMul R F U h x = toΓ F U x := rfl

variable (F) in

def topEquiv : sectionsOn F ⊤ ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  equivOfSMul Γ(X, ⊤) F ⊤ fun r x ↦ by rw [restrictGlobal_top]; rfl

def specEquiv {A : CommRingCat.{u}} (F : (Spec A).Modules) (U : (Spec A).Opens) :
    sectionsOn F U ≃ₗ[A] Γ(F, U) :=
  equivOfSMul A F U fun r x ↦ by
    rw [Scheme.Modules.smul_Spec_def]
    congr 1

end sectionsOn

namespace cohOn

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

def zeroEquiv (F : X.Modules) (U : X.Opens) : cohOn F U 0 ≃ₗ[R] sectionsOn F U :=
  WithAction.linearEquiv (action F U 0) (sectionsOn.action F U) R
    (SiteCoh.zeroEquiv ((toAbSheaf X).obj F) U) fun r x ↦ by
      rw [action_apply]
      exact SiteCoh.zeroEquiv_map ((toAbSheaf X).map (smulHom F r)) U x

variable {F G : X.Modules} {U V : X.Opens}

lemma toΓ_zeroEquiv (x : cohOn F U 0) :
    sectionsOn.toΓ F U (zeroEquiv R F U x) =
      SiteCoh.zeroEquiv ((toAbSheaf X).obj F) U (toH' F U 0 x) := rfl

lemma zeroEquiv_map (φ : F ⟶ G) (x : cohOn F U 0) :
    zeroEquiv R G U (map R φ U 0 x) = sectionsOn.map R φ U (zeroEquiv R F U x) :=
  SiteCoh.zeroEquiv_map ((toAbSheaf X).map φ) U (toH' F U 0 x)


variable (F U) in

def zeroAddEquiv : cohOn F U 0 ≃+ Γ(F, U) :=
  (zeroEquiv ℤ F U).toAddEquiv.trans (sectionsOn.toΓ F U)


end cohOn

abbrev structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureModuleΓEquiv (X : Scheme.{u}) (U : X.Opens) :
    Γ(structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace coh

def zeroEquiv (F : X.Modules) : coh F 0 ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  (cohOn.zeroEquiv Γ(X, ⊤) F ⊤).trans (sectionsOn.topEquiv F)

lemma zeroEquiv_map {F G : X.Modules} (φ : F ⟶ G) (x : coh F 0) :
    zeroEquiv G (cohOn.map Γ(X, ⊤) φ ⊤ 0 x) = φ.app ⊤ (zeroEquiv F x) :=
  congrArg (sectionsOn.toΓ G ⊤) (cohOn.zeroEquiv_map Γ(X, ⊤) φ x)

def toH (F : X.Modules) (n : ℕ) : coh F n ≃+ Sheaf.H.{u} ((toAbSheaf X).obj F) n :=
  (cohOn.toH' F ⊤ n).trans (SiteCoh.terminalEquiv ((toAbSheaf X).obj F) n isTerminalTop)

lemma toH_map (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (x : coh F n) :
    toH G n (cohOn.map R φ ⊤ n x) = Sheaf.H.map ((toAbSheaf X).map φ) n (toH F n x) :=
  SiteCoh.terminalEquiv_map ((toAbSheaf X).map φ) n isTerminalTop (cohOn.toH' F ⊤ n x)

lemma equiv₀_toH (F : X.Modules) (x : coh F 0) :
    Sheaf.H.equiv₀ ((toAbSheaf X).obj F) isTerminalTop (toH F 0 x) = zeroEquiv F x :=
  SiteCoh.equiv₀_terminalEquiv ((toAbSheaf X).obj F) isTerminalTop (cohOn.toH' F ⊤ 0 x)

def zeroUnitEquiv (X : Scheme.{u}) :
    coh (structureModule X) 0 ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  (zeroEquiv (structureModule X)).trans (structureModuleΓEquiv X ⊤)

def zeroUnitSpecEquiv (A : CommRingCat.{u}) :
    coh (structureModule (Spec A)) 0 ≃ₗ[A] A :=
  ((zeroUnitEquiv (Spec A)).restrictScalars A).trans
    (LinearEquiv.ofBijective (Algebra.linearMap A Γ(Spec A, ⊤)) (by
      have h : ⇑(Algebra.linearMap A Γ(Spec A, ⊤)) = (Scheme.ΓSpecIso A).inv :=
        funext fun r ↦ restrictGlobal_top ((Scheme.ΓSpecIso A).inv r)
      rw [h]
      exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv)).symm

end coh

section Functors

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

@[simps] def cohOnFunctor (U : X.Opens) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := ModuleCat.of R (cohOn F U n)
  map φ := ModuleCat.ofHom (cohOn.map R φ U n)
  map_id F := by rw [cohOn.map_id]; rfl
  map_comp φ ψ := by rw [cohOn.map_comp]; rfl

instance cohOnFunctor_additive (U : X.Opens) (n : ℕ) : (cohOnFunctor R U n).Additive where
  map_add {_ _ φ ψ} := ModuleCat.hom_ext (cohOn.map_add_hom R U n φ ψ)

@[simps] def cohPresheaf (F : X.Modules) (n : ℕ) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (cohOn F U.unop n)
  map i := ModuleCat.ofHom (cohOn.res R F i.unop.le n)
  map_id U := ModuleCat.hom_ext (cohOn.res_refl R F U.unop n)
  map_comp i j := ModuleCat.hom_ext (cohOn.res_comp_res R F n i.unop.le j.unop.le).symm

@[simps] def sectionsOnFunctor (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := ModuleCat.of R (sectionsOn F U)
  map φ := ModuleCat.ofHom (sectionsOn.map R φ U)
  map_id _ := rfl
  map_comp _ _ := rfl

instance sectionsOnFunctor_additive (U : X.Opens) : (sectionsOnFunctor R U).Additive where
  map_add := rfl

@[simps] def sectionsPresheaf (F : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (sectionsOn F U.unop)
  map i := ModuleCat.ofHom (sectionsOn.res R F i.unop.le)
  map_id U := ModuleCat.hom_ext (sectionsOn.res_refl R F U.unop)
  map_comp i j := ModuleCat.hom_ext (sectionsOn.res_comp_res R F i.unop.le j.unop.le).symm

end Functors

abbrev algebraΓOfHom {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) : Algebra R Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra

lemma algebraΓOfHom_algebraMap {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (r : R) :
    letI := algebraΓOfHom f
    algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := rfl

abbrev algebraΓSpec (A : CommRingCat.{u}) : Algebra A Γ(Spec A, ⊤) := inferInstance

lemma algebraΓOfHom_id (R : Type u) [CommRing R] :
    algebraΓOfHom (𝟙 (Spec (.of R))) = algebraΓSpec (.of R) :=
  Algebra.algebra_ext _ _ fun r ↦ (restrictGlobal_top ((Scheme.ΓSpecIso (.of R)).inv r)).symm

abbrev algebraΓOfOver (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))] :
    Algebra R Γ(X, ⊤) :=
  algebraΓOfHom (X ↘ Spec (.of R))

namespace OverSpec

scoped[GlobalTheory.OverSpec] attribute [instance 50] GlobalTheory.algebraΓOfOver

example (R : Type u) [CommRing R] [X.Over (Spec (.of R))] (F : X.Modules) (n : ℕ) :
    Module R (coh F n) := inferInstance

end OverSpec

def hdim (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k (coh F n)

section hdim

variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] {F G : X.Modules} (n : ℕ)

lemma hdim_def (F : X.Modules) : hdim k F n = Module.finrank k (coh F n) := rfl


lemma hdim_eq_zero_iff [Module.Finite k (coh F n)] : hdim k F n = 0 ↔ Subsingleton (coh F n) :=
  Module.finrank_zero_iff

lemma hdim_eq_zero_of_subsingleton [Subsingleton (coh F n)] : hdim k F n = 0 :=
  Module.finrank_zero_of_subsingleton

lemma hdim_congr (e : F ≅ G) : hdim k F n = hdim k G n :=
  (cohOn.mapIso k ⊤ n e).finrank_eq


lemma hdim_pi {ι : Type t} [Fintype ι] (F : ι → X.Modules) [∀ i, Module.Finite k (coh (F i) n)] :
    hdim k (∏ᶜ F) n = ∑ i, hdim k (F i) n :=
  (cohOn.piEquiv k ⊤ n F).finrank_eq.trans (Module.finrank_pi_fintype k)

lemma hdim_zero (F : X.Modules) : hdim k F 0 = Module.finrank k (sectionsOn F ⊤) :=
  (cohOn.zeroEquiv k F ⊤).finrank_eq

end hdim

instance cohOn.finite_biprod (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (F G : X.Modules)
    (U : X.Opens) (n : ℕ) [Module.Finite R (cohOn F U n)] [Module.Finite R (cohOn G U n)] :
    Module.Finite R (cohOn (F ⊞ G) U n) :=
  Module.Finite.equiv (cohOn.biprodEquiv R U n F G).symm

instance cohOn.finite_pi (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type t} [Finite ι]
    (F : ι → X.Modules) (U : X.Opens) (n : ℕ) [∀ i, Module.Finite R (cohOn (F i) U n)] :
    Module.Finite R (cohOn (∏ᶜ F) U n) :=
  Module.Finite.equiv (cohOn.piEquiv R U n F).symm

example (k : Type u) [Field k] :
    letI : Algebra k Γ(Spec (.of k), ⊤) := algebraΓSpec (.of k)
    Module.Finite k (coh (structureModule (Spec (.of k))) 0) ∧
      hdim k (structureModule (Spec (.of k))) 0 = 1 :=
  letI : Algebra k Γ(Spec (.of k), ⊤) := algebraΓSpec (.of k)
  ⟨Module.Finite.equiv (coh.zeroUnitSpecEquiv (.of k)).symm,
    (coh.zeroUnitSpecEquiv (.of k)).finrank_eq.trans (Module.finrank_self k)⟩

example : Nontrivial (coh (structureModule (Spec (.of ℤ))) 0) :=
  (coh.zeroUnitSpecEquiv (.of ℤ)).toEquiv.nontrivial

example (F : X.Modules) (U : X.Opens) (n : ℕ) (x : cohOn F U n) :
    cohOn.map ℤ (-𝟙 F) U n x = -x := by
  rw [cohOn.map_neg_hom, cohOn.map_id]; rfl

end GlobalTheory
end
end
