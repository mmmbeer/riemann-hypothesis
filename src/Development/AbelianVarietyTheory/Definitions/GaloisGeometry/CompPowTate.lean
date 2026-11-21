import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem

section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Rel

variable (R : Type) [CommRing R]

abbrev Shv (X : Scheme.{0}) : Type 2 := Sheaf (Scheme.proetaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R))

instance (X : Scheme.{0}) : HasSheafify (Scheme.proetaleTopology.{0}.over X) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  infer_instance

instance (X : Scheme.{0}) : IsGrothendieckAbelian.{1} (Shv R X) := by
  have : EssentiallySmall.{1} (Over X) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

def free (X : Scheme.{0}) : Over X ⥤ Shv R X :=
  uliftYoneda.{1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R)) ⋙ presheafToSheaf _ _

def freeEquiv {X : Scheme.{0}} (T : Over X) (F : Shv R X) : ((free R X).obj T ⟶ F) ≃ F.obj.obj (op T) :=
  ((sheafificationAdjunction _ _).homEquiv _ F).trans
    (((((ModuleCat.adj (ULift.{1} R)).whiskerRight (Over X)ᵒᵖ)).homEquiv (uliftYoneda.{1}.obj T) F.obj).trans
      uliftYonedaEquiv)

abbrev res {X Y : Scheme.{0}} (f : X ⟶ Y) : Shv R Y ⥤ Shv R X :=
  Scheme.proetaleTopology.{0}.overMapPullback (ModuleCat.{1} (ULift.{1} R)) f

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : PreservesFiniteLimits (res R f) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.map f) (ModuleCat.{1} (ULift.{1} R))
    (Scheme.proetaleTopology.{0}.over X) (Scheme.proetaleTopology.{0}.over Y)).isRightAdjoint
  infer_instance

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : PreservesFiniteColimits (res R f) := by
  have := ((Over.map f).sheafAdjunctionCocontinuous (ModuleCat.{1} (ULift.{1} R))
    (Scheme.proetaleTopology.{0}.over X) (Scheme.proetaleTopology.{0}.over Y)).isLeftAdjoint
  infer_instance

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : (res R f).Additive where
  map_add := rfl

instance {X Y : Scheme.{0}} (f : X ⟶ Y) : (res R f).Linear (ULift.{1} R) where
  map_smul _ _ := rfl

variable {R}

def H {X : Scheme.{0}} (F : Shv R X) (n : ℕ) (T : Over X) : Type 1 := Abelian.Ext.{1} ((free R X).obj T) F n

instance {X : Scheme.{0}} (F : Shv R X) (n : ℕ) (T : Over X) : AddCommGroup (H F n T) :=
  inferInstanceAs (AddCommGroup (Abelian.Ext.{1} ((free R X).obj T) F n))

instance {X : Scheme.{0}} (F : Shv R X) (n : ℕ) (T : Over X) : Module R (H F n T) :=
  Module.compHom (Abelian.Ext.{1} ((free R X).obj T) F n) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

def Sec {X : Scheme.{0}} (F : Shv R X) (T : Over X) : Type 1 := F.obj.obj (op T)

instance {X : Scheme.{0}} (F : Shv R X) (T : Over X) : AddCommGroup (Sec F T) :=
  inferInstanceAs (AddCommGroup (F.obj.obj (op T)))

instance {X : Scheme.{0}} (F : Shv R X) (T : Over X) : Module R (Sec F T) :=
  Module.compHom (F.obj.obj (op T)) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

variable {X Y : Scheme.{0}} {F : Shv R X} {G : Shv R Y} {T : Over X} {T' : Over Y}

def overHom (f : X ⟶ Y) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) : (Over.map f).obj T ⟶ T' :=
  Over.homMk u hu

variable (R) in

def freeRes (f : X ⟶ Y) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) :
    (free R X).obj T ⟶ (res R f).obj ((free R Y).obj T') :=
  (freeEquiv R T ((res R f).obj ((free R Y).obj T'))).symm
    (freeEquiv R ((Over.map f).obj T) ((free R Y).obj T') ((free R Y).map (overHom f u hu)))

def pullExt (f : X ⟶ Y) (c : (res R f).obj G ⟶ F) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) (n : ℕ) :
    Abelian.Ext.{1} ((free R Y).obj T') G n →ₗ[ULift.{1} R] Abelian.Ext.{1} ((free R X).obj T) F n :=
  ((Abelian.Ext.mk₀ (freeRes R f u hu)).precompOfLinear (ULift.{1} R) F (zero_add n)).comp
    (((Abelian.Ext.mk₀ c).postcompOfLinear (ULift.{1} R) ((res R f).obj ((free R Y).obj T')) (add_zero n)).comp
      ((res R f).mapExtLinearMap.{1, 1} (ULift.{1} R) ((free R Y).obj T') G n))

def pull (f : X ⟶ Y) (c : (res R f).obj G ⟶ F) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) (n : ℕ) :
    H G n T' →ₗ[R] H F n T where
  toFun z := pullExt f c u hu n z
  map_add' z w := (pullExt f c u hu n).map_add z w
  map_smul' r z := (pullExt f c u hu n).map_smul (ULift.up r : ULift.{1} R) z

def secPull (f : X ⟶ Y) (c : (res R f).obj G ⟶ F) (u : T.left ⟶ T'.left) (hu : u ≫ T'.hom = T.hom ≫ f) :
    Sec G T' →ₗ[R] Sec F T where
  toFun s := (G.obj.map (overHom f u hu).op ≫ c.hom.app (op T)).hom s
  map_add' s t := map_add _ _ _
  map_smul' r s := map_smul _ (ULift.up r : ULift.{1} R) _

variable (R) [TopologicalSpace R] [IsTopologicalRing R]

abbrev coef (X : Scheme.{0}) : Shv R X := (GlobalTheory.Et.coef R).over X

variable {R} in

def IsLisse (F : Shv R X) : Prop :=
  ∃ S ∈ Scheme.proetaleTopology.{0} X, ∀ ⦃U : Scheme.{0}⦄ (u : U ⟶ X), S u →
    ∃ r : ℕ, Nonempty ((res R u).obj F ≅ ∏ᶜ fun _ : Fin r => coef R U)

end GlobalTheory.Et.Rel

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Rel

variable (R : Type) [CommRing R] {X Y : Scheme.{0}}

def cohomZeroEquivSections (F : Shv R X) (T : Over X) : H F 0 T ≃ₗ[R] Sec F T where
  toEquiv := (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (free R X).obj T) (Y := F)).toEquiv.trans
    (freeEquiv R T F)
  map_add' z w :=
    (congrArg (freeEquiv R T F)
      ((Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (free R X).obj T) (Y := F)).map_add z w)).trans rfl
  map_smul' r z :=
    (congrArg (freeEquiv R T F)
      ((Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (free R X).obj T) (Y := F)).map_smul
        (ULift.up r : ULift.{1} R) z)).trans rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

def secCoef (T : Over X) : Sec (coef R X) T ≃ₗ[R] C(T.left, R) where
  toAddEquiv := (((isoSheafify _ (GlobalTheory.Et.H0.sh R)).app (op T.left)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift
  map_smul' r s := (congrArg AddEquiv.ulift (LinearEquiv.map_smul
    (((isoSheafify _ (GlobalTheory.Et.H0.sh R)).app (op T.left)).symm.toLinearEquiv) (ULift.up r) s)).trans rfl

def resCoef (f : X ⟶ Y) : (res R f).obj (coef R Y) ≅ coef R X :=
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget f) (ModuleCat.{1} (ULift.{1} R))
    (Scheme.proetaleTopology.{0}.over X) (Scheme.proetaleTopology.{0}.over Y) Scheme.proetaleTopology.{0}).app
    (GlobalTheory.Et.coef R)

theorem isLisse_pi_coef (X : Scheme.{0}) (r : ℕ) : IsLisse (∏ᶜ fun _ : Fin r => coef R X) :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ u _ =>
    ⟨r, ⟨PreservesProduct.iso (res R u) _ ≪≫ Pi.mapIso fun _ => resCoef R u⟩⟩⟩

theorem isLisse_coef (X : Scheme.{0}) : IsLisse (coef R X) :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun U u _ =>
    ⟨1, ⟨resCoef R u ≪≫ (productUniqueIso fun _ : Fin 1 => coef R U).symm⟩⟩⟩

end GlobalTheory.Et.Rel

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Rel

section Examples

variable {X : Scheme.{0}}

example : IsGrothendieckAbelian.{1} (Shv ℚ X) := inferInstance

example (F : Shv ℚ X) (T : Over X) : H F 0 T ≃ₗ[ℚ] Sec F T := cohomZeroEquivSections ℚ F T

example (T : Over X) : Sec (coef ℚ X) T ≃ₗ[ℚ] C(T.left, ℚ) := secCoef ℚ T

example : IsLisse (coef ℚ X) := isLisse_coef ℚ X

example : IsLisse (∏ᶜ fun _ : Fin 3 => coef ℚ X) := isLisse_pi_coef ℚ X 3

example (F : Shv ℚ X) (T : Over X) (q : ℚ) (z : H F 0 T) : cohomZeroEquivSections ℚ F T (q • z) = q • cohomZeroEquivSections ℚ F T z :=
  map_smul _ q z

end Examples

end GlobalTheory.Et.Rel

end
end

section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

structure RActPre (X : Scheme.{0}) (Γ : Type) [Group Γ] where

  P : (Over X)ᵒᵖ ⥤ Type

  act : Γ → (P ⟶ P)
  act_one : act 1 = 𝟙 P
  act_mul : ∀ g h, act (g * h) = act g ≫ act h

variable {X : Scheme.{0}} (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

def assocSet (Q : RActPre X Γ) (ξ : Γ →* GL ι E) (T : Over X) :
    Submodule E (∀ (T' : Over X) (_ : T' ⟶ T) (_ : Q.P.obj (op T')), C(T'.left, ι → E)) where
  carrier := {f | (∀ ⦃T'' T' : Over X⦄ (v : T'' ⟶ T') (u : T' ⟶ T) (η : Q.P.obj (op T')) (t : T''.left),
      f T'' (v ≫ u) (Q.P.map v.op η) t = f T' u η (v.left.base t)) ∧
    ∀ ⦃T' : Over X⦄ (u : T' ⟶ T) (η : Q.P.obj (op T')) (γ : Γ) (t : T'.left),
      f T' u ((Q.act γ).app (op T') η) t = ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f T' u η t}
  add_mem' {f g} hf hg := ⟨fun T'' T' v u η t => by
      simp only [Pi.add_apply, ContinuousMap.add_apply, hf.1 v u η t, hg.1 v u η t],
    fun T' u η γ t => by
      simp only [Pi.add_apply, ContinuousMap.add_apply, hf.2 u η γ t, hg.2 u η γ t, Matrix.mulVec_add]⟩
  zero_mem' := ⟨fun _ _ _ _ _ _ => rfl, fun T' u η γ t => by simp⟩
  smul_mem' c {f} hf := ⟨fun T'' T' v u η t => by
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hf.1 v u η t],
    fun T' u η γ t => by
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hf.2 u η γ t, Matrix.mulVec_smul]⟩

def assocRes (Q : RActPre X Γ) (ξ : Γ →* GL ι E) {T₁ T₂ : Over X} (w : T₁ ⟶ T₂) :
    assocSet E Q ξ T₂ →ₗ[E] assocSet E Q ξ T₁ where
  toFun f := ⟨fun T' u η => f.1 T' (u ≫ w) η,
    ⟨fun T'' T' v u η t => by simpa only [Category.assoc] using f.2.1 v (u ≫ w) η t,
      fun T' u η γ t => f.2.2 (u ≫ w) η γ t⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def assocPre (Q : RActPre X Γ) (ξ : Γ →* GL ι E) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} E) where
  obj T := ModuleCat.of (ULift.{1} E) (assocSet E Q ξ T.unop)
  map w := ModuleCat.ofHom
    { toFun := assocRes E Q ξ w.unop
      map_add' := (assocRes E Q ξ w.unop).map_add
      map_smul' := fun r f => (assocRes E Q ξ w.unop).map_smul r.down f }
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (funext fun T' => funext fun u =>
    funext fun η => by
      change f.1 T' (u ≫ 𝟙 _) η = f.1 T' u η
      rw [Category.comp_id]))
  map_comp w₁ w₂ := ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (funext fun T' => funext fun u =>
    funext fun η => by
      change f.1 T' (u ≫ (w₂.unop ≫ w₁.unop)) η = f.1 T' ((u ≫ w₂.unop) ≫ w₁.unop) η
      rw [Category.assoc]))

abbrev cPre (X : Scheme.{0}) (ι : Type) : (Over X)ᵒᵖ ⥤ Type :=
  (Over.forget X).op ⋙ continuousMapPresheaf.{0} (ι → E)

theorem cPre_isSheaf (X : Scheme.{0}) (ι : Type) :
    Presieve.IsSheaf (Scheme.proetaleTopology.{0}.over X) (cPre E X ι) := by
  have h0 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} (ι → E)) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf _)
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (CategoryTheory.Sheaf.over (⟨_, h0⟩ : Sheaf Scheme.proetaleTopology.{0} Type) X).cond

section
variable {E} (Q : RActPre X Γ) (ξ : Γ →* GL ι E)

theorem assocSet_nat {T : Over X} (f : assocSet E Q ξ T) {T'' T' : Over X} (v : T'' ⟶ T') (u : T' ⟶ T)
    (η : Q.P.obj (op T')) :
    f.1 T'' (v ≫ u) (Q.P.map v.op η) = (cPre E X ι).map v.op (f.1 T' u η) :=
  ContinuousMap.ext fun t => f.2.1 v u η t

end

theorem assocPre_isSheaf (Q : RActPre X Γ) (ξ : Γ →* GL ι E) :
    Presheaf.IsSheaf (Scheme.proetaleTopology.{0}.over X) (assocPre E Q ξ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _), isSheaf_iff_isSheaf_of_type]
  intro T S hS x hx
  have hC := cPre_isSheaf E X ι
  let xv : ∀ ⦃Y : Over X⦄ (f : Y ⟶ T), S f → assocSet E Q ξ Y := fun Y f h => x f h

  have K : ∀ ⦃Y₁ Y₂ Z : Over X⦄ (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T) (h₁ : S f₁) (h₂ : S f₂) (a₁ : Z ⟶ Y₁) (a₂ : Z ⟶ Y₂),
      a₁ ≫ f₁ = a₂ ≫ f₂ → ∀ η, (xv f₁ h₁).1 Z a₁ η = (xv f₂ h₂).1 Z a₂ η := by
    intro Y₁ Y₂ Z f₁ f₂ h₁ h₂ a₁ a₂ e η
    have := hx a₁ a₂ h₁ h₂ e
    have h := congrArg (fun z => (show assocSet E Q ξ Z from z).1 Z (𝟙 Z) η) this
    change (xv f₁ h₁).1 Z (𝟙 Z ≫ a₁) η = (xv f₂ h₂).1 Z (𝟙 Z ≫ a₂) η at h
    simpa only [Category.id_comp] using h
  let fam : ∀ (T' : Over X) (_ : T' ⟶ T) (_ : Q.P.obj (op T')),
      Presieve.FamilyOfElements (cPre E X ι) (S.pullback ‹T' ⟶ T›).arrows := fun T' u η Y w hw =>
    (xv (w ≫ u) hw).1 Y (𝟙 Y) (Q.P.map w.op η)
  have famC : ∀ T' u η, (fam T' u η).Compatible := by
    intro T' u η Y₁ Y₂ Z g₁ g₂ w₁ w₂ hw₁ hw₂ e
    change (cPre E X ι).map g₁.op ((xv (w₁ ≫ u) hw₁).1 Y₁ (𝟙 Y₁) (Q.P.map w₁.op η)) =
      (cPre E X ι).map g₂.op ((xv (w₂ ≫ u) hw₂).1 Y₂ (𝟙 Y₂) (Q.P.map w₂.op η))
    rw [← assocSet_nat, ← assocSet_nat, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, e]
    exact K _ _ _ _ _ _ (by simp only [Category.comp_id, ← Category.assoc, e]) _
  let gl : ∀ (T' : Over X) (u : T' ⟶ T) (η : Q.P.obj (op T')), C(T'.left, ι → E) := fun T' u η =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).amalgamate (fam T' u η) (famC T' u η)
  have glv : ∀ T' (u : T' ⟶ T) η ⦃Y : Over X⦄ (w : Y ⟶ T') (hw : S (w ≫ u)),
      (cPre E X ι).map w.op (gl T' u η) = (xv (w ≫ u) hw).1 Y (𝟙 Y) (Q.P.map w.op η) := fun T' u η Y w hw =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).valid_glue (famC T' u η) w hw
  have sep : ∀ (T' : Over X) (u : T' ⟶ T) (c₁ c₂ : C(T'.left, ι → E)),
      (∀ ⦃Y : Over X⦄ (w : Y ⟶ T'), S (w ≫ u) → (cPre E X ι).map w.op c₁ = (cPre E X ι).map w.op c₂) →
        c₁ = c₂ := fun T' u c₁ c₂ h =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).isSeparatedFor.ext fun Y w hw => h w hw
  have mem : (fun T' u η => gl T' u η) ∈ assocSet E Q ξ T := by
    refine ⟨fun T'' T' v u η t => ?_, fun T' u η γ t => ?_⟩
    · have H : gl T'' (v ≫ u) (Q.P.map v.op η) = (cPre E X ι).map v.op (gl T' u η) := by
        refine sep T'' (v ≫ u) _ _ fun Y w hw => ?_
        rw [glv _ _ _ w hw, ← Functor.map_comp_apply (cPre E X ι), ← op_comp,
          glv T' u η (w ≫ v) (by simpa only [Category.assoc] using hw), op_comp, Functor.map_comp_apply]
        exact K _ _ _ _ _ _ (by simp only [Category.assoc]) _
      exact DFunLike.congr_fun H t
    · let M : ∀ Z : Over X, C(Z.left, ι → E) → C(Z.left, ι → E) := fun Z c =>
        ⟨fun t => ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ c t, continuous_const.matrix_mulVec c.continuous⟩
      have hM : ∀ c t, M T' c t = ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ c t := fun _ _ => rfl
      have hMn : ∀ ⦃Y⦄ (w : Y ⟶ T') c, (cPre E X ι).map w.op (M T' c) = M Y ((cPre E X ι).map w.op c) :=
        fun _ _ _ => rfl
      rw [← hM]
      have H : gl T' u ((Q.act γ).app (op T') η) = M T' (gl T' u η) := by
        refine sep T' u _ _ fun Y w hw => ?_
        rw [glv _ _ _ w hw, hMn, glv _ _ _ w hw]
        have hn : Q.P.map w.op ((Q.act γ).app (op T') η) = (Q.act γ).app (op Y) (Q.P.map w.op η) :=
          (NatTrans.naturality_apply (Q.act γ) w.op η).symm
        rw [hn]
        exact ContinuousMap.ext fun t => (xv (w ≫ u) hw).2.2 (𝟙 Y) _ γ t
      exact DFunLike.congr_fun H t
  refine ⟨⟨_, mem⟩, ?_, ?_⟩
  · intro Y f hf
    apply Subtype.ext
    funext Y' u η
    change gl Y' (u ≫ f) η = (xv f hf).1 Y' u η
    refine sep Y' (u ≫ f) _ _ fun Z w hw => ?_
    rw [glv _ _ _ w hw, ← assocSet_nat]
    exact K _ _ _ _ _ _ (by simp only [Category.id_comp, Category.assoc]) _
  · intro t' ht'
    apply Subtype.ext
    funext T' u η
    have ht : ∀ ⦃Y : Over X⦄ (f : Y ⟶ T) (hf : S f) η', (show assocSet E Q ξ T from t').1 Y (𝟙 Y ≫ f) η' =
        (xv f hf).1 Y (𝟙 Y) η' := fun Y f hf η' =>
      congrArg (fun z => (show assocSet E Q ξ Y from z).1 Y (𝟙 Y) η') (ht' f hf)
    change (show assocSet E Q ξ T from t').1 T' u η = gl T' u η
    refine sep T' u _ _ fun Y w hw => ?_
    rw [glv _ _ _ w hw, ← assocSet_nat, ← ht _ hw, Category.id_comp]

def assoc (Q : RActPre X Γ) (ξ : Γ →* GL ι E) : Shv E X := ⟨assocPre E Q ξ, assocPre_isSheaf E Q ξ⟩

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

def secAssoc (Q : RActPre X Γ) (ξ : Γ →* GL ι E) (T : Over X) : Sec (assoc E Q ξ) T ≃ₗ[E] assocSet E Q ξ T where
  toFun f := f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ptOver (T' : Over X) (t : T'.left) : Over X := Over.mk (T'.left.fromSpecResidueField t ≫ T'.hom)

def ptHom (T' : Over X) (t : T'.left) : ptOver T' t ⟶ T' := Over.homMk (T'.left.fromSpecResidueField t) rfl

theorem ptHom_apply (T' : Over X) (t : T'.left) (y : (ptOver T' t).left) : (ptHom T' t).left.base y = t :=
  Scheme.fromSpecResidueField_apply t y

theorem assocSet_apply_of_pointwise (Q : RActPre X Γ) (ξ : Γ →* GL ι E) {T : Over X} (f : assocSet E Q ξ T)
    {T' : Over X} (u : T' ⟶ T) (η η' : Q.P.obj (op T')) (g : T'.left → Γ)
    (h : ∀ t, Q.P.map (ptHom T' t).op η' = (Q.act (g t)).app _ (Q.P.map (ptHom T' t).op η)) (t : T'.left) :
    f.1 T' u η' t = ((ξ (g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f.1 T' u η t := by
  let y : (ptOver T' t).left := IsLocalRing.closedPoint _
  have e1 := f.2.1 (ptHom T' t) u η' y
  have e2 := f.2.1 (ptHom T' t) u η y
  rw [ptHom_apply] at e1 e2
  rw [← e1, ← e2, h t]
  exact f.2.2 _ _ _ _

def trivTorsor (X : Scheme.{0}) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : RActPre X Γ where
  P := (Over.forget X).op ⋙ continuousMapPresheaf.{0} Γ
  act γ :=
    { app := fun T => ↾fun (c : C(T.unop.left, Γ)) => c * ContinuousMap.const _ γ
      naturality := fun _ _ _ => rfl }
  act_one := by
    apply NatTrans.ext
    funext T
    ext (c : C(T.unop.left, Γ))
    exact ContinuousMap.ext fun t => mul_one (c t)
  act_mul g h := by
    apply NatTrans.ext
    funext T
    ext (c : C(T.unop.left, Γ))
    exact ContinuousMap.ext fun t => (mul_assoc (c t) g h).symm

def trivTorsor.ofC [TopologicalSpace Γ] [IsTopologicalGroup Γ] {T : Over X} (c : C(T.left, Γ)) :
    (trivTorsor X Γ).P.obj (op T) := c

def trivTorsor.toC [TopologicalSpace Γ] [IsTopologicalGroup Γ] {T : Over X} (g : (trivTorsor X Γ).P.obj (op T)) :
    C(T.left, Γ) := g

def assocTrivEquiv [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ξ : Γ →* GL ι E) (hξ : Continuous ξ) (T : Over X) :
    assocSet E (trivTorsor X Γ) ξ T ≃ₗ[E] C(T.left, ι → E) where
  toFun f := f.1 T (𝟙 T) (trivTorsor.ofC 1)
  invFun v := ⟨fun T' u g => ⟨fun t => ((ξ (trivTorsor.toC g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v (u.left.base t),
      (Units.continuous_val.comp (hξ.comp (continuous_inv.comp (trivTorsor.toC g).continuous))).matrix_mulVec
        (v.continuous.comp u.left.base.hom.continuous)⟩,
    ⟨fun T'' T' w u g t => rfl, fun T' u g γ t => by
      change ((ξ (trivTorsor.toC g t * γ)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v (u.left.base t) =
        ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ (((ξ (trivTorsor.toC g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v (u.left.base t))
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, _root_.mul_inv_rev]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    apply Subtype.ext
    funext T' u g
    ext t : 1
    have h1 := assocSet_apply_of_pointwise (trivTorsor X Γ) ξ f u (trivTorsor.ofC 1) g (trivTorsor.toC g)
      (fun t => ContinuousMap.ext fun y => by
        change trivTorsor.toC g ((ptHom T' t).left.base y) = 1 * trivTorsor.toC g t
        exact (congrArg (trivTorsor.toC g) (ptHom_apply T' t y)).trans (one_mul _).symm) t
    have h2 := f.2.1 u (𝟙 T) (trivTorsor.ofC 1) t
    rw [Category.comp_id] at h2
    change ((ξ (trivTorsor.toC g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f.1 T (𝟙 T) (trivTorsor.ofC 1) (u.left.base t) =
      f.1 T' u g t
    rw [h1, ← h2]
    rfl
  right_inv v := by
    ext t : 1
    change ((ξ ((1 : C(T.left, Γ)) t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v ((𝟙 T : T ⟶ T).left.base t) = v t
    simp

end GlobalTheory.Et.Rel
end
end

section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.Ix (D : Datum p) : Type := by
  letI := D.freeLa
  exact Module.Free.ChooseBasisIndex ℤ D.La

instance (D : Datum p) : Fintype D.Ix := by
  letI := D.freeLa
  letI := D.finLa
  unfold Datum.Ix
  infer_instance

instance (D : Datum p) : DecidableEq D.Ix := Classical.decEq _

def Datum.basis (D : Datum p) : Module.Basis D.Ix ℤ D.La := by
  letI := D.freeLa
  exact Module.Free.chooseBasis ℤ D.La

def Datum.matO (D : Datum p) (c : D.O) : Matrix D.Ix D.Ix ℤ :=
  LinearMap.toMatrix D.basis D.basis (DistribMulAction.toLinearMap ℤ D.La c)

def Datum.gramEF (D : Datum p) : Matrix D.Ix D.Ix ℤ := LinearMap.BilinForm.toMatrix D.basis D.EF

def Datum.gPts (D : Datum p) (Λ : Type) [CommRing Λ] : Subgroup (GL D.Ix Λ) where
  carrier := {g | (∀ c : D.O, (g : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ) =
      (D.matO c).map (Int.castRingHom Λ) * g) ∧
    ∃ ν : Λˣ, (g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g = (ν : Λ) • D.gramEF.map (Int.castRingHom Λ)}
  mul_mem' {g h} hg hh := by
    refine ⟨fun c => ?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_assoc, hh.1 c, ← Matrix.mul_assoc, hg.1 c, Matrix.mul_assoc]
    · obtain ⟨ν, hν⟩ := hg.2
      obtain ⟨ν', hν'⟩ := hh.2
      refine ⟨ν * ν', ?_⟩
      calc ((g * h : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * (g * h : GL D.Ix Λ)
          = (h : Matrix D.Ix D.Ix Λ)ᵀ * ((g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g) * h := by
            simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]
        _ = ((ν * ν' : Λˣ) : Λ) • D.gramEF.map (Int.castRingHom Λ) := by
            rw [hν, Matrix.mul_smul, Matrix.smul_mul, hν', smul_smul, Units.val_mul, mul_comm]
  one_mem' := ⟨fun c => by simp, ⟨1, by simp⟩⟩
  inv_mem' {g} hg := by
    have h1 : ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * g = 1 := Units.inv_mul g
    have h2 : (g : Matrix D.Ix D.Ix Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) = 1 := Units.mul_inv g
    refine ⟨fun c => ?_, ?_⟩
    · calc ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ)
          = ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ) *
              ((g : Matrix D.Ix D.Ix Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)) := by rw [h2, Matrix.mul_one]
        _ = ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * ((g : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ)) *
              ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) := by rw [hg.1 c]; simp only [Matrix.mul_assoc]
        _ = (D.matO c).map (Int.castRingHom Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) := by
            rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    · obtain ⟨ν, hν⟩ := hg.2
      refine ⟨ν⁻¹, ?_⟩
      have e1 : ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ * (g : Matrix D.Ix D.Ix Λ)ᵀ = 1 := by
        rw [← transpose_mul, h2, transpose_one]
      have key : ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ *
          ((g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) =
          D.gramEF.map (Int.castRingHom Λ) := by
        calc _ = (((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ * (g : Matrix D.Ix D.Ix Λ)ᵀ) * D.gramEF.map (Int.castRingHom Λ) *
              ((g : Matrix D.Ix D.Ix Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [e1, h2, Matrix.one_mul, Matrix.mul_one]
      rw [hν, Matrix.mul_smul, Matrix.smul_mul] at key
      conv_rhs => rw [← key]
      rw [smul_smul, Units.inv_mul, one_smul]

def Datum.gPtsMap (D : Datum p) {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') : D.gPts Λ →* D.gPts Λ' :=
  ((Units.map (φ.mapMatrix : Matrix D.Ix D.Ix Λ →+* Matrix D.Ix D.Ix Λ').toMonoidHom).comp
    (D.gPts Λ).subtype).codRestrict _ fun g => by
    have hc : ∀ M : Matrix D.Ix D.Ix ℤ, (M.map (Int.castRingHom Λ)).map φ = M.map (Int.castRingHom Λ') := fun M => by
      rw [Matrix.map_map]; congr 1; funext z; simp
    refine ⟨fun c => ?_, ?_⟩
    · have := congrArg (fun A : Matrix D.Ix D.Ix Λ => A.map φ) (g.2.1 c)
      change ((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ * _ = _ * ((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ
      simpa only [Matrix.map_mul, hc] using this
    · obtain ⟨ν, hν⟩ := g.2.2
      refine ⟨Units.map φ.toMonoidHom ν, ?_⟩
      have := congrArg (fun A : Matrix D.Ix D.Ix Λ => A.map φ) hν
      have hs : ∀ (a : Λ) (A : Matrix D.Ix D.Ix Λ), (a • A).map φ = φ a • A.map φ := fun a A => by
        ext i j; simp
      change (((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ)ᵀ * _ * ((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ = _
      simp only [Matrix.map_mul, Matrix.transpose_map, hc, hs] at this
      exact this

theorem Datum.gPts_dot (D : Datum p) {Λ : Type} [CommRing Λ] (g : GL D.Ix Λ) (ν : Λˣ)
    (hg : (g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g = (ν : Λ) • D.gramEF.map (Int.castRingHom Λ))
    (v w : D.Ix → Λ) :
    ((g : Matrix D.Ix D.Ix Λ) *ᵥ v) ⬝ᵥ (D.gramEF.map (Int.castRingHom Λ) *ᵥ ((g : Matrix D.Ix D.Ix Λ) *ᵥ w)) =
      (ν : Λ) * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom Λ) *ᵥ w)) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose (g : Matrix D.Ix D.Ix Λ) v,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.vecMul_smul, smul_dotProduct, smul_eq_mul,
    ← Matrix.dotProduct_mulVec]

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

def Obj.IsTateL (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] (T : Over S) (ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o.A)) :
    Prop :=
  (∀ m v w, ev m (v + w) = ev m v * ev m w) ∧
  (∀ m (c : D.O) v, ev m ((D.matO c).map (Int.castRingHom ℤ_[ℓ]) *ᵥ v) = ev m v ≫ o.act.act c) ∧
  (∀ m v, ev m ((ℓ : ℤ_[ℓ]) ^ m • v) = 1) ∧
  (∀ m v, ev (m + 1) v ^ ℓ = ev m v) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (j : Over.mk x ⟶ T),
    ∃ χ : ℕ → AddChar ℤ_[ℓ] kˣ, (∀ m a, χ m a = 1 ↔ (ℓ : ℤ_[ℓ]) ^ m ∣ a) ∧ (∀ m a, χ (m + 1) a ^ ℓ = χ m a) ∧
      (∀ m v, j ≫ ev m v = 1 ↔ ∃ w, v = (ℓ : ℤ_[ℓ]) ^ m • w) ∧
      (∀ m (q : Over.mk x ⟶ o.A), q ^ (ℓ ^ m) = 1 ↔ ∃ v, j ≫ ev m v = q) ∧
      ∀ m v w, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((ℓ ^ m : ℕ) : ℤ) (j ≫ ev m v) (j ≫ ev m w)
        (unitOn (χ m (2 * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w)))))

section
variable {T₀ T : Over S} {A : Over S} [GrpObj A]

theorem comp_pow_tate (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) : u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
end

theorem Obj.IsTateL.comp {o : Obj b N s} {ℓ : ℕ} [Fact ℓ.Prime] {T T' : Over S}
    {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o.A)} (h : o.IsTateL ℓ T ev) (u : T' ⟶ T) :
    o.IsTateL ℓ T' (fun m v => u ≫ ev m v) := by
  obtain ⟨hadd, hlin, hkill, htow, hgeo⟩ := h
  refine ⟨fun m v w => by beta_reduce; rw [hadd, MonObj.comp_mul],
    fun m c v => by beta_reduce; rw [hlin, Category.assoc],
    fun m v => by beta_reduce; rw [hkill, MonObj.comp_one],
    fun m v => by beta_reduce; rw [← comp_pow_tate, htow], ?_⟩
  intro k _ _ x j
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := hgeo k x (j ≫ u)
  exact ⟨χ, h1, h2, fun m v => by beta_reduce; rw [← Category.assoc]; exact h3 m v,
    fun m q => by beta_reduce; simp only [← Category.assoc]; exact h4 m q,
    fun m v w => by beta_reduce; simp only [← Category.assoc]; exact h5 m v w⟩

theorem Obj.IsTateL.smul {o : Obj b N s} {ℓ : ℕ} [Fact ℓ.Prime] {T : Over S}
    {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o.A)} (h : o.IsTateL ℓ T ev) (g : D.gPts ℤ_[ℓ]) :
    o.IsTateL ℓ T (fun m v => ev m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v)) := by
  obtain ⟨hadd, hlin, hkill, htow, hgeo⟩ := h
  obtain ⟨hc, ν, hν⟩ := g.2
  set M : Matrix D.Ix D.Ix ℤ_[ℓ] := ((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) with hM
  set Mi : Matrix D.Ix D.Ix ℤ_[ℓ] := (((g : GL D.Ix ℤ_[ℓ])⁻¹ : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) with hMi
  have hMiM : ∀ v, Mi *ᵥ (M *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hMi, hM, Units.inv_mul, Matrix.one_mulVec]
  have hMMi : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hMi, hM, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨fun m v w => by simp only [Matrix.mulVec_add, hadd], fun m c v => ?_,
    fun m v => by simp only [Matrix.mulVec_smul, hkill], fun m v => htow m _, ?_⟩
  · beta_reduce
    rw [Matrix.mulVec_mulVec, hc c, ← Matrix.mulVec_mulVec, hlin]
  intro k _ _ x j
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := hgeo k x j
  refine ⟨fun m => (χ m).compAddMonoidHom (AddMonoidHom.mulLeft (ν : ℤ_[ℓ])), fun m a => ?_, fun m a => ?_,
    fun m v => ?_, fun m q => ?_, fun m v w => ?_⟩
  · simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft, h1, Units.dvd_mul_left]
  · simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft, h2]
  · beta_reduce
    rw [h3]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Mi *ᵥ w, by rw [← hMiM v, hw, Matrix.mulVec_smul]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨M *ᵥ w, Matrix.mulVec_smul _ _ _⟩
  · beta_reduce
    rw [h4]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨Mi *ᵥ v, by beta_reduce; rw [hMMi]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨M *ᵥ v, rfl⟩
  · have := h5 m (M *ᵥ v) (M *ᵥ w)
    rw [D.gPts_dot _ ν hν] at this
    have e : (2 : ℤ_[ℓ]) * ((ν : ℤ_[ℓ]) * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w))) =
        (ν : ℤ_[ℓ]) * (2 * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w))) := by ring
    rw [e] at this
    exact this

def Obj.tateLPre (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] : (Over S)ᵒᵖ ⥤ Type where
  obj T := {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}
  map u := ↾fun z => ⟨fun m v => u.unop ≫ z.1 m v, z.2.comp u.unop⟩
  map_id T := by
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}) : 3
    apply Subtype.ext
    funext m v
    exact Category.id_comp _
  map_comp {T₁ T₂ T₃} u u' := by
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T₁.unop ⟶ o.A) // o.IsTateL ℓ T₁.unop ev}) : 3
    apply Subtype.ext
    funext m v
    exact Category.assoc _ _ _

def Obj.tateL (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] : GlobalTheory.Et.Rel.RActPre S (D.gPts ℤ_[ℓ]) where
  P := o.tateLPre ℓ
  act g :=
    { app := fun T => ↾fun z => ⟨fun m v => z.1 m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v), z.2.smul g⟩
      naturality := fun _ _ _ => rfl }
  act_one := by
    apply NatTrans.ext
    funext T
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}) : 3
    apply Subtype.ext
    funext m v
    change z.1 m (((1 : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v) = z.1 m v
    rw [Units.val_one, Matrix.one_mulVec]
  act_mul g h := by
    apply NatTrans.ext
    funext T
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}) : 3
    apply Subtype.ext
    funext m v
    change z.1 m (((g * h : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v) =
      z.1 m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ (((h : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v))
    rw [Units.val_mul, Matrix.mulVec_mulVec]

def Obj.xiSheaf (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p) (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) :
    GlobalTheory.Et.Rel.Shv E S :=
  GlobalTheory.Et.Rel.assoc E (o.tateL ℓ) ξ.toMonoidHom

def Datum.stdRep (D : Datum p) (ℓ : ℕ) [Fact ℓ.Prime] : D.gPts ℤ_[ℓ] →ₜ* GL D.Ix ℤ_[ℓ] where
  toMonoidHom := (D.gPts ℤ_[ℓ]).subtype
  continuous_toFun := continuous_subtype_val

def RepFam.xiSheaf (F₀ : RepFam b N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) :
    GlobalTheory.Et.Rel.Shv E F₀.X :=
  F₀.univ.xiSheaf ℓ hℓ E ξ

end GlobalTheory.UPel.HT

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {w : Ideal (NumberField.RingOfIntegers D.F)} {m : ℕ} {e : D.O}

def LevRep.xiSheaf (M : LevRep b N w m e) (F₀ : RepFam b N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (E : Type) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ]
    (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) : GlobalTheory.Et.Rel.Shv E M.X :=
  (GlobalTheory.Et.Rel.res E (M.forget F₀)).obj (F₀.xiSheaf ℓ hℓ E ξ)

end GlobalTheory.DrinLev.HT

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.gPtsZQ (D : Datum p) (ℓ : ℕ) [Fact ℓ.Prime] : D.gPts ℤ_[ℓ] →ₜ* D.gPts ℚ_[ℓ] where
  toMonoidHom := D.gPtsMap (PadicInt.Coe.ringHom : ℤ_[ℓ] →+* ℚ_[ℓ])
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map continuous_subtype_val
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map continuous_subtype_val

section Examples

variable (D : Datum p) (ℓ : ℕ) [Fact ℓ.Prime]

example : IsTopologicalGroup (D.gPts ℤ_[ℓ]) := inferInstance

example (Λ : Type) [CommRing Λ] : (-1 : GL D.Ix Λ) ∈ D.gPts Λ :=
  ⟨fun c => by simp, ⟨1, by simp⟩⟩

example (g : D.gPts ℤ_[ℓ]) : D.stdRep ℓ g = g := rfl

example (X : Scheme.{0}) (T : Over X) :
    GlobalTheory.Et.Rel.assocSet ℤ_[ℓ] (GlobalTheory.Et.Rel.trivTorsor X (D.gPts ℤ_[ℓ])) (D.stdRep ℓ).toMonoidHom T ≃ₗ[ℤ_[ℓ]]
      C(T.left, D.Ix → ℤ_[ℓ]) :=
  GlobalTheory.Et.Rel.assocTrivEquiv _ (D.stdRep ℓ).continuous T

example {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s)
    (g : D.gPts ℤ_[ℓ]) (T : Over S) (z : (o.tateL ℓ).P.obj (Opposite.op T)) (m : ℕ) (v : D.Ix → ℤ_[ℓ]) :
    (((o.tateL ℓ).act g).app _ z).1 m v = z.1 m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v) := rfl

end Examples

end GlobalTheory.UPel.HT
end
end
