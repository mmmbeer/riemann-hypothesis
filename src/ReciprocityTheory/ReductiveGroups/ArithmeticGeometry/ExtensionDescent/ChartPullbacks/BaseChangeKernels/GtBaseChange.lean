import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PreLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.TransPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

abbrev cmap {κ X A : Type} [AddCommGroup X] [CommRing A] (b : Module.Basis κ ℤ X) (v : κ → Aˣ) :
    Multiplicative X →* A :=
  (Units.coeHom A).comp (AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)

theorem cmap_comp {κ X A A' : Type} [AddCommGroup X] [CommRing A] [CommRing A']
    (b : Module.Basis κ ℤ X) (ρ : A →+* A') (v : κ → Aˣ) (v' : κ → A'ˣ)
    (hv : ∀ k, (v' k).val = ρ (v k).val) (x : Multiplicative X) :
    cmap b v' x = ρ (cmap b v x) := by
  have hlin : b.constr ℤ (fun k => Additive.ofMul (v' k)) =
      (MonoidHom.toAdditive (Units.map (ρ : A →* A'))).toIntLinearMap ∘ₗ
        b.constr ℤ (fun k => Additive.ofMul (v k)) := by
    refine b.ext (fun k => ?_)
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    show Additive.ofMul (v' k) = Additive.ofMul (Units.map (ρ : A →* A') (v k))
    congr 1
    exact Units.ext (by simpa using hv k)
  have hx := congrArg (fun f => ((Additive.toMul (f (Multiplicative.toAdd x)) : A'ˣ) : A')) hlin
  first
  | exact hx
  | simpa using hx

open ReciprocityTheory.ChartRestriction.G.Semi in
theorem appLE_res {X Y : Scheme.{0}} (g : Y ⟶ X) {U U₀ : X.Opens} (hU : U ≤ U₀) {V W : Y.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U₀) (hVW : V ≤ W) (u : Γ(X, U₀)ˣ) :
    (res hVW (res hW (pullU g U₀ u))).val = (g.appLE U V hV).hom (res hU u).val := by
  have key : g.app U₀ ≫ Y.presheaf.map (homOfLE hW).op ≫ Y.presheaf.map (homOfLE hVW).op =
      X.presheaf.map (homOfLE hU).op ≫ g.appLE U V hV := by
    rw [Scheme.Hom.map_appLE, ← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 := congrArg (fun f => f.hom u.val) key
  first
  | exact h2
  | simpa [res, pullU] using h2

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

def AffineBCSt : Prop :=
  ∀ {G B G' B' : Scheme.{0}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B},
    IsPullback g q' q b → IsAffineHom q → ∀ {X : Type} [AddCommMonoid X]
    {V : B.Opens}, IsAffineOpen V → ∀ {V' : B'.Opens}, IsAffineOpen V' →
    V' ≤ b ⁻¹ᵁ V → ∀ (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V')),
    (∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _))

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

section
set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

theorem affineBCSt : AffineBCSt := by
  intro G B G' B' g q' q b sq hq X _ V hV V' hV' hle hleG φ φ' hφ' hφ
  exact coord_affineBC sq hq hV hV' hle hleG φ φ' hφ' hφ

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

namespace GluingInclusion

variable {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
  (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))

abbrev cm (V : B.Opens) (h : V ≤ W) : AddMonoidAlgebra Γ(B, V) X →+* Γ(G, q ⁻¹ᵁ V) :=
  AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)

omit [AddCommMonoid X] in
lemma app_res {V₁ V₂ : B.Opens} (h : V₁ ≤ V₂) (c : Γ(B, V₂)) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom ((q.app V₂).hom c) =
      (q.app V₁).hom ((B.presheaf.map (homOfLE h).op).hom c) := by
  have h2 := congrArg (fun f => f.hom c) (q.naturality (homOfLE h).op)
  first
  | exact h2.symm
  | simpa using h2.symm

lemma res_res {Y : Scheme.{0}} {U₁ U₂ U₃ : Y.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (s : Γ(Y, U₃)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom s) =
      (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  have h2 := congrArg (fun f => f.hom s) (Y.presheaf.map_comp (homOfLE h₂).op (homOfLE h₁).op)
  first
  | exact h2.symm
  | simpa using h2.symm

variable (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (x : Multiplicative X),
    φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))

include hnat in
lemma cm_nat {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) :
    (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom.comp (cm q φ V₂ h₂) =
      (cm q φ V₁ h₁).comp (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp [AddMonoidAlgebra.liftNC_single, app_res]
  · intro x
    simp [AddMonoidAlgebra.liftNC_single, hnat V₁ V₂ h₁ h₂ h]

include hnat in
lemma cm_nat_apply {V₁ V₂ : B.Opens} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂)
    (p : AddMonoidAlgebra Γ(B, V₂) X) :
    cm q φ V₁ h₁ (AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE h).op).hom p) =
      (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (cm q φ V₂ h₂ p) := (congrArg (fun f => f p) (cm_nat q φ hnat h₁ h₂ h)).symm

include hnat in

lemma inj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} (U : ι → B.Opens) (hU : ∀ i, U i ≤ V)
    (hcov : V ≤ iSup U) (hinj : ∀ i, Function.Injective (cm q φ (U i) ((hU i).trans h))) :
    Function.Injective (cm q φ V h) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom p = 0 := by
    intro i
    apply hinj i
    rw [cm_nat_apply q φ hnat ((hU i).trans h) h (hU i), hp, map_zero, map_zero]
  ext x
  apply B.sheaf.eq_of_locally_eq' U V (fun i => homOfLE (hU i)) hcov
  intro i
  have h2 := congrArg (fun r => r.coeff x) (h1 i)
  have h3 : (B.presheaf.map (homOfLE (hU i)).op).hom (p.coeff x) = 0 := by simpa using h2
  refine h3.trans ?_
  exact (map_zero _).symm

include hnat in

lemma surj_of_cover {V : B.Opens} (h : V ≤ W) {ι : Type} [Finite ι] (U : ι → B.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ iSup U)
    (hsurj : ∀ i, Function.Surjective (cm q φ (U i) ((hU i).trans h)))
    (hinj2 : ∀ i j, Function.Injective (cm q φ (U i ⊓ U j) (inf_le_left.trans ((hU i).trans h)))) :
    Function.Surjective (cm q φ V h) := by
  classical
  intro s
  haveI := Fintype.ofFinite ι
  have hloc : ∀ i, ∃ p : AddMonoidAlgebra Γ(B, U i) X, cm q φ (U i) ((hU i).trans h) p =
      (G.presheaf.map (homOfLE (q.preimage_mono (hU i))).op).hom s := fun i => hsurj i _
  choose p hp using hloc
  have hcompat : ∀ i j,
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (p i) =
      AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (p j) := by
    intro i j
    apply hinj2 i j
    rw [cm_nat_apply q φ hnat _ ((hU i).trans h) inf_le_left,
      cm_nat_apply q φ hnat _ ((hU j).trans h) inf_le_right, hp i, hp j, res_res, res_res]
  have hcx : ∀ x : X, TopCat.Presheaf.IsCompatible B.sheaf.1 U (fun i => (p i).coeff x) := by
    intro x i j
    have e := congrArg (fun r => r.coeff x) (hcompat i j)
    simp only [AddMonoidAlgebra.coeff_mapRingHom] at e
    exact e
  have hglue : ∀ x : X, ∃ c : Γ(B, V), ∀ i, (B.presheaf.map (homOfLE (hU i)).op).hom c = (p i).coeff x := by
    intro x
    obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' B.sheaf U V (fun i => homOfLE (hU i)) hcov
      (fun i => (p i).coeff x) (hcx x)
    exact ⟨c, hc⟩
  choose c hc using hglue
  let S : Finset X := Finset.univ.biUnion (fun i => (p i).coeff.support)
  let F : X →₀ Γ(B, V) := ∑ x ∈ S, Finsupp.single x (c x)
  have hF : ∀ x, F x = if x ∈ S then c x else 0 := by
    intro x
    simp [F, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hres : ∀ i, AddMonoidAlgebra.mapRingHom X (B.presheaf.map (homOfLE (hU i)).op).hom
      (AddMonoidAlgebra.ofCoeff F) = p i := by
    intro i
    apply AddMonoidAlgebra.coeff_injective
    ext x
    rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_ofCoeff, hF]
    split_ifs with hx
    · exact hc x i
    · rw [map_zero]
      symm
      by_contra hne
      exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hne⟩)
  refine ⟨AddMonoidAlgebra.ofCoeff F, ?_⟩
  have hcovG : q ⁻¹ᵁ V ≤ iSup (fun i => q ⁻¹ᵁ U i) := by
    have e := q.preimage_mono hcov
    rw [Scheme.Hom.preimage_iSup] at e
    exact e
  apply TopCat.Sheaf.eq_of_locally_eq' G.sheaf (fun i => q ⁻¹ᵁ U i) (q ⁻¹ᵁ V)
    (fun i => homOfLE (q.preimage_mono (hU i))) hcovG
  intro i
  have e1 := cm_nat_apply q φ hnat ((hU i).trans h) h (hU i) (AddMonoidAlgebra.ofCoeff F)
  rw [hres i, hp i] at e1
  exact e1.symm

end GluingInclusion

open GluingInclusion in

theorem coord_glue {G B : Scheme.{0}} (q : G ⟶ B) {X : Type} [AddCommMonoid X] {W : B.Opens}
    (φ : ∀ V : B.Opens, V ≤ W → (Multiplicative X →* Γ(G, q ⁻¹ᵁ V)))
    (hnat : ∀ (V₁ V₂ : B.Opens) (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : V₁ ≤ V₂) (x : Multiplicative X),
      φ V₁ h₁ x = (G.presheaf.map (homOfLE (q.preimage_mono h)).op).hom (φ V₂ h₂ x))
    (hgood : ∀ x ∈ W, ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, x ∈ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀),
      IsAffineOpen V₁ → Function.Bijective
        (AddMonoidAlgebra.liftNCRingHom (q.app V₁).hom (φ V₁ (h₁.trans hV₀))
          (fun _ _ => Commute.all _ _)))
    (V : B.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom (φ V h) (fun _ _ => Commute.all _ _)) := by
  classical
  have hbasis := AlgebraicGeometry.Scheme.isBasis_affineOpens B
  have hloc : ∀ x ∈ W, ∀ O : B.Opens, x ∈ O → ∃ A : B.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ O ∧
      ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ →
        Function.Bijective (cm q φ V₁ (h₁.trans hV₀)) := by
    intro x hx O hxO
    obtain ⟨V₀, hV₀, hxV₀, hb⟩ := hgood x hx
    obtain ⟨A, hA, hxA, hAle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis) (show x ∈ O ⊓ V₀ from ⟨hxO, hxV₀⟩)
    exact ⟨A, hA, hxA, hAle.trans inf_le_left, V₀, hV₀, hAle.trans inf_le_right, hb⟩
  have hinj : ∀ (O : B.Opens) (hO : O ≤ W), Function.Injective (cm q φ O hO) := by
    intro O hO
    let ι := {A : B.Opens // IsAffineOpen A ∧ A ≤ O ∧ ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧
      ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ → Function.Bijective (cm q φ V₁ (h₁.trans hV₀))}
    refine inj_of_cover q φ hnat hO (fun a : ι => a.1) (fun a => a.2.2.1) ?_ ?_
    · intro x hx
      obtain ⟨A, hA, hxA, hAO, rest⟩ := hloc x (hO hx) O hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨A, hA, hAO, rest⟩, hxA⟩
    · intro a
      obtain ⟨V₀, hV₀, hAV₀, hb⟩ := a.2.2.2
      exact (hb a.1 hAV₀ a.2.1).1
  constructor
  · exact hinj V h
  · have hx : ∀ x ∈ V, ∃ A : B.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ V ∧
        ∃ V₀ : B.Opens, ∃ hV₀ : V₀ ≤ W, A ≤ V₀ ∧ ∀ (V₁ : B.Opens) (h₁ : V₁ ≤ V₀), IsAffineOpen V₁ →
          Function.Bijective (cm q φ V₁ (h₁.trans hV₀)) := fun x hxV => hloc x (h hxV) V hxV
    choose A hA using hx
    obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (A x.1 x.2 : Set B))
      (fun x => (A x.1 x.2).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hA y hy).2.1⟩)
    refine surj_of_cover q φ hnat h (fun i : t => A i.1.1 i.1.2) (fun i => (hA _ _).2.2.1) ?_ ?_
      (fun i j => hinj _ _)
    · intro y hy
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
    · intro i
      obtain ⟨V₀, hV₀, hAV₀, hb⟩ := (hA _ _).2.2.2
      exact (hb _ hAV₀ (hA _ _).1).2

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

private lemma app_res_app_res_lemma {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (O : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hO : O ≤ f ⁻¹ᵁ V) (hO' : O ≤ (f ≫ g) ⁻¹ᵁ U) :
    g.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ f.app V ≫ X.presheaf.map (homOfLE hO).op =
      (f ≫ g).app U ≫ X.presheaf.map (homOfLE hO').op := by
  first
    | rw [Scheme.Hom.naturality_assoc]
    | rw [← Scheme.Hom.naturality_assoc]
  rw [← Functor.map_comp, ← Category.assoc]
  rfl

private lemma res_app_res_lemma_2 {X Y : Scheme.{0}} (f : X ⟶ Y) (V₁ V : Y.Opens) (O : X.Opens)
    (hV : V₁ ≤ V) (hO : O ≤ f ⁻¹ᵁ V₁) (hO' : O ≤ f ⁻¹ᵁ V) :
    Y.presheaf.map (homOfLE hV).op ≫ f.app V₁ ≫ X.presheaf.map (homOfLE hO).op =
      f.app V ≫ X.presheaf.map (homOfLE hO').op := by
  first
    | rw [Scheme.Hom.naturality_assoc]
    | rw [← Scheme.Hom.naturality_assoc]
  rw [← Functor.map_comp]
  rfl

theorem unit_norm_pull {S₁ S₂ Y Z : Scheme.{0}} (e₁ : S₁ ⟶ Y) (e₂ : S₂ ⟶ Z) (a : Z ⟶ Y) (ff : S₂ ⟶ S₁)
    (he : e₂ ≫ a = ff ≫ e₁) {W : Y.Opens} (u : Γ(Y, W)ˣ) {W' : Z.Opens} (hW' : W' ≤ a ⁻¹ᵁ W)
    {V : S₁.Opens} (r : Γ(S₁, V)ˣ) {V' : S₂.Opens} (hV' : V' ≤ ff ⁻¹ᵁ V)
    (h : res (inf_le_left : e₁ ⁻¹ᵁ W ⊓ V ≤ e₁ ⁻¹ᵁ W) (pullU e₁ W u) *
      res (inf_le_right : e₁ ⁻¹ᵁ W ⊓ V ≤ V) r = 1) :
    res (inf_le_left : e₂ ⁻¹ᵁ W' ⊓ V' ≤ e₂ ⁻¹ᵁ W') (pullU e₂ W' (res hW' (pullU a W u))) *
      res (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V') (res hV' (pullU ff V r)) = 1 := by
  have p1 : e₂ ⁻¹ᵁ W' ⊓ V' ≤ (e₂ ≫ a) ⁻¹ᵁ W :=
    inf_le_left.trans ((TopologicalSpace.Opens.map e₂.base).map (homOfLE hW')).le
  have p2 : e₂ ⁻¹ᵁ W' ⊓ V' ≤ (ff ≫ e₁) ⁻¹ᵁ W := by rw [← he]; exact p1
  have hq : e₂ ⁻¹ᵁ W' ⊓ V' ≤ ff ⁻¹ᵁ V :=
    inf_le_right.trans hV'
  have hO : e₂ ⁻¹ᵁ W' ⊓ V' ≤ ff ⁻¹ᵁ (e₁ ⁻¹ᵁ W ⊓ V) := by
    show _ ≤ ff ⁻¹ᵁ (e₁ ⁻¹ᵁ W) ⊓ ff ⁻¹ᵁ V
    exact le_inf p2 hq
  have hC : ∀ (g₁ g₂ : S₂ ⟶ Y) (_ : g₁ = g₂) (p : e₂ ⁻¹ᵁ W' ⊓ V' ≤ g₁ ⁻¹ᵁ W)
      (q : e₂ ⁻¹ᵁ W' ⊓ V' ≤ g₂ ⁻¹ᵁ W),
      g₁.app W ≫ S₂.presheaf.map (homOfLE p).op = g₂.app W ≫ S₂.presheaf.map (homOfLE q).op := by
    intro g₁ g₂ hg p q
    subst hg
    rfl
  have hA := app_res_app_res_lemma e₂ a W W' (e₂ ⁻¹ᵁ W' ⊓ V') hW' inf_le_left p1
  have hB := app_res_app_res_lemma ff e₁ W (e₁ ⁻¹ᵁ W ⊓ V) (e₂ ⁻¹ᵁ W' ⊓ V') inf_le_left hO p2
  have hAB := hA.trans ((hC _ _ he p1 p2).trans hB.symm)
  have hD := res_app_res_lemma_2 ff (e₁ ⁻¹ᵁ W ⊓ V) V (e₂ ⁻¹ᵁ W' ⊓ V') inf_le_right hO hq
  have hE : ff.app V ≫ S₂.presheaf.map (homOfLE hV').op ≫
      S₂.presheaf.map (homOfLE (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V')).op =
      ff.app V ≫ S₂.presheaf.map (homOfLE hq).op := by
    rw [← Functor.map_comp]
    rfl
  have key := congrArg (fun t => res hO (pullU ff _ t)) h
  simp only [map_mul, map_one] at key
  refine Eq.trans ?_ key
  congr 1
  · ext
    have hu := congrArg (fun φ => φ.hom (u : Γ(Y, W))) hAB
    simpa [res, pullU] using hu
  · ext
    have hr := congrArg (fun φ => φ.hom (r : Γ(S₁, V))) (hE.trans hD.symm)
    simpa [res, pullU] using hr

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

attribute [local instance] SplitExt.free SplitExt.finite

variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

theorem unit_normB (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X) :
    res (inf_le_left : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j))
        (pullU (eSec ((Over.pullback f).obj G)) _ (uB f E d j k)) *
      res (inf_le_right : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k))
        (((pullExt f E).O ((pullExt f E).basis k)).rig.s (fun _ => j k)) = 1 := by
  have hmB : (mB f E).e = f := rfl
  have he : eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f = (mB f E).e ≫ eSec G := by
    rw [hmB]
    simp [eSec]
    refine (pullback.lift_fst _ _ _).trans ?_
    simpa using (pullback.condition_assoc (f := 𝟙 S) (g := f) η[G].left)
  exact unit_norm_pull (eSec G) (eSec ((Over.pullback f).obj G)) (pullback.fst G.hom f) (mB f E).e he
    (d.u (jj f E j) k) (pre_le f E d j) ((E.O (E.basis k)).rig.s (fun _ => jj f E j k))
    (rigPull_le (mB f E).F (mB f E).e (mB f E).e_comm (E.O (E.basis k)).L (fun _ => j k))
    (d.unit_norm (jj f E j) k)

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

section General

theorem gmRP {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U)
    (hz : z ∈ V) (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u :=
  (gm_res (𝟙 Z) z hle hz _).trans ((gm_pull (𝟙 Z) a z U (hle hz) u).trans (by rw [Category.id_comp]))

theorem act_le_of_hom {S : Scheme.{0}} {B G T : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
    [IsMonHom q] (i : T ⟶ G) (hk : i ≫ q = toUnit _ ≫ η[B]) (U : B.left.Opens) :
    (snd T G).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) ≤
      (lift (fst T G ≫ i) (snd T G) ≫ μ[G]).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
  have e : (lift (fst T G ≫ i) (snd T G) ≫ μ[G]) ≫ q = snd T G ≫ q := by
    rw [← Hom.mul_def, MonObj.mul_comp, Category.assoc, hk, ← Hom.one_def, MonObj.comp_one,
      _root_.one_mul]
  have e' : (lift (fst T G ≫ i) (snd T G) ≫ μ[G]).left ≫ q.left = (snd T G).left ≫ q.left := by
    rw [← Over.comp_left, e, Over.comp_left]
  intro y hy
  have e₁ := congrArg (fun g => g y) e'
  simp only [Scheme.Hom.comp_apply] at e₁
  exact (congrArg (· ∈ U) e₁).mpr hy

theorem equivPullL {T₁ T₂ Y Z P₁ P₂ : Scheme.{0}} (act₁ s₁ : P₁ ⟶ Y) (f₁ : P₁ ⟶ T₁)
    (act₂ s₂ : P₂ ⟶ Z) (f₂ : P₂ ⟶ T₂) (b : P₂ ⟶ P₁) (a : Z ⟶ Y) (h : T₂ ⟶ T₁)
    (W : Y.Opens) (u : Γ(Y, W)ˣ) (W' : Z.Opens) (hW' : W' ≤ a ⁻¹ᵁ W)
    (c : Γ(T₁, ⊤)ˣ) (c' : Γ(T₂, ⊤)ˣ)
    (hc : res (fun _ _ => trivial : (⊤ : T₂.Opens) ≤ h ⁻¹ᵁ ⊤) (pullU h ⊤ c) = c')
    (le₁ : s₁ ⁻¹ᵁ W ≤ act₁ ⁻¹ᵁ W) (t₁ : s₁ ⁻¹ᵁ W ≤ f₁ ⁻¹ᵁ ⊤)
    (H : res le₁ (pullU act₁ W u) = res t₁ (pullU f₁ ⊤ c) * pullU s₁ W u)
    (ha : act₂ ≫ a = b ≫ act₁) (hs : s₂ ≫ a = b ≫ s₁) (hf : f₂ ≫ h = b ≫ f₁)
    (le₂ : s₂ ⁻¹ᵁ W' ≤ act₂ ⁻¹ᵁ W') (t₂ : s₂ ⁻¹ᵁ W' ≤ f₂ ⁻¹ᵁ ⊤) :
    res le₂ (pullU act₂ W' (res hW' (pullU a W u))) =
      res t₂ (pullU f₂ ⊤ c') * pullU s₂ W' (res hW' (pullU a W u)) := by
  refine unit_ext fun y hy => ?_
  have hsy : s₂ y ∈ W' := hy
  have hby : b y ∈ s₁ ⁻¹ᵁ W := by
    have e₁ := congrArg (fun g => g y) hs
    simp only [Scheme.Hom.comp_apply] at e₁
    show s₁ (b y) ∈ W
    rw [← e₁]
    exact hW' hsy
  have hay : act₂ y ∈ W' := le₂ hy
  have o := congrArg (gm b y (s₁ ⁻¹ᵁ W)) H
  rw [map_mul, gm_res b y _ hby, gm_res b y _ hby, gm_pull b act₁ y W (le₁ hby),
    gm_pull b f₁ y ⊤ trivial, gm_pull b s₁ y W hby, ← ha, ← hs, ← hf] at o
  have e3 : gm f₂ y ⊤ c' = gm (f₂ ≫ h) y ⊤ c := by
    subst hc
    refine (gm_res f₂ y (V := ⊤) (U := h ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans ?_
    exact gm_pull f₂ h y ⊤ trivial c
  rw [map_mul, gmRP act₂ y W' _ le₂ hy, gmRP f₂ y ⊤ _ t₂ hy,
    gm_res act₂ y hW' hay, gm_pull act₂ a y W (hW' hay), e3]
  have e2 : gm (𝟙 P₂) y (s₂ ⁻¹ᵁ W') (pullU s₂ W' (res hW' (pullU a W u))) =
      gm (s₂ ≫ a) y W u := by
    rw [gm_pull (𝟙 P₂) s₂ y W' hsy, Category.id_comp, gm_res s₂ y hW' hsy,
      gm_pull s₂ a y W (hW' hsy)]
  rw [e2]
  exact o

end General

section Torus

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]

theorem charUnit_hTB (χ : X) :
    res (fun _ _ => trivial : (⊤ : (splitTorus S' X).left.Opens) ≤ hT f X ⁻¹ᵁ ⊤)
      (pullU (hT f X) ⊤ (charUnit S X χ)) = charUnit S' X χ := by
  let w := Units.map (Scheme.ΓSpecIso (torusRing ZU X)).inv.hom.toMonoidHom
    (Units.map (AddMonoidAlgebra.of ZU X) (toUnits (Multiplicative.ofAdd χ)))
  refine unit_ext fun x _ => ?_
  have e3 : hT f X ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) =
      pullback.fst (splitTorusAff ZU X).hom (toZ S') := pullback.lift_fst _ _ _
  have e1 : gm (𝟙 _) x ⊤ (charUnit S' X χ) =
      gm (pullback.fst (splitTorusAff ZU X).hom (toZ S')) x ⊤ w :=
    gmRP (pullback.fst (splitTorusAff ZU X).hom (toZ S')) x ⊤ ⊤ _ trivial w
  have e2 : gm (hT f X) x ⊤ (charUnit S X χ) =
      gm (hT f X ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S)) x ⊤ w :=
    (gm_res (hT f X) x (V := ⊤) (U := pullback.fst (splitTorusAff ZU X).hom (toZ S) ⁻¹ᵁ ⊤) _
      trivial _).trans (gm_pull _ _ x ⊤ trivial w)
  rw [e3] at e2
  exact (gmRP (hT f X) x ⊤ ⊤ _ trivial _).trans (e2.trans e1.symm)

end Torus

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] {G : Over S} [GrpObj G]

abbrev PQ : Over S := Over.mk ((splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f)

def uT : PQ f X (G := G) ⟶ splitTorus S X :=
  Over.homMk ((fst (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ hT f X) (by
    show _ ≫ _ ≫ (splitTorus S X).hom = (splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f
    rw [hT_snd, ← Category.assoc, Over.w (fst (splitTorus S' X) ((Over.pullback f).obj G))])

def vG : PQ f X (G := G) ⟶ G :=
  Over.homMk ((snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f) (by
    show _ ≫ _ ≫ G.hom = (splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd (splitTorus S' X) ((Over.pullback f).obj G))))

def bm : (splitTorus S' X ⊗ (Over.pullback f).obj G).left ⟶ (splitTorus S X ⊗ G).left :=
  (lift (uT f X) (vG f X)).left

lemma bm_snd : (snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f =
    bm f X ≫ (snd (splitTorus S X) G).left := by
  show _ = (lift (uT f X) (vG f X) ≫ snd _ _).left
  rw [lift_snd]
  rfl

lemma bm_fst : (fst (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ hT f X =
    bm f X ≫ (fst (splitTorus S X) G).left := by
  show _ = (lift (uT f X) (vG f X) ≫ fst _ _).left
  rw [lift_fst]
  rfl

lemma bm_act (i : splitTorus S X ⟶ G) :
    (lift (fst (splitTorus S' X) ((Over.pullback f).obj G) ≫ iB f X i)
        (snd (splitTorus S' X) ((Over.pullback f).obj G)) ≫ μ[(Over.pullback f).obj G]).left ≫
      pullback.fst G.hom f =
    bm f X ≫ (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left := by
  have hx : (lift (uT f X) (vG f X) ≫ fst (splitTorus S X) G ≫ i).left =
      (fst (splitTorus S' X) ((Over.pullback f).obj G) ≫ iB f X i).left ≫ pullback.fst G.hom f := by
    rw [← Category.assoc, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, iB_h]
    exact Category.assoc _ _ _
  have hy : (lift (uT f X) (vG f X) ≫ snd (splitTorus S X) G).left =
      (snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f := by
    rw [lift_snd]
    rfl
  have key := (isGrpPullback_pullback G f).2 _ _ _ _ _ hx hy
  rw [← Hom.mul_def, ← Hom.mul_def, ← key, ← MonObj.comp_mul]
  rfl

end Act

section Fields

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S) {G : Over S} [GrpObj G] (d : E.GtDatum G)

theorem actB_le : ∀ j : (pullExt f E).ChartIdx,
    (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⁻¹ᵁ
        ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ≤
      (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
        μ[(Over.pullback f).obj G]).left ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) := by
  haveI := d.q_hom
  haveI : IsMonHom (qB f d.q) :=
    isMonHom_of_grpPullback (isGrpPullback_pullback G f) (isGrpPullback_pullback E.B f) d.q
      (qB f d.q) (qB_h f d.q)
  intro j
  exact act_le_of_hom (qB f d.q) (iB f E.X d.i) (iB_isKernel f E.X d.q d.i d.isKernel).w _

theorem equivB : ∀ (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X),
    res (actB_le f E d j)
        (pullU (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
            μ[(Over.pullback f).obj G]).left _ (uB f E d j k)) =
      res (fun x _ => show (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left.base x ∈
          (⊤ : TopologicalSpace.Opens _) from trivial)
          (pullU (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⊤
            (charUnit S' (pullExt f E).X ((pullExt f E).basis k))) *
        pullU (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left _ (uB f E d j k) := by
  intro j k
  exact equivPullL (act₁ := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left)
    (s₁ := (snd (splitTorus S E.X) G).left) (f₁ := (fst (splitTorus S E.X) G).left)
    (act₂ := (lift (fst (splitTorus S' E.X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' E.X) ((Over.pullback f).obj G)) ≫ μ[(Over.pullback f).obj G]).left)
    (s₂ := (snd (splitTorus S' E.X) ((Over.pullback f).obj G)).left)
    (f₂ := (fst (splitTorus S' E.X) ((Over.pullback f).obj G)).left)
    (b := bm f E.X) (a := pullback.fst G.hom f) (h := hT f E.X)
    (W := d.q.left ⁻¹ᵁ E.chart (jj f E j)) (u := d.u (jj f E j) k)
    (W' := (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) (hW' := pre_le f E d j)
    (c := charUnit S E.X (E.basis k)) (c' := charUnit S' E.X (E.basis k))
    (hc := charUnit_hTB f E.X (E.basis k))
    (le₁ := d.act_le (jj f E j)) (t₁ := fun x _ => trivial)
    (H := d.equiv (jj f E j) k)
    (ha := bm_act f E.X d.i) (hs := bm_snd f E.X) (hf := bm_fst f E.X)
    (le₂ := actB_le f E d j) (t₂ := fun x _ => trivial)

end Fields

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

lemma res_val_res {X : Scheme.{0}} {U V₁ V₂ : X.Opens} (h₁ : V₁ ≤ U) (h₂ : V₂ ≤ U) (h : V₁ ≤ V₂)
    (u : Γ(X, U)ˣ) :
    (res h₁ u).val = (X.presheaf.map (homOfLE h).op).hom (res h₂ u).val := by
  show (X.presheaf.map (homOfLE h₁).op).hom u.val =
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE h₂).op).hom u.val)
  have e : (homOfLE h₁).op = (homOfLE h₂).op ≫ (homOfLE h).op := by
    first
    | rfl
    | exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [e, Functor.map_comp]
  rfl

section Datum

variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

lemma hleG (j : (pullExt f E).ChartIdx) {V : E.B.left.Opens} {V₁ : ((Over.pullback f).obj E.B).left.Opens}
    (h₁ : V₁ ≤ pullback.fst E.B.hom f ⁻¹ᵁ V) :
    (qB f d.q).left ⁻¹ᵁ V₁ ≤ pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ V) := by
  have key : ((qB f d.q).left ≫ pullback.fst E.B.hom f) ⁻¹ᵁ V
      = (pullback.fst G.hom f ≫ d.q.left) ⁻¹ᵁ V := by
    first
    | rw [qB_h]
    | exact congrArg (fun g => g ⁻¹ᵁ V) (qB_h f d.q)
  calc (qB f d.q).left ⁻¹ᵁ V₁ ≤ (qB f d.q).left ⁻¹ᵁ (pullback.fst E.B.hom f ⁻¹ᵁ V) :=
        (qB f d.q).left.preimage_mono h₁
    _ = ((qB f d.q).left ≫ pullback.fst E.B.hom f) ⁻¹ᵁ V := by
        first
        | rfl
        | exact (Scheme.preimage_comp _ _ _).symm
    _ = (pullback.fst G.hom f ≫ d.q.left) ⁻¹ᵁ V := key
    _ = pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ V) := by
        first
        | rfl
        | exact Scheme.preimage_comp _ _ _

set_option maxHeartbeats 800000 in

def datum : (pullExt f E).GtDatum ((Over.pullback f).obj G) where
  q := qB f d.q
  i := iB f E.X d.i
  q_hom := by
    haveI := d.q_hom
    exact isMonHom_of_grpPullback (isGrpPullback_pullback G f) (isGrpPullback_pullback E.B f) d.q
      (qB f d.q) (qB_h f d.q)
  i_hom := by
    haveI := d.i_hom
    exact iB_hom f E.X d.i
  q_flat := qB_flat f d.q d.q_flat
  q_surjective := qB_surj f d.q d.q_surjective
  q_affine := qB_affine f d.q d.q_affine
  isKernel := iB_isKernel f E.X d.q d.i d.isKernel
  u := uB f E d
  coord := fun j V hV h => by
    refine coord_glue (qB f d.q).left (W := (pullExt f E).chart j)
      (fun V' h' => cmap (pullExt f E).basis
        (fun k => res ((qB f d.q).left.preimage_mono h') (uB f E d j k)))
      (fun V₁ V₂ h₁ h₂ h x => cmap_comp _ _ _ _ (fun k => res_val_res _ _ _ _) x) ?_ V hV h
    intro x hx
    have hFx : pullback.fst E.B.hom f x ∈ E.chart (jj f E j) := chart_le f E j hx
    obtain ⟨V, hVa, hxV, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 E.B.left.isBasis_affineOpens hFx
    refine ⟨(pullExt f E).chart j ⊓ pullback.fst E.B.hom f ⁻¹ᵁ V, inf_le_left, ⟨hx, hxV⟩,
      fun V₁ h₁ hV₁ => ?_⟩
    exact affineBCSt (qB_sq f d.q) d.q_affine hVa hV₁ (h₁.trans inf_le_right)
      (hleG f E d j (h₁.trans inf_le_right))
      (cmap E.basis (fun k => res (d.q.left.preimage_mono hVle) (d.u (jj f E j) k))) _
      (fun y => cmap_comp _ _ _ _ (fun k => appLE_res _ _ _ _ _ _) y) (d.coord (jj f E j) V hVa hVle)
  trans := fun j j' k => trans_pull (pullback.fst G.hom f) d.q.left (qB f d.q).left
    (pullback.fst E.B.hom f) (qB_h f d.q) (E.O (E.basis k)).L (j k PUnit.unit) (j' k PUnit.unit)
    (E.chart_le (jj f E j) k) (E.chart_le (jj f E j') k) ((pullExt f E).chart_le j k)
    ((pullExt f E).chart_le j' k) (d.u (jj f E j) k) (d.u (jj f E j') k)
    (d.trans (jj f E j) (jj f E j') k) (pre_le f E d j) (pre_le f E d j')
  act_le := actB_le f E d
  equiv := equivB f E d
  unit_norm := unit_normB f E d

end Datum

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V)
    (u : Γ(X, U)ˣ) : res h' (res h u) = res (h'.trans h) u := by
  ext
  exact (res_val_res (h'.trans h) h h' u).symm

private lemma gen_div_self_lemma_2 {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.div M M), t.IsGen := by
  refine ⟨⟨fun p => M.g p.1 p.2⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨c, d⟩
  try dsimp only [LB.div]
  have e1 := congrArg (res (show M.U a ⊓ M.U b ⊓ (M.U c ⊓ M.U d) ≤ M.U a ⊓ M.U c ⊓ M.U d from
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right))) (hM.cocycle a c d)
  have e2 := congrArg (res (show M.U a ⊓ M.U b ⊓ (M.U c ⊓ M.U d) ≤ M.U a ⊓ M.U b ⊓ M.U d from
    le_inf inf_le_left (inf_le_right.trans inf_le_right))) (hM.cocycle a b d)
  simp only [map_mul, res_res_lemma] at e1 e2
  have e3 := eq_mul_inv_of_mul_eq e2
  rw [← e1] at e3
  exact e3.trans (mul_right_comm _ _ _)

theorem gtBaseChange : GtBaseChangeSt := by
  intro S S' f E G _ hG
  obtain ⟨d⟩ := hG
  refine ⟨pullExt f E, AddEquiv.refl _, Iso.refl _, ?_, fun χ => ?_, Nonempty.intro (datum f E d)⟩
  · first
    | exact (inferInstance : IsMonHom (𝟙 ((Over.pullback f).obj E.B)))
    | (rw [Iso.refl_hom]; infer_instance)
    | (constructor <;> simp <;> rfl)
  · show ∃ w : LB.Iso ((E.O χ).L.pull (𝟙 (pullback E.B.hom f) ≫ pullback.fst E.B.hom f))
        ((E.O χ).L.pull (mB f E).F), w.IsGen
    rw [mB_F, Category.id_comp]
    exact gen_div_self_lemma_2 _ (LB.isLB_pull (E.O χ).isLB _)

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
end
end
