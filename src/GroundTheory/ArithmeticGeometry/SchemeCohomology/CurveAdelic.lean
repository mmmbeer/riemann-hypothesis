import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL

section
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian TopologicalSpace

universe w' v u

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

instance freeSheafMap_mono {U V : C} (f : U ⟶ V) [Mono f] : Mono (freeSheafMap J f) := by
  have : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
    (mono_iff_injective _).2 (fun a b h => (cancel_mono f).1 h)
  have : Mono (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) :=
    NatTrans.mono_of_mono_app _
  exact (presheafToSheaf J AddCommGrpCat.{v}).map_mono _

theorem surjective_map_of_injective (I : Sheaf J AddCommGrpCat.{v}) [Injective I] {U V : C}
    (f : U ⟶ V) [Mono f] : Function.Surjective (I.obj.map f.op) := by
  intro s
  refine ⟨freeSheafHomAddEquiv V I
    (Injective.factorThru ((freeSheafHomAddEquiv U I).symm s) (freeSheafMap J f)), ?_⟩
  rw [← freeSheafHomAddEquiv_naturality_left, Injective.comp_factorThru,
    AddEquiv.apply_symm_apply]

end Site

section Space

variable {X : TopCat.{u}}

theorem isFlasque_of_injective (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [Injective I] : TopCat.Presheaf.IsFlasque I.obj where
  epi {U V} i := by
    have : Mono i.unop := ⟨fun _ _ _ => Subsingleton.elim _ _⟩
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_map_of_injective I i.unop

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

theorem ext_freeSheaf_eq_zero_of_isFlasque (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      [TopCat.Presheaf.IsFlasque F.obj] (U : Opens X)
      (x : Ext (freeSheaf (Opens.grothendieckTopology X) U) F (n + 1)), x = 0 := by
  induction n with
  | zero =>
    intro F _ U x
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    have : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque F.obj)
    have : TopCat.Presheaf.IsFlasque S.X₂.obj := isFlasque_of_injective (Injective.under F)
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ (freeSheaf _ U) hS x
      (by
        have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
        exact Ext.eq_zero_of_injective _) (zero_add 1)

    have hsurj : Function.Surjective (S.g.hom.app (op U)) :=
      (AddCommGrpCat.epi_iff_surjective _).1
        (TopCat.Sheaf.IsFlasque.epi_of_shortExact (X := X) (U := U) hS)
    obtain ⟨z, hz⟩ := hsurj (H'.equiv₀ S.X₃ U y)
    obtain ⟨w, rfl⟩ := (H'.equiv₀ S.X₂ U).surjective z
    have : y = (show Ext (freeSheaf _ U) S.X₂ 0 from w).comp (Ext.mk₀ S.g) (add_zero 0) := by
      apply (H'.equiv₀ S.X₃ U).injective
      rw [← hz, ← H'.equiv₀_naturality]
      rfl
    rw [this, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ n ih =>
    intro F _ U x
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    have : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque F.obj)
    have : TopCat.Presheaf.IsFlasque S.X₂.obj := isFlasque_of_injective (Injective.under F)
    have : TopCat.Presheaf.IsFlasque S.X₃.obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (X := X) hS
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ (freeSheaf _ U) hS x
      (by
        have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
        exact Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
    rw [ih S.X₃ U y, Ext.zero_comp]

theorem H'_eq_zero_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) (x : F.H' (n + 1) U) : x = 0 :=
  ext_freeSheaf_eq_zero_of_isFlasque n F U x

theorem H_eq_zero_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (x : Sheaf.H F (n + 1)) : x = 0 := by
  apply (cohomologyPresheafTerminalAddEquiv F (n + 1) (T := ⊤) isTerminalTop).symm.injective
  rw [map_zero]
  exact H'_eq_zero_of_isFlasque F n ⊤ _

instance subsingleton_H_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) : Subsingleton (Sheaf.H F (n + 1)) :=
  subsingleton_of_forall_eq 0 (H_eq_zero_of_isFlasque F n)

end Space

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

variable {X : Scheme.{u}}

section Local

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

def PrimeDivisor.divisorSubgroup (Z : PrimeDivisor X) (D : WeilDivisor X) :
    AddSubgroup X.functionField where
  carrier := {f | Z.valuation f ≤ WithZero.exp (D Z)}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    have hf' : Z.valuation f ≤ WithZero.exp (D Z) := hf
    have hg' : Z.valuation g ≤ WithZero.exp (D Z) := hg
    exact (Valuation.map_add _ _ _).trans (max_le hf' hg')
  neg_mem' {f} hf := by
    have hf' : Z.valuation f ≤ WithZero.exp (D Z) := hf
    change Z.valuation (-f) ≤ WithZero.exp (D Z)
    rwa [Valuation.map_neg]

lemma PrimeDivisor.mem_divisorSubgroup (Z : PrimeDivisor X) (D : WeilDivisor X)
    (f : X.functionField) : f ∈ Z.divisorSubgroup D ↔ Z.valuation f ≤ WithZero.exp (D Z) := by
  simp only [PrimeDivisor.divisorSubgroup, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]

open Classical in

noncomputable def pointSubgroup (D : WeilDivisor X) (x : X) : AddSubgroup X.functionField :=
  if h : ringKrullDim (X.presheaf.stalk x) = 1 then (PrimeDivisor.ofPoint x h).divisorSubgroup D
  else ⊤

lemma mem_pointSubgroup_iff (D : WeilDivisor X) (x : X) (f : X.functionField) :
    f ∈ pointSubgroup D x ↔ ∀ h : ringKrullDim (X.presheaf.stalk x) = 1,
      (PrimeDivisor.ofPoint x h).valuation f ≤ WithZero.exp (D (PrimeDivisor.ofPoint x h)) := by
  unfold pointSubgroup
  split_ifs with h
  · simp only [PrimeDivisor.mem_divisorSubgroup]
    exact ⟨fun hf _ => hf, fun hf => hf h⟩
  · exact ⟨fun _ h' => absurd h' h, fun _ => AddSubgroup.mem_top f⟩

lemma mem_pointSubgroup_primeDivisor (D : WeilDivisor X) (Z : PrimeDivisor X)
    (f : X.functionField) : f ∈ pointSubgroup D Z.point ↔ f ∈ Z.divisorSubgroup D := by
  rw [mem_pointSubgroup_iff, PrimeDivisor.mem_divisorSubgroup]
  exact ⟨fun hf => hf Z.2, fun hf _ => hf⟩

end Local

section Finite

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

lemma finite_not_mem_divisorSubgroup (D : WeilDivisor X)
    (f : X.functionField) : {Z : PrimeDivisor X | f ∉ Z.divisorSubgroup D}.Finite := by
  by_cases hf : f = 0
  · simp [hf]
  refine ((PrimeDivisor.finite_ord_ne_zero hf).union D.support.finite_toSet).subset ?_
  intro Z hZ
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe,
    Finsupp.mem_support_iff] at hc
  apply hZ
  rw [PrimeDivisor.mem_divisorSubgroup, PrimeDivisor.valuation_le_exp_iff Z hf, hc.1, hc.2]
  simp

end Finite

section Constant

variable [IsIntegral X]

def constPredicate : TopCat.LocalPredicate (X := X.carrier) (fun _ => X.functionField) where
  pred {V} f := ∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ ∀ z : V, z.1 ∈ W → f z = f y
  res {V W} i f h := by
    intro y
    obtain ⟨W', hyW', hW'⟩ := h (i y)
    exact ⟨W', hyW', fun z hz => hW' (i z) hz⟩
  locality {V} f w := by
    intro y
    obtain ⟨W, hyW, i, hW⟩ := w y
    obtain ⟨W', hyW', hW'⟩ := hW ⟨y.1, hyW⟩
    refine ⟨W ⊓ W', ⟨hyW, hyW'⟩, fun z hz => ?_⟩
    exact hW' ⟨z.1, hz.1⟩ hz.2

def constSections (V : X.Opens) : AddSubgroup (V → X.functionField) where
  carrier := {f | constPredicate.pred f}
  zero_mem' := fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩
  add_mem' {f g} hf hg := by
    intro y
    obtain ⟨W₁, hy₁, h₁⟩ := hf y
    obtain ⟨W₂, hy₂, h₂⟩ := hg y
    exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by simp only [Pi.add_apply, h₁ z hz.1, h₂ z hz.2]⟩
  neg_mem' {f} hf := by
    intro y
    obtain ⟨W, hyW, h⟩ := hf y
    exact ⟨W, hyW, fun z hz => by simp only [Pi.neg_apply, h z hz]⟩

lemma constSections_apply_eq {V : X.Opens} (t : constSections V) (y z : V) : t.1 y = t.1 z := by
  obtain ⟨Wy, hyW, hy⟩ := t.2 y
  obtain ⟨Wz, hzW, hz⟩ := t.2 z
  obtain ⟨w, hw⟩ := nonempty_preirreducible_inter (Wy ⊓ V).isOpen (Wz ⊓ V).isOpen
    ⟨y.1, hyW, y.2⟩ ⟨z.1, hzW, z.2⟩
  rw [← hy ⟨w, hw.1.2⟩ hw.1.1, hz ⟨w, hw.1.2⟩ hw.2.1]

def constSection (V : X.Opens) (c : X.functionField) : constSections V :=
  ⟨fun _ => c, fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩⟩

def constSectionsRes {V W : X.Opens} (h : W ≤ V) : constSections V →+ constSections W where
  toFun f := ⟨fun y => f.1 ⟨y.1, h y.2⟩, constPredicate.res (homOfLE h) f.1 f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (X) in

noncomputable def constPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (constSections V.unop)
  map i := AddCommGrpCat.ofHom (constSectionsRes i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

variable (X) in

theorem constPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (X := X.carrier) (constPresheaf X) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (constPredicate (X := X)))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

variable (X) in

noncomputable def constSheaf : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  ⟨constPresheaf X, constPresheaf_isSheaf X⟩

instance : TopCat.Presheaf.IsFlasque (constSheaf X).obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    by_cases hV : Nonempty V.unop
    · obtain ⟨y⟩ := hV
      refine ⟨constSection U.unop (t.1 y), ?_⟩
      apply Subtype.ext
      funext z
      exact constSections_apply_eq t y z
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      funext z
      exact absurd ⟨z⟩ hV

end Constant

section Quot

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

def quotPredicate :
    TopCat.LocalPredicate (X := X.carrier) (fun x => X.functionField ⧸ pointSubgroup D x) where
  pred {V} a := ∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ {z : V | z.1 ∈ W ∧ a z ≠ 0}.Finite
  res {V W} i a h := by
    intro y
    obtain ⟨W', hyW', hW'⟩ := h (i y)
    refine ⟨W', hyW', ?_⟩
    have hinj : Function.Injective (fun z : V => i z) := fun z z' hz =>
      Subtype.ext (congrArg Subtype.val hz :)
    exact (hW'.preimage hinj.injOn).subset fun z hz => hz
  locality {V} a w := by
    intro y
    obtain ⟨V', hyV', i, hV'⟩ := w y
    obtain ⟨W, hyW, hW⟩ := hV' ⟨y.1, hyV'⟩
    refine ⟨W ⊓ V', ⟨hyW, hyV'⟩, ?_⟩
    refine (hW.image (fun z : V' => i z)).subset ?_
    rintro z ⟨⟨hzW, hzV'⟩, hz⟩
    exact ⟨⟨z.1, hzV'⟩, ⟨hzW, hz⟩, rfl⟩

def quotSections (V : X.Opens) : AddSubgroup (∀ z : V, X.functionField ⧸ pointSubgroup D z.1) where
  carrier := {a | (quotPredicate D).pred a}
  zero_mem' := fun _ => ⟨⊤, trivial, by simp⟩
  add_mem' {a b} ha hb := by
    intro y
    obtain ⟨W₁, hy₁, h₁⟩ := ha y
    obtain ⟨W₂, hy₂, h₂⟩ := hb y
    refine ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, (h₁.union h₂).subset ?_⟩
    rintro z ⟨⟨hz₁, hz₂⟩, hz⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    exact hz (by simp only [Pi.add_apply, hc.1 hz₁, hc.2 hz₂, add_zero])
  neg_mem' {a} ha := by
    intro y
    obtain ⟨W, hyW, h⟩ := ha y
    refine ⟨W, hyW, h.subset ?_⟩
    rintro z ⟨hzW, hz⟩
    exact ⟨hzW, fun h0 => hz (by simp only [Pi.neg_apply, h0, neg_zero])⟩

def quotSectionsRes {V W : X.Opens} (h : W ≤ V) : quotSections D V →+ quotSections D W where
  toFun a := ⟨fun y => a.1 ⟨y.1, h y.2⟩, (quotPredicate D).res (homOfLE h) a.1 a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def quotPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (quotSections D V.unop)
  map i := AddCommGrpCat.ofHom (quotSectionsRes D i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem quotPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (X := X.carrier) (quotPresheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (quotPredicate D))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

noncomputable def quotSheaf : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  ⟨quotPresheaf D, quotPresheaf_isSheaf D⟩

noncomputable def divisorToConst : modulesAb (divisorSheaf D) ⟶ constSheaf X :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨(show divisorSections D V.unop from t).1,
            (show divisorSections D V.unop from t).2.1⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
     naturality := fun _ _ _ => rfl }⟩

end Quot

section Resolution

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

lemma finite_not_mem_pointSubgroup (c : X.functionField) :
    {x : X | c ∉ pointSubgroup D x}.Finite := by
  refine ((finite_not_mem_divisorSubgroup D c).image PrimeDivisor.point).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, mem_pointSubgroup_iff, not_forall] at hx
  obtain ⟨h, hc⟩ := hx
  exact ⟨PrimeDivisor.ofPoint x h, by
    simpa only [Set.mem_ofPred_eq, PrimeDivisor.mem_divisorSubgroup] using hc, rfl⟩

lemma mk_mem_quotSections {V : X.Opens} (t : constSections V) :
    (fun z : V => (QuotientAddGroup.mk (t.1 z) : X.functionField ⧸ pointSubgroup D z.1)) ∈
      quotSections D V := by
  intro y
  refine ⟨⊤, trivial, ?_⟩
  have hinj : Function.Injective (fun z : V => z.1) := Subtype.val_injective
  refine (((finite_not_mem_pointSubgroup D (t.1 y)).preimage hinj.injOn)).subset ?_
  rintro z ⟨-, hz⟩
  intro hmem
  apply hz
  change (QuotientAddGroup.mk (t.1 z) : X.functionField ⧸ pointSubgroup D z.1) = 0
  rw [constSections_apply_eq t z y]
  exact (QuotientAddGroup.eq_zero_iff _).mpr hmem

noncomputable def constToQuot : constSheaf X ⟶ quotSheaf D :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨fun z => QuotientAddGroup.mk (t.1 z), mk_mem_quotSections D t⟩
          map_zero' := by
            apply Subtype.ext
            funext z
            exact QuotientAddGroup.mk_zero _
          map_add' := fun s t => by
            apply Subtype.ext
            funext z
            exact QuotientAddGroup.mk_add _ _ _ }
     naturality := fun _ _ _ => rfl }⟩

lemma constToQuot_app_apply (V : X.Opens) (t : constSections V) (z : V) :
    ((constToQuot D).hom.app (op V) t).1 z = QuotientAddGroup.mk (t.1 z) := rfl

noncomputable def divisorSeq : ShortComplex (Sheaf (Opens.grothendieckTopology X.toTopCat)
    AddCommGrpCat.{u}) :=
  ShortComplex.mk (divisorToConst D) (constToQuot D) (by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro t
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk ((show divisorSections D V.unop from t).1 z) :
      X.functionField ⧸ pointSubgroup D z.1) = 0
    rw [QuotientAddGroup.eq_zero_iff, mem_pointSubgroup_iff]
    exact fun h => (show divisorSections D V.unop from t).2.2 z h)

instance : Mono (divisorSeq D).f := by
  apply Sheaf.mono_of_injective
  intro V s t hst
  exact Subtype.ext (congrArg Subtype.val hst :)

lemma mem_pointSubgroup_of_eq_genericPoint {x : X} (hx : x = genericPoint X) (c : X.functionField) :
    c ∈ pointSubgroup D x := by
  subst hx
  rw [mem_pointSubgroup_iff]
  intro h
  exact absurd rfl (PrimeDivisor.ofPoint (genericPoint X) h).point_ne_genericPoint

theorem constToQuot_isLocallySurjective (hX : topologicalKrullDim X ≤ 1) :
    TopCat.Presheaf.IsLocallySurjective (constToQuot D).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hxU
  obtain ⟨W, hxW, hfin⟩ := t.2 ⟨x, hxU⟩
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (t.1 ⟨x, hxU⟩)
  have hcx : ∀ p : U, p.1 = x →
      (QuotientAddGroup.mk c : X.functionField ⧸ pointSubgroup D p.1) = t.1 p := by
    rintro ⟨p, hp⟩ rfl
    exact hc
  set B : Set X := {y | y ≠ x ∧ ((∃ z : U, z.1 = y ∧ z.1 ∈ W ∧ t.1 z ≠ 0) ∨
    c ∉ pointSubgroup D y)} with hB
  have hBfin : B.Finite := by
    refine ((hfin.image Subtype.val).union (finite_not_mem_pointSubgroup D c)).subset ?_
    rintro y ⟨-, ⟨z, rfl, hzW, hz⟩ | hy⟩
    · exact Or.inl ⟨z, ⟨hzW, hz⟩, rfl⟩
    · exact Or.inr hy
  have hBgen : ∀ y ∈ B, y ≠ genericPoint X := by
    rintro y ⟨-, ⟨z, rfl, -, hz⟩ | hy⟩ hgen
    · apply hz
      obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (t.1 z)
      rw [← hr]
      exact (QuotientAddGroup.eq_zero_iff r).mpr (mem_pointSubgroup_of_eq_genericPoint D hgen r)
    · exact hy (mem_pointSubgroup_of_eq_genericPoint D hgen c)
  have hBcl : IsClosed B := by
    have : B = ⋃ y ∈ B, ({y} : Set X) := by simp
    rw [this]
    exact hBfin.isClosed_biUnion fun y hy => isClosed_singleton_of_ne hX (hBgen y hy)
  let V : X.Opens := U ⊓ W ⊓ ⟨Bᶜ, hBcl.isOpen_compl⟩
  have hxV : x ∈ V := ⟨⟨hxU, hxW⟩, fun h => h.1 rfl⟩
  refine ⟨V, fun y hy => hy.1.1, ⟨constSection V c, ?_⟩, hxV⟩
  apply Subtype.ext
  funext z
  change (QuotientAddGroup.mk c : X.functionField ⧸ pointSubgroup D z.1) = t.1 ⟨z.1, z.2.1.1⟩
  by_cases hzx : z.1 = x
  · exact hcx ⟨z.1, z.2.1.1⟩ hzx
  · have hzB : z.1 ∉ B := z.2.2
    simp only [hB, Set.mem_ofPred_eq, not_and, not_or, not_exists, not_not] at hzB
    obtain ⟨h1, h2⟩ := hzB hzx
    rw [(QuotientAddGroup.eq_zero_iff _).mpr h2]
    exact (h1 ⟨z.1, z.2.1.1⟩ rfl z.2.1.2).symm

lemma divisorSeq_epi (hX : topologicalKrullDim X ≤ 1) : Epi (divisorSeq D).g :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi (constToQuot D)).mp
    (constToQuot_isLocallySurjective D hX)

theorem divisorSeq_exact : (divisorSeq D).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{u})
    (X := X.toTopCat) (divisorSeq D)).mpr fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro s hs
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (constSheaf X).obj s
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToQuot D).hom
    (TopCat.Presheaf.germ (constSheaf X).obj U x hxU t) = 0 at hs
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hs
  have hs' := hs.trans
    (map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ (quotSheaf D).obj U x hxU))).symm
  obtain ⟨W, hxW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ hs'
  have hW : ∀ z : W, t.1 ⟨z.1, iU.le z.2⟩ ∈ pointSubgroup D z.1 := by
    intro z
    have := congrArg (fun a => (show quotSections D W from a).1 z) heq
    change (QuotientAddGroup.mk (t.1 ⟨z.1, iU.le z.2⟩) :
      X.functionField ⧸ pointSubgroup D z.1) = 0 at this
    exact (QuotientAddGroup.eq_zero_iff _).mp this
  let s' : divisorSections D W :=
    ⟨fun z => t.1 ⟨z.1, iU.le z.2⟩, constPredicate.res iU t.1 t.2,
      fun y hy => (mem_pointSubgroup_iff D y.1 _).mp (hW y) hy⟩
  let s'' : ToType ((modulesAb (divisorSheaf D)).obj.obj (op W)) := s'
  refine ⟨TopCat.Presheaf.germ (modulesAb (divisorSheaf D)).obj W x hxW s'', ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (divisorToConst D).hom
    (TopCat.Presheaf.germ (modulesAb (divisorSheaf D)).obj W x hxW s'') = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.germ_res_apply (constSheaf X).obj iU x hxW t]
  rfl

theorem divisorSeq_shortExact (hX : topologicalKrullDim X ≤ 1) : (divisorSeq D).ShortExact := by
  have := divisorSeq_epi D hX
  exact ⟨divisorSeq_exact D⟩

end Resolution

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe w' u

namespace GroundTheory.Arith.SchemeCoh

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section Scalars

variable [IsIntegral X]

lemma sectionValue_restrictTop (V : X.Opens) (y : V) (r : Γ(X, ⊤)) :
    sectionValue V y (restrictTop V r) = X.germToFunctionField ⊤ r := by
  rw [restrictTop, sectionValue_res le_top y r, sectionValue_eq]

lemma sectionValue_scalar (V : X.Opens) (y : V) (c : k) :
    sectionValue V y (restrictTop V (scalarRingHom X c)) = algebraMap k X.functionField c := by
  rw [sectionValue_restrictTop, algebraMap_functionField]

variable [IsLocallyNoetherian X] [IsNormalScheme X]

lemma PrimeDivisor.valuation_algebraMap_scalar_le_one (Z : PrimeDivisor X) (c : k) :
    Z.valuation (algebraMap k X.functionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk Z.point) X.functionField]
  exact Z.valuation_algebraMap_le_one _

lemma mul_mem_pointSubgroup (D : WeilDivisor X) (x : X) (c : k) {f : X.functionField}
    (hf : f ∈ pointSubgroup D x) : algebraMap k X.functionField c * f ∈ pointSubgroup D x := by
  rw [mem_pointSubgroup_iff] at hf ⊢
  intro h
  rw [map_mul]
  calc _ ≤ 1 * WithZero.exp (D (PrimeDivisor.ofPoint x h)) :=
        mul_le_mul' ((PrimeDivisor.ofPoint x h).valuation_algebraMap_scalar_le_one c) (hf h)
    _ = _ := one_mul _

end Scalars

section Endo

variable [IsIntegral X]

lemma mul_mem_constSections (c : k) {V : X.Opens} (t : constSections V) :
    (fun y => algebraMap k X.functionField c * t.1 y) ∈ constSections V := by
  intro y
  obtain ⟨W, hyW, h⟩ := t.2 y
  exact ⟨W, hyW, fun z hz => by simp only [h z hz]⟩

noncomputable def constSmul (c : k) : constSheaf X ⟶ constSheaf X :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨fun y => algebraMap k X.functionField c * t.1 y,
            mul_mem_constSections c t⟩
          map_zero' := Subtype.ext (funext fun _ => mul_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => mul_add _ _ _) }
     naturality := fun _ _ _ => rfl }⟩

variable [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

noncomputable def quotMul (c : k) (x : X) :
    X.functionField ⧸ pointSubgroup D x →+ X.functionField ⧸ pointSubgroup D x :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (algebraMap k X.functionField c))
    (fun _ hf => mul_mem_pointSubgroup D x c hf)

lemma quotMul_mk (c : k) (x : X) (f : X.functionField) :
    quotMul D c x (QuotientAddGroup.mk f) = QuotientAddGroup.mk (algebraMap k X.functionField c * f) :=
  rfl

lemma quotMul_mem_quotSections (c : k) {V : X.Opens} (a : quotSections D V) :
    (fun z : V => quotMul D c z.1 (a.1 z)) ∈ quotSections D V := by
  intro y
  obtain ⟨W, hyW, h⟩ := a.2 y
  refine ⟨W, hyW, h.subset ?_⟩
  rintro z ⟨hzW, hz⟩
  exact ⟨hzW, fun h0 => hz (by simp only [h0, map_zero])⟩

noncomputable def quotSmul (c : k) : quotSheaf D ⟶ quotSheaf D :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun a => ⟨fun z => quotMul D c z.1 (a.1 z), quotMul_mem_quotSections D c a⟩
          map_zero' := Subtype.ext (funext fun _ => map_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
     naturality := fun _ _ _ => rfl }⟩

noncomputable def divisorSeqSmul (c : k) : divisorSeq D ⟶ divisorSeq D where
  τ₁ := modulesAbMap (smulHom (divisorSheaf D) (scalarRingHom X c))
  τ₂ := constSmul c
  τ₃ := quotSmul D c
  comm₁₂ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro t
    apply Subtype.ext
    funext y
    change sectionValue V.unop y (restrictTop V.unop (scalarRingHom X c)) *
      (show divisorSections D V.unop from t).1 y = _
    rw [sectionValue_scalar]
    rfl
  comm₂₃ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro t
    rfl

end Endo

noncomputable instance globalAlgebra : Algebra k Γ(X, ⊤) := (scalarRingHom X).toAlgebra

section H0

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

variable (k) in

def globalL (D : WeilDivisor X) : Submodule k X.functionField where
  carrier := {f | ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z)}
  zero_mem' := fun Z => by simp
  add_mem' {f g} hf hg := fun Z => (Valuation.map_add _ _ _).trans (max_le (hf Z) (hg Z))
  smul_mem' c {f} hf := fun Z => by
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * WithZero.exp (D Z) :=
          mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) (hf Z)
      _ = _ := one_mul _

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma mem_globalL (D : WeilDivisor X) (f : X.functionField) :
    f ∈ globalL k D ↔ ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z) := Iff.rfl

variable (k) in

noncomputable def divisorSectionsTopEquiv (D : WeilDivisor X) :
    divisorSections D ⊤ ≃+ globalL k D where
  toFun t := ⟨t.1 ⟨genericPoint X, trivial⟩, fun Z => by
    rw [divisorSections_apply_eq D t ⟨genericPoint X, trivial⟩ ⟨Z.point, trivial⟩]
    exact t.2.2 ⟨Z.point, trivial⟩ Z.2⟩
  invFun f := ⟨fun _ => f.1, fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩,
    fun y hy => f.2 (PrimeDivisor.ofPoint y.1 hy)⟩
  left_inv t := Subtype.ext (funext fun y => divisorSections_apply_eq D t _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (k) in

noncomputable def divisorH0AddEquiv (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0 ≃+ globalL k D :=
  (Sheaf.H.equiv₀ (modulesAb (divisorSheaf D)) isTerminalTop).trans (divisorSectionsTopEquiv k D)

lemma divisorH0AddEquiv_apply (D : WeilDivisor X) (x : Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0)
    (y : (⊤ : X.Opens)) :
    (divisorH0AddEquiv k D x : X.functionField) =
      (show divisorSections D ⊤ from Sheaf.H.equiv₀ _ isTerminalTop x).1 y :=
  divisorSections_apply_eq D _ _ _

variable (k) in

noncomputable def divisorH0Equiv (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0 ≃ₗ[k] globalL k D where
  toAddEquiv := divisorH0AddEquiv k D
  map_smul' c x := by
    apply Subtype.ext
    change (divisorH0AddEquiv k D (c • x) : X.functionField) =
      algebraMap k X.functionField c * (divisorH0AddEquiv k D x : X.functionField)
    rw [divisorH0AddEquiv_apply D _ ⟨genericPoint X, trivial⟩,
      divisorH0AddEquiv_apply D _ ⟨genericPoint X, trivial⟩, H.smul_def,
      ← Sheaf.H.equiv₀_naturality]
    change sectionValue ⊤ _ (restrictTop ⊤ (scalarRingHom X c)) * _ = _
    rw [sectionValue_scalar]

end H0

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe w' u

namespace GroundTheory.Arith.SchemeCoh

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section Repartitions

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

variable (k X) in

def repartitions : Submodule k (PrimeDivisor X → X.functionField) where
  carrier := {a | {Z : PrimeDivisor X | ¬ Z.valuation (a Z) ≤ 1}.Finite}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    refine (ha.union hb).subset fun Z hZ => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hZ ((Valuation.map_add _ _ _).trans (max_le hc.1 hc.2))
  smul_mem' c {a} ha := by
    refine ha.subset fun Z hZ => ?_
    intro h
    apply hZ
    change Z.valuation (c • a Z) ≤ 1
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * 1 := mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) h
      _ = 1 := one_mul 1

variable (k) in

def boundedRepartitions (D : WeilDivisor X) : Submodule k (repartitions k X) where
  carrier := {a | ∀ Z : PrimeDivisor X, a.1 Z ∈ Z.divisorSubgroup D}
  zero_mem' Z := (Z.divisorSubgroup D).zero_mem
  add_mem' {a b} ha hb Z := (Z.divisorSubgroup D).add_mem (ha Z) (hb Z)
  smul_mem' c {a} ha Z := by
    have h := ha Z
    rw [PrimeDivisor.mem_divisorSubgroup] at h ⊢
    change Z.valuation (c • a.1 Z) ≤ _
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * WithZero.exp (D Z) := mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) h
      _ = _ := one_mul _

lemma mem_boundedRepartitions (D : WeilDivisor X) (a : repartitions k X) :
    a ∈ boundedRepartitions k D ↔ ∀ Z : PrimeDivisor X, a.1 Z ∈ Z.divisorSubgroup D := Iff.rfl

lemma const_mem_repartitions (f : X.functionField) :
    (fun _ : PrimeDivisor X => f) ∈ repartitions k X := by
  refine (finite_not_mem_divisorSubgroup (0 : WeilDivisor X) f).subset fun Z hZ => ?_
  simpa only [Set.mem_ofPred_eq, PrimeDivisor.mem_divisorSubgroup, Finsupp.coe_zero,
    Pi.zero_apply, WithZero.exp_zero] using hZ

variable (k X) in

def diagRepartition : X.functionField →ₗ[k] repartitions k X where
  toFun f := ⟨fun _ => f, const_mem_repartitions f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Repartitions

section Principal

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

open Classical in

noncomputable def extendRep (a : PrimeDivisor X → X.functionField) (x : X) : X.functionField :=
  if h : ringKrullDim (X.presheaf.stalk x) = 1 then a (PrimeDivisor.ofPoint x h) else 0

omit [AlgebraicGeometry.IsNoetherian X] [IsNormalScheme X] in
lemma extendRep_point (a : PrimeDivisor X → X.functionField) (Z : PrimeDivisor X) :
    extendRep a Z.point = a Z := by
  rw [extendRep, dif_pos (show ringKrullDim (X.presheaf.stalk Z.point) = 1 from Z.2)]
  rfl

lemma quot_eq_zero_of_not_primeDivisor {x : X} (hx : ¬ ringKrullDim (X.presheaf.stalk x) = 1)
    (q : X.functionField ⧸ pointSubgroup D x) : q = 0 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [QuotientAddGroup.eq_zero_iff, mem_pointSubgroup_iff]
  exact fun h => absurd h hx

lemma mk_extendRep_mem (a : repartitions k X) :
    (fun z : (⊤ : X.Opens) =>
      (QuotientAddGroup.mk (extendRep a.1 z.1) : X.functionField ⧸ pointSubgroup D z.1)) ∈
      quotSections D ⊤ := by
  intro y
  refine ⟨⊤, trivial, ?_⟩
  have hfin : {Z : PrimeDivisor X | a.1 Z ∉ Z.divisorSubgroup D}.Finite := by
    refine (a.2.union D.support.finite_toSet).subset fun Z hZ => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe,
      Finsupp.mem_support_iff] at hc
    apply hZ
    rw [PrimeDivisor.mem_divisorSubgroup, hc.2, WithZero.exp_zero]
    exact hc.1
  have hinj : Function.Injective (fun z : (⊤ : X.Opens) => z.1) := Subtype.val_injective
  refine ((hfin.image PrimeDivisor.point).preimage hinj.injOn).subset ?_
  rintro z ⟨-, hz⟩
  by_cases h : ringKrullDim (X.presheaf.stalk z.1) = 1
  · refine ⟨PrimeDivisor.ofPoint z.1 h, fun hmem => hz ?_, rfl⟩
    rw [QuotientAddGroup.eq_zero_iff, extendRep, dif_pos h, mem_pointSubgroup_iff]
    intro h'
    exact (PrimeDivisor.mem_divisorSubgroup _ _ _).mp hmem
  · exact absurd (quot_eq_zero_of_not_primeDivisor D h _) hz

variable (k) in

noncomputable def repToQuot : repartitions k X →+ quotSections D ⊤ where
  toFun a := ⟨fun z => QuotientAddGroup.mk (extendRep a.1 z.1), mk_extendRep_mem D a⟩
  map_zero' := by
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep 0 z.1) : X.functionField ⧸ pointSubgroup D z.1) = 0
    unfold extendRep
    split_ifs <;> rfl
  map_add' a b := by
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep (a.1 + b.1) z.1) :
      X.functionField ⧸ pointSubgroup D z.1) =
      QuotientAddGroup.mk (extendRep a.1 z.1) + QuotientAddGroup.mk (extendRep b.1 z.1)
    rw [← QuotientAddGroup.mk_add]
    unfold extendRep
    split_ifs
    · rfl
    · rw [add_zero]

lemma repToQuot_apply (a : repartitions k X) (z : (⊤ : X.Opens)) :
    (repToQuot k D a).1 z = QuotientAddGroup.mk (extendRep a.1 z.1) := rfl

lemma repToQuot_eq_zero_iff (a : repartitions k X) :
    repToQuot k D a = 0 ↔ a ∈ boundedRepartitions k D := by
  constructor
  · intro h Z
    have := congrArg (fun s : quotSections D ⊤ => s.1 ⟨Z.point, trivial⟩) h
    change (QuotientAddGroup.mk (extendRep a.1 Z.point) :
      X.functionField ⧸ pointSubgroup D Z.point) = 0 at this
    rw [QuotientAddGroup.eq_zero_iff, extendRep_point, mem_pointSubgroup_primeDivisor] at this
    exact this
  · intro h
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep a.1 z.1) : X.functionField ⧸ pointSubgroup D z.1) = 0
    by_cases hz : ringKrullDim (X.presheaf.stalk z.1) = 1
    · rw [QuotientAddGroup.eq_zero_iff, extendRep, dif_pos hz, mem_pointSubgroup_iff]
      intro _
      exact (PrimeDivisor.mem_divisorSubgroup _ _ _).mp (h _)
    · exact quot_eq_zero_of_not_primeDivisor D hz _

lemma quotSections_top_finite (s : quotSections D ⊤) :
    {z : (⊤ : X.Opens) | s.1 z ≠ 0}.Finite := by
  choose W hW hfin using fun y : (⊤ : X.Opens) => s.2 y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : (⊤ : X.Opens) => (W y : Set X))
    (fun y => (W y).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨⟨x, trivial⟩, hW _⟩)
  refine (t.finite_toSet.biUnion fun y _ => hfin y).subset fun z hz => ?_
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z.1))
  exact Set.mem_iUnion₂.mpr ⟨y, hy, hzy, hz⟩

open Classical in

lemma repToQuot_surjective : Function.Surjective (repToQuot k D) := by
  intro s
  let r : PrimeDivisor X → X.functionField := fun Z =>
    if s.1 ⟨Z.point, trivial⟩ = 0 then 0
    else (QuotientAddGroup.mk_surjective (s.1 ⟨Z.point, trivial⟩)).choose
  have hr : ∀ Z : PrimeDivisor X,
      (QuotientAddGroup.mk (r Z) : X.functionField ⧸ pointSubgroup D Z.point) =
        s.1 ⟨Z.point, trivial⟩ := by
    intro Z
    simp only [r]
    split_ifs with h
    · rw [h]
      rfl
    · exact (QuotientAddGroup.mk_surjective (s.1 ⟨Z.point, trivial⟩)).choose_spec
  have hmem : r ∈ repartitions k X := by
    have hinj : Function.Injective (fun Z : PrimeDivisor X => (⟨Z.point, trivial⟩ : (⊤ : X.Opens))) :=
      fun Z Z' h => PrimeDivisor.point_injective (congrArg (fun p : (⊤ : X.Opens) => p.1) h :)
    refine ((quotSections_top_finite D s).preimage hinj.injOn).subset fun Z hZ => ?_
    intro h0
    have h1 : r Z = 0 := if_pos h0
    change ¬ Z.valuation (r Z) ≤ 1 at hZ
    rw [h1, map_zero] at hZ
    exact hZ zero_le
  refine ⟨⟨r, hmem⟩, ?_⟩
  apply Subtype.ext
  funext z
  rw [repToQuot_apply]
  by_cases hz : ringKrullDim (X.presheaf.stalk z.1) = 1
  · have := hr (PrimeDivisor.ofPoint z.1 hz)
    rw [extendRep, dif_pos hz]
    exact this
  · exact (quot_eq_zero_of_not_primeDivisor D hz _).trans
      (quot_eq_zero_of_not_primeDivisor D hz _).symm

lemma quotSmul_repToQuot (c : k) (a : repartitions k X) :
    (quotSmul D c).hom.app (op ⊤) (repToQuot k D a) = repToQuot k D (c • a) := by
  apply Subtype.ext
  funext z
  change quotMul D c z.1 (QuotientAddGroup.mk (extendRep a.1 z.1)) =
    QuotientAddGroup.mk (extendRep (c • a.1) z.1)
  rw [quotMul_mk]
  unfold extendRep
  split_ifs
  · rw [Pi.smul_apply, Algebra.smul_def]
  · rw [mul_zero]

lemma constToQuot_top (t : constSections (⊤ : X.Opens)) :
    (constToQuot D).hom.app (op ⊤) t =
      repToQuot k D (diagRepartition k X (t.1 ⟨genericPoint X, trivial⟩)) := by
  apply Subtype.ext
  funext z
  rw [constToQuot_app_apply, repToQuot_apply]
  by_cases hz : ringKrullDim (X.presheaf.stalk z.1) = 1
  · rw [extendRep, dif_pos hz, constSections_apply_eq t z ⟨genericPoint X, trivial⟩]
    rfl
  · exact (quot_eq_zero_of_not_primeDivisor D hz _).trans
      (quot_eq_zero_of_not_primeDivisor D hz _).symm

end Principal

section H1

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (hX : topologicalKrullDim X ≤ 1) (D : WeilDivisor X)

variable (k) in

noncomputable def repToQuotTop : repartitions k X →+ (quotSheaf D).obj.obj (op ⊤) where
  toFun a := repToQuot k D a
  map_zero' := (repToQuot k D).map_zero
  map_add' := (repToQuot k D).map_add

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma quotSmul_repToQuotTop (c : k) (a : repartitions k X) :
    (quotSmul D c).hom.app (op ⊤) (repToQuotTop k D a) = repToQuotTop k D (c • a) :=
  quotSmul_repToQuot D c a

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma constToQuot_constSection (f : X.functionField) :
    (constToQuot D).hom.app (op ⊤) (show (constSheaf X).obj.obj (op ⊤) from constSection ⊤ f) =
      repToQuotTop k D (diagRepartition k X f) :=
  constToQuot_top D (constSection ⊤ f)

noncomputable def quotDelta :
    Sheaf.H.{w'} (quotSheaf D) 0 →+ Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 :=
  H.δ.{w'} (divisorSeq_shortExact D hX) 0 1 rfl

lemma quotDelta_surjective : Function.Surjective (quotDelta.{w'} hX D) := fun x =>
  H.exact₁ (divisorSeq_shortExact D hX) (n₀ := 0) rfl x
    (H_eq_zero_of_isFlasque (constSheaf X) 0 _)

lemma quotDelta_eq_zero_iff (y : Sheaf.H.{w'} (quotSheaf D) 0) :
    quotDelta hX D y = 0 ↔
      ∃ w : Sheaf.H.{w'} (constSheaf X) 0, Sheaf.H.map (constToQuot D) 0 w = y :=
  ⟨fun h => H.exact₃ (divisorSeq_shortExact D hX) rfl y h, fun ⟨w, hw⟩ => hw ▸
    H.δ_map_g (divisorSeq_shortExact D hX) rfl w⟩

lemma quotDelta_smul (c : k) (y : Sheaf.H.{w'} (quotSheaf D) 0) :
    quotDelta hX D (Sheaf.H.map (quotSmul D c) 0 y) = c • quotDelta hX D y :=
  H.δ_naturality (divisorSeq_shortExact D hX) (divisorSeq_shortExact D hX) (divisorSeqSmul D c)
    0 1 rfl y

variable (k) in

noncomputable def repartitionToH1 : repartitions k X →+ Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 :=
  (quotDelta hX D).comp
    ((Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop).symm.toAddMonoidHom.comp (repToQuotTop k D))

lemma repartitionToH1_apply (a : repartitions k X) :
    repartitionToH1 k hX D a = quotDelta hX D
      ((Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop).symm (repToQuotTop k D a)) := rfl

lemma repartitionToH1_surjective : Function.Surjective (repartitionToH1.{w'} k hX D) := by
  intro x
  obtain ⟨y, rfl⟩ := quotDelta_surjective hX D x
  obtain ⟨a, ha⟩ := repToQuot_surjective (k := k) D
    (Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop y)
  refine ⟨a, ?_⟩
  have ha' : repToQuotTop k D a = Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop y := ha
  rw [repartitionToH1_apply, ha', AddEquiv.symm_apply_apply]

lemma repartitionToH1_eq_zero_iff (a : repartitions k X) :
    repartitionToH1.{w'} k hX D a = 0 ↔
      a ∈ boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X) := by
  constructor
  · intro h
    rw [repartitionToH1_apply, quotDelta_eq_zero_iff] at h
    obtain ⟨w, hw⟩ := h
    let t : (constSheaf X).obj.obj (op ⊤) := Sheaf.H.equiv₀ (constSheaf X) isTerminalTop w
    have e1 : (constToQuot D).hom.app (op ⊤) t =
        Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop (Sheaf.H.map (constToQuot D) 0 w) :=
      Sheaf.H.equiv₀_naturality (hT := isTerminalTop) (constToQuot D) w
    rw [hw, AddEquiv.apply_symm_apply] at e1
    have e3 : (constToQuot D).hom.app (op ⊤) t =
        repToQuotTop k D (diagRepartition k X ((show constSections ⊤ from t).1
          ⟨genericPoint X, trivial⟩)) :=
      constToQuot_top D t
    have hb : a - diagRepartition k X ((show constSections ⊤ from t).1 ⟨genericPoint X, trivial⟩) ∈
        boundedRepartitions k D := by
      rw [← repToQuot_eq_zero_iff, map_sub]
      change repToQuotTop k D a - repToQuotTop k D _ = 0
      rw [← e1, e3, sub_self]
    exact Submodule.mem_sup.mpr ⟨_, hb, _, ⟨_, rfl⟩, sub_add_cancel _ _⟩
  · intro h
    obtain ⟨b, hb, d, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h
    rw [map_add]
    have h1 : repartitionToH1.{w'} k hX D b = 0 := by
      have : repToQuotTop k D b = repToQuotTop k D 0 :=
        ((repToQuot_eq_zero_iff D b).mpr hb).trans (map_zero (repToQuot k D)).symm
      rw [repartitionToH1_apply, this, ← repartitionToH1_apply hX D 0, map_zero]
    have h2 : repartitionToH1.{w'} k hX D (diagRepartition k X f) = 0 := by
      rw [repartitionToH1_apply, ← constToQuot_constSection, ← Sheaf.H.equiv₀_symm_naturality,
        quotDelta_eq_zero_iff]
      exact ⟨_, rfl⟩
    rw [h1, h2, add_zero]

lemma repartitionToH1_smul (c : k) (a : repartitions k X) :
    repartitionToH1.{w'} k hX D (c • a) = c • repartitionToH1.{w'} k hX D a := by
  rw [repartitionToH1_apply, repartitionToH1_apply, ← quotSmul_repToQuotTop, ← quotDelta_smul,
    Sheaf.H.equiv₀_symm_naturality]

variable (k) in

noncomputable def repartitionToH1Linear :
    repartitions k X →ₗ[k] Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 where
  toFun := repartitionToH1 k hX D
  map_add' := map_add _
  map_smul' := repartitionToH1_smul hX D

lemma ker_repartitionToH1Linear :
    LinearMap.ker (repartitionToH1Linear.{w'} k hX D) =
      boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X) := by
  ext a
  exact repartitionToH1_eq_zero_iff hX D a

variable (k) in

noncomputable def divisorH1Equiv : Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 ≃ₗ[k]
    (repartitions k X ⧸ (boundedRepartitions k D ⊔ LinearMap.range (diagRepartition k X))) :=
  ((Submodule.quotEquivOfEq _ _ (ker_repartitionToH1Linear hX D).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (repartitionToH1_surjective hX D))).symm

end H1

end GroundTheory.Arith.SchemeCoh
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsNormalScheme X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField] (hX : topologicalKrullDim X ≤ 1)

noncomputable def toRepartition (a : repartitions k X) : Repartition k X.functionField :=
  Repartition.mk (fun v => a.1 ((placeEquiv (k := k) hX).symm v)) (by
    refine (a.2.image (placeEquiv (k := k) hX)).subset fun v hv => ?_
    refine ⟨(placeEquiv (k := k) hX).symm v, ?_, Equiv.apply_symm_apply _ _⟩
    intro h
    apply hv
    obtain ⟨Z, rfl⟩ := (placeEquiv (k := k) hX).surjective v
    rw [Equiv.symm_apply_apply] at h ⊢
    exact (Z.mem_toPlace_ring _).mpr h)

omit [IsFunctionField k X.functionField] in
lemma toRepartition_apply_toPlace (a : repartitions k X) (Z : PrimeDivisor X) :
    toRepartition (k := k) hX a Z.toPlace = a.1 Z := by
  rw [toRepartition, Repartition.mk_apply, ← placeEquiv_apply hX, Equiv.symm_apply_apply]

noncomputable def repartitionEquiv : repartitions k X ≃ₗ[k] Repartition k X.functionField where
  toFun := toRepartition hX
  invFun b := ⟨fun Z => b Z.toPlace, by
    refine ((Repartition.finite_not_mem b).preimage
      (PrimeDivisor.toPlace_injective (k := k)).injOn).subset fun Z hZ => ?_
    intro h
    exact hZ ((Z.mem_toPlace_ring _).mp h)⟩
  map_add' a b := Repartition.ext fun v => by
    simp only [toRepartition, Repartition.mk_apply, Repartition.add_apply]
    rfl
  map_smul' c a := Repartition.ext fun v => by
    simp only [toRepartition, Repartition.mk_apply, Repartition.smul_apply, RingHom.id_apply]
    change c • a.1 _ = _
    rw [Algebra.smul_def]
  left_inv a := Subtype.ext (funext fun Z => toRepartition_apply_toPlace hX a Z)
  right_inv b := Repartition.ext fun v => by
    obtain ⟨Z, rfl⟩ := PrimeDivisor.toPlace_surjective (k := k) hX v
    exact toRepartition_apply_toPlace hX _ Z

lemma map_boundedRepartitions (D : WeilDivisor X) :
    (boundedRepartitions k D).map (repartitionEquiv (k := k) hX).toLinearMap =
      Divisor.A (divisorEquiv (k := k) hX D) := by
  ext b
  rw [Submodule.mem_map_equiv, mem_boundedRepartitions, Divisor.mem_A]
  constructor
  · intro h v
    obtain ⟨Z, rfl⟩ := PrimeDivisor.toPlace_surjective (k := k) hX v
    have := (Z.mem_divisorSubgroup D _).mp (h Z)
    rw [PrimeDivisor.toPlace_valuation, divisorEquiv_apply_toPlace]
    exact this
  · intro h Z
    rw [PrimeDivisor.mem_divisorSubgroup]
    have := h Z.toPlace
    rwa [PrimeDivisor.toPlace_valuation, divisorEquiv_apply_toPlace] at this

lemma map_range_diagRepartition :
    (LinearMap.range (diagRepartition k X)).map (repartitionEquiv (k := k) hX).toLinearMap =
      Repartition.principal k X.functionField := by
  rw [← LinearMap.range_comp]
  congr 1

lemma globalL_eq (D : WeilDivisor X) :
    globalL k D = Divisor.L (divisorEquiv (k := k) hX D) := by
  ext f
  rw [mem_globalL, mem_L_divisorEquiv]

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

noncomputable def divisorH0EquivL (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0 ≃ₗ[k] Divisor.L (divisorEquiv (k := k) hX D) :=
  (divisorH0Equiv k D).trans (LinearEquiv.ofEq _ _ (globalL_eq hX D))

end GroundTheory.Arith.SchemeCoh
end
