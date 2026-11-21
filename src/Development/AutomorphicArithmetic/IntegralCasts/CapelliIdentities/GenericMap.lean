import Mathlib

theorem UpperTheory.Reformulated.B.GenericMap.aux1 :
    ∀ {Ω : Type} [inst : Field Ω],
      @IsLocalRing Ω (@CommSemiring.toSemiring Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst))) := by
  intro Ω inst
  infer_instance

noncomputable def UpperTheory.Reformulated.B.GenericMap.genPt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) → ↥X :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [Field Ω]
        (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) =>
      ξ (IsLocalRing.closedPoint Ω)

noncomputable def UpperTheory.Reformulated.B.GenericMap.Cpt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) → Type :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [Field Ω]
        (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) =>
      { p : ↥X // UpperTheory.Reformulated.B.GenericMap.genPt ξ ⤳ p }

theorem UpperTheory.Reformulated.B.GenericMap.aux4 :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      (ξ :
        @Quiver.Hom AlgebraicGeometry.Scheme
          (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
            (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
          (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
      (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ),
      @Specializes (↥X)
        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
          X.toSheafedSpace)
        (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ)
        (@Subtype.val (↥X)
          (fun (p : ↥X) ↦
            @Specializes (↥X)
              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                X.toSheafedSpace)
              (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
          p) := by
  intro X Ω inst ξ p
  exact p.2

theorem UpperTheory.Reformulated.B.GenericMap.aux5 :
    ∀ {Ω : Type} [inst : Field Ω],
      @IsLocalRing (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
        (@CommSemiring.toSemiring (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
          (@CommRing.toCommSemiring (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
            (@CommRingCat.instCommRingObjForgetRingHomCarrier (@CommRingCat.of Ω (@Field.toCommRing Ω inst))))) := by
  intro Ω inst
  infer_instance

noncomputable def UpperTheory.Reformulated.B.GenericMap.genMap :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) →
              @RingHom
                (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                      (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                          X.toSheafedSpace))
                      (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                          X.toSheafedSpace))
                      (@Subtype.val (↥X)
                        (fun (p : ↥X) ↦
                          @Specializes (↥X)
                            (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                              CommRingCat.instCategory X.toSheafedSpace)
                            (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                        p)) :
                  Type)
                Ω
                (@Semiring.toNonAssocSemiring
                  (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                        CommRingCat.Colimits.hasColimits_commRingCat
                        (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                            X.toSheafedSpace))
                        (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                            X.toSheafedSpace))
                        (@Subtype.val (↥X)
                          (fun (p : ↥X) ↦
                            @Specializes (↥X)
                              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                CommRingCat.instCategory X.toSheafedSpace)
                              (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                          p)) :
                    Type)
                  (@CommSemiring.toSemiring
                    (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                          CommRingCat.Colimits.hasColimits_commRingCat
                          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                            p)) :
                      Type)
                    (@CommRing.toCommSemiring
                      (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                            CommRingCat.Colimits.hasColimits_commRingCat
                            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                                X.toSheafedSpace))
                            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                                X.toSheafedSpace))
                            (@Subtype.val (↥X)
                              (fun (p : ↥X) ↦
                                @Specializes (↥X)
                                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                    CommRingCat.instCategory X.toSheafedSpace)
                                  (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                              p)) :
                        Type)
                      (@CommRingCat.instCommRingObjForgetRingHomCarrier
                        (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                          CommRingCat.Colimits.hasColimits_commRingCat
                          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                            p))))))
                (@Semiring.toNonAssocSemiring Ω
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst)))) :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) ↦
      @CommRingCat.Hom.hom
        (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
          (@Subtype.val (↥X)
            (fun (p : ↥X) ↦
              @Specializes (↥X)
                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                  X.toSheafedSpace)
                (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
            p))
        (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
        (@CategoryTheory.CategoryStruct.comp CommRingCat
          (@CategoryTheory.Category.toCategoryStruct CommRingCat CommRingCat.instCategory)
          (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@Subtype.val (↥X)
              (fun (p : ↥X) ↦
                @Specializes (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                    X.toSheafedSpace)
                  (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
              p))
          (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ))
          (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
          (@TopCat.Presheaf.stalkSpecializes CommRingCat CommRingCat.instCategory
            CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ)
            (@Subtype.val (↥X)
              (fun (p : ↥X) ↦
                @Specializes (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                    X.toSheafedSpace)
                  (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
              p)
            (@UpperTheory.Reformulated.B.GenericMap.aux4 X Ω inst ξ p))
          (@AlgebraicGeometry.Scheme.stalkClosedPointTo X (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
            (@UpperTheory.Reformulated.B.GenericMap.aux5 Ω inst) ξ))

noncomputable def UpperTheory.Reformulated.B.GenericMap.regAt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ →
              @Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))) :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) ↦
      @RingHom.range
        (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
              (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
              (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
              (@Subtype.val (↥X)
                (fun (p : ↥X) ↦
                  @Specializes (↥X)
                    (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace)
                    (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                p)) :
          Type)
        Ω
        (@NonAssocCommRing.toNonAssocRing
          (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@Subtype.val (↥X)
                  (fun (p : ↥X) ↦
                    @Specializes (↥X)
                      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                        CommRingCat.instCategory X.toSheafedSpace)
                      (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                  p)) :
            Type)
          (@CommRing.toNonAssocCommRing
            (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                  (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace))
                  (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace))
                  (@Subtype.val (↥X)
                    (fun (p : ↥X) ↦
                      @Specializes (↥X)
                        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                          CommRingCat.instCategory X.toSheafedSpace)
                        (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                    p)) :
              Type)
            (@CommRingCat.instCommRingObjForgetRingHomCarrier
              (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@Subtype.val (↥X)
                  (fun (p : ↥X) ↦
                    @Specializes (↥X)
                      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                        CommRingCat.instCategory X.toSheafedSpace)
                      (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                  p)))))
        (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))
        (@UpperTheory.Reformulated.B.GenericMap.genMap X Ω inst ξ p)

noncomputable def UpperTheory.Reformulated.B.GenericMap.unitAt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) →
            UpperTheory.Reformulated.B.GenericMap.Cpt ξ → Ω → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [Field Ω]
        (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X)
        (p : UpperTheory.Reformulated.B.GenericMap.Cpt ξ) (a : Ω) =>
      a ≠ 0 ∧
        a ∈ UpperTheory.Reformulated.B.GenericMap.regAt ξ p ∧
          a⁻¹ ∈ UpperTheory.Reformulated.B.GenericMap.regAt ξ p

noncomputable def UpperTheory.Reformulated.B.GenericMap.InFibre :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) →
            ℕ → UpperTheory.Reformulated.B.GenericMap.Cpt ξ → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [Field Ω]
        (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ)
        (q : UpperTheory.Reformulated.B.GenericMap.Cpt ξ) =>
      ¬UpperTheory.Reformulated.B.GenericMap.unitAt ξ q ↑p

noncomputable def UpperTheory.Reformulated.B.GenericMap.Char0 :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) →
            UpperTheory.Reformulated.B.GenericMap.Cpt ξ → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [Field Ω]
        (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X)
        (p : UpperTheory.Reformulated.B.GenericMap.Cpt ξ) =>
      ∀ (r : ℕ), Nat.Prime r → ¬UpperTheory.Reformulated.B.GenericMap.InFibre ξ r p

namespace UpperTheory.Reformulated.B.GenericMap.Hlp
private theorem units_nat {Ω : Type} [Field Ω] (S : Subring Ω)
    (hp : ∀ r : ℕ, r.Prime → ((r : Ω) ≠ 0 ∧ (r : Ω) ∈ S ∧ (r : Ω)⁻¹ ∈ S)) :
    ∀ n : ℕ, n ≠ 0 → ((n : Ω) ≠ 0 ∧ (n : Ω) ∈ S ∧ (n : Ω)⁻¹ ∈ S) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [S.one_mem]
  | prime p hpp => intro _; exact hp p hpp
  | mul a b ha hb =>
    intro hab
    have ha0 : a ≠ 0 := fun h => hab (by simp [h])
    have hb0 : b ≠ 0 := fun h => hab (by simp [h])
    obtain ⟨a1, a2, a3⟩ := ha ha0
    obtain ⟨b1, b2, b3⟩ := hb hb0
    refine ⟨by push_cast; exact mul_ne_zero a1 b1, by push_cast; exact S.mul_mem a2 b2, ?_⟩
    push_cast; rw [mul_inv]; exact S.mul_mem a3 b3
end UpperTheory.Reformulated.B.GenericMap.Hlp

theorem UpperTheory.Reformulated.B.GenericMap.main :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      {ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X}
      {q : UpperTheory.Reformulated.B.GenericMap.Cpt ξ},
      UpperTheory.Reformulated.B.GenericMap.Char0 ξ q →
        ∀ (n : ℕ), n ≠ 0 → UpperTheory.Reformulated.B.GenericMap.unitAt ξ q ↑n := by
  intro X Ω inst ξ q hq n hn
  have key := UpperTheory.Reformulated.B.GenericMap.Hlp.units_nat (UpperTheory.Reformulated.B.GenericMap.regAt ξ q)
    (fun r hr => by
      have := hq r hr
      unfold UpperTheory.Reformulated.B.GenericMap.InFibre at this
      exact not_not.mp this) n hn
  exact key
