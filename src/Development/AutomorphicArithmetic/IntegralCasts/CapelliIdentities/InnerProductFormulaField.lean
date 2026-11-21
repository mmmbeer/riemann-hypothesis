import Mathlib

noncomputable def UpperTheory.Reformulated.B.InnerProductFormulaField.GlRel.{u_2, u_5} :
    {R : Type u_2} → [DecidableEq R] → {A : Type u_5} → [Ring A] → (R → R → A) → Prop :=
    fun {R : Type u_2} [inst : DecidableEq R] {A : Type u_5} [inst_1 : Ring A] (T : R → R → A) ↦
      ∀ (a b c d : R),
        @Eq A
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst_1)))))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst_1))))
              (T a b) (T c d))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst_1))))
              (T c d) (T a b)))
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst_1)))))
            (@ite A (@Eq R b c) (inst b c) (T a d)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst_1))))))
            (@ite A (@Eq R d a) (inst d a) (T c b)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst_1)))))))
