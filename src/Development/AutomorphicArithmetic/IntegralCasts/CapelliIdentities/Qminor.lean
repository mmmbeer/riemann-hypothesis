import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qf10.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : Nat} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [inst : Ring A] {n : Nat} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        @Eq A
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst)))))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst)))) (E a b)
              (E c d))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst)))) (E c d)
              (E a b)))
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst)))))
            (@ite A (@Eq (Fin n) b c) (instDecidableEqFin n b c) (E a d)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst))))))
            (@ite A (@Eq (Fin n) d a) (instDecidableEqFin n d a) (E c b)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst)))))))

noncomputable def UpperTheory.Reformulated.B.Qf10.Tm.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n : Nat} → (Fin n → Fin n → A) → Complex → Fin n → Fin n → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n : Nat} (E : Fin n → Fin n → A) (u : Complex) (a b : Fin n) ↦
      @HAdd.hAdd A A A (@instHAdd A (@Distrib.toAdd A (@instDistribOfSemiring A (@Ring.toSemiring A inst))))
        (@ite A (@Eq (Fin n) a b) (instDecidableEqFin n a b)
          (@DFunLike.coe
            (@RingHom Complex A
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
              (@Semiring.toNonAssocSemiring A (@Ring.toSemiring A inst)))
            Complex (fun (x : Complex) ↦ A)
            (@RingHom.instFunLike Complex A
              (@Semiring.toNonAssocSemiring Complex (@CommSemiring.toSemiring Complex Complex.instCommSemiring))
              (@Semiring.toNonAssocSemiring A (@Ring.toSemiring A inst)))
            (@Algebra.algebraMap Complex A Complex.instCommSemiring (@Ring.toSemiring A inst) inst_1) u)
          (@OfNat.ofNat A (nat_lit 0)
            (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst))))))
        (E a b)

noncomputable def UpperTheory.Reformulated.B.Qf10.qminor.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n t : Nat} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → Complex → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n t : Nat} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : Complex) ↦
      ∑ σ : Equiv.Perm (Fin t),
        @HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst))))
          (@Int.cast A (@AddGroupWithOne.toIntCast A (@Ring.toAddGroupWithOne A inst))
            (@Units.val Int Int.instMonoid
              (@DFunLike.coe
                (@MonoidHom (Equiv.Perm (Fin t)) (@Units Int Int.instMonoid)
                  (@MulOneClass.toMulOne (Equiv.Perm (Fin t))
                    (@Monoid.toMulOneClass (Equiv.Perm (Fin t))
                      (@DivInvMonoid.toMonoid (Equiv.Perm (Fin t))
                        (@Group.toDivInvMonoid (Equiv.Perm (Fin t)) (@Equiv.Perm.permGroup (Fin t))))))
                  (@MulOneClass.toMulOne (@Units Int Int.instMonoid) (@Units.instMulOneClass Int Int.instMonoid)))
                (Equiv.Perm (Fin t)) (fun (x : Equiv.Perm (Fin t)) ↦ @Units Int Int.instMonoid)
                (@MonoidHom.instFunLike (Equiv.Perm (Fin t)) (@Units Int Int.instMonoid)
                  (@MulOneClass.toMulOne (Equiv.Perm (Fin t))
                    (@Monoid.toMulOneClass (Equiv.Perm (Fin t))
                      (@DivInvMonoid.toMonoid (Equiv.Perm (Fin t))
                        (@Group.toDivInvMonoid (Equiv.Perm (Fin t)) (@Equiv.Perm.permGroup (Fin t))))))
                  (@MulOneClass.toMulOne (@Units Int Int.instMonoid) (@Units.instMulOneClass Int Int.instMonoid)))
                (@Equiv.Perm.sign (Fin t) (instDecidableEqFin t) (Fin.fintype t)) σ)))
          (@List.prod A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst)))
            (@AddMonoidWithOne.toOne A (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A inst)))
            (@List.ofFn A t fun (k : Fin t) ↦
              @UpperTheory.Reformulated.B.Qf10.Tm A inst inst_1 n E
                (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) u
                  (@Nat.cast Complex Complex.instNatCast (@Fin.val t k)))
                (a
                  (@DFunLike.coe (Equiv.Perm (Fin t)) (Fin t) (fun (x : Fin t) ↦ Fin t)
                    (@EquivLike.toFunLike (Equiv.Perm (Fin t)) (Fin t) (Fin t) (@Equiv.instEquivLike (Fin t) (Fin t))) σ k))
                (b k)))

noncomputable def UpperTheory.Reformulated.B.Qf10.qdet.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n : Nat} → (Fin n → Fin n → A) → Complex → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n : Nat} (E : Fin n → Fin n → A) (u : Complex) ↦
      @UpperTheory.Reformulated.B.Qf10.qminor A inst inst_1 n n E (@id (Fin n)) (@id (Fin n)) u

theorem UpperTheory.Reformulated.B.Qf10.casimir :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V]
      (E : Fin 2 → Fin 2 → Module.End ℂ V),
      UpperTheory.Reformulated.B.Qf10.GlRel E →
        ∀ (k : ℂ) (φ : V),
          (E 0 0) φ + (E 1 1) φ = 0 →
            (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
              (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
                ∀ (u : ℂ),
                  (UpperTheory.Reformulated.B.Qf10.qdet E (u + 1 / 2)) φ =
                    ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  intro V _ _ E hE k φ h1 h2 h3 u
  have rel : ∀ a b c d : Fin 2, E a b (E c d φ) - E c d (E a b φ) =
      (if b = c then E a d φ else 0) - (if d = a then E c b φ else 0) := by
    intro a b c d
    have h := congrArg (fun f : Module.End ℂ V => f φ) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [h]
    split_ifs <;> simp
  have rab : E 0 0 (E 0 1 φ) - E 0 1 (E 0 0 φ) = E 0 1 φ := by simpa using rel 0 0 0 1
  have rac : E 0 0 (E 1 0 φ) - E 1 0 (E 0 0 φ) = -E 1 0 φ := by simpa using rel 0 0 1 0
  have rdb : E 1 1 (E 0 1 φ) - E 0 1 (E 1 1 φ) = -E 0 1 φ := by simpa using rel 1 1 0 1
  have rdc : E 1 1 (E 1 0 φ) - E 1 0 (E 1 1 φ) = E 1 0 φ := by simpa using rel 1 1 1 0
  have rbc : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by simpa using rel 0 1 1 0
  have rad : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by simpa using rel 0 0 1 1
  have t1 : ∀ X : Module.End ℂ V, X (E 0 0 φ) + X (E 1 1 φ) = 0 := fun X => by
    rw [← map_add, h1, map_zero]
  have t2 : ∀ X : Module.End ℂ V,
      X (E 0 1 φ) - X (E 1 0 φ) = (Complex.I * k) • X φ := fun X => by
    rw [← map_sub, h2, map_smul]
  have t3 : ∀ X : Module.End ℂ V, X (E 0 0 φ) - X (E 1 1 φ) =
      Complex.I • (X (E 0 1 φ) + X (E 1 0 φ)) := fun X => by
    rw [← map_sub, h3, map_smul, map_add]
  have hc : (E 0 0 (E 0 0 φ) - E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) + E 1 1 (E 1 1 φ)) +
      (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ)) =
      (-2 * k) • φ := by
    linear_combination (norm := module)
      (t3 (E 0 0) - t3 (E 1 1) + Complex.I • t3 (E 0 1) + Complex.I • t3 (E 1 0)) +
        Complex.I • (rab + rac - rdb - rdc) + (2 * Complex.I) • h2 +
        Complex.I_sq • (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) +
          (2 * k) • φ)
  have hw : E 0 1 (E 0 1 φ) - E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) =
      (-k ^ 2) • φ := by
    linear_combination (norm := module)
      (t2 (E 0 1) - t2 (E 1 0)) + (Complex.I * k) • h2 + Complex.I_sq • (k ^ 2 • φ)
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hq : ∀ v : ℂ, UpperTheory.Reformulated.B.Qf10.qdet E v φ =
      v • ((v - 1) • φ + E 1 1 φ) + ((v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ)) - E 1 0 (E 0 1 φ) := by
    intro v
    unfold UpperTheory.Reformulated.B.Qf10.qdet UpperTheory.Reformulated.B.Qf10.qminor UpperTheory.Reformulated.B.Qf10.Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  rw [hq]
  linear_combination (norm := module)
    u • h1 + (1 / 4 : ℂ) • (t1 (E 0 0) + t1 (E 1 1)) + (1 / 2 : ℂ) • rad - (1 / 4 : ℂ) • hc +
      (1 / 4 : ℂ) • hw + (1 / 2 : ℂ) • rbc
