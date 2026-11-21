import Mathlib

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.GlRel.{u_1} :
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

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm.{u_1} :
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

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor.{u_1} :
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
              @UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm A inst inst_1 n E
                (@HSub.hSub Complex Complex Complex (@instHSub Complex Complex.instSub) u
                  (@Nat.cast Complex Complex.instNatCast (@Fin.val t k)))
                (a
                  (@DFunLike.coe (Equiv.Perm (Fin t)) (Fin t) (fun (x : Fin t) ↦ Fin t)
                    (@EquivLike.toFunLike (Equiv.Perm (Fin t)) (Fin t) (Fin t) (@Equiv.instEquivLike (Fin t) (Fin t))) σ k))
                (b k)))

noncomputable def UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet.{u_1} :
    {A : Type u_1} →
      [inst : Ring A] →
        [@Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)] →
          {n : Nat} → (Fin n → Fin n → A) → Complex → A :=
    fun {A : Type u_1} [inst : Ring A] [inst_1 : @Algebra Complex A Complex.instCommSemiring (@Ring.toSemiring A inst)]
        {n : Nat} (E : Fin n → Fin n → A) (u : Complex) ↦
      @UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor A inst inst_1 n n E (@id (Fin n)) (@id (Fin n)) u

theorem UpperTheory.Reformulated.B.QuantumMinorsCasimir.casimir :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V]
      (E : Fin 2 → Fin 2 → Module.End ℂ V),
      UpperTheory.Reformulated.B.QuantumMinorsCasimir.GlRel E →
        ∀ (k : ℂ) (φ : V),
          (E 0 0) φ + (E 1 1) φ = 0 →
            (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
              (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
                ∀ (u : ℂ),
                  (UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet E (u + 1 / 2)) φ =
                    ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  intro V _ _ E h k φ h1 h2 h3 u
  have hq : ∀ v : ℂ, UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet E v φ =
      (v * (v - 1)) • φ + v • E 1 1 φ + (v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ) - E 1 0 (E 0 1 φ) := by
    intro v
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
    unfold UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  have c (a b c d : Fin 2) := congrArg (fun f : Module.End ℂ V => f φ) (h a b c d)
  have cad := c 0 0 1 1
  have cab := c 0 0 0 1
  have cac := c 0 0 1 0
  have cdb := c 1 1 0 1
  have cdc := c 1 1 1 0
  have cbc := c 0 1 1 0
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, Fin.zero_eq_one_iff,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, LinearMap.zero_apply] at cad cab cac cdb cdc cbc
  have z (a b : Fin 2) := congrArg (E a b) h1
  have w (a b : Fin 2) := congrArg (E a b) h2
  have g (a b : Fin 2) := congrArg (E a b) h3
  simp only [map_add, map_sub, map_smul, map_zero] at z w g
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hq]
  linear_combination (norm := skip) u • h1 + (1 / 4 : ℂ) • (z 0 0 + z 1 1 - (g 0 0 - g 1 1)
    - Complex.I • (g 0 1 + g 1 0) - (2 * Complex.I) • h2 + (w 0 1 - w 1 0) + (Complex.I * k) • h2
    + (2 : ℂ) • cad - Complex.I • (cab + cac - cdb - cdc) + (2 : ℂ) • cbc)
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
