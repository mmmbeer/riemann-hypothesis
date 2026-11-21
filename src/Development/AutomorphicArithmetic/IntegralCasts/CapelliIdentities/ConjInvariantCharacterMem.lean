import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yzd4.cT :
    {A : Type} →
      [inst : CommRing A] →
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) →
          {m p : Type} → Matrix m p A → Matrix p m A :=
    fun {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) =>
      (M.map ⇑σ).transpose

private theorem cT_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (a b : Matrix n n A) :
    UpperTheory.Reformulated.B.Yzd4.cT σ (a * b) = UpperTheory.Reformulated.B.Yzd4.cT σ b * UpperTheory.Reformulated.B.Yzd4.cT σ a := by
  simp only [UpperTheory.Reformulated.B.Yzd4.cT]
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) : UpperTheory.Reformulated.B.Yzd4.cT σ (1 : Matrix n n A) = 1 := by
  simp only [UpperTheory.Reformulated.B.Yzd4.cT]
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.Yzd4.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
      (σ :
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
      (J : Matrix n n A)
      {a b : @Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (Set
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
            @Eq (Matrix n n A)
              (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                  (@Distrib.toMul A
                    (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                    (@Units.val (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                      g))
                  J)
                (@Units.val (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                  g))
              J)
          a →
        @Membership.mem
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (Set
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
              @Eq (Matrix n n A)
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                      (@Distrib.toMul A
                        (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                      (@Units.val (Matrix n n A)
                        (@Semiring.toMonoid (Matrix n n A)
                          (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                            inst_2))
                        g))
                    J)
                  (@Units.val (Matrix n n A)
                    (@Semiring.toMonoid (Matrix n n A)
                      (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                    g))
                J)
            b →
          @Membership.mem
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (Set
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
              @Eq (Matrix n n A)
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                      (@Distrib.toMul A
                        (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                      (@Units.val (Matrix n n A)
                        (@Semiring.toMonoid (Matrix n n A)
                          (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                            inst_2))
                        g))
                    J)
                  (@Units.val (Matrix n n A)
                    (@Semiring.toMonoid (Matrix n n A)
                      (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                    g))
                J)
            (@HMul.hMul
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@instHMul
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@MulOne.toMul
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@DivInvMonoid.toMonoid
                        (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@Group.toDivInvMonoid
                          (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@Units.instGroup (Matrix n n A)
                            (@Semiring.toMonoid (Matrix n n A)
                              (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                                inst_2)))))))))
              a b) := by
  intro A _ n _ _ σ J a b ha hb
  have ha' : UpperTheory.Reformulated.B.Yzd4.cT σ (a : Matrix n n A) * J * (a : Matrix n n A) = J := ha
  have hb' : UpperTheory.Reformulated.B.Yzd4.cT σ (b : Matrix n n A) * J * (b : Matrix n n A) = J := hb
  change UpperTheory.Reformulated.B.Yzd4.cT σ ((a * b : Matrix.GeneralLinearGroup n A) : Matrix n n A) * J *
    ((a * b : Matrix.GeneralLinearGroup n A) : Matrix n n A) = J
  rw [Units.val_mul, cT_mul]
  calc _ = UpperTheory.Reformulated.B.Yzd4.cT σ (b : Matrix n n A) *
        (UpperTheory.Reformulated.B.Yzd4.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha', hb']

theorem UpperTheory.Reformulated.B.Yzd4.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
      (σ :
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
      (J : Matrix n n A),
      @Eq (Matrix n n A)
        (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
            (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
              (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
              (@Units.val (Matrix n n A)
                (@Semiring.toMonoid (Matrix n n A)
                  (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                (@OfNat.ofNat
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (nat_lit 1)
                  (@One.toOfNat1
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@MulOne.toOne
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@MulOneClass.toMulOne
                        (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@Monoid.toMulOneClass
                          (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@DivInvMonoid.toMonoid
                            (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                            (@Group.toDivInvMonoid
                              (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                              (@Units.instGroup (Matrix n n A)
                                (@Semiring.toMonoid (Matrix n n A)
                                  (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                                    inst_1 inst_2))))))))))))
            J)
          (@Units.val (Matrix n n A)
            (@Semiring.toMonoid (Matrix n n A)
              (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
            (@OfNat.ofNat
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (nat_lit 1)
              (@One.toOfNat1
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@MulOne.toOne
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@DivInvMonoid.toMonoid
                        (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                        (@Group.toDivInvMonoid
                          (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                          (@Units.instGroup (Matrix n n A)
                            (@Semiring.toMonoid (Matrix n n A)
                              (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                                inst_2))))))))))))
        J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Yzd4.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
      (σ :
        @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
      (J : Matrix n n A)
      {g : @Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (Set
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
            @Eq (Matrix n n A)
              (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                  (@Distrib.toMul A
                    (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                    (@Units.val (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                      g))
                  J)
                (@Units.val (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                  g))
              J)
          g →
        @Membership.mem
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (Set
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
            @Eq (Matrix n n A)
              (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                  (@Distrib.toMul A
                    (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                    (@Units.val (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                      g))
                  J)
                (@Units.val (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                  g))
              J)
          (@Inv.inv
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@InvOneClass.toInv
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@DivInvOneMonoid.toInvOneClass
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@DivisionMonoid.toDivInvOneMonoid
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@Group.toDivisionMonoid
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Units.instGroup (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                          inst_2)))))))
            g) := by
  intro A _ n _ _ σ J g hg
  have hg' : UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  change UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) * J *
    ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = J
  have h1 : (g : Matrix n n A) * ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = 1 :=
    Units.mul_inv g
  have h2 : UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
      UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) = 1 := by
    rw [← cT_mul, h1, cT_one]
  calc _ = UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
        (UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) := by rw [hg']
    _ = (UpperTheory.Reformulated.B.Yzd4.cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
        UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A)) * J *
        ((g : Matrix n n A) * ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.Yzd4.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} →
          [inst_1 : Fintype n] →
            [inst_2 : DecidableEq n] →
              @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) →
                Matrix n n A →
                  @Subgroup
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Units.instGroup (Matrix n n A)
                      (@Semiring.toMonoid (Matrix n n A)
                        (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                          inst_2))) :=
    fun {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
        (σ :
          @RingHom A A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
        (J : Matrix n n A) ↦
      @Subgroup.mk
        (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
        (@Units.instGroup (Matrix n n A)
          (@Semiring.toMonoid (Matrix n n A)
            (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2)))
        (@Submonoid.mk
          (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
          (@Monoid.toMulOneClass
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@DivInvMonoid.toMonoid
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@Group.toDivInvMonoid
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@Units.instGroup (Matrix n n A)
                  (@Semiring.toMonoid (Matrix n n A)
                    (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))))))
          (@Subsemigroup.mk
            (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@MulOne.toMul
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                (@Monoid.toMulOneClass
                  (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                  (@DivInvMonoid.toMonoid
                    (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                    (@Group.toDivInvMonoid
                      (@Matrix.GeneralLinearGroup n A inst_2 inst_1
                        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
                      (@Units.instGroup (Matrix n n A)
                        (@Semiring.toMonoid (Matrix n n A)
                          (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                            inst_2))))))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n A inst_2 inst_1 (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n A inst_2 inst_1
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))) ↦
              @Eq (Matrix n n A)
                (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                    (@Distrib.toMul A
                      (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                  (@HMul.hMul (Matrix n n A) (Matrix n n A) (Matrix n n A)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid n n n A inst_1
                      (@Distrib.toMul A
                        (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
                    (@UpperTheory.Reformulated.B.Yzd4.cT A inst σ n n
                      (@Units.val (Matrix n n A)
                        (@Semiring.toMonoid (Matrix n n A)
                          (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1
                            inst_2))
                        g))
                    J)
                  (@Units.val (Matrix n n A)
                    (@Semiring.toMonoid (Matrix n n A)
                      (@Matrix.semiring n A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) inst_1 inst_2))
                    g))
                J)
            (@UpperTheory.Reformulated.B.Yzd4.aux2 A inst n inst_1 inst_2 σ J))
          (@UpperTheory.Reformulated.B.Yzd4.aux3 A inst n inst_1 inst_2 σ J))
        (@UpperTheory.Reformulated.B.Yzd4.aux4 A inst n inst_1 inst_2 σ J)

theorem UpperTheory.Reformulated.B.Yzd4.aux6 :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra F R],
      SMulCommClass F F R := by
  intro F _ R _ _
  exact inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.aux7 :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra F R],
      IsScalarTower F F R := by
  intro F _ R _ _
  exact inferInstance

noncomputable def UpperTheory.Reformulated.B.Yzd4.sigR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 : Algebra F R] →
                  (E →ₐ[F] E) → TensorProduct F R E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
        (σ : E →ₐ[F] E) =>
      (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

theorem UpperTheory.Reformulated.B.Yzd4.aux9 :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra F R],
      SMulCommClass F R R := by
  intro F _ R _ _
  exact inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.laurent_T_neg_one_mul_T_one :
    ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra F R],
      IsScalarTower F R R := by
  intro F _ R _ _
  exact inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.aux11 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E],
      SMulCommClass F E E := by
  intro F E _ _ _
  exact inferInstance

theorem UpperTheory.Reformulated.B.Yzd4.aux12 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E],
      IsScalarTower F E E := by
  intro F E _ _ _
  exact inferInstance

noncomputable def UpperTheory.Reformulated.B.Yzd4.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] →
            (R : Type) →
              [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] =>
      Algebra.TensorProduct.includeRight.toRingHom

noncomputable def UpperTheory.Reformulated.B.Yzd4.JR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 : Algebra F R] →
                  {M : ℕ} →
                    Matrix (Fin M) (Fin M) E → Matrix (Fin M) (Fin M) (TensorProduct F R E) :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
        {M : ℕ} (J : Matrix (Fin M) (Fin M) E) =>
      J.map ⇑(UpperTheory.Reformulated.B.Yzd4.inclR R)

noncomputable def UpperTheory.Reformulated.B.Yzd4.HR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 : Algebra F R] →
                  (E →ₐ[F] E) →
                    {M : ℕ} →
                      Matrix (Fin M) (Fin M) E → Subgroup (GL (Fin M) (TensorProduct F R E)) :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
        (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) =>
      UpperTheory.Reformulated.B.Yzd4.UJ (UpperTheory.Reformulated.B.Yzd4.sigR R σ)
        (UpperTheory.Reformulated.B.Yzd4.JR R J)

noncomputable def UpperTheory.Reformulated.B.Yzd4.HA :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [Algebra F R] → (E →ₐ[F] E) → {M : ℕ} → Matrix (Fin M) (Fin M) E → Type :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
        (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) =>
      ↥(UpperTheory.Reformulated.B.Yzd4.HR R σ J)

noncomputable def UpperTheory.Reformulated.B.Yzd4.topTens :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 : Algebra F R] →
                  [TopologicalSpace R] → TopologicalSpace (TensorProduct F R E) :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
        [TopologicalSpace R] =>
      moduleTopology R (TensorProduct F R E)

noncomputable def UpperTheory.Reformulated.B.Yzd4.d18 :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  (σ :
                      @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2 inst_2) →
                    {M : Nat} →
                      (J : Matrix (Fin M) (Fin M) E) →
                        [TopologicalSpace R] →
                          Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) → Prop :=
    fun {F E : Type} [inst : Field F] [inst_1 : Field E]
        [inst_2 :
          @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
        (R : Type) [inst_3 : CommRing R]
        [inst_4 :
          @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))]
        (σ :
          @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
        {M : Nat} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
        (s : Set ↥(@UpperTheory.Reformulated.B.Yzd4.HR F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)) ↦
      ∃ (t :
        Set
          (@Matrix.GeneralLinearGroup (Fin M)
            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
              (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2))
            (instDecidableEqFin M) (Fin.fintype M)
            (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2))),
        And
          (@IsOpen
            (@Matrix.GeneralLinearGroup (Fin M)
              (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2))
              (instDecidableEqFin M) (Fin.fintype M)
              (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2))
            (@Units.instTopologicalSpaceUnits
              (Matrix (Fin M) (Fin M)
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                  (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                    inst_2)))
              (@instTopologicalSpaceMatrix (Fin M) (Fin M)
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                  (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                    inst_2))
                (@UpperTheory.Reformulated.B.Yzd4.topTens F E inst inst_1 inst_2 R inst_3 inst_4 inst_5))
              (@Semiring.toMonoid
                (Matrix (Fin M) (Fin M)
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                    (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                    (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2)))
                (@Matrix.semiring (Fin M)
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                    (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                    (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2))
                  (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)
                  (Fin.fintype M) (instDecidableEqFin M))))
            t)
          (@Eq (Set ↥(@UpperTheory.Reformulated.B.Yzd4.HR F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))
            (@Set.preimage (↥(@UpperTheory.Reformulated.B.Yzd4.HR F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))
              (@Matrix.GeneralLinearGroup (Fin M)
                (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                  (@Semiring.toAddCommMonoid E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                  (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                  (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                    inst_2))
                (instDecidableEqFin M) (Fin.fintype M)
                (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2))
              (@Subtype.val
                (@Matrix.GeneralLinearGroup (Fin M)
                  (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                    (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                    (@Semiring.toAddCommMonoid E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                    (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                    (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2))
                  (instDecidableEqFin M) (Fin.fintype M)
                  (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                    inst_2))
                fun
                  (x :
                    @Matrix.GeneralLinearGroup (Fin M)
                      (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Semiring.toAddCommMonoid E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (instDecidableEqFin M) (Fin.fintype M)
                      (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2)) ↦
                @Membership.mem
                  (@Matrix.GeneralLinearGroup (Fin M)
                    (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                      (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                      (@Semiring.toAddCommMonoid E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                      (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                      (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2))
                    (instDecidableEqFin M) (Fin.fintype M)
                    (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                      inst_2))
                  (@Subgroup
                    (@Matrix.GeneralLinearGroup (Fin M)
                      (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Semiring.toAddCommMonoid E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (instDecidableEqFin M) (Fin.fintype M)
                      (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2))
                    (@Units.instGroup
                      (Matrix (Fin M) (Fin M)
                        (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                          (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                          (@Semiring.toAddCommMonoid E
                            (@DivisionSemiring.toSemiring E
                              (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                          (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                            inst_2)))
                      (@Semiring.toMonoid
                        (Matrix (Fin M) (Fin M)
                          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                            (@Semiring.toAddCommMonoid E
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                            (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2)))
                        (@Matrix.semiring (Fin M)
                          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                            (@Semiring.toAddCommMonoid E
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                            (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2))
                          (@Algebra.TensorProduct.instSemiring F R E
                            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                            inst_2)
                          (Fin.fintype M) (instDecidableEqFin M)))))
                  (@SetLike.instMembership
                    (@Subgroup
                      (@Matrix.GeneralLinearGroup (Fin M)
                        (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                          (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                          (@Semiring.toAddCommMonoid E
                            (@DivisionSemiring.toSemiring E
                              (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                          (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                            inst_2))
                        (instDecidableEqFin M) (Fin.fintype M)
                        (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (@Units.instGroup
                        (Matrix (Fin M) (Fin M)
                          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                            (@Semiring.toAddCommMonoid E
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                            (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2)))
                        (@Semiring.toMonoid
                          (Matrix (Fin M) (Fin M)
                            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                              (@Semiring.toAddCommMonoid E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                              (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                inst_2)))
                          (@Matrix.semiring (Fin M)
                            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                              (@Semiring.toAddCommMonoid E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                              (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                inst_2))
                            (@Algebra.TensorProduct.instSemiring F R E
                              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2)
                            (Fin.fintype M) (instDecidableEqFin M)))))
                    (@Matrix.GeneralLinearGroup (Fin M)
                      (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                        (@Semiring.toAddCommMonoid E
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                        (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                        (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (instDecidableEqFin M) (Fin.fintype M)
                      (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2))
                    (@Subgroup.instSetLike
                      (@Matrix.GeneralLinearGroup (Fin M)
                        (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                          (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                          (@Semiring.toAddCommMonoid E
                            (@DivisionSemiring.toSemiring E
                              (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                          (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                            inst_2))
                        (instDecidableEqFin M) (Fin.fintype M)
                        (@Algebra.TensorProduct.instSemiring F R E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                          inst_2))
                      (@Units.instGroup
                        (Matrix (Fin M) (Fin M)
                          (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                            (@Semiring.toAddCommMonoid E
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                            (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                            (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2)))
                        (@Semiring.toMonoid
                          (Matrix (Fin M) (Fin M)
                            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                              (@Semiring.toAddCommMonoid E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                              (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                inst_2)))
                          (@Matrix.semiring (Fin M)
                            (@TensorProduct F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) R E
                              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)))
                              (@Semiring.toAddCommMonoid E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
                              (@Algebra.toModule F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4)
                              (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                                inst_2))
                            (@Algebra.TensorProduct.instSemiring F R E
                              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3)) inst_4
                              (@DivisionSemiring.toSemiring E
                                (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                              inst_2)
                            (Fin.fintype M) (instDecidableEqFin M))))))
                  (@UpperTheory.Reformulated.B.Yzd4.HR F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) x)
              t)
            s)

theorem UpperTheory.Reformulated.B.Yzd4.blockM_one_partner_eq_one :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      (R : Type) [inst_3 : CommRing R]
      [inst_4 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      {M : Nat} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R],
      @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5
        (@Set.univ (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)) := by
  intro F E _ _ _ R _ _ σ M J _
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  exact ⟨Set.univ, isOpen_univ, rfl⟩

theorem UpperTheory.Reformulated.B.Yzd4.blockM_mul_alt :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (R : Type)
      [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
      (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
      (s t : Set (UpperTheory.Reformulated.B.Yzd4.HA R σ J)),
      UpperTheory.Reformulated.B.Yzd4.d18 R σ J s →
        UpperTheory.Reformulated.B.Yzd4.d18 R σ J t →
          UpperTheory.Reformulated.B.Yzd4.d18 R σ J (s ∩ t) := by
  intro F E _ _ _ R _ _ σ M J _ s t hs ht
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a ∩ b, ha.inter hb, rfl⟩

theorem UpperTheory.Reformulated.B.Yzd4.conj_invariant_character_mem :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      (R : Type) [inst_3 : CommRing R]
      [inst_4 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      {M : Nat} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
      (s : Set (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))),
      (∀ (t : Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)),
          @Membership.mem (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))
              (Set (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J)))
              (@Set.instMembership (Set (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J))) s t →
            @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5 t) →
        @UpperTheory.Reformulated.B.Yzd4.d18 F E inst inst_1 inst_2 R inst_3 inst_4 σ M J inst_5
          (@Set.sUnion (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) s) := by
  intro F E _ _ _ R _ _ σ M J _ s hs
  letI : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  refine ⟨⋃₀ {u : Set (Matrix.GeneralLinearGroup (Fin M) (TensorProduct F R E)) |
    IsOpen u ∧ Subtype.val ⁻¹' u ∈ s}, isOpen_sUnion (fun u hu => hu.1), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_sUnion]
  constructor
  · rintro ⟨u, ⟨_, hu⟩, hx⟩
    exact ⟨_, hu, hx⟩
  · rintro ⟨t, ht, hx⟩
    obtain ⟨u, hu, rfl⟩ := hs t ht
    exact ⟨u, ⟨hu, ht⟩, hx⟩

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 :
              @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            (R : Type) →
              [inst_3 : CommRing R] →
                [inst_4 :
                    @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_3))] →
                  (σ :
                      @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
                        inst_2 inst_2) →
                    {M : Nat} →
                      (J : Matrix (Fin M) (Fin M) E) →
                        [TopologicalSpace R] →
                          TopologicalSpace (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_3 inst_4 σ M J) :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
        (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] =>
      { IsOpen := UpperTheory.Reformulated.B.Yzd4.d18 R σ J,
        isOpen_univ := UpperTheory.Reformulated.B.Yzd4.blockM_one_partner_eq_one R σ J,
        isOpen_inter := UpperTheory.Reformulated.B.Yzd4.blockM_mul_alt R σ J,
        isOpen_sUnion := UpperTheory.Reformulated.B.Yzd4.conj_invariant_character_mem R σ J }
attribute [local instance] UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA

private theorem closed_UJ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    (J : Matrix n n A) :
    IsClosed ((UpperTheory.Reformulated.B.Yzd4.UJ σ J : Subgroup (Matrix.GeneralLinearGroup n A)) :
      Set (Matrix.GeneralLinearGroup n A)) := by
  have hv : Continuous (fun g : Matrix.GeneralLinearGroup n A => (g : Matrix n n A)) :=
    Units.continuous_val
  have hc : Continuous (fun g : Matrix.GeneralLinearGroup n A =>
      UpperTheory.Reformulated.B.Yzd4.cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
    simp only [UpperTheory.Reformulated.B.Yzd4.cT]
    exact ((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

private theorem lcsc_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {n : Type} [Fintype n]
    [DecidableEq n] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n A) ∧
      SecondCountableTopology (Matrix.GeneralLinearGroup n A) ∧
      T2Space (Matrix.GeneralLinearGroup n A) := by
  haveI : LocallyCompactSpace (Matrix n n A) := inferInstanceAs (LocallyCompactSpace (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A) :=
    inferInstanceAs (SecondCountableTopology (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have he : Topology.IsClosedEmbedding (Units.embedProduct (Matrix n n A)) :=
    Units.isClosedEmbedding_embedProduct
  exact ⟨he.locallyCompactSpace, he.isEmbedding.secondCountableTopology, he.isEmbedding.t2Space⟩

private theorem lcsc_sub {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H :=
  ⟨hH.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

private theorem props_of_free {R D : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [Ring D] [Algebra R D]
    {ι : Type} [Fintype ι] (B : Module.Basis ι R D) [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] :
    IsTopologicalRing D ∧ LocallyCompactSpace D ∧ SecondCountableTopology D ∧ T2Space D := by
  have hr := IsModuleTopology.isTopologicalRing R D
  haveI := IsModuleTopology.toContinuousAdd R D
  let e := B.equivFun
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : D ≃ₜ (ι → R) := { toEquiv := e.toEquiv, continuous_toFun := c1, continuous_invFun := c2 }
  exact ⟨hr, h.isClosedEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology,
    h.isEmbedding.t2Space⟩

private theorem tens_props (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [TopologicalSpace (TensorProduct F R E)] [IsModuleTopology R (TensorProduct F R E)] :
    IsTopologicalRing (TensorProduct F R E) ∧ LocallyCompactSpace (TensorProduct F R E) ∧
      SecondCountableTopology (TensorProduct F R E) ∧ T2Space (TensorProduct F R E) :=
  props_of_free (Algebra.TensorProduct.basis R (Module.finBasis F E))

private theorem sigR_continuous {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace (TensorProduct F R E)]
    [IsModuleTopology R (TensorProduct F R E)] (σ : E →ₐ[F] E) :
    Continuous (UpperTheory.Reformulated.B.Yzd4.sigR R σ) := by
  haveI := IsModuleTopology.toContinuousAdd R (TensorProduct F R E)
  have h : (⇑(UpperTheory.Reformulated.B.Yzd4.sigR R σ) : TensorProduct F R E → TensorProduct F R E) =
      ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [UpperTheory.Reformulated.B.Yzd4.sigR]
    | add a b ha hb => simp [map_add, ha, hb]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

theorem UpperTheory.Reformulated.B.Yzd4.lcsc_HA :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
      [inst_2 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
      [@FiniteDimensional F E (@Field.toDivisionRing F inst)
          (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_1)))
          (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2)]
      (R : Type) [inst_4 : CommRing R]
      [inst_5 :
        @Algebra F R (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_4))]
      [inst_6 : TopologicalSpace R]
      [@IsTopologicalRing R inst_6
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing R
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing R (@CommRing.toNonUnitalCommRing R inst_4)))]
      [@LocallyCompactSpace R inst_6] [@SecondCountableTopology R inst_6] [@T2Space R inst_6]
      (σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))) inst_2 inst_2)
      (M : Nat) (J : Matrix (Fin M) (Fin M) E),
      And
        (@LocallyCompactSpace (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
          (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
        (And
          (@SecondCountableTopology (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))
          (@T2Space (@UpperTheory.Reformulated.B.Yzd4.HA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J)
            (@UpperTheory.Reformulated.B.Yzd4.instTopologicalSpaceHA F E inst inst_1 inst_2 R inst_4 inst_5 σ M J inst_6))) := by
  intro F E _ _ _ _ R _ _ _ _ _ _ _ σ M J
  letI τ : TopologicalSpace (TensorProduct F R E) := UpperTheory.Reformulated.B.Yzd4.topTens R
  haveI hm : IsModuleTopology R (TensorProduct F R E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := tens_props F E R
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g1, g2, g3⟩ := lcsc_GL (A := TensorProduct F R E) (n := Fin M)
  haveI := g1
  haveI := g2
  haveI := g3
  have hc := closed_UJ (UpperTheory.Reformulated.B.Yzd4.sigR R σ) (sigR_continuous R σ) (UpperTheory.Reformulated.B.Yzd4.JR R J)
  exact lcsc_sub _ hc
