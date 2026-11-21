import Mathlib

noncomputable def UpperTheory.Reformulated.B.StandardLattice.pZ :
    Nat → @Ideal Int Int.instSemiring :=
    fun (l : Nat) ↦
      @Ideal.span Int Int.instSemiring
        (@Singleton.singleton Int (Set Int) (@Set.instSingletonSet Int) (@Nat.cast Int instNatCastInt l))

theorem UpperTheory.Reformulated.B.StandardLattice.aux2 :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)], @Ideal.IsPrime Int Int.instSemiring (UpperTheory.Reformulated.B.StandardLattice.pZ l) := by
  intro l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.Ml :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            @Submonoid (@NumberField.RingOfIntegers K inst)
              (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] ↦
      @Algebra.algebraMapSubmonoid Int Int.instCommSemiring (@NumberField.RingOfIntegers K inst)
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@Ring.toIntAlgebra (@NumberField.RingOfIntegers K inst)
          (@CommRing.toRing (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@Ideal.primeCompl Int Int.instSemiring (UpperTheory.Reformulated.B.StandardLattice.pZ l) (@UpperTheory.Reformulated.B.StandardLattice.aux2 l hl))

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.Rl :
    (l : Nat) → [hl : Fact (Nat.Prime l)] → (K : Type) → [Field K] → Type :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] ↦
      @Localization (@NumberField.RingOfIntegers K inst)
        (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
        (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)

theorem UpperTheory.Reformulated.B.StandardLattice.aux5 :
    ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K],
      IsLocalization (UpperTheory.Reformulated.B.StandardLattice.Ml l K)
        (Localization (UpperTheory.Reformulated.B.StandardLattice.Ml l K)) := by
  intro l hl K inst
  exact Localization.isLocalization

theorem UpperTheory.Reformulated.B.StandardLattice.aux6 :
    ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [NumberField K]
      (y : ↥(UpperTheory.Reformulated.B.StandardLattice.Ml l K)),
      IsUnit ((algebraMap (NumberField.RingOfIntegers K) K) ↑y) := by
  intro l hl K inst _ y
  obtain ⟨y, n, hn, rfl⟩ := y
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Ideal.zero_mem _)
  refine isUnit_iff_ne_zero.mpr ?_
  simpa using hn0

noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlToK :
    (l : ℕ) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [NumberField K] → UpperTheory.Reformulated.B.StandardLattice.Rl l K →+* K :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K] =>
      IsLocalization.lift (UpperTheory.Reformulated.B.StandardLattice.aux6 l K)

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlAlgebra :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [@NumberField K inst] →
              @Algebra (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) K
                (@OreLocalization.instCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                  (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K] =>
      (UpperTheory.Reformulated.B.StandardLattice.rlToK l K).toAlgebra
attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.rlAlgebra

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlModule :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [@NumberField K inst] →
              (V : Type) →
                [inst_2 : AddCommGroup V] →
                  [@_root_.Module K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_2)] →
                    @_root_.Module (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
                      (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                        (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
                      (@AddCommGroup.toAddCommMonoid V inst_2) :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K] (V : Type)
        [AddCommGroup V] [Module K V] =>
      Module.compHom V (algebraMap (UpperTheory.Reformulated.B.StandardLattice.Rl l K) K)

noncomputable def UpperTheory.Reformulated.B.StandardLattice.atL :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [inst_1 : @NumberField K inst] →
              {V : Type} →
                [inst_2 : AddCommGroup V] →
                  [inst_3 :
                      @_root_.Module K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_2)] →
                    [inst_4 :
                        @_root_.Module (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2)] →
                      @Submodule (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4 →
                        @Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
                          (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                (@NumberField.instCommRingRingOfIntegers K inst)))
                            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                            (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                              (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                                (@NumberField.instCommRingRingOfIntegers K inst))
                              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2)
                          (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] {V : Type}
        [inst_2 : AddCommGroup V]
        [inst_3 :
          @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2)]
        [inst_4 :
          @_root_.Module (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2)]
        (L :
          @Submodule (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) inst_4) ↦
      @Submodule.span (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
        (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
        (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3)
        (@SetLike.coe
          (@Submodule (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
          V
          (@Submodule.setLike (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
          L)

theorem UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] {V : Type}
      [inst_2 : AddCommGroup V]
      [inst_3 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2)]
      [inst_4 :
        @_root_.Module (@NumberField.RingOfIntegers K inst) V
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2)]
      [@IsScalarTower (@NumberField.RingOfIntegers K inst) K V
          (@Algebra.toSMul (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
          (@SMulZeroClass.toSMul K V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
            (@DistribSMul.toSMulZeroClass K V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
              (@DistribMulAction.toDistribSMul K V
                (@Semiring.toMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                (@Module.toDistribMulAction K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_3))))
          (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
            (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
              (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) V
                (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4))))]
      {L :
        @Submodule (@NumberField.RingOfIntegers K inst) V
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4}
      {x : V},
      Iff
        (@Membership.mem V
          (@Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
            (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
              (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3))
          (@SetLike.instMembership
            (@Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
              (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
              (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3))
            V
            (@Submodule.setLike (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
              (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
              (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3)))
          (@UpperTheory.Reformulated.B.StandardLattice.atL l hl K inst inst_1 V inst_2 inst_3 inst_4 L) x)
        (∃ (s : @NumberField.RingOfIntegers K inst),
          And
            (@Membership.mem (@NumberField.RingOfIntegers K inst)
              (@Submonoid (@NumberField.RingOfIntegers K inst)
                (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                  (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                        (@NumberField.instCommRingRingOfIntegers K inst))))))
              (@SetLike.instMembership
                (@Submonoid (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst))))))
                (@NumberField.RingOfIntegers K inst)
                (@Submonoid.instSetLike (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst)))))))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst) s)
            (@Membership.mem V
              (@Submodule (@NumberField.RingOfIntegers K inst) V
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
              (@SetLike.instMembership
                (@Submodule (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
                V
                (@Submodule.setLike (@NumberField.RingOfIntegers K inst) V
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) inst_4))
              L
              (@HSMul.hSMul (@NumberField.RingOfIntegers K inst) V V
                (@instHSMul (@NumberField.RingOfIntegers K inst) V
                  (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) V
                    (@AddZero.toZero V
                      (@AddZeroClass.toAddZero V
                        (@AddMonoid.toAddZeroClass V
                          (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))))
                    (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) V
                      (@AddMonoid.toAddZeroClass V
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2))))
                      (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) V
                        (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst))))
                        (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_2)))
                        (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)))))
                s x))) := by
  intro l hl K inst inst_1 V inst_2 inst_3 inst_4 tower L x
  letI := UpperTheory.Reformulated.B.StandardLattice.rlModule l K V
  have hact : ∀ (r : NumberField.RingOfIntegers K) (v : V),
      (algebraMap (NumberField.RingOfIntegers K) (UpperTheory.Reformulated.B.StandardLattice.Rl l K) r) • v = r • v := by
    intro r v
    change UpperTheory.Reformulated.B.StandardLattice.rlToK l K (algebraMap _ _ r) • v = r • v
    unfold UpperTheory.Reformulated.B.StandardLattice.rlToK
    rw [IsLocalization.lift_eq, algebraMap_smul]
  haveI : IsScalarTower (NumberField.RingOfIntegers K) (UpperTheory.Reformulated.B.StandardLattice.Rl l K) V :=
    IsScalarTower.of_algebraMap_smul hact
  unfold UpperTheory.Reformulated.B.StandardLattice.atL
  rw [IsLocalization.mem_span_iff (UpperTheory.Reformulated.B.StandardLattice.Ml l K), Submodule.span_eq]
  constructor
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← hact, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    exact hy
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← hact, smul_smul]
    have := IsLocalization.mk'_spec (UpperTheory.Reformulated.B.StandardLattice.Rl l K) (1 : NumberField.RingOfIntegers K)
      (⟨s, hs⟩ : UpperTheory.Reformulated.B.StandardLattice.Ml l K)
    rw [this, map_one, one_smul]
