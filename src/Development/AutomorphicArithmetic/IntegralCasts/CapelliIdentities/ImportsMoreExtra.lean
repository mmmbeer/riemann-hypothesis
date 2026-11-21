import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

theorem UpperTheory.Reformulated.B.Qh15.aux1 :
    ∀ {A : Type} [inst : CommRing A],
      @SMulCommClass A A A
        (@Algebra.toSMul A A (@CommRing.toCommSemiring A inst)
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)) (@Algebra.id A (@CommRing.toCommSemiring A inst)))
        (@instSMulOfMul A
          (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))) := by
  intro A _
  infer_instance

theorem UpperTheory.Reformulated.B.Qh15.aux2 :
    ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A]
      (κ :
        @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
          (@MulOneClass.toMulOne
            (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@Units.instMulOneClass A
              (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))),
      @Eq
        (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
        (@HSMul.hSMul A
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@instHSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@NonUnitalNonAssocSemiring.toDistribSMul A
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
              (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
          (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@DFunLike.coe
              (@MonoidHom G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              G
              (fun (x : G) ↦
                @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MonoidHom.instFunLike G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              κ
              (@OfNat.ofNat G (nat_lit 1)
                (@One.toOfNat1 G
                  (@MulOne.toOne G
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)))))))))
          (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
        (@OfNat.ofNat
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (nat_lit 1)
          (@One.toOfNat1
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOne.toOne
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulOneClass.toMulOne
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulZeroOneClass.toMulOneClass
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@instMulZeroOneClassOfSemiring
                    (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@RingHom.id A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))))))) := by
  intro G A _ _ κ
  ext
  simp

theorem UpperTheory.Reformulated.B.Qh15.aux3 :
    ∀ {G A : Type} [inst : Group G] [inst_1 : CommRing A]
      (κ :
        @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
          (@MulOneClass.toMulOne
            (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@Units.instMulOneClass A
              (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
      (g h : G),
      @Eq
        (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
        (@HSMul.hSMul A
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@instHSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@NonUnitalNonAssocSemiring.toDistribSMul A
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
              (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
          (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@DFunLike.coe
              (@MonoidHom G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              G
              (fun (x : G) ↦
                @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MonoidHom.instFunLike G
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulOneClass.toMulOne G
                  (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                (@MulOneClass.toMulOne
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Units.instMulOneClass A
                    (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
              κ
              (@HMul.hMul G G G
                (@instHMul G
                  (@MulOne.toMul G
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))))
                g h)))
          (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
        (@HMul.hMul
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@instHMul
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOne.toMul
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulOneClass.toMulOne
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MulZeroOneClass.toMulOneClass
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@instMulZeroOneClassOfSemiring
                    (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@RingHom.id A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                      (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                      (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))))))
          (@HSMul.hSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@instHSMul A
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@NonUnitalNonAssocSemiring.toDistribSMul A
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
                (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
            (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@DFunLike.coe
                (@MonoidHom G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                G
                (fun (x : G) ↦
                  @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MonoidHom.instFunLike G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                κ g))
            (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
          (@HSMul.hSMul A
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@instHSMul A
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@NonUnitalNonAssocSemiring.toDistribSMul A
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
                (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
            (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@DFunLike.coe
                (@MonoidHom G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                G
                (fun (x : G) ↦
                  @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@MonoidHom.instFunLike G
                  (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MulOneClass.toMulOne G
                    (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                  (@MulOneClass.toMulOne
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@Units.instMulOneClass A
                      (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                κ h))
            (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))) := by
  intro G A _ _ κ g h
  ext
  simp [mul_comm]

noncomputable def UpperTheory.Reformulated.B.Qh15.chRep :
    {G A : Type} →
      [inst : Group G] →
        [inst_1 : CommRing A] →
          @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
              (@MulOneClass.toMulOne
                (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@Units.instMulOneClass A
                  (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))) →
            @Representation A G A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))) :=
    fun {G A : Type} [inst : Group G] [inst_1 : CommRing A]
        (κ :
          @MonoidHom G (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
            (@MulOneClass.toMulOne
              (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@Units.instMulOneClass A
                (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))) ↦
      @MonoidHom.mk G
        (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
          (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
        (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
        (@MulOneClass.toMulOne
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulZeroOneClass.toMulOneClass
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@instMulZeroOneClassOfSemiring
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))))
        (@OneHom.mk G
          (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
            (@RingHom.id A
              (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
            (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
          (@MulOne.toOne G
            (@MulOneClass.toMulOne G (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst)))))
          (@MulOne.toOne
            (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
              (@RingHom.id A
                (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
              (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
            (@MulOneClass.toMulOne
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@MulZeroOneClass.toMulOneClass
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@instMulZeroOneClassOfSemiring
                  (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@RingHom.id A
                      (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@Module.End.instSemiring A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                    (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                    (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))))
          (fun (g : G) ↦
            @HSMul.hSMul A
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@RingHom.id A
                  (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
              (@instHSMul A
                (@LinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  A A (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                (@LinearMap.instSMul A A A A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                  (@RingHom.id A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@NonUnitalNonAssocSemiring.toDistribSMul A
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring A
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing A
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing A (@CommRing.toNonUnitalCommRing A inst_1)))))
                  (@UpperTheory.Reformulated.B.Qh15.aux1 A inst_1)))
              (@Units.val A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@DFunLike.coe
                  (@MonoidHom G
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@MulOneClass.toMulOne
                      (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      (@Units.instMulOneClass A
                        (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                  G
                  (fun (x : G) ↦
                    @Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                  (@MonoidHom.instFunLike G
                    (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst))))
                    (@MulOneClass.toMulOne
                      (@Units A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))
                      (@Units.instMulOneClass A
                        (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))))))
                  κ g))
              (@LinearMap.id A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1))
                (@Semiring.toAddCommMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))
                (@Semiring.toModule A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst_1)))))
          (@UpperTheory.Reformulated.B.Qh15.aux2 G A inst inst_1 κ))
        (@UpperTheory.Reformulated.B.Qh15.aux3 G A inst inst_1 κ)

theorem UpperTheory.Reformulated.B.Qh15.act_mul :
    ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp] [inst_2 : Field K₀]
      [inst_3 : Field K] [inst_4 : Algebra Qp K₀] [inst_5 : Algebra Qp K]
      [inst_6 : Algebra K₀ K] [inst_7 : IsScalarTower Qp K₀ K] {B BdR : Type}
      [inst_8 : CommRing B] [inst_9 : CommRing BdR] [inst_10 : Algebra Qp B]
      [inst_11 : Algebra K₀ B] [inst_12 : IsScalarTower Qp K₀ B] [inst_13 : Algebra Qp BdR]
      [inst_14 : Algebra K₀ BdR] [inst_15 : Algebra K BdR] [inst_16 : IsScalarTower Qp K BdR]
      [inst_17 : IsScalarTower K₀ K BdR] [inst_18 : IsScalarTower Qp K₀ BdR]
      (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {E : Type}
      [inst_19 : Field E] [inst_20 : Algebra Qp E] (κ : G →* Eˣ) (g : G)
      (x y : TensorProduct Qp E B),
      (Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep κ)
              g)
            x *
          (Formalism.WeaklyAdmissibleFiltrations.actVB PD
              (UpperTheory.Reformulated.B.Qh15.chRep κ⁻¹) g)
            y =
        (Formalism.WeaklyAdmissibleFiltrations.actVB PD
            (UpperTheory.Reformulated.B.Qh15.chRep 1) g)
          (x * y) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ κ g x y
  have hch : ∀ (μ : G →* Eˣ) (a : E), UpperTheory.Reformulated.B.Qh15.chRep μ g a = (μ g : E) * a :=
    fun μ a => rfl
  have hact : ∀ (μ : G →* Eˣ) (a : E) (b : B),
      Formalism.WeaklyAdmissibleFiltrations.actVB PD (UpperTheory.Reformulated.B.Qh15.chRep μ) g (a ⊗ₜ[Qp] b) =
        ((μ g : E) * a) ⊗ₜ[Qp] PD.actB g b := by
    intro μ a b
    rw [← hch]
    rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
    | tmul c d =>
      have hu : (κ g : E) * a * ((κ⁻¹ g : E) * c) = ((1 : G →* Eˣ) g : E) * (a * c) := by
        rw [mul_mul_mul_comm, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel,
          MonoidHom.one_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, hact, hact, hact,
        Algebra.TensorProduct.tmul_mul_tmul, hu, map_mul]
