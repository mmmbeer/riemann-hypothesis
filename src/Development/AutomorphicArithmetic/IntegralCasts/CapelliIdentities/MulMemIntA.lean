import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Uc13.Af :
    (F : Type) → [inst : Field F] → [@NumberField F inst] → Type :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst] ↦
      @IsDedekindDomain.FiniteAdeleRing (@NumberField.RingOfIntegers F inst)
        (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F
        inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Uc13.Fv :
    (F : Type) →
      [inst : Field F] →
        [@NumberField F inst] →
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst) →
            Type :=
    fun (F : Type) [Field F] [NumberField F]
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

theorem UpperTheory.Reformulated.B.Uc13.aux3 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F]
      (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      SubringClass (ValuationSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletion F i))
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion F i) := by
  intro F _ _ i
  infer_instance

theorem UpperTheory.Reformulated.B.Uc13.aux4 :
    ∀ (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
      (v :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst))
      (x : F),
      @Eq (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
        (@OneHom.toFun
          (@RestrictedProduct
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @SetLike.coe
                (@ValuationSubring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@ValuationSubring.instSetLike
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
            (@Filter.cofinite
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
          (@MulOne.toOne
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))))))
          (@MulOne.toOne
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))))))
          (@MonoidHom.toOneHom
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1)))))))
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))))
            (@RingHom.toMonoidHom
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@Semiring.toNonAssocSemiring
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@Ring.toSemiring
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@RestrictedProduct.instRingCoeOfSubringClass
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (w :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                    (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
              (@Semiring.toNonAssocSemiring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@Ring.toSemiring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))
              (@RestrictedProduct.evalRingHom
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (w :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                v
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
          (@DFunLike.coe
            (@RingHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            F (fun (x : F) ↦ @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@RingHom.instFunLike F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            (@Algebra.algebraMap F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            x))
        (@OneHom.toFun
          (@RestrictedProduct
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @SetLike.coe
                (@ValuationSubring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@ValuationSubring.instSetLike
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
            (@Filter.cofinite
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
          (@MulOne.toOne
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))))))
          (@MulOne.toOne
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))))))
          (@MonoidHom.toOneHom
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@MulOneClass.toMulOne
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@MulZeroOneClass.toMulOneClass
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@NonAssocSemiring.toMulZeroOneClass
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring
                    (@RestrictedProduct
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (fun
                          (i :
                            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                        @SetLike.coe
                          (@ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@Filter.cofinite
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))))
                    (@Ring.toSemiring
                      (@RestrictedProduct
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @SetLike.coe
                            (@ValuationSubring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@ValuationSubring.instSetLike
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst))))
                      (@RestrictedProduct.instRingCoeOfSubringClass
                        (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst))
                        (fun
                            (w :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                        (@Filter.cofinite
                          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @ValuationSubring.instSetLike
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                        (fun
                            (i :
                              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                          @DivisionRing.toRing
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                              (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                            (@Field.toDivisionRing
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                        (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1)))))))
            (@MulOneClass.toMulOne
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@MulZeroOneClass.toMulOneClass
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@NonAssocSemiring.toMulZeroOneClass
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@Semiring.toNonAssocSemiring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Ring.toSemiring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))))
            (@RingHom.toMonoidHom
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@Semiring.toNonAssocSemiring
                (@RestrictedProduct
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (fun
                      (i :
                        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                    @SetLike.coe
                      (@ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@Filter.cofinite
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@Ring.toSemiring
                  (@RestrictedProduct
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @SetLike.coe
                        (@ValuationSubring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@ValuationSubring.instSetLike
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@RestrictedProduct.instRingCoeOfSubringClass
                    (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))
                    (fun
                        (w :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                    (@Filter.cofinite
                      (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @ValuationSubring.instSetLike
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                    (fun
                        (i :
                          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                      @DivisionRing.toRing
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                          (@NumberField.instCommRingRingOfIntegers F inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                        (@Field.toDivisionRing
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                            (@NumberField.instCommRingRingOfIntegers F inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                    (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
              (@Semiring.toNonAssocSemiring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@Ring.toSemiring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)))))
              (@RestrictedProduct.evalRingHom
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (w :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                v
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
          (@DFunLike.coe
            (@RingHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            F (fun (x : F) ↦ @UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@RingHom.instFunLike F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semiring.toNonAssocSemiring F
                (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
              (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                    (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))))
            (@Algebra.algebraMap F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)))
            x)) := by
  intro F _ _ v x
  rfl

noncomputable def UpperTheory.Reformulated.B.Uc13.evalV :
    (F : Type) →
      [inst : Field F] →
        [inst_1 : @NumberField F inst] →
          (v :
              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)) →
            @AlgHom F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
                  (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
              (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                  (@Field.toSemifield (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
              (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
              (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F F inst
                (@Semifield.toCommSemiring F (@Field.toSemifield F inst)) (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v
                (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))) :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
        (v :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      let __src :
        @RingHom
          (@RestrictedProduct
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
            (fun
                (i :
                  @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)) ↦
              @SetLike.coe
                (@ValuationSubring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@ValuationSubring.instSetLike
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
            (@Filter.cofinite
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
          (@Semiring.toNonAssocSemiring
            (@RestrictedProduct
              (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (fun
                  (i :
                    @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                @SetLike.coe
                  (@ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                  (@ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
              (@Filter.cofinite
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@Ring.toSemiring
              (@RestrictedProduct
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @SetLike.coe
                    (@ValuationSubring
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@ValuationSubring.instSetLike
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@RestrictedProduct.instRingCoeOfSubringClass
                (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))
                (fun
                    (w :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
                (@Filter.cofinite
                  (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @ValuationSubring.instSetLike
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
                (fun
                    (i :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)) ↦
                  @DivisionRing.toRing
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                    (@Field.toDivisionRing
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
                (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1))))
          (@Semiring.toNonAssocSemiring
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
            (@Ring.toSemiring
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
              (@DivisionRing.toRing
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                (@Field.toDivisionRing
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))) :=
        @RestrictedProduct.evalRingHom
          (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst))
          (fun
              (w :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) w)
          (@Filter.cofinite
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)))
          (fun
              (i :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @ValuationSubring
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
          (fun
              (i :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @ValuationSubring.instSetLike
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i))
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
          v
          (fun
              (i :
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)) ↦
            @DivisionRing.toRing
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
              (@Field.toDivisionRing
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) i)))
          (@UpperTheory.Reformulated.B.Uc13.aux3 F inst inst_1);
      @AlgHom.mk F (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
        (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
        (@CommSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
          (@CommRing.toCommSemiring (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1)
            (@IsDedekindDomain.instCommRingFiniteAdeleRing (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))))
        (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
          (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
            (@Field.toSemifield (@UpperTheory.Reformulated.B.Uc13.Fv F inst inst_1 v)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
        (@IsDedekindDomain.FiniteAdeleRing.instAlgebra (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1))
        (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F F inst (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@NumberField.RingOfIntegers.instAlgebra_1 F inst) (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1)
          v (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
        __src (@UpperTheory.Reformulated.B.Uc13.aux4 F inst inst_1 v)

noncomputable def UpperTheory.Reformulated.B.Uc13.intAf :
    (F : Type) → [inst : Field F] → [inst_1 : @NumberField F inst] → Set (@UpperTheory.Reformulated.B.Uc13.Af F inst inst_1) :=
    fun (F : Type) [Field F] [NumberField F] =>
      {a : UpperTheory.Reformulated.B.Uc13.Af F |
        ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
          (UpperTheory.Reformulated.B.Uc13.evalV F v) a ∈
            IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}

noncomputable def UpperTheory.Reformulated.B.Uc13.intA :
    (F E : Type) →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              AddSubgroup (TensorProduct F (UpperTheory.Reformulated.B.Uc13.Af F) E) :=
    fun (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] =>
      AddSubgroup.closure
        {y : TensorProduct F (UpperTheory.Reformulated.B.Uc13.Af F) E |
          ∃ a ∈ UpperTheory.Reformulated.B.Uc13.intAf F,
            ∃ (x : NumberField.RingOfIntegers E), y = a ⊗ₜ[F] ↑x}

private theorem UpperTheory.Reformulated.B.Uc13.intAf_mul (F : Type) [Field F] [NumberField F]
    {a b : UpperTheory.Reformulated.B.Uc13.Af F} (ha : a ∈ UpperTheory.Reformulated.B.Uc13.intAf F)
    (hb : b ∈ UpperTheory.Reformulated.B.Uc13.intAf F) : a * b ∈ UpperTheory.Reformulated.B.Uc13.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

theorem UpperTheory.Reformulated.B.Uc13.mul_mem_intA :
    ∀ (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E]
      [inst_4 : Algebra F E] {x y : TensorProduct F (UpperTheory.Reformulated.B.Uc13.Af F) E},
      x ∈ UpperTheory.Reformulated.B.Uc13.intA F E →
        y ∈ UpperTheory.Reformulated.B.Uc13.intA F E →
          x * y ∈ UpperTheory.Reformulated.B.Uc13.intA F E := by
  intro F E _ _ _ _ _ x y hx hy
  unfold UpperTheory.Reformulated.B.Uc13.intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure
      ⟨a * b, UpperTheory.Reformulated.B.Uc13.intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h
