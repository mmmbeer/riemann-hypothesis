import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.H23.Pl :
    (E : Type) → [inst : Field E] → [@NumberField E inst] → Type :=
    fun (E : Type) [inst : Field E] [@NumberField E inst] ↦
      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst)
        (@NumberField.instCommRingRingOfIntegers E inst)

@[reducible] noncomputable def UpperTheory.Reformulated.B.H23.GLw :
    {E : Type} → [inst : Field E] → [inst_1 : @NumberField E inst] → Nat → @UpperTheory.Reformulated.B.H23.Pl E inst inst_1 → Type :=
    fun {E : Type} [Field E] [NumberField E] (n : ℕ)
        (w : UpperTheory.Reformulated.B.H23.Pl E) =>
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)

theorem UpperTheory.Reformulated.B.H23.aux3 :
    ∀ (k : Type) [inst : Field k],
      @SubsemiringClass (@Subring k (@Ring.toNonAssocRing k (@CommRing.toRing k (@Field.toCommRing k inst)))) k
        (@NonAssocRing.toNonAssocSemiring k
          (@NonAssocCommRing.toNonAssocRing k (@CommRing.toNonAssocCommRing k (@Field.toCommRing k inst))))
        (@Subring.instSetLike k (@Ring.toNonAssocRing k (@CommRing.toRing k (@Field.toCommRing k inst)))) := by
  intro k _
  infer_instance

theorem UpperTheory.Reformulated.B.H23.aux4 :
    ∀ (k : Type) [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k]
      [IsNonarchimedeanLocalField k], IsLocalRing ↥(ValuativeRel.valuation k).integer := by
  intro k _ _ _ _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.H23.blk :
    {α n : Type} → {m : α → Type} → Equiv (@Sigma α fun (a : α) ↦ m a) n → n → α :=
    fun {α n : Type} {m : α → Type} (e : Equiv (@Sigma α fun (a : α) ↦ m a) n) (i : n) ↦
      @Sigma.fst α (fun (a : α) ↦ m a)
        (@DFunLike.coe (Equiv n (@Sigma α fun (a : α) ↦ m a)) n (fun (x : n) ↦ @Sigma α fun (a : α) ↦ m a)
          (@EquivLike.toFunLike (Equiv n (@Sigma α fun (a : α) ↦ m a)) n (@Sigma α fun (a : α) ↦ m a)
            (@Equiv.instEquivLike n (@Sigma α fun (a : α) ↦ m a)))
          (@Equiv.symm (@Sigma α fun (a : α) ↦ m a) n e) i)

theorem UpperTheory.Reformulated.B.H23.aux6 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n)
      {x y : @Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (Set
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
            @Matrix.BlockTriangular α n R
              (@Preorder.toLT α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
              (@MulZeroClass.toZero R
                (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              (@Units.val (Matrix n n R)
                (@Semiring.toMonoid (Matrix n n R)
                  (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                g)
              (@UpperTheory.Reformulated.B.H23.blk α n m e))
          x →
        @Membership.mem
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (Set
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
              @Matrix.BlockTriangular α n R
                (@Preorder.toLT α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
                (@MulZeroClass.toZero R
                  (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                (@Units.val (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                  g)
                (@UpperTheory.Reformulated.B.H23.blk α n m e))
            y →
          @Membership.mem
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (Set
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
              @Matrix.BlockTriangular α n R
                (@Preorder.toLT α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
                (@MulZeroClass.toZero R
                  (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                (@Units.val (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                  g)
                (@UpperTheory.Reformulated.B.H23.blk α n m e))
            (@HMul.hMul
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@instHMul
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@MulOne.toMul
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@DivInvMonoid.toMonoid
                        (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Group.toDivInvMonoid
                          (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Units.instGroup (Matrix n n R)
                            (@Semiring.toMonoid (Matrix n n R)
                              (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                                inst_3)))))))))
              x y) := by
  intro R _ α n m _ _ _ e x y hx hy
  exact Matrix.BlockTriangular.mul hx hy

theorem UpperTheory.Reformulated.B.H23.aux7 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n),
      @Membership.mem
        (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
        (Set (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@Set.instMembership
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@Set.ofPred
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          fun
            (g :
              @Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
          @Matrix.BlockTriangular α n R
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
            (@MulZeroClass.toZero R
              (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Units.val (Matrix n n R)
              (@Semiring.toMonoid (Matrix n n R)
                (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
              g)
            (@UpperTheory.Reformulated.B.H23.blk α n m e))
        (@OfNat.ofNat
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (nat_lit 1)
          (@One.toOfNat1
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@MulOne.toOne
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@Monoid.toMulOneClass
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@DivInvMonoid.toMonoid
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Group.toDivInvMonoid
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Units.instGroup (Matrix n n R)
                        (@Semiring.toMonoid (Matrix n n R)
                          (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                            inst_3)))))))))) := by
  intro R _ α n m _ _ _ e
  exact Matrix.blockTriangular_one

theorem UpperTheory.Reformulated.B.H23.aux8 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n)
      {x : @Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (Set
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
            @Matrix.BlockTriangular α n R
              (@Preorder.toLT α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
              (@MulZeroClass.toZero R
                (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              (@Units.val (Matrix n n R)
                (@Semiring.toMonoid (Matrix n n R)
                  (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                g)
              (@UpperTheory.Reformulated.B.H23.blk α n m e))
          x →
        @Membership.mem
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (Set
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
            @Matrix.BlockTriangular α n R
              (@Preorder.toLT α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
              (@MulZeroClass.toZero R
                (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              (@Units.val (Matrix n n R)
                (@Semiring.toMonoid (Matrix n n R)
                  (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                g)
              (@UpperTheory.Reformulated.B.H23.blk α n m e))
          (@Inv.inv
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@InvOneClass.toInv
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@DivInvOneMonoid.toInvOneClass
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@DivisionMonoid.toDivInvOneMonoid
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@Group.toDivisionMonoid
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Units.instGroup (Matrix n n R)
                      (@Semiring.toMonoid (Matrix n n R)
                        (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                          inst_3)))))))
            x) := by
  intro R _ α n m _ _ _ e x hx
  change Matrix.BlockTriangular (x⁻¹ : Matrix.GeneralLinearGroup n R).val _
  rw [Matrix.coe_units_inv]
  letI := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def UpperTheory.Reformulated.B.H23.parab :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [LinearOrder α] →
              [inst_2 : Fintype n] →
                [inst_3 : DecidableEq n] →
                  Equiv (@Sigma α fun (a : α) ↦ m a) n →
                    @Subgroup
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Units.instGroup (Matrix n n R)
                        (@Semiring.toMonoid (Matrix n n R)
                          (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                            inst_3))) :=
    fun (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
        [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n) ↦
      @Subgroup.mk
        (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
        (@Units.instGroup (Matrix n n R)
          (@Semiring.toMonoid (Matrix n n R)
            (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3)))
        (@Submonoid.mk
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (@Monoid.toMulOneClass
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@DivInvMonoid.toMonoid
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Group.toDivInvMonoid
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@Units.instGroup (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))))))
          (@Subsemigroup.mk
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@MulOne.toMul
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@Monoid.toMulOneClass
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@DivInvMonoid.toMonoid
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Group.toDivInvMonoid
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Units.instGroup (Matrix n n R)
                        (@Semiring.toMonoid (Matrix n n R)
                          (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                            inst_3))))))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
              @Matrix.BlockTriangular α n R
                (@Preorder.toLT α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
                (@MulZeroClass.toZero R
                  (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                (@Units.val (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                  g)
                (@UpperTheory.Reformulated.B.H23.blk α n m e))
            (@UpperTheory.Reformulated.B.H23.aux6 R inst α n m inst_1 inst_2 inst_3 e))
          (@UpperTheory.Reformulated.B.H23.aux7 R inst α n m inst_1 inst_2 inst_3 e))
        (@UpperTheory.Reformulated.B.H23.aux8 R inst α n m inst_1 inst_2 inst_3 e)

noncomputable def UpperTheory.Reformulated.B.H23.points :
    (n : Type) → Equiv (@Sigma n fun (x : n) ↦ Unit) n :=
    fun (n : Type) ↦ @Equiv.sigmaUnique n (fun (x : n) ↦ Unit) fun (a : n) ↦ PUnit.instUnique

noncomputable def UpperTheory.Reformulated.B.H23.borel :
    (R : Type) →
      [inst : CommRing R] →
        (n : Type) →
          [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n R) :=
    fun (R : Type) [inst : CommRing R] (n : Type) [inst_1 : Fintype n] [inst_2 : DecidableEq n] [inst_3 : LinearOrder n] ↦
      @UpperTheory.Reformulated.B.H23.parab R inst n n (fun (a : n) ↦ Unit) inst_3 inst_1 inst_2 (UpperTheory.Reformulated.B.H23.points n)

noncomputable def UpperTheory.Reformulated.B.H23.iwahori :
    (k : Type) →
      [inst : Field k] →
        [inst_1 : ValuativeRel k] →
          [inst_2 : TopologicalSpace k] →
            [IsNonarchimedeanLocalField k] →
              (n : Type) →
                [inst_4 : Fintype n] →
                  [inst_5 : DecidableEq n] → [LinearOrder n] → Subgroup (GL n k) :=
    fun (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
        [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] =>
      Subgroup.map
        (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
        (Subgroup.comap
          (Matrix.GeneralLinearGroup.map
            (IsLocalRing.residue ↥(ValuativeRel.valuation k).integer))
          (UpperTheory.Reformulated.B.H23.borel
            (IsLocalRing.ResidueField ↥(ValuativeRel.valuation k).integer) n))

@[reducible] noncomputable def UpperTheory.Reformulated.B.H23.complRel :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : @NumberField F inst] →
          (p :
              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)) →
            @ValuativeRel
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
              (@DivisionSemiring.toSemiring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
                (@Semifield.toDivisionSemiring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
                  (@Field.toSemifield
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)))) :=
    fun {F : Type} [Field F] [NumberField F]
        (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) =>
      ValuativeRel.ofValuation Valued.v

open IsDedekindDomain NumberField in
private theorem UpperTheory.Reformulated.B.H23.exists_global_approx {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (RingOfIntegers F)) (x : p.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ r : RingOfIntegers F,
      Valued.v (algebraMap F (p.adicCompletion F) (algebraMap (RingOfIntegers F) F r) - x) < 1 := by
  have hval : ∀ k : F, Valued.v (algebraMap F (p.adicCompletion F) k) = p.valuation F k :=
    fun k ↦ p.valuedAdicCompletion_eq_valuation' k
  have hn : {y : p.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy ↦ ?_⟩
    exact (Valuation.restrict_lt_one_iff _).mp hy
  obtain ⟨k, hk⟩ := (p.denseRange_algebraMap F).mem_nhds hn
  have hk' : Valued.v (algebraMap F (p.adicCompletion F) k - x) < 1 := hk
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hval, ← sub_add_cancel (algebraMap F (p.adicCompletion F) k) x]
    exact Valuation.map_add_le _ hk'.le hx
  obtain ⟨r, hr⟩ := p.exists_valuation_sub_lt_of_integer hk1 1
  refine ⟨r, ?_⟩
  rw [← sub_add_sub_cancel _ (algebraMap F (p.adicCompletion F) k) x]
  refine Valuation.map_add_lt _ ?_ hk'
  rw [← map_sub, hval]
  exact hr

open IsDedekindDomain NumberField in
private theorem UpperTheory.Reformulated.B.H23.finite_residueField {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (p.adicCompletionIntegers F)) := by
  have hval : ∀ k : F, Valued.v (algebraMap F (p.adicCompletion F) k) = p.valuation F k :=
    fun k ↦ p.valuedAdicCompletion_eq_valuation' k
  have hmem : ∀ y : p.adicCompletionIntegers F, Valued.v (y : p.adicCompletion F) < 1 →
      IsLocalRing.residue (p.adicCompletionIntegers F) y = 0 := by
    intro y hy
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let f : RingOfIntegers F →+* IsLocalRing.ResidueField (p.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (RingOfIntegers F) (p.adicCompletionIntegers F))
  have hker : ∀ a ∈ p.asIdeal, f a = 0 := by
    intro a ha
    refine hmem _ ?_
    have h := (p.valuation_lt_one_iff_mem (K := F) a).mpr ha
    rw [← hval] at h
    exact h
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, hr⟩ := UpperTheory.Reformulated.B.H23.exists_global_approx p x.1 x.2
    refine ⟨r, ?_⟩
    rw [← sub_eq_zero]
    have h := hmem (algebraMap (RingOfIntegers F) (p.adicCompletionIntegers F) r - x) hr
    rw [map_sub] at h
    exact h
  have : Finite (RingOfIntegers F ⧸ p.asIdeal) := p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  exact Finite.of_surjective (Ideal.Quotient.lift p.asIdeal f hker)
    (Ideal.Quotient.lift_surjective_of_surjective _ hker hsurj)

open IsDedekindDomain NumberField in
private theorem UpperTheory.Reformulated.B.H23.locallyCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (RingOfIntegers F)) :
    LocallyCompactSpace (p.adicCompletion F) := by
  have hc : CompactSpace (Valued.integer (p.adicCompletion F)) := by
    rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
    refine ⟨(Valued.isClosed_integer (p.adicCompletion F)).completeSpace_coe,
      inferInstanceAs (IsDiscreteValuationRing (p.adicCompletionIntegers F)),
      UpperTheory.Reformulated.B.H23.finite_residueField p⟩
  have hc' : IsCompact (Valued.integer (p.adicCompletion F) : Set (p.adicCompletion F)) :=
    isCompact_iff_compactSpace.mpr hc
  exact hc'.locallyCompactSpace_of_mem_nhds_of_addGroup (x := 0)
    ((Valued.isOpen_integer (p.adicCompletion F)).mem_nhds (zero_mem _))

theorem UpperTheory.Reformulated.B.H23.zero_contDiffOn_supported :
    ∀ {F : Type} [inst : Field F] [inst_1 : @NumberField F inst]
      (p :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst)),
      @IsNonarchimedeanLocalField
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
        (@UpperTheory.Reformulated.B.H23.complRel F inst inst_1 p)
        (@UniformSpace.toTopologicalSpace
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)) := by
  intro F _ _ p
  letI := UpperTheory.Reformulated.B.H23.complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact
    { toIsValuativeTopology :=
        IsValuativeTopology.of_mem_nhds_iff_vle
          (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))) Valued.mem_nhds
      toLocallyCompactSpace := UpperTheory.Reformulated.B.H23.locallyCompact p
      toIsNontrivial :=
        (ValuativeRel.isNontrivial_iff_isNontrivial
          (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr
          inferInstance }

noncomputable def UpperTheory.Reformulated.B.H23.iwGL :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          (n : Nat) →
            (w : @UpperTheory.Reformulated.B.H23.Pl E inst inst_1) →
              @Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                (@Units.instGroup
                  (Matrix (Fin n) (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Semiring.toMonoid
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Matrix.semiring (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@DivisionSemiring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Semifield.toDivisionSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                      (Fin.fintype n) (instDecidableEqFin n)))) :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst] (n : Nat) (w : @UpperTheory.Reformulated.B.H23.Pl E inst inst_1) ↦
      @UpperTheory.Reformulated.B.H23.iwahori
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
          (@NumberField.instCommRingRingOfIntegers E inst) (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1)
          E inst (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
          (@NumberField.instCommRingRingOfIntegers E inst) (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1)
          E inst (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
        (@UpperTheory.Reformulated.B.H23.complRel E inst inst_1 w)
        (@UniformSpace.toTopologicalSpace
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
            (@NumberField.instCommRingRingOfIntegers E inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace (@NumberField.RingOfIntegers E inst)
            (@NumberField.instCommRingRingOfIntegers E inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
        (@UpperTheory.Reformulated.B.H23.zero_contDiffOn_supported E inst inst_1 w) (Fin n) (Fin.fintype n) (instDecidableEqFin n) (@Fin.instLinearOrder n)

noncomputable def UpperTheory.Reformulated.B.H23.dcos :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          (n : Nat) →
            (w : @UpperTheory.Reformulated.B.H23.Pl E inst inst_1) →
              @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w → @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w → Complex :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst] (n : Nat) (w : @UpperTheory.Reformulated.B.H23.Pl E inst inst_1)
        (t y : @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) ↦
      @ite Complex
        (∃ (x : @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w),
          And
            (@Membership.mem (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
              (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                (@Units.instGroup
                  (Matrix (Fin n) (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Semiring.toMonoid
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Matrix.semiring (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@DivisionSemiring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Semifield.toDivisionSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                      (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                  (@Units.instGroup
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Semiring.toMonoid
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Matrix.semiring (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@DivisionSemiring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Semifield.toDivisionSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                        (Fin.fintype n) (instDecidableEqFin n)))))
                (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                  (@Units.instGroup
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Semiring.toMonoid
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Matrix.semiring (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@DivisionSemiring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Semifield.toDivisionSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.H23.iwGL E inst inst_1 n w) x)
            (∃ (z : @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w),
              And
                (@Membership.mem (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                  (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@Units.instGroup
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Semiring.toMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Matrix.semiring (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@DivisionSemiring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Semifield.toDivisionSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                          (Fin.fintype n) (instDecidableEqFin n)))))
                  (@SetLike.instMembership
                    (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@Units.instGroup
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n)))))
                    (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@Units.instGroup
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n))))))
                  (@UpperTheory.Reformulated.B.H23.iwGL E inst inst_1 n w) z)
                (@Eq (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) y
                  (@HMul.hMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@instHMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@Units.instMul
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n)))))
                    (@HMul.hMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@instHMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                        (@Units.instMul
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n)))))
                      x t)
                    z))))
        (Classical.propDecidable
          (∃ (x : @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w),
            And
              (@Membership.mem (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                  (@Units.instGroup
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Semiring.toMonoid
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Matrix.semiring (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@DivisionSemiring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Semifield.toDivisionSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                        (Fin.fintype n) (instDecidableEqFin n)))))
                (@SetLike.instMembership
                  (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@Units.instGroup
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Semiring.toMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Matrix.semiring (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@DivisionSemiring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Semifield.toDivisionSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                          (Fin.fintype n) (instDecidableEqFin n)))))
                  (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                  (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@Units.instGroup
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Semiring.toMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Matrix.semiring (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@DivisionSemiring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Semifield.toDivisionSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                          (Fin.fintype n) (instDecidableEqFin n))))))
                (@UpperTheory.Reformulated.B.H23.iwGL E inst inst_1 n w) x)
              (∃ (z : @UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w),
                And
                  (@Membership.mem (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                    (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@Units.instGroup
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n)))))
                    (@SetLike.instMembership
                      (@Subgroup (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                        (@Units.instGroup
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n)))))
                      (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                        (@Units.instGroup
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n))))))
                    (@UpperTheory.Reformulated.B.H23.iwGL E inst inst_1 n w) z)
                  (@Eq (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) y
                    (@HMul.hMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                      (@instHMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                        (@Units.instMul
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n)))))
                      (@HMul.hMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                        (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                        (@instHMul (@UpperTheory.Reformulated.B.H23.GLw E inst inst_1 n w)
                          (@Units.instMul
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Semiring.toMonoid
                              (Matrix (Fin n) (Fin n)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                              (@Matrix.semiring (Fin n)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@DivisionSemiring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Semifield.toDivisionSemiring
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@Field.toSemifield
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers E inst)
                                        (@NumberField.instCommRingRingOfIntegers E inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers E inst)
                                        (@NumberField.instCommRingRingOfIntegers E inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                                (Fin.fintype n) (instDecidableEqFin n)))))
                        x t)
                      z)))))
        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
        (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))

theorem UpperTheory.Reformulated.B.H23.dcos_right :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] {m : ℕ}
      {w : UpperTheory.Reformulated.B.H23.Pl E}
      (t k g : UpperTheory.Reformulated.B.H23.GLw m w),
      k ∈ UpperTheory.Reformulated.B.H23.iwGL m w →
        UpperTheory.Reformulated.B.H23.dcos m w t (g * k) =
          UpperTheory.Reformulated.B.H23.dcos m w t g := by
  intro E _ _ _ m w t k g hk
  unfold UpperTheory.Reformulated.B.H23.dcos
  refine @if_congr _ _ _ (Classical.propDecidable _) (Classical.propDecidable _) _ _ _ _
    ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hk), by
      rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k, Subgroup.mul_mem _ hz hk, by rw [h, mul_assoc (x * t)]⟩
