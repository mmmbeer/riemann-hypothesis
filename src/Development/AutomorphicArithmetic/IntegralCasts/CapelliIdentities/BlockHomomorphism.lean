import Mathlib

noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) =>
      ∀ (v : V), IsOpen {g : G | (ρ g) v = v}

noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.glCongr :
    (k : Type) → [inst : Field k] → {a b : ℕ} → a = b → GL (Fin a) k →* GL (Fin b) k :=
    fun (k : Type) [Field k] {a b : ℕ} (h : a = b) =>
      Units.map (Matrix.reindexAlgEquiv k k (finCongr h)).toMulEquiv.toMonoidHom

theorem UpperTheory.Reformulated.B.BlockHomomorphism.aux3 :
    ∀ (k : Type) [inst : Field k] (n r : Nat),
      @Eq (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
        (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k
          (@OfNat.ofNat (Matrix (Fin n) (Fin n) k) (nat_lit 1)
            (@One.toOfNat1 (Matrix (Fin n) (Fin n) k)
              (@MulOne.toOne (Matrix (Fin n) (Fin n) k)
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
                  (@MulOneClass.toMulOne k
                    (@MulZeroOneClass.toMulOneClass k
                      (@instMulZeroOneClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                  (@Semiring.toAddCommMonoid k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
              (@Matrix.zero (Fin n) (Fin r) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
              (@Matrix.zero (Fin r) (Fin n) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
            (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
              (@Matrix.one (Fin r) k (instDecidableEqFin r)
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                (@AddMonoidWithOne.toOne k
                  (@AddGroupWithOne.toAddMonoidWithOne k
                    (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
        (@OfNat.ofNat (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k) (nat_lit 1)
          (@One.toOfNat1 (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@MulOne.toOne (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
                (fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
                (@MulOneClass.toMulOne k
                  (@MulZeroOneClass.toMulOneClass k
                    (@instMulZeroOneClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                (@Semiring.toAddCommMonoid k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))))) := by
  intro k _ n r
  exact Matrix.fromBlocks_one

theorem UpperTheory.Reformulated.B.BlockHomomorphism.aux4 :
    ∀ (k : Type) [inst : Field k] (n r : Nat) (A B : Matrix (Fin n) (Fin n) k),
      @Eq (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
        (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k
          (@HMul.hMul (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k)
            (@instHMul (Matrix (Fin n) (Fin n) k)
              (@MulOne.toMul (Matrix (Fin n) (Fin n) k)
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
                  (@MulOneClass.toMulOne k
                    (@MulZeroOneClass.toMulOneClass k
                      (@instMulZeroOneClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                  (@Semiring.toAddCommMonoid k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))))
            A B)
          (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
              (@Matrix.zero (Fin n) (Fin r) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
              (@Matrix.zero (Fin r) (Fin n) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
            (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
              (@Matrix.one (Fin r) k (instDecidableEqFin r)
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                (@AddMonoidWithOne.toOne k
                  (@AddGroupWithOne.toAddMonoidWithOne k
                    (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
        (@HMul.hMul (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (@instHMul (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@MulOne.toMul (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
                (fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
                (@MulOneClass.toMulOne k
                  (@MulZeroOneClass.toMulOneClass k
                    (@instMulZeroOneClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                (@Semiring.toAddCommMonoid k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))))
          (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k A
            (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
                (@Matrix.zero (Fin n) (Fin r) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
                (@Matrix.zero (Fin r) (Fin n) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
              (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
                (@Matrix.one (Fin r) k (instDecidableEqFin r)
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                  (@AddMonoidWithOne.toOne k
                    (@AddGroupWithOne.toAddMonoidWithOne k
                      (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
          (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k B
            (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
                (@Matrix.zero (Fin n) (Fin r) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
                (@Matrix.zero (Fin r) (Fin n) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
              (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
                (@Matrix.one (Fin r) k (instDecidableEqFin r)
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                  (@AddMonoidWithOne.toOne k
                    (@AddGroupWithOne.toAddMonoidWithOne k
                      (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))) := by
  intro k _ n r A B
  simp [Matrix.fromBlocks_multiply]

noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.blkHom :
    (k : Type) →
      [inst : Field k] →
        (n r : Nat) →
          @MonoidHom (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
              (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
              (fun (a b : Sum (Fin n) (Fin r)) ↦
                @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))) :=
    fun (k : Type) [inst : Field k] (n r : Nat) ↦
      @MonoidHom.mk (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
          (@MulOneClass.toMulOne k
            (@MulZeroOneClass.toMulOneClass k
              (@instMulZeroOneClassOfSemiring k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (@Semiring.toAddCommMonoid k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
          (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
          (fun (a b : Sum (Fin n) (Fin r)) ↦
            @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
          (@MulOneClass.toMulOne k
            (@MulZeroOneClass.toMulOneClass k
              (@instMulZeroOneClassOfSemiring k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (@Semiring.toAddCommMonoid k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
        (@OneHom.mk (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (@MulOne.toOne (Matrix (Fin n) (Fin n) k)
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (@MulOne.toOne (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
              (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
              (fun (a b : Sum (Fin n) (Fin r)) ↦
                @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (fun (A : Matrix (Fin n) (Fin n) k) ↦
            @Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k A
              (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
                (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
                  (@Matrix.zero (Fin n) (Fin r) k
                    (@MulZeroClass.toZero k
                      (@instMulZeroClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
              (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
                (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
                  (@Matrix.zero (Fin r) (Fin n) k
                    (@MulZeroClass.toZero k
                      (@instMulZeroClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
              (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
                (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
                  (@Matrix.one (Fin r) k (instDecidableEqFin r)
                    (@MulZeroClass.toZero k
                      (@instMulZeroClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                    (@AddMonoidWithOne.toOne k
                      (@AddGroupWithOne.toAddMonoidWithOne k
                        (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
          (@UpperTheory.Reformulated.B.BlockHomomorphism.aux3 k inst n r))
        (@UpperTheory.Reformulated.B.BlockHomomorphism.aux4 k inst n r)

noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.blkGL :
    (k : Type) → [inst : Field k] → (n r : ℕ) → GL (Fin n) k →* GL (Fin (n + r)) k :=
    fun (k : Type) [Field k] (n r : ℕ) =>
      Units.map
        ((Matrix.reindexAlgEquiv k k finSumFinEquiv).toMulEquiv.toMonoidHom.comp
          (UpperTheory.Reformulated.B.BlockHomomorphism.blkHom k n r))

noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.blkAt :
    (k : Type) → [inst : Field k] → (n N : ℕ) → n ≤ N → GL (Fin n) k →* GL (Fin N) k :=
    fun (k : Type) [Field k] (n N : ℕ) (h : n ≤ N) =>
      (UpperTheory.Reformulated.B.BlockHomomorphism.glCongr k (Nat.add_sub_cancel' h)).comp
        (UpperTheory.Reformulated.B.BlockHomomorphism.blkGL k n (N - n))

noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.FixK :
    {k : Type} →
      [inst : Field k] →
        {m N : ℕ} →
          m + 1 ≤ N →
            {V : Type} →
              [inst_1 : AddCommGroup V] →
                [inst_2 : Module ℂ V] →
                  Representation ℂ (GL (Fin N) k) V → Subgroup (GL (Fin (m + 1)) k) → V → Prop :=
    fun {k : Type} [Field k] {m N : ℕ} (h : m + 1 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (GL (Fin N) k) V) (K : Subgroup (GL (Fin (m + 1)) k)) (v : V) =>
      ∀ g ∈ K, (π ((UpperTheory.Reformulated.B.BlockHomomorphism.blkAt k (m + 1) N h) g)) v = v

theorem UpperTheory.Reformulated.B.BlockHomomorphism.aux9 :
    ∀ {m N : ℕ} {h : m + 2 ≤ N}, ¬m + 1 ≤ N → False := by
  intro m N h a
  omega

private theorem UpperTheory.Reformulated.B.BlockHomomorphism.continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (UpperTheory.Reformulated.B.BlockHomomorphism.blkAt k n N h) := by
  have h1 : Continuous (UpperTheory.Reformulated.B.BlockHomomorphism.blkGL k n (N - n)) := by
    unfold UpperTheory.Reformulated.B.BlockHomomorphism.blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (UpperTheory.Reformulated.B.BlockHomomorphism.glCongr k e) := by
    intro a b e
    unfold UpperTheory.Reformulated.B.BlockHomomorphism.glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1

private def UpperTheory.Reformulated.B.BlockHomomorphism.fixer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem UpperTheory.Reformulated.B.BlockHomomorphism.exists_fixK :
    ∀ {k : Type} [inst : Field k]
      [inst_1 :
        @ValuativeRel k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))]
      [inst_2 : TopologicalSpace k] [@IsNonarchimedeanLocalField k inst inst_1 inst_2] {m N : Nat}
      {h :
        @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) N}
      {V : Type} [inst_4 : AddCommGroup V]
      [inst_5 : @_root_.Module Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_4)]
      {π :
        @Representation Complex
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          V Complex.instSemiring
          (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          (@AddCommGroup.toAddCommMonoid V inst_4) inst_5},
      @UpperTheory.Reformulated.B.BlockHomomorphism.IsSmooth Complex
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          V Complex.instField
          (@Units.instGroup (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          inst_4 inst_5
          (@Units.instTopologicalSpaceUnits (Matrix (Fin N) (Fin N) k)
            (@instTopologicalSpaceMatrix (Fin N) (Fin N) k inst_2)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N))))
          π →
        ∀ (v w : V),
          ∃ (K :
            @Subgroup
              (@Matrix.GeneralLinearGroup
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                k
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Units.instGroup
                (Matrix
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k)
                (@Semiring.toMonoid
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@Matrix.semiring
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))),
            And
              (@IsOpen
                (@Matrix.GeneralLinearGroup
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instTopologicalSpaceUnits
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@instTopologicalSpaceMatrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k inst_2)
                  (@Semiring.toMonoid
                    (Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k)
                    (@Matrix.semiring
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@SetLike.coe
                  (@Subgroup
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Units.instGroup
                      (Matrix
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k)
                      (@Semiring.toMonoid
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Matrix.semiring
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (@Matrix.GeneralLinearGroup
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  (@Subgroup.instSetLike
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Units.instGroup
                      (Matrix
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k)
                      (@Semiring.toMonoid
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Matrix.semiring
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  K))
              (And
                (@UpperTheory.Reformulated.B.BlockHomomorphism.FixK k inst m N
                  (@Decidable.byContradiction
                    (@LE.le Nat instLENat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      N)
                    ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLe
                      N)
                    fun
                      (a :
                        Not
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            N)) ↦
                    @UpperTheory.Reformulated.B.BlockHomomorphism.aux9 m N h a)
                  V inst_4 inst_5 π K v)
                (@UpperTheory.Reformulated.B.BlockHomomorphism.FixK k inst m N
                  (@Decidable.byContradiction
                    (@LE.le Nat instLENat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      N)
                    ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLe
                      N)
                    fun
                      (a :
                        Not
                          (@LE.le Nat instLENat
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            N)) ↦
                    @UpperTheory.Reformulated.B.BlockHomomorphism.aux9 m N h a)
                  V inst_4 inst_5 π K w)) := by
  intro k _ _ _ _ m N h V _ _ π hπ v w
  have hle : m + 1 ≤ N := by omega
  refine ⟨(UpperTheory.Reformulated.B.BlockHomomorphism.fixer π v ⊓ UpperTheory.Reformulated.B.BlockHomomorphism.fixer π w).comap
    (UpperTheory.Reformulated.B.BlockHomomorphism.blkAt k (m + 1) N hle), ?_, fun g hg => hg.1, fun g hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (UpperTheory.Reformulated.B.BlockHomomorphism.continuous_blkAt (m + 1) N hle)
