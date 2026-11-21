import Mathlib

section
noncomputable section

namespace GlobalTheory.KS

variable {O : Type} [Ring O] {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

def matAct (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : (Fin m → V) →ₗ[R] (Fin m → V) :=
  LinearMap.pi fun i => ∑ j, ρ (M i j) ∘ₗ LinearMap.proj j

theorem matAct_apply (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (x : Fin m → V) (i : Fin m) :
    matAct ρ M x i = ∑ j, ρ (M i j) (x j) := by
  simp [matAct]

abbrev Alt (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] (E : Type) [CommRing E] [Algebra R E] (q : ℕ) :
    Type := W [⋀^Fin q]→ₗ[R] E

variable {E : Type} [CommRing E] [Algebra R E]

def altPull (E : Type) [CommRing E] [Algebra R E] {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) : Alt R W E q →ₗ[E] Alt R W' E q where
  toFun f := f.compLinearMap u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem altPull_apply {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) (f : Alt R W E q) (x : Fin q → W') : altPull E u q f x = f fun i => u (x i) := rfl

def altOp (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) :
    Module.End E (Alt R (Fin m → V) E q) :=
  ε.sum fun M c => c • altPull E (matAct ρ M) q

structure IsCut (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Prop where
  idem : altOp ρ ε k * altOp ρ ε k = altOp ρ ε k
  zero : ∀ q, q ≠ k → altOp ρ ε q = 0

variable {Γ : Type} [Group Γ]

def altRep (E : Type) [CommRing E] [Algebra R E] {W : Type} [AddCommGroup W] [Module R W] (σ : Representation R Γ W) (q : ℕ) :
    Representation E Γ (Alt R W E q) where
  toFun γ := altPull E (σ γ⁻¹) q
  map_one' := by
    ext f x
    simp [altPull]
  map_mul' γ δ := by
    ext f x
    simp [Module.End.mul_apply]

def powRep (σ : Representation R Γ V) (m : ℕ) : Representation R Γ (Fin m → V) where
  toFun γ := LinearMap.pi fun i => σ γ ∘ₗ LinearMap.proj i
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

theorem altOp_comm (ρ : O →+* Module.End R V) (σ : Representation R Γ V) (hσ : ∀ γ b, σ γ * ρ b = ρ b * σ γ) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) (γ : Γ) :
    altRep E (powRep σ m) q γ * altOp ρ ε q = altOp ρ ε q * altRep E (powRep σ m) q γ := by
  have h : ∀ (M : Matrix (Fin m) (Fin m) O) (x : Fin m → V),
      matAct ρ M (powRep σ m γ⁻¹ x) = powRep σ m γ⁻¹ (matAct ρ M x) := by
    intro M x
    funext i
    have h1 : ∀ b y, σ γ⁻¹ (ρ b y) = ρ b (σ γ⁻¹ y) := fun b y => LinearMap.congr_fun (hσ γ⁻¹ b) y
    simp [matAct_apply, powRep, map_sum, h1]
  unfold altOp Finsupp.sum
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ext f x
  change f (fun i => matAct ρ M (powRep σ m γ⁻¹ (x i))) = f (fun i => powRep σ m γ⁻¹ (matAct ρ M (x i)))
  simp only [h]

def xiRep (ρ : O →+* Module.End R V) (σ : Representation R Γ V) (hσ : ∀ γ b, σ γ * ρ b = ρ b * σ γ) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Representation E Γ (LinearMap.range (altOp ρ ε k)) :=
  (altRep E (powRep σ m) k).subrepresentation _ fun γ => by
    rintro _ ⟨f, rfl⟩
    exact ⟨altRep E (powRep σ m) k γ f, (LinearMap.congr_fun (altOp_comm ρ σ hσ ε k γ) f).symm⟩

example (ρ : O →+* Module.End R V) : IsCut ρ (Finsupp.single (1 : Matrix (Fin 0) (Fin 0) O) (1 : E)) 0 where
  idem := by
    have : altOp ρ (Finsupp.single (1 : Matrix (Fin 0) (Fin 0) O) (1 : E)) 0 = 1 := by
      ext f x
      simp only [altOp, zero_smul, Finsupp.sum_single_index, one_smul, altPull_apply, Module.End.one_apply]
      exact congrArg f (Subsingleton.elim _ _)
    rw [this, one_mul]
  zero q hq := by
    ext f x
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    simp only [altOp, zero_smul, Finsupp.sum_single_index, one_smul, altPull, LinearMap.coe_mk, AddHom.coe_mk,
      AlternatingMap.compLinearMap_apply, LinearMap.zero_apply, AlternatingMap.zero_apply]
    exact f.map_coord_zero 0 (Subsingleton.elim _ _)

end GlobalTheory.KS
end
end

section
noncomputable section

namespace GlobalTheory.KS

open CategoryTheory

variable {Γ : Type} [Group Γ] {L : Type} [AddCommGroup L]

def autOf (σ : Representation ℤ Γ L) : Γ →* MulAut (Multiplicative L) where
  toFun γ :=
    { toFun := fun x => Multiplicative.ofAdd (σ γ x.toAdd)
      invFun := fun x => Multiplicative.ofAdd (σ γ⁻¹ x.toAdd)
      left_inv := fun x => by simp [← Module.End.mul_apply, ← map_mul]
      right_inv := fun x => by simp [← Module.End.mul_apply, ← map_mul]
      map_mul' := fun x y => by simp }
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

abbrev SD (σ : Representation ℤ Γ L) : Type := Multiplicative L ⋊[autOf σ] Γ

variable {Γ' : Type} [Group Γ'] {L' : Type} [AddCommGroup L']

def sdMap {σ' : Representation ℤ Γ' L'} {σ : Representation ℤ Γ L} (α : Γ' →* Γ) (u : L' →ₗ[ℤ] L)
    (h : ∀ γ x, u (σ' γ x) = σ (α γ) (u x)) : SD σ' →* SD σ :=
  SemidirectProduct.map (AddMonoidHom.toMultiplicative u.toAddMonoidHom) α fun γ => by
    ext x
    simp [autOf, h]

variable (E : Type) [Field E]

abbrev altRepZ (σ : Representation ℤ Γ L) (q : ℕ) : Representation E Γ (Alt ℤ L E q) := altRep E σ q

abbrev SH (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  Module.Dual E (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} E) n).obj (ModuleCat.of E E)).obj (TopCat.of X))

def shMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) : SH E Y n →ₗ[E] SH E X n :=
  Module.Dual.transpose (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} E) n).obj (ModuleCat.of E E)).map
    (TopCat.ofHom f)).hom

structure Asph (Y : Type) [TopologicalSpace Y] where
  n : ℕ
  G : Fin n → Type
  [grp : ∀ i, Group (G i)]
  X : Fin n → Type
  [top : ∀ i, TopologicalSpace (X i)]
  [act : ∀ i, MulAction (G i) (X i)]
  contr : ∀ i, ContractibleSpace (X i)
  π : ∀ i, C(X i, Y)
  isOpen : ∀ i, IsOpen (Set.range (π i))
  cov : ∀ i, IsQuotientCoveringMap (Set.rangeFactorization (π i)) (G i)
  disj : Pairwise fun i j => Disjoint (Set.range (π i)) (Set.range (π j))
  cover : ∀ y, ∃ i, y ∈ Set.range (π i)

attribute [instance] Asph.grp Asph.top Asph.act

structure Asph.Lift {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (K' : Asph Y') (K : Asph Y) (f : C(Y', Y)) where
  κ : Fin K'.n → Fin K.n
  α : ∀ i, K'.G i →* K.G (κ i)
  lift : ∀ i, C(K'.X i, K.X (κ i))
  equiv : ∀ i (g : K'.G i) x, lift i (g • x) = α i g • lift i x
  comm : ∀ i x, K.π (κ i) (lift i x) = f (K'.π i x)

def Asph.point : Asph Unit where
  n := 1
  G _ := Unit
  X _ := Unit
  contr _ := inferInstance
  π _ := ContinuousMap.const _ ()
  isOpen _ := isOpen_discrete _
  cov _ :=
    { toIsQuotientMap := by
        refine ⟨⟨Subsingleton.elim _ _⟩, fun y => ⟨(), Subtype.ext (Subsingleton.elim _ _)⟩⟩
      toContinuousConstSMul := ⟨fun _ => continuous_id⟩
      apply_eq_iff_mem_orbit := by
        intro a b
        simp [Subsingleton.elim a b, MulAction.mem_orbit_self]
      disjoint := fun _ => ⟨Set.univ, Filter.univ_mem, fun g _ => Subsingleton.elim _ _⟩ }
  disj i j h := absurd (Subsingleton.elim i j) h
  cover _ := ⟨0, (), rfl⟩

def circleAsph : Asph (AddCircle (1 : ℝ)) where
  n := 1
  G _ := Multiplicative (AddSubgroup.zmultiples (1 : ℝ))
  X _ := ℝ
  contr _ := inferInstance
  π _ := ⟨((↑) : ℝ → AddCircle (1 : ℝ)), continuous_quotient_mk'⟩
  isOpen _ := by
    show IsOpen (Set.range ((↑) : ℝ → AddCircle (1 : ℝ)))
    rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk_surjective)]
    exact isOpen_univ
  cov _ := by
    have h := (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).toMultiplicative
    have hs : Set.range ((↑) : ℝ → AddCircle (1 : ℝ)) = Set.univ :=
      Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective
    let φ : AddCircle (1 : ℝ) ≃ₜ Set.range ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      (Homeomorph.Set.univ _).symm.trans (Homeomorph.setCongr hs.symm)
    have := h.homeomorph_comp φ
    show IsQuotientCoveringMap (Set.rangeFactorization ((↑) : ℝ → AddCircle (1 : ℝ))) _
    convert this using 1
    funext x
    rfl
  disj i j h := absurd (Subsingleton.elim i j) h
  cover y := ⟨0, QuotientAddGroup.mk_surjective y⟩

def Asph.liftId {Y : Type} [TopologicalSpace Y] (K : Asph Y) : Asph.Lift K K (ContinuousMap.id Y) where
  κ := id
  α _ := MonoidHom.id _
  lift _ := ContinuousMap.id _
  equiv _ _ _ := rfl
  comm _ _ := rfl


example : Asph.Lift circleAsph circleAsph (ContinuousMap.id _) := circleAsph.liftId
example : circleAsph.n = 1 := rfl

example (σ : Representation ℤ Γ L) (a b : SD σ) :
    (a * b).left = Multiplicative.ofAdd ((a.left).toAdd + σ a.right (b.left).toAdd) := rfl

end GlobalTheory.KS
end
end
