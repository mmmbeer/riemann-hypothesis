import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply

open TensorProduct

namespace GlobalTheory.Forms

abbrev Bil (Y A : Type*) [AddCommGroup Y] [AddCommGroup A] := Y →ₗ[ℤ] Y →ₗ[ℤ] A

section Symmetric

variable (S : Type*) [Semiring S] (Y : Type*) [AddCommGroup Y] (A : Type*) [AddCommGroup A]
  [Module S A]

def symForms : Submodule S (Bil Y A) where
  carrier := {b | ∀ y y', b y y' = b y' y}
  add_mem' {b c} hb hc y y' := by simp only [LinearMap.add_apply, hb y y', hc y y']
  zero_mem' _ _ := rfl
  smul_mem' s b hb y y' := by simp only [LinearMap.smul_apply, hb y y']

variable {S Y A}

theorem mem_symForms {b : Bil Y A} : b ∈ symForms S Y A ↔ ∀ y y', b y y' = b y' y := Iff.rfl

theorem mem_symForms_iff_flip {b : Bil Y A} : b ∈ symForms S Y A ↔ b.flip = b :=
  ⟨fun h => by ext y y'; exact h y' y, fun h y y' => by
    conv_lhs => rw [← h]
    rfl⟩


variable (Y) in

abbrev SymLattice : Type _ := symForms ℤ Y ℤ

instance [Module.Finite ℤ Y] [Module.Free ℤ Y] (L : Submodule ℤ (Bil Y ℤ)) : Module.Finite ℤ L :=
  Module.Finite.of_injective L.subtype L.injective_subtype

instance [Module.Finite ℤ Y] [Module.Free ℤ Y] (L : Submodule ℤ (Bil Y ℤ)) : Module.Free ℤ L :=
  Module.free_of_finite_type_torsion_free'

end Symmetric

section Pullback

variable (S : Type*) [Semiring S] {Y Y' Y'' : Type*} [AddCommGroup Y] [AddCommGroup Y']
  [AddCommGroup Y''] (A : Type*) [AddCommGroup A] [Module S A]

def pullback (f : Y →ₗ[ℤ] Y') : Bil Y' A →ₗ[S] Bil Y A where
  toFun b := b.compl₁₂ f f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S A}

@[simp] theorem pullback_apply (f : Y →ₗ[ℤ] Y') (b : Bil Y' A) (y y' : Y) :
    pullback S A f b y y' = b (f y) (f y') := rfl

@[simp] theorem pullback_id : pullback S A (LinearMap.id : Y →ₗ[ℤ] Y) = LinearMap.id := rfl

theorem pullback_comp (f : Y →ₗ[ℤ] Y') (g : Y' →ₗ[ℤ] Y'') :
    pullback S A (g ∘ₗ f) = pullback S A f ∘ₗ pullback S A g := rfl


theorem pullback_mem_symForms (f : Y →ₗ[ℤ] Y') {b : Bil Y' A} (hb : b ∈ symForms S Y' A) :
    pullback S A f b ∈ symForms S Y A := fun _ _ => hb _ _



variable (S A) in

def symPullback (f : Y →ₗ[ℤ] Y') : symForms S Y' A →ₗ[S] symForms S Y A :=
  (pullback S A f).restrict fun _ hb => pullback_mem_symForms f hb

@[simp] theorem coe_symPullback (f : Y →ₗ[ℤ] Y') (b : symForms S Y' A) :
    (symPullback S A f b : Bil Y A) = pullback S A f b := rfl


variable (S Y A) in

def glAction : (Y ≃ₗ[ℤ] Y) →* (Bil Y A ≃ₗ[S] Bil Y A) where
  toFun g :=
    { pullback S A g.symm.toLinearMap with
      invFun := pullback S A g.toLinearMap
      left_inv := fun b => by ext y y'; simp
      right_inv := fun b => by ext y y'; simp }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem glAction_apply (g : Y ≃ₗ[ℤ] Y) (b : Bil Y A) (y y' : Y) :
    glAction S Y A g b y y' = b (g.symm y) (g.symm y') := rfl


def restrictAction {Γ : Type*} [Group Γ] (ρ : Γ →* (Y ≃ₗ[ℤ] Y)) (L : Submodule S (Bil Y A))
    (hL : ∀ γ, ∀ b ∈ L, glAction S Y A (ρ γ) b ∈ L) : Γ →* (L ≃ₗ[S] L) where
  toFun γ :=
    { (glAction S Y A (ρ γ)).toLinearMap.restrict (hL γ) with
      invFun := (glAction S Y A (ρ γ⁻¹)).toLinearMap.restrict (hL γ⁻¹)
      left_inv := fun b => Subtype.ext <| by
        change (glAction S Y A (ρ γ⁻¹) * glAction S Y A (ρ γ)) b.1 = b.1
        rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]; rfl
      right_inv := fun b => Subtype.ext <| by
        change (glAction S Y A (ρ γ) * glAction S Y A (ρ γ⁻¹)) b.1 = b.1
        rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]; rfl }
  map_one' := by
    ext b : 2
    change glAction S Y A (ρ 1) b.1 = b.1
    rw [map_one, map_one]; rfl
  map_mul' γ δ := by
    ext b : 2
    change glAction S Y A (ρ (γ * δ)) b.1 = (glAction S Y A (ρ γ) * glAction S Y A (ρ δ)) b.1
    rw [map_mul, map_mul]

@[simp] theorem coe_restrictAction {Γ : Type*} [Group Γ] (ρ : Γ →* (Y ≃ₗ[ℤ] Y))
    (L : Submodule S (Bil Y A)) (hL : ∀ γ, ∀ b ∈ L, glAction S Y A (ρ γ) b ∈ L) (γ : Γ) (b : L) :
    (restrictAction ρ L hL γ b : Bil Y A) = glAction S Y A (ρ γ) b := rfl

theorem glAction_mem_symForms (g : Y ≃ₗ[ℤ] Y) {b : Bil Y A} (hb : b ∈ symForms S Y A) :
    glAction S Y A g b ∈ symForms S Y A := fun _ _ => hb _ _

variable (S Y A) in

def symAction : (Y ≃ₗ[ℤ] Y) →* (symForms S Y A ≃ₗ[S] symForms S Y A) :=
  restrictAction (MonoidHom.id _) _ fun g _ hb => glAction_mem_symForms g hb

@[simp] theorem symAction_apply (g : Y ≃ₗ[ℤ] Y) (b : symForms S Y A) (y y' : Y) :
    (symAction S Y A g b : Bil Y A) y y' = (b : Bil Y A) (g.symm y) (g.symm y') := rfl

end Pullback

section SymSq

variable {S : Type*} [Semiring S] (Y : Type*) [AddCommGroup Y]

def symRel : AddSubgroup (Y ⊗[ℤ] Y) :=
  AddSubgroup.closure {x | ∃ y y' : Y, x = y ⊗ₜ y' - y' ⊗ₜ y}

def SymSq : Type _ := (Y ⊗[ℤ] Y) ⧸ symRel Y

instance : AddCommGroup (SymSq Y) := inferInstanceAs (AddCommGroup ((Y ⊗[ℤ] Y) ⧸ symRel Y))

namespace SymSq

def ofTensor : Y ⊗[ℤ] Y →+ SymSq Y := QuotientAddGroup.mk' (symRel Y)

theorem ofTensor_surjective : Function.Surjective (ofTensor Y) :=
  QuotientAddGroup.mk'_surjective _

theorem ker_ofTensor : (ofTensor Y).ker = symRel Y := QuotientAddGroup.ker_mk' _

variable {Y}

def mk : Bil Y (SymSq Y) :=
  LinearMap.mk₂ ℤ (fun y y' => ofTensor Y (y ⊗ₜ y'))
    (fun _ _ _ => by rw [add_tmul, map_add])
    (fun n y y' => by rw [← map_zsmul]; rfl)
    (fun _ _ _ => by rw [tmul_add, map_add])
    (fun n y y' => by rw [← map_zsmul, ← smul_tmul]; rfl)

theorem mk_apply (y y' : Y) : mk y y' = ofTensor Y (y ⊗ₜ y') := rfl

theorem mk_comm (y y' : Y) : mk y y' = mk y' y := by
  rw [mk_apply, mk_apply, ← sub_eq_zero, ← map_sub, ← AddMonoidHom.mem_ker, ker_ofTensor]
  exact AddSubgroup.subset_closure ⟨y, y', rfl⟩

@[ext high] theorem hom_ext {A : Type*} [AddCommGroup A] {f g : SymSq Y →ₗ[ℤ] A}
    (h : ∀ y y', f (mk y y') = g (mk y y')) : f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := ofTensor_surjective Y x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul y y' => exact h y y'
  | add x y hx hy => simp only [map_add, hx, hy]


variable {A : Type*} [AddCommGroup A] [Module S A]

variable (S Y A) in

def lift : symForms S Y A ≃ₗ[S] (SymSq Y →ₗ[ℤ] A) where
  toFun b := AddMonoidHom.toIntLinearMap (M := SymSq Y) <|
    QuotientAddGroup.lift (symRel Y) (TensorProduct.lift b.1).toAddMonoidHom <|
      (AddSubgroup.closure_le _).2 <| by
        rintro _ ⟨y, y', rfl⟩
        rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub]
        exact sub_eq_zero.2 (b.2 y y')
  map_add' b c := by ext; rfl
  map_smul' s b := by ext; rfl
  invFun l := ⟨mk.compr₂ l, fun y y' => congrArg l (mk_comm y y')⟩
  left_inv b := by ext; rfl
  right_inv l := by ext; rfl

@[simp] theorem lift_mk (b : symForms S Y A) (y y' : Y) :
    lift S Y A b (mk y y') = (b : Bil Y A) y y' := rfl

@[simp] theorem lift_symm_apply (l : SymSq Y →ₗ[ℤ] A) (y y' : Y) :
    ((lift S Y A).symm l : Bil Y A) y y' = l (mk y y') := rfl

def map {Y' : Type*} [AddCommGroup Y'] (f : Y →ₗ[ℤ] Y') : SymSq Y →ₗ[ℤ] SymSq Y' :=
  lift ℤ Y (SymSq Y') ⟨pullback ℤ _ f mk, fun _ _ => mk_comm _ _⟩

@[simp] theorem map_mk {Y' : Type*} [AddCommGroup Y'] (f : Y →ₗ[ℤ] Y') (y y' : Y) :
    map f (mk y y') = mk (f y) (f y') := rfl


noncomputable def basis {ι : Type*} (e : Module.Basis ι ℤ Y) : Module.Basis (Sym2 ι) ℤ (SymSq Y) :=
  .ofRepr <| LinearEquiv.ofLinear
    (lift ℤ Y (Sym2 ι →₀ ℤ)
      ⟨e.constr ℤ fun i => e.constr ℤ fun j => Finsupp.single s(i, j) 1, by
        rw [mem_symForms_iff_flip]
        refine e.ext fun i => e.ext fun j => ?_
        simp only [LinearMap.flip_apply, Module.Basis.constr_basis, Sym2.eq_swap]⟩)
    (Finsupp.linearCombination ℤ (Sym2.lift ⟨fun i j => mk (e i) (e j), fun _ _ => mk_comm _ _⟩))
    (by
      refine Finsupp.lhom_ext' fun p => LinearMap.ext_ring ?_
      induction p using Sym2.ind with
      | h i j => simp)
    (by
      refine (lift ℤ Y (SymSq Y)).symm.injective (Subtype.ext ?_)
      refine e.ext fun i => e.ext fun j => ?_
      simp)

@[simp] theorem basis_apply {ι : Type*} (e : Module.Basis ι ℤ Y) (i j : ι) :
    basis e s(i, j) = mk (e i) (e j) := by
  simp [basis, Module.Basis.coe_ofRepr]

instance [Module.Free ℤ Y] : Module.Free ℤ (SymSq Y) :=
  .of_basis (basis (Module.Free.chooseBasis ℤ Y))

instance [Module.Finite ℤ Y] : Module.Finite ℤ (SymSq Y) :=
by
  have h : Module.Finite ℤ (Y ⊗[ℤ] Y) := by
    convert Module.Finite.tensorProduct ℤ Y Y using 0
    congr!
  exact Module.Finite.of_surjective (ofTensor Y).toIntLinearMap (ofTensor_surjective Y)

theorem finrank_eq [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.finrank ℤ (SymSq Y) = (Module.finrank ℤ Y + 1).choose 2 := by
  classical
  rw [Module.finrank_eq_card_basis (basis (Module.Free.chooseBasis ℤ Y)), Sym2.card,
    Module.finrank_eq_card_chooseBasisIndex]

variable (Y) in

noncomputable def dualEquiv [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    SymSq Y ≃ₗ[ℤ] Module.Dual ℤ (SymLattice Y) :=
  Module.evalEquiv ℤ (SymSq Y) ≪≫ₗ (lift ℤ Y ℤ).dualMap

@[simp] theorem dualEquiv_apply [Module.Finite ℤ Y] [Module.Free ℤ Y] (x : SymSq Y)
    (b : SymLattice Y) : dualEquiv Y x b = lift ℤ Y ℤ b x := rfl


variable (Y) in

noncomputable def equivSymmetricPower : SymSq Y ≃+ Sym[ℤ]^2 Y :=
  let F : SymSq Y →+ Sym[ℤ]^2 Y := (lift ℤ Y (Sym[ℤ]^2 Y) ⟨
    (AddMonoidHom.mk' (fun y => (AddMonoidHom.mk' (fun y' => SymmetricPower.tprod ℤ ![y, y'])
      fun a b => by
        have := (SymmetricPower.tprod ℤ (ι := Fin 2) (M := Y)).map_update_add ![y, 0] 1 a b
        have h (c : Y) : Function.update ![y, 0] 1 c = ![y, c] := by
          ext i; fin_cases i <;> simp
        simpa only [h] using this).toIntLinearMap) fun a b => by
        ext y'
        have := (SymmetricPower.tprod ℤ (ι := Fin 2) (M := Y)).map_update_add ![0, y'] 0 a b
        have h (c : Y) : Function.update ![0, y'] 0 c = ![c, y'] := by
          ext i; fin_cases i <;> simp
        simp only [h] at this
        exact this).toIntLinearMap, fun y y' => by
      have := SymmetricPower.tprod_equiv (R := ℤ) (Equiv.swap (0 : Fin 2) 1) ![y', y]
      refine Eq.trans (congrArg (SymmetricPower.tprod ℤ) ?_) this
      ext i; fin_cases i <;> simp⟩).toAddMonoidHom
  let m : MultilinearMap ℤ (fun _ : Fin 2 => Y) (SymSq Y) :=
    { toFun := fun f => mk (f 0) (f 1)
      map_update_add' := fun f i a b => by
        fin_cases i <;> simp [Function.update_apply]
      map_update_smul' := fun f i a b => by
        fin_cases i <;> simp [Function.update_apply] }
  let G : Sym[ℤ]^2 Y →+ SymSq Y :=
    AddCon.lift _ (PiTensorProduct.lift m).toAddMonoidHom <| AddCon.addConGen_le.2 <| by
      rintro _ _ ⟨σ, f⟩
      rw [AddCon.ker_rel]
      refine (PiTensorProduct.lift.tprod (φ := m) f).trans
        (Eq.trans ?_ (PiTensorProduct.lift.tprod (φ := m) fun i => f (σ i)).symm)
      change mk (f 0) (f 1) = mk (f (σ 0)) (f (σ 1))
      have hσ : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
        revert σ; decide
      rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, mk_comm]
  have hG (f : Fin 2 → Y) : G (SymmetricPower.tprod ℤ f) = mk (f 0) (f 1) :=
    PiTensorProduct.lift.tprod (φ := m) f
  AddMonoidHom.toAddEquiv F G
    (by
      have : (G.comp F).toIntLinearMap = LinearMap.id := by
        ext y y'
        exact hG ![y, y']
      exact congrArg LinearMap.toAddMonoidHom this)
    (by
      ext x
      obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.1 (SymmetricPower.range_mk ℤ (Fin 2) Y) x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        have h1 : F (G (SymmetricPower.tprod ℤ f)) = SymmetricPower.tprod ℤ f := by
          rw [hG]
          change SymmetricPower.tprod ℤ ![f 0, f 1] = _
          congr 1
          ext i; fin_cases i <;> rfl
        have h2 := map_zsmul (SymmetricPower.mk ℤ (Fin 2) Y).toAddMonoidHom r
          (PiTensorProduct.tprod ℤ f)
        refine (congrArg (F.comp G) h2).trans (Eq.trans ?_ h2.symm)
        rw [map_zsmul]
        exact congrArg _ h1
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy])

@[simp] theorem equivSymmetricPower_mk (y y' : Y) :
    equivSymmetricPower Y (mk y y') = SymmetricPower.tprod ℤ ![y, y'] := rfl

end SymSq

theorem finrank_symLattice [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Module.finrank ℤ (SymLattice Y) = (Module.finrank ℤ Y + 1).choose 2 := by
  rw [(SymSq.lift ℤ Y ℤ).finrank_eq, ← SymSq.finrank_eq]
  exact Module.finrank_linearMap_self ℤ ℤ _

end SymSq

section Balanced

variable {S : Type*} [Semiring S] (O : Type*) [CommRing O] [StarRing O] {Y Y' : Type*} [AddCommGroup Y] [Module O Y]
  [AddCommGroup Y'] [Module O Y'] {A : Type*} [AddCommGroup A]

def IsBalanced (b : Bil Y A) : Prop := ∀ (a : O) (y y' : Y), b (a • y) y' = b y (star a • y')

variable {O}

theorem IsBalanced.right {b : Bil Y A} (hb : IsBalanced O b) (a : O) (y y' : Y) :
    b y (a • y') = b (star a • y) y' := by
  rw [hb, star_star]

theorem IsBalanced.smul_smul {b : Bil Y A} (hb : IsBalanced O b) (w : O) (y y' : Y) :
    b (w • y) (w • y') = b y ((w * star w) • y') := by
  rw [hb, _root_.smul_smul, mul_comm]


theorem IsBalanced.add_of_add_star {b : Bil Y A} (hb : IsBalanced O b) {w : O}
    (hw : w + star w = 1) (y y' : Y) : b y (w • y') + b (w • y) y' = b y y' := by
  rw [hb, ← map_add, ← add_smul, hw, one_smul]

theorem IsBalanced.smul_mem_ker {b : Bil Y A} (hb : IsBalanced O b) (a : O) {y : Y}
    (hy : y ∈ LinearMap.ker b) : a • y ∈ LinearMap.ker b := by
  rw [LinearMap.mem_ker] at hy ⊢
  ext y'
  rw [hb, hy]
  rfl

def IsBalanced.radical {b : Bil Y A} (hb : IsBalanced O b) : Submodule O Y where
  __ := (LinearMap.ker b).toAddSubmonoid
  smul_mem' a _ hy := hb.smul_mem_ker a hy


variable [Module S A]

variable (S O Y A) in

def balForms : Submodule S (Bil Y A) where
  carrier := {b | b ∈ symForms S Y A ∧ IsBalanced O b}
  add_mem' {b c} hb hc := ⟨add_mem hb.1 hc.1, fun a y y' => by
    simp only [LinearMap.add_apply, hb.2 a y y', hc.2 a y y']⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' s b hb := ⟨Submodule.smul_mem _ s hb.1, fun a y y' => by
    simp only [LinearMap.smul_apply, hb.2 a y y']⟩

variable (O Y) in

abbrev BalLattice : Type _ := balForms ℤ O Y ℤ

theorem mem_balForms {b : Bil Y A} :
    b ∈ balForms S O Y A ↔ b ∈ symForms S Y A ∧ IsBalanced O b := Iff.rfl

variable (S O Y A) in
theorem balForms_le_symForms : balForms S O Y A ≤ symForms S Y A := fun _ hb => hb.1





def traceForm (t : O →ₗ[ℤ] A) : Bil O A :=
  LinearMap.mk₂ ℤ (fun x y => t (x * star y))
    (fun _ _ _ => by rw [add_mul, map_add])
    (fun _ _ _ => by rw [smul_mul_assoc, map_smul])
    (fun _ _ _ => by rw [star_add, mul_add, map_add])
    (fun _ _ _ => by rw [star_zsmul, mul_smul_comm, map_smul])

@[simp] theorem traceForm_apply (t : O →ₗ[ℤ] A) (x y : O) : traceForm t x y = t (x * star y) := rfl


theorem mem_symForms_of_zsmul_mem [Module.IsTorsionFree ℤ A] {Y : Type*} [AddCommGroup Y]
    {b : Bil Y A} {n : ℤ} (hn : n ≠ 0) (hb : n • b ∈ symForms S Y A) : b ∈ symForms S Y A :=
  fun y y' => smul_right_injective A hn (hb y y')

theorem mem_balForms_of_zsmul_mem [Module.IsTorsionFree ℤ A] {b : Bil Y A} {n : ℤ} (hn : n ≠ 0)
    (hb : n • b ∈ balForms S O Y A) : b ∈ balForms S O Y A :=
  ⟨mem_symForms_of_zsmul_mem hn hb.1, fun a y y' => smul_right_injective A hn (hb.2 a y y')⟩

variable (O Y) in

def balInclusion : BalLattice O Y →ₗ[ℤ] SymLattice Y :=
  Submodule.inclusion (balForms_le_symForms ℤ O Y ℤ)

@[simp] theorem coe_balInclusion (b : BalLattice O Y) :
    (balInclusion O Y b : Bil Y ℤ) = b := rfl

variable (O Y) in
theorem balInclusion_injective : Function.Injective (balInclusion O Y) :=
  Submodule.inclusion_injective _

theorem mem_range_balInclusion {b : SymLattice Y} :
    b ∈ LinearMap.range (balInclusion O Y) ↔ IsBalanced O (b : Bil Y ℤ) :=
  ⟨by rintro ⟨c, rfl⟩; exact c.2.2, fun h => ⟨⟨b, b.2, h⟩, rfl⟩⟩


variable (O Y) in

theorem isSaturated_balForms : IsSaturatedSubmodule (balForms ℤ O Y ℤ) :=
  isSaturatedSubmodule_iff.2 fun _ hn _ hb => mem_balForms_of_zsmul_mem hn hb

variable (O Y) in

theorem isSaturated_range_balInclusion :
    IsSaturatedSubmodule (LinearMap.range (balInclusion O Y)) :=
  isSaturatedSubmodule_iff.2 fun n hn b hb => mem_range_balInclusion.2
    (mem_balForms_of_zsmul_mem (S := ℤ) hn ⟨(n • b).2, mem_range_balInclusion.1 hb⟩).2

instance : Module.IsTorsionFree ℤ (SymLattice Y ⧸ LinearMap.range (balInclusion O Y)) :=
  (isSaturated_range_balInclusion O Y).isTorsionFree_quotient

variable (O Y) in

theorem exists_isCompl_range_balInclusion [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    ∃ Q : Submodule ℤ (SymLattice Y), IsCompl (LinearMap.range (balInclusion O Y)) Q := by
  have : Module.Free ℤ (SymLattice Y ⧸ LinearMap.range (balInclusion O Y)) :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (LinearMap.range (balInclusion O Y)).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨q, rfl⟩
    have h1 : q = 0 := by
      rw [← (Submodule.Quotient.mk_eq_zero _).2 hx]
      exact (congr($hs q)).symm
    rw [h1, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (Submodule.Quotient.mk x), ?_, _, ⟨_, rfl⟩,
      sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.eq]
    exact (congr($hs (Submodule.Quotient.mk x))).symm

theorem IsBalanced.pullback_of_semilinear {O' Z : Type*} [CommRing O'] [StarRing O']
    [AddCommGroup Z] [Module O' Z] (σ : O → O') (hσ : ∀ a, σ (star a) = star (σ a))
    (f : Y →ₗ[ℤ] Z) (hf : ∀ (a : O) y, f (a • y) = σ a • f y) {b : Bil Z A}
    (hb : IsBalanced O' b) : IsBalanced O (pullback S A f b) := fun a y y' => by
  rw [pullback_apply, pullback_apply, hf, hf, hσ, hb]

theorem pullback_mem_balForms (f : Y →ₗ[O] Y') {b : Bil Y' A} (hb : b ∈ balForms S O Y' A) :
    pullback S A (f.restrictScalars ℤ) b ∈ balForms S O Y A :=
  ⟨pullback_mem_symForms _ hb.1,
    hb.2.pullback_of_semilinear id (fun _ => rfl) _ fun a y => f.map_smul a y⟩


variable (S A) in

def balPullback (f : Y →ₗ[O] Y') : balForms S O Y' A →ₗ[S] balForms S O Y A :=
  (pullback S A (f.restrictScalars ℤ)).restrict fun _ hb => pullback_mem_balForms f hb

@[simp] theorem balPullback_apply (f : Y →ₗ[O] Y') (b : balForms S O Y' A) (y y' : Y) :
    (balPullback S A f b : Bil Y A) y y' = (b : Bil Y' A) (f y) (f y') := rfl


omit [StarRing O] in
variable (O Y) in

def autToGL : (Y ≃ₗ[O] Y) →* (Y ≃ₗ[ℤ] Y) where
  toFun g := g.restrictScalars ℤ
  map_one' := rfl
  map_mul' _ _ := rfl

omit [StarRing O] in
@[simp] theorem autToGL_apply (g : Y ≃ₗ[O] Y) (y : Y) : autToGL O Y g y = g y := rfl

omit [StarRing O] in
@[simp] theorem autToGL_symm_apply (g : Y ≃ₗ[O] Y) (y : Y) :
    (autToGL O Y g).symm y = g.symm y := rfl

theorem glAction_mem_balForms (g : Y ≃ₗ[O] Y) {b : Bil Y A} (hb : b ∈ balForms S O Y A) :
    glAction S Y A (autToGL O Y g) b ∈ balForms S O Y A :=
  pullback_mem_balForms g.symm.toLinearMap hb


variable (S O Y A) in

def autAction : (Y ≃ₗ[O] Y) →* (balForms S O Y A ≃ₗ[S] balForms S O Y A) :=
  restrictAction (autToGL O Y) _ fun g _ hb => glAction_mem_balForms g hb

@[simp] theorem autAction_apply (g : Y ≃ₗ[O] Y) (b : balForms S O Y A) (y y' : Y) :
    (autAction S O Y A g b : Bil Y A) y y' = (b : Bil Y A) (g.symm y) (g.symm y') := rfl


variable (O Y) in

def balRel : Submodule ℤ (SymSq Y) :=
  saturation (Submodule.span ℤ
    {x : SymSq Y | ∃ (a : O) (y y' : Y), x = SymSq.mk (a • y) y' - SymSq.mk y (star a • y')})

theorem mem_balRel {x : SymSq Y} : x ∈ balRel O Y ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ
    {x : SymSq Y | ∃ (a : O) (y y' : Y), x = SymSq.mk (a • y) y' - SymSq.mk y (star a • y')} :=
  mem_saturation_iff

variable (O Y) in

abbrev BalSq : Type _ := SymSq Y ⧸ balRel O Y

namespace BalSq

variable (O) in

def mk : Bil Y (BalSq O Y) := SymSq.mk.compr₂ (balRel O Y).mkQ

theorem mk_apply (y y' : Y) : mk O y y' = (balRel O Y).mkQ (SymSq.mk y y') := rfl

variable (O Y) in
theorem mk_mem_balForms : mk O ∈ balForms ℤ O Y (BalSq O Y) :=
  ⟨fun y y' => congrArg (balRel O Y).mkQ (SymSq.mk_comm y y'), fun a y y' =>
    (Submodule.Quotient.eq _).2 <| mem_balRel.2
      ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨a, y, y', rfl⟩⟩⟩

@[ext high] theorem hom_ext {f g : BalSq O Y →ₗ[ℤ] A}
    (h : ∀ y y', f (mk O y y') = g (mk O y y')) : f = g :=
  Submodule.linearMap_qext _ (SymSq.hom_ext h)

instance : Module.IsTorsionFree ℤ (BalSq O Y) := isTorsionFree_quotient_saturation _

instance [Module.Finite ℤ Y] : Module.Free ℤ (BalSq O Y) :=
  Module.free_of_finite_type_torsion_free'

variable (S O Y A) in

def lift [Module.IsTorsionFree ℤ A] : balForms S O Y A ≃ₗ[S] (BalSq O Y →ₗ[ℤ] A) where
  toFun b := (balRel O Y).liftQ (SymSq.lift S Y A ⟨b.1, b.2.1⟩) <| by
    intro x hx
    obtain ⟨n, hn, hx⟩ := mem_balRel.1 hx
    have h : n • x ∈ LinearMap.ker (SymSq.lift S Y A ⟨b.1, b.2.1⟩) := by
      refine Submodule.span_le.2 ?_ hx
      rintro _ ⟨a, y, y', rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 (b.2.2 a y y')
    rw [LinearMap.mem_ker, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left hn
  map_add' b c := by ext; rfl
  map_smul' s b := by ext; rfl
  invFun l := ⟨(mk O).compr₂ l, fun y y' => congrArg l ((mk_mem_balForms O Y).1 y y'),
    fun a y y' => congrArg l ((mk_mem_balForms O Y).2 a y y')⟩
  left_inv b := by ext; rfl
  right_inv l := by ext; rfl

@[simp] theorem lift_mk [Module.IsTorsionFree ℤ A] (b : balForms S O Y A) (y y' : Y) :
    lift S O Y A b (mk O y y') = (b : Bil Y A) y y' := rfl

@[simp] theorem lift_symm_apply [Module.IsTorsionFree ℤ A] (l : BalSq O Y →ₗ[ℤ] A) (y y' : Y) :
    ((lift S O Y A).symm l : Bil Y A) y y' = l (mk O y y') := rfl

variable (O Y) in

noncomputable def dualEquiv [Module.Finite ℤ Y] :
    BalSq O Y ≃ₗ[ℤ] Module.Dual ℤ (BalLattice O Y) :=
  Module.evalEquiv ℤ (BalSq O Y) ≪≫ₗ (lift ℤ O Y ℤ).dualMap

@[simp] theorem dualEquiv_apply [Module.Finite ℤ Y] (x : BalSq O Y) (b : BalLattice O Y) :
    dualEquiv O Y x b = lift ℤ O Y ℤ b x := rfl


theorem dualEquiv_mkQ [Module.Finite ℤ Y] [Module.Free ℤ Y] (x : SymSq Y) :
    dualEquiv O Y ((balRel O Y).mkQ x) = (balInclusion O Y).dualMap (SymSq.dualEquiv Y x) := rfl

end BalSq

variable (O Y) in

theorem dualMap_balInclusion_surjective [Module.Finite ℤ Y] [Module.Free ℤ Y] :
    Function.Surjective (balInclusion O Y).dualMap := by
  intro l
  obtain ⟨x, rfl⟩ := (BalSq.dualEquiv O Y).surjective l
  obtain ⟨x, rfl⟩ := (balRel O Y).mkQ_surjective x
  exact ⟨_, (BalSq.dualEquiv_mkQ x).symm⟩

end Balanced

section Level

variable {Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y']

def level (M : ℤ) (L : Submodule ℤ (Bil Y ℤ)) : Submodule ℤ (Bil Y ℤ) :=
  L.map (LinearMap.lsmul ℤ _ M)

theorem mem_level {M : ℤ} {L : Submodule ℤ (Bil Y ℤ)} {b : Bil Y ℤ} :
    b ∈ level M L ↔ ∃ c ∈ L, M • c = b := Iff.rfl

theorem smul_mem_level (M : ℤ) {L : Submodule ℤ (Bil Y ℤ)} {b : Bil Y ℤ} (hb : b ∈ L) :
    M • b ∈ level M L := ⟨b, hb, rfl⟩

theorem level_le (M : ℤ) (L : Submodule ℤ (Bil Y ℤ)) : level M L ≤ L := by
  rintro _ ⟨c, hc, rfl⟩
  exact L.smul_mem M hc

theorem level_mono (M : ℤ) {L L' : Submodule ℤ (Bil Y ℤ)} (h : L ≤ L') :
    level M L ≤ level M L' := Submodule.map_mono h

@[simp] theorem level_one (L : Submodule ℤ (Bil Y ℤ)) : level 1 L = L :=
  le_antisymm (level_le 1 L) fun b hb => ⟨b, hb, one_smul ℤ b⟩

theorem level_mul (M N : ℤ) (L : Submodule ℤ (Bil Y ℤ)) :
    level (M * N) L = level M (level N L) := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨N • c, smul_mem_level N hc, (mul_smul M N c).symm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, mul_smul M N c⟩







noncomputable def levelEquiv {M : ℤ} (hM : M ≠ 0) (L : Submodule ℤ (Bil Y ℤ)) :
    L ≃ₗ[ℤ] level M L :=
  Submodule.equivMapOfInjective _ (fun b c h => by
    ext y y'
    exact mul_left_cancel₀ hM congr($h y y')) L

@[simp] theorem coe_levelEquiv {M : ℤ} (hM : M ≠ 0) (L : Submodule ℤ (Bil Y ℤ)) (b : L) :
    (levelEquiv hM L b : Bil Y ℤ) = M • (b : Bil Y ℤ) := rfl

theorem pullback_mem_level (f : Y →ₗ[ℤ] Y') {L : Submodule ℤ (Bil Y ℤ)}
    {L' : Submodule ℤ (Bil Y' ℤ)} (h : ∀ b ∈ L', pullback ℤ ℤ f b ∈ L) (M : ℤ) {b : Bil Y' ℤ}
    (hb : b ∈ level M L') : pullback ℤ ℤ f b ∈ level M L := by
  obtain ⟨c, hc, rfl⟩ := hb
  exact ⟨_, h c hc, rfl⟩

variable (Y) in

def symLevelAction (M : ℤ) :
    (Y ≃ₗ[ℤ] Y) →* (level M (symForms ℤ Y ℤ) ≃ₗ[ℤ] level M (symForms ℤ Y ℤ)) :=
  restrictAction (MonoidHom.id _) _ fun g _ hb =>
    pullback_mem_level g.symm.toLinearMap (fun _ h => glAction_mem_symForms g h) M hb

variable (Y) in

def balLevelAction (O : Type*) [CommRing O] [StarRing O] [Module O Y] (M : ℤ) :
    (Y ≃ₗ[O] Y) →* (level M (balForms ℤ O Y ℤ) ≃ₗ[ℤ] level M (balForms ℤ O Y ℤ)) :=
  restrictAction (autToGL O Y) _ fun g _ hb =>
    pullback_mem_level (autToGL O Y g).symm.toLinearMap
      (fun _ h => glAction_mem_balForms g h) M hb

end Level

end GlobalTheory.Forms
