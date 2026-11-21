import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule

section
namespace GroundTheory.Global

open NumberField IntermediateField

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

abbrev FiniteSubfield : Type := {F : IntermediateField ℚ ℚ̄ // FiniteDimensional ℚ F}

namespace FiniteSubfield

instance (F : FiniteSubfield) : FiniteDimensional ℚ F.1 := F.2

instance (F : FiniteSubfield) : NumberField F.1 where
  to_finiteDimensional := by convert F.2

instance : IsDirectedOrder FiniteSubfield where
  directed F E := ⟨⟨F.1 ⊔ E.1, inferInstance⟩, le_sup_left (a := F.1), le_sup_right (a := F.1)⟩

instance : Nonempty FiniteSubfield := ⟨⟨⊥, inferInstance⟩⟩

abbrev algebraOfLE {F E : FiniteSubfield} (h : F ≤ E) : Algebra F.1 E.1 :=
  (IntermediateField.inclusion (show F.1 ≤ E.1 from h)).toRingHom.toAlgebra


def ideleClassMap {F E : FiniteSubfield} (h : F ≤ E) :
    IdeleClassGroup F.1 →* IdeleClassGroup E.1 :=
  letI := algebraOfLE h
  GroundTheory.Global.ideleClassMap F.1 E.1

theorem ideleClassMap_mk {F E : FiniteSubfield} (h : F ≤ E) (x : IdeleGroup F.1) :
    ideleClassMap h (IdeleClassGroup.mk F.1 x) =
      IdeleClassGroup.mk E.1 (@ideleEmbedding F.1 E.1 _ _ _ _ (algebraOfLE h) x) :=
  rfl

theorem ideleClassMap_injective {F E : FiniteSubfield} (h : F ≤ E) :
    Function.Injective (ideleClassMap h) :=
  letI := algebraOfLE h
  GroundTheory.Global.ideleClassMap_injective

theorem ideleClassMap_ideleClassMap {F E M : FiniteSubfield} (hFE : F ≤ E) (hEM : E ≤ M)
    (c : IdeleClassGroup F.1) :
    ideleClassMap hEM (ideleClassMap hFE c) = ideleClassMap (hFE.trans hEM) c := by
  let := algebraOfLE hFE
  let := algebraOfLE hEM
  let := algebraOfLE (hFE.trans hEM)
  have : IsScalarTower F.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact GroundTheory.Global.ideleClassMap_ideleClassMap c

@[simp]
theorem ideleClassMap_self {F : FiniteSubfield} (h : F ≤ F) (c : IdeleClassGroup F.1) :
    ideleClassMap h c = c :=
  ideleClassMap_injective h (ideleClassMap_ideleClassMap h h c)

instance directedSystem : DirectedSystem (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ ideleClassMap h) where
  map_self _ c := ideleClassMap_self _ c
  map_map _ _ _ hFE hEM c := ideleClassMap_ideleClassMap hFE hEM c

end FiniteSubfield

def IdeleClassLimit : Type :=
  DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)

namespace IdeleClassLimit

instance : CommGroup IdeleClassLimit :=
  inferInstanceAs (CommGroup (DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)))

def of (F : FiniteSubfield) : IdeleClassGroup F.1 →* IdeleClassLimit where
  toFun c := (⟦⟨F, c⟩⟧ : DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h))
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F).symm
  map_mul' x y := (DirectLimit.mul_def (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F x y).symm

@[simp]
theorem of_ideleClassMap {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup F.1) :
    of E (FiniteSubfield.ideleClassMap h c) = of F c :=
  show (⟦⟨E, FiniteSubfield.ideleClassMap h c⟩⟧ : DirectLimit
    (fun F : FiniteSubfield ↦ IdeleClassGroup F.1) (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)) =
      ⟦⟨F, c⟩⟧ from DirectLimit.mk_apply (F := fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
        (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F E c h

theorem of_injective (F : FiniteSubfield) : Function.Injective (of F) :=
  DirectLimit.mk_injective (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap_injective h) F

theorem exists_of (z : IdeleClassLimit) : ∃ (F : FiniteSubfield) (c : IdeleClassGroup F.1),
    of F c = z := by
  obtain ⟨F, c, rfl⟩ := DirectLimit.exists_eq_mk
    (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) z
  exact ⟨F, c, rfl⟩

theorem exists_of₂ (z w : IdeleClassLimit) : ∃ (F : FiniteSubfield) (c d : IdeleClassGroup F.1),
    of F c = z ∧ of F d = w := by
  obtain ⟨F, c, d, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂
    (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) z w
  exact ⟨F, c, d, rfl, rfl⟩


section lift

variable {G : Type*} [CommGroup G] (g : ∀ F : FiniteSubfield, IdeleClassGroup F.1 →* G)
  (compat : ∀ (F E : FiniteSubfield) (h : F ≤ E) (c : IdeleClassGroup F.1),
    g E (FiniteSubfield.ideleClassMap h c) = g F c)

def lift : IdeleClassLimit →* G where
  toFun := DirectLimit.lift (fun _ _ h ↦ FiniteSubfield.ideleClassMap h) (fun F c ↦ g F c)
    fun F E h c ↦ (compat F E h c).symm
  map_one' := by
    obtain ⟨F⟩ := (inferInstance : Nonempty FiniteSubfield)
    have h1 : (1 : IdeleClassLimit) = of F 1 := (map_one _).symm
    rw [h1]
    exact map_one (g F)
  map_mul' z w := by
    obtain ⟨F, c, d, rfl, rfl⟩ := exists_of₂ z w
    rw [← map_mul]
    exact map_mul (g F) c d

@[simp]
theorem lift_of (F : FiniteSubfield) (c : IdeleClassGroup F.1) : lift g compat (of F c) = g F c :=
  rfl

theorem lift_unique (φ : IdeleClassLimit →* G) (hφ : ∀ F, φ.comp (of F) = g F) :
    φ = lift g compat := by
  ext z
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [lift_of, ← hφ F, MonoidHom.comp_apply]

end lift

@[ext]
theorem hom_ext {G : Type*} [Monoid G] {φ ψ : IdeleClassLimit →* G}
    (h : ∀ F : FiniteSubfield, φ.comp (of F) = ψ.comp (of F)) : φ = ψ := by
  ext z
  obtain ⟨F, c, rfl⟩ := exists_of z
  exact DFunLike.congr_fun (h F) c

end IdeleClassLimit

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open NumberField IntermediateField AdeleBaseChange
open scoped NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Naturality

variable {L L' M M' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field M]
  [NumberField M] [Field M'] [NumberField M'] [Algebra L M] [Algebra L' M']

theorem adeleRingEquiv_adeleMap_of_comm (τ : L ≃+* L') (ρ : M ≃+* M')
    (h : ∀ l : L, ρ (algebraMap L M l) = algebraMap L' M' (τ l)) (a : 𝔸[L]) :
    adeleRingEquiv ρ (adeleMap L M a) = adeleMap L' M' (adeleRingEquiv τ a) := by
  have : IsScalarTower ℚ L M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsScalarTower ℚ L' M' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have key : ((adeleRingEquiv ρ : 𝔸[M] →+* 𝔸[M']).comp (adeleMap L M) : 𝔸[L] →+* 𝔸[M']) =
      (adeleMap L' M').comp (adeleRingEquiv τ : 𝔸[L] →+* 𝔸[L']) := by
    refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, adeleMap_algebraMap,
        adeleRingEquiv_algebraMap, h]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, adeleMap_adeleMap,
        adeleRingEquiv_adeleMap_rat]
  exact congrArg (fun f : 𝔸[L] →+* 𝔸[M'] ↦ f a) key

theorem ideleEquiv_ideleEmbedding_of_comm (τ : L ≃+* L') (ρ : M ≃+* M')
    (h : ∀ l : L, ρ (algebraMap L M l) = algebraMap L' M' (τ l)) (x : IdeleGroup L) :
    ideleEquiv ρ (ideleEmbedding L M x) = ideleEmbedding L' M' (ideleEquiv τ x) :=
  Units.ext (adeleRingEquiv_adeleMap_of_comm τ ρ h (x : 𝔸[L]))

theorem ideleClassEquiv_ideleClassMap_of_comm (τ : L ≃+* L') (ρ : M ≃+* M')
    (h : ∀ l : L, ρ (algebraMap L M l) = algebraMap L' M' (τ l)) (c : IdeleClassGroup L) :
    ideleClassEquiv ρ (ideleClassMap L M c) = ideleClassMap L' M' (ideleClassEquiv τ c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassMap_mk, ideleClassEquiv_mk, ideleClassEquiv_mk, ideleClassMap_mk,
    ideleEquiv_ideleEmbedding_of_comm τ ρ h]

end Naturality

namespace FiniteSubfield

def map (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : FiniteSubfield :=
  ⟨F.1.map (σ : ℚ̄ →ₐ[ℚ] ℚ̄),
    LinearEquiv.finiteDimensional (IntermediateField.equivMap F.1 (σ : ℚ̄ →ₐ[ℚ] ℚ̄)).toLinearEquiv⟩

def mapEquiv (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : F.1 ≃+* (map σ F).1 :=
  (IntermediateField.equivMap F.1 (σ : ℚ̄ →ₐ[ℚ] ℚ̄)).toRingEquiv

@[simp]
theorem coe_mapEquiv (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (x : F.1) :
    ((mapEquiv σ F x : (map σ F).1) : ℚ̄) = σ x :=
  rfl

theorem map_mono (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) {F E : FiniteSubfield} (h : F ≤ E) : map σ F ≤ map σ E :=
  IntermediateField.map_mono _ (show F.1 ≤ E.1 from h)

theorem of_ideleClassEquiv_congr {F E E' : FiniteSubfield} (τ : F.1 ≃+* E.1) (τ' : F.1 ≃+* E'.1)
    (h : ∀ x : F.1, (τ x : ℚ̄) = τ' x) (c : IdeleClassGroup F.1) :
    IdeleClassLimit.of E (ideleClassEquiv τ c) = IdeleClassLimit.of E' (ideleClassEquiv τ' c) := by
  have hE : E = E' := by
    refine Subtype.ext (SetLike.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩)
    · obtain ⟨x, hx⟩ := τ.surjective ⟨y, hy⟩
      have hy' : y = ((τ' x : E'.1) : ℚ̄) := by rw [← h x, hx]
      rw [hy']
      exact (τ' x).2
    · obtain ⟨x, hx⟩ := τ'.surjective ⟨y, hy⟩
      have hy' : y = ((τ x : E.1) : ℚ̄) := by rw [h x, hx]
      rw [hy']
      exact (τ x).2
  subst hE
  have : τ = τ' := RingEquiv.ext fun x ↦ Subtype.ext (h x)
  rw [this]

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield

def conjOf (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : IdeleClassGroup F.1 →* IdeleClassLimit :=
  (of (map σ F)).comp (ideleClassEquiv (mapEquiv σ F)).toMulEquiv.toMonoidHom

theorem conjOf_apply (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    conjOf σ F c = of (map σ F) (ideleClassEquiv (mapEquiv σ F) c) :=
  rfl

theorem conjOf_compat (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F E : FiniteSubfield) (h : F ≤ E)
    (c : IdeleClassGroup F.1) : conjOf σ E (FiniteSubfield.ideleClassMap h c) = conjOf σ F c := by
  rw [conjOf_apply, conjOf_apply, FiniteSubfield.ideleClassMap]
  let := algebraOfLE h
  let := algebraOfLE (map_mono σ h)
  rw [ideleClassEquiv_ideleClassMap_of_comm (mapEquiv σ F) (mapEquiv σ E) (fun x ↦ rfl)]
  exact of_ideleClassMap (map_mono σ h) _

def galoisHom (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : IdeleClassLimit →* IdeleClassLimit :=
  lift (conjOf σ) (conjOf_compat σ)

theorem galoisHom_of (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    galoisHom σ (of F c) = of (map σ F) (ideleClassEquiv (mapEquiv σ F) c) :=
  rfl

theorem galoisHom_one (z : IdeleClassLimit) : galoisHom 1 z = z := by
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [galoisHom_of]
  refine (of_ideleClassEquiv_congr (mapEquiv 1 F) (RingEquiv.refl F.1) (fun x ↦ rfl) c).trans ?_
  rw [ideleClassEquiv_refl]

theorem galoisHom_mul (σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleClassLimit) :
    galoisHom (σ * τ) z = galoisHom σ (galoisHom τ z) := by
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [galoisHom_of, galoisHom_of, galoisHom_of, ← ideleClassEquiv_trans]
  exact of_ideleClassEquiv_congr (mapEquiv (σ * τ) F)
    ((mapEquiv τ F).trans (mapEquiv σ (map τ F))) (fun x ↦ rfl) c

instance : MulDistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit where
  smul σ z := galoisHom σ z
  one_smul := galoisHom_one
  mul_smul := galoisHom_mul
  smul_one σ := map_one (galoisHom σ)
  smul_mul σ := map_mul (galoisHom σ)

theorem smul_def (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleClassLimit) : σ • z = galoisHom σ z :=
  rfl

theorem smul_of (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    σ • of F c = of (map σ F) (ideleClassEquiv (mapEquiv σ F) c) :=
  rfl

theorem smul_of_eq_of_mem_fixingSubgroup {F : FiniteSubfield} {σ : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hσ : σ ∈ F.1.fixingSubgroup) (c : IdeleClassGroup F.1) : σ • of F c = of F c := by
  rw [smul_of]
  refine (of_ideleClassEquiv_congr (mapEquiv σ F) (RingEquiv.refl F.1)
    (fun x ↦ (IntermediateField.mem_fixingSubgroup_iff F.1 σ).1 hσ x x.2) c).trans ?_
  rw [ideleClassEquiv_refl]

instance : GroundTheory.LocalField.Abstract.IsDiscreteModule (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit where
  isOpen_stabilizer z := by
    obtain ⟨F, c, rfl⟩ := exists_of z
    have : FiniteDimensional ℚ F.1 := F.2
    exact Subgroup.isOpen_mono (H₁ := F.1.fixingSubgroup)
      (fun σ hσ ↦ smul_of_eq_of_mem_fixingSubgroup hσ c) F.1.fixingSubgroup_isOpen

end IdeleClassLimit

end

end GroundTheory.Global
end
