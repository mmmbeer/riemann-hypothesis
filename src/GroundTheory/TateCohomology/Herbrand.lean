import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
import GroundTheory.TateCohomology.TateLow

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def repSubOne (A : Rep.{w} k G) (σ : G) : A →+ A :=
  (A.ρ σ - 1 : Module.End k A).toAddMonoidHom

theorem repSubOne_apply (A : Rep.{w} k G) (σ : G) (x : A) : repSubOne A σ x = A.ρ σ x - x :=
  rfl

variable [Fintype G]

def repNorm (A : Rep.{w} k G) : A →+ A :=
  A.ρ.norm.toAddMonoidHom

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory

theorem natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker :=
  rfl

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

omit [Fintype G] in

theorem ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]

theorem range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem ker_repNorm (A : Rep.{u} R G) :
    (repNorm A).ker = (LinearMap.ker A.ρ.norm).toAddSubgroup :=
  rfl

theorem range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem natCard_tateCohomology_zero (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A 0) = Nat.card (KerModRange (repSubOne A σ) (repNorm A)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repSubOne A hσ, range_repNorm]
  exact Nat.card_congr ((tateCohomologyZeroIso R G).app A).toLinearEquiv.toEquiv

theorem natCard_tateCohomology_neg_one (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A (-1)) = Nat.card (KerModRange (repNorm A) (repSubOne A σ)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repNorm, range_repSubOne A hσ]
  exact Nat.card_congr ((tateCohomologyNegOneIso R G).app A).toLinearEquiv.toEquiv

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory Rep.FiniteCyclicGroup

section CommGroup

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G] (A : Rep.{u} R G) {σ : G}
  (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

include hσ in

theorem invariants_eq_ker_normHomCompSub_g :
    A.ρ.invariants = LinearMap.ker (normHomCompSub A σ).g.hom := by
  ext x
  simpa [Rep.sub_hom, Rep.applyAsHom, sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ x

include hσ in
theorem normRangeInvariants_map :
    (normRangeInvariants A).map
        (LinearEquiv.ofEq _ _ (invariants_eq_ker_normHomCompSub_g A hσ) :
          A.ρ.invariants →ₗ[R] LinearMap.ker (normHomCompSub A σ).g.hom) =
      LinearMap.range (normHomCompSub A σ).moduleCatToCycles := by
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨m, hm⟩, he⟩
    refine ⟨m, Subtype.ext ?_⟩
    have he' := congrArg Subtype.val he
    change (z : A) = y at he'
    change A.ρ.norm m = y
    rw [← he']
    exact hm
  · rintro ⟨m, hm⟩
    have hm' := congrArg Subtype.val hm
    change A.ρ.norm m = y at hm'
    refine ⟨⟨A.ρ.norm m, fun g => Representation.self_norm_apply A.ρ g m⟩, ⟨m, rfl⟩, Subtype.ext ?_⟩
    exact hm'

noncomputable def tateCohomologyZeroIsoHomology :
    tateCohomology A 0 ≅ (normHomCompSub A σ).homology :=
  (tateCohomologyZeroIso R G).app A ≪≫
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (invariants_eq_ker_normHomCompSub_g A hσ))
      (normRangeInvariants_map A hσ)).toModuleIso ≪≫
    (normHomCompSub A σ).moduleCatHomologyIso.symm

theorem ker_norm_eq_ker_subCompNormHom_g :
    LinearMap.ker A.ρ.norm = LinearMap.ker (subCompNormHom A σ).g.hom :=
  rfl

include hσ in
theorem augmentationKerNorm_map :
    (augmentationKerNorm A).map
        (LinearEquiv.ofEq _ _ (ker_norm_eq_ker_subCompNormHom_g A (σ := σ)) :
          LinearMap.ker A.ρ.norm →ₗ[R] LinearMap.ker (subCompNormHom A σ).g.hom) =
      LinearMap.range (subCompNormHom A σ).moduleCatToCycles := by
  have hc := Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, hzm, he⟩
    have he' := congrArg Subtype.val he
    change (z : A) = y at he'
    rw [mem_augmentationKerNorm_iff, hc] at hzm
    obtain ⟨m, hm⟩ := hzm
    refine ⟨m, Subtype.ext ?_⟩
    change A.ρ σ m - m = y
    rw [← he']
    exact hm
  · rintro ⟨m, hm⟩
    have hm' := congrArg Subtype.val hm
    change A.ρ σ m - m = y at hm'
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [mem_augmentationKerNorm_iff, hc]
    exact ⟨m, hm'⟩

noncomputable def tateCohomologyNegOneIsoHomology :
    tateCohomology A (-1) ≅ (subCompNormHom A σ).homology :=
  (tateCohomologyNegOneIso R G).app A ≪≫
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (ker_norm_eq_ker_subCompNormHom_g A))
      (augmentationKerNorm_map A hσ)).toModuleIso ≪≫
    (subCompNormHom A σ).moduleCatHomologyIso.symm

theorem odd_of_even_negSucc {i : ℕ} (h : Even (Int.negSucc i)) : Odd i := by
  rw [Int.negSucc_eq, even_neg, ← Nat.cast_succ, Int.even_coe_nat, Nat.even_add_one] at h
  exact Nat.not_even_iff_odd.1 h

theorem even_of_odd_negSucc {i : ℕ} (h : Odd (Int.negSucc i)) : Even i := by
  rw [Int.negSucc_eq, odd_neg, ← Nat.cast_succ, Int.odd_coe_nat, Nat.odd_add_one] at h
  exact Nat.not_odd_iff_even.1 h

variable [DecidableEq G]

noncomputable def tateCohomologyIsoEven :
    ∀ n : ℤ, Even n → (tateCohomology A n ≅ (normHomCompSub A σ).homology)
  | .ofNat 0, _ => tateCohomologyZeroIsoHomology A hσ
  | .ofNat (i + 1), hn =>
      (TateCohomology.isoGroupCohomology (i + 1)).app A ≪≫
        groupCohomologyIsoEven A σ hσ (i + 1) ((Int.even_coe_nat (i + 1)).1 hn)
  | .negSucc i, hn =>
      haveI : NeZero i := ⟨fun h => by
        have := odd_of_even_negSucc hn
        rw [h] at this
        exact Nat.not_odd_zero this⟩
      (TateCohomology.isoGroupHomology (Int.negSucc i) i (Int.negSucc_eq i)).app A ≪≫
        groupHomologyIsoOdd A σ hσ i (odd_of_even_negSucc hn)

noncomputable def tateCohomologyIsoOdd :
    ∀ n : ℤ, Odd n → (tateCohomology A n ≅ (subCompNormHom A σ).homology)
  | .ofNat 0, hn => absurd hn (by decide)
  | .ofNat (i + 1), hn =>
      (TateCohomology.isoGroupCohomology (i + 1)).app A ≪≫
        groupCohomologyIsoOdd A σ hσ (i + 1) ((Int.odd_coe_nat (i + 1)).1 hn)
  | .negSucc 0, _ => tateCohomologyNegOneIsoHomology A hσ
  | .negSucc (i + 1), hn =>
      (TateCohomology.isoGroupHomology (Int.negSucc (i + 1)) (i + 1)
          (Int.negSucc_eq (i + 1))).app A ≪≫
        groupHomologyIsoEven A σ hσ (i + 1) (even_of_odd_negSucc hn)

noncomputable def tateCohomologyPeriodicIsoOfComm (n : ℤ) :
    tateCohomology A (n + 2) ≅ tateCohomology A n :=
  if h : Even n then
    tateCohomologyIsoEven A hσ (n + 2) (h.add even_two) ≪≫ (tateCohomologyIsoEven A hσ n h).symm
  else
    tateCohomologyIsoOdd A hσ (n + 2) ((Int.not_even_iff_odd.1 h).add_even even_two) ≪≫
      (tateCohomologyIsoOdd A hσ n (Int.not_even_iff_odd.1 h)).symm

end CommGroup

noncomputable def tateCohomologyPeriodicIso {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (n : ℤ) :
    tateCohomology A (n + 2) ≅ tateCohomology A n := by
  classical
  letI : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm := fun a b => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ b)
        exact zpow_mul_comm σ i j }
  exact tateCohomologyPeriodicIsoOfComm A hσ n

end GroundTheory.GroupCoh
end
