import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.IsSelfDual

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section ObjJ

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def fixZ (H : HermSp M V) (Z : Submodule E V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.closure {g | IsUnitary H g ∧ ∀ v ∈ Z, g v = v}

def Commens {G : Type*} [Group G] (K K' : Subgroup G) : Prop :=
  K.relIndex K' ≠ 0 ∧ K'.relIndex K ≠ 0

def OrbRel (G : Subgroup (V ≃ₗ[E] V)) (Λ Λ' : Submodule M.L.O V) : Prop :=
  ∃ g ∈ G, img g Λ = Λ'

def massOf (G K : Subgroup (V ≃ₗ[E] V)) (Rs : Set (Submodule M.L.O V)) : ENNReal :=
  ∑' Λ : Rs, ENNReal.ofReal (1 / volRel (G ⊓ Aut (Λ : Submodule M.L.O V)) K)

def SigZ (H : HermSp M V) (Z : Submodule E V) (Mh : Submodule M.L.O V) : Set (Submodule M.L.O V) :=
  {Λ | IsSelfDual H Λ ∧ Λ ⊓ Z.restrictScalars M.L.O = Mh}

def piIn (H : HermSp M V) (ϖ : 𝒪[F]) (Λs : Submodule M.L.O V) : Submodule M.L.O Λs :=
  (H.smulLat (algebraMap F E (ϖ : F)) Λs).comap Λs.subtype

def PrimTup (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (x : Fin m → Λs) : Prop :=
  ∀ c : Fin m → M.L.O, ∃ y ∈ Λs, ∀ a, H.h y (x a : V) = (c a : E)

def GramCong (H : HermSp M V) (ϖ : 𝒪[F]) {m : ℕ} (x : Fin m → V) (Gm : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ a b, ∃ e ∈ M.L.O, H.h (x b) (x a) - Gm a b = algebraMap F E (ϖ : F) * e

def dlCount (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) {m : ℕ} (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Nat.card {c : Fin m → (Λs ⧸ piIn H ϖ Λs) //
    ∃ x : Fin m → Λs, (∀ a, Submodule.Quotient.mk (x a) = c a) ∧ PrimTup H Λs x ∧
      GramCong H ϖ (fun a => (x a : V)) Gm}

def dl (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) {m : ℕ} (Gm : Matrix (Fin m) (Fin m) E) : ℝ :=
  (dlCount H Λs ϖ Gm : ℝ) / (qF F : ℝ) ^ (2 * Module.finrank E V * m - m ^ 2)

def idx (M : Model F E) {m : ℕ} (ff b : Fin m → V) : ℕ :=
  Nat.card (Submodule.span M.L.O (Set.range b) ⧸
    (Submodule.span M.L.O (Set.range ff)).comap (Submodule.span M.L.O (Set.range b)).subtype)

end ObjJ

end PI.SelfDualHermitianLattices

end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Ler

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def tupMul {m : ℕ} (y : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O) : Fin m → V :=
  fun a => ∑ i, ((A i a : M.L.O) : E) • y i

def lerCnt (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) (J : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) M.L.O) (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Nat.card {c : Fin m → (Λs ⧸ piIn H (ϖ ^ J) Λs) //
    ∃ x y : Fin m → Λs, (∀ a, Submodule.Quotient.mk (x a) = c a) ∧ PrimTup H Λs y ∧
      (fun a => (x a : V)) = tupMul (fun i => (y i : V)) A ∧ GramCong H (ϖ ^ J) (fun a => (x a : V)) Gm}

def ler (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) (J : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) M.L.O) (Gm : Matrix (Fin m) (Fin m) E) : ℝ :=
  (lerCnt H Λs ϖ J A Gm : ℝ) / (qF F : ℝ) ^ (J * (2 * Module.finrank E V * m - m ^ 2))

end Ler

def LatticeUnfoldingLerayVolume : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ K : Subgroup (V ≃ₗ[E] V), K ≤ fixZ H (Submodule.span E (Set.range ff)) →
        Commens K (fixZ H (Submodule.span E (Set.range ff)) ⊓ Aut Λs) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (b : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O), (∀ a, b a ∈ Submodule.span E (Set.range ff)) →
          ff = tupMul b A →
          ∀ Rs : Set (Submodule M.L.O V),
            IsTransv (OrbRel (fixZ H (Submodule.span E (Set.range ff))))
              (SigZ H (Submodule.span E (Set.range ff)) (Submodule.span M.L.O (Set.range b))) Rs →
            ∃ J0 : ℕ, ∀ J, J0 ≤ J →
              massOf (fixZ H (Submodule.span E (Set.range ff))) K Rs =
                ENNReal.ofReal (κ * ler H Λs ϖ J A (H.gram ff))

end PI.SelfDualHermitianLattices

end
end

section
noncomputable section

open scoped Classical
set_option linter.style.haveILetI false
open ValuativeRel

namespace PI.SelfDualHermitianLattices.Hd

open Formalism.MainNotions.S.Loc

section Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem locE_nontrivial (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega


theorem locE_algMap_mem (L : LocE F E) [IsNonarchimedeanLocalField F] {f : F} :
    algebraMap F E f ∈ L.O ↔ f ∈ 𝒪[F] := by
  haveI := locE_nontrivial L
  rw [L.O_def]
  constructor
  · intro h
    have h' : IsIntegral 𝒪[F] f :=
      (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F])
        (algebraMap F E).injective).mp h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
    rw [← hy]; exact y.2
  · intro h
    have : algebraMap F E f = algebraMap 𝒪[F] E ⟨f, h⟩ := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
    rw [this]; exact isIntegral_algebraMap



end Alg

section Alg2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


structure QBasis (L : LocE F E) where
  ω : E
  hω : ω ∈ L.O
  hnot : ω ∉ Set.range (algebraMap F E)
  t : 𝒪[F]
  n : 𝒪[F]
  hcj : L.cj ω = algebraMap F E (t : F) - ω
  hn : ω * L.cj ω = algebraMap F E (n : F)
  span : ∀ x ∈ L.O, ∃ a b : 𝒪[F], x = algebraMap F E (a : F) + algebraMap F E (b : F) * ω

theorem QBasis.sq {L : LocE F E} (Q : QBasis L) :
    Q.ω * Q.ω = algebraMap F E (Q.t : F) * Q.ω - algebraMap F E (Q.n : F) := by
  have := Q.hn; rw [Q.hcj] at this; rw [← this]; ring


end Alg2

section Alg3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_a_mod [IsNonarchimedeanLocalField F] (t n : 𝒪[F]) (hΔ : t * t - 4 * n ∈ 𝓂[F]) :
    ∃ a : 𝒪[F], t + 2 * a ∈ 𝓂[F] ∧ a * a - n ∈ 𝓂[F] := by
  by_cases h2 : IsUnit (2 : 𝒪[F])
  · obtain ⟨u, hu⟩ := h2
    have hmul : (u : 𝒪[F]) * ↑u⁻¹ = 1 := u.mul_inv
    refine ⟨-(t * ↑u⁻¹), ?_, ?_⟩
    · have : t + 2 * -(t * ↑u⁻¹) = 0 := by
        linear_combination (-t) * hmul + (t * ↑u⁻¹) * hu
      rw [this]; exact zero_mem _
    · have : -(t * ↑u⁻¹) * -(t * ↑u⁻¹) - n = ↑u⁻¹ * ↑u⁻¹ * (t * t - 4 * n) := by
        linear_combination (n * ((u : 𝒪[F]) * ↑u⁻¹ + 1)) * hmul +
          (-(n * ↑u⁻¹ * ↑u⁻¹ * ((u : 𝒪[F]) + 2))) * hu
      rw [this]; exact Ideal.mul_mem_left _ _ hΔ
  · have h2m : (2 : 𝒪[F]) ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr h2
    have htt : t * t ∈ 𝓂[F] := by
      have : t * t = (t * t - 4 * n) + 2 * (2 * n) := by ring
      rw [this]; exact add_mem hΔ (Ideal.mul_mem_right _ _ h2m)
    have ht : t ∈ 𝓂[F] := by
      rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem htt with h | h <;> exact h
    have h2k : (2 : 𝓀[F]) = 0 := by
      have := (IsLocalRing.residue_eq_zero_iff (2 : 𝒪[F])).mpr h2m
      rwa [map_ofNat] at this
    have hinj : Function.Injective (fun x : 𝓀[F] => x * x) := by
      intro x y hxy
      simp only at hxy
      have h1 : (x + y) * (x + y) = 0 := by
        linear_combination (-1 : 𝓀[F]) * hxy + (x * x + x * y) * h2k
      have h3 : x + y = 0 := mul_self_eq_zero.mp h1
      linear_combination h3 - y * h2k
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) (IsLocalRing.residue 𝒪[F] n)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
    refine ⟨a, add_mem ht (Ideal.mul_mem_right _ _ h2m), ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, ha]
    simp only at hr; rw [hr, sub_self]

variable (L : LocE F E) [IsNonarchimedeanLocalField F]

theorem QBasis.normE {L : LocE F E} (Q : QBasis L) (a b : F) :
    (algebraMap F E a + algebraMap F E b * Q.ω) * L.cj (algebraMap F E a + algebraMap F E b * Q.ω) =
      algebraMap F E (a * a + (Q.t : F) * a * b + (Q.n : F) * b * b) := by
  have hn := Q.hn
  rw [Q.hcj] at hn
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
  simp only [map_add, map_mul]
  linear_combination (algebraMap F E b * algebraMap F E b) * hn

end Alg3

end PI.SelfDualHermitianLattices.Hd
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

end PI.SelfDualHermitianLattices
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

namespace Hg

section TupDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def UGrp (H : HermSp M V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | IsUnitary H g}
  mul_mem' {a b} ha hb x y := by
    change H.h (a (b x)) (a (b y)) = H.h x y
    rw [ha (b x) (b y), hb x y]
  one_mem' x y := rfl
  inv_mem' {a} ha x y := by
    have h1 : ∀ v, a (a⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    change H.h (a⁻¹ x) (a⁻¹ y) = H.h x y
    rw [← ha (a⁻¹ x) (a⁻¹ y), h1, h1]

def FixT {m : ℕ} (x : Fin m → V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ a, g (x a) = x a}
  mul_mem' {a b} ha hb i := by
    change a (b (x i)) = x i
    rw [hb i, ha i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by
    change a⁻¹ (x i) = x i
    conv_lhs => rw [← ha i]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

def actT {m : ℕ} (g : V ≃ₗ[E] V) (x : Fin m → V) : Fin m → V := fun a => g (x a)

end TupDefs

end Hg

open Hg

end PI.SelfDualHermitianLattices
end
end
