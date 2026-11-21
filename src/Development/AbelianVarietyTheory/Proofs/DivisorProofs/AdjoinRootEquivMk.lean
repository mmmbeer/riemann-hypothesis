import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

namespace GlobalTheory.LKCent

section Equiv

variable {F : Type} [Field F] {B : Type} [Ring B] [Algebra F B]

def gen (γ : B) : Algebra.adjoin F ({γ} : Set B) := ⟨γ, Algebra.self_mem_adjoin_singleton F γ⟩

theorem aeval_gen (γ : B) (p : Polynomial F) :
    ((Polynomial.aeval (gen (F := F) γ) p : Algebra.adjoin F ({γ} : Set B)) : B) = Polynomial.aeval γ p :=
  Polynomial.aeval_subalgebra_coe p _ _

end Equiv

section Star

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {B : Type} [Ring B] [StarRing B]
  [Algebra F B] [Algebra k B] [IsScalarTower k F B] (γ : B)

def starL (hk : ∀ t : k, star (algebraMap k B t) = algebraMap k B t)
    (hs : ∀ x ∈ Algebra.adjoin F ({γ} : Set B), star x ∈ Algebra.adjoin F ({γ} : Set B)) :
    Algebra.adjoin F ({γ} : Set B) →ₐ[k] Algebra.adjoin F ({γ} : Set B) where
  toFun x := ⟨star (x : B), hs _ x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    have h := mul_comm (⟨star (y : B), hs _ y.2⟩ : Algebra.adjoin F ({γ} : Set B)) ⟨star (x : B), hs _ x.2⟩
    ext
    simpa [star_mul] using congrArg Subtype.val h
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' t := by
    ext
    simp only [Subalgebra.coe_algebraMap]
    exact hk t

@[simp]
theorem coe_starL (hk : ∀ t : k, star (algebraMap k B t) = algebraMap k B t)
    (hs : ∀ x ∈ Algebra.adjoin F ({γ} : Set B), star x ∈ Algebra.adjoin F ({γ} : Set B))
    (x : Algebra.adjoin F ({γ} : Set B)) : ((starL k γ hk hs x : Algebra.adjoin F ({γ} : Set B)) : B) =
      star (x : B) := rfl

end Star

end GlobalTheory.LKCent
