import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar

noncomputable section

open MeasureTheory Matrix GlobalTheory.WeilM ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.VacLoc

def intMat {E : Type} [CommRing E] (A : Subring E) (α β : Type) : AddSubgroup (Matrix α β E) where
  carrier := {x | ∀ i j, x i j ∈ A}
  zero_mem' := fun _ _ => zero_mem _
  add_mem' := fun hx hy i j => add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => neg_mem (hx i j)

structure Inert (k : Type) [Field k] [ValuativeRel k] {E : Type} [CommRing E] [Algebra k E] (c : E →ₐ[k] E) (ξ : E) :
    Prop where
  quad : IsQuad c ξ
  two : valuation k (2 : k) = 1
  sq : ∃ δ : k, valuation k δ = 1 ∧ ξ * ξ = algebraMap k E δ ∧ ∀ y : k, valuation k y ≤ 1 → valuation k (y * y - δ) = 1

def Unram {E : Type} [CommRing E] (A : Subring E) (χ : Eˣ →* Circle) : Prop :=
  ∀ z : Eˣ, (z : E) ∈ A → ((z⁻¹ : Eˣ) : E) ∈ A → χ z = 1

section Adelic

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intA : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun _ => zero_mem _
  one_mem' := fun _ => one_mem _
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)
  mul_mem' := fun hx hy v => mul_mem (hx v) (hy v)

abbrev EA : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

def cA (c : E →ₐ[F] E) : EA F E →ₐ[FiniteAdeleRing (𝓞 F) F] EA F E :=
  Algebra.TensorProduct.map (AlgHom.id _ _) c

def intE : Subring (EA F E) :=
  Subring.closure ((fun x => x ⊗ₜ[F] (1 : E)) '' (intA F : Set (FiniteAdeleRing (𝓞 F) F)) ∪
    Set.range fun y : 𝓞 E => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (y : E))

end Adelic

namespace Unr

def sqrtConj {k : Type} [Field k] (δ : k) : QuadraticAlgebra k δ 0 →ₐ[k] QuadraticAlgebra k δ 0 where
  toFun z := star z
  map_one' := star_one _
  map_mul' x y := star_mul' x y
  map_zero' := star_zero _
  map_add' := star_add
  commutes' r := by ext <;> simp

example {k : Type} [Field k] [ValuativeRel k] {E : Type} [CommRing E] [Algebra k E] {c : E →ₐ[k] E} {ξ : E}
    (h : Inert k c ξ) : ξ * ξ ≠ 1 := by
  obtain ⟨δ, -, h2, h3⟩ := h.sq
  intro e
  have e2 : δ = 1 := h.quad.algebraMap_injective (by rw [← h2, e, map_one])
  simpa [e2] using h3 1 (by simp)

example {E : Type} [CommRing E] (A : Subring E) : Unram A 1 ∧ (0 : Matrix Unit Unit E) ∈ intMat A Unit Unit :=
  ⟨fun _ _ _ => rfl, zero_mem _⟩

end Unr

end GlobalTheory.CompanionTheory.VacLoc
