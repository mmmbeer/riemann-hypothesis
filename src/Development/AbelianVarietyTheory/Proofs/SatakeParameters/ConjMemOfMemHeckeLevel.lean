import Mathlib

namespace GlobalTheory.HeckeCorr

variable {Gf : Type*} [Group Gf]

def cosetTr (U' U : Subgroup Gf) (g : Gf) (h : ∀ u ∈ U', g⁻¹ * u * g ∈ U) : Gf ⧸ U' → Gf ⧸ U :=
  Quotient.map' (· * g) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h _ hab
    convert this using 1
    group

theorem cosetTr_mk (U' U : Subgroup Gf) (g : Gf) (h : ∀ u ∈ U', g⁻¹ * u * g ∈ U) (x : Gf) :
    cosetTr U' U g h (x : Gf ⧸ U') = ((x * g : Gf) : Gf ⧸ U) := rfl

noncomputable def cosetTrace {U' U : Subgroup Gf} (h : U' ≤ U) {M : Type*} [AddCommMonoid M] (φ : Gf ⧸ U' → M)
    (c : Gf ⧸ U) : M :=
  ∑ᶠ y ∈ Subgroup.quotientMapOfLE h ⁻¹' {c}, φ y

def heckeLevel (U : Subgroup Gf) (g : Gf) : Subgroup Gf := U ⊓ U.map (MulAut.conj g).toMonoidHom

theorem heckeLevel_le (U : Subgroup Gf) (g : Gf) : heckeLevel U g ≤ U := inf_le_left

theorem conj_mem_of_mem_heckeLevel {U : Subgroup Gf} {g u : Gf} (hu : u ∈ heckeLevel U g) : g⁻¹ * u * g ∈ U := by
  obtain ⟨-, v, hv, rfl⟩ := hu
  simpa [MulAut.conj_apply, mul_assoc] using hv

end GlobalTheory.HeckeCorr
