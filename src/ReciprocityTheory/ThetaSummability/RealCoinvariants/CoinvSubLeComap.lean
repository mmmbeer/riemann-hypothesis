import Mathlib

section
noncomputable section

open Finset

namespace ReciprocityTheory.ThetaSummability.Real

section Defs

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def GlRel {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)

structure IsCCR {X : Type*} [DecidableEq X] (α β : X → Module.End ℂ M) : Prop where
  β_α : ∀ x y, β x * α y - α y * β x = if x = y then 1 else 0
  α_α : ∀ x y, α x * α y = α y * α x
  β_β : ∀ x y, β x * β y = β y * β x

variable {n N : ℕ}

end Defs

end ReciprocityTheory.ThetaSummability.Real
end
end

section
noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}

def coinvSub (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨆ i, LinearMap.range (Y i - μ i • 1)

def jointEig (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨅ i, LinearMap.ker (Y i - μ i • 1)

abbrev Coinv (Y : ι → Module.End ℂ M) (μ : ι → ℂ) := M ⧸ coinvSub Y μ

theorem coinvSub_le_comap {Y : ι → Module.End ℂ M} (μ : ι → ℂ) {T : Module.End ℂ M}
    (hT : ∀ i, Commute T (Y i)) : coinvSub Y μ ≤ (coinvSub Y μ).comap T := by
  unfold coinvSub
  apply iSup_le
  intro i
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_comap]
  apply Submodule.mem_iSup_of_mem i
  refine ⟨T y, ?_⟩
  have hc : T (Y i y) = Y i (T y) := by
    rw [← Module.End.mul_apply, (hT i).eq, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc]

def coinvOp {Y : ι → Module.End ℂ M} (μ : ι → ℂ) (T : Module.End ℂ M)
    (hT : ∀ i, Commute T (Y i)) : Module.End ℂ (Coinv Y μ) :=
  (coinvSub Y μ).mapQ (coinvSub Y μ) T (coinvSub_le_comap μ hT)

end ReciprocityTheory.ThetaSummability.Real
end
end
