import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions Finset

section
variable {p : ℕ} [Fact p.Prime]

end

section
variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

end

section LeafEx

variable {K : Type} [Field K] (p : ℕ) {h : ℕ}

end LeafEx

section LeafUn

variable {K : Type} [Field K] (p : ℕ) {h : ℕ}

end LeafUn

section
variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

end
section
variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

end

section
variable (p : ℕ) {Kc : Type} [Field Kc]

end

section
variable {Kc : Type} [Field Kc] (Oc : Subring Kc)

variable (p : ℕ)

end

section
variable {p : ℕ} {Kc : Type} [Field Kc] {Oc : Subring Kc}

theorem deg2 (n : Fin 2 →₀ ℕ) : n.degree = n 0 + n 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

def DD (p : ℕ) (Oc : Subring Kc) (vp : Kc) (H : MvPowerSeries (Fin 2) Kc) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, vp ^ n.degree * (p : Kc) ^ (n 1 / p) * MvPowerSeries.coeff n H ∈ Oc

end

end Formalism.MainNotions.KernelEntryData
