import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

theorem SoleTerm.mono {ι : Type} {C : ι → ℂ} {p q p' q' : ι → Prop} (h : SoleTerm C p q) (hp : ∀ i, p i → p' i)
    (hq : ∀ i, q' i → q i) : SoleTerm C p' q' := by
  obtain ⟨i, h0, h1, hu⟩ := h
  exact ⟨i, h0, hp i h1, fun j hj hj' => hu j hj (hq j hj')⟩

example : ¬ SoleTerm (![1, -1] : Fin 2 → ℂ) (fun _ => True) (fun _ => True) := by
  rintro ⟨i, -, -, hu⟩
  exact absurd ((hu 0 (by simp) trivial).trans (hu 1 (by simp) trivial).symm) (by decide)

example : SoleTerm (![2, 0] : Fin 2 → ℂ) (fun _ => True) (fun _ => True) :=
  ⟨0, by simp, trivial, fun i hi _ => by fin_cases i <;> simp_all⟩

example : SoleTerm (![2, -2] : Fin 2 → ℂ) (· = 0) (· = 0) := ⟨0, by simp, rfl, fun _ _ h => h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
