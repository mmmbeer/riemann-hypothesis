import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def strictCone (ϖ : kˣ) (r : ℕ) : Set (Fin r → kˣ) :=
  {t | ∃ a : Fin r → ℤ, StrictAnti a ∧ t = fun i => ϖ ^ a i}

open Classical in

def IsExp {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V)
    (E : Multiset ((Fin r → kˣ) →* ℂˣ)) : Prop :=
  ∀ χ, expMult π χ = (E.count χ : ℕ∞)

def charSum {r : ℕ} (E : Multiset ((Fin r → kˣ) →* ℂˣ)) (t : Fin r → kˣ) : ℂ :=
  (E.map fun χ => (χ t : ℂ)).sum

def ExponentsSeparate : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (r n : ℕ) (V : Fin n → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (π : ∀ i, Representation ℂ (GL (Fin r) k) (V i)),
      (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) →
      (∀ i j, i ≠ j → IsEmpty ((π i).Equiv (π j))) →
      (∀ i, fixed (π i) (iwahori k (Fin r)) ≠ ⊥) →
      ∀ (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)), (∀ i, IsExp (π i) (E i)) →
        ∀ c : Fin n → ℂ, (∀ t ∈ strictCone ϖ r, ∑ i, c i * charSum (E i) t = 0) → ∀ i, c i = 0

theorem IsExp.unique {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin r) k) V} {E E' : Multiset ((Fin r → kˣ) →* ℂˣ)}
    (h : IsExp π E) (h' : IsExp π E') : E = E' := by
  classical
  refine Multiset.ext.2 fun χ => ?_
  have := (h χ).symm.trans (h' χ)
  convert Nat.cast_injective (R := ℕ∞) this

theorem IsExp.unramified {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin r) k) V} {E : Multiset ((Fin r → kˣ) →* ℂˣ)}
    (h : IsExp π E) {χ : (Fin r → kˣ) →* ℂˣ} (hχ : χ ∈ E) {t : Fin r → kˣ}
    (ht : t ∈ torusO k (Fin r)) : χ t = 1 := by
  classical
  have h0 : expMult π χ ≠ 0 := by
    rw [h χ]
    have : Multiset.count χ E ≠ 0 := Multiset.count_ne_zero.2 hχ
    intro h1
    apply this
    convert Nat.cast_eq_zero.1 h1
  have h1 := Model.scalar_of_isSubquotient (g := t) (c := 1) (JHMult.jhMult_ne_zero_iff.1 h0)
    (fun v => Subtype.ext (by
      have h2 : jacBU π t v.1 = _ := v.2 ⟨t, ht⟩
      show jacBU π t v.1 = _
      simpa using h2)) 1
  ext
  simpa using h1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

example (ϖ : kˣ) (r : ℕ) : (fun i : Fin r => ϖ ^ (-((i : ℕ) : ℤ))) ∈ strictCone ϖ r :=
  ⟨fun i => -((i : ℕ) : ℤ), fun i j h => by have : (i : ℕ) < j := h; simp only; omega, rfl⟩




end GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries
