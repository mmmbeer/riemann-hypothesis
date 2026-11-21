import Formalism.CharacterColumnKernels.StatementMF

section
open Classical

noncomputable section

namespace Formalism.NG

universe u v

section Mult
variable (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]

abbrev csFactor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : Type u :=
  s i.succ ⧸ (s (Fin.castSucc i)).comap (s i.succ).subtype

def csMult (s : CompositionSeries (Submodule R M)) (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  (Finset.univ.filter fun i : Fin s.length => Nonempty (csFactor R M s i ≃ₗ[R] S)).card

def IsFullSeries (s : CompositionSeries (Submodule R M)) : Prop := s.head = ⊥ ∧ s.last = ⊤

def compMult (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  if h : ∃ s : CompositionSeries (Submodule R M), IsFullSeries R M s then
    csMult R M (Classical.choose h) S
  else 0

end Mult

end Formalism.NG
end
end

section
open Classical

noncomputable section

namespace Formalism.NG

universe u v w

def StatCompMultSimple : Prop :=
  ∀ (R : Type*) [Ring R] (T : Type u) [AddCommGroup T] [Module R T] (S : Type v) [AddCommGroup S]
    [Module R S], IsSimpleModule R T →
    compMult R T S = if Nonempty (T ≃ₗ[R] S) then 1 else 0

end Formalism.NG
end
end
