import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocks
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetry
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker

open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.HCWhittaker

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

section Transport

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem glEquiv_mem_unip (e : α ≃ β) {s : ℕ} (b' : β → Fin s) {u : GL α K}
    (hu : u ∈ unip K (b' ∘ e)) : glEquiv K e u ∈ unip K b' := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have val : ∀ (g : GL α K) (i j : β), ((glEquiv K e g : GL β K) : Matrix β β K) i j =
      (g : Matrix α α K) (e.symm i) (e.symm j) := fun _ _ _ => rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [val]
    exact h1 _ _ (by simpa using hij)
  · intro i j hij
    rw [← map_inv, val]
    exact h2 _ _ (by simpa using hij)
  · intro i j hij
    rw [val, h3 _ _ (by simpa using hij)]
    simp

end Transport

section Matrices

variable {N s : ℕ}

end Matrices

section Term

variable {N s k : ℕ} (b : Fin N → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

end Term

end GlobalTheory.CompanionTheory.TyFin.HCWhittaker
