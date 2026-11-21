import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffModel

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}



def HasFrames (p : SplitPt D k) : Prop :=
  ∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k),
    b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b

theorem HasFrames.nonempty {p : SplitPt D k} (h : HasFrames p) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (hn : Fintype.card n = S.rank) : Nonempty (Frame p S n) := by
  let e : n ≃ Fin S.rank := Fintype.equivFinOfCardEq hn
  obtain ⟨β, -⟩ := h S n ((1 : Matrix n n k).submatrix e.symm id) ((1 : Matrix n n k).submatrix id e.symm)
    ((Matrix.submatrix_mul_equiv (1 : Matrix n n k) 1 e.symm (Equiv.refl n) e.symm).trans (by simp))
    (by rw [Matrix.submatrix_mul_equiv (e₂ := e.symm)]; simp)
  exact ⟨β⟩


variable {d : Dat D u} {o : OffDat d k ι}

end GlobalTheory.FinPl.OffModel

end
