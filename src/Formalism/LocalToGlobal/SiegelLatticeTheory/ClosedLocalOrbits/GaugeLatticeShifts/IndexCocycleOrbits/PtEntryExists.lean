import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

noncomputable section

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits.CU

open Formalism.MainNotions.S Matrix

theorem ptEntry_symm {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (i j : ℕ), ptEntry bs i j = ptEntry bs j i
  | [], _, _ => rfl
  | (t, s) :: bs, i, j => by
    simp only [ptEntry]
    rw [ptEntry_symm bs (i - s) (j - s)]
    split_ifs <;> first | rfl | (exfalso; omega)




structure Mono {N : ℕ} {K : Type*} [Zero K] (P : Matrix (Fin N) (Fin N) K) : Prop where
  ex : ∀ i, ∃ j, P i j ≠ 0
  row : ∀ i j j', P i j ≠ 0 → P i j' ≠ 0 → j = j'
  col : ∀ i i' j, P i j ≠ 0 → P i' j ≠ 0 → i = i'


end Formalism.L2.SG.Pf.IndexCocycleOrbits.CU
