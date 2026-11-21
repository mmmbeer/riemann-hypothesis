import Formalism.YangianSpanCharacter.StatementY

namespace Formalism.YangianSpanCharacter.Y

open Matrix Formalism.YangianSpanCharacter.T

def tE (u : ℚ) : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℚ) :=
  !![!![u + 1, 0; 0, u], !![0, 1; 0, 0]; !![0, 0; 1, 0], !![u, 0; 0, u + 1]]

def τE (u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![u⁻¹, 0; 0, (u + 1)⁻¹]

def qE (Y : ℚ) : ℚ := Y * (Y + 2)

def SE : Set ℚ := {u | u ≠ 0 ∧ u + 1 ≠ 0}

def ModHypYangian : Prop :=
  ModHyp tE τE qE SE ∧ tE 0 1 1 ≠ tE 1 1 1 ∧
    tE 0 0 1 * tE 0 1 0 - tE 0 1 0 * tE 0 0 1 ≠ 0 ∧ (1 : ℚ) ∈ SE

end Formalism.YangianSpanCharacter.Y
