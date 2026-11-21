import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem subsingleton_obj_of_isEmpty (G : Shv R) (U : Scheme.{0}) [IsEmpty U] :
    Subsingleton (G.val.obj (op U)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_propQCTopology (P := @WeaklyEtale) U)).isZero

end GlobalTheory.Et

end
