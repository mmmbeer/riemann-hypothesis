import Formalism.RankGapBounds.UniformMeanBound
import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData

open Real

namespace Formalism.RankGapBounds.UniformMeanTopLine

open Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

end

def C0 : Consts := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

noncomputable def D0 : Data Unit (fun _ => Unit) Unit 1 1 where
  x := 1
  ε := 0
  a := 1
  b := 1
  b' := 0
  k := 1
  L := 0
  La := 0
  B0 := 0
  Nc := 0
  gam := 0
  LpL := 0
  v := π
  lg := 0
  logGam := 0
  aT := fun _ => 1
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 1
  muMaxN := fun _ _ => 1
  h := fun _ _ => -1
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 2
  muMinCC := fun _ => 2
  Fo := fun _ => 2
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

end Formalism.RankGapBounds.UniformMeanTopLine
