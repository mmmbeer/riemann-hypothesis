import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
import Mathlib
import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ParamDefs

noncomputable section

open scoped BigOperators Classical Pointwise

namespace Formalism.InvariantFactorPaths.G0

open Formalism.G0

def ElementarySymmetricExpBound : Prop :=
  ∀ (V : ℕ) (κ : Fin V → ℝ) (m : ℝ), (∀ v, 0 ≤ κ v) → 0 ≤ m → m * ∑ v, κ v ≤ 1 / 2 →
    (∀ j : ℕ, m ^ j * esymmR κ j ≤ (m * ∑ v, κ v) ^ j / (j.factorial : ℝ)) ∧
    Summable (fun j : ℕ => (m * ∑ v, κ v) ^ (j + 1) / ((j + 1).factorial : ℝ)) ∧
    ∑' j : ℕ, (m * ∑ v, κ v) ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ 2 * (m * ∑ v, κ v)

def InvariantFactorsSubmodule : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R) (M M' P : Submodule R X) (g E : ℕ), P ≤ M' → M' ≤ M →
    AllButLE π M P g E → AllButLE π M' P g E

def InvShift : Prop :=
  ∀ {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] [Module R X]
    (π : R) (A B NA NB : Submodule R X) (g E e : ℕ), B ≤ A → NA ≤ A → π ^ e • NA ≤ NB → NB ≤ B →
    AllButLE π A NA g E → AllButLE π B NB g (E + e)

def AlmostEverywhereSpherical : Prop :=
  ∀ {R X Z : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Z] [Module R Z]
    (π : R) (vπ : ℝ) (V m : ℕ) (M : Submodule R X) (y : Fin V → Module.End R X) (Sv : Fin V → ℕ)
    (K : X →ₗ[R] Z) (Fil : ℝ → Submodule R Z) (g Pr g0 : Fin V → Fin m → ℝ) (rest : ℝ),
    Antitone Fil → (∀ t z, z ∈ Fil t → π • z ∈ Fil (t + vπ)) →
    (∀ v, (∑ j, pp (g v j - Pr v j - g0 v j)) ≤ vπ * (Sv v : ℝ)) →
    (∀ E : Fin V → Bool, ∀ F ∈ M, K (monoOp π y m (fun _ => 0) E F) ∈
      Fil ((∑ j, ((∑ v with E v = true, max (g v j - Pr v j) (g0 v j)) + ∑ v with E v = false, g0 v j)) + rest)) →
    ∀ F ∈ prodIdealMap π y m Sv M, K F ∈ Fil ((∑ j, ∑ v, max (g v j - Pr v j) (g0 v j)) + rest)

end Formalism.InvariantFactorPaths.G0
