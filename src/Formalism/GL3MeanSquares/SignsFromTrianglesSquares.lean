import Mathlib
import Formalism.GL3MeanSquares.ModelCocycleExponent

noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

def ImHGenusOne : Prop :=
  ∀ (d x0 x1 y0 y1 : ℝ), 0 < d →
    (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).im /
        (Real.sqrt d / 2) = x1 * y0 - x0 * y1 ∧
    2 * (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).re =
        2 * (x0 * y0 + x0 * y1 + (1 + d) / 4 * (x1 * y1)) + (x1 * y0 - x0 * y1)

def Heisenberg₂ {V : Type} [AddCommGroup V] (H : V → V → ℂ) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2)

def HeisenbergCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V),
      Heisenberg₂ H x (Heisenberg₂ H y F) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x y).im : ℂ))) * Heisenberg₂ H (x + y) F z

def TranslateProduct : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (s : V → ℂ) (w : V → V → ℂ), (∀ a b, s (a + b) * s (a - b) = w a b * s a ^ 2 * s b ^ 2) →
    ∀ P Q z : V, Heisenberg₂ H (P + Q) s z * Heisenberg₂ H (P - Q) s z =
      (Heisenberg₂ H Q s 0) ^ 2 * w (z + P) Q * (Heisenberg₂ H P s z) ^ 2

def SumExpansion : Prop :=
  ∀ (M Q : Type) [AddCommGroup M] [AddCommGroup Q] (φ : M → Q),
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    ∀ (k : ℕ) (a : Fin k → M),
      φ (∑ j, a j) =
        (∑ j, φ (a j)) + ∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'), cob φ (a j) (a j')

def GramExpansion : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n : Type) [Fintype n] (k : ℕ) (A : n → Fin k → O) (u : Fin k → M),
      ∑ i, φ (∑ j, A i j • u j) =
        (∑ j, (∑ i, nm (A i j)) • φ (u j)) +
          ∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'),
            cob φ ((∑ i, star (A i j') * A i j) • u j) (u j')

def OddOrderDetermined : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [Fintype G] [CommGroup H] (Φ Φ' : G → H) (B : G → G → H),
    Odd (Fintype.card G) →
    (∀ x y, Φ (x + y) = Φ x * Φ y * B x y) → (∀ x y, Φ' (x + y) = Φ' x * Φ' y * B x y) →
    (∀ x, Φ (-x) = Φ x) → (∀ x, Φ' (-x) = Φ' x) → ∀ x, Φ x = Φ' x

def SignsFromTrianglesSquares : Prop :=
  ∀ (X X' : Type) [Nonempty X] [Nonempty X'] (s1 : X → X → X' → ℤˣ) (s2 : X → X' → X' → ℤˣ),
    (∀ L L1 L2 L', s1 L L1 L' * s1 L1 L2 L' = s1 L L2 L') →
    (∀ L L' L'' L''', s2 L L' L'' * s2 L L'' L''' = s2 L L' L''') →
    (∀ L L1 L' L'', s1 L L1 L' * s2 L1 L' L'' = s2 L L' L'' * s1 L L1 L'') →
    ∃ ε : X → X' → ℤˣ, (∀ L L1 L', ε L L' * s1 L L1 L' = ε L1 L') ∧
      ∀ L L' L'', ε L L' * s2 L L' L'' = ε L L''

def ModelCocycleTwoSwapped : Prop :=
  ∀ δ a b : ℚ_[2], δ ≠ 0 →
    ((-(1 + δ)) / (2 * δ)) * ((a + b * δ) / 2) + ((1 - δ) / (2 * δ)) * ((a - b * δ) / 2) =
      -((a + b) / 2)

end Formalism.HermitianLattices.WeilRepresentation
