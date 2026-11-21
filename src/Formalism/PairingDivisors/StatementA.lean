import Mathlib
import Formalism.PairingDivisors.StatementH

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def ValAdd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (a b : K),
    a ≠ 0 → b ≠ 0 → a + b ≠ 0 → min (vw w a) (vw w b) ≤ vw w (a + b)

def eq {k : Type} [Field k] (q : ℕ) (s : ℕ) (Y : k) : k :=
  (1 - Y * ((q : k) ^ s)⁻¹) * (1 - Y⁻¹ * ((q : k) ^ s)⁻¹) + ((q : k) - 1) * (((q : k) ^ s)⁻¹) ^ 2

def UpperStays : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (P : Type) (R : Finset P)
    (y y' : K) (e : P → K) (B : ℝ),
    y ≠ 0 → y = y' * ∏ q ∈ R, e q → (∀ q ∈ R, 0 ≤ vw w (e q)) → (vw w y : ℝ) ≤ B →
    (vw w y' : ℝ) ≤ B

def GaussUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (G G' : 𝓞 K) (q : ℕ),
    1 ≤ q → (G : K) * (G' : K) = (q : K) → vw w (q : K) = 0 → vw w (G : K) = 0

def RatioVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : Pl K) (a a' : K) (g : ℤ),
    a ≠ 0 → a' ≠ 0 → vw w (a / a') = (vw w a + g) - (vw w a' + g)

end Formalism.PairingDivisionLocalBalance
