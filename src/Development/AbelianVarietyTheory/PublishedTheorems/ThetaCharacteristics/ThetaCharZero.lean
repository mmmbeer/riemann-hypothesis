import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def CanonKeySt : Prop :=
  ∃ κ : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R], KeyIn R → Rˣ,
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R], GlobalTheory.KeyPow.ClauseH R (fun _ => 1) 1 (κ R)) ∧
    (∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
      [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsPrincipalIdealRing R'] (f : R →+* R') (x : KeyIn R) (x' : KeyIn R'),
      KeyPB x' x f → (κ R' x' : R') = f (κ R x)) ∧
    ∀ (x : KeyIn ℂ) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 0 0 1 → κ ℂ x = 1

namespace CanonKeySt

theorem const_pow (g : ℕ) :
    ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 = (2 * Real.pi : ℂ) ^ (4 * g) := by
  rw [← pow_mul, Nat.mul_comm g 4, pow_mul, pow_mul, mul_pow, Complex.I_pow_four, _root_.mul_one]

end CanonKeySt

end GlobalTheory.Published
