import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def fT (L : PeriodPair) (t z : ℂ) : ℂ := opU L t (sgStar L) z / sgStar L z

def thetaZeroCharacter (L : PeriodPair) (ω₀ ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))

def FtQuasi : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice →
    fT L t (z + ω) = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L ω t : ℂ)) * fT L t z

def OpUTh0 : Prop :=
  ∀ (L : PeriodPair) (t x z : ℂ),
    opU L x (th0 L t) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x t : ℂ)) * opU L (x + t) (sgStar L) z
        / opU L t (sgStar L) 0

def ThetaZeroTranslateProduct : Prop :=
  ∀ (L : PeriodPair) (t P Q z : ℂ), Q ∉ L.lattice → z + P + t ∉ L.lattice →
    opU L (P + Q) (th0 L t) z * opU L (P - Q) (th0 L t) z
      = opU L Q (sgStar L) 0 ^ 2 * (L.weierstrassP Q - L.weierstrassP (z + P + t))
        * opU L P (th0 L t) z ^ 2

def ThetaZeroLine : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (F : ℂ → ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, F (z + ω) = thetaZeroCharacter L ω₀ ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * F z) →
    ∀ z, F z = F 0 * th0 L (ω₀ / 2) z

def IsFibreReps (L : PeriodPair) (α t : ℂ) (T : Finset ℂ) : Prop :=
  (∀ Q ∈ T, α * Q - t ∈ L.lattice ∧ 2 * Q ∉ L.lattice) ∧
  (∀ Q ∈ T, ∀ Q' ∈ T, (Q - Q' ∈ L.lattice ∨ Q + Q' ∈ L.lattice) → Q = Q') ∧
  (∀ z, α * z - t ∈ L.lattice → ∃ Q ∈ T, z - Q ∈ L.lattice ∨ z + Q ∈ L.lattice)

end Formalism.L2.Th1.F
