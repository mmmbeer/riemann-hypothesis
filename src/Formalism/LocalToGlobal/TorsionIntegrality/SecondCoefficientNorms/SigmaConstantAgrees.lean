import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ChordSecondLogDeriv
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormClosed
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.JetExpShape

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def SigmaConstantAgrees : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (fa fb : G →+ G) (wp : G → K) (al be : K),
    (∀ Q, fb Q = 0 ↔ ∃ T, fa T = Q) → (∀ Q, fa Q = 0 ↔ ∃ T, fb T = Q) →
    (∀ T, fa T ≠ 0 → al ^ 2 * wp (fa T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), (wp (T + P) - wp P)) →
    (∀ T, fb T ≠ 0 → be ^ 2 * wp (fb T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fb P = 0 ∧ P ≠ 0), (wp (T + P) - wp P)) →
    al ^ 2 ≠ ((Finset.univ.filter (fun P => fa P = 0)).card : K) →
    be ^ 2 ≠ ((Finset.univ.filter (fun P => fb P = 0)).card : K) →
    s2Of (fun P : {P : G // fa P = 0 ∧ P ≠ 0} => wp P) al =
      s2Of (fun P : {P : G // fb P = 0 ∧ P ≠ 0} => wp P) be

def JetsAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    IsLogPair l linv → IsOneUnit R (PowerSeries.derivative K l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 3 ≤ i → jet l ph i ∈ R) →
    PhNormAt R l linv ph (-1) (-1) → (2 : K)⁻¹ ∈ R →
    AdjAt R l linv ph a b → (a - b)⁻¹ ∈ R → a ≠ b →
    ∀ i : ℕ, jet l (mvExp (-ph) : PowerSeries K) i ∈ R

end Formalism.L2.Th1.C
