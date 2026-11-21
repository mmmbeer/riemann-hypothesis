import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MirabolicColumnBlock
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

namespace UpperTheory.V.Lib.Small

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul X Y hX hY a

end UpperTheory.V.Lib.Small
