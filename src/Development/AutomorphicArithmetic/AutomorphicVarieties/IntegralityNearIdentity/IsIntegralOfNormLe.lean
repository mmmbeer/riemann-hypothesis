import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfCoeff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EigenMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdMulMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralOfNormLe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne

namespace UpperTheory.V.Lib.Small


theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W :=
  _root_.UpperTheory.Reformulated.B.S3.single_mem W d hd hW v hv i hi

theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z :=
  _root_.UpperTheory.Reformulated.B.S4.isIntegral_of_norm_le hz

end UpperTheory.V.Lib.Small
