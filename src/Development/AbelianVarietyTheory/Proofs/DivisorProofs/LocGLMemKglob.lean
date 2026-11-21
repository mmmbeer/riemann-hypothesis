import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerTwSplit
open GlobalTheory.EulerTw GlobalTheory.EulerTwU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem theta_mem {v w : Pl E} (f : v.adicCompletion E →+* w.adicCompletion E) (hf : ∀ x, Valued.v (f x) = Valued.v x)
    {g : GLw n v} (hg : g ∈ GlobalTheory.LFun.KGL v n) :
    thetaGL n (RingHom.id _) (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL w n := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f g := Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) (GeneralLinearGroup.map f g)) * (PhiU n _)⁻¹ ∈ _
  rw [hid]
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n) (GlobalTheory.BCT.LocGlue.intst E n v w f hf g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem thF_mem_Kglob {x : GL (Fin n) (Af E)} (hx : x ∈ Kglob E n) : thF E n x ∈ Kglob E n := by
  rw [mem_Kglob_iff] at hx ⊢
  intro v
  rw [pc_thF]
  exact theta_mem _ (conjLoc_spec _ v).2.2 (hx _)

set_option hygiene false in
local notation "PC[" v "]" => GeneralLinearGroup.map (pLoc E v)


end GlobalTheory.EulerTwSplit
