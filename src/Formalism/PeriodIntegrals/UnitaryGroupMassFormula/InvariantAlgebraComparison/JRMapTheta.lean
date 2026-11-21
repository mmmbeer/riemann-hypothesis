import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantAlgebraComparison.InvAlgOfSteps

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem hmat_mul (I : AutInst) (g h : HAd I) : hmat I (g * h) = hmat I g * hmat I h := rfl

theorem hmat_one (I : AutInst) : hmat I 1 = 1 := rfl

theorem P_mul_inv (I : AutInst) (v : InfinitePlace I.F) : I.P v * (I.P v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem P_inv_mul (I : AutInst) (v : InfinitePlace I.F) : (I.P v)⁻¹ * I.P v = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))

theorem ofHAInf_mul (I : AutInst) (g h : HAd I) (v : InfinitePlace I.F) :
    ofHAInf I (g * h) v = ofHAInf I g v * ofHAInf I h v := by
  unfold ofHAInf
  rw [hmat_mul, Matrix.map_mul]
  set A := (hmat I g).map (thetaV I v)
  set B := (hmat I h).map (thetaV I v)
  set P := I.P v
  calc P⁻¹ * (A * B) * P = P⁻¹ * A * (P * P⁻¹) * B * P := by
        rw [P_mul_inv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = P⁻¹ * A * P * (P⁻¹ * B * P) := by simp only [Matrix.mul_assoc]

theorem ofHAInf_one (I : AutInst) (v : InfinitePlace I.F) : ofHAInf I 1 v = 1 := by
  unfold ofHAInf
  rw [hmat_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, P_inv_mul]

theorem ofHAFin_mul (I : AutInst) (g h : HAd I) :
    ofHAFin I (g * h) = ofHAFin I g * ofHAFin I h := by
  unfold ofHAFin
  rw [hmat_mul, Matrix.map_mul]

theorem ofHAFin_one (I : AutInst) : ofHAFin I 1 = 1 := by
  unfold ofHAFin
  rw [hmat_one, Matrix.map_one _ (map_zero _) (map_one _)]

def infU (I : AutInst) (h : HAd I) (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨ofHAInf I h v, ofHAInf I h⁻¹ v,
    by rw [← ofHAInf_mul, mul_inv_cancel, ofHAInf_one],
    by rw [← ofHAInf_mul, inv_mul_cancel, ofHAInf_one]⟩, ofHAInf_mem I h v⟩

def finU (I : AutInst) (h : HAd I) : I.Gf :=
  ⟨⟨ofHAFin I h, ofHAFin I h⁻¹,
    by rw [← ofHAFin_mul, mul_inv_cancel, ofHAFin_one],
    by rw [← ofHAFin_mul, inv_mul_cancel, ofHAFin_one]⟩, ofHAFin_mem I h⟩

def bridgeHom (I : AutInst) : HAd I →* I.GA where
  toFun h := (fun v => infU I h v, finU I h)
  map_one' := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext (ofHAInf_one I v))
    · exact Subtype.ext (Units.ext (ofHAFin_one I))
  map_mul' g h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext (ofHAInf_mul I g h v))
    · exact Subtype.ext (Units.ext (ofHAFin_mul I g h))

end PI.UnitaryGroupMassFormula.BridgeInvAlg
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem matEq_of_inj (hi : ThetaInj) (I : AutInst)
    {A B : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)}
    (hv : ∀ v, A.map (thetaV I v) = B.map (thetaV I v)) (hf : A.map (tauF I) = B.map (tauF I)) :
    A = B := by
  ext i j
  apply hi I
  rw [theta_apply, theta_apply]
  refine Prod.ext (funext fun v => ?_) ?_
  · exact congrArg (fun M => M i j) (hv v)
  · exact congrArg (fun M => M i j) hf

end PI.UnitaryGroupMassFormula.BridgeInvAlg
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.BridgeInvAlg

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def pre (hs : ThetaSurj) (I : AutInst) (z : (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E := (hs I z).choose

theorem theta_pre (hs : ThetaSurj) (I : AutInst)
    (z : (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Theta I (pre hs I z) = z :=
  (hs I z).choose_spec

def coZ (I : AutInst) (y : I.GA) (i j : Fin I.n) :
    (InfinitePlace I.F → ℂ) × (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  (fun v => (I.P v * uMat (y.1 v) * (I.P v)⁻¹) i j, I.fmat y.2 i j)

def coM (hs : ThetaSurj) (I : AutInst) (y : I.GA) :
    Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  Matrix.of fun i j => pre hs I (coZ I y i j)

theorem coM_theta (hs : ThetaSurj) (I : AutInst) (y : I.GA) (v : InfinitePlace I.F) :
    (coM hs I y).map (thetaV I v) = I.P v * uMat (y.1 v) * (I.P v)⁻¹ := by
  ext i j
  exact congrArg (fun z => z.1 v) (theta_pre hs I (coZ I y i j))

theorem coM_tau (hs : ThetaSurj) (I : AutInst) (y : I.GA) :
    (coM hs I y).map (tauF I) = I.fmat y.2 := by
  ext i j
  exact congrArg (fun z => z.2) (theta_pre hs I (coZ I y i j))

theorem coM_mul (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) (y z : I.GA) :
    coM hs I (y * z) = coM hs I y * coM hs I z := by
  apply matEq_of_inj hi I
  · intro v
    rw [Matrix.map_mul, coM_theta, coM_theta, coM_theta]
    have : uMat ((y * z).1 v) = uMat (y.1 v) * uMat (z.1 v) := rfl
    rw [this]
    calc I.P v * (uMat (y.1 v) * uMat (z.1 v)) * (I.P v)⁻¹
        = I.P v * uMat (y.1 v) * 1 * uMat (z.1 v) * (I.P v)⁻¹ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = I.P v * uMat (y.1 v) * (I.P v)⁻¹ * (I.P v * uMat (z.1 v) * (I.P v)⁻¹) := by
          rw [← P_inv_mul I v]; simp only [Matrix.mul_assoc]
  · rw [Matrix.map_mul, coM_tau, coM_tau, coM_tau]
    rfl

theorem coM_one (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) : coM hs I 1 = 1 := by
  apply matEq_of_inj hi I
  · intro v
    rw [coM_theta, Matrix.map_one _ (map_zero _) (map_one _)]
    have : uMat ((1 : I.GA).1 v) = 1 := rfl
    rw [this, Matrix.mul_one, P_mul_inv]
  · rw [coM_tau, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem cT_map_theta (I : AutInst) (v : InfinitePlace I.F)
    (M : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (thetaV I v) =
      (M.map (thetaV I v))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, thetaV_sigR]

theorem JR_map_theta (I : AutInst) (v : InfinitePlace I.F) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (thetaV I v) = I.J.map (I.φ v) := by
  ext i j
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, thetaV_inclR]

theorem tauF_sigR (I : AutInst) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (tauF I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, tauF_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cT_map_tau (I : AutInst)
    (M : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (tauF I) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (M.map (tauF I)) := by
  ext i j
  simp [Formalism.UG.cT, tauF_sigR]

theorem JR_map_tau (I : AutInst) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (tauF I) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, tauF_inclR]

theorem conj_unitary (I : AutInst) (v : InfinitePlace I.F) (X : Matrix (Fin I.n) (Fin I.n) ℂ)
    (hX : Xᴴ * Formalism.REAL.Jm (I.ε v) * X = Formalism.REAL.Jm (I.ε v)) :
    (I.P v * X * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * X * (I.P v)⁻¹) = I.J.map (I.φ v) := by
  set P := I.P v
  set Q := (I.P v)⁻¹
  set Jv := I.J.map (I.φ v)
  have hS : Pᴴ * Jv * P = Formalism.REAL.Jm (I.ε v) := I.P_spec v
  have hPQ : P * Q = 1 := P_mul_inv I v
  have hJ : Jv = Qᴴ * Formalism.REAL.Jm (I.ε v) * Q := by
    rw [← hS]
    calc Jv = (P * Q)ᴴ * Jv * (P * Q) := by
          rw [hPQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * (Pᴴ * Jv * P) * Q := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  calc (P * X * Q)ᴴ * Jv * (P * X * Q)
      = Qᴴ * (Xᴴ * (Pᴴ * Jv * P) * X) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jv := by rw [hS, hX, ← hJ]

theorem coM_mem (hi : ThetaInj) (hs : ThetaSurj) (I : AutInst) (y : I.GA) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) (coM hs I y) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * coM hs I y =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J := by
  apply matEq_of_inj hi I
  · intro v
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_theta, JR_map_theta, coM_theta]
    exact conj_unitary I v _ (y.1 v).2
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_tau, JR_map_tau, coM_tau]
    exact y.2.2

end PI.UnitaryGroupMassFormula.BridgeInvAlg
end
end
