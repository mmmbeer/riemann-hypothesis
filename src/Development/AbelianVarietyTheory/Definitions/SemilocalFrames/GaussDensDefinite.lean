import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

theorem lamX_one (I : AutInst) : lamX I (1, 1) = I.L := by
  refine le_antisymm (fun y hy => (I.L_dual y).2 fun z hz => ?_) (GlobalTheory.Count.Test.le_lamX_one I)
  exact ((GlobalTheory.PointLattice.lamX_selfDual I (1, 1)).2.2.2.1 y).1 hy z (GlobalTheory.Count.Test.le_lamX_one I hz)




variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isPerpInst_ofSigns (cm : Formalism.BasicNotions.CMData F E) {n : ℕ} (s : Bool) (ε : Fin n → Bool) :
    IsPerpInst (ofSigns cm (Fin.cons s ε : Fin (n + 1) → Bool)) (ofSigns cm ε) (RingEquiv.refl E) s
      (Pi.single (0 : Fin (n + 1)) (1 : E)) (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) 1 := by
  unfold IsPerpInst
  rw [lamX_one]
  refine ⟨fun _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ⬝ᵥ (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : E))) = sgn E s
    simp [signMat, sgn, dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal]
  · show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ᵥ* (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)) = 0
    funext j
    simp [signMat, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_mul, (Fin.succ_ne_zero j).symm]
  · show (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)ᴴ * signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) = (signMat E ε).map (RingEquiv.refl E)
    ext i j
    rw [Matrix.mul_apply]
    simp only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.map_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · show (Pi.single (0 : Fin (n + 1)) (1 : E)) ∈ intLat E (n + 1)
    exact Submodule.subset_span ⟨0, by simp⟩
  · show ∀ y : Fin n → E, y ∈ intLat E n ↔ (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ y ∈ intLat E (n + 1)
    intro y
    have e : (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ (y : Fin n → E)
        = (Fin.cons 0 y : Fin (n + 1) → E) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, (Fin.succ_ne_zero _).symm]
      · simp [Matrix.mulVec, dotProduct]
    rw [e, mem_intLat, mem_intLat, Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨fun h => ⟨zero_mem _, h⟩, fun h => h.2⟩

theorem exists_isPerpInst (n : ℕ) (s : Bool) :
    ∃ (I I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf),
      I.n = n + 1 ∧ IsPerpInst I I' e s x A xf := by
  obtain ⟨I, -⟩ := exists_signature 0 0
  exact ⟨_, _, _, _, _, _, rfl, isPerpInst_ofSigns I.cm s (fun _ : Fin n => true)⟩


end GlobalTheory.GaussMean.Test
