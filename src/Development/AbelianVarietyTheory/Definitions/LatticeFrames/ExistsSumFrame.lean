import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.DblInh

variable {D : D7}

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def conjHom {R : Type} [CommRing R] (x : Matrix n m R) (y : Matrix m n R) (hx : x * y = 1) (hy : y * x = 1) :
    Matrix m m R →* Matrix n n R where
  toFun g := x * g * y
  map_one' := by rw [Matrix.mul_one, hx]
  map_mul' g h := by
    rw [Matrix.mul_assoc (x * g), ← Matrix.mul_assoc y, ← Matrix.mul_assoc y, hy, Matrix.one_mul]
    simp only [Matrix.mul_assoc]

def rebase {S : HSp D} (β : Frame p S n) (b : Matrix (Fin S.rank) m k) (b' : Matrix m (Fin S.rank) k) (h : b * b' = 1)
    (h' : b' * b = 1) : Frame p S m where
  b := b
  b' := b'
  bb' := h
  b'b := h'
  gl := β.gl.comp (Units.map (conjHom (β.b' * b) (b' * β.b)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc b, h, Matrix.one_mul, β.b'b])
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, h'])))
  gl_supp g := β.gl_supp _
  gl_mat g := by
    refine (β.gl_mat _).trans ?_
    change β.b * (β.b' * b * g.val * (b' * β.b)) * β.b' = _
    simp only [← Matrix.mul_assoc, β.bb', Matrix.one_mul]
    rw [Matrix.mul_assoc _ β.b, β.bb', Matrix.mul_one]

theorem exists_sumFrame {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    (β : Frame p A (Fin A.rank)) (γ : Frame p S n) : ∃ β₀ : Frame p S (Fin A.rank ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let w : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hw : w ⬝ᵥ ζ = 1 := by
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let M : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (vecB o ζ))
  let N : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (w ᵥ* o.qB))
  have hNM : N * M = 1 := by
    rw [fromRows_mul_fromCols, o.qA_iA, ← replicateCol_mulVec, vecB, mulVec_mulVec, o.qA_iB, zero_mulVec,
      ← replicateRow_vecMul, vecMul_vecMul, o.qB_iA, vecMul_zero, replicateRow_mul_replicateCol, dotProduct_mulVec,
      vecMul_vecMul, o.qB_iB, vecMul_one, hw, replicateCol_zero, replicateRow_zero, ← fromBlocks_one]
    congr 1
    ext i j
    rw [Subsingleton.elim i j, one_apply_eq, of_apply]
  let X : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have h1 : (X' * N.map f) * (M.map f * X) = (1 : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (N.map f), ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, fromBlocks_multiply]
    simp [β.b'b]
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← o.rank_add, hζ.1])).1 h1
  refine ⟨rebase γ _ _ h2 h1, ?_⟩
  change M.map f * X = _
  rw [fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  rfl

end Frames

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

def stdLat {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) : DblLat B J B' :=
  ⟨PlaceModel.latFrame _, PlaceModel.latFrame _, PlaceModel.latFrame _, PlaceModel.latFrame _, PlaceModel.latFrame _,
    PlaceModel.latFrame _⟩

end GlobalTheory.FinPl.DblInh

end
