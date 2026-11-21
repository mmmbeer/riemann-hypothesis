import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents

section
noncomputable section

namespace GlobalTheory.StdPairLoc

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

variable {F : Type} [Field F] [NumberField F]

section Blocks

variable {R : Type} {n a m : ℕ}

def leftBlock (X : Matrix (Fin n) (Fin (a + m)) R) : Matrix (Fin n) (Fin a) R := fun i j => X i (Fin.castAdd m j)

def rightBlock' (X : Matrix (Fin n) (Fin (a + m)) R) : Matrix (Fin n) (Fin m) R := fun i j => X i (Fin.natAdd a j)

end Blocks

def InPow (v : Pl F) (c : ℕ) (x : Fv F v) : Prop := ((unifAt v : Fv F v) ^ c)⁻¹ * x ∈ v.adicCompletionIntegers F

def InGLO (v : Pl F) {p : ℕ} (A : Matrix (Fin p) (Fin p) (Fv F v)) : Prop :=
  (∀ i j, A i j ∈ v.adicCompletionIntegers F) ∧ A.det ≠ 0 ∧ A.det⁻¹ ∈ v.adicCompletionIntegers F

open Classical in

def stdBig (v : Pl F) (ν : (Fv F v)ˣ →* ℂˣ) {a m : ℕ} (X : Matrix (Fin a) (Fin (a + m)) (Fv F v)) : ℂ :=
  if h : InGLO v (leftBlock X) ∧ ∀ i j, InPow v (condExp ν) (rightBlock' X i j) then
    (((ν (Units.mk0 _ h.1.2.1))⁻¹ : ℂˣ) : ℂ) else 0

open Classical in

def stdSmall (v : Pl F) (ν : (Fv F v)ˣ →* ℂˣ) {a' a : ℕ} (Y : Matrix (Fin a') (Fin (a + a')) (Fv F v)) : ℂ :=
  if h : (∀ i j, InPow v (condExp ν) (leftBlock Y i j)) ∧ InGLO v (rightBlock' Y) then
    (((ν (Units.mk0 _ h.2.2.1))⁻¹ : ℂˣ) : ℂ) else 0

section Ins

variable {R : Type} [Zero R] {a b : ℕ}

def insB (Y : Matrix (Fin a) (Fin (a + b)) R) (t : Fin a → R) : Matrix (Fin a) (Fin (a + (b + 2))) R := fun i j =>
  if h₁ : j.1 < a then Y i ⟨j.1, by omega⟩ else if h₂ : j.1 = a then t i else if h₃ : j.1 = a + b + 1 then 0 else
    Y i ⟨j.1 - 1, by have := j.2; omega⟩

def insS (Y : Matrix (Fin b) (Fin (a + b)) R) (r : Fin (a + (b + 2)) → R) (c : Fin b → R) (l : R) :
    Matrix (Fin (b + 2)) (Fin (a + (b + 2))) R := fun i j =>
  if i0 : i.1 = 0 then (if j.1 = a + b + 1 then l else 0) else if i1 : i.1 = b + 1 then r j else
    if h₁ : j.1 < a then Y ⟨i.1 - 1, by have := i.2; omega⟩ ⟨j.1, by omega⟩ else if h₂ : j.1 = a then 0 else
      if h₃ : j.1 = a + b + 1 then c ⟨i.1 - 1, by have := i.2; omega⟩ else
        Y ⟨i.1 - 1, by have := i.2; omega⟩ ⟨j.1 - 1, by have := j.2; omega⟩

end Ins

def intPC (v : Pl F) : TopologicalSpace.PositiveCompacts (Fv F v) :=
  ⟨⟨v.adicCompletionIntegers F, isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)⟩,
    ⟨0, mem_interior_iff_mem_nhds.2 ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))⟩⟩

def haarO (v : Pl F) : MeasureTheory.Measure (Fv F v) := MeasureTheory.Measure.addHaarMeasure (intPC v)

def haarVec (v : Pl F) (p : ℕ) : MeasureTheory.Measure (Fin p → Fv F v) := MeasureTheory.Measure.pi fun _ => haarO v

theorem haarO_isAddHaar (v : Pl F) : (haarO v).IsAddHaarMeasure := MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure _

end GlobalTheory.StdPairLoc

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairLoc
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.FlipOnto

theorem det_ne_zero_of_isSkew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero, mul_zero])

theorem det_ne_zero_of_isHerm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero])

theorem isUnit_det_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (t : E →ₐ[F] K)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) : IsUnit (J.map t).det := by
  have : (J.map t).det = t J.det := by
    rw [← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ t.toRingHom.injective).mpr hJ

theorem coX_coY_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t bb cc Z
  constructor
  · obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (bb.1 * Z * cc.1ᵀ) 0
    refine ⟨u, hu, h1, ?_⟩
    have hc : cc.1ᵀ * (cc⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    unfold GlobalTheory.FlipMatch.coX
    rw [h0, Matrix.mul_assoc, Matrix.mul_assoc, hc, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  · have hA : IsUnit (bb.1ᵀ * X.J.map t).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (Units.isUnit (Matrix.GeneralLinearGroup.det bb)).mul (isUnit_det_map t (det_ne_zero_of_isHerm hX))
    have hC : IsUnit ((W.J.map t)ᵀ * cc.1).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (isUnit_det_map t (det_ne_zero_of_isSkew hW)).mul (Units.isUnit (Matrix.GeneralLinearGroup.det cc))
    obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t 0
      (-((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹))
    refine ⟨u, hu, h0, ?_⟩
    unfold GlobalTheory.FlipMatch.coY
    rw [h1]
    calc -(bb.1ᵀ * X.J.map t * -((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹) * (W.J.map t)ᵀ * cc.1)
        = (bb.1ᵀ * X.J.map t * (bb.1ᵀ * X.J.map t)⁻¹) * Z * (((W.J.map t)ᵀ * cc.1)⁻¹ * ((W.J.map t)ᵀ * cc.1)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = Z := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.FlipOnto
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairLoc
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  first | exact @GlobalTheory.FlipOnto.coX_coY_onto | exact GlobalTheory.FlipOnto.coX_coY_onto | (intros; apply GlobalTheory.FlipOnto.coX_coY_onto <;> assumption)
end
