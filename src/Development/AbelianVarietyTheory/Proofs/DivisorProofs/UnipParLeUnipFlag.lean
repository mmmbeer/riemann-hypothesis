import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero

noncomputable section

namespace GlobalTheory.ThK.FlagPar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

variable (σ) in

def stabCols {d r m : ℕ} (J : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin r) (AE F E))
    (I : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ J) where
  carrier := {u | ∃ (A : GL (Fin r) (AE F E)) (D : GL (Fin m) (AE F E)), mat u * X = X * A.1 ∧
    ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a}
  one_mem' := ⟨1, 1, by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨A, D, h1, h2⟩ ⟨A', D', h1', h2'⟩
    refine ⟨A * A', D * D', ?_, fun z => ?_⟩
    · rw [mat_mul, Matrix.mul_assoc, h1', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, Units.val_mul]
    · obtain ⟨a', ha'⟩ := h2' z
      obtain ⟨a, ha⟩ := h2 (D'.1 *ᵥ z)
      refine ⟨a + A.1 *ᵥ a', ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
        Matrix.mulVec_add, Units.val_mul, ← Matrix.mulVec_mulVec z D.1, ← Matrix.mulVec_mulVec a' X, add_assoc]
  inv_mem' := by
    rintro u ⟨A, D, h1, h2⟩
    have e : mat u⁻¹ * X = X * (A⁻¹).1 := by
      have : X = mat u * (X * (A⁻¹).1) := by
        rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      conv_lhs => rw [this, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    refine ⟨A⁻¹, D⁻¹, e, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 ((D⁻¹).1 *ᵥ z)
    refine ⟨-((A⁻¹).1 *ᵥ a), ?_⟩
    have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [Matrix.mulVec_add] at h3
    rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_mulVec z D.1,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_mulVec a (mat u⁻¹) X, e,
      ← Matrix.mulVec_mulVec] at h3
    rw [h3, Matrix.mulVec_neg, add_neg_cancel_right]

variable (σ) in

def unipCols {d r m : ℕ} (J : Matrix (Fin d) (Fin d) E) (X : Matrix (Fin d) (Fin r) (AE F E))
    (I : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ J) where
  carrier := {u | mat u * X = X ∧ ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ z + X *ᵥ a}
  one_mem' := ⟨by simp [mat_one], fun z => ⟨0, by simp [mat_one]⟩⟩
  mul_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, fun z => ?_⟩
    · rw [mat_mul, Matrix.mul_assoc, h1', h1]
    · obtain ⟨a', ha'⟩ := h2' z
      obtain ⟨a, ha⟩ := h2 z
      refine ⟨a + a', ?_⟩
      rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
        Matrix.mulVec_add, add_assoc]
  inv_mem' := by
    rintro u ⟨h1, h2⟩
    have e : mat u⁻¹ * X = X := by
      conv_lhs => rw [← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
    refine ⟨e, fun z => ?_⟩
    obtain ⟨a, ha⟩ := h2 z
    refine ⟨-a, ?_⟩
    have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [Matrix.mulVec_add] at h3
    rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_mulVec a (mat u⁻¹) X, e] at h3
    rw [Matrix.mulVec_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h3.symm

section Cols

variable {d r m : ℕ} {J : Matrix (Fin d) (Fin d) E} {X : Matrix (Fin d) (Fin r) (AE F E)}
  {I : Matrix (Fin d) (Fin m) (AE F E)}

theorem act_inv {u : UA σ J} {A : GL (Fin r) (AE F E)} {D : GL (Fin m) (AE F E)} (h1 : mat u * X = X * A.1)
    (h2 : ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a) :
    mat u⁻¹ * X = X * (A⁻¹).1 ∧ ∀ z, ∃ a, mat u⁻¹ *ᵥ (I *ᵥ z) = I *ᵥ ((D⁻¹).1 *ᵥ z) + X *ᵥ a := by
  have e : mat u⁻¹ * X = X * (A⁻¹).1 := by
    have : X = mat u * (X * (A⁻¹).1) := by
      rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    conv_lhs => rw [this, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨e, fun z => ?_⟩
  obtain ⟨a, ha⟩ := h2 ((D⁻¹).1 *ᵥ z)
  refine ⟨-((A⁻¹).1 *ᵥ a), ?_⟩
  have h3 := congrArg (mat u⁻¹ *ᵥ ·) ha
  simp only [Matrix.mulVec_add] at h3
  rw [Matrix.mulVec_mulVec _ (mat u⁻¹) (mat u), mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_mulVec z D.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_mulVec a (mat u⁻¹) X, e,
    ← Matrix.mulVec_mulVec] at h3
  rw [h3, Matrix.mulVec_neg, add_neg_cancel_right]

theorem act_mul {u v : UA σ J} {A A' : GL (Fin r) (AE F E)} {D D' : GL (Fin m) (AE F E)}
    (h : mat u * X = X * A.1 ∧ ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ (D.1 *ᵥ z) + X *ᵥ a)
    (h' : mat v * X = X * A'.1 ∧ ∀ z, ∃ a, mat v *ᵥ (I *ᵥ z) = I *ᵥ (D'.1 *ᵥ z) + X *ᵥ a) :
    mat (u * v) * X = X * (A * A').1 ∧ ∀ z, ∃ a, mat (u * v) *ᵥ (I *ᵥ z) = I *ᵥ ((D * D').1 *ᵥ z) + X *ᵥ a := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul, Matrix.mul_assoc, h1', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, Units.val_mul]
  · obtain ⟨a', ha'⟩ := h2' z
    obtain ⟨a, ha⟩ := h2 (D'.1 *ᵥ z)
    refine ⟨a + A.1 *ᵥ a', ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, ha', Matrix.mulVec_add, ha, Matrix.mulVec_mulVec a' (mat u) X, h1,
      Matrix.mulVec_add, Units.val_mul, ← Matrix.mulVec_mulVec z D.1, ← Matrix.mulVec_mulVec a' X, add_assoc]

theorem mem_unipCols_iff {u : UA σ J} : u ∈ unipCols σ J X I ↔
    mat u * X = X * (1 : GL (Fin r) (AE F E)).1 ∧
      ∀ z, ∃ a, mat u *ᵥ (I *ᵥ z) = I *ᵥ ((1 : GL (Fin m) (AE F E)).1 *ᵥ z) + X *ᵥ a := by
  simp only [Units.val_one, Matrix.mul_one, Matrix.one_mulVec]; rfl

theorem conj_mem_unipCols {p n : UA σ J} (hp : p ∈ stabCols σ J X I) (hn : n ∈ unipCols σ J X I) :
    p * n * p⁻¹ ∈ unipCols σ J X I := by
  obtain ⟨A, D, h⟩ := hp
  have := act_mul (act_mul h (mem_unipCols_iff.1 hn)) (act_inv h.1 h.2)
  rw [mul_one, mul_one, mul_inv_cancel, mul_inv_cancel] at this
  exact mem_unipCols_iff.2 this

end Cols

variable (σ) in

def unipPar {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (i : ℕ) : Subgroup (UA σ W.J) :=
  unipCols σ W.J (incM F (flagX H' pl (i + 1))) (incM F (chainEmb H' pl i))

section Flag

variable {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} {i : ℕ}




theorem act_of_isLeviFlag {Y : Spc F E (d₁ - 2 * i)} {h₁ : UA σ Y.J} {m : UA σ W.J} (hm : IsLeviFlag H' pl i h₁ m) :
    mat m * incM F (flagX H' pl (i + 1)) = incM F (flagX H' pl (i + 1)) * (1 : GL (Fin (i + 1)) (AE F E)).1 ∧ ∀ z, ∃ a,
      mat m *ᵥ (incM F (chainEmb H' pl i) *ᵥ z) =
        incM F (chainEmb H' pl i) *ᵥ (h₁.1.1 *ᵥ z) + incM F (flagX H' pl (i + 1)) *ᵥ a :=
  ⟨by rw [Units.val_one, Matrix.mul_one]; exact hm.1, fun z => ⟨0, by
    rw [Matrix.mulVec_mulVec, hm.2.2, Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec]; rfl⟩⟩


end Flag

def LiftZero (ψ : AddChar (AF F) ℂ) {n m : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E)
    (χX χY : Chr F E) (f : UA σ JY → ℂ) : Prop :=
  ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m),
    (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ),
      IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om →
      ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (g : UA σ JX) (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ JY) 𝓕 μ → ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ = 0

end GlobalTheory.ThK.FlagPar

end
