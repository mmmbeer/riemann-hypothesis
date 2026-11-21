import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.IsHaarMeasureDoubledGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import GroundTheory.GlobalFields.Adele.Compact

section
noncomputable section

open Matrix

namespace GlobalTheory.EisBL.NilAlg

variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def blk (X : Matrix n n B) : Matrix (n ⊕ n) (n ⊕ n) B := fromBlocks (1 + X) (-X) X (1 - X)

theorem blk_mul (X Y : Matrix n n B) : blk X * blk Y = blk (X + Y) := by
  simp only [blk, fromBlocks_multiply]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

omit [Fintype n] in
theorem blk_zero : blk (0 : Matrix n n B) = 1 := by
  simp [blk, fromBlocks_one]

def phi (c : B →+* B) (J X : Matrix n n B) : Matrix n n B := Xᵀ * J + J * X.map c

theorem blk_map (c : B →+* B) (X : Matrix n n B) : (blk X).map c = blk (X.map c) := by
  have e : ∀ M : Matrix n n B, M.map c = c.mapMatrix M := fun _ => rfl
  simp only [blk, fromBlocks_map, e, map_add, map_sub, map_neg, map_one]

theorem blk_form (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c =
      GlobalTheory.WeilM.dbl J + fromBlocks (phi c J X) (-phi c J X) (-phi c J X) (phi c J X) := by
  rw [blk_map]
  simp only [blk, phi, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_add, transpose_add,
    transpose_sub, transpose_neg, transpose_one]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

theorem blk_form_iff (c : B →+* B) (J X : Matrix n n B) :
    (blk X)ᵀ * GlobalTheory.WeilM.dbl J * (blk X).map c = GlobalTheory.WeilM.dbl J ↔ phi c J X = 0 := by
  rw [blk_form]
  constructor
  · intro h
    rw [GlobalTheory.WeilM.dbl, fromBlocks_add, fromBlocks_inj] at h
    simpa using h.1
  · intro h
    rw [h]
    simp

def tau (c : B →+* B) (J K X : Matrix n n B) : Matrix n n B := -(J * X.map c * K)ᵀ

theorem phi_eq_zero_iff (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1)
    (X : Matrix n n B) : phi c J X = 0 ↔ tau c J K X = X := by
  unfold phi tau
  constructor
  · intro h
    have h1 : J * X.map c * K = -Xᵀ := by
      calc J * X.map c * K = (Xᵀ * J + J * X.map c) * K - Xᵀ * (J * K) := by noncomm_ring
        _ = -Xᵀ := by rw [h, hJK]; noncomm_ring
    rw [h1, transpose_neg, transpose_transpose, neg_neg]
  · intro h
    have h1 : Xᵀ = -(J * X.map c * K) := by
      conv_lhs => rw [← h]
      rw [transpose_neg, transpose_transpose]
    rw [h1]
    calc -(J * X.map c * K) * J + J * X.map c = -(J * X.map c * (K * J)) + J * X.map c := by noncomm_ring
      _ = 0 := by rw [hKJ]; noncomm_ring

theorem tau_add (c : B →+* B) (J K X Y : Matrix n n B) : tau c J K (X + Y) = tau c J K X + tau c J K Y := by
  unfold tau
  rw [show (X + Y).map c = X.map c + Y.map c from map_add c.mapMatrix X Y, Matrix.mul_add, Matrix.add_mul,
    transpose_add, neg_add]

omit [DecidableEq n] in
theorem tau_smul (c : B →+* B) (J K : Matrix n n B) (h : B) (hh : c h = h) (X : Matrix n n B) :
    tau c J K (h • X) = h • tau c J K X := by
  unfold tau
  have : (h • X).map c = h • X.map c := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hh]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, transpose_smul, smul_neg]

theorem tau_tau (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (X : Matrix n n B) :
    tau c J K (tau c J K X) = X := by
  have hcc : (X.map c).map c = X := by ext i j; simp [hc]
  have h1 : (tau c J K X).map c = -(K * Xᵀ * J) := by
    unfold tau
    rw [Matrix.map_neg _ (map_neg c), transpose_map, Matrix.map_mul, Matrix.map_mul, hcc, transpose_mul, transpose_mul,
      hKc, hJc]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hε, one_smul, Matrix.mul_assoc]
  show -(J * (tau c J K X).map c * K)ᵀ = X
  rw [h1]
  rw [show J * -(K * Xᵀ * J) * K = -((J * K) * Xᵀ * (J * K)) by noncomm_ring, transpose_neg, neg_neg, hJK,
    Matrix.one_mul, Matrix.mul_one, transpose_transpose]

def proj (c : B →+* B) (J K : Matrix n n B) (h : B) (X : Matrix n n B) : Matrix n n B := h • (X + tau c J K X)

theorem unip_iff_blk (M : Matrix (n ⊕ n) (n ⊕ n) B) :
    ((M - 1) * Matrix.fromRows (1 : Matrix n n B) (1 : Matrix n n B) = 0 ∧
      Matrix.fromCols (1 : Matrix n n B) (-1 : Matrix n n B) * (M - 1) = 0) ↔
      ∃ X, M = blk X := by
  constructor
  · rintro ⟨h1, h2⟩
    have hM : M - 1 = fromBlocks (M - 1).toBlocks₁₁ (M - 1).toBlocks₁₂ (M - 1).toBlocks₂₁ (M - 1).toBlocks₂₂ :=
      (fromBlocks_toBlocks (M - 1)).symm
    set a := (M - 1).toBlocks₁₁
    set b := (M - 1).toBlocks₁₂
    set c := (M - 1).toBlocks₂₁
    set d := (M - 1).toBlocks₂₂
    rw [hM, fromBlocks_mul_fromRows] at h1
    rw [hM, fromCols_mul_fromBlocks] at h2
    have e1 := congrArg Matrix.toRows₁ h1
    have e2 := congrArg Matrix.toRows₂ h1
    have e3 := congrArg Matrix.toCols₁ h2
    have e4 := congrArg Matrix.toCols₂ h2
    have z1 : toRows₁ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z2 : toRows₂ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z3 : toCols₁ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    have z4 : toCols₂ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    simp only [toRows₁_fromRows, toRows₂_fromRows, toCols₁_fromCols, toCols₂_fromCols, Matrix.mul_one,
      Matrix.one_mul, Matrix.neg_mul, z1, z2, z3, z4] at e1 e2 e3 e4
    have hb : b = -a := eq_neg_of_add_eq_zero_right e1
    have hc : c = a := (sub_eq_zero.1 (by simpa [sub_eq_add_neg] using e3)).symm
    have hd : d = -a := by rw [← hc]; exact eq_neg_of_add_eq_zero_right e2
    refine ⟨a, ?_⟩
    have : M = 1 + (M - 1) := by abel
    rw [this, hM, hb, hc, hd, blk, ← fromBlocks_one, fromBlocks_add]
    simp [sub_eq_add_neg]
  · rintro ⟨X, rfl⟩
    have e : blk X - 1 = fromBlocks X (-X) X (-X) := by
      rw [blk, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      congr 1 <;> abel
    rw [e, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks]
    constructor <;> ext i j <;> (try rcases i with i | i) <;> (try rcases j with j | j) <;>
      simp [Matrix.fromRows, Matrix.fromCols, Sum.elim_inl, Sum.elim_inr] <;> rfl


end GlobalTheory.EisBL.NilAlg
end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.EisBL.NilAlg

namespace GlobalTheory.EisBL.DoubledUnipotentRadical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem matrixRep_mul {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (a b : G2 σ Y) : mat2 (a * b) = mat2 a * mat2 b := rfl

omit [NumberField E] in
theorem matrixRep_one {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : mat2 (1 : G2 σ Y) = 1 := rfl

omit [NumberField E] in
theorem matrix_inv_mul_doubled {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (a : G2 σ Y) : mat2 a⁻¹ * mat2 a = 1 :=
  Units.inv_mul a.1

omit [NumberField E] in
theorem diagCols_eq {n : ℕ} : diagCols (E := AE F E) (Fin n) =
    Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  unfold diagCols; rfl

omit [NumberField E] in
theorem unip_iff {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (g : G2 σ Y) :
    ((mat2 g - 1) * diagCols (E := AE F E) (Fin n) = 0 ∧
      Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (mat2 g - 1) = 0) ↔
      ∃ X, mat2 g = blk X := by
  rw [diagCols_eq]; exact unip_iff_blk (mat2 g)

variable (σ) in

def nil2 {n : ℕ} (Y : Spc F E n) : Subgroup (G2 σ Y) where
  carrier := {g | (mat2 g - 1) * diagCols (Fin n) = 0 ∧
    Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (mat2 g - 1) = 0}
  one_mem' := (unip_iff (1 : G2 σ Y)).2 ⟨0, by rw [matrixRep_one, blk_zero]⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨X, hX⟩ := (unip_iff a).1 ha
    obtain ⟨Z, hZ⟩ := (unip_iff b).1 hb
    exact (unip_iff (a * b)).2 ⟨X + Z, by rw [matrixRep_mul, hX, hZ, blk_mul]⟩
  inv_mem' := by
    intro a ha
    obtain ⟨X, hX⟩ := (unip_iff a).1 ha
    refine (unip_iff a⁻¹).2 ⟨-X, ?_⟩
    calc mat2 a⁻¹ = mat2 a⁻¹ * (blk X * blk (-X)) := by rw [blk_mul, add_neg_cancel, blk_zero, Matrix.mul_one]
      _ = (mat2 a⁻¹ * mat2 a) * blk (-X) := by rw [hX, Matrix.mul_assoc]
      _ = blk (-X) := by rw [matrix_inv_mul_doubled, Matrix.one_mul]

def eltA (σ : E →ₐ[F] E) {n : ℕ} (Y : Spc F E n) (Z : Matrix (Fin n) (Fin n) (AE F E))
    (hZ : phi (cA σ).toRingHom (incM F Y.J) Z = 0) : G2 σ Y :=
  ⟨⟨blk Z, blk (-Z), by rw [blk_mul, add_neg_cancel, blk_zero], by rw [blk_mul, neg_add_cancel, blk_zero]⟩,
    (blk_form_iff _ _ _).2 hZ⟩

omit [NumberField E] in
theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [NumberField E] in
theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.EisBL.DoubledUnipotentRadical
end
end
