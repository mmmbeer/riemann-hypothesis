import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeOfSig

section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_eq (e : E) : inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := rfl

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  have : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    apply Algebra.TensorProduct.ext'
    intro a e
    simp [cA, hσ]
  exact congrArg (fun f : AE F E →ₐ[AF F] AE F E => f z) this

def cAe {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) : AE F E ≃ₐ[AF F] AE F E :=
  AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext (cA_cA hσ)) (AlgHom.ext (cA_cA hσ))

theorem trace_cA {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (z : AE F E) :
    Algebra.trace (AF F) (AE F E) (cA σ z) = Algebra.trace (AF F) (AE F E) z :=
  Algebra.trace_eq_of_algEquiv (cAe hσ) z

theorem incM_mul {a b c : Type} [Fintype b] (x : Matrix a b E) (y : Matrix b c E) :
    incM F (x * y) = incM F x * incM F y := Matrix.map_mul

theorem incM_transpose {a b : Type} (x : Matrix a b E) : incM F xᵀ = (incM F x)ᵀ := (Matrix.transpose_map).symm

theorem map_cA_incM {σ : E →ₐ[F] E} {a b : Type} (x : Matrix a b E) : (incM F x).map (cA σ) = incM F (x.map σ) := by
  ext i j; rfl

variable {m n : ℕ}

theorem sum_crdB (bs : Module.Basis (Fin 2) F E) (Z : Mx F E m n) : ∑ k, crdB bs Z k • Ek bs k = Z := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ek, Matrix.single_apply, smul_ite, smul_zero, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp only [and_self, if_true, crdB]
    conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) bs).sum_repr (Z i j)]
    simp [Algebra.TensorProduct.basis_apply]
  · intro j' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp

def BfR (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m n) : Mx F E m n →ₗ[AF F] AF F where
  toFun Z := Bf σ J X Z
  map_add' Z Z' := by
    simp only [Bf, Matrix.map_add _ (map_add (cA σ)), Matrix.mul_add, Matrix.trace_add, map_add]
  map_smul' c Z := by
    have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by ext i j; simp [map_smul]
    simp only [Bf, this, Matrix.mul_smul, Matrix.trace_smul, map_smul, RingHom.id_apply]

def BfL (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (Z : Mx F E m n) : Mx F E m n →ₗ[AF F] AF F where
  toFun X := Bf σ J X Z
  map_add' X X' := by
    simp only [Bf, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add, map_add]
  map_smul' c X := by
    simp only [Bf, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, RingHom.id_apply]

theorem Bf_eq_sum_right (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (X Z : Mx F E m n) :
    Bf σ J X Z = ∑ k, crdB bs Z k * Bf σ J X (Ek bs k) := by
  conv_lhs => rw [← sum_crdB bs Z]
  change BfR σ J X _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem Bf_eq_sum_left (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (X Z : Mx F E m n) :
    Bf σ J X Z = ∑ k, crdB bs X k * Bf σ J (Ek bs k) Z := by
  conv_lhs => rw [← sum_crdB bs X]
  change BfL σ J Z _ = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

theorem hTens_eq {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (c : AE F E →ₐ[AF F] AE F E)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (x y : Matrix α β (AE F E)) :
    hTens c JA JB x y = (x * (JB * (y.map c)ᵀ * JAᵀ)).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem map_cA_mul {σ : E →ₐ[F] E} {a b c : Type} [Fintype b] (x : Matrix a b (AE F E)) (y : Matrix b c (AE F E)) :
    (x * y).map (cA σ) = x.map (cA σ) * y.map (cA σ) := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem incM_jeps (ε : ℤˣ) : incM F (jeps (E := E) n ε) =
    Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  ext (i | i) (j | j) <;> simp [jeps, incM, Matrix.one_apply] <;> split_ifs <;> simp

theorem incM_dbl (YJ : Matrix (Fin n) (Fin n) E) : dbl (incM F YJ) = incM F (dbl YJ) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem incM_b (b : GL (Fin n ⊕ Fin n) E) :
    (incM F b.1)ᵀ = Matrix.fromRows (incM F b.1.toCols₁)ᵀ (incM F b.1.toCols₂)ᵀ := by
  ext (i | i) j <;> rfl

theorem tr_swap (JA : Matrix (Fin m) (Fin m) (AE F E)) (Z W : Mx F E m n) :
    (Z * Wᵀ * JAᵀ).trace = (Zᵀ * JA * W).trace := by
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

theorem symp_frame (σ : E →ₐ[F] E) (JA : Matrix (Fin m) (Fin m) E) (YJ : Matrix (Fin n) (Fin n) E)
    (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε) (Z X Z' X' : Mx F E m n) :
    symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F YJ)) (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ)
      (Z' * (incM F b.1.toCols₁)ᵀ + X' * (incM F b.1.toCols₂)ᵀ) = -(Bf σ JA Z X' + ((ε : ℤ) : AF F) * Bf σ JA X Z') := by
  have hw : ∀ Z X : Mx F E m n, Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ =
      Matrix.fromCols Z X * (incM F b.1)ᵀ := fun Z X => by
    rw [incM_b, Matrix.fromCols_mul_fromRows]
  rw [hw, hw, symp, hTens_eq, map_cA_mul]
  have hN : (incM F b.1)ᵀ * dbl (incM F YJ) * ((incM F b.1)ᵀ.map (cA σ))ᵀ = incM F (jeps n ε) := by
    rw [← hb, incM_dbl, Matrix.transpose_map, map_cA_incM, Matrix.transpose_transpose, incM_mul, incM_mul, incM_transpose]
  rw [Matrix.transpose_mul]
  simp only [← Matrix.mul_assoc]
  have hN' : Matrix.fromCols Z X * (incM F b.1)ᵀ * dbl (incM F YJ) * ((incM F b.1)ᵀ.map (cA σ))ᵀ =
      (Matrix.fromCols Z X * (incM F (jeps (E := E) n ε) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
        Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [← hN]; simp only [Matrix.mul_assoc]
  have hc : (Matrix.fromCols Z' X').map (cA σ) = Matrix.fromCols (Z'.map (cA σ)) (X'.map (cA σ)) := by
    ext i (j | j) <;> rfl
  rw [hN', hc, Matrix.transpose_fromCols, incM_jeps, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_add, Matrix.trace_smul, tr_swap]
  have key : ∀ t : AE F E, Algebra.trace (AF F) (AE F E) (((ε : ℤ) : AE F E) * t) =
      ((ε : ℤ) : AF F) * Algebra.trace (AF F) (AE F E) t := fun t => by
    rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have key2 : ∀ t : AE F E, Algebra.trace (AF F) (AE F E) (((ε : ℤ) : AE F E) • t) =
      ((ε : ℤ) : AF F) * Algebra.trace (AF F) (AE F E) t := fun t => by rw [smul_eq_mul, key]
  have key3 : ∀ t : AE F E, Algebra.trace (AF F) (AE F E) (t * ((ε : ℤ) : AE F E)) =
      ((ε : ℤ) : AF F) * Algebra.trace (AF F) (AE F E) t := fun t => by rw [mul_comm, key]
  simp only [Bf, neg_one_mul, map_neg, map_add, key, key2, key3]
  ring

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
