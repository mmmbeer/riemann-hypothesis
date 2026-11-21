import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdelicFunctionRightTranslateDiamond
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusIdentitiesNoKernelOfClauses

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.DIV
open Formalism.GradedWeylDivisibility (blockAct)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem at_infinity_unitary (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (τ : ι) :
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ =
      gramC J emb τ := by
  have h : cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ =
      (cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (emb τ) := by
    ext a b
    simp [atInf, cT, conjTranspose_apply, hc]
  rw [e]
  simp only [gramC, atInf]
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

def frameTranslate (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]; exact (isUnit_det_atInf emb γ τ).mul (y.2 τ)⟩

theorem frame_translate_is_orthonormal (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) (hy : y.IsON) :
    (frameTranslate emb hc γ hγ y).IsON := fun τ => by
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) =
      (y.1 τ)ᴴ * ((atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ *
        atInf emb (γ : Matrix (Fin n) (Fin n) E) τ) * y.1 τ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  show (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = 1 ∨
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = -1
  rw [e, at_infinity_unitary emb hc γ hγ τ]
  exact hy τ

theorem at_infinity_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem adelic_value_translate (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (y : Frames (gramC J emb)) :
    g x' y = (S.chi κ : ℂ) * g x (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y) := by
  apply hg γ hγ x x' κ hx
  intro τ
  show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
    (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem embedding_conj_compat (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem forms_from_adelic_function (Tf : Forms0 D u) (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (hφ : φ ∈ (D.fm u).Fi i) :
    ∃ g ∈ AdForms (Tf.cls i hi h0).lev (embT D) (lamT u i),
      ∀ c, φ c = fun z => g ((Tf.cls i hi h0).y c) ((Tf.val i hi h0).eY z) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi h0).Fi φ).1 hφ
  refine ⟨g, hg, fun c => ?_⟩
  funext z
  have := congrFun (congrFun hgφ c) ((Tf.val i hi h0).eY z)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open NumberField IsDedekindDomain Formalism.UG Classical Matrix Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def localAdeleSingle (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] FiniteAdeleRing (𝓞 F) F where
  toFun x := (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x :
    FiniteAdeleRing (𝓞 F) F)
  map_add' x y := by
    apply RestrictedProduct.ext
    intro w
    change Pi.single v (x + y) w = Pi.single v x w + Pi.single v y w
    rw [Pi.single_add]; rfl
  map_smul' c x := by
    apply RestrictedProduct.ext
    intro w
    change Pi.single v (c • x) w = (algebraMap F (w.adicCompletion F) c) * Pi.single v x w
    by_cases h : w = v
    · subst h; simp [Algebra.smul_def]
    · simp [Pi.single_eq_of_ne h]

theorem local_adele_single_same_place (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : (localAdeleSingle v x) v = x := by
  show RestrictedProduct.single _ v x v = x
  simp

theorem local_adele_single_other_place (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) : (localAdeleSingle v x) w = 0 := by
  show RestrictedProduct.single _ v x w = 0
  exact RestrictedProduct.single_eq_of_ne _ _ h

theorem local_adele_single_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    localAdeleSingle v (x * y) = localAdeleSingle v x * localAdeleSingle v y := by
  apply RestrictedProduct.ext
  intro w
  change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
  by_cases h : w = v
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

def localExtensionTensor (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₗ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  TensorProduct.map LinearMap.id (localAdeleSingle v)

theorem local_extension_tensor_tmul (v : HeightOneSpectrum (𝓞 F)) (x : E) (y : v.adicCompletion F) :
    localExtensionTensor v (x ⊗ₜ y) = x ⊗ₜ localAdeleSingle v y := rfl

theorem proj_local_extension_same_place (v : HeightOneSpectrum (𝓞 F)) (t : E ⊗[F] v.adicCompletion F) :
    prV (E := E) v (localExtensionTensor v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [local_extension_tensor_tmul]
    simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    congr 1
    exact local_adele_single_same_place v y
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem proj_local_extension_other_place (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (t : E ⊗[F] v.adicCompletion F) :
    prV (E := E) w (localExtensionTensor v t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [local_extension_tensor_tmul]
    simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have : (evalV F w) (localAdeleSingle v y) = 0 := local_adele_single_other_place v w h y
    rw [this, TensorProduct.tmul_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

theorem local_extension_tensor_mul (v : HeightOneSpectrum (𝓞 F)) (t t' : E ⊗[F] v.adicCompletion F) :
    localExtensionTensor v (t * t') = localExtensionTensor v t * localExtensionTensor v t' := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction t' using TensorProduct.induction_on with
    | zero => simp
    | tmul x' y' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, local_extension_tensor_tmul, local_extension_tensor_tmul, local_extension_tensor_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        local_adele_single_mul]
    | add a b ha hb => rw [mul_add, map_add, map_add, ha, hb, mul_add]
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]

theorem local_extension_mul_incl (v : HeightOneSpectrum (𝓞 F)) (t : E ⊗[F] v.adicCompletion F) (j : E) :
    localExtensionTensor v (t * inclE (F := F) (v.adicCompletion F) j) = localExtensionTensor v t * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) j := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      local_extension_tensor_tmul]
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]

theorem local_extension_conj_comm (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (t : E ⊗[F] v.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (localExtensionTensor v t) = localExtensionTensor v (sigR σ (v.adicCompletion F) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, local_extension_tensor_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

section Mat

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

def localIdempotent : E ⊗[F] FiniteAdeleRing (𝓞 F) F := localExtensionTensor v 1

def localExtensionMatrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  M.map (localExtensionTensor v)

def localDiagMatrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  (1 - localIdempotent (E := E) v) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) + localExtensionMatrix v M

theorem local_idempotent_mul_extension (t : E ⊗[F] v.adicCompletion F) : localIdempotent (E := E) v * localExtensionTensor v t = localExtensionTensor v t := by
  rw [localIdempotent, ← local_extension_tensor_mul, one_mul]

theorem complement_idempotent_mul_extension (t : E ⊗[F] v.adicCompletion F) : (1 - localIdempotent (E := E) v) * localExtensionTensor v t = 0 := by
  rw [sub_mul, one_mul, local_idempotent_mul_extension, sub_self]

theorem complement_local_idempotent_idem : (1 - localIdempotent (E := E) v) * (1 - localIdempotent (E := E) v) = 1 - localIdempotent (E := E) v := by
  have h : localIdempotent (E := E) v * localIdempotent (E := E) v = localIdempotent (E := E) v := local_idempotent_mul_extension v 1
  rw [sub_mul, one_mul, mul_sub, mul_one, h, sub_self, sub_zero]

theorem local_extension_matrix_mul (M N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : localExtensionMatrix v M * localExtensionMatrix v N = localExtensionMatrix v (M * N) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.mul_apply, Matrix.map_apply, map_sum, local_extension_tensor_mul]

theorem local_extension_matrix_mul_gram (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (J : Matrix (Fin n) (Fin n) E) :
    localExtensionMatrix v M * J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = localExtensionMatrix v (M * J.map (inclE (F := F) (v.adicCompletion F))) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.mul_apply, Matrix.map_apply, map_sum, local_extension_mul_incl]

theorem gram_mul_local_extension_matrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (J : Matrix (Fin n) (Fin n) E) :
    J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * localExtensionMatrix v M = localExtensionMatrix v (J.map (inclE (F := F) (v.adicCompletion F)) * M) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← local_extension_mul_incl, mul_comm]

theorem complement_smul_local_extension_matrix (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : (1 - localIdempotent (E := E) v) • localExtensionMatrix v M = 0 := by
  ext i j
  simp only [localExtensionMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, complement_idempotent_mul_extension, Matrix.zero_apply]

theorem local_extension_matrix_one : localExtensionMatrix (E := E) v (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = localIdempotent (E := E) v • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [localExtensionMatrix, localIdempotent]
  · simp [localExtensionMatrix, Matrix.one_apply_ne h]

theorem local_extension_matrix_map_gram (J : Matrix (Fin n) (Fin n) E) :
    localExtensionMatrix v (J.map (inclE (F := F) (v.adicCompletion F))) = localIdempotent (E := E) v • J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := by
  ext i j
  simp only [localExtensionMatrix, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, localIdempotent]
  rw [← local_extension_mul_incl, one_mul]

theorem local_diag_matrix_mul (M N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) : localDiagMatrix v M * localDiagMatrix v N = localDiagMatrix v (M * N) := by
  simp only [localDiagMatrix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    local_extension_matrix_mul, complement_smul_local_extension_matrix, complement_local_idempotent_idem, add_zero, zero_add]

theorem local_diag_matrix_one : localDiagMatrix (E := E) v (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) = 1 := by
  rw [localDiagMatrix, local_extension_matrix_one, ← add_smul, sub_add_cancel, one_smul]

def localExtensionGL (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  ⟨localDiagMatrix v M, localDiagMatrix v ↑M⁻¹, by rw [local_diag_matrix_mul, Units.mul_inv, local_diag_matrix_one], by rw [local_diag_matrix_mul, Units.inv_mul, local_diag_matrix_one]⟩

theorem proj_local_idempotent_same_place : prV (E := E) v (localIdempotent (E := E) v) = 1 := proj_local_extension_same_place v 1

theorem proj_local_idempotent_other_place (w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) : prV (E := E) w (localIdempotent (E := E) v) = 0 := proj_local_extension_other_place v w h 1

theorem local_extension_GL_same_place (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : bc (prV (E := E) v) (localExtensionGL v M) = M := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_same_place, proj_local_extension_same_place]
  · simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_same_place, proj_local_extension_same_place, Matrix.one_apply_ne h]

theorem local_extension_GL_other_place (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) w) (localExtensionGL v M) = 1 := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_other_place v w hw, proj_local_extension_other_place v w hw]
  · simp [bc, localExtensionGL, localDiagMatrix, localExtensionMatrix, proj_local_idempotent_other_place v w hw, proj_local_extension_other_place v w hw, Matrix.one_apply_ne h]

end Mat

section Unit

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

theorem conj_local_idempotent : sigR σ (FiniteAdeleRing (𝓞 F) F) (localIdempotent (E := E) v) = localIdempotent (E := E) v := by
  rw [localIdempotent, local_extension_conj_comm, map_one]

theorem local_diag_matrix_conj_transpose (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (localDiagMatrix v M) = localDiagMatrix v (cT (sigR σ (v.adicCompletion F)) M) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, localDiagMatrix, localExtensionMatrix, Matrix.transpose_apply, Matrix.map_apply, local_extension_conj_comm, conj_local_idempotent]
  · simp [cT, localDiagMatrix, localExtensionMatrix, Matrix.transpose_apply, Matrix.map_apply, local_extension_conj_comm, conj_local_idempotent, Matrix.one_apply_ne h,
      Matrix.one_apply_ne (Ne.symm h)]

theorem local_extension_GL_mem_unitary (J : Matrix (Fin n) (Fin n) E) (M : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hM : M ∈ UPts σ J (v.adicCompletion F)) : localExtensionGL v M ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  have h : cT (sigR σ (v.adicCompletion F)) (M : Matrix (Fin n) (Fin n) _) * J.map (inclE (F := F) (v.adicCompletion F)) *
      (M : Matrix (Fin n) (Fin n) _) = J.map (inclE (F := F) (v.adicCompletion F)) := hM
  show cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (localDiagMatrix v (M : Matrix (Fin n) (Fin n) _)) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * localDiagMatrix v (M : Matrix (Fin n) (Fin n) _) =
    J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
  rw [local_diag_matrix_conj_transpose]
  simp only [localDiagMatrix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, local_extension_matrix_mul_gram, gram_mul_local_extension_matrix,
    local_extension_matrix_mul, smul_smul, complement_local_idempotent_idem, complement_smul_local_extension_matrix, add_zero, zero_add]
  rw [h, local_extension_matrix_map_gram, ← add_smul, sub_add_cancel, one_smul]

end Unit

section Assemble

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

def IsLocalDiamond (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) : Prop :=
  ∃ M : GL (Fin n) (E ⊗[F] v.adicCompletion F), M ∈ levelVL σ J v S.Lb ∧
    ∃ hg : M ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
      ∀ x, k • S.fT v hv ⟨(M : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ = S.fT v hv x

theorem is_diamond_of_local_diamond (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (h : IsLocalDiamond S v hv k) : ∃ δ, Formalism.L2.Forms.IsDia S v hv k δ := by
  obtain ⟨M, hM, hg, hf⟩ := h
  have hU : M ∈ UPts σ J (v.adicCompletion F) := (Subgroup.mem_inf.1 hM).1
  refine ⟨⟨localExtensionGL v M, local_extension_GL_mem_unitary v σ J M hU⟩, fun v' hv' => local_extension_GL_other_place v v' hv' M, ?_, ?_⟩
  · dsimp only
    rw [local_extension_GL_same_place]; exact hM
  · dsimp only
    have e := local_extension_GL_same_place v M
    refine ⟨by rw [e]; exact hg, fun x => ?_⟩
    rw [← hf x]
    congr 2
    exact Subtype.ext (congrArg (fun N : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
      (N : Matrix (Fin n) (Fin n) _) *ᵥ x.1) e)

end Assemble

end Ext

section Tied

open Formalism.BasicNotions Formalism.L2.Forms

variable {D : D7} {u : D.what₂.Word}

def LocalDiamondElementsExist (Tf : Forms0 D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
    IsLocalDiamond (Tf.cls i hi h0).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k

theorem diamond_elements_of_local (Tf : Forms0 D u) (h : LocalDiamondElementsExist Tf) : DiamondElementsExist Tf := by
  intro i hi h0 v a
  obtain ⟨k, hk, hl⟩ := h i hi h0 v a
  exact ⟨k, hk, is_diamond_of_local_diamond _ _ _ k hl⟩

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open NumberField IsDedekindDomain Formalism.UG Classical Matrix Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Prime

theorem subgroup_prime_card_eq_top {G : Type} [AddCommGroup G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
    (H : AddSubgroup G) {y : G} (hy : y ∈ H) (hy0 : y ≠ 0) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.ne_zero)
  have hd : Nat.card H ∣ p := hG ▸ AddSubgroup.card_addSubgroup_dvd_card H
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exact absurd (AddSubgroup.mem_bot.1 ((AddSubgroup.eq_bot_of_card_eq H h) ▸ hy)) hy0
  · exact AddSubgroup.eq_top_of_card_eq H (h.trans hG.symm)

theorem idempotent_action_prime_card {O : Type} [Ring O] {G : Type} [AddCommGroup G] [Module O G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : O} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  by_cases h : ∀ y : G, e • y = 0
  · exact Or.inl h
  · obtain ⟨y0, hy0⟩ := not_forall.1 h
    right
    have htop := subgroup_prime_card_eq_top hp hG (DistribSMul.toAddMonoidHom G e).range ⟨y0, rfl⟩ hy0
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [htop]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

theorem unit_lift_int_prime_field {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime) (hK : Fintype.card K = p) (a : Kˣ) :
    ∃ k : ℤ, (k : K) = a ∧ ¬ (p : ℤ) ∣ k := by
  have hG : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hK]
  have htop := subgroup_prime_card_eq_top hp hG (AddSubgroup.zmultiples (1 : K)) (AddSubgroup.mem_zmultiples 1) one_ne_zero
  have ha : (a : K) ∈ AddSubgroup.zmultiples (1 : K) := by rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ha
  rw [zsmul_one] at hk
  refine ⟨k, hk, fun ⟨m, hm⟩ => a.ne_zero ?_⟩
  have hp0 : (p : K) = 0 := by
    have := card_nsmul_eq_zero' (G := K) (x := 1)
    rwa [hG, nsmul_eq_mul, mul_one] at this
  rw [← hk, hm, Int.cast_mul, Int.cast_natCast, hp0, zero_mul]

end Prime

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem int_not_mem_prime_over (v : HeightOneSpectrum (𝓞 F)) {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} (hk : ¬ (T : ℤ) ∣ k) : (k : 𝓞 F) ∉ v.asIdeal := by
  intro hkv
  have h1 : ¬ T ∣ k.natAbs := fun h => hk (Int.natCast_dvd.2 h)
  have h2 : Nat.Coprime T k.natAbs := (Nat.Prime.coprime_iff_not_dvd hT).2 h1
  have hcop : IsCoprime k (T : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact h2.symm
  obtain ⟨a, b, hab⟩ := hcop
  have hmem : ((a * k + b * (T : ℤ) : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hkv) (Ideal.mul_mem_left _ _ hv)
  rw [hab, Int.cast_one] at hmem
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)

theorem valuation_int_not_mem_eq_one (v : HeightOneSpectrum (𝓞 F)) {k : ℤ} (hk : (k : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (k : v.adicCompletion F) = 1 := by
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (k : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hk] at h
  simpa using h

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem scalar_mem_lattice_stabiliser {A : Type} [CommRing A] {S : Subring A} (Λ : Submodule S (Fin n → A))
    (g : GL (Fin n) A) (μ μ' : A) (hμ : μ ∈ S) (hμ' : μ' ∈ S) (h1 : μ' * μ = 1)
    (hg : ∀ x, (g : Matrix (Fin n) (Fin n) A) *ᵥ x = μ • x) : g ∈ stabGL Λ := by
  intro x
  rw [hg]
  constructor
  · intro hx
    exact Λ.smul_mem (⟨μ, hμ⟩ : S) hx
  · intro hx
    have h := Λ.smul_mem (⟨μ', hμ'⟩ : S) hx
    change μ' • μ • x ∈ Λ at h
    rwa [smul_smul, h1, one_smul] at h

theorem local_diamond_of_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (c c' e : E ⊗[F] v.adicCompletion F)
    (hc : c ∈ intV E v) (hc' : c' ∈ intV E v) (he : e ∈ intV E v) (hee : e * e = e)
    (hσ : sigR σ (v.adicCompletion F) e = 1 - e) (hσc : sigR σ (v.adicCompletion F) c = c)
    (hσc' : sigR σ (v.adicCompletion F) c' = c') (hcc : c * c' = 1)
    (hkc : (k : E ⊗[F] v.adicCompletion F) * c = 1)
    (hact : ∀ y : S.fM v hv, (⟨e, he⟩ : intV E v) • y = y) : IsLocalDiamond S v hv k := by
  set μ : E ⊗[F] v.adicCompletion F := c * e + c' * (1 - e) with hμdef
  set μ' : E ⊗[F] v.adicCompletion F := c * (1 - e) + c' * e with hμ'def
  have hμμ' : μ * μ' = 1 := by
    rw [hμdef, hμ'def]
    linear_combination (-c ^ 2 + 2 * c * c' - c' ^ 2) * hee + hcc
  have hμ'μ : μ' * μ = 1 := by rw [mul_comm]; exact hμμ'
  have hσμ : sigR σ (v.adicCompletion F) μ = μ' := by
    rw [hμdef, hμ'def, map_add, map_mul, map_mul, map_sub, map_one, hσ, hσc, hσc']
    ring
  have hμO : μ ∈ intV E v :=
    add_mem (mul_mem hc he) (mul_mem hc' (sub_mem (one_mem _) he))
  have hμ'O : μ' ∈ intV E v :=
    add_mem (mul_mem hc (sub_mem (one_mem _) he)) (mul_mem hc' he)
  let M : GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    ⟨μ • (1 : Matrix (Fin n) (Fin n) _), μ' • (1 : Matrix (Fin n) (Fin n) _),
      by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμμ', one_smul],
      by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμ'μ, one_smul]⟩
  have hmv : ∀ x : Fin n → E ⊗[F] v.adicCompletion F, (M : Matrix (Fin n) (Fin n) _) *ᵥ x = μ • x := by
    intro x
    show (μ • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x = μ • x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcT : cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) =
      μ' • (1 : Matrix (Fin n) (Fin n) _) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT, hσμ]
    · simp [cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have hU : M ∈ UPts σ J (v.adicCompletion F) := by
    show cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) _)) *
        J.map (inclE (F := F) (v.adicCompletion F)) * (μ • (1 : Matrix (Fin n) (Fin n) _)) =
      J.map (inclE (F := F) (v.adicCompletion F))
    rw [hcT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hμ'μ,
      one_smul]
  have hL : M ∈ levelVL σ J v S.Lb := by
    show M ∈ UJ _ _ ⊓ stabGL _
    exact Subgroup.mem_inf.2 ⟨hU, scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv⟩
  have hg : M ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :=
    scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv
  refine ⟨M, hL, hg, fun x => ?_⟩
  have hx : (⟨(M : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) = (⟨μ, hμO⟩ : intV E v) • x := by
    apply Subtype.ext
    exact (hmv x.1).trans rfl
  rw [hx, map_smul]
  set y := S.fT v hv x
  have hsplit : (⟨μ, hμO⟩ : intV E v) = ⟨c, hc⟩ * ⟨e, he⟩ + ⟨c', hc'⟩ * (1 - ⟨e, he⟩) := Subtype.ext rfl
  have h1e : (1 - (⟨e, he⟩ : intV E v)) • y = 0 := by rw [sub_smul, one_smul, hact y, sub_self]
  have hkO : ((k : intV E v)) * ⟨c, hc⟩ = 1 := by
    apply Subtype.ext
    simpa using hkc
  rw [hsplit, add_smul, mul_smul, mul_smul, h1e, smul_zero, add_zero, hact y, ← Int.cast_smul_eq_zsmul (intV E v),
    smul_smul, hkO, one_smul]

theorem local_diamond_of_split_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hT : T.Prime) (k : ℤ) (hk : ¬ (T : ℤ) ∣ k) (e : E ⊗[F] v.adicCompletion F)
    (he : e ∈ intV E v) (hee : e * e = e) (hσ : sigR σ (v.adicCompletion F) e = 1 - e) : IsLocalDiamond S v hv k := by
  have hval := valuation_int_not_mem_eq_one v (int_not_mem_prime_over v hT hv hk)
  have hk0 : (k : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
  have hkI : (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have hkI' : (k : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hR : ∀ y ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] y) ∈ intV E v := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have hσR : ∀ y : v.adicCompletion F, sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
    intro y; simp [sigR]
  have hcc : ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hk0, Algebra.TensorProduct.one_def]
  have hkA : ((k : E ⊗[F] v.adicCompletion F)) = (1 : E) ⊗ₜ[F] (k : v.adicCompletion F) := by
    rw [← Algebra.TensorProduct.includeRight_apply]
    exact (map_intCast _ k).symm
  have hkc : ((k : E ⊗[F] v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) = 1 := by
    rw [hkA, mul_comm, hcc]
  rcases idempotent_action_prime_card hT (S.fM_card v hv) (e := (⟨e, he⟩ : intV E v)) (Subtype.ext hee) with h0 | h1
  · have he' : 1 - e ∈ intV E v := sub_mem (one_mem _) he
    refine local_diamond_of_idempotent S v hv k _ _ (1 - e) (hR _ hkI') (hR _ hkI) he' (by linear_combination hee)
      (by rw [map_sub, map_one, hσ]) (hσR _) (hσR _) hcc hkc (fun y => ?_)
    have : (⟨1 - e, he'⟩ : intV E v) = 1 - ⟨e, he⟩ := Subtype.ext rfl
    rw [this, sub_smul, one_smul, h0 y, sub_zero]
  · exact local_diamond_of_idempotent S v hv k _ _ e (hR _ hkI') (hR _ hkI) he hee hσ (hσR _) (hσR _) hcc hkc h1

end Local

section Tied

variable {D : D7} {u : D.what₂.Word}

def SplitAtT (A : AtTTied u) : Prop :=
  ∀ v : (D.mem u).A.vT, ∃ e ∈ intV D.host.E (A.eV v).1, e * e = e ∧
    sigR (sigD D) ((A.eV v).1.adicCompletion D.host.F) e = 1 - e

theorem local_diamonds_of_split (Tf : Forms0 D u) (hs : SplitAtT Tf.atT) : LocalDiamondElementsExist Tf := by
  intro i hi h0 v a
  obtain ⟨k, hk, hkT⟩ := unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := hs v
  exact ⟨k, hk, local_diamond_of_split_idempotent (Tf.cls i hi h0).lev _ _ (D.mem u).A.T_prime k hkT e he hee hσ⟩

theorem diamond_elements_of_split (Tf : Forms0 D u) (hs : SplitAtT Tf.atT) : DiamondElementsExist Tf :=
  diamond_elements_of_local Tf (local_diamonds_of_split Tf hs)

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
end
