import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatDarboux

theorem exists_rat_matrix {F R V W ι : Type} [Field F] [CommRing R] [Nontrivial R] [Algebra F R] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    (j : V →+ W) (hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x) (hinj : Function.Injective j)
    (hc : Module.finrank F V = Fintype.card ι) (e₀ e₂ : W ≃ₗ[R] (ι → R))
    (h₀ : ∀ x, ∃ u : ι → F, e₀ (j x) = fun i => algebraMap F R (u i))
    (h₂ : ∀ x, ∃ u : ι → F, e₂ (j x) = fun i => algebraMap F R (u i)) :
    ∃ g : Matrix ι ι F, ∀ w, e₂ w = g.map (algebraMap F R) *ᵥ e₀ w := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective
  have hvec : ∀ a b : ι → F, (fun i => algebraMap F R (a i)) = (fun i => algebraMap F R (b i)) → a = b := by
    intro a b h
    funext i
    exact hφ (congrFun h i)

  have lin : ∀ (e : W ≃ₗ[R] (ι → R)) (u : V → ι → F), (∀ x, e (j x) = fun i => algebraMap F R (u x i)) →
      ∃ U : V →ₗ[F] (ι → F), ∀ x, U x = u x := by
    intro e u hu
    refine ⟨{ toFun := u, map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
    · intro x y
      apply hvec
      rw [← hu, map_add, map_add, hu, hu]
      funext i
      simp
    · intro c x
      apply hvec
      rw [← hu, hj, map_smul, hu]
      funext i
      simp
  choose u₀ hu₀ using h₀
  choose u₂ hu₂ using h₂
  obtain ⟨U₀, hU₀⟩ := lin e₀ u₀ hu₀
  obtain ⟨U₂, hU₂⟩ := lin e₂ u₂ hu₂

  have inj : Function.Injective U₀ := by
    intro x y hxy
    apply hinj
    apply e₀.injective
    rw [hu₀, hu₀, ← hU₀, ← hU₀, hxy]
  have surj : Function.Surjective U₀ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [hc, Module.finrank_fintype_fun_eq_card]
  let E₀ : V ≃ₗ[F] (ι → F) := LinearEquiv.ofBijective U₀ ⟨inj, surj⟩
  refine ⟨LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap), ?_⟩
  set g := LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap) with hg

  have onForm : ∀ x, e₂ (j x) = g.map (algebraMap F R) *ᵥ e₀ (j x) := by
    intro x
    have h1 : g *ᵥ U₀ x = U₂ x := by
      rw [hg, LinearMap.toMatrix'_mulVec]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      congr 1
      exact E₀.symm_apply_apply x
    funext i
    rw [hu₂, hu₀, ← hU₂, ← h1, ← hU₀]
    exact RingHom.map_mulVec (algebraMap F R) g (U₀ x) i

  have onBasis : ∀ i, e₂ (e₀.symm (Pi.single i 1)) = g.map (algebraMap F R) *ᵥ Pi.single i 1 := by
    intro i
    obtain ⟨x, hx⟩ := surj (Pi.single i 1)
    have hs : e₀ (j x) = Pi.single i 1 := by
      rw [hu₀, ← hU₀, hx]
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [← hs, LinearEquiv.symm_apply_apply, onForm]
  have hL : (e₂.toLinearMap ∘ₗ e₀.symm.toLinearMap) = Matrix.mulVecLin (g.map (algebraMap F R)) := by
    apply (Pi.basisFun R ι).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Matrix.mulVecLin_apply]
    exact onBasis i
  intro w
  have := LinearMap.congr_fun hL (e₀ w)
  simpa using this

theorem std_form {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (a b : κ ⊕ κ → R) :
    a ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) *ᵥ b) =
      (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (b ∘ Sum.inl) ⬝ᵥ (a ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]
  conv_lhs => rw [← Sum.elim_comp_inl_inr a]
  rw [sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
    dotProduct_comm (a ∘ Sum.inr)]
  simp only [neg_dotProduct, sub_eq_add_neg]

theorem exists_rat_symplectic_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Nontrivial R] [Algebra F R] {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    {Bf : Matrix α β (R ⊗[F] E) → Matrix α β (R ⊗[F] E) → R} (d₀ d₂ : Darboux Bf κ)
    (inc : Matrix α β E → Matrix α β (R ⊗[F] E)) (hinc : ∀ x a b, inc x a b = (1 : R) ⊗ₜ[F] x a b)
    (hc : Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E)
    (h₀ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₀.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i)))
    (h₂ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₂.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) :
    ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective

  let j : Matrix α β E →+ Matrix α β (R ⊗[F] E) :=
    { toFun := inc
      map_zero' := by
        ext a b
        simp [hinc]
      map_add' := by
        intro x y
        ext a b
        simp [hinc, TensorProduct.tmul_add] }
  have hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x := by
    intro c x
    ext a b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc, Matrix.smul_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [Algebra.smul_def]
  have hinj : Function.Injective j := by
    intro x y hxy
    ext a b
    have h := congrFun (congrFun hxy a) b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc] at h
    apply Algebra.TensorProduct.includeRight_injective (A := R) (B := E) hφ
    simpa [Algebra.TensorProduct.includeRight_apply] using h

  let σ := (LinearEquiv.sumArrowLequivProdArrow κ κ R R).symm
  have hσ : ∀ p : (κ → R) × (κ → R), σ p = Sum.elim p.1 p.2 := fun p => rfl
  have hcard : Module.finrank F (Matrix α β E) = Fintype.card (κ ⊕ κ) := by
    rw [Module.finrank_matrix, Fintype.card_sum, ← hc]
    ring
  have rat : ∀ (d : Darboux Bf κ), (∀ x : Matrix α β E, ∃ u v : κ → F,
      d.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) →
      ∀ x, ∃ u : κ ⊕ κ → F, (d.e.trans σ) (j x) = fun i => algebraMap F R (u i) := by
    intro d hd x
    obtain ⟨u, v, huv⟩ := hd x
    refine ⟨Sum.elim u v, ?_⟩
    simp only [LinearEquiv.trans_apply, j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hσ, huv]
    funext i
    cases i <;> rfl
  obtain ⟨g, hg⟩ := GlobalTheory.RatDarboux.exists_rat_matrix j hj hinj hcard (d₀.e.trans σ) (d₂.e.trans σ)
    (rat d₀ h₀) (rat d₂ h₂)
  simp only [LinearEquiv.trans_apply, hσ] at hg
  set G := g.map (algebraMap F R) with hG
  set JR : Matrix (κ ⊕ κ) (κ ⊕ κ) R := Matrix.fromBlocks 0 1 (-1) 0 with hJR

  have form : ∀ (d : Darboux Bf κ) w w',
      Bf w w' = Sum.elim (d.e w).1 (d.e w).2 ⬝ᵥ (JR *ᵥ Sum.elim (d.e w').1 (d.e w').2) := by
    intro d w w'
    rw [hJR, GlobalTheory.RatDarboux.std_form, d.form]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  have pres : ∀ y y' : κ ⊕ κ → R, y ⬝ᵥ (JR *ᵥ y') = y ⬝ᵥ ((Gᵀ * JR * G) *ᵥ y') := by
    intro y y'
    obtain ⟨w, hw⟩ := (d₀.e.trans σ).surjective y
    obtain ⟨w', hw'⟩ := (d₀.e.trans σ).surjective y'
    simp only [LinearEquiv.trans_apply, hσ] at hw hw'
    have h := (form d₀ w w').symm.trans (form d₂ w w')
    rw [hg, hg, hw, hw'] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose G y, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
  refine ⟨g, ?_, ?_⟩
  ·
    have hJmap : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = JR := by
      ext i k
      rcases i with i | i <;> rcases k with k | k <;>
        simp [hJR, Matrix.one_apply, apply_ite (algebraMap F R)]
    have key : (gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g).map (algebraMap F R) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJmap, ← hG]
      ext i k
      have h := pres (Pi.single i 1) (Pi.single k 1)
      simp only [single_dotProduct, one_mul, Matrix.mulVec_single_one] at h
      exact h.symm
    exact Matrix.map_injective hφ key
  · intro w
    unfold GlobalTheory.AdelicSvN.act
    rw [← hG, ← hg w]
    exact Prod.ext (Sum.elim_comp_inl (d₂.e w).1 (d₂.e w).2).symm (Sum.elim_comp_inr (d₂.e w).1 (d₂.e w).2).symm

theorem exists_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β κ : Type) [Fintype α] [Fintype β]
  [Fintype κ] [DecidableEq κ] (Bf : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F) (d₀ d₂ : Darboux Bf κ),
  Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₀.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₂.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
    ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  intro F E _ _ _ _ _ α β κ _ _ _ _ Bf d₀ d₂ hc h₀ h₂

  have : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  exact exists_rat_symplectic_gen (R := AF F) d₀ d₂ (incM F)
    (fun x a b => rfl) hc h₀ h₂

end GlobalTheory.RatDarboux
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SympGen

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev J (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] : Matrix (κ ⊕ κ) (κ ⊕ κ) F :=
  Matrix.fromBlocks 0 1 (-1) 0

def Sp (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := gᵀ * J F κ * g = J F κ

theorem J_mul_J : J F κ * J F κ = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [J, Matrix.fromBlocks_multiply]

def sInv (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := -(J F κ * gᵀ * J F κ)

theorem sInv_mul {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) : sInv g * g = 1 := by
  have h : J F κ * gᵀ * J F κ * g = J F κ * (gᵀ * J F κ * g) := by simp only [Matrix.mul_assoc]
  rw [sInv, Matrix.neg_mul, h, hg, J_mul_J, neg_neg]

theorem mul_sInv {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) : g * sInv g = 1 :=
  mul_eq_one_comm.mp (sInv_mul hg)

theorem Sp.mul {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) (hh : Sp h) : Sp (g * h) := by
  unfold Sp at *
  rw [Matrix.transpose_mul]
  calc hᵀ * gᵀ * J F κ * (g * h) = hᵀ * (gᵀ * J F κ * g) * h := by simp only [Matrix.mul_assoc]
    _ = J F κ := by rw [hg]; exact hh

theorem Sp.of_mul_eq_one {g s : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) (h1 : g * s = 1) : Sp s := by
  unfold Sp at *
  calc sᵀ * J F κ * s = sᵀ * (gᵀ * J F κ * g) * s := by rw [hg]
    _ = (g * s)ᵀ * J F κ * (g * s) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = J F κ := by rw [h1]; simp

theorem Sp.sInv {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) : Sp (sInv g) :=
  Sp.of_mul_eq_one hg (mul_sInv hg)

theorem sp_of_mem_gens {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ GlobalTheory.AdelicSvN.gens F κ) : Sp g := by
  rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hw
  · have h1 : Aᵀ * A⁻¹ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hA, Matrix.transpose_one]
    have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
    simp [Sp, J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h1, h2]
  · simp [Sp, J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hC]
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    simp [Sp, J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

theorem sp_of_mem_closure {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ)) : Sp g := by
  induction hg using Submonoid.closure_induction with
  | mem x hx => exact sp_of_mem_gens hx
  | one => simp [Sp]
  | mul x y _ _ hx hy => exact hx.mul hy

private theorem full_of_depthZeroLabels_of_one_le_d {a b c d : Matrix κ κ F} (h : Sp (Matrix.fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d - cᵀ * b = 1 ∧ bᵀ * d = dᵀ * b := by
  have e : (Matrix.fromBlocks a b c d)ᵀ * J F κ * Matrix.fromBlocks a b c d =
      Matrix.fromBlocks (aᵀ * c - cᵀ * a) (aᵀ * d - cᵀ * b) (bᵀ * c - dᵀ * a) (bᵀ * d - dᵀ * b) := by
    simp [J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, sub_eq_add_neg, add_comm]
  unfold Sp at h
  rw [e] at h
  obtain ⟨h1, h2, -, h4⟩ := Matrix.fromBlocks_inj.mp h
  exact ⟨sub_eq_zero.mp h1, h2, sub_eq_zero.mp h4⟩

end GlobalTheory.SympGen

namespace GlobalTheory.SympGen

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem mem_closure_of_lower {k : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hk : Sp k) (h12 : k.toBlocks₁₂ = 0) :
    k ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  obtain ⟨A, B, c, D, rfl⟩ : ∃ A B c D, k = Matrix.fromBlocks A B c D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks k).symm⟩
  simp only [Matrix.toBlocks_fromBlocks₁₂] at h12
  subst h12
  obtain ⟨hc, hAD, -⟩ := full_of_depthZeroLabels_of_one_le_d hk
  simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_zero] at hAD
  have hdet : IsUnit A.det := by
    have := congrArg Matrix.det hAD
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hD : D = A⁻¹ᵀ := by
    rw [Matrix.transpose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv hAD).symm
  subst hD
  have hAA : A⁻¹ᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv A hdet, Matrix.transpose_one]
  have hsym : (-(Aᵀ * c))ᵀ = -(Aᵀ * c) := by
    rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_transpose, hc]
  have e : Matrix.fromBlocks A 0 c A⁻¹ᵀ =
      Matrix.fromBlocks A 0 0 A⁻¹ᵀ * Matrix.fromBlocks 1 0 (-(-(Aᵀ * c))) 1 := by
    simp [Matrix.fromBlocks_multiply, ← Matrix.mul_assoc, hAA]
  rw [e]
  refine Submonoid.mul_mem _ (Submonoid.subset_closure ?_) (Submonoid.subset_closure ?_)
  · exact Or.inl (Or.inl ⟨A, hdet, rfl⟩)
  · exact Or.inl (Or.inr ⟨-(Aᵀ * c), hsym, rfl⟩)

def vert : (κ → F) →ₗ[F] (κ ⊕ κ → F) where
  toFun y := Sum.elim 0 y
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

private theorem exists_symm_isUnit_det_sub_mul_of_finrank_ker (b : Matrix κ κ F) :
    ∀ (n : ℕ) (d : Matrix κ κ F), Module.finrank F (LinearMap.ker d.mulVecLin) = n →
      bᵀ * d = dᵀ * b → (∀ x, b *ᵥ x = 0 → d *ᵥ x = 0 → x = 0) →
        ∃ C : Matrix κ κ F, Cᵀ = C ∧ IsUnit (d - C * b).det := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hn hbd hinj
  by_cases hd : LinearMap.ker d.mulVecLin = ⊥
  · refine ⟨0, by simp, ?_⟩
    rw [Matrix.zero_mul, sub_zero, ← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hd)
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd
  have hdx : d *ᵥ x = 0 := by simpa using hxk
  have hbx : b *ᵥ x ≠ 0 := fun h0 => hx0 (hinj x h0 hdx)
  obtain ⟨i, hi⟩ : ∃ i, (b *ᵥ x) i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hbx (funext hc)
  have key : ∀ y, (b *ᵥ x) ⬝ᵥ (d *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hbd,
      ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hdx, Matrix.zero_vecMul, zero_dotProduct]
  set E : Matrix κ κ F := Matrix.diagonal (Pi.single i 1) with hEdef
  have hE : ∀ w : κ → F, E *ᵥ w = Pi.single i (w i) := by
    intro w
    funext j
    rw [hEdef, Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  have hET : Eᵀ = E := by rw [hEdef, Matrix.diagonal_transpose]
  set d' := d - E * b with hd'
  have hd'v : ∀ y, d' *ᵥ y = d *ᵥ y - Pi.single i ((b *ᵥ y) i) := by
    intro y
    rw [hd', Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hE]
  have hbd' : bᵀ * d' = d'ᵀ * b := by
    rw [hd', Matrix.transpose_sub, Matrix.transpose_mul, hET, Matrix.mul_sub, Matrix.sub_mul, hbd,
      Matrix.mul_assoc]
  have hsub : ∀ y, d' *ᵥ y = 0 → d *ᵥ y = 0 := by
    intro y hy
    rw [hd'v, sub_eq_zero] at hy
    have h1 := key y
    rw [hy, dotProduct_single] at h1
    have h2 : (b *ᵥ y) i = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hi
      · exact h
    rw [hy, h2, Pi.single_zero]
  have hinj' : ∀ y, b *ᵥ y = 0 → d' *ᵥ y = 0 → y = 0 :=
    fun y hb hy => hinj y hb (hsub y hy)
  have hlt : LinearMap.ker d'.mulVecLin < LinearMap.ker d.mulVecLin := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun y hy => ?_, x, hxk, fun hx' => ?_⟩
    · simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
      exact hsub y hy
    · simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx'
      rw [hd'v, hdx, zero_sub, neg_eq_zero] at hx'
      have := congrFun hx' i
      simp only [Pi.single_eq_same, Pi.zero_apply] at this
      exact hi this
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hn] at hlt'
  obtain ⟨C, hC, hu⟩ := ih _ hlt' d' rfl hbd' hinj'
  refine ⟨C + E, by rw [Matrix.transpose_add, hC, hET], ?_⟩
  have : d - (C + E) * b = d' - C * b := by
    rw [hd', Matrix.add_mul]; abel
  rw [this]
  exact hu

private theorem fromBlocks_one_symm_mem_closure_gens (T : Matrix κ κ F) (hT : Tᵀ = T) :
    Matrix.fromBlocks 1 T 0 1 ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  have hw : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) ∈
      Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) :=
    Submonoid.subset_closure (Or.inr rfl)
  have hu : (Matrix.fromBlocks 1 0 (-T) 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) ∈
      Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) :=
    Submonoid.subset_closure (Or.inl (Or.inr ⟨T, hT, rfl⟩))
  have e : (Matrix.fromBlocks 1 T 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) =
      Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 (-T) 1 *
        (Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 (-1) 0) := by
    simp [Matrix.fromBlocks_multiply]
  rw [e]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hw hu)
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ hw hw) hw)

theorem main (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (hg : Sp g) : g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, g = Matrix.fromBlocks a b c d :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  obtain ⟨-, -, hbd⟩ := full_of_depthZeroLabels_of_one_le_d hg
  have hinj : ∀ x, b *ᵥ x = 0 → d *ᵥ x = 0 → x = 0 := by
    intro x hb hd
    have h1 : Matrix.fromBlocks a b c d *ᵥ (Sum.elim 0 x) = 0 := by
      rw [Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [hb, hd]
    have h2 : Sum.elim (0 : κ → F) x = 0 := by
      have := congrArg (fun v => sInv (Matrix.fromBlocks a b c d) *ᵥ v) h1
      simpa [Matrix.mulVec_mulVec, sInv_mul hg] using this
    funext i
    exact congrFun h2 (Sum.inr i)
  obtain ⟨C, hC, hdu⟩ := exists_symm_isUnit_det_sub_mul_of_finrank_ker b _ d rfl hbd hinj
  set d' := d - C * b with hd'
  have hu : Sp (Matrix.fromBlocks 1 0 (-C) 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
    sp_of_mem_gens (Or.inl (Or.inr ⟨C, hC, rfl⟩))
  have e1 : Matrix.fromBlocks 1 0 (-C) 1 * Matrix.fromBlocks a b c d =
      Matrix.fromBlocks a b (c - C * a) d' := by
    simp [Matrix.fromBlocks_multiply, hd', sub_eq_add_neg, add_comm]
  have hg1 : Sp (Matrix.fromBlocks a b (c - C * a) d') := by
    rw [← e1]; exact hu.mul hg
  obtain ⟨-, -, hbd1⟩ := full_of_depthZeroLabels_of_one_le_d hg1
  have hdu' : IsUnit d'ᵀ.det := by rwa [Matrix.det_transpose]
  set S := b * d'⁻¹ with hSdef
  have hS : Sᵀ = S := by
    calc Sᵀ = d'ᵀ⁻¹ * bᵀ := by rw [hSdef, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      _ = d'ᵀ⁻¹ * (bᵀ * d') * d'⁻¹ := by
        rw [Matrix.mul_assoc _ (bᵀ * d'), Matrix.mul_assoc bᵀ, Matrix.mul_nonsing_inv _ hdu,
          Matrix.mul_one]
      _ = d'ᵀ⁻¹ * d'ᵀ * b * d'⁻¹ := by rw [hbd1]; simp only [Matrix.mul_assoc]
      _ = S := by rw [Matrix.nonsing_inv_mul _ hdu', Matrix.one_mul]
  have hSd : S * d' = b := by
    rw [hSdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdu, Matrix.mul_one]
  set k := Matrix.fromBlocks 1 (-S) 0 1 * Matrix.fromBlocks a b (c - C * a) d' with hk
  have hkSp : Sp k := by
    have hn : Sp (Matrix.fromBlocks 1 (-S) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
      sp_of_mem_closure (fromBlocks_one_symm_mem_closure_gens (-S) (by rw [Matrix.transpose_neg, hS]))
    exact hn.mul hg1
  have hk12 : k.toBlocks₁₂ = 0 := by
    simp [hk, Matrix.fromBlocks_multiply, Matrix.neg_mul, hSd]
  have hkm := mem_closure_of_lower hkSp hk12
  have e2 : Matrix.fromBlocks a b c d =
      Matrix.fromBlocks 1 0 (-(-C)) 1 * (Matrix.fromBlocks 1 S 0 1 * k) := by
    rw [hk, ← Matrix.mul_assoc (Matrix.fromBlocks 1 S 0 1), ← e1]
    simp [Matrix.fromBlocks_multiply]
  rw [e2]
  refine Submonoid.mul_mem _ (Submonoid.subset_closure ?_) (Submonoid.mul_mem _ (fromBlocks_one_symm_mem_closure_gens S hS) hkm)
  exact Or.inl (Or.inr ⟨-C, by rw [Matrix.transpose_neg, hC], rfl⟩)

end GlobalTheory.SympGen

theorem GlobalTheory.sympGen : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F),
    gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 →
      g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  intro F _ κ _ _ g hg
  exact GlobalTheory.SympGen.main g hg
end

section
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU
open GlobalTheory.AdelicSvN GlobalTheory.AdelicSvNLevi

namespace GlobalTheory.TowU.LeviModel

variable {F : Type} [Field F] [NumberField F]

theorem isOp_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix ι ι (AF F) := A.map (algebraMap F (AF F))
  let Aim : Matrix ι ι (AF F) := A⁻¹.map (algebraMap F (AF F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine
    { pres := comp_mem A⁻¹ A h2 h1
      pres' := comp_mem A A⁻¹ h1 h2
      left := fun φ _ => funext fun x => ?_
      right := fun φ _ => funext fun x => ?_
      adm := fun l hl g hg => ?_
      adm' := fun l hl g hg => ?_
      Heisenberg₂ := fun w φ _ => funext fun x => ?_
      theta := ⟨1, one_ne_zero, fun φ _ => ?_⟩
      norm := fun μ μ' hμ hμ' => ?_ }
  · change φ (Aim *ᵥ (Am *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A A⁻¹ h1 h2).continuous,
      hg.2.comp_homeomorph (finHomeo A A⁻¹ h1 h2)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A A⁻¹ h1 h2)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A A⁻¹ h1 h2, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  · rw [one_mul]
    unfold thetaSum
    let e : (ι → F) ≃ (ι → F) :=
      { toFun := fun ξ => A⁻¹ *ᵥ ξ
        invFun := fun ξ => A *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] }
    have he := Equiv.tsum_eq e (fun ξ : ι → F => φ fun i => algebraMap F (AF F) (ξ i))
    refine Eq.trans (tsum_congr fun ξ => ?_) he
    change φ (Aim *ᵥ _) = φ (fun i => algebraMap F (AF F) ((A⁻¹ *ᵥ ξ) i))
    congr 1
    funext i
    exact (RingHom.map_mulVec (algebraMap F (AF F)) A⁻¹ ξ i).symm
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    letI : MeasurableSpace (ι → AF F) := borel _
    haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
    let L : (ι → AF F) ≃+ (ι → AF F) :=
      { toFun := fun x => Aim *ᵥ x
        invFun := fun x => Am *ᵥ x
        left_inv := fun x => by simp only [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
        right_inv := fun x => by simp only [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
        map_add' := fun x y => Matrix.mulVec_add _ _ _ }
    have hc : Continuous L := continuous_const.matrix_mulVec continuous_id
    have hc' : Continuous L.symm := continuous_const.matrix_mulVec continuous_id
    let H : (ι → AF F) ≃ₜ (ι → AF F) := { toEquiv := L.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
    haveI : (Measure.map L μ').IsAddHaarMeasure := L.isAddHaarMeasure_map μ' hc hc'
    have e := Measure.isAddLeftInvariant_eq_smul (Measure.map L μ') μ
    refine ⟨Measure.addHaarScalarFactor (Measure.map L μ') μ, ?_, ENNReal.coe_ne_top, fun φ _ => ?_⟩
    · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.map L μ') μ).ne'
    · have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) H.toMeasurableEquiv (μ := μ')
      change ∫⁻ x, ‖φ (Aim *ᵥ x)‖ₑ ^ 2 ∂μ' = _
      have hL : (Measure.map H.toMeasurableEquiv μ') = Measure.map L μ' := rfl
      rw [hL, e, lintegral_smul_measure] at hm
      exact hm.symm.trans rfl

theorem inv_diag {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    (Matrix.fromBlocks A 0 0 A)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hA]
  simp [Matrix.fromBlocks_one]

theorem dblAct_levi {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : IsUnit A.det) :
    dblAct (AdelicSvN.act (R := AF F) (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) =
      AdelicSvN.act (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 A) 0 0 (Matrix.fromBlocks A 0 0 A)⁻¹ᵀ) := by
  funext w
  rw [inv_diag A hA, act_levi, Matrix.fromBlocks_transpose]
  simp only [dblAct, act_levi, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.transpose_zero, Matrix.mulVec_neg, neg_neg]

theorem isOp2_levi (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : IsUnit A.det) :
    IsOp2 ψ (AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) (compM A⁻¹) (compM A) := by
  have hA2 : IsUnit (Matrix.fromBlocks A 0 0 A).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hA
  refine ⟨isOp_levi ψ A hA, compM (Matrix.fromBlocks A 0 0 A)⁻¹, compM (Matrix.fromBlocks A 0 0 A), ?_,
    fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_levi A hA]; exact isOp_levi ψ _ hA2
  · funext x
    rw [inv_diag A hA]
    change boxFun φ₁ φ₂ _ = φ₁ _ * star (star (φ₂ _))
    rw [star_star]
    simp only [boxFun, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add]
    rfl

end GlobalTheory.TowU.LeviModel

open GlobalTheory.TowU.LeviModel in

theorem GlobalTheory.TowU.realised_levi2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ A : Matrix κ κ F, IsUnit A.det →
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) S S' :=
  fun _ _ _ ψ _ _ _ _ A hA => ⟨_, _, isOp2_levi ψ A hA⟩

end
end

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darbouxOperators_levi_and_double : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ A : Matrix κ κ F, IsUnit A.det → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) S S' := by
  atlas_forward_decl GlobalTheory.TowU.realised_levi2
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem star_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [show star (ψ t) = starRingEnd ℂ (ψ t) from rfl, Complex.conj_mul', GlobalTheory.StdCharFromIsStd.norm_psi hψ t]
  simp

theorem invOf_two_eq : (⅟(2 : AF F)) = algebraMap F (AF F) (2⁻¹) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
    mul_inv_cancel₀ (two_ne_zero), map_one]

theorem quad_rat {κ : Type} [Fintype κ] (B : Matrix κ κ F) (ξ : κ → F) :
    quad (⅟(2 : AF F)) (B.map (algebraMap F (AF F))) (fun i => algebraMap F (AF F) (ξ i)) =
      algebraMap F (AF F) (quad (2⁻¹ : F) B ξ) := by
  rw [map_quad, invOf_two_eq]

theorem isOp_unip (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ F) (hC : Cᵀ = C) :
    IsOp ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1))
      (mulQ (F := F) ψ (⅟2) (C.map (algebraMap F (AF F)))) (mulQ (F := F) ψ (⅟2) (-(C.map (algebraMap F (AF F))))) := by
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  have hA : Aᵀ = A := by rw [hAdef, ← Matrix.transpose_map, hC]
  have inv : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) (-B) (mulQ ψ (⅟2) B φ) = φ := fun B φ => by
    funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have inv' : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) B (mulQ ψ (⅟2) (-B) φ) = φ := fun B φ => by
    have := inv (-B) φ
    rwa [neg_neg] at this
  have adm : ∀ B : Matrix κ κ (AF F), ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ mulQ ψ (⅟2) B ∈ (adeleClass F).adm κ := by
    intro B l hl g hg
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) B hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => by rw [LinearMap.comp_apply, hM f, hT]; rfl⟩
  have nrm : ∀ (B : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) x, ‖mulQ ψ (⅟2) B φ x‖ₑ = ‖φ x‖ₑ := by
    intro B φ x
    rw [mulQ_apply, enorm_mul, ← ofReal_norm (ψ _), GlobalTheory.StdCharFromIsStd.norm_psi hψ, ENNReal.ofReal_one, one_mul]
  refine ⟨mulQ_mem ψ hψ _ A, mulQ_mem ψ hψ _ (-A), fun φ _ => inv A φ, fun φ _ => inv' A φ, adm A, adm (-A),
    fun w φ _ => funext fun x => ?_, ⟨1, one_ne_zero, fun φ _ => ?_⟩, ?_⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]
  · rw [one_mul]
    unfold thetaSum
    congr 1
    funext ξ
    rw [mulQ_apply, hAdef, quad_rat, hψ.2.1, one_mul]
  · intro μ μ' hμ hμ'
    letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : SecondCountableTopology (κ → AF F) := inferInstance
    haveI := hμ
    haveI := hμ'
    have e := Measure.isAddLeftInvariant_eq_smul μ' μ
    have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ
    refine ⟨(μ'.addHaarScalarFactor μ : ℝ≥0∞), by exact_mod_cast hpos.ne', ENNReal.coe_ne_top, fun φ _ => ?_⟩
    simp_rw [nrm]
    conv_lhs => rw [e]
    rw [lintegral_smul_measure]
    rfl

end GlobalTheory.TowU.UnipOp

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dblAct_unip {κ : Type} [Fintype κ] [DecidableEq κ] (C : Matrix κ κ F) :
    dblAct (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) :
        (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) =
      GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-(Matrix.fromBlocks C 0 0 (-C))) 1) := by
  funext w
  rw [act_unip]
  simp only [dblAct, act_unip]
  refine Prod.ext ?_ ?_
  · funext a
    rcases a with a | a <;> rfl
  · funext a
    rcases a with a | a <;>
      simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec] <;> ring

theorem quad_dbl {κ : Type} [Fintype κ] (h : AF F) (A : Matrix κ κ (AF F)) (x : κ ⊕ κ → AF F) :
    quad h (Matrix.fromBlocks A 0 0 (-A)) x = quad h A (x ∘ Sum.inl) + -quad h A (x ∘ Sum.inr) := by
  simp only [quad, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Matrix.neg_mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  intro F _ _ ψ hψ κ _ _ C hC
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  let Cd : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks C 0 0 (-C)
  have hCd : Cdᵀ = Cd := by
    simp only [Cd, Matrix.fromBlocks_transpose, hC, Matrix.transpose_zero, Matrix.transpose_neg]
  have hn : (-C).map (algebraMap F (AF F)) = -C.map (algebraMap F (AF F)) := Matrix.map_neg _ (map_neg _) _
  have hCdA : Cd.map (algebraMap F (AF F)) = Matrix.fromBlocks A 0 0 (-A) := by
    simp only [Cd, Matrix.fromBlocks_map, hAdef, Matrix.map_zero _ (map_zero _), hn]
  refine ⟨_, _, isOp_unip ψ hψ C hC, mulQ ψ (⅟2) (Cd.map (algebraMap F (AF F))),
    mulQ ψ (⅟2) (-(Cd.map (algebraMap F (AF F)))), ?_, fun φ₁ _ φ₂ _ => funext fun x => ?_⟩
  · rw [dblAct_unip]
    exact isOp_unip ψ hψ Cd hCd
  · rw [mulQ_apply, hCdA, quad_dbl]
    simp only [boxFun, Pi.star_apply, mulQ_apply, star_mul', star_star, star_psi hψ]
    rw [AddChar.map_add_eq_mul, ← hAdef]
    ring

end GlobalTheory.TowU.UnipOp
end
end

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  atlas_forward_decl GlobalTheory.TowU.UnipOp.main
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexConjugate
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.WeylModel

variable {F : Type} [Field F] [NumberField F]

theorem act_weyl {κ : Type} [Fintype κ] [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = (w.2, -w.1) := by
  simp [AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]

end GlobalTheory.TowU.WeylModel

open GlobalTheory.TowU.WeylModel in

theorem GlobalTheory.TowU.realised_weyl2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  intro F _ _ ψ hψ κ _ _
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩
  let μ : Measure (κ → AF F) := Measure.addHaar
  let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => by simp
      right_inv := fun x => by simp
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous E := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous
  have hc' : Continuous E.symm := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous
  let H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F) :=
    { toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let ν : Measure (κ ⊕ κ → AF F) := Measure.map E (μ.prod μ)
  haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'
  let ε₁ : κ → ℤˣ := fun _ => 1
  let ε₂ : κ ⊕ κ → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ inferInstance ε₁
  obtain ⟨Sd, Sd', hSd, hSdf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ (κ ⊕ κ) ν inferInstance ε₂
  refine ⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · convert hS using 1
    funext w
    rw [act_weyl]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]
  · convert hSd using 1
    funext w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [dblAct, act_weyl, ε₂]
  · funext y
    have hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ) := rfl
    have e₂ : star (S (star φ₂)) (y ∘ Sum.inr) =
        ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ := by
      rw [Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]
    change _ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)
    rw [e₂, hSf φ₁ h₁, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _
    have es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i =
        ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i +
          -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i) := by
      simp [Fintype.sum_sum_type, ε₁, ε₂]
    rw [es, AddChar.map_add_eq_mul]
    ring

end
end

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylElement_realised_by_fourierTransforms : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  atlas_forward_decl GlobalTheory.TowU.realised_weyl2
end

section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F]

theorem isOp_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp ψ s S S') (ht : IsOp ψ t T T') : IsOp ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') where
  pres φ h := ht.pres _ (hs.pres φ h)
  pres' φ h := hs.pres' _ (ht.pres' φ h)
  left φ h := by simp only [LinearMap.comp_apply]; rw [ht.left _ (hs.pres φ h), hs.left φ h]
  right φ h := by simp only [LinearMap.comp_apply]; rw [hs.right _ (ht.pres' φ h), ht.right φ h]
  adm l hl := by rw [← LinearMap.comp_assoc]; exact hs.adm _ (ht.adm l hl)
  adm' l hl := by rw [← LinearMap.comp_assoc]; exact ht.adm' _ (hs.adm' l hl)
  Heisenberg₂ w φ h := by
    simp only [LinearMap.comp_apply, Function.comp_apply]
    rw [hs.Heisenberg₂ w φ h, ht.Heisenberg₂ _ _ (hs.pres φ h)]
  theta := by
    obtain ⟨c₁, hc₁, e₁⟩ := hs.theta
    obtain ⟨c₂, hc₂, e₂⟩ := ht.theta
    exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun φ h => by
      simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩
  norm μ μ'' hμ hμ'' := by
    letI : MeasurableSpace (κ' → AF F) := borel _
    haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
    haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
    obtain ⟨c₁, h1, h1', e₁⟩ := hs.norm μ Measure.addHaar hμ inferInstance
    obtain ⟨c₂, h2, h2', e₂⟩ := ht.norm Measure.addHaar μ'' inferInstance hμ''
    exact ⟨c₂ * c₁, mul_ne_zero h2 h1, ENNReal.mul_ne_top h2' h1', fun φ h => by
      simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩

theorem dblAct_comp {κ κ' κ'' : Type} (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) :
    dblAct (t ∘ s) = dblAct t ∘ dblAct s := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem isOp2_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp2 ψ s S S') (ht : IsOp2 ψ t T T') : IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  obtain ⟨hs1, Sd, Sd', hsd, hsb⟩ := hs
  obtain ⟨ht1, Td, Td', htd, htb⟩ := ht
  have hc : ∀ {ι : Type} [Fintype ι], ∀ φ ∈ schA F ι, star φ ∈ schA F ι := fun φ h => GlobalTheory.ConjSch.conj_mem_schA φ h
  refine ⟨isOp_comp hs1 ht1, Td ∘ₗ Sd, Sd' ∘ₗ Td', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [dblAct_comp]; exact isOp_comp hsd htd
  · simp only [LinearMap.comp_apply]
    rw [hsb φ₁ h₁ φ₂ h₂, htb _ (hs1.pres _ h₁) _ (hc _ (hs1.pres _ (hc _ h₂))), star_star]

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

def addRe {X : Type} [TopologicalSpace X] [AddCommGroup X] (e : κ' ≃ κ) : (κ' → X) ≃ₜ+ (κ → X) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

def reix {R : Type} (e : κ' ≃ κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : κ' → R => x ∘ e.symm)

theorem reix_apply {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e.symm) := rfl

theorem reix_symm_reix {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) : reix e.symm (reix e φ) = φ := by
  funext x; simp only [reix_apply, Equiv.symm_symm]; congr 1; funext i; simp

def linRe (e : κ' ≃ κ) : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e.symm).toContinuousLinearEquiv

theorem sb_reix (e : κ' ≃ κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y : κ' → FiniteAdeleRing (𝓞 F) F => g (y ∘ e.symm)) ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) :=
  ⟨hg.1.comp_continuous (addRe e).continuous, hg.2.comp_homeomorph (addRe e).toHomeomorph⟩

theorem reix_pureA (e : κ' ≃ κ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    reix e (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e) f)
      (fun y => g (y ∘ e.symm)) := by
  funext x
  rfl

theorem reix_mem_schA (e : κ' ≃ κ) {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have hle : schA F κ ≤ (schA F κ').comap (reix e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, _, sb_reix e hg, reix_pureA e f g⟩
  exact hle h

theorem reix_adm (e : κ' ≃ κ) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ reix e ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl _ (sb_reix e hg)
  exact ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e)), fun f => by
    rw [LinearMap.comp_apply, reix_pureA]; exact hT _⟩

theorem reix_theta (e : κ' ≃ κ) (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AF F) (ξ i)))

theorem reix_heis (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    reix e (schr ψ w φ) = schr ψ (w.1 ∘ e, w.2 ∘ e) (reix e φ) := by
  have hd : ∀ u v : κ → AF F, (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := fun u v => by
    simp only [dotProduct, Function.comp_apply]; exact Equiv.sum_comp e (fun i => u i * v i)
  funext x
  simp only [reix_apply, schr]
  have h1 : (x ∘ e.symm) ⬝ᵥ w.2 = x ⬝ᵥ (w.2 ∘ e) := by
    rw [← hd]; congr 1; funext i; simp
  have h2 : x ∘ e.symm + w.1 = (x + w.1 ∘ e) ∘ e.symm := by funext i; simp
  rw [h1, h2, hd]

theorem reix_norm (e : κ' ≃ κ) (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (hμ' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : (κ → AF F) → ℂ,
      ∫⁻ x, ‖reix e φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  letI : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  haveI := hμ'
  let L : (κ' → AF F) ≃ₜ+ (κ → AF F) := addRe e
  haveI : (μ'.map L).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ' L
  have heq := Measure.isAddLeftInvariant_eq_smul (μ'.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ'.map L) μ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top,
    fun φ => ?_⟩
  have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv (μ := μ')
  have hL : (⇑L.toHomeomorph.toMeasurableEquiv : (κ' → AF F) → (κ → AF F)) = ⇑L := rfl
  rw [hL, heq, lintegral_smul_measure] at hm
  rw [ENNReal.smul_def, smul_eq_mul] at hm
  exact hm.symm

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem isOp_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) where
  pres _ h := reix_mem_schA e h
  pres' _ h := reix_mem_schA e.symm h
  left φ _ := reix_symm_reix e φ
  right φ _ := by simpa using reix_symm_reix e.symm φ
  adm _ hl := reix_adm e hl
  adm' _ hl := reix_adm e.symm hl
  Heisenberg₂ w φ _ := reix_heis ψ e w φ
  theta := ⟨1, one_ne_zero, fun φ _ => by rw [reix_theta, one_mul]⟩
  norm μ μ' hμ hμ' := by
    obtain ⟨c, h0, h1, h⟩ := reix_norm e μ μ' hμ hμ'
    exact ⟨c, h0, h1, fun φ _ => h φ⟩

theorem dblAct_reix (e : κ' ≃ κ) :
    dblAct (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) =
      fun w => (w.1 ∘ Equiv.sumCongr e e, w.2 ∘ Equiv.sumCongr e e) := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

theorem isOp2_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp2 ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  refine ⟨isOp_reix ψ e, reix (Equiv.sumCongr e e), reix (Equiv.sumCongr e e).symm, ?_, fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_reix]; exact isOp_reix ψ _
  · funext x
    simp only [reix_apply, boxFun, Pi.star_apply, star_star]
    congr 2 <;> funext i <;> simp

theorem realised_comp_reix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' :=
  fun _ _ _ ψ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hs ht => isOp2_comp hs ht, fun _ _ _ _ e => ⟨_, _, isOp2_reix ψ e⟩⟩

end GlobalTheory.TowU.RealComp

end
end

section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxChange_realised_comp_and_reindex : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' := by
  first | exact @GlobalTheory.TowU.RealComp.realised_comp_reix | exact GlobalTheory.TowU.RealComp.realised_comp_reix | (intros; apply GlobalTheory.TowU.RealComp.realised_comp_reix <;> assumption)
end

section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU

theorem card_two_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) :
    Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
  have h1 := d.e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_matrix,
    Module.finrank_baseChange] at h1
  omega

noncomputable def reidx {F : Type} [Field F] [NumberField F] {κ κ' : Type} (e : κ' ≃ κ) :
    ((κ' → AF F) × (κ' → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)) where
  toFun p := (p.1 ∘ e.symm, p.2 ∘ e.symm)
  invFun p := (p.1 ∘ e, p.2 ∘ e)
  map_add' p q := rfl
  map_smul' c p := rfl
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp

noncomputable def reindexD {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) : Darboux B κ where
  e := d.e.trans (reidx e)
  form w w' := by
    rw [d.form]
    have h : ∀ u v : κ' → AF F, (u ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = u ⬝ᵥ v := fun u v => by
      simp only [dotProduct, Function.comp_apply]
      exact e.symm.sum_comp (fun j => u j * v j)
    simp only [LinearEquiv.trans_apply]
    exact (congrArg₂ (· - ·) (h _ _) (h _ _)).symm

theorem reindexD_e {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) (w : W) :
    (reindexD d e).e w = ((d.e w).1 ∘ e.symm, (d.e w).2 ∘ e.symm) := rfl

theorem realised_of_sp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (hg : gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0) :
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act g) S S' := by
  have hcl := GlobalTheory.sympGen F κ g hg
  clear hg
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hx
    · exact GlobalTheory.T.exists_darbouxOperators_levi_and_double F ψ hψ κ A hA
    · exact GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent F ψ hψ κ C hC
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact GlobalTheory.T.weylElement_realised_by_fourierTransforms F ψ hψ κ
  | one =>
    obtain ⟨S, S', h⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ (Equiv.refl κ)
    refine ⟨S, S', ?_⟩
    have : GlobalTheory.AdelicSvN.act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) = fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ Equiv.refl κ, w.2 ∘ Equiv.refl κ) := by
      funext w; rw [GlobalTheory.AdelicSvN.act_one]; rfl
    rw [this]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨S, S', hS⟩ := hx
    obtain ⟨T, T', hT⟩ := hy
    have : GlobalTheory.AdelicSvN.act (x * y) = GlobalTheory.AdelicSvN.act x ∘ GlobalTheory.AdelicSvN.act (R := AF F) y := by
      funext w; exact GlobalTheory.AdelicSvN.act_mul x y w
    rw [this]
    exact ⟨S ∘ₗ T, T' ∘ₗ S', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ _ _ T T' S S' hT hS⟩

theorem darboux_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ (α β κ κ' : Type) [Fintype α] [Fintype β] [Fintype κ] [Fintype κ'] (B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F) (d : Darboux B κ) (d' : Darboux B κ'), IsRat d → IsRat d' → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => d'.e (d.e.symm w)) S S' := by
  intro F E _ _ _ _ _ σ _ ψ hψ α β κ κ' _ _ _ _ B d d' hd hd'
  have hc := card_two_eq F E d
  have hc' := card_two_eq F E d'
  have hκ : Fintype.card κ' = Fintype.card κ := by omega
  let e : κ' ≃ κ := Fintype.equivOfCardEq hκ
  let d'' := reindexD d' e
  have hd'' : IsRat d'' := fun x => by
    obtain ⟨y, z, h⟩ := hd' x
    refine ⟨y ∘ e.symm, z ∘ e.symm, ?_⟩
    rw [reindexD_e, h]; rfl
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.RatDarboux.exists_rat_symplectic F E α β κ B d d'' hc hd hd''
  obtain ⟨S, S', hS⟩ := realised_of_sp ψ hψ g hg
  obtain ⟨T, T', hT⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ' e
  have hs : (fun w => d'.e (d.e.symm w)) = (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) ∘ GlobalTheory.AdelicSvN.act g := by
    funext w
    have := hgd (d.e.symm w)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [Function.comp_apply, ← this, reindexD_e]
    ext i <;> simp
  rw [hs]
  exact ⟨T ∘ₗ S, S' ∘ₗ T', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ' _ _ S S' T T' hS hT⟩

end GlobalTheory.TowU
end
