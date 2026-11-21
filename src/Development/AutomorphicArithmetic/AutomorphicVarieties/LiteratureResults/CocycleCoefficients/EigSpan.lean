import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

noncomputable section

namespace UpperTheory.V.Lit.KT

open UpperHalfPlane ModularForm
open scoped Manifold

private structure Good (H : Subgroup SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) : Prop where
  hol : MDiff F
  bd : ∃ C : ℝ, ∀ z, ‖petersson k F F z‖ ≤ C
  inv : ∀ γ ∈ H, F ∣[k] γ = F

variable {H : Subgroup SL(2, ℤ)} {k : ℤ} {F G : ℍ → ℂ}

private theorem Good.cont (hF : Good H k F) (hG : Good H k G) : Continuous (petersson k F G) :=
  petersson_continuous k hF.hol.continuous hG.hol.continuous

private theorem Good.pbd (hF : Good H k F) (hG : Good H k G) : ∃ C : ℝ, ∀ z, ‖petersson k F G z‖ ≤ C := by
  obtain ⟨A, hA⟩ := hF.bd
  obtain ⟨B, hB⟩ := hG.bd
  refine ⟨A + B, fun z => le_trans ?_ (add_le_add (hA z) (hB z))⟩
  simp only [petersson, norm_mul, Complex.norm_conj]
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  nlinarith [sq_nonneg (‖F z‖ - ‖G z‖), norm_nonneg (F z), norm_nonneg (G z)]

private theorem Good.pinv (hF : Good H k F) (hG : Good H k G) : ∀ γ ∈ H, ∀ z, petersson k F G (γ • z) = petersson k F G z :=
  fun γ hγ z => by rw [← petersson_slash_SL, hF.inv γ hγ, hG.inv γ hγ]

private theorem Good.slash {K : Subgroup SL(2, ℤ)} (hF : Good K k F) (α : GL (Fin 2) ℝ) (h : H ≤ conjGL K α) :
    Good H k (F ∣[k] α) := by
  obtain ⟨A, hA⟩ := hF.bd
  refine ⟨hF.hol.slash k α, ⟨‖((|α.det.val| : ℝ) : ℂ) ^ (k - 2)‖ * A, fun z => ?_⟩, fun γ hγ => ?_⟩
  · rw [petersson_slash, norm_mul, norm_σ]
    exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
  · obtain ⟨y, hy, e⟩ := mem_conjGL.1 (h hγ)
    have e' : α * (γ : GL (Fin 2) ℝ) = (y : GL (Fin 2) ℝ) * α := by rw [e]; group
    rw [SL_slash, ← SlashAction.slash_mul, e', SlashAction.slash_mul, ← SL_slash, hF.inv y hy]

private theorem le_conj [hN : H.Normal] (γ : SL(2, ℤ)) : H ≤ conjGL H (γ : GL (Fin 2) ℝ) := fun x hx =>
  mem_conjGL.2 ⟨_, hN.conj_mem x hx γ, by simp⟩

private theorem Good.slashSL [H.Normal] (hF : Good H k F) (γ : SL(2, ℤ)) : Good H k (F ∣[k] γ) :=
  hF.slash _ (le_conj γ)

private theorem B_slash [H.FiniteIndex] {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (h1 : (conjGL H α).FiniteIndex)
    (h2 : (conjGL H α⁻¹).FiniteIndex) (hF : Good H k F) (hG : Good H k G) (hF' : Good H k (F ∣[k] α))
    (hG' : Good H k (G ∣[k] α)) :
    quotInt H (petersson k (F ∣[k] α) (G ∣[k] α)) = (α.det.val : ℂ) ^ (k - 2) * quotInt H (petersson k F G) := by
  have e : ∀ z, petersson k (F ∣[k] α) (G ∣[k] α) z = (α.det.val : ℂ) ^ (k - 2) * petersson k F G (α • z) := fun z => by
    rw [petersson_slash, σ, if_pos hα, abs_of_pos hα]; rfl
  have h0 : (α.det.val : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hα.ne')
  obtain ⟨C, hC⟩ := hF.pbd hG
  rw [funext e, quotInt_mul, quotInt_conj H α h1 h2 (hF.cont hG) hC (hF.pinv hG) fun γ hγ z => ?_]
  refine mul_left_cancel₀ h0 ?_
  rw [← e, ← e, hF'.pinv hG' γ hγ]

private theorem B_slashSL [H.FiniteIndex] [H.Normal] (γ : SL(2, ℤ)) (hF : Good H k F) (hG : Good H k G) :
    quotInt H (petersson k (F ∣[k] γ) (G ∣[k] γ)) = quotInt H (petersson k F G) := by
  have hd : (γ : GL (Fin 2) ℝ).det.val = 1 := by simp
  have h2 : (conjGL H (γ : GL (Fin 2) ℝ)⁻¹).FiniteIndex := by
    have := Subgroup.finiteIndex_of_le (le_conj (H := H) γ⁻¹)
    rwa [map_inv, map_inv] at this
  have := B_slash (α := (γ : GL (Fin 2) ℝ)) (by rw [hd]; exact one_pos) (Subgroup.finiteIndex_of_le (le_conj γ)) h2 hF hG
    (hF.slashSL γ) (hG.slashSL γ)
  rw [hd, Complex.ofReal_one, one_zpow, one_mul] at this
  exact this

private theorem B_smul_left [H.FiniteIndex] (c : ℂ) :
    quotInt H (petersson k (c • F) G) = conj c * quotInt H (petersson k F G) := by
  rw [← quotInt_mul]; congr 1; funext z; simp [petersson]; ring

private theorem B_smul_right [H.FiniteIndex] (c : ℂ) :
    quotInt H (petersson k F (c • G)) = c * quotInt H (petersson k F G) := by
  rw [← quotInt_mul]; congr 1; funext z; simp [petersson]; ring

private theorem Good.smul (hF : Good H k F) (c : ℂ) : Good H k (c • F) := by
  obtain ⟨A, hA⟩ := hF.bd
  refine ⟨hF.hol.const_smul c, ⟨‖c‖ ^ 2 * A, fun z => ?_⟩, fun γ hγ => by rw [SL_smul_slash, hF.inv γ hγ]⟩
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hA z) (by positivity))
  simp [petersson]; ring

private theorem B_adj [H.FiniteIndex] {α β : GL (Fin 2) ℝ} {p : ℕ} (hp : 0 < p) (hβ : β.det.val = p)
    (h1 : (conjGL H β).FiniteIndex) (h2 : (conjGL H β⁻¹).FiniteIndex) (hF : Good H k F) (hG : Good H k G)
    (hF' : Good H k (F ∣[k] α)) (hG' : Good H k (G ∣[k] β)) (e : (F ∣[k] α) ∣[k] β = (p : ℂ) ^ (k - 2) • F) :
    quotInt H (petersson k F (G ∣[k] β)) = quotInt H (petersson k (F ∣[k] α) G) := by
  have h := B_slash (by rw [hβ]; exact_mod_cast hp) h1 h2 hF' hG (e ▸ hF.smul _) hG'
  rw [e, B_smul_left, hβ, map_zpow₀, map_natCast, Complex.ofReal_natCast] at h
  exact mul_left_cancel₀ (zpow_ne_zero _ (by exact_mod_cast hp.ne')) h

private def dg (m n : ℕ) (h : m * n ≠ 0) : GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℚ), 0; 0, (n : ℚ)]
    (by rw [Matrix.det_fin_two_of, mul_zero, sub_zero]; exact_mod_cast h)).map (Rat.castHom ℝ)

private theorem dg_val (m n : ℕ) (h : m * n ≠ 0) : (dg m n h).1 = !![(m : ℝ), 0; 0, (n : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

private theorem dg_det (m n : ℕ) (h : m * n ≠ 0) : (dg m n h).det.val = (m * n : ℕ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, dg_val]; simp

private theorem dg_fin (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (m n : ℕ) (h : m * n ≠ 0) :
    (conjGL H (dg m n h)).FiniteIndex := finiteIndex_conjGL_rat H _

private theorem dg_fin' (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (m n : ℕ) (h : m * n ≠ 0) :
    (conjGL H (dg m n h)⁻¹).FiniteIndex := by
  rw [dg, ← map_inv]; exact finiteIndex_conjGL_rat H _

private theorem dg_slash (m n : ℕ) (h : m * n ≠ 0) (k : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[k] dg m n h) z = ((m * n : ℕ) : ℂ) ^ (k - 1) * (n : ℂ) ^ (-k) * F (ofComplex (m * (z : ℂ) / n)) := by
  have hpos : 0 < (dg m n h).det.val := by rw [dg_det]; exact_mod_cast Nat.pos_of_ne_zero h
  rw [slash_apply, σ, if_pos hpos, dg_det, ← ofComplex_apply (dg m n h • z), coe_smul_of_det_pos hpos]
  simp [num, denom, dg_val]
  ring

private theorem dg_mul (m n : ℕ) (h : m * n ≠ 0) (h' : n * m ≠ 0) (k : ℤ) (F : ℍ → ℂ) :
    (F ∣[k] dg m n h) ∣[k] dg n m h' = ((m * n : ℕ) : ℂ) ^ (k - 2) • F := by
  have e : dg m n h * dg n m h' = dg (m * n) (m * n) (mul_ne_zero h h) := by
    apply Units.ext
    simp [dg_val, mul_comm]
  have h0 : ((m * n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h
  funext z
  rw [← SlashAction.slash_mul, e, dg_slash, mul_div_cancel_left₀ _ h0, ofComplex_apply, Nat.cast_mul (m * n), mul_zpow,
    ← zpow_add₀ h0, ← zpow_add₀ h0, Pi.smul_apply, smul_eq_mul]
  congr 2
  ring

private theorem T_exp {M k : ℕ} [NeZero M] (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) (c : ℂ) (f Tf : CuspForm (Gamma1 M) (k : ℤ))
    (h : ∀ n, 1 ≤ n → coef Tf n = coef f (p * n) + c * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0))
    (ha : p * 1 ≠ 0) (hb : 1 * p ≠ 0) (z : ℍ) :
    Tf z = c * (⇑f ∣[(k : ℤ)] dg p 1 ha) z +
      ∑ u ∈ Finset.range p, ((⇑f ∣[(k : ℤ)] dg 1 p hb) ∣[(k : ℤ)] (ModularGroup.T ^ (u : ℤ))) z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp.ne_one)
  have h1 : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hsum : ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (τ : ℍ),
      HasSum (fun m => coef f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := fun f τ =>
    hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1) f.holo'
      (ModularFormClass.bdd_at_infty f) τ
  have h0 : ∀ f : CuspForm (Gamma1 M) (k : ℤ), coef f 0 = 0 := fun f => CuspFormClass.qExpansion_coeff_zero f one_pos h1
  have a1 := hasSum_heckeOne 1 hp.pos (hsum f) z
  have a2 := hasSum_heckeOne 2 hp.pos (hsum f) z
  have a3 := a1.add ((a2.sub a1).mul_left ((c * (p : ℂ) ^ (k - 1) - 1) / (p - 1)))
  have e := (hsum Tf z).unique (cast (congrArg (HasSum · _) (funext fun m => ?_)) a3)
  · have e1 : ∀ u : ℕ, ((⇑f ∣[(k : ℤ)] dg 1 p hb) ∣[(k : ℤ)] (ModularGroup.T ^ (u : ℤ))) z =
        (p : ℂ)⁻¹ * f (ofComplex (((z : ℂ) + u) / p)) := fun u => by
      have hd : denom (ModularGroup.T ^ (u : ℤ) : SL(2, ℤ)) z = 1 := by
        rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
      rw [SL_slash_apply, dg_slash, ModularGroup.coe_T_zpow_smul_eq, hd]
      simp [zpow_sub₀ hp0]
      left
      field_simp
    rw [e, dg_slash]
    simp only [e1, heckeOne, ← Finset.mul_sum]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp
    field_simp
    ring
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [h0]
    · rw [h m hm]
      simp only [smul_eq_mul]
      field_simp
      ring

private theorem B_symm [H.FiniteIndex] : quotInt H (petersson k G F) = conj (quotInt H (petersson k F G)) := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  simp only [quotInt, finsum_eq_sum_of_fintype, map_sum, ← integral_conj, ← petersson_symm]

private theorem quotInt_petersson_eq_add_of_hecke_sum [H.FiniteIndex] [H.Normal] {p : ℕ} {c : ℂ} {A B TF : ℍ → ℂ} (hF : Good H k F) (hA : Good H k A)
    (hB : Good H k B) (hT : ∀ u : ℤ, F ∣[k] (ModularGroup.T ^ u) = F)
    (e : ∀ z, TF z = c * A z + ∑ u ∈ Finset.range p, (B ∣[k] (ModularGroup.T ^ (u : ℤ))) z) :
    quotInt H (petersson k F TF) = c * quotInt H (petersson k F A) + p * quotInt H (petersson k F B) := by
  have e1 : petersson k F TF = fun z => petersson k F (c • A) z +
      ∑ u ∈ Finset.range p, petersson k F (B ∣[k] (ModularGroup.T ^ (u : ℤ))) z := by
    funext z
    simp only [petersson, e, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  have hc := fun u : ℕ => hF.cont (hB.slashSL (ModularGroup.T ^ (u : ℤ)))
  have hb := fun u : ℕ => hF.pbd (hB.slashSL (ModularGroup.T ^ (u : ℤ)))
  choose C hC using hb
  obtain ⟨D, hD⟩ := hF.pbd (hA.smul c)
  rw [e1, quotInt_add H (hF.cont (hA.smul c)) hD (continuous_finset_sum _ fun u _ => hc u)
    (C' := ∑ u ∈ Finset.range p, C u) fun z => (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => hC u z),
    quotInt_sum H _ hc fun u => ⟨_, hC u⟩, B_smul_right]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => quotInt H (petersson k F B)) fun u _ => ?_]
  · simp
  · rw [← B_slashSL (ModularGroup.T ^ (u : ℤ)) hF hB, hT]

private theorem good_cusp {M k : ℕ} [NeZero M] (f : CuspForm (Gamma1 M) (k : ℤ)) (h : H ≤ Gamma1 M) : Good H k f :=
  ⟨f.holo', CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f,
    fun γ hγ => f.slash_action_eq' _ ⟨γ, h hγ, rfl⟩⟩

private theorem dg_swap {M p : ℕ} (hc : p.Coprime M) (ha : p * 1 ≠ 0) (hb : 1 * p ≠ 0) :
    ∃ δ ∈ Gamma0 M, ∃ γ ∈ Gamma1 M, δ 1 1 = p ∧ dg p 1 ha * (δ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * dg 1 p hb := by
  obtain ⟨r, s, h⟩ : IsCoprime (p : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  obtain ⟨δ, hδ⟩ : ∃ δ : SL(2, ℤ), δ.1 = !![r, -s; M, p] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination h⟩, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), γ.1 = !![p * r, -s; M, 1] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination h⟩, rfl⟩
  refine ⟨δ, by simp [Gamma0_mem, hδ], γ, ?_, by simp [hδ], ?_⟩
  · have := congrArg (Int.cast : ℤ → ZMod M) h
    rw [Gamma1_mem]
    simpa [mul_comm, hγ] using this
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg_val, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, hδ, hγ]

end UpperTheory.V.Lit.KT

open UpperHalfPlane ModularForm UpperTheory.V.Lit.KT in
theorem UpperTheory.V.Lit.KT.petAdj :
    ∀ (M k : ℕ), 0 < M → 1 ≤ k → ∀ (χ : DirichletCharacter ℂ M) (p : ℕ), p.Prime → ¬ p ∣ M → ∀ f g Tf Tg : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f → HasChar k χ g →
    (∀ n, 1 ≤ n → coef Tf n = coef f (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0)) →
    (∀ n, 1 ≤ n → coef Tg n = coef g (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g (n / p) else 0)) →
    pet M k f Tg = χ (p : ZMod M) * pet M k Tf g := by
  intro M k hM hk χ p hp hpM f g Tf Tg _ hg hTf hTg
  haveI : NeZero M := ⟨hM.ne'⟩
  have hc : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  have ha : p * 1 ≠ 0 := by simpa using hp.ne_zero
  have hb : 1 * p ≠ 0 := by simpa using hp.ne_zero
  haveI := dg_fin (Gamma1 M) p 1 ha
  haveI := dg_fin (Gamma1 M) 1 p hb
  set H := (Gamma1 M ⊓ conjGL (Gamma1 M) (dg p 1 ha) ⊓ conjGL (Gamma1 M) (dg 1 p hb)).normalCore with hH
  have hle := (Gamma1 M ⊓ conjGL (Gamma1 M) (dg p 1 ha) ⊓ conjGL (Gamma1 M) (dg 1 p hb)).normalCore_le
  rw [← hH, le_inf_iff, le_inf_iff] at hle
  obtain ⟨⟨l1, la⟩, lb⟩ := hle
  have G0 := fun f : CuspForm (Gamma1 M) (k : ℤ) => good_cusp f l1
  have G1 := fun f : CuspForm (Gamma1 M) (k : ℤ) => good_cusp f le_rfl
  have Ga := fun f : CuspForm (Gamma1 M) (k : ℤ) => (G1 f).slash _ la
  have Gb := fun f : CuspForm (Gamma1 M) (k : ℤ) => (G1 f).slash _ lb
  have hT : ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (u : ℤ), ⇑f ∣[(k : ℤ)] (ModularGroup.T ^ u) = f := fun f u =>
    (G1 f).inv _ (by rw [Gamma1_mem]; simp [ModularGroup.coe_T_zpow])
  have tow : ∀ f g : CuspForm (Gamma1 M) (k : ℤ),
      quotInt H (petersson k f g) = (H.relIndex (Gamma1 M) : ℂ) * pet M k f g := fun f g =>
    quotInt_tower l1 _ ((G1 f).pinv (G1 g))
  have e1 := quotInt_petersson_eq_add_of_hecke_sum (G0 f) (Ga g) (Gb g) (hT f) (T_exp hk hp _ g Tg hTg ha hb)
  have e2 := congrArg conj (quotInt_petersson_eq_add_of_hecke_sum (G0 g) (Ga f) (Gb f) (hT g) (T_exp hk hp _ f Tf hTf ha hb))
  rw [map_add, map_mul, map_mul, ← B_symm, ← B_symm, ← B_symm, Complex.conj_natCast] at e2
  have e3 := B_adj hp.pos (by rw [dg_det, one_mul]) (dg_fin H 1 p hb) (dg_fin' H 1 p hb) (G0 f) (G0 g) (Ga f) (Gb g)
    (by rw [dg_mul, mul_one])
  have e4 := B_adj hp.pos (by rw [dg_det, mul_one]) (dg_fin H p 1 ha) (dg_fin' H p 1 ha) (G0 f) (G0 g) (Gb f) (Ga g)
    (by rw [dg_mul, one_mul])
  obtain ⟨δ, hδ, γ, hγ, h11, hm⟩ := dg_swap hc ha hb
  have e5 := B_slashSL δ (Ga f) (G0 g)
  rw [hg δ hδ, h11, Int.cast_natCast, B_smul_right, SL_slash, ← SlashAction.slash_mul, hm, SlashAction.slash_mul,
    ← SL_slash, (G1 f).inv γ hγ] at e5
  have e6 : χ (p : ZMod M) * conj (χ (p : ZMod M)) = 1 := by
    have := χ.unit_norm_eq_one (ZMod.unitOfCoprime p hc)
    rw [ZMod.coe_unitOfCoprime] at this
    rw [Complex.mul_conj', this]; simp
  refine mul_left_cancel₀ (a := (H.relIndex (Gamma1 M) : ℂ)) (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) ?_
  rw [mul_left_comm, ← tow, ← tow, e1, e2, e3, e4, ← e5]
  linear_combination (-(χ (p : ZMod M)) * quotInt H (petersson k (⇑f ∣[(k : ℤ)] dg 1 p hb) g)) * e6
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

open UpperHalfPlane MeasureTheory in
private theorem petHerm_cont (M k : ℕ) (f g : CuspForm (Gamma1 M) (k : ℤ)) (γ : SL(2, ℤ)) :
    Continuous fun z : ℍ => petersson (k : ℤ) f g (γ • z) :=
  (petersson_continuous _ (ModularFormClass.continuous f) (ModularFormClass.continuous g)).comp
    (continuous_const_smul (γ : GL (Fin 2) ℝ))

open UpperHalfPlane MeasureTheory in
private theorem petHerm_int (hF : UpperTheory.V.Af.Rs.FdFin) (M k : ℕ) [NeZero M] (f g : CuspForm (Gamma1 M) (k : ℤ)) (γ : SL(2, ℤ)) :
    IntegrableOn (fun z : ℍ => petersson (k : ℤ) f g (γ • z)) ModularGroup.fd := by
  obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f g
  exact Measure.integrableOn_of_bounded (M := B) hF.2.ne (petHerm_cont M k f g γ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hB _)

open UpperHalfPlane in
private theorem petHerm_self (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    petersson (k : ℤ) f f z = ((Complex.normSq (f z) * z.im ^ k : ℝ) : ℂ) := by
  simp [petersson, Complex.normSq_eq_conj_mul_self]

open UpperHalfPlane MeasureTheory in
theorem UpperTheory.V.Lit.KT.petHerm :
    ∀ (M k : ℕ), 0 < M → (∀ f g h : CuspForm (Gamma1 M) (k : ℤ), pet M k f (g + h : CuspForm (Gamma1 M) (k : ℤ)) = pet M k f g + pet M k f h) ∧ (∀ (c : ℂ) (f g : CuspForm (Gamma1 M) (k : ℤ)), pet M k f (c • g : CuspForm (Gamma1 M) (k : ℤ)) = c * pet M k f g) ∧
    (∀ f g : CuspForm (Gamma1 M) (k : ℤ), pet M k g f = conj (pet M k f g)) ∧ ∀ f : CuspForm (Gamma1 M) (k : ℤ), pet M k f f = 0 → f = 0 := by
  intro M k hM
  haveI : NeZero M := ⟨hM.ne'⟩
  have hV : UpperTheory.V.Af.Rs.VolMap := UpperTheory.V.Af.Rs.volMap
  have hF : UpperTheory.V.Af.Rs.FdFin := UpperTheory.V.Af.Rs.fdFin (UpperTheory.V.Af.Rs.stripIm hV) hV
  have hP : UpperTheory.V.Af.Rs.FdPos := UpperTheory.V.Af.Rs.fdPos hV
  have : Finite (SL(2, ℤ) ⧸ Gamma1 M) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (SL(2, ℤ) ⧸ Gamma1 M) := Fintype.ofFinite _
  refine ⟨fun f g h => ?_, fun c f g => ?_, fun f g => ?_, fun f hf => ?_⟩
  · simp only [pet, finsum_eq_sum_of_fintype]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_add (petHerm_int hF M k f g _) (petHerm_int hF M k f h _)]
    congr 1
    funext z
    simp only [petersson, CuspForm.add_apply]
    ring
  · simp only [pet, finsum_eq_sum_of_fintype]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext z
    simp only [petersson, CuspForm.IsGLPos.smul_apply, smul_eq_mul]
    ring
  · simp only [pet, finsum_eq_sum_of_fintype]
    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_conj]
    congr 1
    funext z
    exact petersson_symm _ _ _ _
  · by_contra hne
    obtain ⟨z0, hz0⟩ : ∃ z, f z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by ext z; simpa using hall z)
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z0
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gamma1 M) g
    have hre : (pet M k f f).re = ∑ γ : SL(2, ℤ) ⧸ Gamma1 M,
        ∫ z in ModularGroup.fd, (petersson (k : ℤ) f f (γ.out⁻¹ • z)).re := by
      simp only [pet, finsum_eq_sum_of_fintype]
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      exact (integral_re (petHerm_int hF M k f f _)).symm
    have h0 : ∀ z : ℍ, 0 ≤ (petersson (k : ℤ) f f z).re := fun z => by
      rw [petHerm_self, Complex.ofReal_re]
      exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le _)
    rw [hf, Complex.zero_re] at hre
    refine ne_of_lt (Finset.sum_pos' (fun γ _ => integral_nonneg fun z => h0 _)
      ⟨(g : SL(2, ℤ) ⧸ Gamma1 M), Finset.mem_univ _, ?_⟩) hre
    refine hP _ (Complex.continuous_re.comp (petHerm_cont M k f f _)) (fun z => h0 _)
      (petHerm_int hF M k f f _).re (g • z0) hg ?_
    rw [hh, mul_inv_rev, mul_smul, inv_smul_smul]
    have e : petersson (k : ℤ) f f (((h : SL(2, ℤ))⁻¹) • z0) = petersson (k : ℤ) f f z0 :=
      SlashInvariantFormClass.petersson_smul (Γ := (Gamma1 M : Subgroup (GL (Fin 2) ℝ)))
        (g := ((h⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨_, inv_mem h.2, rfl⟩
    rw [e, petHerm_self, Complex.ofReal_re]
    exact mul_pos (Complex.normSq_pos.2 hz0) (pow_pos z0.im_pos _)
end

section
noncomputable section SlopeTestRemainingChoices

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Lit
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Lit.KT.EigenformSpan

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [← map_add]
  congr 1
  exact ModularForm.qExpansion_add one_pos (one_mem_per N) f g

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  funext n
  simp only [fT_apply]
  have h1 : q ∣ p * n ↔ q ∣ n := hc.symm.dvd_mul_left
  have h2 : p ∣ q * n ↔ p ∣ n := hc.dvd_mul_left
  by_cases a : p ∣ n <;> by_cases b : q ∣ n
  · obtain ⟨m, rfl⟩ : p * q ∣ n := hc.mul_dvd_of_dvd_of_dvd a b
    have e1 : p * q * m / p = q * m := by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have e2 : p * q * m / q = p * m := by rw [mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
    simp only [h1, h2, a, b, if_true, e1, e2, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_assoc _ a, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · have b' : ¬ q ∣ n / p := fun h => b (h.trans (Nat.div_dvd_of_dvd a))
    simp only [h1, h2, a, b, b', if_true, if_false, Nat.mul_div_assoc _ a, mul_left_comm q p]
    ring
  · have a' : ¬ p ∣ n / q := fun h => a (h.trans (Nat.div_dvd_of_dvd b))
    simp only [h1, h2, a, b, a', if_true, if_false, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · simp only [h1, h2, a, b, if_false, mul_left_comm q p]
    ring

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

section
open Module
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

end

private theorem span_eig {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (T : J → Module.End ℂ M)
    (hc : ∀ i j, T i * T j = T j * T i) (B : M → M →ₗ[ℂ] ℂ) (hB : ∀ x y, B y x = conj (B x y))
    (h0 : ∀ x, B x x = 0 → x = 0) (c : J → ℂ) (hadj : ∀ j x y, B x (T j y) = c j * B (T j x) y) :
    Submodule.span ℂ {v : M | ∀ j, ∃ a : ℂ, T j v = a • v} = ⊤ := by
  set S : Set M := {v : M | ∀ j, ∃ a : ℂ, T j v = a • v} with hS
  by_contra hne
  have hlt : Module.finrank ℂ (Submodule.span ℂ S) < Module.finrank ℂ M := Submodule.finrank_lt hne
  let b := Module.finBasis ℂ (Submodule.span ℂ S)
  let L : M →ₗ[ℂ] (Fin (Module.finrank ℂ (Submodule.span ℂ S)) → ℂ) := LinearMap.pi fun i => B (b i).1
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hyS : ∀ v ∈ S, B v y = 0 := by
    intro v hv
    have h1 : (B y).comp (Submodule.span ℂ S).subtype = 0 := b.ext fun i => by
      have : B (b i).1 y = 0 := congrFun (LinearMap.mem_ker.1 hy) i
      change B y (b i).1 = 0
      rw [hB, this, map_zero]
    have h2 : B y v = 0 := LinearMap.congr_fun h1 ⟨v, Submodule.subset_span hv⟩
    rw [hB, h2, map_zero]
  let U : Submodule ℂ M := ⨅ v : S, LinearMap.ker (B v.1)
  have hU : ∀ x, x ∈ U ↔ ∀ v ∈ S, B v x = 0 := fun x => by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  obtain ⟨w, hw, hw0, hwe⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl ((Submodule.ne_bot_iff U).2 ⟨y, (hU y).2 hyS, hy0⟩) (by
    intro j x hx
    rw [hU] at hx ⊢
    intro v hv
    obtain ⟨a, ha⟩ := hv j
    have h3 : B x v = 0 := by rw [hB, hx v hv, map_zero]
    rw [hadj, ha, hB, map_smul, h3, smul_zero, map_zero, mul_zero])
  exact hw0 (h0 w ((hU w).1 hw w hwe))

private def Phi (N : ℕ) (k : ℤ) : CuspForm (Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun g n := if n = 0 then 0 else coef g n
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi N k g n = if n = 0 then 0 else coef g n := rfl

private theorem fT_Phi (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p e (Phi N k g) n = coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0) := by
  have h1 : p * n ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
  rw [fT_apply, Phi_apply, if_neg h1]
  by_cases h : p ∣ n
  · have : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne'
    rw [if_pos h, if_pos h, Phi_apply, if_neg this]
  · rw [if_neg h, if_neg h]

private theorem eig_iff (N k : ℕ) (χ : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) (k : ℤ)) {p : ℕ} (hp : p.Prime) (c : ℂ) :
    fT p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (Phi N k g) = c • Phi N k g ↔ IsEigAt k χ g p c := by
  constructor
  · intro h n hn
    have := congrFun h n
    rwa [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show ¬ n = 0 by omega), smul_eq_mul] at this
  · intro h
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg hn.ne', smul_eq_mul]
      exact h n hn

private theorem main (M N k : ℕ) (hN : 0 < N) (hNM : N ∣ M) (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) (k : ℤ)) (hg : HasChar k χ g) :
    g ∈ Submodule.span ℂ {h : CuspForm (Gamma1 N) (k : ℤ) | HasChar k χ h ∧
      ∃ b : ℕ → ℂ, ∀ p : ℕ, p.Prime → ¬ p ∣ M → IsEigAt k χ h p (b p)} := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI := (finDim N k).1
  have hinj : Function.Injective (Phi N k) := (injective_iff_map_eq_zero _).2 fun f h0 =>
    (finDim N k).2 f fun n hn => by
      have := congrFun h0 n
      rwa [Phi_apply, if_neg (by omega)] at this
  let J := {p : ℕ // p.Prime ∧ ¬ p ∣ M}
  let e : J → ℂ := fun p => χ ((p.1 : ℕ) : ZMod N) * ((p.1 : ℕ) : ℂ) ^ (k - 1)
  have hex := fun (p : J) (f : chSub N k χ) => heckeEx N k hk χ f.1 f.2 p.1 p.2.1
  choose t ht1 ht2 using hex
  have ht : ∀ (p : J) (f : chSub N k χ), Phi N k (t p f) = fT p.1 (e p) (Phi N k f.1) := by
    intro p f
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k f.1 p.2.1 _ hn, Phi_apply, if_neg hn.ne', ht2 p f n hn]
  let T : J → Module.End ℂ (chSub N k χ) := fun p =>
    { toFun := fun f => ⟨t p f, ht1 p f⟩
      map_add' := fun f f' => Subtype.ext (hinj (by
        simp only [Submodule.coe_add, map_add, ht]))
      map_smul' := fun a f => Subtype.ext (hinj (by
        simp only [Submodule.coe_smul, map_smul, ht, RingHom.id_apply])) }
  have hT : ∀ p (f : chSub N k χ), (T p f).1 = t p f := fun _ _ => rfl
  have hc : ∀ p q, T p * T q = T q * T p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · ext1 v
      refine Subtype.ext (hinj ?_)
      simp only [Module.End.mul_apply, hT, ht]
      exact fT_comm p.2.1 q.2.1 (fun h => hpq (Subtype.ext h)) _ _ _
  obtain ⟨hadd, hsmul, hherm, hdef⟩ := petHerm N k hN
  let B : chSub N k χ → chSub N k χ →ₗ[ℂ] ℂ := fun f =>
    { toFun := fun f' => pet N k f.1 f'.1
      map_add' := fun x y => hadd f.1 x.1 y.1
      map_smul' := fun a x => hsmul a f.1 x.1 }
  have htop := span_eig T hc B (fun x y => hherm x.1 y.1) (fun x hx => Subtype.ext (hdef x.1 hx))
    (fun p => χ (p.1 : ZMod N)) (fun p x y => petAdj N k hN hk χ p.1 p.2.1 (fun h => p.2.2 (h.trans hNM))
      x.1 y.1 (t p x) (t p y) x.2 y.2 (ht2 p x) (ht2 p y))
  have hmem : (⟨g, hg⟩ : chSub N k χ) ∈ Submodule.span ℂ {v : chSub N k χ | ∀ j, ∃ a : ℂ, T j v = a • v} := by
    rw [htop]; trivial
  have h2 := Submodule.mem_map_of_mem (f := (chSub N k χ).subtype) hmem
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, hv, rfl⟩
  choose a ha using hv
  refine ⟨v.2, fun p => if h : p.Prime ∧ ¬ p ∣ M then a ⟨p, h⟩ else 0, fun p hp hpM => ?_⟩
  simp only [dif_pos (And.intro hp hpM)]
  refine (eig_iff N k χ v.1 hp _).1 ?_
  have h3 := congrArg (fun x : chSub N k χ => Phi N k x.1) (ha ⟨p, hp, hpM⟩)
  simp only [hT, ht, Submodule.coe_smul, map_smul] at h3
  exact h3

end UpperTheory.V.Lit.KT.EigenformSpan

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

end
