import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplitting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryRootEmbedding
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpperTriangular

section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_linear_functional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ w : ℂ, w ≠ 0 → ‖w‖ * (q : ℝ) ^ 2 < 1 →
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | exact GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | (intros; apply GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral <;> assumption)
end

section
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot

section Cont

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem continuous_of_v_eq (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero L _).tendsto_iff (Valued.hasBasis_nhds_zero L _)]
  refine fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rwa [show Valued.v.restrict (σ x) = Valued.v.restrict x from (Valuation.restrict_inj _).2 (hv x)]

theorem continuous_nU_val : Continuous fun x : L => ((nU x : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact continuous_id | exact continuous_const

theorem continuous_nU_inv_val :
    Continuous fun x : L => (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nU, Units.inv_mk] <;>
    first | exact continuous_id | exact continuous_const | exact continuous_neg

theorem continuous_partner_nU (σ : L →+* L) (hc : Continuous σ) :
    Continuous fun x : L => partner σ (nU x) := by
  unfold partner cT
  exact (continuous_const.matrix_mul
    (continuous_nU_inv_val.matrix_map hc).matrix_transpose).matrix_mul continuous_const

theorem continuous_uR_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) (a : ℕ)
    (h : 2 * (a + 2) ≤ n) :
    Continuous fun x : L => (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  simp only [uR, rootHom_val, blockM]
  exact (continuous_const.add (((continuous_const.matrix_mul
    (continuous_nU_val.sub continuous_const))).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul
    ((continuous_partner_nU σ hc).sub continuous_const)).matrix_mul continuous_const)

theorem uR_neg (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) :
    (uR σ hσ a h x)⁻¹ = uR σ hσ a h (-x) := by
  have h0 : uR σ hσ a h (0 : L) = 1 := by
    have e : nU (0 : L) = 1 := by
      ext p r; fin_cases p <;> fin_cases r <;> simp [nU]
    simp only [uR, e, map_one]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← uR_add, add_neg_cancel, h0]

theorem continuous_uR : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    Continuous (uR σ hU.1 a h : L → GU σ n) := by
  intro L _ _ ϖ σ q n hU a h
  have hc : Continuous σ := continuous_of_v_eq σ hU.2.1
  refine Continuous.subtype_mk (f := fun x => ((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)) ?_ _
  refine Units.continuous_iff.2 ⟨continuous_uR_val σ hU.1 hc a h, ?_⟩
  have e : ∀ x : L, ((((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((uR σ hU.1 a h (-x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun x => by
    rw [← uR_neg, Subgroup.coe_inv]
  simp only [e]
  exact (continuous_uR_val σ hU.1 hc a h).comp continuous_neg

end Cont

end GlobalTheory.CompanionTheory.SwapRoot

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitary_root_map : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), Continuous (uR σ hU.1 a h : L → GU σ n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapRoot.continuous_uR
end

section
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapFactor

section Local
variable {L : Type} [Field L]

def betaU (x : L) (hx : x ≠ 0) : GL (Fin 2) L where
  val := !![-x⁻¹, 1; 0, x]
  inv := !![-x, 1; 0, x⁻¹]
  val_inv := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
  inv_val := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem wU_mul_nU (x : L) (hx : x ≠ 0) :
    wU L * nU x = betaU x hx * (wU L * nU x⁻¹ * wU L) := by
  apply Units.ext
  ext p r
  fin_cases p <;> fin_cases r <;>
    simp [betaU, wU, nU, w2, Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem partner_betaU_lower (σ : L →+* L) (x : L) (hx : x ≠ 0) : partner σ (betaU x hx) 1 0 = 0 := by
  have : ((betaU x hx)⁻¹ : GL (Fin 2) L).val = !![-x, 1; 0, x⁻¹] := rfl
  have hw : ∀ M : Matrix (Fin 2) (Fin 2) L, (w2 L * M * w2 L) 1 0 = M 0 1 := fun M => by
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [partner, hw, this]
  simp [cT]

theorem arith (u v Q : ℂ) (hQ : Q ≠ 0) (o N : ℤ) :
    u ^ (-o) * Q ^ (-(-o) * N) * (v ^ o * Q ^ (-o * (N - 2))) = ((u / v) / Q ^ 2) ^ (-o) := by
  have h2 : (Q ^ 2) ^ (-o) = Q ^ (-(2 * o)) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have h3 : Q ^ (-(-o) * N) * Q ^ (-o * (N - 2)) = Q ^ (2 * o) := by
    rw [← zpow_add₀ hQ]; congr 1; ring
  have h4 : v ^ o = (v ^ (-o))⁻¹ := by rw [zpow_neg, inv_inv]
  rw [div_zpow, div_zpow, h2, zpow_neg Q (2 * o)]
  calc _ = u ^ (-o) * (v ^ (-o))⁻¹ * (Q ^ (-(-o) * N) * Q ^ (-o * (N - 2))) := by rw [h4]; ring
    _ = _ := by rw [h3]; simp [div_eq_mul_inv]

end Local

section Root
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}

theorem ordL_neg' (x : L) (hx : x ≠ 0) : ordL (-x) = ordL x := by
  have h1 := v_eq_exp' (neg_ne_zero.2 hx)
  rw [Valuation.map_neg, v_eq_exp' hx] at h1
  have := WithZero.exp_injective h1
  omega

theorem ordL_one' : ordL (1 : L) = 0 := by simp [ordL]; rfl

theorem isBorel_root (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) :
    IsBorelU (rootHom σ hσ a h (betaU x hx)) := by
  intro i j hji
  rw [rootHom_val]
  by_cases hI : (∃ p, i = cI n a h p) ∧ ∃ r, j = cI n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hI
    rw [blockM_cI]
    have hlt : (cI n a h r : ℕ) < (cI n a h p : ℕ) := hji
    simp only [cI] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    rfl
  by_cases hJ : (∃ p, i = cJ n a h p) ∧ ∃ r, j = cJ n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hJ
    rw [blockM_cJ]
    have hlt : (cJ n a h r : ℕ) < (cJ n a h p : ℕ) := hji
    simp only [cJ] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    exact partner_betaU_lower σ x hx
  rw [blockM_out]
  · exact Matrix.one_apply_ne (ne_of_gt hji)
  · by_contra hc
    push_neg at hc
    exact hI ⟨by simpa [eq_comm] using hc.1, by simpa using hc.2⟩
  · by_contra hc
    push_neg at hc
    exact hJ ⟨by simpa using hc.1, by simpa using hc.2⟩

theorem diag_a (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a, hk⟩ ⟨a, hk⟩ = -x⁻¹ := by
  have e : (⟨a, hk⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem root_hom_diag_entry_eq (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a + 1 < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a + 1, hk⟩ ⟨a + 1, hk⟩ = x := by
  have e : (⟨a + 1, hk⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem diag_other (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (k : Fin n)
    (hk : k.val < n / 2) (h1 : k.val ≠ a) (h2 : k.val ≠ a + 1) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k = 1 := by
  rw [rootHom_val, blockM_out]
  · exact Matrix.one_apply_eq k
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cI] at this
    omega
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cJ] at this
    omega

end Root

theorem sR_uR_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj x hx
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨rootHom σ hU.1 a h (betaU x hx), isBorel_root hU.1 a h x hx, ?_, ?_⟩
  · have hij : i ≠ j := fun e => by
      have := congrArg Fin.val e
      omega
    have ha : a < n := by omega
    have ha1 : a + 1 < n := by omega
    have hin : i.val < n := by omega
    have hjn : j.val < n := by omega
    unfold chiDeltaU
    rw [Finset.prod_eq_mul i j hij ?_ (by simp) (by simp)]
    · rw [dif_pos hin, dif_pos hjn]
      have ei : (⟨i.val, hin⟩ : Fin n) = ⟨a, ha⟩ := Fin.ext hi
      have ej : (⟨j.val, hjn⟩ : Fin n) = ⟨a + 1, ha1⟩ := Fin.ext hj
      rw [ei, ej, diag_a, root_hom_diag_entry_eq, ordL_neg' _ (inv_ne_zero hx), ordL_inv' hx, hi, hj]
      have hN : ((n : ℤ) - 1 - 2 * ((a + 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 - 2 * (a : ℤ)) - 2 := by
        push_cast; ring
      rw [hN]
      exact arith _ _ _ hq _ _
    · intro k _ hk
      have hkn : k.val < n := by omega
      rw [dif_pos hkn, diag_other hU.1 a h x hx ⟨k.val, hkn⟩ (by simpa using k.2)
        (fun e => hk.1 (Fin.ext (by simpa [hi] using e)))
        (fun e => hk.2 (Fin.ext (by simpa [hj] using e))), ordL_one']
      simp
  · simp only [sR, uR, ← map_mul]
    exact congrArg _ (wU_mul_nU x hx)

end GlobalTheory.CompanionTheory.SwapFactor

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_reflection_root_borel_decomp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor
end

section
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

variable {L : Type} [Field L]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  have hw : (((wU L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = w2 L := rfl
  have hc : cT σ (w2 L) = w2 L := by
    delta cT w2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  delta partner
  rw [hw, hc, weyl_mul_weyl, one_mul]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem cM_conj_int {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c)ᵀ) b d) ≤ 1 := by
  have hA : ∀ (x : Fin n) (p : Fin 2), Valued.v (cM L c x p) ≤ 1 := by
    intro x p
    show Valued.v (if x = c p then (1 : L) else 0) ≤ 1
    split_ifs <;> simp
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun r _ => ?_
  rw [Valuation.map_mul, Matrix.transpose_apply, Matrix.mul_apply]
  refine mul_le_one' ?_ (hA d r)
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun p _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA b p) (hP p r)

theorem weyl_sub_one_entries_integral (p r : Fin 2) : Valued.v ((w2 L - 1) p r) ≤ 1 := by
  delta w2
  fin_cases p <;> fin_cases r <;> simp [Matrix.one_apply]

theorem block_matrix_weyl_integral {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Formalism.UG.P.fIwasawaInt (blockM a h (w2 L) (w2 L)) := by
  delta blockM
  intro i j
  simp only [Matrix.add_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (cM_conj_int _ _ weyl_sub_one_entries_integral i j))
    (cM_conj_int _ _ weyl_sub_one_entries_integral i j)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem sR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    sR σ hU.1 a h ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h
  have hval : (((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (w2 L) (w2 L) := by
    show blockM a h (w2 L) (partner σ (wU L)) = _
    rw [partner_wU]
  have hwinv : (wU L)⁻¹ = wU L := Units.ext rfl
  have hginv : (sR σ hU.1 a h)⁻¹ = sR σ hU.1 a h := by
    show ((rootHom σ hU.1 a h) (wU L))⁻¹ = (rootHom σ hU.1 a h) (wU L)
    rw [← map_inv, hwinv]
  have hBB : blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L) = 1 := by
    have h1 := ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L).mul_inv
    rw [← Subgroup.coe_inv, hginv, hval] at h1
    exact h1
  have hint : ∀ i j, blockM a h (w2 L) (w2 L) i j ∈ intL L := fun i j => block_matrix_weyl_integral (L := L) a h i j
  let Bi : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨blockM a h (w2 L) (w2 L) i j, hint i j⟩
  have hBi : ∀ i j, ((Bi * Bi) i j : L) = (blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L)) i j := by
    intro i j
    simp [Bi, Matrix.mul_apply]
  have hy : Bi * Bi = 1 := by
    ext i j
    rw [hBi, hBB, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) ∈ GU σ n ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨(sR σ hU.1 a h).2, ⟨⟨Bi, Bi, hy, hy⟩, ?_⟩⟩
  apply Units.ext
  rw [hval]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SwapRoot

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_reflection_mem_maximal_compact : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), sR σ hU.1 a h ∈ KU σ n := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapRoot.sR_mem_KU
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

noncomputable section

namespace GlobalTheory.CompanionTheory.SwapRoot

section RootInt

variable {L : Type} [Field L]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hi : (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  simp only [partner, hi, hc, w2]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem val_cM_conj_le_one {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c).transpose) b d) ≤ 1 := by
  rw [cM_conj_apply]
  refine Valuation.map_sum_le _ fun p _ => Valuation.map_sum_le _ fun r _ => ?_
  split_ifs
  · exact hP p r
  · rw [map_zero]; exact zero_le

theorem blockM_int {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L)
    (hX : ∀ p r, Valued.v ((X - 1) p r) ≤ 1) (hY : ∀ p r, Valued.v ((Y - 1) p r) ≤ 1) :
    Formalism.UG.P.fIwasawaInt (blockM a h X Y) := by
  intro b d
  simp only [blockM, Matrix.add_apply]
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (Formalism.UG.P.fIwasawa_int_one b d)
    (val_cM_conj_le_one _ _ hX b d)) (val_cM_conj_le_one _ _ hY b d)

theorem val_unip_sub_one_le {y : L} (hy : Valued.v y ≤ 1) (p r : Fin 2) :
    Valued.v (((!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) L) - 1) p r) ≤ 1 := by
  fin_cases p <;> fin_cases r <;> simp [hy]

theorem uR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h x hx
  have hσv := hU.2.1
  have hI : Formalism.UG.P.fIwasawaInt (((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.P.fIwasawaInt (blockM a h (nU x : GL (Fin 2) L).val (partner σ (nU x)))
    rw [partner_nU]
    refine blockM_int a h _ _ (val_unip_sub_one_le hx) (val_unip_sub_one_le ?_)
    rw [Valuation.map_neg, hσv]
    exact hx
  have hK := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) hI
  have he : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) = uR σ hU.1 a h x :=
    Subtype.ext (Units.ext (Formalism.UG.P.fIwasawa_mk_val σ _ _))
  rwa [he] at hK

end RootInt

end GlobalTheory.CompanionTheory.SwapRoot

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_map_mem_compact_of_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapRoot.uR_mem_KU
end

section
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot.Unip

variable {L : Type} [Field L] {n : ℕ}

noncomputable def UT (A : Matrix (Fin n) (Fin n) L) : Prop :=
  _root_.UpperTheory.Reformulated.B.UpperTriangular.UT A

theorem UT.mul {A B : Matrix (Fin n) (Fin n) L} (hA : UT A) (hB : UT B) : UT (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hB.1 k j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Fintype.sum_eq_single i]
    · rw [hA.2, hB.2, one_mul]
    · intro k hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]

def pn (n a b : ℕ) : ℕ :=
  if b = a then a + 1 else if b = a + 1 then a else
    if b = n - 2 - a then n - 1 - a else if b = n - 1 - a then n - 2 - a else b

theorem pn_lt {a b : ℕ} (h : 2 * (a + 2) ≤ n) (hb : b < n) : pn n a b < n := by
  unfold pn; split_ifs <;> omega

theorem sR_uR_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip

end GlobalTheory.CompanionTheory.SwapRoot.Unip

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reflection_root_unipotent_shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapRoot.Unip.sR_uR_mul_unip
end

section
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot.Torus

section Mat

variable {L : Type} [Field L] {n : ℕ}

theorem blockM_mul_diag (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y X' Y' : Matrix (Fin 2) (Fin 2) L) (d d' : Fin n → L)
    (hI : ∀ p r, X p r * d (cI n a h r) = d' (cI n a h p) * X' p r)
    (hJ : ∀ p r, Y p r * d (cJ n a h r) = d' (cJ n a h p) * Y' p r)
    (hO : ∀ b, (∀ p, b ≠ cI n a h p) → (∀ p, b ≠ cJ n a h p) → d b = d' b) :
    blockM a h X Y * Matrix.diagonal d = Matrix.diagonal d' * blockM a h X' Y' := by
  ext b e
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hbI : ∃ p, b = cI n a h p
  · obtain ⟨p, rfl⟩ := hbI
    by_cases heI : ∃ r, e = cI n a h r
    · obtain ⟨r, rfl⟩ := heI
      rw [blockM_cI, blockM_cI]; exact hI p r
    · push_neg at heI
      have hb : ∀ r, cI n a h p ≠ cJ n a h r := cI_ne_cJ a h p
      rw [blockM_out a h _ _ (Or.inr heI) (Or.inl hb), blockM_out a h _ _ (Or.inr heI) (Or.inl hb)]
      have hne : cI n a h p ≠ e := fun hh => heI p hh.symm
      simp [Matrix.one_apply, hne]
  · push_neg at hbI
    by_cases hbJ : ∃ p, b = cJ n a h p
    · obtain ⟨p, rfl⟩ := hbJ
      by_cases heJ : ∃ r, e = cJ n a h r
      · obtain ⟨r, rfl⟩ := heJ
        rw [blockM_cJ, blockM_cJ]; exact hJ p r
      · push_neg at heJ
        rw [blockM_out a h _ _ (Or.inl hbI) (Or.inr heJ), blockM_out a h _ _ (Or.inl hbI) (Or.inr heJ)]
        have hne : cJ n a h p ≠ e := fun hh => heJ p hh.symm
        simp [Matrix.one_apply, hne]
    · push_neg at hbJ
      rw [blockM_out a h _ _ (Or.inl hbI) (Or.inl hbJ), blockM_out a h _ _ (Or.inl hbI) (Or.inl hbJ)]
      by_cases hbe : b = e
      · subst hbe
        simp [hO b hbI hbJ]
      · simp [Matrix.one_apply, hbe]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  show w2 L * cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) * w2 L = _
  rw [hc]
  ext p r
  fin_cases p <;> fin_cases r <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  show w2 L * cT σ (w2 L) * w2 L = _
  rw [conj_transpose_antidiag_fixed, weyl_mul_weyl, Matrix.one_mul]

theorem diag_unitary (σ : L →+* L) (t : GU σ n) (d : Fin n → L)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d) (p r : Fin n)
    (hpr : p.val + r.val + 1 = n) : σ (d p) * d r = 1 := by
  have h2 : cT σ ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n := t.2
  rw [ht] at h2
  have hc : cT σ (Matrix.diagonal d) = Matrix.diagonal (fun k => σ (d k)) := by
    ext b e
    by_cases hbe : b = e
    · subst hbe; simp [cT]
    · have : e ≠ b := fun hh => hbe hh.symm
      simp [cT, Matrix.diagonal_apply, hbe, this]
  rw [hc] at h2
  have h3 := congrFun (congrFun h2 p) r
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
  simpa [antiJ, hpr] using h3

theorem uR_mul_diag (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (t : GU σ n) (d : Fin n → L)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d)
    (hd : ∀ k, d k ≠ 0) (x : L) :
    uR σ hσ a h x * t = t * uR σ hσ a h (d (cI n a h 1) * (d (cI n a h 0))⁻¹ * x) := by
  have e0 : σ (d (cI n a h 0)) * d (cJ n a h 1) = 1 :=
    diag_unitary σ t d ht _ _ (by simp only [cI, cJ]; simp; omega)
  have e1 : σ (d (cI n a h 1)) * d (cJ n a h 0) = 1 :=
    diag_unitary σ t d ht _ _ (by simp only [cI, cJ]; simp; omega)
  have hd0 := hd (cI n a h 0)
  have hσ0 : σ (d (cI n a h 0)) ≠ 0 := by simpa using hd0
  apply Subtype.ext
  apply Units.ext
  show (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((uR σ hσ a h (d (cI n a h 1) * (d (cI n a h 0))⁻¹ * x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [ht]
  simp only [uR, rootHom_val, partner_nU]
  refine blockM_mul_diag a h _ _ _ _ d d ?_ ?_ fun _ _ _ => rfl
  · intro p r
    fin_cases p <;> fin_cases r <;> simp [nU]
    field_simp
  · intro p r
    fin_cases p <;> fin_cases r <;> simp
    have e1' : d (cJ n a h 1) = (σ (d (cI n a h 0)))⁻¹ := eq_inv_of_mul_eq_one_right e0
    rw [e1']
    field_simp
    linear_combination (-(σ x)) * e1

def dS (a : ℕ) (h : 2 * (a + 2) ≤ n) (d : Fin n → L) (k : Fin n) : L :=
  if k = cI n a h 0 then d (cI n a h 1) else if k = cI n a h 1 then d (cI n a h 0) else
  if k = cJ n a h 0 then d (cJ n a h 1) else if k = cJ n a h 1 then d (cJ n a h 0) else d k

theorem sR_conj_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (t : GU σ n) (d : Fin n → L)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d) :
    (((sR σ hσ a h * t * sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (dS a h d) := by
  have n01 : cI n a h 0 ≠ cI n a h 1 := fun e => by simpa using cI_injective a h e
  have m01 : cJ n a h 0 ≠ cJ n a h 1 := fun e => by simpa using cJ_injective a h e
  have hne := cI_ne_cJ (n := n) a h
  have key : blockM a h (w2 L) (w2 L) * Matrix.diagonal d =
      Matrix.diagonal (dS a h d) * blockM a h (w2 L) (w2 L) := by
    refine blockM_mul_diag a h _ _ _ _ d _ ?_ ?_ ?_
    · intro p r
      fin_cases p <;> fin_cases r <;> simp [w2, dS, n01, n01.symm]
    · intro p r
      fin_cases p <;> fin_cases r <;> simp [w2, dS, m01, m01.symm, (hne _ _).symm]
    · intro b h1 h2
      simp [dS, h1, h2]
  have hs : (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = blockM a h (w2 L) (w2 L) := by
    simp only [sR, rootHom_val, partner_wU]
    rfl
  show (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
  rw [ht, hs, key, Matrix.mul_assoc, blockM_mul, weyl_mul_weyl, blockM_one, Matrix.mul_one]

end Mat

theorem prod_compare {m : ℕ} (χ : Fin m → ℂˣ) (Q : ℂ) (hQ : Q ≠ 0) (N : ℤ) (i j : Fin m) (hij : j.val = i.val + 1)
    (o o' : Fin m → ℤ) (h1 : o' i = o j) (h2 : o' j = o i) (h3 : ∀ k, k ≠ i → k ≠ j → o' k = o k) :
    (∏ k : Fin m, (χ k : ℂ) ^ (o' k) * Q ^ (-(o' k) * (N - 2 * (k.val : ℤ)))) * Q ^ (2 * (o j - o i)) =
      ∏ k : Fin m, ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ))) := by
  have hne : j ≠ i := fun e => by rw [e] at hij; omega
  have split : ∀ f : Fin m → ℂ, ∏ k, f k = f i * (f j * ∏ k ∈ (Finset.univ.erase i).erase j, f k) := fun f => by
    rw [Finset.mul_prod_erase (Finset.univ.erase i) f (by simp [hne]),
      Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  rw [split, split (fun k => ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ))))]
  have hrest : ∏ k ∈ (Finset.univ.erase i).erase j, (χ k : ℂ) ^ (o' k) * Q ^ (-(o' k) * (N - 2 * (k.val : ℤ))) =
      ∏ k ∈ (Finset.univ.erase i).erase j, ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ))) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.1 hk).1
    have hki : k ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1
    rw [h3 k hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, h1, h2, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
  generalize (∏ k ∈ (Finset.univ.erase i).erase j, ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ)))) = P
  have hq : Q ^ (-(o j) * (N - 2 * (i.val : ℤ))) * Q ^ (-(o i) * (N - 2 * ((i.val + 1 : ℕ) : ℤ))) * Q ^ (2 * (o j - o i)) =
      Q ^ (-(o i) * (N - 2 * (i.val : ℤ))) * Q ^ (-(o j) * (N - 2 * ((i.val + 1 : ℕ) : ℤ))) := by
    rw [← zpow_add₀ hQ, ← zpow_add₀ hQ, ← zpow_add₀ hQ]
    congr 1
    push_cast
    ring
  linear_combination ((χ i : ℂ) ^ (o j) * (χ j : ℂ) ^ (o i) * P) * hq

section Ord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul' {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have h1 := v_eq_exp' (mul_ne_zero hx hy)
  rw [map_mul, v_eq_exp' hx, v_eq_exp' hy, ← WithZero.exp_add] at h1
  have := WithZero.exp_injective h1
  omega

end Ord

theorem torus_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) →
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj t hdiag
  have hσ := hU.1
  set d : Fin n → L := fun k => ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k with hddef
  have ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d := by
    ext b e
    by_cases hbe : b = e
    · subst hbe; simp [hddef]
    · rw [hdiag b e hbe]; simp [hbe]
  have hd : ∀ k, d k ≠ 0 := fun k hk => by
    have := diag_unitary σ t d ht (⟨n - 1 - k.val, by omega⟩ : Fin n) k (by simp; omega)
    rw [hk, mul_zero] at this
    exact zero_ne_one this
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hsv := sR_conj_val σ hσ a h t d ht
  refine ⟨d (cI n a h 1) * (d (cI n a h 0))⁻¹, mul_ne_zero (hd _) (inv_ne_zero (hd _)),
    sR σ hσ a h * t * sR σ hσ a h, ?_, ?_, ?_⟩
  · intro b e hbe
    rw [hsv, Matrix.diagonal_apply_ne _ (ne_of_gt hbe)]
  · intro x
    have hs := sR_mul_sR σ hσ a h
    rw [mul_assoc (sR σ hσ a h) (uR σ hσ a h x) t, uR_mul_diag σ hσ a h t d ht hd x,
      mul_assoc (sR σ hσ a h * t), ← mul_assoc (sR σ hσ a h) (sR σ hσ a h), hs, one_mul, ← mul_assoc (sR σ hσ a h) t]
  · have hlt : ∀ k : Fin (n / 2), k.val < n := fun k => by have := k.2; omega
    set o : Fin (n / 2) → ℤ := fun k => ordL (d ⟨k.val, hlt k⟩) with hodef
    set o' : Fin (n / 2) → ℤ := fun k => ordL (dS a h d ⟨k.val, hlt k⟩) with ho'def
    have hL : chiDeltaU q (fun k => (χ k : ℂ)) (sR σ hσ a h * t * sR σ hσ a h) =
        ∏ k : Fin (n / 2), (χ k : ℂ) ^ (o' k) * (q : ℂ) ^ (-(o' k) * (((n : ℤ) - 1) - 2 * (k.val : ℤ))) := by
      unfold chiDeltaU
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [dif_pos (hlt k), hsv, Matrix.diagonal_apply_eq]
    have hR : chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t =
        ∏ k : Fin (n / 2), (χ (Equiv.swap i j k) : ℂ) ^ (o k) * (q : ℂ) ^ (-(o k) * (((n : ℤ) - 1) - 2 * (k.val : ℤ))) := by
      unfold chiDeltaU
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [dif_pos (hlt k)]
      rfl
    have hci : (⟨i.val, hlt i⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI, hi])
    have hcj : (⟨j.val, hlt j⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI, hj])
    have n01 : cI n a h 0 ≠ cI n a h 1 := fun e => by simpa using cI_injective a h e
    have hoi : o i = ordL (d (cI n a h 0)) := by simp only [hodef, hci]
    have hoj : o j = ordL (d (cI n a h 1)) := by simp only [hodef, hcj]
    have hc : ordL (d (cI n a h 1) * (d (cI n a h 0))⁻¹) = o j - o i := by
      rw [ordL_mul' (hd _) (inv_ne_zero (hd _)), ordL_inv' (hd _), hoi, hoj]
      ring
    rw [hL, hR, hc]
    refine prod_compare χ _ hq _ i j (by omega) o o' ?_ ?_ ?_
    · simp only [ho'def, hci, hoj]
      simp [dS]
    · simp only [ho'def, hcj, hoi]
      simp [dS, n01.symm]
    · intro k hki hkj
      have hkn := k.2
      have e1 : ∀ p, (⟨k.val, hlt k⟩ : Fin n) ≠ cI n a h p := fun p e => by
        have := congrArg Fin.val e
        simp only [cI] at this
        have hp := p.2
        have hp' : p = 0 ∨ p = 1 := by omega
        rcases hp' with rfl | rfl
        · exact hki (Fin.ext (by simp at this; omega))
        · exact hkj (Fin.ext (by simp at this; omega))
      have e2 : ∀ p, (⟨k.val, hlt k⟩ : Fin n) ≠ cJ n a h p := fun p e => by
        have := congrArg Fin.val e
        simp only [cJ] at this
        have hp := p.2
        omega
      simp only [ho'def, hodef]
      simp [dS, e1, e2]

end GlobalTheory.CompanionTheory.SwapRoot.Torus

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reflection_root_diagonal_conj : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) →
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapRoot.Torus.torus_step
end

section
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

section Lem
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem step_exists_int [CompleteSpace L] (hU : IsUnramInv ϖ σ q) (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ * (q : ℝ) ^ 2 < 1) :
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) :=
  GlobalTheory.T.exists_admissible_linear_functional L ϖ σ q hU w hw0 hw

theorem step_uR_continuous (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Continuous (uR σ hU.1 a h : L → GU σ n) :=
  GlobalTheory.T.continuous_unitary_root_map L ϖ σ q n hU a h

theorem step_factor (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (x : L) (hx : x ≠ 0) :
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) :=
  GlobalTheory.T.simple_reflection_root_borel_decomp L ϖ σ q n hU a h χ i j hi hj x hx

theorem step_sR_mem_KU (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) : sR σ hU.1 a h ∈ KU σ n :=
  GlobalTheory.T.simple_reflection_mem_maximal_compact L ϖ σ q n hU a h

theorem step_uR_mem_KU (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : Valued.v x ≤ 1) :
    uR σ hU.1 a h x ∈ KU σ n :=
  GlobalTheory.T.root_map_mem_compact_of_integral L ϖ σ q n hU a h x hx

theorem step_unip_shift (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n) (hv : IsUnipU v) :
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) :=
  GlobalTheory.T.reflection_root_unipotent_shift L σ n hσ a h v hv

theorem step_torus_shift (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (t : GU σ n) (ht : IsDiagM (t : GL (Fin n) L)) :
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t :=
  GlobalTheory.T.reflection_root_diagonal_conj L ϖ σ q n hU a h χ i j hi hj t ht

end Lem

section Main
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem step_borel_shift (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (b : GU σ n) (hb : IsBorelU b) :
    ∃ (c y : L) (C : ℂ), c ≠ 0 ∧
      (∀ x : L, ∃ b' : GU σ n, IsBorelU b' ∧ chiDeltaU q (fun k => (χ k : ℂ)) b' = C ∧
        sR σ hU.1 a h * uR σ hU.1 a h x * b = b' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x + y))) ∧
      C * (q : ℂ) ^ (2 * ordL c) = chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) b := by
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (show q ≠ 0 by omega)
  obtain ⟨t, v, ht, hv, rfl⟩ := GlobalTheory.CompanionTheory.BorelSplit.borelSplitU L σ n hU.1 b hb
  have hv' : IsUnipU v := ⟨fun p r hpr => hv.1 p r hpr, hv.2⟩
  obtain ⟨y, hy⟩ := step_unip_shift hU.1 a h v hv'
  obtain ⟨c, hc, t', ht', h1, h2⟩ := step_torus_shift hU a h χ i j hi hj t ht
  have ht2 : IsBorelU t := fun p r hpr => ht p r (ne_of_gt hpr)
  refine ⟨c, y, chiDeltaU q (fun k => (χ k : ℂ)) t', hc, fun x => ?_, ?_⟩
  · obtain ⟨b0, hb0, e⟩ := hy (c * x)
    refine ⟨t' * b0, borel_mul _ _ ht' hb0.1, ?_, ?_⟩
    · rw [chi_borel_mul hq χ _ _ ht' hb0.1, chi_unip _ _ hb0, mul_one]
    · rw [← mul_assoc, h1 x, mul_assoc, mul_assoc, ← mul_assoc _ _ v, e, mul_assoc]
  · rw [h2, chi_borel_mul hq (χ ∘ Equiv.swap i j) t v ht2 hv'.1, chi_unip _ v hv', mul_one]

theorem step_stab_adm (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2))
    (hi : i.val = a) (hj : j.val = a + 1) (φ : GU σ n → ℂ) (hφ : φ ∈ psSpaceU σ q χ) (S : Set (GU σ n)) (hS : IsOpen S)
    (h1 : (1 : GU σ n) ∈ S) (hinv : ∀ s ∈ S, ∀ g, φ (g * s) = φ g) (g : GU σ n) :
    IsAdm (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) (fun x => φ (sR σ hU.1 a h * uR σ hU.1 a h x * g)) := by
  have hc := step_uR_continuous (L := L) (n := n) hU a h
  set s := sR σ hU.1 a h
  set u : L → GU σ n := uR σ hU.1 a h
  have hu0 : u 0 = 1 := by
    have := uR_add σ hU.1 a h (0 : L) 0
    simpa using this
  have hss : s * s = 1 := sR_mul_sR σ hU.1 a h
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hA : Continuous fun y : L => g⁻¹ * u (y - x) * g := by fun_prop
    have hA1 : (fun y : L => g⁻¹ * u (y - x) * g) x = 1 := by simp [hu0]
    have : ∀ᶠ y in nhds x, g⁻¹ * u (y - x) * g ∈ S :=
      hA.continuousAt.eventually_mem (hS.mem_nhds (by have h2 := h1; rw [← hA1] at h2; exact h2))
    filter_upwards [this] with y hy
    have e : s * u y * g = s * u x * g * (g⁻¹ * u (y - x) * g) := by
      have : u y = u x * u (y - x) := by
        rw [← uR_add]; congr 1; ring
      rw [this]; group
    rw [e, hinv _ hy]
  · have hB : Continuous fun y : L => g⁻¹ * (s * u y * s) * g := by fun_prop
    have hB1 : (fun y : L => g⁻¹ * (s * u y * s) * g) 0 = 1 := by
      simp [hu0, hss]
    have hB2 : (fun y : L => g⁻¹ * (s * u y * s) * g) ⁻¹' S ∈ nhds (0 : L) :=
      hB.continuousAt.preimage_mem_nhds (hS.mem_nhds (by have h2 := h1; rw [← hB1] at h2; exact h2))
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hB2
    have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc'
    refine ⟨WithZero.log c - 1, φ g, fun x hx hR => ?_⟩
    have hv : Valued.v x⁻¹ < c := by
      rw [v_eq_exp' (inv_ne_zero hx), ordL_inv' hx, neg_neg, ← WithZero.exp_log hne]
      exact WithZero.exp_lt_exp.2 (by omega)
    have hmem : g⁻¹ * (s * u x⁻¹ * s) * g ∈ S :=
      hγ (by simpa [Valuation.restrict_lt_iff_lt_embedding, sub_zero] using hv)
    obtain ⟨b, hb, hbc, e⟩ := step_factor hU a h χ i j hi hj x hx
    have e1 : s * u x * g = b * (g * (g⁻¹ * (s * u x⁻¹ * s) * g)) := by
      have : s * u x = b * (s * u x⁻¹ * s) := e
      rw [this]; group
    show φ (s * u x * g) = _
    rw [e1, hφ b _ hb, hinv _ hmem, hbc, mul_comm]

end Main

theorem swapStepU : PositivityTheory.SphericalProduct.SwapStepU := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hadm hirr hsph χ i j hij hz f hinj hf
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (0 : ℝ) < (q : ℝ) ^ 2 := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hj2 := j.2
  have h : 2 * (i.val + 2) ≤ n := by omega
  set w : ℂ := ((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2 with hwdef
  have hw0 : w ≠ 0 := div_ne_zero (div_ne_zero (χ i).ne_zero (χ j).ne_zero) (pow_ne_zero _ hq)
  have hw : ‖w‖ * (q : ℝ) ^ 2 < 1 := by
    rw [hwdef, norm_div, norm_pow, Complex.norm_natCast, div_mul_cancel₀ _ hqr.ne']
    exact hz
  obtain ⟨I, Iadd, Ismul, Itr, Isc, Isph, Ival⟩ := step_exists_int (L := L) hU w hw0 hw
  set s := sR σ hU.1 i.val h with hs
  set u : L → GU σ n := uR σ hU.1 i.val h with hu
  have hr : ∀ (k : GU σ n) (v : V) (g' : GU σ n), (f (ρ k v)).1 g' = (f v).1 (g' * k) := fun k v g' => by
    rw [hf]; rfl
  have hAdm : ∀ (v : V) (g : GU σ n), IsAdm w (fun x => (f v).1 (s * u x * g)) := fun v g =>
    step_stab_adm hU i.val h χ i j rfl hij.symm (f v).1 (f v).2 {k | ρ k v = v} (hadm.1 v) (by simp)
      (fun k hk g' => by rw [← hr, show ρ k v = v from hk]) g
  let T : V → (GU σ n → ℂ) := fun v g => I (fun x => (f v).1 (s * u x * g))
  have Tmem : ∀ v, T v ∈ psSpaceU σ q (χ ∘ Equiv.swap i j) := by
    intro v b g hb
    obtain ⟨c, y, C, hc, hrel, hC⟩ := step_borel_shift hU i.val h χ i j rfl hij.symm b hb
    have hF := hAdm v g
    have hG := (Itr _ y hF).1
    have hH := (Isc _ c hG hc).1
    have e : (fun x => (f v).1 (s * u x * (b * g))) =
        C • (fun x => (fun x' => (fun x'' => (f v).1 (s * u x'' * g)) (x' + y)) (c * x)) := by
      funext x
      obtain ⟨b', hb', hb'C, hx⟩ := hrel x
      have e2 := (f v).2 b' (s * u (c * x + y) * g) hb'
      show (f v).1 (s * u x * (b * g)) = C * (f v).1 (s * u (c * x + y) * g)
      have e3 : s * u x * b = b' * (s * u (c * x + y)) := hx
      rw [← mul_assoc, e3, mul_assoc, ← hb'C]
      exact e2
    show I (fun x => (f v).1 (s * u x * (b * g))) = _ * I (fun x => (f v).1 (s * u x * g))
    rw [e, Ismul C _ hH, (Isc _ c hG hc).2, (Itr _ y hF).2, ← hC]
    ring
  let f' : V →ₗ[ℂ] psSpaceU σ q (χ ∘ Equiv.swap i j) :=
    { toFun := fun v => ⟨T v, Tmem v⟩
      map_add' := fun v v' => by
        refine Subtype.ext (funext fun g => ?_)
        show I (fun x => (f (v + v')).1 (s * u x * g)) = I _ + I _
        rw [← Iadd _ _ (hAdm v g) (hAdm v' g)]
        congr 1
        funext x
        simp [map_add]
      map_smul' := fun c v => by
        refine Subtype.ext (funext fun g => ?_)
        show I (fun x => (f (c • v)).1 (s * u x * g)) = c * I _
        rw [← Ismul c _ (hAdm v g)]
        congr 1
        funext x
        simp [map_smul] }
  have hf' : ∀ (g : GU σ n) (v : V), f' (ρ g v) = psFunU σ q (χ ∘ Equiv.swap i j) g (f' v) := by
    intro g v
    refine Subtype.ext (funext fun g' => ?_)
    show I (fun x => (f (ρ g v)).1 (s * u x * g')) = I (fun x => (f v).1 (s * u x * (g' * g)))
    congr 1
    funext x
    rw [hr, mul_assoc]
  refine ⟨f', ?_, hf'⟩

  obtain ⟨v₀, hv₀, hv₀0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hfix : ∀ k ∈ KU σ n, ρ k v₀ = v₀ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hv₀ k hk
  have hK : ∀ (g : GU σ n), ∀ k ∈ KU σ n, (f v₀).1 (g * k) = (f v₀).1 g := fun g k hk => by
    rw [← hr, hfix k hk]
  have hone : (f v₀).1 1 ≠ 0 := by
    intro h0
    refine hv₀0 (hinj (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g
    have e := (f v₀).2 b k hb
    have e2 := hK 1 k hk
    rw [one_mul] at e2
    rw [map_zero]
    show (f v₀).1 (b * k) = 0
    rw [e, e2, h0, mul_zero]
  have hsph' : (fun x => (f v₀).1 (s * u x * 1)) = ((f v₀).1 1) • sphFn w := by
    funext x
    show _ = (f v₀).1 1 * sphFn w x
    rw [mul_one]
    by_cases hx : Valued.v x ≤ 1
    · have hk : s * u x ∈ KU σ n := mul_mem (step_sR_mem_KU hU _ h) (step_uR_mem_KU hU _ h x hx)
      have := hK 1 _ hk
      rw [one_mul] at this
      rw [this, sphFn, if_pos hx, mul_one]
    · have hx0 : x ≠ 0 := fun e => hx (by simp [e])
      obtain ⟨b, hb, hbc, e⟩ := step_factor hU i.val h χ i j rfl hij.symm x hx0
      have hx1 : Valued.v x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx))
      have hk : s * u x⁻¹ * s ∈ KU σ n :=
        mul_mem (mul_mem (step_sR_mem_KU hU _ h) (step_uR_mem_KU hU _ h _ hx1)) (step_sR_mem_KU hU _ h)
      have e1 : s * u x = b * (s * u x⁻¹ * s) := e
      have e2 := hK 1 _ hk
      rw [one_mul] at e2
      rw [e1, (f v₀).2 b _ hb, e2, hbc, sphFn, if_neg hx, mul_comm]
  have hne : f' v₀ ≠ 0 := by
    intro h0
    have e : T v₀ 1 = 0 := congrFun (congrArg Subtype.val h0) 1
    have e2 : T v₀ 1 = (f v₀).1 1 * ((1 - w) / (1 - w * (q : ℂ) ^ 2)) := by
      show I (fun x => (f v₀).1 (s * u x * 1)) = _
      rw [hsph', Ismul _ _ Isph, Ival]
    rw [e2] at e
    have hw1 : ‖w‖ < 1 := by
      have h1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
        nlinarith
      nlinarith [norm_nonneg w]
    have n1 : (1 - w) ≠ 0 := fun e0 => by
      have : w = 1 := by linear_combination -e0
      rw [this] at hw1
      simp at hw1
    have n2 : (1 - w * (q : ℂ) ^ 2) ≠ 0 := fun e0 => by
      have e3 : w * (q : ℂ) ^ 2 = 1 := by linear_combination -e0
      have : ‖w * (q : ℂ) ^ 2‖ = 1 := by rw [e3]; simp
      rw [norm_mul, norm_pow, Complex.norm_natCast] at this
      linarith
    exact mul_ne_zero hone (div_ne_zero n1 n2) e
  let F := f'.intertwiningMap_of_isIntertwiningMap ρ (psFunU σ q (χ ∘ Equiv.swap i j)) hf'
  haveI := hirr
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
  · exact hi
  · exact absurd (DFunLike.congr_fun hz v₀) hne

end GlobalTheory.CompanionTheory.SwapRoot

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_swap_reduction : PositivityTheory.SphericalProduct.SwapStepU := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SwapRoot.swapStepU
end
