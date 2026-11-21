import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fdeg

open Formalism.QuantumDeterminants

theorem integral_normSq_coef (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ) (μG : Measure (Mt k r)) (hw : ‖w‖ = 1)
    (hF : IsFdegB μG σ d) :
    ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
  obtain ⟨_, hS⟩ := hF
  have h1 := (hS w w w w).2
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  rw [hww] at h1
  have hfun : (fun g : Mt k r => ⟪w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ) =
      fun g => ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast; rfl
  rw [hfun, integral_complex_ofReal] at h1
  have h2 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2

theorem fdegH_eq : FdegHEqStatement := by
  intro k r H _ _ σ w d μG hw hF
  unfold Formalism.MainNotions.S.fdegH
  rw [integral_normSq_coef k r H σ w d μG hw hF, hw]
  have hd : d ≠ 0 := ne_of_gt hF.1
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fdeg
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core

open Formalism.QuantumDeterminants

section hpk

variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  have key : ∀ (c : ℕ) (hc : c < 2 * r + k + 1) (a : ℂ),
      ∑ j : Fin (2 * r + k + 1), (if j.val = c then a else 0) * v j = a * v ⟨c, hc⟩ := by
    intro c hc a
    rw [Finset.sum_eq_single ⟨c, hc⟩]
    · simp
    · intro b _ hb
      have hbc : b.val ≠ c := fun h => hb (Fin.ext h)
      simp [hbc]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hi := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [hpk_out k r h]
    rw [key _ (by omega), one_mul]
  · rw [if_neg h]
    simp only [hpk_mid k r h]
    rw [key i.val hi]
    split_ifs <;> simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h' : (2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := by omega
    rw [hpk_mulVec, if_pos h, hpk_mulVec, if_pos h']
    congr 1
    ext
    simp only
    omega
  · rw [hpk_mulVec, if_neg h, hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

end hpk

theorem inv_mul_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := hpk_sq k r

theorem mul_inv_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h := inv_mul_UH k r hg
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h)

theorem mul_mem_UH (k r : ℕ) {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem one_mem_UH (k r : ℕ) : (1 : Mat k r) ∈ UH (Hpk k r) := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem inv_mem_UH (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have e := mul_inv_UH k r hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e]; simp


theorem coef_mul (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ)
    (y g : Mat k r) (hy : y ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    ⟪w, σ (y * g) w⟫_ℂ = ⟪σ y⁻¹ w, σ g w⟫_ℂ := by
  have hyi := inv_mem_UH k r y hy
  have hmul := hσ.1.2
  have h1 : σ y (σ y⁻¹ w) = w := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul y hy y⁻¹ hyi, mul_inv_UH k r hy, hσ.1.1]
    rfl
  let L : H →ₗᵢ[ℂ] H := ⟨(σ y).toLinearMap, hσ.2.1 y hy⟩
  have hL := L.inner_map_map (σ y⁻¹ w) (σ g w)
  rw [hmul y hy g hg, ContinuousLinearMap.comp_apply]
  have e : ⟪w, σ y (σ g w)⟫_ℂ = ⟪σ y (σ y⁻¹ w), σ y (σ g w)⟫_ℂ := by rw [h1]
  rw [e]
  exact hL



end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec

open Formalism.QuantumDeterminants

theorem one_le_gN (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g :=
  DecA.one_le_gN' hg

theorem pair_bound (k r : ℕ) (a : ℝ) (ha : 0 ≤ a) (y g : Mat k r) (hy : y ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.gN g ^ (-a) * Formalism.FourierDecayAlt.B.gN (y * g) ^ (-a) ≤
      Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * (Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) + Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2))) := by
  have hA := DecA.one_le_gN' hg
  have hB := DecA.one_le_gN' (DecA.mul_mem hy hg)
  have hY := DecA.one_le_gN' hy
  have hYBA := DecA.gN_le_mul (y := y) hg
  have hAh : 0 ≤ Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2)) := Real.rpow_nonneg (by linarith) _
  have hYq : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (Formalism.FourierDecayAlt.B.gN g) (Formalism.FourierDecayAlt.B.gN (y * g)) with h | h
  · calc _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * Formalism.FourierDecayAlt.B.gN (y * g) ^ (-(a / 2)) :=
          DecA.pb_real a _ _ _ ha hA hB (by linarith) hYBA h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hYq
  · have := DecA.pb_real a (Formalism.FourierDecayAlt.B.gN (y * g)) (Formalism.FourierDecayAlt.B.gN g) (Formalism.FourierDecayAlt.B.gN y) ha hB hA (by linarith)
      (by rw [mul_comm]; exact hYBA) h
    rw [mul_comm] at this
    calc _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (-(a / 4)) * Formalism.FourierDecayAlt.B.gN g ^ (-(a / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hYq

theorem of_cont (k r : ℕ) : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) :=
  continuous_matrix fun i j => by
    simp only [Matrix.of_apply]; exact (continuous_apply j).comp (continuous_apply i)

theorem gN_cont (k r : ℕ) : Continuous (fun M : Mat k r => Formalism.FourierDecayAlt.B.gN M) := by
  unfold Formalism.FourierDecayAlt.B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

theorem lmulM_cont {k r : ℕ} (s : Mat k r) : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.QuantumDeterminants.lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))


theorem UW_inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := DecA.inv_mul hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨DecA.inv_mem hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem UH_closed (k r : ℕ) : IsClosed (UH (Hpk k r) : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem UW_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
      {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z}) := by
    ext g; simp only [UWset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact (UH_closed k r).inter ((isClosed_iInter fun a =>
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)).inter
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const))

theorem psiGen_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (fun M : Mat k r => Formalism.MainNotions.S.psiGen k r z c M) := by
  have hell : ∀ a : Fin r, Continuous (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) := by
    intro a
    by_cases h : a.val + 1 < r
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) =
          fun M : Mat k r => M (eI k r a) (eI k r ⟨a.val + 1, h⟩) :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dif_pos h]
      rw [e]; exact continuous_id.matrix_elem _ _
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) = fun M : Mat k r => ∑ j, M (eI k r a) j * z j :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dif_neg h]; rfl
      rw [e]; exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (hell a)))))

theorem product_bound_of_factor_bounds (D M1 M2 X P Q C : ℝ) (hD : 0 ≤ D) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hX : 0 ≤ X)
    (h1 : M1 ≤ C * P) (h2 : M2 ≤ C * Q) : D * M1 * (M2 * X) ≤ D * C ^ 2 * X * (P * Q) := by
  have := mul_le_mul h1 h2 hM2 (hM1.trans h1)
  calc D * M1 * (M2 * X) = (D * X) * (M1 * M2) := by ring
    _ ≤ (D * X) * ((C * P) * (C * Q)) := mul_le_mul_of_nonneg_left this (mul_nonneg hD hX)
    _ = _ := by ring

def Sg3 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x₀ x : Mat k r) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ UH (Hpk k r) ∧ (Matrix.of q.2.1 ∈ UWset k r z ∧
    x₀⁻¹ * (Matrix.of q.2.1 * Matrix.of q.2.2 * x) * Matrix.of q.1 ∈ UH (Hpk k r))}



end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec
end
end
