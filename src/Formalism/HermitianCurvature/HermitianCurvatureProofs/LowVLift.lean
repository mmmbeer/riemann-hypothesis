import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem castM_inv' {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h
  simp [D.castM]

private theorem castV_rfl' {a : ℕ} (h : a = a) (v : Fin (2 * a + k + 1) → ℂ) : D.castV h v = v := by
  funext i
  rfl

theorem psi_castM {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h v) c (D.castM h g) = psi k a v c g := by
  subst h
  simp [D.castM, castV_rfl']


theorem castM_N {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM h g ∈ Nset k b := by
  subst h
  simpa [D.castM] using hg

theorem castM_UWv {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} {g : B.Mat k a} (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by
  subst h
  simpa [D.castM, castV_rfl'] using hg


theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by
  subst h
  have e : (D.castM (k := k) (rfl : a = a)) = fun g => g := by
    funext g
    simp [D.castM]
  rw [e]
  exact continuous_id

theorem inWb_castV {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} (hv : inWb k a v) : inWb k b (D.castV h v) := by
  subst h
  rw [castV_rfl']
  exact hv

theorem uw_closedSubgroup (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B2.IsClosedSubgroup (UWset k r z) :=
  ⟨Dx2.Rad.one_UW z, fun _ ha _ hb => WeylGroupFacts.uw_mul ha hb, fun _ ha => WeylGroupFacts.uw_inv ha,
    fun _ ha => HermitianFormFactor.UH_unit (Ux3.hpk_det k r) ha.1, B6.isClosed_UWset k r z⟩

def levA (ρ : ℕ) (x : Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)))

private theorem continuous_ιLev_apply (ρ : ℕ) (p q : Fin (2 * (1 + ρ) + k + 1)) :
    Continuous fun x : Mt k ρ => ιLev k 1 ρ (Matrix.of x) p q := by
  simp only [Formalism.QuantumDeterminants.ιLev]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * ρ + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * ρ + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_pos hp, dif_neg hq]
      exact continuous_const
  · simp only [dif_neg hp]
    exact continuous_const

theorem levA_cont (ρ : ℕ) : Continuous (levA (k := k) ρ) := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [levA, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact continuous_ιLev_apply ρ _ _

private theorem castM_mul_hermitian_curvature {a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h
  simp [D.castM]

theorem lev_mul' (ρ : ℕ) (a b : B.Mat k ρ) :
    D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a * b)) =
      D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ b) := by
  have hL := PI.QnLevBasicsW.level_group_homomorphism
  unfold Formalism.QuantumDeterminants.LevHom at hL
  rw [(hL k 1 ρ).2 a b]
  exact castM_mul_hermitian_curvature _ _ _

theorem castM_back {a b : ℕ} (h : a = b) (g : B.Mat k b) : D.castM h (D.castM h.symm g) = g := by
  subst h
  simp [D.castM]

theorem castV_back {a b : ℕ} (h : a = b) (v : Fin (2 * b + k + 1) → ℂ) : D.castV h (D.castV h.symm v) = v := by
  subst h
  rw [castV_rfl', castV_rfl']

theorem levA_apply (ρ : ℕ) (x : Mt k ρ) :
    (Matrix.of (levA ρ x) : B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) := rfl

theorem lev_onto {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ) (a : B.Mat k (ρ + 1))
    (ha : a ∈ UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) :
    ∃ a0 ∈ UWset k ρ z0, D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) = a := by
  have ha' : D.castM (Nat.add_comm 1 ρ).symm a ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := by
    have := castM_UWv (Nat.add_comm 1 ρ).symm ha
    have e : D.castV (Nat.add_comm 1 ρ).symm (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) = liftVec k 1 ρ z0 := by
      have := castV_back (k := k) (Nat.add_comm 1 ρ).symm (liftVec k 1 ρ z0)
      simpa using this
    rwa [e] at this
  obtain ⟨y, hy, hy'⟩ := JCTx5.uw_onto (k := k) (i := 1) (r' := ρ) z0 _ ha'
  exact ⟨y, hy, by rw [hy']; exact castM_back _ a⟩

theorem muW_lev {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ)
    (μ0 : Measure (Mt k ρ)) (μ1 : Measure (Mt k (ρ + 1)))
    (h0 : B.IsHaarOn (UWset k ρ z0) μ0)
    (h1 : B.IsHaarOn (UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) μ1)
    (n0 : μ0 Set.univ = 1) (n1 : μ1 Set.univ = 1) :
    μ1 = μ0.map (levA ρ) := by
  set U1 := UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) with hU1
  have hm : Measurable (levA (k := k) ρ) := (levA_cont ρ).measurable
  have hmem : ∀ y ∈ UWset k ρ z0, (Matrix.of (levA ρ y) : B.Mat k (ρ + 1)) ∈ U1 := fun y hy =>
    castM_UWv _ (Dx2.Tower.lev_UW 1 ρ z0 (Matrix.of y) hy)
  set ν := μ0.map (levA (k := k) ρ) with hν
  have hνu : ν Set.univ = 1 := by rw [hν, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, n0]
  have hconc : ν U1ᶜ = 0 := by
    have hcl : IsClosed {x : Mt k (ρ + 1) | Matrix.of x ∈ U1} := B7.isClosed_UW _
    show ν {x : Mt k (ρ + 1) | Matrix.of x ∈ U1}ᶜ = 0
    rw [hν, Measure.map_apply hm hcl.measurableSet.compl]
    apply measure_mono_null _ h0.conc
    intro y hy hyU
    exact hy (hmem y hyU)
  have hleft : ∀ a ∈ U1, ν.map (lmulM a) = ν := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := lev_onto z0 a ha
    have hl : Measurable (lmulM (k := k) (r := ρ + 1) (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0))) :=
      B2x5.measurable_lmulM _
    have hl0 : Measurable (lmulM (k := k) (r := ρ) a0) := B2x5.measurable_lmulM _
    have e : lmulM (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0)) ∘ levA (k := k) ρ = levA ρ ∘ lmulM a0 := by
      funext x
      show (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) :
          B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a0 * Matrix.of x))
      rw [lev_mul']
    rw [hν, Measure.map_map hl hm, e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  have hfin : ∀ K : Set (Mt k (ρ + 1)), IsCompact K → ν K < ⊤ := by
    intro K _
    calc ν K ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hνu
      _ < ⊤ := ENNReal.one_lt_top
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (ρ + 1) U1 μ1 ν (uw_closedSubgroup (ρ + 1) _) h1 hconc hleft hfin
  have hc1 : (c : ENNReal) = 1 := by
    have := congrArg (fun μ : Measure (Mt k (ρ + 1)) => μ Set.univ) hc
    simp only [Measure.smul_apply, n1, hνu, smul_eq_mul, mul_one, ENNReal.smul_def] at this
    exact this.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hc, hc1', one_smul]

def Qm (ρ : ℕ) (p : Mt k (1 + ρ) × Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (Matrix.of p.1 * ιLev k 1 ρ (Matrix.of p.2)))

theorem Qm_cont (ρ : ℕ) : Continuous (Qm (k := k) ρ) := by
  have hI : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => ιLev k 1 ρ (Matrix.of p.2) :=
    continuous_pi fun a => continuous_pi fun b => (continuous_ιLev_apply ρ a b).comp continuous_snd
  have h1 : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => (Matrix.of p.1 : B.Mat k (1 + ρ)) := continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Qm, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply _).comp ((continuous_apply _).comp (h1.matrix_mul hI))

theorem sf_heis (ρ : ℕ) : SigmaFinite (B2.μHeis k ρ) :=
  Dx2.MN.sigma_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)

theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := Dx2.MN.sigma_of_haar (Dx2.MN.haar ρ)

theorem muN_succ' (ρ : ℕ) : D.muN k (ρ + 1) = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by
  have := sf_heis (k := k) ρ
  have := sf_muN (k := k) ρ
  have hl : Measurable (B2.levM k ρ) := (B2x2.levM_cont k ρ).measurable
  have hmu : Measurable (B2.mulM : Mt k (1 + ρ) × Mt k (1 + ρ) → Mt k (1 + ρ)) := B2x2.mulM_cont.measurable
  have hc : Measurable (Dx2.MN.castMt (k := k) (Nat.add_comm 1 ρ)) := (Dx2.MN.castMt_cont _).measurable
  have e1 : (B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ)) =
      ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Prod.map id (B2.levM k ρ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hl, Measure.map_id]
  rw [Dx2.MN.muN_succ, e1, Measure.map_map hmu (measurable_id.prodMap hl), Measure.map_map hc (hmu.comp (measurable_id.prodMap hl))]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

private theorem iotaLev_one_eq_blk3 (ρ : ℕ) (g : B.Mat k ρ) :
    ιLev k 1 ρ g = U.blk3 (j := 1) 1 0 0 0 g 0 0 0 1 := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective q
  rw [Ux3.block3_apply]
  have vX : ∀ x : Fin 1, ((U.eB k 1 ρ) (Sum.inl (Sum.inl x))).val = 0 := fun x => by
    simp [U.eB]
  have vV : ∀ v : Fin (2 * ρ + k + 1), ((U.eB k 1 ρ) (Sum.inl (Sum.inr v))).val = 1 + v.val := fun v => by
    simp [U.eB]
  have vS : ∀ b : Fin 1, ((U.eB k 1 ρ) (Sum.inr b)).val = 2 * ρ + k + 2 := fun b => by
    simp [U.eB] <;> omega
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp only [Formalism.QuantumDeterminants.ιLev, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, vX, vV, vS, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | (congr <;> (try apply Fin.ext) <;> simp [vV])

theorem lev_mMap (ρ : ℕ) (g g' : B.Mat k ρ) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    ιLev k 1 ρ g * U.mMap k 1 ρ Z γ * ιLev k 1 ρ g' = U.mMap k 1 ρ Z (g * γ * g') := by
  rw [iotaLev_one_eq_blk3, iotaLev_one_eq_blk3]
  simp only [U.mMap]
  rw [Ux5.block3_mul_blocks, Ux5.block3_mul_blocks]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem sgs_alg (ρ : ℕ) (h0 y h0' y' : B.Mat k ρ) (hh0 : IsUnit h0.det) (hy : IsUnit y.det) (hh0' : IsUnit h0'.det)
    (hy' : IsUnit y'.det) (a a' : B.Mat k (1 + ρ)) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    (ιLev k 1 ρ h0)⁻¹ * (a * ιLev k 1 ρ y)⁻¹ * U.mMap k 1 ρ Z γ * (a' * ιLev k 1 ρ y') * ιLev k 1 ρ h0' =
      ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0))⁻¹ *
        U.mMap k 1 ρ Z ((y * h0)⁻¹ * γ * (y' * h0')) * ((ιLev k 1 ρ (y' * h0'))⁻¹ * a' * ιLev k 1 ρ (y' * h0')) := by
  have hL0 := PI.QnLevBasicsW.level_group_homomorphism
  have hL := hL0
  unfold Formalism.QuantumDeterminants.LevHom at hL
  have ιmul : ∀ g h : B.Mat k ρ, ιLev k 1 ρ (g * h) = ιLev k 1 ρ g * ιLev k 1 ρ h := (hL k 1 ρ).2
  have ιone : ιLev k 1 ρ (1 : B.Mat k ρ) = 1 := (hL k 1 ρ).1
  have ιinv : ∀ g : B.Mat k ρ, IsUnit g.det → (ιLev k 1 ρ g)⁻¹ = ιLev k 1 ρ g⁻¹ :=
    fun g hg => PIQnLT.ιLev_inv hL0 g hg
  have hW : IsUnit (y * h0).det := by
    rw [Matrix.det_mul]
    exact hy.mul hh0
  have hW' : IsUnit (y' * h0').det := by
    rw [Matrix.det_mul]
    exact hy'.mul hh0'
  have hW1 : ∀ X, ιLev k 1 ρ (y * h0) * (ιLev k 1 ρ (y * h0)⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW, ιone, one_mul]
  have hW2 : ∀ X, ιLev k 1 ρ (y' * h0') * (ιLev k 1 ρ (y' * h0')⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW', ιone, one_mul]
  have hLw : ∀ X, ιLev k 1 ρ h0⁻¹ * (ιLev k 1 ρ y⁻¹ * X) = ιLev k 1 ρ (y * h0)⁻¹ * X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_inv_rev]
  have hRw : ιLev k 1 ρ y' * ιLev k 1 ρ h0' = ιLev k 1 ρ (y' * h0') := (ιmul _ _).symm
  rw [Matrix.mul_inv_rev a, ιinv _ hh0, ιinv _ hy, ιinv _ hW, ιinv _ hW', ← lev_mMap]
  rw [Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹ * a) (ιLev k 1 ρ (y * h0)),
    Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹) a, ιinv _ hW, ιinv _ (Matrix.isUnit_nonsing_inv_det _ hW),
    Matrix.nonsing_inv_nonsing_inv _ hW]
  simp only [mul_assoc]
  rw [hLw, hRw, hW1, hW2]

theorem psi_Qm (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : Mt k (1 + ρ)} {y : Mt k ρ}
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (hy : Matrix.of y ∈ Nset k ρ) :
    psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (D.castM (Nat.add_comm 1 ρ) (Matrix.of a)) *
        psi k ρ z0 cStd (Matrix.of y) := by
  show psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd
      (D.castM (Nat.add_comm 1 ρ) (Matrix.of a * ιLev k 1 ρ (Matrix.of y))) = _
  rw [psi_castM, psi_castM, Qx4.psi_mul (Qx4.lift_inWb hz0) ha (B2x6.lev_n hy), Qx4.psi_lev]

theorem psi_conjLev (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : B.Mat k (1 + ρ)}
    {y h0 : B.Mat k ρ} (ha : a ∈ Nset k (1 + ρ)) (hy : y ∈ Nset k ρ) (hh0 : h0 ∈ UWset k ρ z0) :
    psi k (1 + ρ) (liftVec k 1 ρ z0) cStd ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0)) =
      psi k (1 + ρ) (liftVec k 1 ρ z0) cStd a := by
  have hz1 := Qx4.lift_inWb hz0
  have hyN : ιLev k 1 ρ y ∈ Nset k (1 + ρ) := B2x6.lev_n hy
  have hhW : ιLev k 1 ρ h0 ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := Dx2.Tower.lev_UW 1 ρ z0 h0 hh0
  have hu : (ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y ∈ Nset k (1 + ρ) :=
    WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hyN) ha) hyN
  have e : (ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0) =
      (ιLev k 1 ρ h0)⁻¹ * ((ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y) * ιLev k 1 ρ h0 := by
    rw [Dx2.Tower.lev_mul, Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  rw [e, Qx4.psi_conjW' hz1 hhW hu, Qx4.psi_conjN' hz1 hyN ha]


theorem heis_meas_conj_inv (ρ : ℕ) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    (B2.μHeis k ρ).map (conjM ((ιLev k 1 ρ g)⁻¹)) = B2.μHeis k ρ := by
  have hu : IsUnit g.det := HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg
  have hgi : g⁻¹ ∈ B.GV k ρ := HermitianFormFactor.UH_inv (Ux3.hpk_det k ρ) hg
  have h := Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure k ρ g⁻¹ hgi
  rwa [LongWeylElement.lev_inv _ hu] at h

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem phi_cont (ρ : ℕ) : Continuous (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  have e : (Dx2.MN.phi (k := k) (ρ := ρ)) = fun x => Dx2.MN.phi x := rfl
  rw [e]
  simp only [Dx2.MN.phi]
  fun_prop

def heisT (ρ : ℕ) (x : B2.HPar k ρ) : Mt k (1 + ρ) := Matrix.of.symm (B2.heis0 k ρ x)

theorem heis_cont (ρ : ℕ) : Continuous (heisT (k := k) ρ) := B2x5.continuous_heis0 k ρ

theorem heis_emb (ρ : ℕ) : MeasurableEmbedding (heisT (k := k) ρ) :=
  (heis_cont ρ).measurableEmbedding (Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed k ρ).1

def phiE (ρ : ℕ) : U.RC k 1 ρ ≃ᵐ B2.HPar k ρ where
  toFun := Dx2.MN.phi
  invFun p := (fun i _ => p.1 i, (fun _ => 0, fun _ => p.2))
  left_inv x := by
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Dx2.MN.phi, Prod.mk.injEq]
    refine ⟨?_, Subsingleton.elim _ _, ?_⟩
    · funext i a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
    · funext a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
  right_inv p := by simp [Dx2.MN.phi]
  measurable_toFun := (phi_cont ρ).measurable
  measurable_invFun := by
    apply Continuous.measurable
    exact (continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst).prodMk
      (continuous_const.prodMk (continuous_pi fun _ => continuous_snd))

theorem phi_emb (ρ : ℕ) : MeasurableEmbedding (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  exact (phiE ρ).measurableEmbedding

theorem heis_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : B.Mat k (1 + ρ) → B.Mat k (1 + ρ) → E) :
    ∫ p : Mt k (1 + ρ) × Mt k (1 + ρ), Φ (Matrix.of p.1) (Matrix.of p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, Φ (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
        ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
  have e0 : B2.μHeis k ρ = (volume : Measure (B2.HPar k ρ)).map (heisT ρ) := rfl
  have e1 : (B2.μHeis k ρ).prod (B2.μHeis k ρ) =
      ((volume : Measure (B2.HPar k ρ)).prod volume).map (Prod.map (heisT (k := k) ρ) (heisT ρ)) := by
    rw [e0, Measure.map_prod_map _ _ (heis_emb ρ).measurable (heis_emb ρ).measurable]
  rw [e1, ((heis_emb ρ).prodMap (heis_emb ρ)).integral_map]
  have hmp : MeasurePreserving (Prod.map (Dx2.MN.phi (k := k) (ρ := ρ)) (Dx2.MN.phi (k := k) (ρ := ρ)))
      ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) ((volume : Measure (B2.HPar k ρ)).prod volume) := by
    have := (Dx2.MN.phi_mp (k := k) (ρ := ρ)).prod (Dx2.MN.phi_mp (k := k) (ρ := ρ))
    simpa [U.muRC] using this
  rw [← hmp.integral_comp ((phi_emb ρ).prodMap (phi_emb ρ))]
  apply integral_congr_ae
  filter_upwards with xx
  rw [Dx2.MN.rn_heis, Dx2.MN.rn_heis]
  rfl

def conjE {r : ℕ} (b : B.Mat k r) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM b
  invFun := conjM b⁻¹
  left_inv x := by
    show b⁻¹ * (b * Matrix.of x * b⁻¹) * b⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hb, Matrix.nonsing_inv_mul _ hb, Matrix.mul_one]
  right_inv x := by
    show b * (b⁻¹ * Matrix.of x * b⁻¹⁻¹) * b⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hb, Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]
  measurable_toFun := B2x5.measurable_conjM b
  measurable_invFun := B2x5.measurable_conjM b⁻¹

theorem heis_conj_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g g' : B.Mat k ρ}
    (hg : g ∈ B.GV k ρ) (hg' : g' ∈ B.GV k ρ) (Φ : Mt k (1 + ρ) × Mt k (1 + ρ) → E) :
    ∫ p, Φ (conjM ((ιLev k 1 ρ g)⁻¹) p.1, conjM ((ιLev k 1 ρ g')⁻¹) p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ p, Φ p ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
  have := sf_heis (k := k) ρ
  have hu : IsUnit ((ιLev k 1 ρ g)⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg))
  have hu' : IsUnit ((ιLev k 1 ρ g')⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg'))
  have m1 : MeasurePreserving (conjE _ hu) (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu).measurable, heis_meas_conj_inv ρ hg⟩
  have m2 : MeasurePreserving (conjE _ hu') (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu').measurable, heis_meas_conj_inv ρ hg'⟩
  have := (m1.prod m2).integral_comp ((conjE _ hu).measurableEmbedding.prodMap (conjE _ hu').measurableEmbedding) Φ
  exact this

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem rhs_int {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) (g : B.Mat k r) (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    Integrable (JF.integrand Bs F g) Bs.μSS := by
  obtain ⟨hFs, ⟨R, hR⟩, -⟩ := hF
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  set A : ℝ := 9 * ((r : ℝ) + 1) * (n ^ 2 + 1) with hA
  have hthr : JF.TransportedAlt k r A 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    have e : (A - 6 * (r : ℝ) * ((0 : ℕ) : ℝ)) / (9 * ((r : ℝ) + 1)) = n ^ 2 + 1 := by
      rw [hA]; push_cast; field_simp; ring
    rw [← hn, e]; linarith
  have hcc : B.InCC A 0 F := JFxG.cptInCC_G hFs (PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra h0
      exact hgC (hR g hg h0)) A 0
  exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq Bs A F hthr hcc).1 g hg

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

def psiInt {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (γ : B.Mat k ρ) (b b' : B.Mat k (1 + ρ)) : Wq →L[ℂ] Wp :=
  (psi k (ρ + 1) B1.z cStd (D.castM (Nat.add_comm 1 ρ) b) *
      star (psi k (ρ + 1) B1.z' cStd (D.castM (Nat.add_comm 1 ρ) b'))) •
    f1 ((D.castM (Nat.add_comm 1 ρ) b)⁻¹ * D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) *
      D.castM (Nat.add_comm 1 ρ) b')

theorem levA_inv (ρ : ℕ) {h : B.Mat k ρ} (hh : IsUnit h.det) :
    (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h))⁻¹ = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h⁻¹) := by
  rw [← castM_inv', LongWeylElement.lev_inv _ hh]

theorem pt_eq {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq)
    (hz : B1.z = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z))
    (hz' : B1.z' = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z'))
    (hπ : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (hπ' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ) (γ : B.Mat k ρ)
    (h0 y h0' y' : Mt k ρ) (a a' : Mt k (1 + ρ))
    (hh0 : Matrix.of h0 ∈ UWset k ρ B0.z) (hy : Matrix.of y ∈ Nset k ρ)
    (hh0' : Matrix.of h0' ∈ UWset k ρ B0.z') (hy' : Matrix.of y' ∈ Nset k ρ)
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (ha' : Matrix.of a' ∈ Nset k (1 + ρ)) :
    JF.integrand B1 f1 (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))
        ((levA ρ h0, Qm ρ (a, y)), (levA ρ h0', Qm ρ (a', y'))) =
      (psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y'))) •
        (B0.π (Matrix.of h0)).comp
          ((psiInt B1 f1 c ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))).comp
            (B0.π' (Matrix.of h0')⁻¹)) := by
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hH := Ux3.hpk_det k ρ
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH hh0.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH hh0'.1
  have huy : IsUnit (Matrix.of y).det := HermitianFormFactor.UH_unit hH hy.1
  have huy' : IsUnit (Matrix.of y').det := HermitianFormFactor.UH_unit hH hy'.1
  have hg : IsUnit (ιLev k 1 ρ (Matrix.of y * Matrix.of h0)).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy.mul hu0)
  have hg' : IsUnit (ιLev k 1 ρ (Matrix.of y' * Matrix.of h0')).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy'.mul hu0')

  have hconj : ∀ (g : B.Mat k (1 + ρ)) (hg : IsUnit g.det) (x : Mt k (1 + ρ)),
      (Matrix.of (conjM g⁻¹ x) : B.Mat k (1 + ρ)) = g⁻¹ * Matrix.of x * g := by
    intro g hg x
    show g⁻¹ * Matrix.of x * g⁻¹⁻¹ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ hg]

  have hψ1 : psi k (ρ + 1) B1.z cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) B1.z cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))) *
        psi k ρ B0.z cStd (Matrix.of y) := by
    rw [hz, psi_Qm ρ B0.z_mem ha hy, psi_castM, psi_castM, hconj _ hg, psi_conjLev ρ B0.z_mem ha hy hh0]
  have hψ2 : psi k (ρ + 1) B1.z' cStd (Matrix.of (Qm ρ (a', y'))) =
      psi k (ρ + 1) B1.z' cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))) *
        psi k ρ B0.z' cStd (Matrix.of y') := by
    rw [hz', psi_Qm ρ B0.z'_mem ha' hy', psi_castM, psi_castM, hconj _ hg', psi_conjLev ρ B0.z'_mem ha' hy' hh0']

  have hπa : B1.π (Matrix.of (levA ρ h0)) = B0.π (Matrix.of h0) := (hπ _).symm
  have hπb : B1.π' (Matrix.of (levA ρ h0'))⁻¹ = B0.π' (Matrix.of h0')⁻¹ := by
    rw [levA_apply, levA_inv ρ hu0', ← hπ']

  have hpt : (Matrix.of (levA ρ h0))⁻¹ * (Matrix.of (Qm ρ (a, y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * Matrix.of (Qm ρ (a', y')) * Matrix.of (levA ρ h0') =
      (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c)
          ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))) *
        D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a')) := by
    rw [hconj _ hg, hconj _ hg']
    show (D.castM κ (ιLev k 1 ρ (Matrix.of h0)))⁻¹ * (D.castM κ (Matrix.of a * ιLev k 1 ρ (Matrix.of y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * D.castM κ (Matrix.of a' * ιLev k 1 ρ (Matrix.of y')) *
        D.castM κ (ιLev k 1 ρ (Matrix.of h0')) = _
    rw [← castM_inv', ← castM_inv', ← castM_inv', ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      sgs_alg ρ _ _ _ _ hu0 huy hu0' huy']
  unfold JF.integrand JF.xiP B.rho B.sgs psiInt
  rw [hψ1, hψ2, hπa, hπb, hpt]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  rw [star_mul']
  ring

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section reorder

variable {X Y A X' Y' A' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace X']
  [MeasurableSpace Y'] [MeasurableSpace A']

def reorderE : ((X × Y) × (X' × Y')) × (A × A') ≃ᵐ (X × (A × Y)) × (X' × (A' × Y')) where
  toFun q := ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
  invFun p := (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable fun q : ((X × Y) × (X' × Y')) × (A × A') => ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun p : (X × (A × Y)) × (X' × (A' × Y')) => (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
    fun_prop

theorem reorder_mp (μX : Measure X) (μY : Measure Y) (μA : Measure A) (μX' : Measure X') (μY' : Measure Y')
    (μA' : Measure A') [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μA] [SigmaFinite μX'] [SigmaFinite μY']
    [SigmaFinite μA'] :
    MeasurePreserving (reorderE (X := X) (Y := Y) (A := A) (X' := X') (Y' := Y') (A' := A'))
      (((μX.prod μY).prod (μX'.prod μY')).prod (μA.prod μA'))
      ((μX.prod (μA.prod μY)).prod (μX'.prod (μA'.prod μY'))) := by
  have h1 := Dx2.SplitM.middle_four_swap_measure_preserving (μX.prod μY) (μX'.prod μY') μA μA'
  have h2 := ((MeasurePreserving.id μX).prod (Measure.measurePreserving_swap (μ := μY) (ν := μA))).comp
    (measurePreserving_prodAssoc μX μY μA)
  have h2' := ((MeasurePreserving.id μX').prod (Measure.measurePreserving_swap (μ := μY') (ν := μA'))).comp
    (measurePreserving_prodAssoc μX' μY' μA')
  have hall := (h2.prod h2').comp h1
  convert hall using 1
  funext ⟨⟨⟨x, y⟩, ⟨x', y'⟩⟩, ⟨a, a'⟩⟩
  rfl

end reorder

variable {k : ℕ}

def MCOm : Prop :=
  ∀ (k ρ : ℕ) (z0 z0' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z0 → inWb k ρ z0' → ∀ c : ℂ, c ≠ 0 →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ z0 z0' →
      D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) ∈
        JF.Om k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0'))

theorem ae_mem_of_haar {r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact h.conc

theorem jfStep_of (hO : MCOm) : JFStep := by
  intro k ρ m e Wp Wq _ _ _ _ _ _ B1 B0 hz hz' hπ hπ' hW1 hW1' hW0 hW0' hN1 hN0 f1 f0 c hc hf1 hstep γ hγ hγO
  subst e
  rw [Dx2.Tower.castV_rfl] at hz hz'
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hπ1 : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hπ1' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ' y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hmc : mc rfl c γ = D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) := by
    unfold mc; rw [Dx2.MN.castM_rfl]

  have hμW : B1.μW = B0.μW.map (levA ρ) :=
    muW_lev B0.z B0.μW B1.μW B0.haarW (by rw [← hz]; exact B1.haarW) hW0 hW1
  have hμW' : B1.μW' = B0.μW'.map (levA ρ) :=
    muW_lev B0.z' B0.μW' B1.μW' B0.haarW' (by rw [← hz']; exact B1.haarW') hW0' hW1'
  have hμN : B1.μN = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by rw [hN1, muN_succ']

  have hOm := hO k ρ B0.z B0.z' B0.z_mem B0.z'_mem c hc γ hγ hγO
  rw [← hz, ← hz', ← hmc] at hOm
  have hInt := rhs_int B1 f1 hf1 _ hOm
  have hsH := sf_heis (k := k) ρ
  have hsN := sf_muN (k := k) ρ
  have hfW : IsFiniteMeasure B0.μW := ⟨by rw [hW0]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure B0.μW' := ⟨by rw [hW0']; exact ENNReal.one_lt_top⟩
  set T : (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) × (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) → B.SS k (ρ + 1) :=
    Prod.map (Prod.map (levA ρ) (Qm ρ)) (Prod.map (levA ρ) (Qm ρ)) with hT
  have hTm : Measurable T :=
    ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable).prodMap
      ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
  set big := (B0.μW.prod ((B2.μHeis k ρ).prod (D.muN k ρ))).prod
    (B0.μW'.prod ((B2.μHeis k ρ).prod (D.muN k ρ))) with hbig
  have hμSS : B1.μSS = big.map T := by
    unfold B.RealPlaceData.μSS
    rw [hμW, hμW', hμN, Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
        ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)]
  set FI := JF.integrand B1 f1 (mc rfl c γ) with hFI
  have hR : B.JF B1 f1 (mc rfl c γ) = ∫ p, FI p ∂B1.μSS := rfl
  have hL : B.JF B0 f0 γ = ∫ p, JF.integrand B0 f0 γ p ∂((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))) := by
    rw [← hN0]; rfl
  have hAE : AEStronglyMeasurable FI (big.map T) := by rw [← hμSS]; exact hInt.aestronglyMeasurable
  have hInt2 : Integrable (FI ∘ T) big := (integrable_map_measure hAE hTm.aemeasurable).1 (by rw [← hμSS]; exact hInt)
  have hRmp := reorder_mp B0.μW (D.muN k ρ) (B2.μHeis k ρ) B0.μW' (D.muN k ρ) (B2.μHeis k ρ)
  have hInt3 : Integrable (FI ∘ T ∘ reorderE) (((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))).prod
      ((B2.μHeis k ρ).prod (B2.μHeis k ρ))) :=
    (hRmp.integrable_comp_emb reorderE.measurableEmbedding).2 hInt2
  rw [hR, hμSS, integral_map hTm.aemeasurable hAE, ← hRmp.integral_comp reorderE.measurableEmbedding]
  change B.JF B0 f0 γ = ∫ x, (FI ∘ T ∘ reorderE) x ∂_
  rw [integral_prod _ hInt3, hL]

  have w1 : ∀ᵐ x ∂B0.μW, Matrix.of x ∈ UWset k ρ B0.z := ae_mem_of_haar B0.haarW
  have w1' : ∀ᵐ x ∂B0.μW', Matrix.of x ∈ UWset k ρ B0.z' := ae_mem_of_haar B0.haarW'
  have w2 : ∀ᵐ x ∂(D.muN k ρ), Matrix.of x ∈ Nset k ρ := ae_mem_of_haar (Dx2.MN.haar ρ)
  have wH : ∀ᵐ x ∂(B2.μHeis k ρ), Matrix.of x ∈ Nset k (1 + ρ) := by
    filter_upwards [ae_mem_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)] with x hx
    obtain ⟨p, hp⟩ := hx
    rw [← hp]; exact Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent k ρ p
  set μO := (B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ)) with hμO
  have o1 : ∀ᵐ o ∂μO, Matrix.of o.1.1 ∈ UWset k ρ B0.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1)
  have o2 : ∀ᵐ o ∂μO, Matrix.of o.1.2 ∈ Nset k ρ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have o3 : ∀ᵐ o ∂μO, Matrix.of o.2.1 ∈ UWset k ρ B0.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae w1')
  have o4 : ∀ᵐ o ∂μO, Matrix.of o.2.2 ∈ Nset k ρ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have i1 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.1 ∈ Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_fst.ae wH
  have i2 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.2 ∈ Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_snd.ae wH
  apply integral_congr_ae
  filter_upwards [o1, o2, o3, o4] with o ho1 ho2 ho3 ho4
  obtain ⟨⟨h0, y⟩, ⟨h0', y'⟩⟩ := o
  simp only at ho1 ho2 ho3 ho4
  have hH := Ux3.hpk_det k ρ
  have hgG : Matrix.of y * Matrix.of h0 ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho2.1 ho1.1
  have hgG' : Matrix.of y' * Matrix.of h0' ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho4.1 ho3.1
  set γh := (Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0') with hγhd
  have hγh : γh ∈ B.GV k ρ := HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv hH hgG) hγ) hgG'

  have hrep := B0.π_rep
  have hrep' := B0.π'_rep
  have hi0 : (Matrix.of h0)⁻¹ ∈ UWset k ρ B0.z := WeylGroupFacts.uw_inv ho1
  have hi0' : (Matrix.of h0')⁻¹ ∈ UWset k ρ B0.z' := WeylGroupFacts.uw_inv ho3
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH ho1.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH ho3.1
  let eA : Wp ≃L[ℂ] Wp := ContinuousLinearEquiv.equivOfInverse (B0.π (Matrix.of h0)) (B0.π (Matrix.of h0)⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hi0 _ ho1, Matrix.nonsing_inv_mul _ hu0, hrep.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ ho1 _ hi0, Matrix.mul_nonsing_inv _ hu0, hrep.1]; rfl)
  let eB : Wq ≃L[ℂ] Wq := ContinuousLinearEquiv.equivOfInverse (B0.π' (Matrix.of h0')) (B0.π' (Matrix.of h0')⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ hi0' _ ho3, Matrix.nonsing_inv_mul _ hu0', hrep'.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ ho3 _ hi0', Matrix.mul_nonsing_inv _ hu0', hrep'.1]; rfl)
  let Λ : (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) := eB.arrowCongr eA
  have hΛ : ∀ Tm : Wq →L[ℂ] Wp, Λ Tm = (B0.π (Matrix.of h0)).comp (Tm.comp (B0.π' (Matrix.of h0')⁻¹)) := by
    intro Tm; ext v; rfl
  set K : ℂ := psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y')) with hK
  set Ψ : Mt k (1 + ρ) × Mt k (1 + ρ) → (Wq →L[ℂ] Wp) := fun p => psiInt B1 f1 c γh (Matrix.of p.1) (Matrix.of p.2)
    with hΨ
  symm
  calc ∫ i, (FI ∘ T ∘ reorderE) (((h0, y), (h0', y')), i) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))
      = ∫ i, K • Λ (Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2)) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
        apply integral_congr_ae
        filter_upwards [i1, i2] with i hi1 hi2
        rw [hΛ]
        show JF.integrand B1 f1 (mc rfl c γ) ((levA ρ h0, Qm ρ (i.1, y)), (levA ρ h0', Qm ρ (i.2, y'))) = _
        rw [hmc, pt_eq B1 B0 hz hz' hπ1 hπ1' f1 c γ h0 y h0' y' i.1 i.2 ho1 ho2 ho3 ho4 hi1 hi2]
    _ = K • Λ (∫ i, Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [integral_smul, Λ.integral_comp_comm]
    _ = K • Λ (∫ i, Ψ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [heis_conj_int ρ hgG hgG' Ψ]
    _ = K • Λ (∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, psiInt B1 f1 c γh (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) := by
        rw [← heis_int ρ (fun b b' => psiInt B1 f1 c γh b b')]
    _ = K • Λ (f0 γh) := by
        rw [hstep γh hγh]
        rfl
    _ = JF.integrand B0 f0 γ ((h0, y), (h0', y')) := by
        rw [hΛ]
        unfold JF.integrand JF.xiP B.rho B.sgs
        congr 3
        show f0 γh = f0 ((Matrix.of h0)⁻¹ * (Matrix.of y)⁻¹ * γ * Matrix.of y' * Matrix.of h0')
        rw [hγhd, Matrix.mul_inv_rev]
        simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.PBH
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem om_cast {a b : ℕ} (h : a = b) (v v' : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ JF.Om k a v v') :
    D.castM h g ∈ JF.Om k b (D.castV h v) (D.castV h v') := by
  subst h; rwa [Dx2.MN.castM_rfl, Dx2.Tower.castV_rfl, Dx2.Tower.castV_rfl]

theorem lowV_lift (ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) : U.lowV k 1 ρ (liftVec k 1 ρ v) = v := by
  funext i
  simp only [U.lowV, liftVec]
  rw [dif_pos (by omega)]
  congr 1; ext; simp

theorem mcOm : MCOm := by
  intro k ρ z0 z0' hz0 hz0' c hc γ hγ hγO
  apply om_cast
  set Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c with hZd
  have hZdet : Z.det = c := by rw [Matrix.det_unique]; rfl
  have hz := Qx4.lift_inWb hz0
  have hz' := Qx4.lift_inWb hz0'
  have hZ : Zhat k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
      Matrix.reindex (Ux3.eC 1 ρ) (Ux3.eC 1 ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ z0 z0' γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 _ _ hz hz', Formalism.QuantumDeterminants.Zhat_eq, lowV_lift, lowV_lift]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k 1 ρ).1 Z γ (by rw [hZdet]; exact hc) hγ, ?_, ?_⟩
  · intro l hl
    obtain ⟨lv, hlv⟩ := l
    rcases Nat.eq_zero_or_pos lv with h0 | hpos
    · subst h0
      unfold Dmin
      rw [Matrix.det_isEmpty]; exact one_ne_zero
    · obtain ⟨l', rfl⟩ : ∃ l', lv = 1 + l' := ⟨lv - 1, by omega⟩
      have hl' : l' ≤ ρ := by simp only at hl; omega
      unfold Dmin
      rw [hZ, Ux3.minor_blocks Z _ l' (by omega) (by omega), hZdet]
      refine mul_ne_zero hc ?_
      exact hγO.1 ⟨l', by omega⟩ hl'
  · have h1 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) (Fin.last _) =
        Z.det * Dmin k ρ z0 z0' γ (Fin.last _) := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ (ρ + 1) le_rfl _
    have h0 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) ⟨1 + ρ, by omega⟩ =
        Z.det * Dmin k ρ z0 z0' γ ⟨ρ, by omega⟩ := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ ρ (by omega) _
    have ht : Tz k (1 + ρ) (liftVec k 1 ρ z0) = Tz k ρ z0 := by rw [Ux3.tz_low _ hz, lowV_lift]
    have ht' : Tz k (1 + ρ) (liftVec k 1 ρ z0') = Tz k ρ z0' := by rw [Ux3.tz_low _ hz', lowV_lift]
    have hG : Gf k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
        Complex.normSq c * Gf k ρ z0 z0' γ := by
      unfold Gf
      rw [h1, h0, ht, ht', hZdet, Complex.normSq_mul, Complex.normSq_mul]
      ring
    rw [hG]
    exact mul_pos (Complex.normSq_pos.2 hc) hγO.2

theorem jfStep : JFStep := jfStep_of mcOm

end Formalism.FourierDecayAlt.P.PBH
end
end
