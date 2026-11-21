import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootCoordinatesIndex

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RealConjugatorData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) :
    Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_inv' {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g⁻¹ = (uMat g)⁻¹ := by
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)⁻¹
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem uMat_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : uMat g * (uMat g)⁻¹ = 1 := by
  rw [← uMat_inv']
  show (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : (uMat g)⁻¹ * uMat g = 1 := by
  rw [← uMat_inv']
  show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
    (((g : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

local notation "NN" => 2 * D.R.rS + D.R.k + 1

def cMr (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) : Matrix (Fin NN) (Fin NN) ℂ)

theorem cMr_eq (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (cMr C γ τ y : Matrix (Fin NN) (Fin NN) ℂ) = Formalism.L2.SG.RealFrameCoordinates.cMg C γ τ y := by
  show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ) =
    C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ
  simp only [Matrix.mul_assoc]

theorem cMr_closedEmb : Topology.IsClosedEmbedding (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  set g := uMat (γ (vOf X τ))
  have h1 : g * g⁻¹ = 1 := uMat_mul_inv _
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  let L : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ ≃ₜ Matrix (Fin NN) (Fin NN) ℂ :=
    { toFun := fun M => C.Qi τ * g⁻¹ * M * (g * C.Q τ)
      invFun := fun M => g * C.Q τ * M * (C.Qi τ * g⁻¹)
      left_inv := fun M => by
        show g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹) = M
        calc g * C.Q τ * (C.Qi τ * g⁻¹ * M * (g * C.Q τ)) * (C.Qi τ * g⁻¹)
            = g * (C.Q τ * C.Qi τ) * g⁻¹ * M * (g * (C.Q τ * C.Qi τ) * g⁻¹) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [hQQi, Matrix.mul_one, h1, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun M => by
        show C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ) = M
        calc C.Qi τ * g⁻¹ * (g * C.Q τ * M * (C.Qi τ * g⁻¹)) * (g * C.Q τ)
            = C.Qi τ * (g⁻¹ * g) * C.Q τ * M * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by simp only [Matrix.mul_assoc]
          _ = M := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp ((Formalism.REAL.isClosedEmbeddingMatrix _ (X.B.I.ε (vOf X τ))).1)

theorem cMr_measEmb : MeasurableEmbedding (cMr C γ τ) := (cMr_closedEmb C γ τ).measurableEmbedding

variable (u u' : D.what₂.Word)

theorem conjugator_inverse : (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ =
    C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  refine Matrix.inv_eq_right_inv ?_
  show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = 1
  calc C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ)
      = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, hQiQ]

theorem stV_iff (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ) ↔
      (cMr C γ τ y : Matrix (Fin NN) (Fin NN) ℂ) ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) := by
  obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := y.2
  have hy' : (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) *
      uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)).2
  have h1 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u τ).1 _ hy
  have h2 := Formalism.L2.SG.RootCoordinatesIndex.inN_iff (C := C) (τ := τ) _ (Formalism.L2.SG.Pf.zTr C u' τ).1 _ hy'
  have e2 : C.Qi τ * uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) * C.Q τ = (cMr C γ τ y : Matrix (Fin NN) (Fin NN) ℂ) := by
    rw [cMr_eq]
    unfold Formalism.L2.SG.RealFrameCoordinates.cMg
    rw [show uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) = uMat ((γ (vOf X τ))⁻¹) * uMat y * uMat (γ (vOf X τ)) from rfl,
      uMat_inv']
  have e1 : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)) * Matrix.of (cMr C γ τ y) *
      (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ)))⁻¹ = C.Qi τ * uMat y * C.Q τ := by
    rw [conjugator_inverse]
    show C.Qi τ * uMat (γ (vOf X τ)) * C.Q τ * (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat y * (uMat (γ (vOf X τ)) * C.Q τ)) *
      (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * C.Q τ) = C.Qi τ * uMat y * C.Q τ
    calc _ = C.Qi τ * (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * uMat y *
          (uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) * (uMat (γ (vOf X τ)))⁻¹) * C.Q τ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.mul_one, Matrix.mul_one]
  show (Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat y) ∧ Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)))) ↔ _
  rw [h1, h2, e2]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    convert ha using 1
    exact e1
  · rintro ⟨hb, ha⟩
    refine ⟨?_, hb⟩
    convert ha using 1
    exact e1.symm

theorem rset_range (m : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hm : Matrix.of m ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ)) :
    m ∈ Set.range (cMr C γ τ) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
  have hmU : (Matrix.of m)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm.1.1
  have hgi0 : (uMat (γ (vOf X τ))⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat (γ (vOf X τ))⁻¹ =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := ((γ (vOf X τ))⁻¹).2
  rw [uMat_inv'] at hgi0
  set g := uMat (γ (vOf X τ))
  have hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := (γ (vOf X τ)).2
  have hgi : (g⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g⁻¹ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := hgi0
  have hQi : (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    rw [← hH]
    calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
        = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  set M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹ with hM
  have hMU : Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc Mᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M
        = (g⁻¹)ᴴ * ((C.Qi τ)ᴴ * ((Matrix.of m)ᴴ * ((C.Q τ)ᴴ *
            (gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g) * C.Q τ) * Matrix.of m) * C.Qi τ) * g⁻¹ := by
          rw [hM]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hg, hH, hmU, hQi, hgi]
  have h2 : g⁻¹ * g = 1 := uMat_inv_mul _
  refine ⟨toUJn M hMU, ?_⟩
  show C.Qi τ * g⁻¹ * M * (g * C.Q τ) = Matrix.of m
  rw [hM]
  calc C.Qi τ * g⁻¹ * (g * C.Q τ * Matrix.of m * C.Qi τ * g⁻¹) * (g * C.Q τ)
      = (C.Qi τ * (g⁻¹ * g) * C.Q τ) * Matrix.of m * (C.Qi τ * (g⁻¹ * g) * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of m := by rw [h2, Matrix.mul_one, hQiQ, Matrix.one_mul, Matrix.mul_one]

end Formalism.L2.SG.RealConjugatorData

end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.RootPatterns

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.RealConjugatorData

variable {D : D7}

theorem blockIdx_loc (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (a i : ℕ), blockIdx (locBlocksFrom D ρ v a bs) i = Formalism.L2.SG.RealObj.blkOf bs i
  | [], _, _ => rfl
  | (t, s) :: bs, a, i => by
    simp only [locBlocksFrom, blockIdx, Formalism.L2.SG.RealObj.blkOf]
    split_ifs
    · rfl
    · rw [blockIdx_loc ρ v bs (a + s) (i - s), add_comm]

theorem mem_rootPat_iff (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) (q : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    q ∈ rootPat (ptLoc D τ w) ↔ q.1 < q.2 ∧ Formalism.L2.SG.RealObj.blkOf w.1 q.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 q.2.1 := by
  simp only [rootPat, ptLoc, ptLocS, locBlocks, Set.mem_setOf_eq, blockIdx_loc]
  simp [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ]

def idxF (τ : D.what₂.Tau) (w : Point D.host.E (D.R.rS + 1)) : ↥(rootPat (ptLoc D τ w)) ≃ Formalism.L2.SG.RealObj.FreeE w where
  toFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).1 q.2⟩
  invFun q := ⟨q.1, (mem_rootPat_iff τ w q.1).2 q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootCoords_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  unfold Formalism.MainNotions.S.rootCoords
  refine continuous_pi (fun q => ?_)
  unfold flagMat
  first
    | fun_prop
    | (simp only [Matrix.mul_apply, Matrix.of_apply]; fun_prop)
    | continuity
    | (exact ((continuous_apply _).comp (continuous_apply _)).comp
        (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const))

variable {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

theorem stCoordV_comp :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) =
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)) ∘
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) ∘ cMr C γ τ := by
  funext y q
  have ha : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega
  have hpc : ∀ x : ↥(rootPat (ptLoc D τ w)) → ℂ,
      MeasurableEquiv.piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w) x q = x ((idxF τ w).symm q) :=
    fun x => by simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [Function.comp_apply]
  rw [hpc, Formalism.L2.SG.RealFrameCoordinates.stCoordV_eq C u' w γ τ y q]
  unfold rootCoords flagMat
  rw [dif_pos (show ((idxF τ w).symm q).1.1.val < D.R.rS from ha), ← cMr_eq]
  rfl

include C in

theorem place (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    ∃ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (c : ℝ≥0∞),
      Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) μ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
        μ.map (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) =
          c • Measure.pi (fun _ : Formalism.L2.SG.RealObj.FreeE w => (volume : Measure ℂ)) := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  obtain ⟨μ₀, c, hHaar, hc0, hctop, hmap⟩ := hLoc D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW'
    (by rw [hTz']; exact hT u') (ptLoc D τ w) _ hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)
  have hemb := cMr_measEmb C γ τ
  set μ := Measure.comap (cMr C γ τ) μ₀ with hμ
  have hconc : μ₀ (Set.range (cMr C γ τ))ᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_) hHaar.2.2.1
    intro hR
    exact hx (rset_range C γ τ x hR)
  have hres : μ₀.restrict (Set.range (cMr C γ τ)) = μ₀ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hconc)
  have hmapc : μ.map (cMr C γ τ) = μ₀ := by rw [hμ, hemb.map_comap, hres]
  have : SigmaFinite μ₀ := hHaar.1
  refine ⟨μ, c, ⟨?_, ?_, ?_, fun s hs => ?_⟩, hc0, hctop, ?_⟩
  · exact SigmaFinite.of_map μ hemb.measurable.aemeasurable (by rw [hmapc]; infer_instance)
  · intro h0
    apply hHaar.2.1
    rw [← hmapc, h0, Measure.map_zero]
  · rw [hμ, hemb.comap_apply]
    refine measure_mono_null ?_ hHaar.2.2.1
    rintro _ ⟨y, hy, rfl⟩ hR
    exact hy ((stV_iff C γ τ u u' y).2 hR)
  · have hs0 := (stV_iff C γ τ u u' s).1 hs
    have hfun : cMr C γ τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (cMr C γ τ s) ∘ cMr C γ τ := by
      funext x
      obtain ⟨hQiQ, hQQi, _, _⟩ := C.isT τ
      show C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat (s * x) * (uMat (γ (vOf X τ)) * C.Q τ) =
        (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * (uMat (γ (vOf X τ)) * C.Q τ)) *
          (C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat x * (uMat (γ (vOf X τ)) * C.Q τ))
      rw [show uMat (s * x) = uMat s * uMat x from rfl]
      calc C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * (uMat s * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ)
          = C.Qi τ * (uMat (γ (vOf X τ)))⁻¹ * uMat s * ((uMat (γ (vOf X τ)) * (C.Q τ * C.Qi τ) *
              (uMat (γ (vOf X τ)))⁻¹) * uMat x) * (uMat (γ (vOf X τ)) * C.Q τ) := by
            rw [hQQi, Matrix.mul_one, uMat_mul_inv, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hmeas_s : Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => s * x) := measurable_const_mul s
    have hmeas_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (cMr C γ τ s)) := by
      refine Continuous.measurable ?_
      unfold Formalism.QuantumDeterminants.lmulM
      refine Continuous.matrix_mul continuous_const ?_
      exact continuous_id
    have key : (μ.map (fun x => s * x)).map (cMr C γ τ) = μ.map (cMr C γ τ) := by
      rw [Measure.map_map hemb.measurable hmeas_s, hfun, ← Measure.map_map hmeas_l hemb.measurable, hmapc]
      exact hHaar.2.2.2 _ hs0
    calc μ.map (fun x => s * x) = (((μ.map (fun x => s * x)).map (cMr C γ τ))).comap (cMr C γ τ) :=
          (hemb.comap_map _).symm
      _ = μ := by rw [key, hemb.comap_map]
  · rw [stCoordV_comp C u' w γ τ, ← Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable
      ((rootCoords_cont _ _ _ _).measurable.comp hemb.measurable),
      ← Measure.map_map (rootCoords_cont _ _ _ _).measurable hemb.measurable, hmapc, hmap, Measure.map_smul,
      (volume_measurePreserving_piCongrLeft (fun _ : Formalism.L2.SG.RealObj.FreeE w => ℂ) (idxF τ w)).map_eq]
    rfl

theorem placeHaar_of_loc (hLoc : Formalism.L2.SG.NGPin.LocRootHaar) : Formalism.L2.SG.NGPin.PlaceHaar := by
  intro D X u u' w γ hrep v
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  exact place C u u' w γ τ hLoc hrep

end Formalism.L2.SG.RootPatterns

end
end
