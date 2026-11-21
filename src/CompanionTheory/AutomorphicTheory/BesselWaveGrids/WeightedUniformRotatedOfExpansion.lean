import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TBBTie
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.FamilyThroughDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsBisTer
import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsFRepDualStandardUnitaryRep
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.WeilFormulaIntegrableComplexImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.IsHaarOnIffGroupsUnitaryUnipotentImports
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselCharacterUnipotentRadicalPropertiesImports
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselSubgroupParameterMeasurePreservingImports
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeHW
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.IsData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie
import Formalism.HermitianCurvature.StatementSz
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.BesselNormSqEqBigCellNormSqAltImports
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PowFourLeRpowNineHalves

section
noncomputable section

namespace CompanionTheory.WaveGrid.GapSizes

theorem sizes (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (Cg : ℝ) (hCg : 1000 ≤ Cg) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have em : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have eN : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have e3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK
  rw [em, eN, e3]
  generalize hm : 2 * (r : ℝ) + 2 = m
  generalize hN : 2 * (r : ℝ) + k + 1 = N
  have hm2 : (2 : ℝ) ≤ m := by rw [← hm]; linarith
  have hmN : m ≤ N := by rw [← hm, ← hN]; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsq : Real.sqrt (2 * ((r : ℝ) + 1)) = Real.sqrt m := by rw [← hm]; ring_nf
  have h92 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hmpos, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hspos : (0 : ℝ) < Real.sqrt m := by linarith
  have hN3 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have hPN : N ^ 3 ≤ 3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3 := by
    have : (0 : ℝ) ≤ 3 * ((r : ℝ) + 1) * N ^ 2 := by positivity
    linarith
  obtain ⟨s1, s2⟩ := sizes Cg m N (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) (Real.sqrt m) hCg hm2 hmN hPN hs1
  have hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (Cg * m ^ ((9 : ℝ) / 2) * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 4) =
      Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [hsq, h92]
    field_simp
    ring
  obtain ⟨cM, cM0, cS, cS0, cG, cG0⟩ := consts k r hk
  rw [hm] at cM
  rw [hN] at cS cG
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hN3' : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hmm : m ^ 2 * N ^ 3 ≥ 4 * N ^ 3 := by nlinarith
  have hX : 4 * N ^ 3 ≤ m ^ 2 * N ^ 3 := by nlinarith
  have hX1 : (4 : ℝ) ≤ m ^ 2 * N ^ 3 := by linarith
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [h92]; linarith
  · rw [hA]
    have hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 6 * N ^ 3 := by linarith
    have hL : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 2 * (m ^ 2 / 2) * (6 * N ^ 3) :=
      mul_le_mul (by linarith) hsum (by positivity) (by positivity)
    have hL' : 2 * (m ^ 2 / 2) * (6 * N ^ 3) = 6 * (m ^ 2 * N ^ 3) := by ring
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [hL, hL', s2', cG, hX, hX1]
  · rw [hA]
    have hN23 : N ^ 2 ≤ N ^ 3 := by
      have : N ^ 3 = N ^ 2 * N := by ring
      rw [this]; exact le_mul_of_one_le_right (by positivity) hN1
    have h9 : 9 * ((r : ℝ) + 1) = 4.5 * m := by rw [← hm]; ring
    have e1 : 9 * ((r : ℝ) + 1) * N ^ 2 ≤ 4.5 * m * N ^ 3 := by
      rw [h9]; exact mul_le_mul_of_nonneg_left hN23 (by positivity)
    have hq : 4.5 * m ≤ 3 * m ^ 2 := by nlinarith only [hm2]
    have e2 : 4.5 * m * N ^ 3 ≤ 3 * (m ^ 2 * N ^ 3) := by
      have := mul_le_mul_of_nonneg_right hq hN3'
      linarith only [this]
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [e1, e2, hX, hX1, s2', cG]

end CompanionTheory.WaveGrid.GapSizes
end
end

section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.TypeHC

section param
open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem isType_of_hc {u : ℕ → ℝ} {u₀ : Fin k → ℝ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hπ : IsHCTypeW k r z u₀ π) (hu : ∀ s : Fin k, u (s.val + 1) = u₀ s) : Q.IsType k r z π u := by
  obtain ⟨p1, pmul, punit, pcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π := ⟨p1, pmul⟩
  have hcont : ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) := continuousOn_clm_apply.2 pcont
  obtain ⟨g, hg, h₀⟩ := hπ
  have hirr : ∀ S : Submodule ℂ W, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS => h₀.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ (conj_mem_UW hg (by
      have := Matrix.mem_unitaryGroup_iff'.mp hx.1
      rw [Matrix.star_eq_conjTranspose] at this
      exact mem_UJset_allPos.2 this)) v hv
  obtain ⟨E, hgl, -, hE⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k W _ h₀.2.2.1
  obtain ⟨v, hv, hq⟩ := qdet_eigen h₀ E hgl hE
  have hB := isFrameOf hg
  set A := g * incl k r with hA
  set B := Aᴴ * Hpk k r with hBd
  have hd : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ x, Q.dRep π (A * Z * B) x = ∑ a, ∑ b, Z a b • E a b x := by
    intro Z hZ x
    rw [← (hE Z hZ x).deriv]
    unfold Q.dRep
    congr 1
    funext t
    rw [conj_blockW hg.1, ← exp_corner _ _ (co_mul hg.1), Matrix.mul_smul, Matrix.smul_mul]
  have hH : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Hpk_mul_self
  have hc : ∀ Y : Matrix (Fin k) (Fin k) ℂ,
      (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * (A * Y * B)ᴴ * Formalism.QuantumDeterminants.Hpk k r = A * Yᴴ * B := by
    intro Y
    rw [hH, hBd]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose, ← Matrix.mul_assoc,
      Hpk_mul_self, Matrix.one_mul]
    rfl
  have hEB : Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) = E := by
    funext a b
    refine LinearMap.ext fun x => ?_
    have hl := P.QrD.frame_lie hB a b
    show P.QrD.ecOp π _ x = _
    rw [← P.QrD.ecRep_eq hrep hcont hl.1 hl.2, unitB_eq]
    unfold Q.EcRep Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [← hA, ← hBd, hc, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, hd, hd]
    · simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
      have e : ∀ c d, ((1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - (Matrix.single a b (1 : ℂ))ᴴ)) c d +
          Complex.I * ((1 / (2 * Complex.I) : ℂ) • (Matrix.single a b (1 : ℂ) + (Matrix.single a b (1 : ℂ))ᴴ)) c d =
          Matrix.single a b (1 : ℂ) c d := by
        intro c d
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
        field_simp
        ring
      simp only [e]
      simp [Matrix.single, ite_and, ite_smul]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, ← neg_smul, add_comm]
      congr 1
      simp [Complex.conj_ofNat]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]
      congr 1
      simp
  let K : Submodule ℂ W :=
    { carrier := {x | ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((k : ℂ) - 1) / 2) x = (∏ s, (Y + (u₀ s : ℂ))) • x}
      add_mem' := fun ha hb w => by rw [map_add, ha w, hb w, smul_add]
      zero_mem' := fun w => by simp
      smul_mem' := fun s x hx w => by rw [map_smul, hx w, smul_comm] }
  have hKs : Qr.Stab (Qr.EB π (fun a => g *ᵥ bvec (bl k r a))) K := by
    rw [hEB]
    intro a b x hx w
    have := congrArg (fun T : Module.End ℂ W => T x) (Formalism.REAL.qDetCentral _ k _ hgl (w + ((k : ℂ) - 1) / 2) a b)
    simp only [Module.End.mul_apply] at this
    rw [this, hx w, map_smul]
  have hK := P.lie_stabilizer W k r z π _ hz hT ⟨hrep, hcont⟩ hB K hKs
  have hKt : K = ⊤ := (hirr K hK).resolve_left ((Submodule.ne_bot_iff K).2 ⟨v, hq, hv⟩)
  refine ⟨h₀.1, hrep, hcont, punit, hirr, fun Bs hBs w x => ?_⟩
  have hx : x ∈ K := hKt ▸ Submodule.mem_top
  have e := hx (w - ((k : ℂ) - 1) / 2)
  rw [sub_add_cancel] at e
  rw [(P.frame_general_linear W k r k z π Bs ⟨hrep, hcont⟩ hBs).2, P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hB, hEB, e,
    CompanionTheory.D.Inhab.TypeHW.prod_Icc]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hu]
  ring

end param

theorem exists_place : ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (μW μW' : Measure (Formalism.QuantumDeterminants.Mt P.k P.r)) (l0 : ℕ), Q.IsPlace P z z' π π' → 2 ≤ P.k → 1 ≤ l0 → l0 ≤ P.k →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z) μW → μW Set.univ = 1 →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z') μW' → μW' Set.univ = 1 →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π' ∧
      p.T.base.μW = μW ∧ p.T.base.μN = D.muN P.k P.r ∧ p.T.base.μW' = μW' ∧
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P z z' π π' μW μW' l0 hP hk hl1 hl2 hW hW1 hW' hW1'
  obtain ⟨μ, hμ⟩ := CompanionTheory.D.Inhab.IsDataInh.haar_glev_last P.k P.r
  obtain ⟨hOK, hz, hz', hT, hT', ⟨-, hr, hc, hu, -, -⟩, ⟨-, hr', hc', hu', -, -⟩⟩ := id hP
  obtain ⟨B0, e1, e2, e3, e4, -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists P.k P.r Wp Wq z z' π π' hOK.k_pos hz hz'
    (by rw [hT]; exact hOK.T_pos) (by rw [hT']; exact hOK.T'_pos) hr hr' hu hu' hc hc'
  obtain ⟨T0, -, -, -, -, hN0⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq B0
  have hmuN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset P.k P.r) (D.muN P.k P.r) := by
    have h := (hN0 0 (Nat.zero_le _)).2.2
    have h' : T0.base.μN = D.muN P.k P.r := (by simpa using h : (T0.bs 0).μN = D.muN P.k P.r)
    exact h' ▸ T0.base.haarN
  subst e1 e2 e3 e4
  let Bs : B.RealPlaceData P.k P.r Wp Wq :=
    { B0 with μW := μW, μN := D.muN P.k P.r, μW' := μW', haarW := hW, haarN := hmuN, haarW' := hW' }
  obtain ⟨T, hTb, hTN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower P.k P.r Wp Wq Bs hW1 hW1' rfl
  have hPl : Q.IsPlace P T.base.z T.base.z' T.base.π T.base.π' := by
    rw [hTb]; exact hP
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of T.base
  obtain ⟨X, L, st, hD⟩ := CompanionTheory.D.Inhab.IsDataInh.isData_of_place P _ _ _ _ hPl μ hμ l0
  obtain ⟨Θ, hI, hDD⟩ := hTL Wp Wq P T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P T.base.z T.base.z' T.base.π T.base.π' (m₀ *ᵥ ν') hPl
    f1 f2 f3
  refine ⟨⟨l0, T, ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hTN, hF, hPl, ⟨X, μ, L, st, hD, hI⟩⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hDD⟩
  · change T.base.z = B0.z; rw [hTb]
  · change T.base.z' = B0.z'; rw [hTb]
  · change T.base.π = B0.π; rw [hTb]
  · change T.base.π' = B0.π'; rw [hTb]
  · change T.base.μW = μW; rw [hTb]
  · change T.base.μN = D.muN P.k P.r; rw [hTb]
  · change T.base.μW' = μW'; rw [hTb]

end CompanionTheory.WaveGrid.TypeHC
end
end

section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Finset

noncomputable def cfgPar (c : Sz.Cfg) (r : ℕ) (T T' : ℝ) (de de' : ℕ → ℝ) : M.Par := ⟨c.k, r, T, T', c.u de, c.u de'⟩

section cfg

variable (c : Sz.Cfg)

theorem cfg_v_step (i : ℕ) : c.v i = c.v (i + 1) + 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

theorem cfg_v_mem (hok : c.Ok) (i : ℕ) (hi1 : 1 ≤ i) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i ∧ c.v i ≤ c.v 1 := by
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have h1 : (1:ℝ) ≤ i := by exact_mod_cast hi1
  have h2 : (i:ℝ) + 1 ≤ c.k := by exact_mod_cast hi
  simp only [Sz.Cfg.v, Nat.cast_one]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 1 - i)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * c.Del) (by linarith : (0:ℝ) ≤ (i:ℝ) - 1)]

theorem cfg_v_last (hk : 1 ≤ c.k) : c.v (c.k - 1) = c.vlast := by
  simp only [Sz.Cfg.v, Nat.cast_sub hk, Nat.cast_one]
  ring

theorem cfg_b_pos (hok : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact hok.hb1
  | succ n hn ih =>
    intro hnm
    have h1 := hok.hgap n hn (by omega)
    have h2 := ih (by omega)
    linarith

theorem cfg_inter (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : ℕ) (hs1 : 1 ≤ s)
    (hsk : s ≤ c.k - 1) : c.lam s + 1 / 2 ≤ c.u de s ∧ c.u de (s + 1) ≤ c.lam s - 1 / 2 := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlam : c.lam s = c.v s := by
    rw [Sz.Cfg.lam, if_pos (by omega)]
  rw [hlam]
  constructor
  · rcases Nat.lt_or_ge s 2 with h | h
    · have hs : s = 1 := by omega
      subst hs
      rw [Sz.Cfg.u, if_pos rfl]
      have := hok.ha
      nlinarith [mul_nonneg (sub_nonneg.2 hk') (sub_nonneg.2 hD)]
    · rw [Sz.Cfg.u, if_neg (by omega), if_neg (by omega)]
      have hstep := cfg_v_step c (s - 1)
      rw [Nat.sub_add_cancel hs1] at hstep
      rcases hde (s - 1) with h0 | h0 <;> rw [h0] <;> linarith
  · rw [Sz.Cfg.u, if_neg (by omega)]
    by_cases hks : s + 1 = c.k
    · rw [if_pos hks, Sz.Cfg.ulast]
      have hv : c.v s = c.vlast := by
        have := cfg_v_last c (by omega : 1 ≤ c.k)
        rw [show s = c.k - 1 by omega]
        exact this
      rw [hv]
      split_ifs with ht
      · obtain ⟨h1, _⟩ := hok.htop ht
        have := hok.hb1
        have := hok.hv0
        linarith
      · linarith
    · rw [if_neg hks, Nat.add_sub_cancel]
      rcases hde s with h0 | h0 <;> rw [h0] <;> linarith

theorem cfg_u_le (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (b : ℝ) (ha : c.a ≤ b)
    (hb1 : c.b 1 ≤ b) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ c.k) : |c.u de i| ≤ b := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hprod : 16 * c.Del ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0:ℝ) ≤ c.Del)]
  have hv1 : c.vlast ≤ c.v 1 := (cfg_v_mem c hok 1 le_rfl (by omega)).1
  have hv0 := hok.hv0
  have hav := hok.ha
  have hb1 := hok.hb1
  rw [Sz.Cfg.u, abs_le]
  split_ifs with h1 h2
  · constructor <;> linarith
  · rw [Sz.Cfg.ulast]
    split_ifs with ht
    · obtain ⟨h3, h4⟩ := hok.htop ht
      constructor <;> linarith
    · constructor <;> linarith
  · have hm := cfg_v_mem c hok (i - 1) (by omega) (by omega)
    rcases hde (i - 1) with h0 | h0 <;> rw [h0] <;> constructor <;> linarith [hm.1, hm.2]

theorem lamData_cfg (r : ℕ) (hm : c.m = 2 * r + 2) (hok : c.Ok) (T T' : ℝ) (de de' : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) (hde' : ∀ i, de' i = 0 ∨ de' i = 1) (cs b : ℝ) (hc0 : 0 < cs)
    (hc : 1 + cs ≤ 4 * c.Del) (ha : c.a ≤ b) (hb : ∀ j, 1 ≤ j → j ≤ c.m → c.b j ≤ b) :
    LamData (cfgPar c r T T' de de') c.lam cs (4 * c.Del) b := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hprod : 16 * c.Del ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0:ℝ) ≤ c.Del)]
  have hkD : (c.k:ℝ) ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c.k) (sub_nonneg.2 hD)]
  have hv1 : c.vlast ≤ c.v 1 := (cfg_v_mem c hok 1 le_rfl (by omega)).1
  have hv0 := hok.hv0
  have hav := hok.ha
  have hbpos := cfg_b_pos c hok
  refine ⟨hc0, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · show (c.k:ℝ) ≤ b
    linarith
  · linarith
  · intro s hs1 hs2
    change s ≤ c.k + 2 * r + 1 at hs2
    rw [Sz.Cfg.lam]
    split_ifs with hsk
    · have := cfg_v_mem c hok s hs1 (by omega)
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    · have hj1 : 1 ≤ s + 1 - c.k := by omega
      have hj2 : s + 1 - c.k ≤ c.m := by omega
      have h1 := hbpos _ hj1 hj2
      have h2 := hb _ hj1 hj2
      rw [abs_neg, abs_of_pos (by linarith)]
      exact h2
  · intro s hs1 hs2
    change s + 1 ≤ c.k - 1 at hs2
    rw [Sz.Cfg.lam, Sz.Cfg.lam, if_pos (by omega), if_pos (by omega)]
    have := cfg_v_step c s
    linarith
  · intro s hs1 hs2
    exact ⟨cfg_inter c hok de hde s hs1 hs2, cfg_inter c hok de' hde' s hs1 hs2⟩
  · intro i hi1 hi2
    have hb1 := hb 1 le_rfl (by omega)
    exact ⟨cfg_u_le c hok de hde b ha hb1 i hi1 hi2, cfg_u_le c hok de' hde' b ha hb1 i hi1 hi2⟩

end cfg

noncomputable def cfg₀ : Sz.Cfg where
  k := 4
  m := 2
  Del := 15
  vlast := 0
  b := fun j => (j : ℝ) + 1
  a := 400
  top := false
  bp := 0

theorem cfg₀_ok : cfg₀.Ok where
  hk := by
    norm_num [cfg₀]
  hm := by norm_num [cfg₀]
  hDel := by norm_num [cfg₀]
  hv0 := by norm_num [cfg₀]
  hv1 := by norm_num [cfg₀, Sz.Cfg.v]
  hb1 := by norm_num [cfg₀]
  hgap := by
    intro j _ _
    simp only [cfg₀]
    push_cast
    linarith
  ha := by norm_num [cfg₀, Sz.Cfg.v]
  htop := by simp [cfg₀]

theorem lamData_cfg₀ :
    LamData (cfgPar cfg₀ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)) cfg₀.lam 10 (4 * cfg₀.Del) 400 := by
  refine lamData_cfg cfg₀ 0 (by norm_num [cfg₀]) cfg₀_ok 1 1 _ _ (fun _ => Or.inl rfl) ?_ 10 400
    (by norm_num) (by norm_num [cfg₀]) (by norm_num [cfg₀]) ?_
  · intro i
    split_ifs <;> simp
  · intro j _ hj
    simp only [cfg₀] at hj ⊢
    have : (j:ℝ) ≤ 2 := by exact_mod_cast hj
    linarith

end CompanionTheory.WaveGrid
end

section
namespace CompanionTheory.WaveGrid.Inhab

open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem int_of_half {k : ℕ} {u v : ℕ → ℝ} (hk : 1 ≤ k)
    (hu : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m)
    (hv : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, v i - ((k : ℝ) - 1) / 2 = m) :
    ∀ i ∈ Icc 1 k, ∃ n : ℤ, v i - u 1 = n := by
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m1, hm1⟩ := hu 1 le_rfl hk
  obtain ⟨m2, hm2⟩ := hv i hi1 hik
  exact ⟨m2 - m1, by push_cast; linarith⟩

theorem ok_diff (P : M.Par) (hk : 1 ≤ P.k) (hT : 0 < P.T) (hT' : 0 < P.T') (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b) :
    P.OK := by
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, int_of_half hk hu.half hu'.half, ?_⟩
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
  obtain ⟨b1, b2⟩ := inter_half hc hu' i hi1 hik
  simp only [M.Par.lo, M.Par.hi]
  have hmax := max_le a2 b2
  have hmin := le_min a1 b1
  linarith

def uP (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l + 1 then u i + n₀ else u i
def uM (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l then u i - n₀ else u i

theorem ok_plus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uP u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l + 1
    · refine ⟨n + n₀, ?_⟩
      simp only [uP, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uP, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uP]
    by_cases h1 : i + 1 = l + 1
    · have hil : i = l := by omega
      subst hil
      have h2 : ¬ (i = i + 1) := by omega
      rw [if_pos h1, if_neg h2, min_self, max_eq_right (by linarith)]
      linarith
    · by_cases h2 : i = l + 1
      · rw [if_neg h1, if_pos h2, max_self, min_eq_left (by linarith)]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith

theorem ok_minus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uM u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l
    · refine ⟨n - n₀, ?_⟩
      simp only [uM, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uM, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uM]
    by_cases h2 : i = l
    · subst h2
      have h1 : ¬ (i + 1 = i) := by omega
      rw [if_neg h1, if_pos rfl, max_self, min_eq_right (by linarith)]
      linarith
    · by_cases h1 : i + 1 = l
      · rw [if_pos h1, if_neg h2, max_eq_left (by linarith), min_self]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith



noncomputable def lamX (x : ℤ) : Fin (2 * 0 + 3 + 1) → ℝ := ![(x : ℝ) + 1 / 2, -79 / 2, -119 / 2, -159 / 2]
noncomputable def uX : ℕ → ℝ := fun i => if i = 1 then 80 else if i = 2 then 0 else -50







noncomputable def cfg₁ : Sz.Cfg := { cfg₀ with a := 801 / 2 }

theorem cfg₁_ok : cfg₁.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cfg₁, cfg₀, Sz.Cfg.v] <;> norm_num

noncomputable def Pc : M.Par := cfgPar cfg₁ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)




end CompanionTheory.WaveGrid.Inhab
end

section
noncomputable section

namespace CompanionTheory.WaveGrid.Tied

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Coef

def ExpBall : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 a₁ : ℕ) (R0 : BranchingSupport.Rep P.k P.r)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ),
    BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 → BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 →
    P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) →
    BranchingSupport.n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) →
    (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f) →
    CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁


section num

variable {k r : ℕ}

def gapY (k r : ℕ) : ℝ :=
  ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)

theorem pow_four_le_rpow_nine_halves (r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)) (by norm_num)

theorem thrX_le_gapY (k r : ℕ) : thrX k r ≤ gapY k r := by
  unfold thrX gapY
  have h1 : ((r : ℝ) + 1) ^ 4 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) 4
  have e : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (h1.trans (pow_four_le_rpow_nine_halves r)) (by positivity)

theorem mul_le_gapY (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  mul_le_mul (pow_four_le_rpow_nine_halves r) (le_add_of_nonneg_left (by positivity)) (by positivity) (by positivity)

theorem fourth_power_le_gap (k r : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 4 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)))) (mul_le_gapY k r)

theorem cube_le_gap (k r : ℕ) : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ gapY k r :=
  le_trans (le_mul_of_one_le_left (by positivity)
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2)))) (mul_le_gapY k r)

theorem hypType_of (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {b : ℝ} (hlam : IsHCParam lam)
    (hu : IsHCParam u) (hI : InterlaceS (by omega) u lam) (hb : ∀ i, |u i| ≤ b) : HypType k r lam (lamN u) b where
  half := fun i h1 h2 => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [lamN_succ u ⟨j, by omega⟩]
    exact hu.2 _
  inter := by
    refine ⟨fun s t hst => hlam.1 (by simpa using hst), fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hs' : (s : ℕ) < k := by simpa using hs
      rw [lamN_succ u ⟨s, hs'⟩]
      by_cases h : (s : ℕ) + 1 < k
      · exact (hI.1 s h).1
      · have e : (s : ℕ) = k - 1 := by omega
        have := hI.2 (by omega)
        simp only [← e] at this
        exact this
    · have hs' : (s : ℕ) + 1 < k := by
        have : (s : ℕ) + 2 ≤ k := by simpa using hs
        omega
      rw [show (s : ℕ) + 2 = (s + 1) + 1 from rfl, lamN_succ u ⟨s + 1, hs'⟩]
      exact (hI.1 s hs').2
  u_le := fun i h1 h2 => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [lamN_succ u ⟨j, by omega⟩]
    exact hb _

theorem gap_of_lt {n : ℕ} {lam : Fin n → ℝ} {g : ℝ} (hlam : IsHCParam lam) (hg : AllGaps lam g) {a c : Fin n}
    (h : a < c) : g ≤ lam a - lam c := by
  have h1 := hg a c h.ne
  rwa [abs_of_pos (sub_pos.2 (hlam.1 h))] at h1

theorem shape_of (hk : 1 ≤ k) {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {bv : ℝ} (hlam : IsHCParam lam)
    (hu : IsHCParam u) (hI : InterlaceS (by omega) u lam) (hS : ShapeS u lam bv) :
    (∀ a : Fin (2 * r + k + 1), a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8) ∧
      ∀ a : Fin (2 * r + k + 1), k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv := by
  refine ⟨fun a ha => (hS a).1 ⟨⟨_, (hI.1 a ha).1⟩, ⟨_, (hI.1 a ha).2⟩⟩, fun a ha => (hS a).2 ?_⟩
  rintro ⟨-, i, hi⟩
  have h1 := hI.2 (by omega)
  have h2 : lam a ≤ lam ⟨k - 1, by omega⟩ := hlam.1.antitone (by rw [Fin.le_def]; simp only; omega)
  have h3 : u ⟨k - 1, by omega⟩ ≤ u i := hu.1.antitone (by rw [Fin.le_def]; simp only; omega)
  linarith

theorem scaled_le {T ka b Ch : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch)
    (hT : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) : T ≤ b ^ (2 * |Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have e : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hka.ne', one_pow, mul_one]
  have h2 : ka ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    calc ka ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) :=
          pow_le_pow_left₀ hka.le (h1.trans (Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _))) _
      _ ≤ (b ^ |Ch|) ^ (2 * r + 2) := pow_le_pow_right₀ (Real.one_le_rpow hb (abs_nonneg _)) (by omega)
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
  have h3 : b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc T = _ := e
    _ ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) :=
        mul_le_mul (hT.trans h3) h2 (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

end num

open CompanionTheory.LimBd.Main (ZuckT CoefCC) in

theorem coefCC1_of {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hK : PI.KFinSmooth) (hC : CoefCC) :
    CoefCC1 (Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) := by
  intro k r L f _ hf hgap
  have hfK : CutBP.KFinDSCoef L.ε L.lam f := by
    obtain ⟨Pm, Qm, h1, h2, h3⟩ := hf
    exact ⟨L.Hs, _, _, _, L.σ, Pm, Qm, L.hlam, L.hσ, h1, h2, fun g _ => h3 g⟩
  have hc := abs_nonneg Formalism.MainNotions.BigCellDensity.c3
  have hX := thrX_nonneg k r
  have hY1 := thrX_le_gapY k r
  have hY2 := fourth_power_le_gap k r
  have hY3 := cube_le_gap k r
  have hm : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + 2))
  have h1 := ht (2 * r + k + 1) L.ε (by omega)
  have h2 := mul_le_mul_of_nonneg_left hY3 hCt
  have h3 := mul_le_mul_of_nonneg_left hY1 hc
  have hD := kDecay_of_gap hZ k r L.ε (X := |Formalism.MainNotions.BigCellDensity.c3| * thrX k r) (d := 0)
    (h := (Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) * gapY k r) (mul_nonneg hc hX) le_rfl (by nlinarith)
  have hg : PI.ZuckTensor.GapAtLeast L.ε L.lam ((Ct + |Formalism.MainNotions.BigCellDensity.c3| + 2) * gapY k r - 2 * 0) := by
    rw [mul_zero, sub_zero, gapY, ← mul_assoc]
    exact hgap
  exact JCx2.sq_inCC_mono (thr_conv k r (le_abs_self _) hc (by linarith)) le_rfl (kfin_inCC hK hC hD hg hfK 1)

end CompanionTheory.WaveGrid.Tied
end
end

section
noncomputable section

namespace CompanionTheory.WaveGrid.Ties

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal

section energy

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}

theorem norm_JF_eq (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (d : Fin (r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) {γ γ' : B.Mat k r} (hγ : γ ∈ B.GV k r) (hγ' : γ' ∈ B.GV k r)
    (hZ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (PBJ.bigPt d) (r + 1))
    (hZ' : Zhat k r Bs.z Bs.z' γ' = D.ptMatN (PBJ.bigPt d) (r + 1)) (hpos : 0 < Gf k r Bs.z Bs.z' γ) :
    ‖B.hsVec (B.JF Bs F γ)‖ = ‖B.hsVec (B.JF Bs F γ')‖ := by
  have hl : D.IsLocPt (PBJ.bigPt d) (r + 1) := PBJ.Dens.isLocPt_bigPt d hd
  have hpos' : 0 < Gf k r Bs.z Bs.z' γ' := by
    rw [← ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ', ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ]
    exact hpos
  obtain ⟨s, hs, s', hs', hγs⟩ := fibre_orbit_description k r Bs.z Bs.z'
    ⟨Bs.k_pos, Dx2.VV.std_vector_z Bs, Dx2.VV.std_vector_z_prime Bs⟩ _ hγ _ hγ' hpos (hZ.trans hZ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z Bs) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z_prime Bs) hs'
  have hlaw := Dx2.VV.orbJ_pt Bs (PBJ.bigPt d) hl hγ hZ hpos hhA hnA hfA hhB hnB hfB F
  rw [← hγs] at hlaw
  have hw : (hl.2 ▸ D.ptPerm (PBJ.bigPt d) : Equiv.Perm (Fin (r + 1))) = 1 :=
    PBM.cast_perm_eq_one _ _ (PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Dx2.VV.ptMatN_monoP' (PBJ.bigPt d) (r + 1) hl.2 hl.1
  rw [hw] at hmono hlaw
  rw [PBM.orbJ_one_eq Bs hγ' hpos' hnz (hZ'.trans hmono) F, PBM.orbJ_one_eq Bs hγ hpos hnz (hZ.trans hmono) F] at hlaw
  rw [← hlaw, CutBP.hsVec_norm_CinL Bs hhA hhB]

theorem normSq_sec (hk : 2 ≤ k) (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r Bs.z Bs.z' μsec) :
    B.normSq Bs F = jNormSq k r (Tz k r Bs.z) (Tz k r Bs.z')
      fun q => Real.sqrt (hsNormSq (B.JF Bs F (bigCell k r q.1 (μsec q.2)))) := by
  unfold B.normSq jNormSq
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hc, hζ⟩ := Formalism.MainNotions.S.Pv.LemmaJ.bcWeight_ne hk hw0
  have hζ0 : q.2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact absurd (mul_pos Bs.T_pos Bs.T'_pos) (not_lt.2 hζ.le)
  obtain ⟨d, hd1, hd2⟩ : ∃ d : Fin (r + 1) → ℂ, (fun i : Fin r => d i.castSucc) = q.1 ∧ d (Fin.last r) = q.2 :=
    ⟨Fin.snoc q.1 q.2, by funext i; simp, by simp⟩
  have hd : ∀ a, d a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [hd2]; exact hζ0
    · rw [congrFun hd1 i]; exact hc i
  have hZ := PBM.zhat_bigCell_pt Bs d (by rw [hd2]; exact hζ)
  have hZ' := PBM.zhat_bigCell_pt { Bs with μsec := μsec, sec := hsec } d (by rw [hd2]; exact hζ)
  rw [hd1, hd2] at hZ hZ'
  have e := norm_JF_eq Bs F d hd (bigCellMem k r _ _ hc (Bs.sec.2 _ hζ).1) (bigCellMem k r _ _ hc (hsec.2 _ hζ).1) hZ hZ'
    (Formalism.MainNotions.S.Pv.LemmaJ.Gf_big Bs.z_mem Bs.z'_mem Bs.sec q.1 hc q.2 hζ)
  congr 2
  rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_nonneg _), Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_eq]
  change ‖B.hsVec (B.JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))‖ ^ 2 = _
  rw [e, PiLp.norm_sq_eq_of_L2]
  rfl

end energy

theorem energy_identity : EnergyTie := by
  intro k r L f μsec u u' p _ hc _ _ htie _ _ hsec
  obtain ⟨hz, hz', hπ, hπ', hW, hN, hW'⟩ := htie
  have e : TBB.jN2 p f = jNorm2 L f μsec := by
    refine (GlobalTheory.T.jN2_eq_normSq_base (parOfL L u u') L.Wp L.Wq p f).trans ?_
    have h := normSq_sec (k := k) (r := r) p.hl.2.2 p.T.base f μsec (by
      have e1 : (p.T.base.z : Fin (2 * r + k + 1) → ℂ) = L.z := hz
      have e2 : (p.T.base.z' : Fin (2 * r + k + 1) → ℂ) = L.z' := hz'
      exact e1 ▸ e2 ▸ hsec)
    refine h.trans ?_
    unfold jNorm2 LocBessel.J B.JF
    rw [hc]
    simp only [hz, hz', hπ, hπ', hW, hN, hW']
  rw [e]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact one_le_pow₀ (by linarith [Real.pi_gt_three])

section scale

variable {k r : ℕ}

@[reducible] def withN (L : LocBessel k r) (κ : ℝ≥0∞) : LocBessel k r := { L with κN := κ }

theorem pairMeas_smul (L : LocBessel k r) (κ s : ℝ≥0∞) (h : L.μN = s • (withN L κ).μN) :
    pairMeas L = (s * s) • pairMeas (withN L κ) := by
  have i1 : SFinite (withN L κ).μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have i2 : SigmaFinite L.μW := L.hμW.1.1
  have i3 : SigmaFinite L.μW' := L.hμW'.1.1
  unfold pairMeas
  rw [h]
  change (L.μW.prod (s • (withN L κ).μN)).prod (L.μW'.prod (s • (withN L κ).μN)) =
    (s * s) • (L.μW.prod (withN L κ).μN).prod (L.μW'.prod (withN L κ).μN)
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]

theorem orbSq_le (L : LocBessel k r) (κ s : ℝ≥0∞) (hs0 : s ≠ 0) (hs : s ≠ ⊤)
    (h : pairMeas L = s • pairMeas (withN L κ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) :
    orbSq L f γ ≤ ENNReal.ofReal (s.toReal ^ 2) * orbSq (withN L κ) f γ := by
  unfold orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hc => ?_
  have hq : IsOrbQuot (withN L κ) g μR (s⁻¹ • ν) := by
    intro φ hφ
    have e := hc.2.2.2 φ hφ
    rw [h, lintegral_smul_measure] at e
    rw [lintegral_smul_measure, ← e, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hs0 hs, one_mul]
  have e : OrbInt L f g ν = ((s.toReal : ℝ) : ℂ) • OrbInt (withN L κ) f g (s⁻¹ • ν) := by
    have e1 : ν = s • (s⁻¹ • ν) := by rw [smul_smul, ENNReal.mul_inv_cancel hs0 hs, one_smul]
    unfold OrbInt
    conv_lhs => rw [e1, integral_smul_measure]
    rw [Complex.coe_smul]
    rfl
  rw [e, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le (s⁻¹ • ν) (le_iSup_of_le ⟨hc.1, hc.2.1, hc.2.2.1, hq⟩ le_rfl)))

theorem jNorm2_eq (L : LocBessel k r) (κ s : ℝ≥0∞) (h : pairMeas L = s • pairMeas (withN L κ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    jNorm2 L f μsec = ENNReal.ofReal (s.toReal ^ 2) * jNorm2 (withN L κ) f μsec := by
  have hJ : ∀ g, L.J f g = ((s.toReal : ℝ) : ℂ) • (withN L κ).J f g := fun g => by
    change ∫ x, besselIntg L f g x ∂(pairMeas L) = _ • ∫ x, besselIntg L f g x ∂(pairMeas (withN L κ))
    rw [h, integral_smul_measure, Complex.coe_smul]
  rw [Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold Formalism.MainNotions.BesselShellMomentBounds.dens
  rw [hJ, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change _ = _ * (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * _)
  ring

end scale

end CompanionTheory.WaveGrid.Ties
end
end

section
noncomputable section

namespace CompanionTheory.WaveGrid.WGlue

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.TheoremBConstants
  Formalism.MainNotions.BigCellDensity Formalism.L2.SG.Pf.BesselExpansion
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Tied
open scoped ENNReal

def WIneq {k r : ℕ} (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (γ : Point ℂ (r + 1)) (w K : ℝ) : Prop :=
  ENNReal.ofReal (w * ptWeight k r (Tz k r L.z) (Tz k r L.z') γ) * orbSq L f γ ≤ ENNReal.ofReal K * jNorm2 L f μsec

def WLoc1 (D : D7) (Ch Cg Ca C : ℝ) (N : LocBessel D.R.k D.R.rS → Prop) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), N L → LocOk D Ch Cg L L.lam ka b 1 →
    AllGaps L.lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ (l : Fin (D.R.rS + 1)) (a : ℕ), (a : ℝ) ≤ Ca * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 → ∀ γ : Point ℂ (D.R.rS + 1),
      Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 →
      WIneq L f μsec γ (‖Dpt γ l‖ ^ (2 * a)) (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) *
        max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) ^ (40 * (D.R.rS + 1) ^ 2))

set_option maxHeartbeats 1600000 in
theorem wLoc1N_of (hW : ∀ Cb, WEnd.WBp Cb) {Cgc : ℝ} (hCC : CoefCC1 Cgc) (Ch Ca : ℝ) :
    ∃ C Cg₀ : ℝ, 0 ≤ C ∧ ∀ Cg, Cg₀ ≤ Cg → ∀ D : D7,
      WLoc1 D Ch Cg Ca C fun L => L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS := by
  obtain ⟨Cb, hPl⟩ := TypeHC.exists_place
  obtain ⟨C₅, Cg₁, hC5, H⟩ := hW Cb (2 * |Ch|) Ca (by positivity)
  refine ⟨C₅ + 8, max (max Cg₁ Cgc) 1000, by linarith, ?_⟩
  intro Cg hCg D L f μsec ka b hμN hL hg4 hf hsec l a ha γ hG
  have g1 : Cg₁ ≤ Cg := le_trans (le_max_of_le_left (le_max_left _ _)) hCg
  have g2 : Cgc ≤ Cg := le_trans (le_max_of_le_left (le_max_right _ _)) hCg
  have g3 : 1000 ≤ Cg := le_trans (le_max_right _ _) hCg
  unfold WIneq
  by_cases h0 : orbSq L f γ = 0
  · simp [h0]
  obtain ⟨hk1, hε, hc, hN0, hNt, hStd, hT1, hT1'⟩ := hL
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk1 hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  obtain ⟨hlam, hI, hI', hka, hka1, -, -, -, hTle, hTle', hlamb, hub, hub', -, hgap, ⟨bv, hbv, hshape⟩, hcut⟩ := hStd
  have hk2 : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hε' : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]
    funext i
    simp [PI.BesselPeriodGGP.eps48, epsSH, epsS]
  clear hε
  rw [one_pow, mul_one] at hT1 hT1'
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hcStd : L.c = cStd := by rw [hc]; exact Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one
  have hInCC := hCC D.R.k D.R.rS L f hk1 hf (Formalism.L2.SG.Pf.BesselExpansion.gap_mono hgap
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g2 (by positivity)) (by positivity)))
  have hok := GapSizes.gapOK_of D.R.k D.R.rS hk1 Cg g3
  rw [mul_assoc] at hgap hok
  have hu := GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW (z := L.z) (u := L.u) (π := L.π) L.hπ
  have hu' := GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW (z := L.z') (u := L.u') (π := L.π') L.hπ'
  have hTy := hypType_of hk1 hlam hu hI hub
  have hTy' := hypType_of hk1 hlam hu' hI' hub'
  obtain ⟨hcl, hnd⟩ := shape_of hk1 hlam hu hI hshape
  have hPOK : (parOfL L (lamN L.u) (lamN L.u')).OK :=
    Inhab.ok_diff (parOfL L (lamN L.u) (lamN L.u')) hk1 L.hz.2 L.hz'.2 L.lam b hlam hTy hTy'
  have hplace : Formalism.FourierDecayAlt.Q.IsPlace (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π L.π' :=
    ⟨hPOK, L.hz.1, L.hz'.1, rfl, rfl, TypeHC.isType_of_hc L.hz.1 L.hz.2 L.hπ (lamN_succ L.u),
      TypeHC.isType_of_hc L.hz'.1 L.hz'.2 L.hπ' (lamN_succ L.u')⟩
  have hW := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 D.R.k D.R.rS L.z L.μW L.hz.1 L.hz.2 L.hμW.1
  have hW' := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 D.R.k D.R.rS L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1
  have hfK : Formalism.FourierDecayAlt.P.CutBP.KFinDSCoef (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam f := by
    obtain ⟨Pm, Qm, h1, h2, h3⟩ := hf
    exact ⟨L.Hs, _, _, _, L.σ, Pm, Qm, L.hlam, hε' ▸ L.hσ, h1, h2, fun g _ => h3 g⟩
  have hr2 : 36 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ Cg * ((D.R.rS : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hr1 : 1 ≤ ((D.R.rS : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg D.R.rS : (0 : ℝ) ≤ D.R.rS)]
  obtain ⟨pl, ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩, hcase⟩ :
      ∃ pl : Formalism.FourierDecayAlt.KB.Pl (parOfL L (lamN L.u) (lamN L.u')) L.Wp L.Wq, PlTie L pl ∧
        ((30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 ≤ |lamN L.u pl.l0 - lamN L.u' pl.l0| ∧
          Formalism.FourierDecayAlt.KB.InDDplus2 _ pl.l0 pl.T.base Cb pl.Θ) ∨
        (lamN L.u = lamN L.u' ∧ ∃ l, 1 ≤ l ∧ l < D.R.k ∧
          2 * (30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6) + 1 ≤ lamN L.u l - lamN L.u (l + 1))) := by
    rcases hcut with ⟨huu, i, hi, hposition, -⟩ | ⟨-, x, y, ⟨i, x', y', -, hxy, hIcc, hx, hy, -⟩, hlen⟩
    · obtain ⟨p, -, e1, e2, e3, e4, e5, e6, e7, -⟩ := hPl L.Wp L.Wq (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π
        L.π' L.μW L.μW' 1 hplace hk2 le_rfl hk1 hW L.hμW.2 hW' L.hμW'.2
      refine ⟨p, ⟨e1, e2, e3, e4, e5, e6.trans hμN.symm, e7⟩, Or.inr ⟨congrArg lamN huu, i + 1, by omega, hi, ?_⟩⟩
      rw [lamN_succ L.u ⟨i, by omega⟩, lamN_succ L.u ⟨i + 1, hi⟩]
      linarith only [hposition, hr1, hr2]
    · obtain ⟨p, e0, e1, e2, e3, e4, e5, e6, e7, hDD⟩ := hPl L.Wp L.Wq (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π
        L.π' L.μW L.μW' (i + 1) hplace hk2 (by omega) i.isLt hW L.hμW.2 hW' L.hμW'.2
      refine ⟨p, ⟨e1, e2, e3, e4, e5, e6.trans hμN.symm, e7⟩, Or.inl ⟨?_, hDD⟩⟩
      rw [e0, lamN_succ L.u i, lamN_succ L.u' i]
      have hxy0 : x ≤ y := by linarith only [hlen, hr1, hr2]
      have h1 : x ∈ Set.Icc x' y' := hIcc ▸ ⟨le_rfl, hxy0⟩
      have h2 : y ∈ Set.Icc x' y' := hIcc ▸ ⟨hxy0, le_rfl⟩
      have h3 := max_sub_min_eq_abs (-L.u i) (-L.u' i)
      rw [show -L.u' i - -L.u i = L.u i - L.u' i by ring] at h3
      linarith only [h1.1, h2.2, hx, hy, h3, hlen, hr1, hr2]
  obtain ⟨g, hg⟩ := exists_relrep L f γ h0
  have hG0 := GPoint_nonneg_of_rep L γ g hg.1
  have hGpos : 0 < Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := lt_of_le_of_ne hG0 (Ne.symm hG)
  have hloc := isLocPt_swap γ
  have hTT : Formalism.FourierDecayAlt.TBB.TTp pl = Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' := by
    unfold Formalism.FourierDecayAlt.TBB.TTp; rw [hz, hz']; rfl
  have hGeq : Formalism.FourierDecayAlt.TBB.Gp pl (γ.1.map Prod.swap) = Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold Formalism.FourierDecayAlt.TBB.Gp; rw [hTT]; exact ptG_eq_GPoint _ _ γ
  have hB := H Cg g1 (parOfL L (lamN L.u) (lamN L.u')) L.Wp L.Wq pl f L.lam b bv l (Nat.le_of_lt_succ l.isLt) a hfK
    hTy hTy' hcl hnd hlamb hbv (fun s s' h => gap_of_lt hlam hg4 h) (hε' ▸ hgap) hok hT1 hT1'
    (scaled_le D.R.rS hb1 hka hka1 hTle) (scaled_le D.R.rS hb1 hka hka1 hTle') hcase ha _ hloc (by rw [hGeq]; exact hGpos)
  have hm : MomL.mnr (Nat.le_of_lt_succ l.isLt) (γ.1.map Prod.swap) = Dpt γ l := by
    unfold MomL.mnr Dpt leadMinor
    rw [ptMatN_swap]
  have hwt := weightTie D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ hk1
  have hn0 : 0 ≤ ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold ptWeight
    exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => (γ.2.1 b hb).2) (by rw [Nat.zero_add]; exact γ.2.2)
      (fun t ht => last_ok_of_G _ _ _ hG0 t ht)
  have hnPt : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Formalism.FourierDecayAlt.TBB.TTp pl) (γ.1.map Prod.swap) := by
    rw [hTT, ← hwt]; exact hn0
  have hEw : Formalism.FourierDecayAlt.TBB.Ew pl (fun _ => 1) f (D.R.rS + 1) [] (γ.1.map Prod.swap) =
      Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Formalism.FourierDecayAlt.TBB.TTp pl) (γ.1.map Prod.swap) *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV pl.T.base pl.ν' pl.m₀ f (γ.1.map Prod.swap))
          (Formalism.FourierDecayAlt.D.vecV pl.T.base pl.ν' pl.m₀ f (γ.1.map Prod.swap))).re := ew_top pl f (γ.1.map Prod.swap) hloc hnPt
  rw [hTT, ← hwt] at hEw
  have hX := tieTopXk D.R.k D.R.rS hk1 L pl.T.base pl.ν' pl.m₀ hcStd hN0 hNt hz hz' hπ hπ' hμW hμN' hμW' pl.hF f γ
    hf hInCC hGpos ⟨g, hg⟩
  have hJ := Ties.energy_identity D.R.k D.R.rS L f μsec _ _ pl hk1 hcStd hN0 hNt ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩ hf hInCC
    hsec
  have hπb : Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) ≤ b ^ (4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) := by
    have h1 : Real.pi ≤ b ^ 2 := by nlinarith [Real.pi_lt_four]
    refine (pow_le_pow_left₀ Real.pi_pos.le h1 _).trans ?_
    rw [← pow_mul, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have h2 : ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + 2)) (by norm_num)
    push_cast at h2 ⊢
    linarith
  have hpc : Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc D.R.rS (γ.1.map Prod.snd)) ≤ Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) := by
    refine pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) ?_
    have := pc_le D.R.rS (γ.1.map Prod.snd)
    nlinarith
  change ENNReal.ofReal (‖MomL.mnr (Nat.le_of_lt_succ l.isLt : (l : ℕ) ≤ D.R.rS) _‖ ^ (2 * a) * Formalism.FourierDecayAlt.TBB.Ew pl _ f (D.R.rS + 1) [] _) ≤
    ENNReal.ofReal (b ^ (C₅ * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / Formalism.FourierDecayAlt.TBB.Gp pl _) ^ (40 * (D.R.rS + 1) ^ 2)) *
      Formalism.FourierDecayAlt.TBB.jN2 pl f at hB
  rw [hm, hGeq] at hB
  rw [hEw] at hB
  rw [hX, ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hn0), mul_left_comm, ENNReal.ofReal_mul (by positivity),
    mul_assoc]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (hpc.trans hπb))
    (hB.trans (mul_le_mul' le_rfl (hJ.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hπb) le_rfl))))).trans (le_of_eq ?_)
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [show (C₅ + 8) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 = 4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 + C₅ * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 +
    4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 by ring, Real.rpow_add hb0, Real.rpow_add hb0]
  ring

theorem wLoc1_of_N {D : D7} {Ch Cg Ca C : ℝ}
    (H : WLoc1 D Ch Cg Ca C fun L => L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS) : WLoc1 D Ch Cg Ca C fun _ => True := by
  intro L f μsec ka b _ hok hg hf hsec l a ha γ hγ
  obtain ⟨c, hc0, hc1, hc⟩ := Formalism.MainNotions.BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS)
    (Formalism.FourierDecayAlt.P.nilpotent_measure_is_haar D.R.k D.R.rS) (Formalism.MainNotions.BridgeCSB.haarLieN D.R.k D.R.rS 1 one_ne_zero ENNReal.one_ne_top)
  have hsm : ∀ κ : ℝ≥0∞, haarLie (Nset D.R.k D.R.rS) κ = κ • haarLie (Nset D.R.k D.R.rS) 1 := fun κ => by
    simp [haarLie]
  have h1 : (Ties.withN L c⁻¹).μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS := by
    change haarLie _ c⁻¹ = _
    rw [hsm, hc, smul_smul, ENNReal.inv_mul_cancel hc0 hc1, one_smul]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hok
  have h2 : L.μN = (L.κN * c) • (Ties.withN L c⁻¹).μN := by
    rw [h1, ← smul_smul, ← hc]
    exact hsm _
  have hs0 : L.κN * c ≠ 0 := mul_ne_zero a4.ne' hc0
  have hs1 : L.κN * c ≠ ⊤ := ENNReal.mul_ne_top a5 hc1
  have h3 := Ties.pairMeas_smul L c⁻¹ _ h2
  have hB := H (Ties.withN L c⁻¹) f μsec ka b h1
    ⟨a1, a2, a3, ENNReal.inv_pos.2 hc1, ENNReal.inv_ne_top.2 hc0, a6⟩ hg hf hsec l a ha γ hγ
  unfold WIneq at hB ⊢
  rw [Ties.jNorm2_eq L c⁻¹ _ h3 f μsec]
  calc _ ≤ _ * (_ * orbSq (Ties.withN L c⁻¹) f γ) :=
        mul_le_mul' le_rfl (Ties.orbSq_le L c⁻¹ _ (mul_ne_zero hs0 hs0) (ENNReal.mul_ne_top hs1 hs1) h3 f γ)
    _ = _ * (_ * orbSq (Ties.withN L c⁻¹) f γ) := mul_left_comm _ _ _
    _ ≤ _ * (_ * jNorm2 (Ties.withN L c⁻¹) f μsec) := mul_le_mul' le_rfl hB
    _ = _ := mul_left_comm _ _ _

theorem dpt_le {r : ℕ} {ka B : ℝ} (hka : 0 < ka) (h1 : ka ≤ B) (h2 : ka⁻¹ ≤ B) (hB : 1 ≤ B) (γ : Point ℂ (r + 1))
    (l : Fin (r + 1)) : ‖Dpt γ l‖ ≤ B ^ (2 * r + 2) ^ 2 *
      ‖Dpt (Formalism.MainNotions.FrameBoundFromBesselTorus.ptTr ka⁻¹ (ka ^ r) (inv_pos.2 hka) (pow_pos hka _) γ) l‖ := by
  unfold Dpt
  rw [Formalism.MainNotions.FrameBoundFromBesselTorus.leadMinor_ptTr, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  have key : ∀ a : ℕ, 1 ≤ B ^ (4 * r) * Formalism.MainNotions.FrameBoundFromBesselTorus.tF r ka⁻¹ (ka ^ r) a ^ 2 := fun a => by
    unfold Formalism.MainNotions.FrameBoundFromBesselTorus.tF
    have e1 : 1 ≤ B * ka := by
      have := mul_le_mul_of_nonneg_right h2 hka.le
      rwa [inv_mul_cancel₀ hka.ne'] at this
    have e2 : 1 ≤ B * ka⁻¹ := by
      have := mul_le_mul_of_nonneg_right h1 (inv_pos.2 hka).le
      rwa [mul_inv_cancel₀ hka.ne'] at this
    have e3 : 1 ≤ B ^ r * ka⁻¹ ^ (r - a) :=
      (one_le_pow₀ e2 (n := r - a)).trans (by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (Nat.sub_le _ _)) (by positivity))
    have e4 : 1 ≤ (B * ka) ^ r * (B ^ r * ka⁻¹ ^ (r - a)) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ e1) e3
    calc (1 : ℝ) ≤ ((B * ka) ^ r * (B ^ r * ka⁻¹ ^ (r - a))) ^ 2 := one_le_pow₀ e4
      _ = _ := by ring
  set S := Finset.univ.filter fun a : Fin (r + 1) => a.val < l.val + 1
  have hc : S.card ≤ r + 1 := (Finset.card_filter_le _ _).trans (by simp)
  have h3 : 1 ≤ ∏ a ∈ S, B ^ (4 * r) * Formalism.MainNotions.FrameBoundFromBesselTorus.tF r ka⁻¹ (ka ^ r) a ^ 2 :=
    le_trans (by simp) (Finset.prod_le_prod (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) fun a _ => key a)
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul] at h3
  refine h3.trans (mul_le_mul (pow_le_pow_right₀ hB ?_) (le_abs_self _)
    (Finset.prod_nonneg fun _ _ => sq_nonneg _) (by positivity))
  nlinarith

theorem w_in_frame {D : D7} {Ch Cg Cgf Ca C : ℝ} (hFr : FrameBesselBound D Cgf 2) (H : WLoc1 D Ch Cg Ca C fun _ => True)
    (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ) (hL : LocOk D Ch Cg L L.lam ka b ka)
    (hg4 : AllGaps L.lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) (hgap : GapFr D Cgf L.ε L.lam) (hB1 : 1 ≤ b ^ Ch)
    (hf : IsKFinCoefH L.σ f) (hsec : IsSection D.R.k D.R.rS L.z L.z' μsec) (l : Fin (D.R.rS + 1)) (a : ℕ)
    (ha : (a : ℝ) ≤ Ca * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) (γ : Point ℂ (D.R.rS + 1))
    (hG : Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0) :
    WIneq L f μsec γ (‖Dpt γ l‖ ^ (2 * a)) (((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) * (FrC D 2 ka *
      (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / (GsC D ka * Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ)) ^
        (40 * (D.R.rS + 1) ^ 2)))) := by
  obtain ⟨hk, hε, hc, hκ0, hκt, hStd, hT1, hT1'⟩ := hL
  have hka : 0 < ka := hStd.2.2.2.1
  have hτ : 0 < ka ^ D.R.rS := pow_pos hka _
  obtain ⟨L₁, f₁, e1, e2, e3, e4, e5, e6, e7, e8, e9, hf₁, hrest⟩ :=
    hFr L f ka ka⁻¹ (ka ^ D.R.rS) hka (inv_pos.2 hka) hτ hc hκ0 hκt hε hgap hf
  obtain ⟨μsec₁, hsec₁, K₁, hK₁, hJ₁, hpt⟩ := hrest μsec hsec
  obtain ⟨γ₁, hγ₁, hG₁, -, hle⟩ := hpt γ hG
  have hγe : γ₁ = Formalism.MainNotions.FrameBoundFromBesselTorus.ptTr ka⁻¹ (ka ^ D.R.rS) (inv_pos.2 hka) hτ γ := Subtype.ext hγ₁
  have hsq : (ka ^ D.R.rS) ^ 2 = ka ^ (2 * D.R.rS) := by rw [← pow_mul, mul_comm]
  have hinv : ka ^ (2 * D.R.rS) * (1 / ka) ^ (2 * D.R.rS) = 1 := by
    rw [← mul_pow, mul_one_div, div_self hka.ne', one_pow]
  have hone : (ka / ka) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hL₁ : LocOk D Ch Cg L₁ L₁.lam ka b 1 := by
    refine ⟨hk, e1.trans hε, ?_, e6, e7, ?_, ?_, ?_⟩
    · rw [e5, inv_mul_cancel₀ hka.ne']
    · rw [e1, e2, e3, e4, e8, e9, hsq]
      have a1 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      have a2 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z' * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z' * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      rw [a1, a2]
      exact hStd
    · rw [e8, hsq, one_pow, mul_one, mul_comm]; exact hT1
    · rw [e9, hsq, one_pow, mul_one, mul_comm]; exact hT1'
  have hG₁0 : Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ ≠ 0 := by
    rw [hG₁]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hka.ne')) (pow_ne_zero _ hτ.ne')) hG
  have hB := H L₁ f₁ μsec₁ ka b trivial hL₁ (e2 ▸ hg4) hf₁ hsec₁ l a ha γ₁ hG₁0
  unfold WIneq at hB ⊢
  rw [hG₁, hJ₁, ENNReal.ofReal_mul (by positivity), mul_assoc] at hB
  have hD : ‖Dpt γ l‖ ^ (2 * a) ≤ ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) * ‖Dpt γ₁ l‖ ^ (2 * a) := by
    rw [← mul_pow, hγe]
    exact pow_le_pow_left₀ (norm_nonneg _) (dpt_le hka hStd.2.2.2.2.1 hStd.2.2.2.2.2.1 hB1 γ l) _
  have hK0 : ENNReal.ofReal K₁ ≠ 0 := (ENNReal.ofReal_pos.2 hK₁).ne'
  have hF0 : 0 ≤ FrC D 2 ka := FrC_nonneg D 2 ka hka
  have hX0 : (0 : ℝ) ≤ ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) := by positivity
  rw [← ENNReal.mul_le_mul_iff_right hK0 ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity), mul_assoc,
    mul_left_comm]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hD) hle).trans ?_
  rw [ENNReal.ofReal_mul hX0, mul_assoc, mul_left_comm (ENNReal.ofReal (‖Dpt γ₁ l‖ ^ (2 * a)))]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hB)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hX0, ENNReal.ofReal_mul hF0]
  unfold FrC GsC
  ring

theorem weight_le {ι : Type} [Fintype ι] [Nonempty ι] (s x : ι → ℝ) (N : ι → ℕ) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs0 : ∀ l, 0 ≤ s l) (hs : ∀ l, s l ≤ σ) :
    ∃ (l : ι) (a : ℕ), a ≤ 2 * ∑ l, N l ∧ (∏ l, (1 + s l * x l ^ 2) ^ N l) ^ 2 ≤ (2 * σ) ^ (2 * ∑ l, N l) * x l ^ (2 * a) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => x l ^ 2) Finset.univ_nonempty
  have key : ∀ M : ℝ, 1 ≤ M → x l ^ 2 ≤ M → (∏ i, (1 + s i * x i ^ 2) ^ N i) ^ 2 ≤ (2 * σ * M) ^ (2 * ∑ i, N i) := by
    intro M hM hx
    rw [mul_comm 2 (∑ i, N i), pow_mul, ← Finset.prod_pow_eq_pow_sum]
    have hn : ∀ i, 0 ≤ 1 + s i * x i ^ 2 := fun i => add_nonneg zero_le_one (mul_nonneg (hs0 i) (sq_nonneg _))
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => pow_nonneg (hn i) _)
      (Finset.prod_le_prod (fun i _ => pow_nonneg (hn i) _) fun i _ => pow_le_pow_left₀ (hn i) ?_ _) 2
    have h1 : s i * x i ^ 2 ≤ σ * M := mul_le_mul (hs i) ((hl i (Finset.mem_univ _)).trans hx) (sq_nonneg _) (by linarith)
    have h2 : 1 ≤ σ * M := one_le_mul_of_one_le_of_one_le hσ hM
    linarith
  rcases le_total (x l ^ 2) 1 with h | h
  · exact ⟨l, 0, Nat.zero_le _, by simpa using key 1 le_rfl h⟩
  · refine ⟨l, _, le_rfl, (key _ h le_rfl).trans (le_of_eq ?_)⟩
    rw [mul_pow (2 * σ), ← pow_mul]

set_option maxHeartbeats 1600000 in

theorem weighted_uniform_rotated_of_expansion_alt_alt (hW : ∀ Cb, WEnd.WBp Cb) {Cgc Cgf : ℝ} (hCC : CoefCC1 Cgc)
    (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform := by
  intro Aw Ch hAw
  obtain ⟨C, Cg₀, hC, H⟩ := wLoc1N_of hW hCC Ch (2 * (1 + Aw + 10))
  refine ⟨((4 + |Ch|) * (2 * (1 + Aw + 10)) + |Ch| * (4 * (1 + Aw + 10)) + 4 * |Ch| + C + (3 + 3 * |Ch|) * 10) + 6,
    max (max Cg₀ Cgf) 2, fun Cg hCg0 D => ?_⟩
  have g1 : Cg₀ ≤ Cg := le_trans (le_max_of_le_left (le_max_left _ _)) hCg0
  have g2 : Cgf ≤ Cg := le_trans (le_max_of_le_left (le_max_right _ _)) hCg0
  have hCg : 2 ≤ Cg := le_trans (le_max_right _ _) hCg0
  have hFr := Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D)
  have H1 := wLoc1_of_N (H Cg g1 D)
  refine Formalism.MainNotions.RotatedPoints.weighted_bound_rotated_of_one_place (A := AQ D 10) hCg ?_
  intro T T' b X hP γ hγ v
  set A := AQ D 10 with hAd
  set p : ℝ := Aw * ((D.R.rS : ℝ) + 1) ^ 2 with hpd
  have hp : 0 ≤ p := by positivity
  by_cases hO : orbSq (X.L v) (X.f v) (Pv.Frames.turnPt (ptLoc D v γ)) = 0
  · rw [hO, mul_zero]; exact bot_le
  have hL := X.hL v
  obtain ⟨hk, -, -, -, -, hStd, -, -⟩ := id hL
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  set xG : ℝ := Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
    (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) with hxGd
  have hxG : plEmb D v (Gglob D T T' γ) = (xG : ℂ) := plEmb_Gglob D T T' v γ
  have hxG0 : xG ≠ 0 := by
    intro h0
    have : plEmb D v (Gglob D T T' γ) = 0 := by rw [hxG, h0]; simp
    exact hγ.2.1 ((map_eq_zero (plEmb D v)).1 this)
  have habs : absV D v (Gglob D T T' γ) = |xG| := by
    unfold absV; rw [hxG, Complex.norm_real, Real.norm_eq_abs]
  have hGreal : Gpt (T : ℝ) (T' : ℝ) (ptLoc D v γ) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 * xG :=
    GPoint_loc D T T' v γ
  have ha4 : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
    positivity
  have hGne : Gpt (Tz D.R.k D.R.rS (X.L v).z) (Tz D.R.k D.R.rS (X.L v).z') (Pv.Frames.turnPt (ptLoc D v γ)) ≠ 0 := by
    rw [Pv.Frames.GPoint_turnPt, (X.hT v).1, (X.hT v).2, hGreal]
    exact mul_ne_zero ha4.ne' hxG0
  obtain ⟨g, hg⟩ := exists_rep_of_orbSq _ _ _ hO
  have hGnn := GPoint_nonneg_of_rep _ _ g hg
  rw [Pv.Frames.GPoint_turnPt, (X.hT v).1, (X.hT v).2] at hGnn
  have hxGnn : 0 ≤ xG := by
    rw [hGreal] at hGnn
    exact nonneg_of_mul_nonneg_right hGnn ha4
  have hGd : absV D v (Gglob D T T' γ) ≤ dLoc D v γ := by
    rw [habs, abs_of_nonneg hxGnn]
    unfold dLoc absV
    rw [← Complex.normSq_eq_norm_sq]
    have : 0 ≤ (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) := by
      have := Complex.normSq_nonneg (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))
      positivity
    linarith
  have hn0 : 0 ≤ nLoc D T T' v γ := by
    unfold nLoc ptWeight
    exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => ((ptLoc D v γ).2.1 b hb).2)
      (by rw [Nat.zero_add]; exact (ptLoc D v γ).2.2)
      (fun t ht => last_ok_of_G _ _ _ hGnn t ht)
  have hb0 : 0 < b := by linarith
  have hCh : 0 ≤ Ch := ch_nonneg hCg ⟨X.hL v, X.hnear v, X.hcoef v, X.hsec v, X.hT v⟩
  rw [abs_of_nonneg hCh]
  have hlam := lam_eq_of_dist0 D X v
  have hgF : GapFr D Cgf (X.L v).ε (X.L v).lam := by
    rw [hlam]
    exact Formalism.L2.SG.Pf.BesselExpansion.gap_mono hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g2 (by positivity)) (by positivity))
  set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + 2)
  have hσ1 : 1 ≤ b ^ ((3 + Ch) * M ^ 2) := Real.one_le_rpow hb1 (by positivity)
  obtain ⟨l, a, ha, hwt⟩ := weight_le (sQ D) (fun l => ‖Dpt (ptLoc D v γ) l‖) (Formalism.MainNotions.TheoremBConstants.NQ D A p) _ hσ1 (sQ_nonneg D)
    fun l => alfProd_inv_le_b D Ch b hCh hb2 hka hk2 _ (by omega)
  simp only [Fl_eq] at hwt
  have hSN := sum_weighted_point_counts_le_cube D Aw 10 hAw (by norm_num)
  have hS2 : ((2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l : ℕ) : ℝ) ≤ 2 * (1 + Aw + 10) * M ^ 3 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have : ((∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l : ℕ) : ℝ) ≤ (1 + Aw + 10) * M ^ 3 := hSN
    linarith only [this]
  have ha' : (a : ℝ) ≤ 2 * (1 + Aw + 10) * M ^ 3 := le_trans (by exact_mod_cast ha) hS2
  have hloc := w_in_frame hFr H1 (X.L v) (X.f v) (X.μsec v) (kaRe D) b (hlam ▸ hL) (hP v) hgF
    (Real.one_le_rpow hb1 hCh) (X.hcoef v) (X.hsec v) l a ha' (Pv.Frames.turnPt (ptLoc D v γ)) hGne
  unfold WIneq at hloc
  simp only [Dpt_norm_turnPt, Pv.Frames.ptWeight_turnPt, Pv.Frames.GPoint_turnPt] at hloc
  rw [(X.hT v).1, (X.hT v).2, hGreal] at hloc
  have hw := weights_le D T T' v γ A p hp hGd
  have h1 : wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p ≤
      (∏ l, Fl D v γ l ^ Formalism.MainNotions.TheoremBConstants.NQ D A p l) ^ 2 * nLoc D T T' v γ := by
    calc wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p
        = (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * WLoc D T T' v γ ^ p) * nLoc D T T' v γ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hw hn0
  have hY0 : 0 ≤ (2 * b ^ ((3 + Ch) * M ^ 2)) ^ (2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l) := by positivity
  have h2 := h1.trans ((mul_le_mul_of_nonneg_right hwt hn0).trans (le_of_eq (mul_assoc _ _ _)))
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl).trans ?_
  rw [ENNReal.ofReal_mul hY0, mul_assoc]
  refine (mul_le_mul' le_rfl hloc).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hY0]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hM25 : M ^ 2 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM45 : M ^ 4 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have n1 : (2 * b ^ ((3 + Ch) * M ^ 2)) ^ (2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l) ≤ b ^ ((4 + Ch) * (2 * (1 + Aw + 10)) * M ^ 5) := by
    have e1 : 2 * b ^ ((3 + Ch) * M ^ 2) ≤ b ^ ((4 + Ch) * M ^ 2) := by
      rw [show (4 + Ch) * M ^ 2 = M ^ 2 + (3 + Ch) * M ^ 2 by ring, Real.rpow_add hb0]
      refine mul_le_mul_of_nonneg_right (hb2.trans ?_) (by positivity)
      simpa using bp_mono hb1 hM2
    refine (bp_pow hb0 e1 (by positivity) _).trans (bp_mono hb1 ?_)
    calc _ ≤ (4 + Ch) * M ^ 2 * (2 * (1 + Aw + 10) * M ^ 3) := mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = _ := by ring
  have n2 : ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) ≤ b ^ (Ch * (4 * (1 + Aw + 10)) * M ^ 5) := by
    refine (bp_pow hb0 (bp_pow hb0 le_rfl (by positivity) _) (by positivity) _).trans (bp_mono hb1 ?_)
    rw [Nat.cast_pow, ← hM, Nat.cast_mul, Nat.cast_ofNat]
    calc _ ≤ Ch * M ^ 2 * (2 * (2 * (1 + Aw + 10) * M ^ 3)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have n3 : FrC D 2 (kaRe D) ≤ b ^ (4 * Ch * M ^ 5) :=
    (num_Fr D Ch 2 b (kaRe D) hCh (by norm_num) hb2 hka hk1 hk2).trans
      (bp_mono hb1 (by nlinarith [mul_le_mul_of_nonneg_left hM25 hCh]))
  have n4 := num_G D Ch 10 b hCh (by norm_num) hb2 hka hk1 hk2 A (AQ_ge D 10) xG hxG0
  rw [show 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 = ((40 * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    show ((40 * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) = 10 * M ^ 2 by rw [hM]; push_cast; ring] at n4
  have n5 : b ^ ((3 + 3 * Ch) * M ^ 2 * (10 * M ^ 2)) ≤ b ^ ((3 + 3 * Ch) * 10 * M ^ 5) :=
    bp_mono hb1 (by nlinarith [mul_le_mul_of_nonneg_left hM45 (show 0 ≤ (3 + 3 * Ch) * 10 by positivity)])
  have n6 := n4.trans (mul_le_mul_of_nonneg_right n5 (by positivity))
  have hF0 := FrC_nonneg D 2 (kaRe D) hka
  rw [habs, add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0,
    Real.rpow_add hb0]
  calc _ ≤ b ^ ((4 + Ch) * (2 * (1 + Aw + 10)) * M ^ 5) * (b ^ (Ch * (4 * (1 + Aw + 10)) * M ^ 5) *
        (b ^ (4 * Ch * M ^ 5) * (b ^ (C * M ^ 5) * (b ^ ((3 + 3 * Ch) * 10 * M ^ 5) * max 1 (1 / |xG|) ^ A)))) := by
        gcongr
    _ = _ := by ring

end CompanionTheory.WaveGrid.WGlue
end
end
