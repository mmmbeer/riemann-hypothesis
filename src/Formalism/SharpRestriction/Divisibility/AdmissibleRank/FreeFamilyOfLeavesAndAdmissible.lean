import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ParahoricIdxZ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DatumConjInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DatumBlockEigen
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.UMultOne
import Formalism.SharpRestriction.AdmissibleParameterJoins.FamilyAuxiliaryPrimeSize
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.GoodPartEigenspaceKernelSplitting
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions MeasureTheory Matrix ComplexConjugate




def LemmaUInst (qn : ℝ) (a t idx : ℕ) (Zv : ℂ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : TopologicalSpace F) (_ : IsTopologicalRing F) (_ : T2Space F)
    (_ : SecondCountableTopology F) (_ : MeasurableSpace F) (_ : BorelSpace F) (O : Subring F)
    (_ : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O) (_ : ϖ ≠ 0) (_ : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ)
    (_ : Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (J' : Subgroup (GL (Fin a) F))
    (_ : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J') (_ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (_ : IsCompact (J' : Set (GL (Fin a) F)))
    (ρ : J' →* ℂˣ) (_ : ∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1)
    (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ)
    (_ : ∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1)
    (c : GL (Fin a) F → ℂ) (_ : ∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g)
    (_ : c 1 = 1)
    (μ : Measure (GL (Fin a) F)) (_ : μ.IsMulLeftInvariant) (_ : μ (J' : Set (GL (Fin a) F)) = 1)
    (ν₁ : Measure (Matrix (Fin a) (Fin a) F)) (_ : ν₁.IsAddLeftInvariant) (_ : SFinite ν₁)
    (_ : ν₁ (Formalism.DoubleCosetMeasures.intMat O a a) = 1)
    (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) (_ : ν₂.IsAddLeftInvariant) (_ : SFinite ν₂)
    (_ : ν₂ (Formalism.DoubleCosetMeasures.intMat O t a) = 1)
    (J : Subgroup (GL (Fin (a + t)) F)) (_ : ∀ A, A ∈ J ↔ Formalism.MainNotions.ZetaProductPairs.blockCond O ϖ J' A),
    qn = (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) ∧
    idx = (J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index ∧
    Zv = Formalism.DoubleCosetMeasures.localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
          (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) c


structure TieG (D : D7) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) : Prop where
  ch : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ, ∀ v ∈ X.Sg,
    LemmaUInst (Formalism.MainNotions.InnerProductFormulaField.normPl v) (D.R.r + (j - 1) * D.R.t) D.R.t (X.idxgCh μ j v) (X.ZgCh μ j σ v)
  sb : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ, ∀ v ∈ X.Sg,
    LemmaUInst (Formalism.MainNotions.InnerProductFormulaField.normPl v) D.R.r D.R.t (X.idxgSb μ j v) (X.ZgSb μ j σ v)









end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar





def ArchimedeanChainApplication (D : D7) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.WtHyp T →
    (∀ j, 1 ≤ j → j ≤ D.R.m →
      ∃ z : D.what₂.Tau → ℂ, (∀ τ, Formalism.MainNotions.InnerProductFormulaField.IsARZ A (z τ)) ∧ ((X.ZChR j : ℝ) : ℂ) = ∏ τ, z τ) ∧
    (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < X.ZSbR j ∧ 0 < X.nT j) ∧
    (∀ (μ : D.what₂.Tup) (i l : ℕ), i < D.R.m → 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
      ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), Formalism.MainNotions.InnerProductFormulaField.IsTypeD T i G →
        Formalism.MainNotions.InnerProductFormulaField.thS T μ i _ Φ G = 0)






def Qof (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) : Submodule ℂ (D.what₂.Amb μ) :=
  D.what₂.V0 μ ⊓ (D.what₂.V0 μ ⊓ LinearMap.ker ι)ᗮ

def BijOn (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) : Prop :=
  Function.Bijective (ι.domRestrict (Qof D μ ι))

def AdjOn (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) (y z : D.what₂.EE) : Prop :=
  (ι.domRestrict (Qof D μ ι) ∘ₗ LinearMap.adjoint (ι.domRestrict (Qof D μ ι))) y = z







def APlusPart (D : D7) (j : ℕ) : Prop :=
  ∀ τ, ∃ z : ℕ → ℕ, (∀ i < (D.R.sigW j).1, DV.aPlus D j τ i = z i) ∧
    ∀ i l, i < l → l < (D.R.sigW j).1 → z l ≤ z i




theorem hkSigPar_lt (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) < DV.sigPar D τ i := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dif_pos h1, dif_pos h0]
    have a := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
    have b := (D.hc τ).v_gt_u ⟨i, h0⟩
    exact a.trans b
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb, dif_pos h0]
      have a := (D.hc τ).u_last_gt (by omega) (by omega)
      have b := (D.hc τ).v_gt_u ⟨i, h0⟩
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      have e2 : (⟨i + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have b' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        rw [← e2]
        exact b
      exact a.trans b'
    · have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb2 : i - (D.R.k - 1) + 1 < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb1, dif_neg h0, dif_pos hb0]
      have a := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have b := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ hb2
      have e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, hb2⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  obtain ⟨a, ha⟩ := DV.sigPar_int D τ i
  obtain ⟨b, hb⟩ := DV.sigPar_int D τ (i + 1)
  have h := hkSigPar_lt D τ i hi
  rw [ha, hb] at h
  have h' : b < a := by exact_mod_cast h
  have h'' : (b : ℚ) + 1 ≤ a := by exact_mod_cast h'
  rw [DV.aPlusQ_eq, DV.aPlusQ_eq, ha, hb]
  push_cast
  linarith




theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c + 1 < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  have h1 : j + (c + 1) < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dif_pos h0, dif_pos h1]
  have a := (D.hc τ).gap_be ⟨j + c, h0⟩
  have b := (D.hc τ).gap_eb ⟨j + c, h0⟩ hc
  have e1 : (⟨j + (c + 1), h1⟩ : Fin D.R.m) = ⟨j + c + 1, hc⟩ := by
    rw [Fin.mk.injEq]
    omega
  rw [e1]
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c c' : ℕ) (h : c ≤ c') (hc' : j + c' < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ c' := by
  induction c', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (aMinusQ_step D j τ n (by omega))









def LambdaLowerBoundAllEmbeddings (D : D7) (Z : DivX D) (b : ℝ) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ), ∀ j ∈ SizeData₂.lifts D, ∀ σ, -b ≤ Z.logLam j σ s





















def ArchimedeanTheoremFiveParts (A : ProvA) : Prop :=
  Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth A

def ExtraLowerBoundAtEmbeddings (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} (L : SizeData₂ D) (XD : DivX D) {Am : AmbForm D V.S}
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (C : ℝ) : Prop :=
  (∀ (s : D.what₂.LL →+* ℂ), ∀ j ∈ SizeData₂.lifts D, ∀ σ : Fin V.n, -L.sc.b ≤ XD.logLam j (V.ft σ) s) ∧
  (∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ Φ, X.T0 μ Φ ∈ X.Good μ Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot ∧
    ∀ F ∈ V.S.V0 μ, X.ev μ Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot (X.T0 μ Φ) F = X.rowUp Φ D.R.m (X.real (V.S.iota μ F))) ∧
  (∀ w Φ, X.T0 (D.what₂.muAt w) Φ ∈ X.IntAt (D.what₂.muAt w) Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot w 0) ∧
  (∀ v Φ, X.T0 D.what₂.mu0 Φ ∈
    X.SzAt D.what₂.mu0 Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot v (C * (D.R.m : ℝ) * (X.Nst : ℝ) ^ 2 * X.weightedLogLevelSum))

def SquareLeaves (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} (L : SizeData₂ D) (XD : DivX D) {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am)
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) : Prop :=
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypSz D L X K ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm1 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm3 D L XD X K.Cint ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.ArchimedeanSignatureMatching D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm10 K.Ctr ∧
  Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar ∧
  ExtraLowerBoundAtEmbeddings D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm9 D L ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm14 D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm15 D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm16 D L X K.Cval ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D V ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm18 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm19 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm20 D L X K.Cfp K.Cfp' ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm21 D L X K.Cip ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm22 D L X K.Cmm ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm23 D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FrobeniusExpansionCongruence D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrExtensionClause D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm26 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrCocycleExtensionClass D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FontaineFormalProperties D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D XD X






def MultiplicityLeaves {D : D7} (T : ThetaX D) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.adm1 ∧ Formalism.MainNotions.ZetaProductPairs.adm2 T ∧ Formalism.MainNotions.ZetaProductPairs.adm3 ∧ Formalism.MainNotions.ZetaProductPairs.adm5 D ∧ Formalism.MainNotions.ZetaProductPairs.adm6 G ∧
    Formalism.MainNotions.ZetaProductPairs.adm7 ∧ Formalism.MainNotions.ZetaProductPairs.ThetaCuspidalChain T

def LiftLeaves (D : D7) (Z : DivX D) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) : Prop :=
  Formalism.MainNotions.InnerProductFormulaField.adm1 D Z T X ∧ Formalism.MainNotions.InnerProductFormulaField.adm2 D Z X ∧ ArchimedeanChainApplication D T A X ∧ Formalism.MainNotions.InnerProductFormulaField.ArchimedeanSignatureMatching D T X ∧ TieG D X ∧
    Formalism.MainNotions.InnerProductFormulaField.adm7 D X ∧ Formalism.MainNotions.InnerProductFormulaField.adm8 D ∧ Formalism.MainNotions.InnerProductFormulaField.adm9 D T X ∧ Rows.IsotInternal D.what₂ ∧
    Rows.IsotRank D.what₂

def ConstantFreeMultiplicityItems {D : D7} {T : ThetaX D} (Z : DivX D) (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.HeckeOperatorScalarUnitary D ∧ Formalism.MainNotions.ZetaProductPairs.L1 ∧ Formalism.MainNotions.ZetaProductPairs.L2 Z ∧ Formalism.MainNotions.ZetaProductPairs.ThetaLiftChainTyped T ∧ Formalism.MainNotions.ZetaProductPairs.UnfoldingScalarUnitary X ∧
    Formalism.MainNotions.ZetaProductPairs.ExchangeOfPositions X ∧ Formalism.MainNotions.ZetaProductPairs.PeriodIntegrality Z


def RowsMultiplicityClosed {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop :=
  Rows.BuDefQ D.what₂ → Formalism.MainNotions.ZetaProductPairs.ZeDef X → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ →
  ∀ u : D.what₂.Word, ∃ h : Formalism.MainNotions.ZetaProductPairs.FFStable D u, Formalism.MainNotions.ZetaProductPairs.FFScalarUnitary u h ∧
    (∀ μ : D.what₂.Tup, ∃ n : ℕ, 0 < n ∧ D.what₂.zeC u μ ^ n = 1) ∧
    ∃ s c : ℂ, Formalism.MainNotions.ZetaProductPairs.SuShape D u s ∧ c ≠ 0 ∧ (∀ da, X.Au u da = c * X.ellT u da) ∧
      (∀ (φ : D.what₂.Mu u) (F : D.what₂.EE),
        D.what₂.Bu u φ F = (c * s⁻¹)⁻¹ * X.B0 u (Formalism.MainNotions.ZetaProductPairs.FFm u h φ) F) ∧
      ∀ (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
        D.what₂.perCol u μ φ F = D.what₂.zeC u μ * D.what₂.Bu u φ (D.what₂.iota μ F)






section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def MultiplicityLeavesFamily (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i)) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.ZetaProductPairs.adm1 ∧ Formalism.MainNotions.ZetaProductPairs.adm2 (Fm.ex x hx i).th ∧ Formalism.MainNotions.ZetaProductPairs.adm3 ∧ Formalism.MainNotions.ZetaProductPairs.adm5 (Fm.D x i) ∧
    Formalism.MainNotions.ZetaProductPairs.adm6 (GF x i) ∧ Formalism.MainNotions.ZetaProductPairs.adm7 ∧ Formalism.MainNotions.ZetaProductPairs.ThetaCuspidalChain (Fm.ex x hx i).th



def LeafHypothesesFamily (A : ProvA) (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.InnerProductFormulaField.adm1 (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.adm2 (Fm.D x i) (Fm.X x i) (XF x hx i) ∧
    ArchimedeanChainApplication (Fm.D x i) (Fm.ex x hx i).th A (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.ArchimedeanSignatureMatching (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
    TieG (Fm.D x i) (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.adm7 (Fm.D x i) (XF x hx i) ∧ Formalism.MainNotions.InnerProductFormulaField.adm8 (Fm.D x i) ∧
    Formalism.MainNotions.InnerProductFormulaField.adm9 (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
    Rows.IsotInternal (Fm.D x i).what₂ ∧ Rows.IsotRank (Fm.D x i).what₂













end Family

structure SqSett {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (μ : D.what₂.Tup) (i j : ℕ) where
  S : Formalism.MainNotions.KudlaSiegelWeil.Sett D T Lc
  rk_a : S.a = D.R.r + j * D.R.t + i * X.s + D.R.t + X.s
  rk_a' : S.a' = D.R.r + j * D.R.t + i * X.s
  p_eq : S.p = (D.R.m - j - 1) / 2
  q_eq : S.q = (D.R.m - j) / 2
  inf : ∀ τ (hj : j < D.R.m), |T.infTy (S.α / S.β) τ| = (D.hc τ).e ⟨j, hj⟩ + X.cInf (D.R.m - i) τ
  csq_def : ∀ c, S.Prop2 0 0 c → X.csq μ i j = c

def TieCsq {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) : Prop :=
  ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ i j, i < D.R.m → j < D.R.m → Nonempty (SqSett T Lc X μ i j)

theorem SqSett.prop2 {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} {T : ThetaX D} {Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T}
    {X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am} {μ : D.what₂.Tup} {i j : ℕ} (Q : SqSett T Lc X μ i j)
    (hK : Formalism.MainNotions.KudlaSiegelWeil.aux₃ D T Lc) : Q.S.Prop2 0 0 (X.csq μ i j) := by
  obtain ⟨_, _, _, _, _, _, hS⟩ := hK
  obtain ⟨-, c, hc, -⟩ := hS Q.S
  have h0 := hc 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  rw [Q.csq_def _ h0]
  exact h0


def SqSett.SeeSaw {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} {T : ThetaX D} {Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T}
    {X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am} {μ : D.what₂.Tup} {i : ℕ} (h : ℕ → ℕ) (Q : SqSett T Lc X μ i (h i)) : Prop :=
  ∀ (P : X.PD μ h) (P' : X.PD μ (Formalism.MainNotions.AbsolutelyIrreducibleSpan.flipP h i)), X.pA μ h i P' = X.pB μ h i P → ∀ F ∈ V.S.V0 μ,
    ∃ (ι : Type) (_ : Fintype ι) (ΦA : ι → T.Sch (Q.S.Vt 0) (Q.S.Wt (0 + 0)))
      (ΦB : ι → T.Sch (Q.S.V't 0) (Q.S.Wt (0 + 0)))
      (Λ : ι → (Lc.w.G (Q.S.Wt (0 + 0)) → ℂ) →ₗ[ℂ] X.th.AF (X.vx D.R.m 0)),
      (∀ k, ΦA k ∈ T.kfin (Q.S.Vt 0) (Q.S.Wt (0 + 0))) ∧ (∀ k, ΦB k ∈ Q.S.Sz 0 0) ∧
      (∀ k, Lc.p.pG (Q.S.Vt 0) (Q.S.V't 0) (Q.S.Wt (0 + 0)) Q.S.α Q.S.β (ΦA k) =
        Lc.p.pG' (Q.S.Vt 0) (Q.S.V't 0) (Q.S.Wt (0 + 0)) Q.S.α Q.S.β (ΦB k)) ∧
      X.ev μ (Formalism.MainNotions.AbsolutelyIrreducibleSpan.flipP h i) P' F = ∑ k, Λ k (Q.S.IA 0 0 (ΦA k)) ∧
      X.ev μ h P F = ∑ k, Λ k (Q.S.IB 0 0 (ΦB k))

def CommutationSquares {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) : Prop :=
  ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ h i, Formalism.MainNotions.AbsolutelyIrreducibleSpan.IsPath D.R.m h → Formalism.MainNotions.AbsolutelyIrreducibleSpan.Flippable D.R.m h i →
    4 * D.R.m + 2 < D.R.t + X.s → 2 * D.R.m + 1 < D.R.r + h i * D.R.t + i * X.s →
    (∀ τ (hj : h i < D.R.m), ((2 * (D.R.r + h i * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) <
      2 * ((D.hc τ).e ⟨h i, hj⟩ + X.cInf (D.R.m - i) τ)) →
    ∃ Q : SqSett T Lc X μ i (h i), Q.SeeSaw h


def SquareLeavesWithoutCommutation (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (L : SizeData₂ D) (XD : DivX D)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) : Prop :=
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypSz D L X K ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm1 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm3 D L XD X K.Cint ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.ArchimedeanSignatureMatching D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm10 K.Ctr ∧
  Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar ∧
  ExtraLowerBoundAtEmbeddings D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm9 D L ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm15 D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm16 D L X K.Cval ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D V ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm19 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm20 D L X K.Cfp K.Cfp' ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm21 D L X K.Cip ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm22 D L X K.Cmm ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm23 D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FrobeniusExpansionCongruence D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrExtensionClause D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm26 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrCocycleExtensionClass D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FontaineFormalProperties D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D XD X






def TieDatG (D : D7) (Z : DivX D) (G : Formalism.MainNotions.CanonicalTranslateJets.Loc D Z) : Prop :=
  ∀ μ j (h : G.Cls μ j) i x, ∃ (F : Type) (_ : Field F) (O : Subring F) (ϖ : F) (a t : ℕ)
    (J' : Subgroup (GL (Fin a) F)) (ρ : J' →* ℂˣ) (_ : ∀ k, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (y : Matrix (Fin a ⊕ Fin t) (Fin a) F),
    D.what₂.embLL (G.datG μ j h i x) = Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ y


end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV


section Proved

open Formalism.BasicNotions.TH






end Proved

section Split20

set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.BasicNotions.TH

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def LiftLeavesFamilyByKind (A : ProvA) (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.InnerProductFormulaField.AdmLit (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th (XF x hx i) ∧
    ArchimedeanChainApplication (Fm.D x i) (Fm.ex x hx i).th A (XF x hx i) ∧
    TieG (Fm.D x i) (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.AdmOwn (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
    Rows.IsotInternal (Fm.D x i).what₂ ∧ Rows.IsotRank (Fm.D x i).what₂


end Split20

end Formalism.MainNotions.DIV

end
