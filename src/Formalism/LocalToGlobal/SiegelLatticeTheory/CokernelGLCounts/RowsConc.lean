import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.HermitianCurvature.StatementPN
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.RowsOther

open Formalism.FourierDecayAlt

section Gen

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)

def KppTermZero : Prop := ∀ t ∈ X.degSet, X.op t = 0

def KppOff : Prop := X.part X.degSet = 0

def KppDiag (du : ℝ) (k f : ℕ) : Prop :=
  ‖X.part X.degSet‖ ^ 2 ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))

def PairsDeg (Pg du : ℝ) (k f : ℕ) : Prop :=
  Pg * X.pairAbs (X.allPairs X.degSet) ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))

theorem kppOff_of_termZero (h : KppTermZero X) : KppOff X := by
  unfold KppOff PB.Terms.part
  have h0 : X.degSet.indicator X.op = 0 := by
    funext t
    exact Set.indicator_apply_eq_zero.2 (fun ht => h t ht)
  rw [h0]
  exact tsum_zero

theorem kppDiag_of_pairs [CompleteSpace H₁] (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (hAbs : X.AbsConv) (hO : X.RowOrth)
    (hC : X.CorankPos) (hN : X.NormExpansionOn X.degSet) (hG : X.GGBound Pg)
    (hB : PairsDeg X Pg du k f) : KppDiag X du k f := by
  unfold KppDiag
  have h1 := hP hE τ Rw I H H₁ X Pg X.degSet hN hG
  rw [((hS τ Rw I H H₁ X hAbs hO hC).1 X.degSet)] at h1
  have h3 := (hSub τ Rw I H H₁ X hAbs _ _ (subset_refl (X.allPairs X.degSet))).2
  calc ‖X.part X.degSet‖ ^ 2 ≤ Pg * X.pairSum (X.allPairs X.degSet) := h1
    _ ≤ Pg * X.pairAbs (X.allPairs X.degSet) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans h3) hPg
    _ ≤ _ := hB

def IdOne (one : H) : Prop := X.part X.idSet = one

def DiagRow (one : H) (Gm dd : ℝ) : Prop := ‖X.K0 - one‖ ^ 2 ≤ Gm * dd

def noId : PB.Terms τ Rw I H H₁ := { X with isId := fun _ => False }

theorem noId_idSet : (noId X).idSet = ∅ := by
  ext t
  simp [PB.Terms.idSet, noId]

theorem noId_idZero : (noId X).IdZero := by
  unfold PB.Terms.IdZero PB.Terms.part
  rw [noId_idSet]
  simp

theorem nonIdentity_K0 (one : H) (h : IdOne X one) : (noId X).K0 = X.K0 - one := by
  have h0 : (noId X).part (noId X).idSet = 0 := noId_idZero X
  have hg : (noId X).part (noId X).genSet = X.part X.genSet := rfl
  have hn : (noId X).part (noId X).ngSet = X.part X.ngSet := rfl
  unfold IdOne at h
  simp only [PB.Terms.K0]
  rw [h0, hg, hn, h]
  abel

theorem diag_of_abstract [CompleteSpace H₁] (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota)
    (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily) (one : H) (Pg A ε ε' dd : ℝ)
    (hPg : 0 ≤ Pg) (hdd : 0 ≤ dd) (hAbs : X.AbsConv)
    (hN : X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) (hG : X.GGBound Pg)
    (hO : X.RowOrth) (hC : X.CorankPos) (hI : IdOne X one) (h1 : X.RowBig ε dd)
    (h2 : X.RowNotScalar ε dd) (h3 : X.RowMain A dd) (h4 : X.RowNG ε' dd) :
    DiagRow X one ((√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2) dd := by
  unfold DiagRow
  rw [← nonIdentity_K0 X one hI]
  exact hA hP hE hS hSub τ Rw I H H₁ (noId X) Pg A ε ε' dd hPg hdd hAbs hN hG hO hC (noId_idZero X) h1 h2 h3 h4

section Loops

def PP : Set (τ × τ) := X.big X.nzSet ∪ X.nsc X.genSet

def ampSum (Q : Set (τ × τ)) : ℝ := ∑' p : τ × τ, Q.indicator (fun p => ‖X.vec p.1‖ * ‖X.vec p.2‖) p

theorem pairAbs_le_ampSum (hG : 0 ≤ X.Gam1) (Q : Set (τ × τ))
    (hs : Summable (Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖))) :
    X.pairAbs Q ≤ X.Gam1 * ampSum X Q := by
  unfold PB.Terms.pairAbs ampSum
  refine mul_le_mul_of_nonneg_left ?_ hG
  have hle : ∀ p, Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p ≤
      Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p := by
    intro p
    by_cases hp : p ∈ Q
    · simp only [Set.indicator_of_mem hp]
      exact norm_inner_le_norm _ _
    · simp [Set.indicator_apply, hp]
  have hnn : ∀ p, 0 ≤ Q.indicator (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) p :=
    fun p => Set.indicator_nonneg (fun _ _ => norm_nonneg _) p
  exact Summable.tsum_le_tsum hle (hs.of_nonneg_of_le hnn hle) hs

def LoopsAmp (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ) : Prop :=
  Summable ((PP X).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) ∧
  X.Gam1 * ampSum X (PP X) ≤
    A * (∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
      Gam ^ 2 * ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi +
      C ^ f * Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
        Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
        Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f))) * dd

theorem loopsInput_of_amp (hG : 0 ≤ X.Gam1) (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ)
    (h : LoopsAmp X A C k r f b g v Gam Xi dd) : PB.LoopsInput X A C k r f b g v Gam Xi dd :=
  (pairAbs_le_ampSum X hG (PP X) h.1).trans h.2

def PairsDegAmp (Pg du : ℝ) (k f : ℕ) : Prop :=
  Summable ((X.allPairs X.degSet).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) ∧
  Pg * (X.Gam1 * ampSum X (X.allPairs X.degSet)) ≤ du * Real.exp (-((k : ℝ) * f * Real.log k))

theorem pairsDeg_of_amp (hG : 0 ≤ X.Gam1) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (h : PairsDegAmp X Pg du k f) :
    PairsDeg X Pg du k f :=
  (mul_le_mul_of_nonneg_left (pairAbs_le_ampSum X hG _ h.1) hPg).trans h.2

end Loops

section NG

variable {E : Type} [Field E] [NumberField E] {r : ℕ} {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu)

def NGFin (k f C1 C0 : ℕ) (rd g TT AAre e1 : ℝ) : Prop :=
  PN.ClassInput X N ∧ PN.AmpInput X N ∧ PN.NormalsInput X N (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) ∧
  PN.PointsInput X N ∧ PN.LocalInput X N C1 C0 k ∧ PN.GenMassInput X N AAre e1 ∧ PN.HeightInput X N (g ^ f)

def NGReal (f A : ℕ) (CB b cSt Ire : ℝ) : Prop :=
  PN.MeasureInput X N cSt ∧
  PN.PointSumInput X N (A * (r + 1) ^ 2) (Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) * Ire)

theorem ngInputs_iff (k f C1 C0 A : ℕ) (CB b rd g TT cSt AAre e1 Ire : ℝ) :
    PN.NGInputs X N k f C1 C0 A CB b rd g TT cSt AAre e1 Ire ↔
      NGFin X N k f C1 C0 rd g TT AAre e1 ∧ NGReal X N f A CB b cSt Ire := by
  unfold PN.NGInputs NGFin NGReal
  tauto

end NG

end Gen

theorem rowLoops_of_input (hL : PN.LoopCores) (hSub : PB.SubFamily) (C : ℝ) (hC : 1 ≤ C) :
    ∃ K₀ : ℝ, ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) (k r f : ℕ)
      (A b g v NT Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ), 1 ≤ A →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k (2 * r + 2) f b g v NT Gam →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k (2 * r + 2) f b v NT Xi →
      6 * Real.log (3 * A) ≤ (k : ℝ) * f * Real.log k → 0 ≤ dd → X.AbsConv →
      PB.LoopsInput X A C k r f b g v Gam Xi dd →
      X.RowBig (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd ∧
      X.RowNotScalar (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd := by
  obtain ⟨h1, h2, h3, h4, h5, hJ, hGR⟩ := hL
  obtain ⟨K₀, hK⟩ := hJ h1 h2 h3 h4 h5 C hC
  refine ⟨K₀, ?_⟩
  intro τ Rw I H H₁ _ _ _ _ _ X k r f A b g v NT Gam Xi dd hA hPar hXi hlog hdd hAbs hIn
  exact hGR hSub τ Rw I H H₁ X _ dd hAbs (hK τ Rw I H H₁ X k r f A b g v NT Gam Xi dd hA hPar hXi hlog hdd hIn)

theorem rowNG_of_cut (hR : PN.RowNGJoint) (hC : PN.NGChain) (C1 C0 A : ℕ) (CB CSt Cg CT : ℝ)
    (h1 : 0 ≤ CB) (h2 : 0 ≤ CSt) (h3 : 0 ≤ Cg) (h4 : 0 ≤ CT) (hA : C1 + C0 + 38 ≤ A) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧
    ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
      [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r k : ℕ) (Cl Nu : Type) (N : PN.NGData τ E r Cl Nu)
      (P : Type) [Fintype P] (B : S3.MassData P) (b rd g TT cSt e1 Irat Ire : ℝ),
      X.AbsConv → X.Gam1 = B.Gam1 → PN.NormInputs B →
      PN.FrameInputs B rd g r k (Fintype.card (NumberField.InfinitePlace E)) Irat Ire →
      PN.NGSizes Cg CT CSt r (Fintype.card (NumberField.InfinitePlace E)) b rd g TT cSt e1 →
      NGFin X N k (Fintype.card (NumberField.InfinitePlace E)) C1 C0 rd g TT
        (PN.abelian₂ rd r k (Fintype.card (NumberField.InfinitePlace E)) * B.AA) e1 →
      NGReal X N (Fintype.card (NumberField.InfinitePlace E)) A CB b cSt Ire →
      X.RowNG (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
        Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card (NumberField.InfinitePlace E) : ℕ) * Real.log b))
        (B.d * B.d' / B.Dstar) := by
  obtain ⟨Cn, hCn, hmain⟩ := hR hC C1 C0 A CB CSt Cg CT h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, ?_⟩
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N P _ B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI hSz hFin hReal
  exact hmain E τ Rw I H H₁ X r k Cl Nu N P B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI hSz
    (by rw [ngInputs_iff]; exact ⟨hFin, hReal⟩)

end Formalism.L2.SG.RowsOther
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt

set_option linter.dupNamespace false

namespace Formalism.L2.SG.RowsConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Num

variable {D : D7} (X : HidaSetting D) (Y : Full X)

def duC (u : D.what₂.Word) : ℝ := (Module.finrank ℂ (Cu X u Y.hK) : ℝ)

def DstC : ℝ := X.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll X.B.I X.B.σ X.B.w) X.B.μf X.B.fund X.B.e

def ddC (u u' : D.what₂.Word) : ℝ := duC X Y u * duC X Y u' / DstC X

def oneC (u : D.what₂.Word) : Formalism.L2.SG.PackageTie.HS (CM (Y.cs u)) (CM (Y.cs u)) :=
  Formalism.L2.SG.PackageTie.hsEmb (ContinuousLinearMap.id ℂ (CM (Y.cs u)))

end Num

def PgC {D : D7} {X : HidaSetting D} (Y : Full X) : ℝ := ∏ v, (1 + 3 / (Fintype.card (Y.TR.Fq v) : ℝ))

def mR (D : D7) : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ)

def epsL (D : D7) : ℝ := Real.exp (-((1 / 3 : ℝ) * D.R.k * D.R.f * Real.log D.R.k))

def epsK (D : D7) : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def epsNG (D : D7) (large₂ : SizeData₂ D) (C4 : ℝ) : ℝ :=
  ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ * Real.exp (C4 * mR D ^ 5 * D.R.f * Real.log large₂.sc.b)

def gamB (D : D7) (large₂ : SizeData₂ D) (CB : ℝ) : ℝ := Real.exp (CB * mR D ^ 5 * D.R.f * Real.log large₂.sc.b)

def TFrameAt (D : D7) : Prop :=
  ∀ w : D.what₂.Word, 1 ≤ Formalism.MainNotions.S.Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS)

def ConcTie {D : D7} (X : HidaSetting D) (Y : Full X) : Prop :=
  X.LevelSubgroupNormalized ∧ (∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) ∧ (∀ u, duC X Y u = (D.duS u : ℝ)) ∧ DstC X = D.what₂.Dstar ∧
    Formalism.L2.SG.WuDecay.WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    (∃ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
      X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧
      Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Formalism.L2.SG.Pf.LocCP.LocTied D) ∧
    TFrameAt D

section Closed

def KppOffC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → u ≠ u' →
      Formalism.L2.SG.RowsOther.KppTermZero (Y.tO u u')

def KppDiagC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
      Formalism.L2.SG.RowsOther.KppDiag (Y.tO u u) (duC X Y u) D.R.k D.R.f

def RowLoopsC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u').AbsConv →
      (Y.tO u u').RowBig (epsL D) (ddC X Y u u') ∧ (Y.tO u u').RowNotScalar (epsL D) (ddC X Y u u')

def RowNGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C4 : ℝ, 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie X Y → (Y.tO u u').AbsConv →
      (Y.tO u u').RowNG (epsNG D large₂ C4) (ddC X Y u u')

def RowMainEqC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowMain (gamB D large₂ CB) (ddC X Y u u)

def DiagC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB C4 : ℝ, 0 ≤ CB ∧ 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT → ConcTie X Y →
      (Y.tO u u).AbsConv → max CB C4 + 1 ≤ large₂.CGam →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

end Closed

section Facts

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem dst_pos (h : ConcTie X Y) (u : D.what₂.Word) : 0 < DstC X := by
  rw [h.2.2.2.1, ← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

theorem dd_nonneg (h : ConcTie X Y) (u u' : D.what₂.Word) : 0 ≤ ddC X Y u u' := by
  unfold ddC
  have h1 : 0 ≤ duC X Y u := Nat.cast_nonneg _
  have h2 : 0 ≤ duC X Y u' := Nat.cast_nonneg _
  exact div_nonneg (mul_nonneg h1 h2) (dst_pos h u).le


end Facts

section Cut

def AbsConvTied : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (Y.tO u u').AbsConv

def NormExpSatTied : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y →
    (Y.tO u u').NormExpansionOn (Y.tO u u').genSet ∧ (Y.tO u u').NormExpansionOn (Y.tO u u').ngSet

def NormExpDegC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    (Y.tO u u).NormExpansionOn (Y.tO u u).degSet

def CorankPosC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (Y.tO u u').CorankPos

def IdOneC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    Formalism.L2.SG.RowsOther.IdOne (Y.tO u u) (oneC X Y u)

theorem card_ge_three {D : D7} {large₂ : SizeData₂ D} {Cl Cg CT : ℝ} (hK : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT)
    {X : HidaSetting D} (TR : TypedRed X) (v : TR.Pl) : 3 ≤ Fintype.card (TR.Fq v) := by
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb : 1 < large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b
    have := Real.add_one_lt_exp (ne_of_gt hL); linarith
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hkb : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have h8 : (3 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hkb 8)
  rcases TR.card_q v with h | h
  · rw [h]; exact_mod_cast h8.trans (hK.2.1 0).1
  · rw [h]; exact_mod_cast h8.trans (hK.2.1 1).1

def LoopsCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ K₀ : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y →
      ∃ (Al NT Gam : ℝ) (Xi : ℕ → ℝ), 1 ≤ Al ∧
        Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v NT Gam ∧
        Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v NT Xi ∧
        6 * Real.log (3 * Al) ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k ∧
        Formalism.L2.SG.RowsOther.LoopsAmp (Y.tO u u') Al C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v Gam Xi
          (ddC X Y u u')


def PairsDegCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y →
      Formalism.L2.SG.RowsOther.PairsDegAmp (Y.tO u u) (PgC Y) (duC X Y u) D.R.k D.R.f

theorem kppDiagC_of_cut (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily)
    (hGG : Formalism.L2.SG.GGMirabolic.TermsGGBound) (hC : CorankPosC) (hN : NormExpDegC)
    (hc : PairsDegCutC) : KppDiagC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hH hT ha => ?_⟩
  have hG0 : 0 ≤ (Y.tO u u).Gam1 := ha.2.2.le
  have hPg : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hGB : (Y.tO u u).GGBound (PgC Y) :=
    Formalism.L2.SG.TermOp.ggBound Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hGG Y.psi_ne
      (fun v => card_ge_three hH.2 Y.TR v)
  refine ⟨ha.1.indicator _, ?_⟩
  exact Formalism.L2.SG.RowsOther.kppDiag_of_pairs (Y.tO u u) hP hE hS hSub (PgC Y) (duC X Y u) D.R.k D.R.f hPg ha
    (Formalism.L2.SG.TermOp.rowOrth Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u)) (hC D X Y u u hT) (hN D X Y u hT) hGB
    (Formalism.L2.SG.RowsOther.pairsDeg_of_amp _ hG0 _ _ _ _ hPg (h C' Cl h1 h2 D large₂ X Y u hH hT))

def DiagNumC : Prop :=
  ∀ Cg cb Cw cT CT C0 A CB C4 : ℝ, 0 ≤ CB → 0 ≤ C4 → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT → ConcTie X Y →
      max CB C4 + 1 ≤ large₂.CGam →
      (√(PgC Y * (gamB D large₂ CB + 2 * epsL D)) + √(PgC Y * (epsL D + epsNG D large₂ C4))) ^ 2 ≤ (D.mem u).A.GamP


end Cut

section FromFull

open Formalism.L2.SG.WuDecay

theorem absConvTied_of_full (hFo : FoldOKC) (hF : FundExistsC) (hO : OOIntAllC)
    (hA : AbsConvC) : AbsConvTied := by
  intro D X Y u u' hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  have f2 := hFo D X Y u' hT.1 hT.2.2.2.2.1
  exact hA D X Y u u' f1 f2 (hF D X Y u u') (hO D X Y u u' f1 f2 (hF D X Y u u'))


theorem hasSum_hsEmb {ι : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {f : ι → W →L[ℂ] W} {a : W →L[ℂ] W} (h : HasSum f a) :
    HasSum (fun i => Formalism.L2.SG.PackageTie.hsEmb (f i)) (Formalism.L2.SG.PackageTie.hsEmb a) :=
  h.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := W) (Wp := W)) (LinearMap.continuous_of_finiteDimensional _)

theorem idOne_of_cell {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (h : Formalism.L2.SG.TermOp.IdCellDiag (X.Fu u) (Y.cs u) (Y.FN u)) :
    Formalism.L2.SG.RowsOther.IdOne (Y.tO u u) (oneC X Y u) := by
  have hs := hasSum_hsEmb (h (Y.FN_fund u))
  unfold Formalism.L2.SG.RowsOther.IdOne PB.Terms.part
  rw [← tsum_subtype]
  exact hs.tsum_eq

theorem idOneC_of_full (hFo : FoldOKC) (hF : FundExistsC) (hO : OOIntAllC)
    (hI : IdCellDiagC) : IdOneC := by
  intro D X Y u hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  exact idOne_of_cell Y u (hI D X Y u hT.1 (hF D X Y u u) (hO D X Y u u f1 f1 (hF D X Y u u)))

theorem norm_vec {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    ‖(Y.tO u u').vec t‖ =
      wt t * ‖Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t)‖ := by
  show ‖vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t‖ = _
  unfold vec
  have e : (fun q : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'} => if q = (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) then
      ((wt t : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t) else 0) =
      Pi.single (⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩)
        (((wt t : ℝ) : ℂ) • Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t)) := by
    funext q; simp [Pi.single_apply]
  rw [e, PiLp.norm_toLp_single, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ) ≤ wt t from Real.sqrt_nonneg _)]

end FromFull

section TermReal

variable {D : D7} (X : HidaSetting D)

variable {X} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

end TermReal

section NGData

def toPts {K : Type} [Zero K] {i : ℕ} (p : Formalism.MainNotions.S.Point K (i + 1)) : Σ c : Composition (i + 1), (Fin c.length → K) :=
  ⟨⟨p.1.map Prod.snd, fun {j} hj => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hj
      exact (p.2.1 b hb).2, p.2.2⟩,
    fun a => (p.1.get ⟨a.1, by simpa [Composition.length] using a.2⟩).1⟩

section Pts

variable {E : Type} [Field E] {r : ℕ}

def endMin (γ : PN.Pts E r) (a : Fin γ.1.length) : E :=
  Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry γ.1.blocksFun γ.2 a

def endIdx (γ : PN.Pts E r) (a : Fin γ.1.length) : ℕ := γ.1.sizeUpTo (a.1 + 1)

def DlastPt (γ : PN.Pts E r) : E :=
  if h : 0 < γ.1.length then endMin γ ⟨γ.1.length - 1, by omega⟩ else 1

def DrPt (γ : PN.Pts E r) : E :=
  if h : 0 < γ.1.length then
    (if γ.1.blocksFun ⟨γ.1.length - 1, by omega⟩ = 1 then
      (if h2 : 2 ≤ γ.1.length then endMin γ ⟨γ.1.length - 2, by omega⟩ else 1) else 0)
  else 1

def GPt [StarRing E] (TT : ℕ) (γ : PN.Pts E r) : E :=
  DlastPt γ * star (DlastPt γ) - (TT : E) * (DrPt γ * star (DrPt γ))

variable [NumberField E]

def NGPt [StarRing E] (rd : ℝ) (TT : ℕ) (γ : PN.Pts E r) : ℝ :=
  ∏ w : InfinitePlace E, (rd ^ (2 * r * (r + 1)))⁻¹ * w (GPt TT γ)

def NDPt (rd : ℝ) (γ : PN.Pts E r) : ℝ :=
  ∏ a : Fin γ.1.length, ∏ w : InfinitePlace E,
    (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2

def nPt [StarRing E] (rd : ℝ) (k TT : ℕ) (γ : PN.Pts E r) : ℝ :=
  ∏ w : InfinitePlace E,
    ((rd ^ (2 * r * (r + 1)))⁻¹ * w (GPt TT γ)) ^ (k - 1) *
      ∏ a : Fin γ.1.length,
        ((rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)) ^
          (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1))

def HPt [StarRing E] (rd g : ℝ) (TT : ℕ) (γ : PN.Pts E r) : ℝ :=
  (g ^ ((2 * r + 1) * Fintype.card (InfinitePlace E)))⁻¹ * NGPt rd TT γ * NDPt rd γ

end Pts

variable {D : D7}

variable {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

abbrev TauC : Type := GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

variable {Y u u'}

def ptPN (t : TauC Y u u') : PN.Pts D.host.E D.R.rS := toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)

variable (Y u u')

def clsOf (t : TauC Y u u') : Set (TauC Y u u') :=
  {t' | t' ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t ∧ (Y.tO u u').s0 t t' = 1}

def ampS (t : TauC Y u u') : ℂ :=
  (X.volK2 : ℂ) * chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
    ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt)

def J2loc (γ : PN.Pts D.host.E D.R.rS) : ℝ :=
  if h : ∃ t : TauC Y u u', t ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').vec t ≠ 0 ∧ ptPN t = γ then
    ‖Formalism.L2.SG.PackageTie.hsEmb
      (((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') : ℝ) : ℂ) • OOt h.choose)‖ ^ 2
  else 0

def a2Of (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : TauC Y u u') : ℝ :=
  if ν ∈ (Y.tO u u').ngSet ∧ clsOf Y u u' ν = c ∧ ptPN ν = γ then wt ν ^ 2 * ‖ampS Y u u' ν‖ ^ 2 else 0

def ngenOf (γ : PN.Pts D.host.E D.R.rS) : ℝ :=
  ∑' t : TauC Y u u', {t : TauC Y u u' | t.generic ∧ t.G ≠ 0 ∧ ptPN t = γ}.indicator (fun t => wt t ^ 2) t

def NOf : PN.NGData (TauC Y u u') D.host.E D.R.rS (Set (TauC Y u u')) (TauC Y u u') where
  cls := clsOf Y u u'
  pt := ptPN
  nml := id
  a2 := a2Of Y u u'
  J2loc := J2loc Y u u'
  jacobianSquareBound := J2loc Y u u'
  n := nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u' : ℕ))
  NG := NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ))
  ND := NDPt D.host.rdE
  Hh := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ))
  ngen := ngenOf Y u u'

end NGData

section NGCut

def NGCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ (C1 C0n A : ℕ) (CB CSt Cgs CTs : ℝ), 0 ≤ CB ∧ 0 ≤ CSt ∧ 0 ≤ Cgs ∧ 0 ≤ CTs ∧
    C1 + C0n + 38 ≤ A ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie X Y →
      ∃ (P : Type) (_ : Fintype P) (B : S3.MassData P) (cSt e1 Irat Ire : ℝ),
        (Y.tO u u').Gam1 = B.Gam1 ∧ B.d * B.d' / B.Dstar = ddC X Y u u' ∧ PN.NormInputs B ∧
        PN.FrameInputs B (2 * D.host.v) (X.B.g : ℝ) D.R.rS D.R.k D.R.f Irat Ire ∧
        PN.NGSizes Cgs CTs CSt D.R.rS D.R.f large₂.sc.b (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) cSt e1 ∧
        Formalism.L2.SG.RowsOther.NGFin (Y.tO u u') (NOf Y u u') D.R.k D.R.f C1 C0n (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
        Formalism.L2.SG.RowsOther.NGReal (Y.tO u u') (NOf Y u u') D.R.f A CB large₂.sc.b cSt Ire


end NGCut

end Formalism.L2.SG.RowsConc
end
end
