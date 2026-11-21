import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory TensorProduct
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialRules

open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (lenI AEq mid3 wnormSq)

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBCont CB

def adm2 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBAdj CB

def adm3 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_cap

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_anti

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_branch

def adm6 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_wigner

def adm10 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBRad CB

def RulesGauge (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def ResidueBoundAlt (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def RulesCapelli (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def RadialRulesCombined (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def RulesSigns (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def adm7 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RulesGauge D ∧ ResidueBoundAlt D C ∧ RulesCapelli D ∧ RadialRulesCombined D ∧ RulesSigns D

def RulesRTT (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def RulesDeterminant (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def adm8 (D : Formalism.BasicNotions.D7) : Prop := RulesRTT D ∧ RulesDeterminant D

def RulesWordModule (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def RulesFormHermitian (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def RulesTelescoping (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def RadialRuleLeadingEntry (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def RulesDuality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def RulesPlaneWave (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def adm9 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RulesWordModule D C ∧ RulesFormHermitian D C ∧ RulesTelescoping D ∧ RadialRuleLeadingEntry D ∧ RulesDuality D C ∧ RulesPlaneWave D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Parts

variable {B : Base E} {r : ℕ} (C : Ctx B r) (Γ : GCtx E r)

def LevelOperatorRules (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  S.UnitaryLevelOperators.stRules C h SS

end Parts

def aux₃ (_D : Formalism.BasicNotions.D7) (C Cv C1 C2 : ℝ) : Prop := S.UnitaryLevelOperators.stLevel C Cv C1 C2

def admitted (D : Formalism.BasicNotions.D7) (CB Ca : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Ca ∧ adm8 D ∧ adm9 D Ca ∧ adm10 D CB

def Stmt (D : Formalism.BasicNotions.D7) (CB Ca C Cv C1 C2 : ℝ) : Prop := admitted D CB Ca → aux₃ D C Cv C1 C2

def UniformExportStatement : Prop :=
  ∀ CB Ca : ℝ, ∃ C₀ Cv : ℝ, ∀ C1 : ℝ, ∃ C2 : ℝ, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7, Stmt D CB Ca C Cv C1 C2

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i) CB
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)
def admF7 (Ca : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i) Ca
def admF8 : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i)
def admF9 (Ca : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm9 (Fm.D x i) Ca
def FamilyRowsCountHypothesis (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm10 (Fm.D x i) CB

def AdmF (CB Ca : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm Ca ∧ admF8 Fm ∧ admF9 Fm Ca ∧
    FamilyRowsCountHypothesis Fm CB

def FamilyTargetsAtConstants (C Cv C1 C2 : ℝ) : Prop := ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) C Cv C1 C2

def OrbitValuationBound (C C1 : ℝ) : Prop := ∃ Cv C2 : ℝ, FamilyTargetsAtConstants Fm C Cv C1 C2

def FamilyStatementAtConstants (CB Ca C Cv C1 C2 : ℝ) : Prop := AdmF Fm CB Ca → FamilyTargetsAtConstants Fm C Cv C1 C2

def KudlaFamilyStatement (CB Ca C C1 : ℝ) : Prop := AdmF Fm CB Ca → OrbitValuationBound Fm C C1

end Family





theorem big_mono {C C' : ℝ} (h : C ≤ C') {L : Lev} {N : ℕ} {A : ℝ} {mm : ℕ} (hB : Big C' L N A mm) :
    Big C L N A mm := by
  unfold Big at *
  have hp : 0 ≤ ((L.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) := by positivity
  have hle : C * ((L.r : ℝ) + 1) ^ 4 *
        ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) ≤
      C' * ((L.r : ℝ) + 1) ^ 4 *
        ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right h hp
  exact ⟨hle.trans hB.1, hle.trans hB.2⟩


end Formalism.MainNotions.RadialRules
