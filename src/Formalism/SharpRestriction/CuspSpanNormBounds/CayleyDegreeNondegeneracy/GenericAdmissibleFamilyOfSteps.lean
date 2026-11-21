import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusMassPosOfMassLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar


section Num

variable (D : D7) (large₂ : SizeData₂ D)










end Num

section C4

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenericThetaSublattice (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → RelZ D (ZhatL (lf D F0) F') →
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
    latticeRank D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
    latticeDetW D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F')

end C4

section C4F

variable {eps : ℝ} (Fm : FamP eps)

def PositionCountFamilyGeneric (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    TermPositionCount (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def GenericThetaFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    GenericThetaSublattice (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

end C4F


section Mean

variable (D : D7)



end Mean

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar


section SW

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def localGramProduct (Z : GramM D) : ℝ :=
  (∏ τ, Cnt.Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)

def sublatticesOfDet (L0 : LatticeW D) (j : ℕ) (G : ℝ) : Set (LatticeW D) :=
  {P | P ≤ L0 ∧ latticeRank D P = j ∧ latticeDetW D P = G}

def classWeightAlt : ℝ :=
  (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f

def GenericThetaWeak (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z →
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
    latticeRank D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
    latticeDetW D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = localGramProduct D u u' Z ∧
    1 ≤ localGramProduct D u u' Z ∧ localGramProduct D u u' Z ≤ HHZ D large₂.sc.b C Z

def SublatticeMeanBound (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ G HH : ℝ, 1 ≤ G → G ≤ HH → NT D u ≤ HH →
    MeanLe D F0 what₂ (fun Λ => (sublatticesOfDet D (L0X D Λ (lf D F0)) (D.R.k - 1) G).encard)
      (LatticeSumBounds.nTot D.R.k D.R.f D.host.v G (NT D u) * NT D u * G ^ (cF D.R.f) * G *
        (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))

def SameTermEquivalence : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D),
    Equivalence (TEqv D Λ (lf D F0) : FlagU D u' → FlagU D u' → Prop)





end SW





section W0

variable (D : D7) (large₂ : SizeData₂ D)


end W0

section SWF

variable {eps : ℝ} (Fm : FamP eps)

def SublatticeMeanFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', SublatticeMeanBound (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def GenericThetaWeakFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    GenericThetaWeak (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C




end SWF

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Eqv

variable (D : D7)

end Eqv

section Sat

variable (D : D7)

end Sat

section Sub

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def PrimitiveMeanCorankOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ de : ℕ, 1 ≤ de → ∀ HH : ℝ, (de : ℝ) ≤ HH → NT D u ≤ HH →
    MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de)
      (((de : ℝ) / NT D u) ^ (D.R.k - 1) * (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))

end Sub

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end
