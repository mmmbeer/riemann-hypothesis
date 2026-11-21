import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.ConstantCoeffAtReducedPoint
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.StepEpsFrob

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3.P4

variable {D : D7} (V : VData D)

def ent (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ)
    (g : K.fixingSubgroup) (i k : Fin 3) : V.S3 l e χ K g1 :=
  ((V.unitaryGaloisRepresentation l e χ K g1 g : GL (Fin 3) (V.S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (V.S3 l e χ K g1)) i k

def psi3 (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (i : Fin 3) (g : GQ) : V.Ol l :=
  ![V.psi l e χ g, 1, V.psi l e χ g⁻¹] i

variable {V} in

def rhoM {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (ξ : V.S3 l e χ K g1 →+* QbarL l) (g : K.fixingSubgroup) : Matrix (Fin 3) (Fin 3) (QbarL l) :=
  ((V.rho3 ξ g : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l))

abbrev HL (l : ℕ) [Fact l.Prime] (χ : Chi D) (K : IntermediateField ℚ QbarQ) : Subgroup GQ :=
  HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)

variable {V} in

abbrev rhoL {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (ξ : V.S3 l e χ K g1 →+* QbarL l) : HL V l χ K →* GL (Fin 3) (QbarL l) :=
  (V.rho3 ξ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))

def AllDat (φ : ∀ (l : ℕ) [Fact l.Prime] (_e : ℕ) (_χ : Chi D) (_K : IntermediateField ℚ QbarQ) (_g1 : GQ), Prop) :
    Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (g1 : GQ),
    Dat V l e χ K g1 → φ l e χ K g1

def AllPt (φ : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ),
    (V.S3 l e χ K g1 →+* QbarL l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (g1 : GQ),
    Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → φ l e χ K g1 ξ

def GenNeg : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ j : ℤ, j < 0 → ∀ x ∈ V.S3gr l e χ K g1 j,
    x ∈ Ideal.span {y | ∃ (g : K.fixingSubgroup) (i k : Fin 3), k < i ∧ y = ent V l e χ K g1 g i k}

def GenPos : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ j : ℤ, 0 < j → ∀ x ∈ V.S3gr l e χ K g1 j,
    x ∈ Ideal.span {y | ∃ (g : K.fixingSubgroup) (i k : Fin 3), i < k ∧ y = ent V l e χ K g1 g i k}

def GenAll : Prop := AllDat V fun l _ e χ K g1 =>
  Algebra.adjoin (V.Ol l) {y | ∃ (g : K.fixingSubgroup) (i k : Fin 3), y = ent V l e χ K g1 g i k} = ⊤

def GradedDegreeZeroIsLocal : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ x ∈ V.S3gr l e χ K g1 0, V.S3emb l e χ K g1 x ∉ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1) →
    ∃ y ∈ V.S3gr l e χ K g1 0, x * y = 1

def PtInt : Prop := AllPt V fun l _ e χ K g1 ξ => ∀ x ∈ V.S3gr l e χ K g1 0, ‖ξ x‖ ≤ 1

def PtLocal : Prop := AllPt V fun l _ e χ K g1 ξ =>
  ∀ x ∈ V.S3gr l e χ K g1 0, V.S3emb l e χ K g1 x ∈ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1) → ‖ξ x‖ < 1

def PtFin : Prop := AllPt V fun l _ _ _ _ _ ξ =>
  ∃ E' : IntermediateField ℚ_[l] (QbarL l), FiniteDimensional ℚ_[l] E' ∧ ∀ x, ξ x ∈ E'

def PtHat : Prop := AllPt V fun l _ e χ K g1 ξ =>
  ∃ (t : (QbarL l)ˣ) (φ : V.S3hat l e χ K g1 →+* QbarL l),
    φ.comp (algebraMap (V.Ol l) (V.S3hat l e χ K g1)) = V.jO l ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
    (∀ y ∈ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1), ‖φ y‖ < 1) ∧
    (∃ E' : IntermediateField ℚ_[l] (QbarL l), FiniteDimensional ℚ_[l] E' ∧ ∀ y, φ y ∈ E') ∧
    ∀ (j : ℤ), ∀ x ∈ V.S3gr l e χ K g1 j, φ (V.S3emb l e χ K g1 x) = (t : QbarL l) ^ j * ξ x

def PtCont : Prop := AllPt V fun _ _ _ _ _ _ ξ => Continuous (V.rho3 ξ)

def PtDual : Prop := AllPt V fun l _ _ _ K _ ξ =>
  ∀ g h : K.fixingSubgroup, (h : GQ) = V.cc * (g : GQ)⁻¹ * V.cc →
    rhoM ξ h = Jad3 (QbarL l) * (rhoM ξ g).transpose * Jad3 (QbarL l)

def PtZ : Prop := AllPt V fun l _ _ _ K g1 ξ =>
  ∀ g h : K.fixingSubgroup, (g : GQ) = g1 → (h : GQ) = V.cc * g1⁻¹ * V.cc →
    ∃ z : QbarL l, ‖z‖ = 1 ∧ rhoM ξ g - rhoM ξ h = Matrix.diagonal ![z, 0, -z]

def RingUq : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A → ¬ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l →
    ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) A → V.psiBar l e χ σ = 1 →
    V.unitaryGaloisRepresentation l e χ K g1 σ = 1

def PtCrys : Prop := AllPt V fun l _ e χ K _ ξ =>
  V.Crys l 3 (HL V l χ K) (V.plc l) (rhoL ξ) ∧
  ∀ τ, Formalism.MainNotions.UnitaryThreeHeightBounds.IndPl V l (HL V l χ K) τ → V.HT l 3 (HL V l χ K) (V.plc l) (rhoL ξ) τ = ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def PtChar : Prop := AllPt V fun l _ e χ K _ ξ =>
  ∀ s : K.fixingSubgroup, (s : GQ) ∈ V.Iq l →
    (rhoM ξ s).charpoly = ∏ i : Fin 3, (X - C (V.jO l (psi3 V l e χ i s)))

def PtTriple : Prop := AllPt V fun l _ e χ K _ ξ =>
  ∀ s : Fin 3 → K.fixingSubgroup, (∀ i, (s i : GQ) ∈ V.Iq l) →
    (rhoM ξ (s 0) - Matrix.scalar (Fin 3) (V.jO l (psi3 V l e χ 0 (s 0)))) *
      (rhoM ξ (s 1) - Matrix.scalar (Fin 3) (V.jO l (psi3 V l e χ 1 (s 1)))) *
      (rhoM ξ (s 2) - Matrix.scalar (Fin 3) (V.jO l (psi3 V l e χ 2 (s 2)))) = 0

def PtDiag : Prop := AllPt V fun l _ e χ K _ ξ =>
  ∀ (g : K.fixingSubgroup) (i : Fin 3), ‖rhoM ξ g i i - V.jO l (psi3 V l e χ i g)‖ < 1

def PtDet : Prop := AllPt V fun l _ e χ K g1 ξ =>
  ∀ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ' → V.rho3 ξ = V.rho3 ξ' → ξ = ξ'

def PtNeg : Prop := AllPt V fun l _ e χ K g1 ξ =>
  (∀ (g : K.fixingSubgroup) (i k : Fin 3), k < i → rhoM ξ g i k = 0) →
    ∀ j : ℤ, j < 0 → ∀ x ∈ V.S3gr l e χ K g1 j, ξ x = 0

def PtPos : Prop := AllPt V fun l _ e χ K g1 ξ =>
  (∀ (g : K.fixingSubgroup) (i k : Fin 3), i < k → rhoM ξ g i k = 0) →
    ∀ j : ℤ, 0 < j → ∀ x ∈ V.S3gr l e χ K g1 j, ξ x = 0

structure Pts : Prop where
  int : PtInt V
  loc : PtLocal V
  fin : PtFin V
  hat : PtHat V
  cont : PtCont V
  dual : PtDual V
  z : PtZ V
  uq : RingUq V
  crys : PtCrys V
  char : PtChar V
  triple : PtTriple V
  diag : PtDiag V
  det : PtDet V
  neg : PtNeg V
  pos : PtPos V

end Formalism.MainNotions.V.Pf.V3.P4
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3.P4

variable {D : D7} (V : VData D)

variable {V} in

def rhoHat {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (φ : V.S3hat l e χ K g1 →+* QbarL l) : K.fixingSubgroup →* GL (Fin 3) (QbarL l) :=
  (Units.map (φ.mapMatrix : Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1) →+*
    Matrix (Fin 3) (Fin 3) (QbarL l)).toMonoidHom).comp (V.rS3hat l e χ K g1)

def hatM (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ)
    (g : K.fixingSubgroup) : Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1) :=
  ((V.rS3hat l e χ K g1 g : GL (Fin 3) (V.S3hat l e χ K g1)) : Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1))

def IsHatPt {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (φ : V.S3hat l e χ K g1 →+* QbarL l) : Prop :=
  φ.comp (algebraMap (V.Ol l) (V.S3hat l e χ K g1)) = V.jO l ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
    (∀ y ∈ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1), ‖φ y‖ < 1) ∧
    ∃ E' : IntermediateField ℚ_[l] (QbarL l), FiniteDimensional ℚ_[l] E' ∧ ∀ y, φ y ∈ E'

def HatCrys : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ φ : V.S3hat l e χ K g1 →+* QbarL l, IsHatPt V φ →
    V.Crys l 3 (HL V l χ K) (V.plc l) ((rhoHat φ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) ∧
    ∀ τ, Formalism.MainNotions.UnitaryThreeHeightBounds.IndPl V l (HL V l χ K) τ →
      V.HT l 3 (HL V l χ K) (V.plc l) ((rhoHat φ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) τ =
        ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def HatChar : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ s : K.fixingSubgroup, (s : GQ) ∈ V.Iq l →
    (hatM V l e χ K g1 s).charpoly =
      ∏ i : Fin 3, (X - C (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ i s)))

def HatTriple : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ s : Fin 3 → K.fixingSubgroup, (∀ i, (s i : GQ) ∈ V.Iq l) →
    (hatM V l e χ K g1 (s 0) - Matrix.scalar (Fin 3) (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ 0 (s 0)))) *
      (hatM V l e χ K g1 (s 1) - Matrix.scalar (Fin 3) (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ 1 (s 1)))) *
      (hatM V l e χ K g1 (s 2) - Matrix.scalar (Fin 3) (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ 2 (s 2)))) = 0

def B_GenNeg : Prop := Giv V → StepPresT V → GenNeg V
def B_GenPos : Prop := Giv V → StepPresT V → GenPos V
def B_GenAll : Prop := Giv V → StepPresT V → GenAll V
def B_S0Loc : Prop := Giv V → StepPresT V → GradedDegreeZeroIsLocal V
def B_PtFin : Prop := Giv V → StepPresT V → PtFin V

def B_PtHat : Prop := Giv V → StepPresT V → PtInt V → PtLocal V → PtFin V → PtHat V

def B_HatCrys : Prop := Giv V → StepPresT V → HatCrys V
def B_HatChar : Prop := Giv V → StepPresT V → HatChar V
def B_HatTriple : Prop := Giv V → StepPresT V → HatTriple V

def F_NormInt : Prop := ∀ (l : ℕ) [Fact l.Prime] (z : QbarL l), IsIntegral ℤ_[l] z ↔ ‖z‖ ≤ 1

def F_NormO : Prop := ∀ (l : ℕ) [Fact l.Prime] (x : V.Ol l),
  ‖V.jO l x‖ ≤ 1 ∧ (x ∈ IsLocalRing.maximalIdeal (V.Ol l) ↔ ‖V.jO l x‖ < 1)

def F_CcSq : Prop := V.cc * V.cc = 1

def F_GK : Prop := ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
  (∀ g ∈ K.fixingSubgroup, ∀ x : GQ, x * g * x⁻¹ ∈ K.fixingSubgroup) ∧
  ∀ c : GQ, c ∉ K.fixingSubgroup → ∀ g : GQ, g ∈ K.fixingSubgroup ∨ g * c ∈ K.fixingSubgroup

def F_FinPlc : Prop := ∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A →
  ∃ q : ℕ, q.Prime ∧ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q

def F_PlcConj : Prop := ∀ (q : ℕ), q.Prime → ∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q →
  ∃ x : GQ, (∀ σ : GQ, σ ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) A ↔ x⁻¹ * σ * x ∈ V.Iq q) ∧
    ∀ σ : GQ, σ ∈ Formalism.MainNotions.V.Lang.Dec (F := ℚ) A ↔ x⁻¹ * σ * x ∈ V.Dq q

def F_PsiMul : Prop := ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (e : ℕ) (χ : Chi D) (g h : GQ),
  V.psi l e χ (g * h) = V.psi l e χ g * V.psi l e χ h ∧ V.psi l e χ 1 = 1

def F_LocOpenHL : Prop := ∀ (l : ℕ) [Fact l.Prime] (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
  Formalism.MainNotions.UnitaryThreeHeightBounds.LocOpen V l (HL V l χ K)

def S_PtInt : Prop := F_NormInt → PtInt V

def S_PtLocal : Prop := F_NormInt → GradedDegreeZeroIsLocal V → PtInt V → PtLocal V

def S_PtCont : Prop := PtHat V → PtCont V

def S_PtDual : Prop := PtDual V

def S_PtDiag : Prop := PtLocal V → PtDiag V

def S_PtZ : Prop := F_NormO V → F_PsiMul V → PtDual V → PtDiag V → PtZ V

def RingUq0 : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q → V.psiBar l e χ σ = 1 →
    V.unitaryGaloisRepresentation l e χ K g1 σ = 1

def S_RingUq0 : Prop := F_PsiMul V → RingUq0 V

def S_RingUq : Prop := F_CcSq V → F_GK → F_FinPlc → F_PlcConj V → F_PsiMul V → RingUq0 V → RingUq V

def S_PtCrys : Prop := Formalism.MainNotions.UnitaryThreeHeightBounds.FonIso V → F_LocOpenHL V → PtHat V → HatCrys V → PtCrys V

def S_PtChar : Prop := HatChar V → PtChar V
def S_PtTriple : Prop := HatTriple V → PtTriple V

def S_PtDet : Prop := GenAll V → PtDet V

def S_PtNeg : Prop := GenNeg V → PtNeg V
def S_PtPos : Prop := GenPos V → PtPos V

structure BridgeA : Prop where
  genNeg : B_GenNeg V
  genPos : B_GenPos V
  genAll : B_GenAll V
  gradedDegreeZeroLocal : B_S0Loc V
  ptFin : B_PtFin V
  ptHat : B_PtHat V
  hatCrys : B_HatCrys V
  hatChar : B_HatChar V
  hatTriple : B_HatTriple V

structure FieldA : Prop where
  normInt : F_NormInt
  normO : F_NormO V
  ccSq : F_CcSq V
  gk : F_GK
  finPlc : F_FinPlc
  plcConj : F_PlcConj V
  psiMul : F_PsiMul V
  locOpen : F_LocOpenHL V

structure StepsA : Prop where
  ptInt : S_PtInt V
  ptLocal : S_PtLocal V
  ptCont : S_PtCont V
  ptDual : S_PtDual V
  ptDiag : S_PtDiag V
  ptZ : S_PtZ V
  ringUq0 : S_RingUq0 V
  ringUq : S_RingUq V
  ptCrys : S_PtCrys V
  ptChar : S_PtChar V
  ptTriple : S_PtTriple V
  ptDet : S_PtDet V
  ptNeg : S_PtNeg V
  ptPos : S_PtPos V

end Formalism.MainNotions.V.Pf.V3.P4
end
end
