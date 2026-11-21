import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel
open GlobalTheory.LocMod (Place Dbl IsOne ofSplit)
open GlobalTheory.FinPl (SplitPt grpAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes

section One
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def volK {a : Type} [Fintype a] [DecidableEq a] (J : Subgroup (GL a k)) : ℝ :=
  ((KO k a).relIndex J : ℝ) / (J.relIndex (KO k a) : ℝ)

def IsCptOpen {a : Type} [Fintype a] [DecidableEq a] (J : Subgroup (GL a k)) : Prop :=
  IsOpen (J : Set (GL a k)) ∧ IsCompact (J : Set (GL a k))

variable [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def RowComb (ψ : AddChar k Circle) (ν : Measure k) (P : ℕ) (Q : GlobalTheory.StepData.Level (GL (n ⊕ Fin c) k))
    (h : GL (n ⊕ Fin c) k) (e : GL (n ⊕ Fin c) k →₀ ℂ) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A), IsSmoothRep σ →
    ∀ L : A →ₗ[ℂ] ℂ, GlobalTheory.RootEx.IsNEquiv ψ P σ L → ∀ v : A, (∀ x : Q.J, σ x v = (Q.lam x : ℂ) • v) →
      GlobalTheory.PosOne.toOne ν σ P L (σ h v) = GlobalTheory.PosOne.comb e fun g => L (σ (g * h) v)

example {a : Type} [Fintype a] [DecidableEq a] : volK (KO k a) = 1 := by simp [volK]

example (ψ : AddChar k Circle) (ν : Measure k) (Q : GlobalTheory.StepData.Level (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) :
    RowComb ψ ν 1 Q h (Finsupp.single 1 1) := fun A _ _ σ _ L _ v _ => by
  rw [GlobalTheory.PosOne.toOne_one, GlobalTheory.PosOne.comb, Finsupp.sum_single_index (by simp)]
  simp

end One

section Many
variable {D : D7} {I : Type} [Fintype I] [DecidableEq I] {k : I → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
  [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def places (q : ∀ i, SplitPt D (k i)) (v : GlobalTheory.FinPl.Pl D) : Prop := ∃ i, (q i).v = v

def IsUnitPair {V : HSp D} (G R : Subgroup (GA D V)) (K : Set (GA D V)) (ρ : Measure (R.subgroupOf G)) (μ : Measure G) : Prop :=
  μ.IsHaarMeasure ∧ μ {h | h.1 ∈ K} = 1 ∧ ρ.IsHaarMeasure ∧ ρ {r | r.1.1 ∈ K} = 1

def IsVac (q : ∀ i, SplitPt D (k i)) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}
    (FS : ∀ i, GlobalTheory.LocMod.Frame (k i) S.rank Y') (FT : ∀ i, GlobalTheory.LocMod.Frame (k i) T.rank Y) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ i, ∃ Tm, (ofSplit (q i)).IsModel ψ (FS i) (FT i) Tm ∧ ∀ O, IsOne O → Tm O = f

def put (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (d : I → WO S T →₀ ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  (Finset.univ : Finset I).toList.foldr (fun i f' => GlobalTheory.SeeSaw.comb ψ S T (d i) f') f

def biPut (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (d : I → WO A S →₀ ℂ) (d' : I → WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  (Finset.univ : Finset I).toList.foldr (fun i C' => biComb ψ A S A' (d i) (d' i) C') C

end Many

end GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes
end
