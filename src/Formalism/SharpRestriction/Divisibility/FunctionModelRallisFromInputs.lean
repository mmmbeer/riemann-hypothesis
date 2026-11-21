import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace Formalism.MainNotions.PDVS

open Formalism.BasicNotions MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TParity {D : D7} (P : TH.TPar D) : Prop :=
  ∀ τ, (∀ i, ∃ n : ℤ, P.u τ i = (n : ℚ) + 1 / 2) ∧ (∀ i, ∃ n : ℤ, P.v τ i = (n : ℚ)) ∧
    (∀ j, ∃ n : ℤ, P.b τ j = (n : ℚ)) ∧ ∀ j, ∃ n : ℤ, P.e τ j = (n : ℚ)

def NCGaps {D : D7} (P : TH.TPar D) : Prop :=
  ∀ j : ℕ, j ≤ D.R.m → ∀ τ, ∀ x ∈ P.Dpar j τ, ∀ y ∈ P.Dpar j τ, x.2 ≠ y.2 →
    ((D.R.r + D.R.m * P.t : ℕ) : ℚ) ^ 3 < |x.1 - y.1|

def car {D : D7} (X : ThetaX D) (μ : ℕ → X.Chr) (s i : ℕ) : X.Chr :=
  if Even i then μ s * X.etaT⁻¹ else μ s

def Hyp3 {D : D7} (X : ThetaX D) (P : TH.TPar D) : Prop :=
  P.Interlace ∧ TParity P ∧ P.Centred ∧ NCGaps P ∧ ∀ τ, P.eta τ = -X.infTy X.etaT τ

def IsMu {D : D7} (X : ThetaX D) (P : TH.TPar D) (μ : ℕ → X.Chr) : Prop :=
  ∀ (j : Fin D.R.m) τ, X.infTy (μ (j.1 + 1)) τ = -P.e τ j

def IsDv {D : D7} (X : ThetaX D) (P : TH.TPar D) (j : ℕ) (F : X.AF (X.Ys P.t j)) : Prop :=
  X.conjAF _ F ∈ X.typ _ (P.Dpar j)

def vth {D : D7} (X : ThetaX D) (t : ℕ) (μ : ℕ → X.Chr) (j : ℕ)
    (Φ : X.Sch (X.Ys t (j + 1)) (X.Ys t j)) : X.cusp (X.Ys t (j + 1)) →ₗ[ℂ] X.AF (X.Ys t j) :=
  X.th _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) Φ

def bB {D : D7} (X : ThetaX D) (t j : ℕ) (pos : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j))
    (s : X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (φ : X.AF (X.Xs t j)) (F : X.cusp (X.Ys t j)) : ℂ :=
  X.Bj t j pos s (X.conjAF _ φ) F

def IsAutRep {D : D7} (X : ThetaX D) (V : TH.HSp D) (π : Submodule ℂ (X.AF V)) : Prop :=
  X.IsStable V π ∧ π ≠ ⊥ ∧ ∀ π' : Submodule ℂ (X.AF V), π' ≤ π → X.IsStable V π' → π' = ⊥ ∨ π' = π

def PerNZ {D : D7} (X : ThetaX D) (t j : ℕ) (φ : X.AF (X.Xs t j)) (F : X.cusp (X.Ys t j)) : Prop :=
  (j < D.R.m ∧ ∃ pos s, bB X t j pos s φ F ≠ 0) ∨
    ∃ h : j = D.R.m, X.Btop (X.Xs t j) (X.Ys t j) (h ▸ X.iYXm t) (X.conjAF _ φ) F ≠ 0

section Part1

variable {D : D7}

def ThetaDescentTowerConditions (X : ThetaX D) (P : TH.TPar D) (μ : ℕ → X.Chr) : Prop :=
  (∀ j, j < D.R.m → ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j)) (F : X.cusp (X.Ys P.t (j + 1))),
    IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) → vth X P.t μ j Φ F ∈ X.cusp (X.Ys P.t j) →
    IsDv X P j (vth X P.t μ j Φ F)) ∧
  (∀ j, j < D.R.m → ∀ i, 1 ≤ i → i ≤ (sigYD D.R j).2 →
    ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.YsLow P.t j i)) (F : X.cusp (X.Ys P.t (j + 1))),
    IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
    X.th _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) Φ F = 0)

def Conclusion1 (D : D7) (X : ThetaX D) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ThetaDescentTowerConditions X P μ

def cenY (P : TH.TPar D) (j : ℕ) (τ : D.what₂.Tau) : ℚ :=
  (if h : j < D.R.m then -P.e τ ⟨j, h⟩ else 0) + (if Odd j then P.eta τ else 0)

def side (S : TH.SPar) (c : ℚ) (sg up : Bool) : List ℚ :=
  ((S.filter fun x => x.2 = sg ∧ (if up then c < x.1 else x.1 < c)).image fun x => x.1 - c).sort (· ≥ ·)

def alL (P : TH.TPar D) (j : ℕ) (τ : D.what₂.Tau) : List ℚ := side (P.Dpar j τ) (cenY P j τ) true true

def beL (P : TH.TPar D) (j : ℕ) (τ : D.what₂.Tau) : List ℚ := side (P.Dpar j τ) (cenY P j τ) true false

def gaL (P : TH.TPar D) (j : ℕ) (τ : D.what₂.Tau) : List ℚ := side (P.Dpar j τ) (cenY P j τ) false true

def deL (P : TH.TPar D) (j : ℕ) (τ : D.what₂.Tau) : List ℚ := side (P.Dpar j τ) (cenY P j τ) false false

def Comb1 (X : ThetaX D) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ j, j < D.R.m → ∀ τ,
    Formalism.MainNotions.SchurIrreducible.DataAR P.t (alL P j τ) (beL P j τ) (gaL P j τ) (deL P j τ) ∧
    (¬ ∃ a, TH.lamA (alL P j τ) (beL P j τ) (gaL P j τ) (deL P j τ) a = ((P.t : ℚ) + 1) / 2) ∧
    (gaL P j τ).length + (deL P j τ).length = (sigYD D.R j).2 ∧
    (sigYD D.R j).2 ≤ (alL P j τ).length + (beL P j τ).length ∧
    (∀ x : ℚ × Bool, x ∈ P.Dpar (j + 1) τ ↔
      (x.2 = true ∧ x.1 - (cenY P j τ + (if Odd j then -P.eta τ else P.eta τ)) ∈
        alL P j τ ++ TH.block P.t ++ deL P j τ) ∨
      (x.2 = false ∧ x.1 - (cenY P j τ + (if Odd j then -P.eta τ else P.eta τ)) ∈ gaL P j τ ++ beL P j τ))

def ArthurRepresentationUpDown (A : TH.ProvA) : Prop := Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine A

def ShareLowerBound (A : TH.ProvA) : Prop := Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth A

def PlancherelDifferenceBound (X : ThetaX D) (A : TH.ProvA) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, j < D.R.m →
    (∀ τ, Formalism.MainNotions.SchurIrreducible.ARiiiDown A (TH.lamA (alL P j τ) (beL P j τ) (gaL P j τ) (deL P j τ))
      (TH.lamA' P.t (alL P j τ) (beL P j τ) (gaL P j τ) (deL P j τ))) →
    ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j)) (F : X.cusp (X.Ys P.t (j + 1))),
      IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) → vth X P.t μ j Φ F ∈ X.cusp (X.Ys P.t j) →
      IsDv X P j (vth X P.t μ j Φ F)

def DegreeNormalizationFormula (X : ThetaX D) (A : TH.ProvA) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, j < D.R.m →
    ∀ i, 1 ≤ i → i ≤ (sigYD D.R j).2 →
    ∀ (Φ : X.Sch (X.Ys P.t (j + 1)) (X.YsLow P.t j i)) (F : X.cusp (X.Ys P.t (j + 1))),
      IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
      X.th _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) Φ F ≠ 0 →
      ∃ (τ : D.what₂.Tau)
        (MM : TH.GKMod ((alL P j τ).length + (beL P j τ).length - i) ((gaL P j τ).length + (deL P j τ).length - i))
        (f : TH.Pol ((alL P j τ).length + (beL P j τ).length - i) ((gaL P j τ).length + (deL P j τ).length - i)
            ((alL P j τ).length + (deL P j τ).length + P.t) ((gaL P j τ).length + (beL P j τ).length) →ₗ[ℂ]
          TensorProduct ℂ MM.V
            (A.ds _ _ (TH.lamA' P.t (alL P j τ) (beL P j τ) (gaL P j τ) (deL P j τ))).HK.V),
        TH.IsIntw (A.fock _ _ _ _) MM
          (A.ds _ _ (TH.lamA' P.t (alL P j τ) (beL P j τ) (gaL P j τ) (deL P j τ))).HK f ∧ f ≠ 0

def Adm1 (X : ThetaX D) (A : TH.ProvA) : Prop := ArthurRepresentationUpDown A ∧ ShareLowerBound A ∧ PlancherelDifferenceBound X A ∧ DegreeNormalizationFormula X A

def IntegralityFromMetric (X : ThetaX D) (A : TH.ProvA) : Prop := Adm1 X A → Conclusion1 D X


end Part1

section Instance

variable {D : D7}

def muOf (T : ThetaX D) (μ : D.what₂.Tup) : ℕ → T.Chr := fun s => T.chrOf μ s




end Instance

structure Loc2 (D : D7) (X : ThetaX D) where
  GA : TH.HSp D → Type
  [gaGrp : ∀ V, Group (GA V)]
  actA : ∀ V, GA V →* Module.End ℂ (X.AF V)
  actA_cusp : ∀ V g, ∀ F ∈ X.cusp V, actA V g F ∈ X.cusp V
  om : ∀ W V, X.Chr → X.Chr → GA W →* Module.End ℂ (X.Sch W V)
  posDn : ∀ t j, Odd t → D.R.r + 5 ≤ t → j + 1 < D.R.m → X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) →
    X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j)
  Q : ∀ t j, X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) → Type
  [msQ : ∀ t j p, MeasurableSpace (Q t j p)]
  nu : ∀ t j p, Measure (Q t j p)
  rep : ∀ t j p, Q t j p → GA (X.Ys t (j + 1))
  SchP : ℕ → ℕ → Type
  tens : ∀ t j, X.Sch (X.Xs t j) (X.Xs t (j + 1)) →
    X.FJd (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) → SchP t j
  perP : ∀ t j, X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) → X.Chr → SchP t j →
    X.cusp (X.Xs t j) → X.cusp (X.Ys t (j + 1)) → ℂ
  perP_tens : ∀ t j p χ Φ' s' φ F,
    perP t j p χ (tens t j Φ' s') φ F = bB X t (j + 1) p s' (X.th _ _ χ χ Φ' φ) F
  flat : ∀ t j, X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)) →
    X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j) → X.Sch (X.Ys t (j + 1)) (X.Ys t j) → SchP t j
  see : ∀ t j, X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j) → X.Sch (X.Ys t (j + 1)) (X.Ys t j) →
    X.Sch (X.Xs t j) (X.Xs t (j + 1))

attribute [instance] Loc2.gaGrp Loc2.msQ

section Part2

variable {D : D7} {X : ThetaX D}

def Loc2.trC (U : Loc2 D X) (V : TH.HSp D) (h : U.GA V) (F : X.cusp V) : X.cusp V :=
  ⟨U.actA V h F, U.actA_cusp V h F F.2⟩

def Loc2.integrand (U : Loc2 D X) (t : ℕ) (μ : ℕ → X.Chr) (j : ℕ)
    (p : X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)))
    (s : X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (Φ : X.Sch (X.Ys t (j + 1)) (X.Ys t j))
    (φ : X.cusp (X.Xs t j)) (F : X.cusp (X.Ys t (j + 1))) (x : U.Q t j p) : ℂ :=
  U.perP t j p (μ (j + 1))
    (U.flat t j p s (U.om _ _ (car X μ (j + 1) (j + 1)) (car X μ (j + 1) j) (U.rep t j p x) Φ)) φ
    (U.trC _ (U.rep t j p x) F)

def Unfold (U : Loc2 D X) (t : ℕ) (ho : Odd t) (hg : D.R.r + 5 ≤ t) (μ : ℕ → X.Chr) : Prop :=
  ∀ j, ∀ hj : j + 1 < D.R.m, ∀ (p : X.Pos (X.Xs t (j + 1)) (X.Ys t (j + 1)) (X.iXYs t (j + 1)))
    (s : X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (Φ : X.Sch (X.Ys t (j + 1)) (X.Ys t j))
    (φ : X.cusp (X.Xs t j)) (F : X.cusp (X.Ys t (j + 1))) (G : X.cusp (X.Ys t j)),
    (G : X.AF (X.Ys t j)) = vth X t μ j Φ F →
    Integrable (U.integrand t μ j p s Φ φ F) (U.nu t j p) ∧
    bB X t j (U.posDn t j ho hg hj p) s (φ : X.AF (X.Xs t j)) G = ∫ x, U.integrand t μ j p s Φ φ F x ∂(U.nu t j p)

def SeeSaw (U : Loc2 D X) (t : ℕ) (μ : ℕ → X.Chr) : Prop :=
  ∀ j, ∀ h : j + 1 = D.R.m, ∀ (p : X.Pos (X.Xs t j) (X.Ys t j) (X.iXYs t j))
    (s : X.FJd (X.Xs t j) (X.Ys t j) (X.iXYs t j)) (Φ : X.Sch (X.Ys t (j + 1)) (X.Ys t j))
    (φ : X.cusp (X.Xs t j)) (F : X.cusp (X.Ys t (j + 1))) (G : X.cusp (X.Ys t j)),
    (G : X.AF (X.Ys t j)) = vth X t μ j Φ F →
    bB X t j p s (φ : X.AF (X.Xs t j)) G =
      X.Btop (X.Xs t (j + 1)) (X.Ys t (j + 1)) (h ▸ X.iYXm t)
        (X.conjAF _ (X.th _ _ (μ (j + 1)) (μ (j + 1)) (U.see t j s Φ) φ)) F

def Conclusion2 (D : D7) (X : ThetaX D) (U : Loc2 D X) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → Unfold U P.t P.t_odd P.t_ge μ ∧ SeeSaw U P.t μ

def kernel_index_full_lattice (D : D7) (X : ThetaX D) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, j < D.R.m →
  ∀ (φ' : X.cusp (X.Xs P.t j)) (Φ' : X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))), Φ' ∈ X.fact _ _ →
    Φ' ∈ X.kfin _ _ → (φ' : X.AF (X.Xs P.t j)) ∈ X.typeX P j →
  ∀ F : X.cusp (X.Ys P.t (j + 1)), IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
    PerNZ X P.t (j + 1) (X.th _ _ (μ (j + 1)) (μ (j + 1)) Φ' φ') F →
  ∃ Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j), Φ ∈ X.fact _ _ ∧ Φ ∈ X.kfin _ _ ∧
    ∀ G : X.cusp (X.Ys P.t j), (G : X.AF (X.Ys P.t j)) = vth X P.t μ j Φ F → PerNZ X P.t j (φ' : X.AF (X.Xs P.t j)) G

def adm2b (U : Loc2 D X) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, j + 1 < D.R.m →
  ∀ (φ' : X.cusp (X.Xs P.t j)) (Φ' : X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))), Φ' ∈ X.fact _ _ →
    Φ' ∈ X.kfin _ _ → (φ' : X.AF (X.Xs P.t j)) ∈ X.typeX P j →
  ∀ (F : X.cusp (X.Ys P.t (j + 1))), IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
  ∀ (p : X.Pos (X.Xs P.t (j + 1)) (X.Ys P.t (j + 1)) (X.iXYs P.t (j + 1)))
    (s' : X.FJd (X.Xs P.t (j + 1)) (X.Ys P.t (j + 1)) (X.iXYs P.t (j + 1))),
    bB X P.t (j + 1) p s' (X.th _ _ (μ (j + 1)) (μ (j + 1)) Φ' φ') F ≠ 0 →
  ∃ Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j), Φ ∈ X.fact _ _ ∧ Φ ∈ X.kfin _ _ ∧
    ∃ s, ∫ x, U.integrand P.t μ j p s Φ φ' F x ∂(U.nu P.t j p) ≠ 0

def ThetaPositivityCondition (D : D7) (X : ThetaX D) : Prop :=
  ∀ (P : TH.TPar D) (j : ℕ), j + 1 = D.R.m → Nonempty (X.Pos (X.Xs P.t j) (X.Ys P.t j) (X.iXYs P.t j))

def adm2c (U : Loc2 D X) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → ∀ j, ∀ h : j + 1 = D.R.m,
  ∀ (φ' : X.cusp (X.Xs P.t j)) (Φ' : X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))), Φ' ∈ X.fact _ _ →
    Φ' ∈ X.kfin _ _ → (φ' : X.AF (X.Xs P.t j)) ∈ X.typeX P j →
  ∀ F : X.cusp (X.Ys P.t (j + 1)), IsDv X P (j + 1) (F : X.AF (X.Ys P.t (j + 1))) →
    X.Btop (X.Xs P.t (j + 1)) (X.Ys P.t (j + 1)) (h ▸ X.iYXm P.t)
      (X.conjAF _ (X.th _ _ (μ (j + 1)) (μ (j + 1)) Φ' φ')) F ≠ 0 →
  ∃ Φ : X.Sch (X.Ys P.t (j + 1)) (X.Ys P.t j), Φ ∈ X.fact _ _ ∧ Φ ∈ X.kfin _ _ ∧
    ∃ s, X.Btop (X.Xs P.t (j + 1)) (X.Ys P.t (j + 1)) (h ▸ X.iYXm P.t)
      (X.conjAF _ (X.th _ _ (μ (j + 1)) (μ (j + 1)) (U.see P.t j s Φ) φ')) F ≠ 0

def NonvanishingFromUnfolding (U : Loc2 D X) : Prop := Conclusion2 D X U → ThetaPositivityCondition D X → adm2b U → adm2c U → kernel_index_full_lattice D X


end Part2

section Part3

open NumberField IsDedekindDomain

section OnePair

open Formalism.MainNotions.SchurIrreducible

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

def dblInt {π : O.Pi} (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) (s : ℂ) : ℂ :=
  ∫ g : O.GQ × O.GQ, O.Eis (O.tensor φ₁ φ₂) s (O.io g.1 g.2) * star (O.form π f₁ g.1) * O.form π f₂ g.2 *
    O.muInv g.2 ∂(O.muG.prod O.muG)

def SWat (t' : ℕ) : Prop :=
  ∀ ph : O.SchD, O.factD ph → ∀ g : O.GhQ,
    Integrable (O.thetaD ph g) O.muH ∧ AnalyticAt ℂ (fun s : ℂ => O.Eis ph s g) ((t' : ℂ) / 2) ∧
      Ith O ph g = O.Eis ph ((t' : ℂ) / 2) g

def FubOK : Prop :=
  IsFiniteMeasure O.muG ∧ ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch), O.good φ₁ → O.good φ₂ →
    Integrable (fun x : (O.GQ × O.GQ) × O.HQ =>
      star (O.form π f₁ x.1.1) * O.form π f₂ x.1.2 * (O.thetaK φ₁ x.1.1 x.2 * star (O.thetaK φ₂ x.1.2 x.2)))
      ((O.muG.prod O.muG).prod O.muH)

def MerOK (t' : ℕ) (Vh : O.Pi → Prop) : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) (S : Finset (Pl F)), Vh π →
    RFData O π f₁ f₂ φ₁ φ₂ S ((t' : ℂ) / 2) →
    MeromorphicOn (dblInt O f₁ f₂ φ₁ φ₂) {s : ℂ | 0 < s.re} ∧
    AnalyticAt ℂ (dblInt O f₁ f₂ φ₁ φ₂) ((t' : ℂ) / 2) ∧
    ∀ v ∈ S, MeromorphicOn (O.Zv π f₁ f₂ φ₁ φ₂ v) {s : ℂ | 0 < s.re} ∧
      AnalyticAt ℂ (O.Zv π f₁ f₂ φ₁ φ₂ v) ((t' : ℂ) / 2)

def LCont (π : O.Pi) (S : Finset (Pl F)) (s₀ : ℂ) (g : ℂ → ℂ) : Prop :=
  ∃ U : Set ℂ, ∃ σ : ℝ, IsOpen U ∧ IsPreconnected U ∧ U ⊆ {s : ℂ | 0 < s.re} ∧ s₀ ∈ U ∧ AnalyticOnNhd ℂ g U ∧
    (∀ σ' : ℝ, ∃ s ∈ U, σ' < s.re) ∧
    ∀ s ∈ U, σ < s.re → HasProd (fun v : {v : Pl F // v ∉ S} => O.Lv π v (s + 1 / 2)) (g s)

def W3at (t' : ℕ) (Vh : O.Pi → Prop) : Prop :=
  ∀ π : O.Pi, Vh π → ∀ (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch), O.good φ₁ → O.good φ₂ →
    AnalyticAt ℂ (dblInt O f₁ f₂ φ₁ φ₂) ((t' : ℂ) / 2) ∧
    thetaIP O f₁ f₂ φ₁ φ₂ = dblInt O f₁ f₂ φ₁ φ₂ ((t' : ℂ) / 2)

def rallisRHS {π : O.Pi} (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) (S : Finset (Pl F)) (t' : ℕ) (g : ℂ → ℂ) : ℂ :=
  O.be π f₁ f₂ * (g ((t' : ℂ) / 2) / dS O S ((t' : ℂ) / 2)) * ZS O f₁ f₂ φ₁ φ₂ S ((t' : ℂ) / 2)

def LemmaRat (t' : ℕ) (Vh : O.Pi → Prop) : Prop :=
  ∀ (π : O.Pi) (S : Finset (Pl F)) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) (g : ℂ → ℂ), Vh π →
    RFData O π f₁ f₂ φ₁ φ₂ S ((t' : ℂ) / 2) → LCont O π S ((t' : ℂ) / 2) g →
    thetaIP O f₁ f₂ φ₁ φ₂ = rallisRHS O f₁ f₂ φ₁ φ₂ S t' g

end OnePair

structure Loc3 (D : D7) (X : ThetaX D) where

  spl : TH.HSp D → TH.HSp D → X.Chr → X.Chr → Prop

  aux : X.Chr → Prop

  rf : ∀ (A B : TH.HSp D) (_χ _χ' : X.Chr), Formalism.MainNotions.SchurIrreducible.RFObj D.host.F D.host.E A B

  cf : ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (π : (rf A B χ χ').Pi), (rf A B χ χ').Vec π → X.cusp A

  sc : ∀ (A B : TH.HSp D) (χ χ' : X.Chr), (rf A B χ χ').Sch → X.Sch A B

  sc_good : ∀ A B χ χ' φ, (rf A B χ χ').good φ → sc A B χ χ' φ ∈ X.fact A B ∧ sc A B χ χ' φ ∈ X.kfin A B

  cPair : TH.HSp D → TH.HSp D → ℝ
  cPair_pos : ∀ A B, 0 < cPair A B

variable {D : D7} {X : ThetaX D}

def cfc (R : Loc3 D X) (A B : TH.HSp D) (χ χ' : X.Chr) {π : (R.rf A B χ χ').Pi}
    (f : (R.rf A B χ χ').Vec π) : X.cusp A :=
  ⟨X.conjAF A (R.cf A B χ χ' π f : X.AF A), X.conjAF_cusp A _ (R.cf A B χ χ' π f).2⟩

def lift3 (R : Loc3 D X) (A B : TH.HSp D) (χ χ' : X.Chr) {π : (R.rf A B χ χ').Pi}
    (f : (R.rf A B χ χ').Vec π) (φ : (R.rf A B χ χ').Sch) : X.AF B :=
  X.th A B χ χ' (R.sc A B χ χ' φ) (cfc R A B χ χ' f)

def Range3 (A B : TH.HSp D) (t' : ℕ) : Prop :=
  1 ≤ A.rank ∧ B.rank = A.rank + t' ∧ 1 ≤ t' ∧ (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ Formalism.MainNotions.SchurIrreducible.wittIdx B < t')

def IsLow (B B' : TH.HSp D) (i : ℕ) : Prop :=
  B.rank = B'.rank + 2 * i ∧ ∃ (ι : B'.V →ₗ[D.host.E] B.V) (W : Submodule D.host.E B.V),
    HSpace.IsIsomEmb B' B ι ∧ Module.finrank D.host.E W = i ∧ (∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) ∧
    ∀ x ∈ W, ∀ y, B.hT x (ι y) = 0

def LowVan (R : Loc3 D X) (A B : TH.HSp D) (χ χ' : X.Chr) (π : (R.rf A B χ χ').Pi) : Prop :=
  ∀ (i : ℕ) (B' : TH.HSp D), 1 ≤ i → i ≤ Formalism.MainNotions.SchurIrreducible.wittIdx B → IsLow B B' i →
    ∀ (f : (R.rf A B χ χ').Vec π) (Φ : X.Sch A B'), X.th A B' χ χ' Φ (cfc R A B χ χ' f) = 0

def V3 (R : Loc3 D X) (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ) (π : (R.rf A B χ χ').Pi) : Prop :=
  0 < Formalism.MainNotions.SchurIrreducible.wittIdx B → t' ≤ A.rank → LowVan R A B χ χ' π

def PointsLemma (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (t' : ℕ), Range3 A B t' →
  ∃ c : ℝ, 0 < c ∧ ∀ χ χ' : X.Chr, R.spl A B χ χ' →
    ∀ (π : (R.rf A B χ χ').Pi) (S : Finset (Formalism.MainNotions.SchurIrreducible.Pl D.host.F)) (f₁ f₂ : (R.rf A B χ χ').Vec π)
      (φ₁ φ₂ : (R.rf A B χ χ').Sch) (g : ℂ → ℂ), V3 R A B χ χ' t' π →
      Formalism.MainNotions.SchurIrreducible.RFData (R.rf A B χ χ') π f₁ f₂ φ₁ φ₂ S ((t' : ℂ) / 2) →
      LCont (R.rf A B χ χ') π S ((t' : ℂ) / 2) g →
      ∀ G₁ : X.cusp B, (G₁ : X.AF B) = lift3 R A B χ χ' f₁ φ₁ →
        X.pet B (lift3 R A B χ χ' f₂ φ₂) G₁ = (c : ℂ) * rallisRHS (R.rf A B χ χ') f₁ f₂ φ₁ φ₂ S t' g

def FunctionModelRallis (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ), Range3 A B t' → R.spl A B χ χ' →
    LemmaRat (R.rf A B χ χ') t' (V3 R A B χ χ' t')

def adm3a (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ), Range3 A B t' → R.spl A B χ χ' → Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 →
    SWat (R.rf A B χ χ') t'

def adm3b (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ), Range3 A B t' → R.spl A B χ χ' → A.rank < t' → SWat (R.rf A B χ χ') t'

def IntegralityRemainder (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ), Range3 A B t' → R.spl A B χ χ' → 0 < Formalism.MainNotions.SchurIrreducible.wittIdx B →
    t' ≤ A.rank → W3at (R.rf A B χ χ') t' (LowVan R A B χ χ')

def DoublingBasicIdentity' (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr), R.spl A B χ χ' → Formalism.MainNotions.SchurIrreducible.DoublingBasicIdentity (R.rf A B χ χ')

def TripleIntegralConvergence (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ), Range3 A B t' → R.spl A B χ χ' → FubOK (R.rf A B χ χ')

def DoublingMeromorphicContinuation (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr) (t' : ℕ), Range3 A B t' → R.spl A B χ χ' →
    MerOK (R.rf A B χ χ') t' (V3 R A B χ χ' t')

def TripleInnerProductCondition (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ (A B : TH.HSp D) (χ χ' : X.Chr), R.spl A B χ χ' → ∀ (π : (R.rf A B χ χ').Pi) (f₁ f₂ : (R.rf A B χ χ').Vec π)
    (φ₁ φ₂ : (R.rf A B χ χ').Sch), (R.rf A B χ χ').good φ₁ → (R.rf A B χ χ').good φ₂ →
    ∀ G₁ : X.cusp B, (G₁ : X.AF B) = lift3 R A B χ χ' f₁ φ₁ →
      X.pet B (lift3 R A B χ χ' f₂ φ₂) G₁ =
        (R.cPair A B : ℂ) * Formalism.MainNotions.SchurIrreducible.thetaIP (R.rf A B χ χ') f₁ f₂ φ₁ φ₂

def Adm3 (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  adm3a D X R ∧ adm3b D X R ∧ IntegralityRemainder D X R ∧ DoublingBasicIdentity' D X R ∧ TripleIntegralConvergence D X R ∧ DoublingMeromorphicContinuation D X R

def FunctionModelRallisFromInputs (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop := Adm3 D X R → FunctionModelRallis D X R

def TowerRallisLemma (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop := Adm3 D X R → TripleInnerProductCondition D X R → PointsLemma D X R





def DefiniteLiftChain (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.ThetaX D) : Prop :=
  ∀ P : Formalism.BasicNotions.TH.TPar D, Hyp3 X P →
  ∃ (μ : ℕ → X.Chr) (π : ∀ j : ℕ, Submodule ℂ (X.AF (X.Xs P.t j))), IsMu X P μ ∧
    (∀ j, j ≤ D.R.m → IsAutRep X _ (π j) ∧ π j ≤ X.cusp _ ∧ π j ≤ X.typeX P j) ∧
    ∀ j, j < D.R.m → ∀ φ ∈ π (j + 1),
      ∃ (N : ℕ) (Φ' : Fin N → X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))) (φ' : Fin N → X.cusp (X.Xs P.t j)),
        (∀ a, Φ' a ∈ X.fact _ _ ∧ Φ' a ∈ X.kfin _ _ ∧ (φ' a : X.AF (X.Xs P.t j)) ∈ π j) ∧
        φ = ∑ a, X.th _ _ (μ (j + 1)) (μ (j + 1)) (Φ' a) (φ' a)

def AllSplit (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ w ∈ S, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) w

def SphSplit (X : ThetaX D) (V : TH.HSp D) (π : Submodule ℂ (X.AF V)) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), AllSplit D S ∧ π ⊓ X.sphOff V S ≠ ⊥

def IsLink (X : ThetaX D) (P : TH.TPar D) (j : ℕ) (π : Submodule ℂ (X.AF (X.Xs P.t j))) : Prop :=
  IsAutRep X _ π ∧ π ≤ X.cusp _ ∧ π ≤ X.typeX P j ∧ SphSplit X _ π

def IsAuxiliaryHeckeCharacter (R : Loc3 D X) (P : TH.TPar D) (μ : ℕ → X.Chr) : Prop :=
  ∀ j, j < D.R.m → R.aux (μ (j + 1)) ∧ R.spl (X.Xs P.t j) (X.Xs P.t (j + 1)) (μ (j + 1)) (μ (j + 1))

def SumLifts (X : ThetaX D) (P : TH.TPar D) (μ : ℕ → X.Chr) (j : ℕ) (π : Submodule ℂ (X.AF (X.Xs P.t j)))
    (π' : Submodule ℂ (X.AF (X.Xs P.t (j + 1)))) : Prop :=
  ∀ φ ∈ π', ∃ (N : ℕ) (Φ' : Fin N → X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))) (φ' : Fin N → X.cusp (X.Xs P.t j)),
    (∀ a, Φ' a ∈ X.fact _ _ ∧ Φ' a ∈ X.kfin _ _ ∧ (φ' a : X.AF (X.Xs P.t j)) ∈ π) ∧
    φ = ∑ a, X.th _ _ (μ (j + 1)) (μ (j + 1)) (Φ' a) (φ' a)

def IsChain (X : ThetaX D) (P : TH.TPar D) (μ : ℕ → X.Chr) : ∀ j, Submodule ℂ (X.AF (X.Xs P.t j)) → Prop
  | 0, π => IsLink X P 0 π
  | j + 1, π' => IsLink X P (j + 1) π' ∧ ∃ π, IsChain X P μ j π ∧ SumLifts X P μ j π π'

theorem IsChain.link {P : TH.TPar D} {μ : ℕ → X.Chr} : ∀ {j} {π}, IsChain X P μ j π → IsLink X P j π
  | 0, _, h => h
  | _ + 1, _, h => h.1

def ThetaCuspidalityCondition (D : D7) (X : ThetaX D) : Prop :=
  ∀ V : TH.HSp D, V.SigOK → V.IsDefinite → X.cusp V = ⊤

def AuxiliaryCharactersExist (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P →
    (∃ μ : ℕ → X.Chr, IsMu X P μ ∧ IsAuxiliaryHeckeCharacter R P μ) ∧ ∃ π : Submodule ℂ (X.AF (X.Xs P.t 0)), IsLink X P 0 π

def ChainPeriodExistence (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → IsAuxiliaryHeckeCharacter R P μ → ∀ j, j < D.R.m →
  ∀ π : Submodule ℂ (X.AF (X.Xs P.t j)), IsChain X P μ j π →
  ∃ (p : (R.rf (X.Xs P.t j) (X.Xs P.t (j + 1)) (μ (j + 1)) (μ (j + 1))).Pi)
    (S : Finset (Formalism.MainNotions.SchurIrreducible.Pl D.host.F))
    (f₁ f₂ : (R.rf (X.Xs P.t j) (X.Xs P.t (j + 1)) (μ (j + 1)) (μ (j + 1))).Vec p)
    (φ₁ φ₂ : (R.rf (X.Xs P.t j) (X.Xs P.t (j + 1)) (μ (j + 1)) (μ (j + 1))).Sch) (g : ℂ → ℂ),
    (cfc R _ _ _ _ f₁ : X.AF (X.Xs P.t j)) ∈ π ∧ (cfc R _ _ _ _ f₂ : X.AF (X.Xs P.t j)) ∈ π ∧
    Formalism.MainNotions.SchurIrreducible.RFData (R.rf _ _ _ _) p f₁ f₂ φ₁ φ₂ S (((P.t + 1 : ℕ) : ℂ) / 2) ∧
    LCont (R.rf _ _ _ _) p S (((P.t + 1 : ℕ) : ℂ) / 2) g ∧
    rallisRHS (R.rf _ _ _ _) f₁ f₂ φ₁ φ₂ S (P.t + 1) g ≠ 0 ∧
    ∃ S' : Finset (HeightOneSpectrum (𝓞 D.host.F)), AllSplit D S' ∧
      lift3 R _ _ (μ (j + 1)) (μ (j + 1)) f₂ φ₂ ∈ X.sphOff (X.Xs P.t (j + 1)) S'

def ChainLinkExistence (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  ∀ P : TH.TPar D, Hyp3 X P → ∀ μ : ℕ → X.Chr, IsMu X P μ → IsAuxiliaryHeckeCharacter R P μ → ∀ j, j < D.R.m →
  ∀ π : Submodule ℂ (X.AF (X.Xs P.t j)), IsLink X P j π →
    (∃ (Φ' : X.Sch (X.Xs P.t j) (X.Xs P.t (j + 1))) (φ' : X.cusp (X.Xs P.t j))
      (S' : Finset (HeightOneSpectrum (𝓞 D.host.F))), AllSplit D S' ∧ Φ' ∈ X.fact _ _ ∧ Φ' ∈ X.kfin _ _ ∧
      (φ' : X.AF (X.Xs P.t j)) ∈ π ∧ X.th _ _ (μ (j + 1)) (μ (j + 1)) Φ' φ' ≠ 0 ∧
      X.th _ _ (μ (j + 1)) (μ (j + 1)) Φ' φ' ∈ X.sphOff (X.Xs P.t (j + 1)) S') →
  ∃ π' : Submodule ℂ (X.AF (X.Xs P.t (j + 1))), IsLink X P (j + 1) π' ∧ SumLifts X P μ j π π'

def WittIndexCondition (D : D7) (X : ThetaX D) : Prop :=
  ∀ t j, j ≤ D.R.m → Formalism.MainNotions.SchurIrreducible.wittIdx (X.Xs t j) = 0

def DefiniteChainFromRallis (D : D7) (X : ThetaX D) (R : Loc3 D X) : Prop :=
  PointsLemma D X R → ThetaCuspidalityCondition D X → WittIndexCondition D X → AuxiliaryCharactersExist D X R → ChainPeriodExistence D X R → ChainLinkExistence D X R → DefiniteLiftChain D X



end Part3

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def Conclusion2Family (UF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc2 (Fm.D x i) (Fm.ex x hx i).th) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion2 (Fm.D x i) (Fm.ex x hx i).th (UF x hx i)

def familyNonvanishing : Prop := ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), kernel_index_full_lattice (Fm.D x i) (Fm.ex x hx i).th


end Family

end Formalism.MainNotions.PDVS

end
