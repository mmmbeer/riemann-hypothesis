import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2OfFiniteDuality
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLatticesStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycleStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsTorRange
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualQOfTopInj
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualDOfDualQ
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsLimitOfCauchyAdicFiltration
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.H2LineOfTateH2AndCoboundaries
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsFinsetSep
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.T2SpaceOfLatticeNhdsBasis
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.MemOfMkMemRange
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FontaineBoundsAllRecords
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.TateFilQuotAllRecords
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Adm8AllRecords
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FundamentalSequenceContinuityAll
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoDimensionRightExact
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoCokernelOfDualityEuler
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotientStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace PositivityTheory.LocalTateOrthogonality.Orth

section Pairing

variable {Qp : Type} [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (R : Type) [CommRing R] [Algebra Qp R]

def pr : V ⊗[Qp] R →ₗ[Qp] V' ⊗[Qp] R →ₗ[Qp] LL ⊗[Qp] R :=
  TensorProduct.map₂ (P.restrictScalars₁₂ Qp Qp) (LinearMap.mul Qp R)

variable {R}

@[simp] theorem pr_tmul (v : V) (r : R) (v' : V') (r' : R) :
    pr P R (v ⊗ₜ[Qp] r) (v' ⊗ₜ[Qp] r') = P v v' ⊗ₜ[Qp] (r * r') := rfl

theorem pr_smul_right (x : V ⊗[Qp] R) (c : LL) (v' : V') (r' : R) :
    pr P R x ((c • v') ⊗ₜ[Qp] r') = c • pr P R x (v' ⊗ₜ[Qp] r') := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v r => rw [pr_tmul, pr_tmul, map_smul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

end Pairing

section Algebra

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}

open GlobalTheory.FundDel

theorem charRep_apply (χ : G →* LLˣ) (g : G) (x : LL) : charRep χ g x = (χ g : LL) * x := rfl

theorem pr_act (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    actVB PD (charRep (cycLL PD LL)) g (pr P B x y) = pr P B (actVB PD ρ g x) (actVB PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      rw [pr_tmul, actVB_tmul', actVB_tmul', actVB_tmul', pr_tmul, hP, map_mul, charRep_apply]

theorem pr_actdR (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) (g : G)
    (x : V ⊗[Qp] BdR) (y : V' ⊗[Qp] BdR) :
    actVdR PD (charRep (cycLL PD LL)) g (pr P BdR x y) =
      pr P BdR (actVdR PD ρ g x) (actVdR PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      rw [pr_tmul, actVdR_tmul', actVdR_tmul', actVdR_tmul', pr_tmul, hP, map_mul, charRep_apply]

theorem pr_φ (x : V ⊗[Qp] B) (v' : V') :
    φVB PD (LL := LL) (V := LL) (pr P B x (v' ⊗ₜ[Qp] 1)) =
      pr P B (φVB PD (LL := LL) (V := V) x) (v' ⊗ₜ[Qp] 1) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r => rw [pr_tmul, φVB_tmul', φVB_tmul', pr_tmul, mul_one, mul_one]

theorem pr_ι (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    ιV PD (LL := LL) (V := LL) (pr P B x y) =
      pr P BdR (ιV PD (LL := LL) (V := V) x) (ιV PD (LL := LL) (V := V') y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' => rw [pr_tmul, ιV_tmul', ιV_tmul', ιV_tmul', pr_tmul, map_mul]

theorem pr_fil (a : ℤ) (y : V ⊗[Qp] BdR) (hy : y ∈ FilV PD (LL := LL) (V := V) a) (v' : V') :
    pr P BdR y (v' ⊗ₜ[Qp] 1) ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [AlgebraTensorModule.map_tmul, pr_tmul, mul_one]
    exact GlobalTheory.CobCrisLift.tmul_mem PD _ b.2
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem hx hy

theorem exists_cochain
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    (hsurj : ∀ (u : LL ⊗[Qp] B) (w : LL ⊗[Qp] BdR), ∃ (x : LL ⊗[Qp] B) (y : LL ⊗[Qp] BdR),
      y ∈ FilV PD (LL := LL) (V := LL) 0 ∧ x - φVB PD (LL := LL) (V := LL) x = u ∧
        ιV PD (LL := LL) (V := LL) x - y = w)
    (hker : ∀ x : LL ⊗[Qp] B, φVB PD (LL := LL) (V := LL) x = x →
      ιV PD (LL := LL) (V := LL) x ∈ FilV PD (LL := LL) (V := LL) 0 → ∃ v : LL, x = v ⊗ₜ[Qp] (1 : B))
    (a : G → V) (x : V ⊗[Qp] B) (hx : ∀ g, a g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
    (h₁ : x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ)
    (d : V ⊗[Qp] BdR) (h₂ : d ∈ DdR PD ρ)
    (hd : ιV PD (LL := LL) (V := V) x - d ∈ FilV PD (LL := LL) (V := V) 0)
    (b : G → V') (hb : ∀ g h, b (g * h) = b g + ρ' g (b h))
    (β : V' ⊗[Qp] B) (hβ : ∀ g, b g ⊗ₜ[Qp] (1 : B) = actVB PD ρ' g β - β) :
    ∃ (f : G → LL) (w : LL ⊗[Qp] B),
      (∀ g, f g ⊗ₜ[Qp] (1 : B) = pr P B x (b g ⊗ₜ[Qp] 1) +
        (actVB PD (charRep (cycLL PD LL)) g w - w)) ∧
      ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f = cupL ρ' P a b := by
  obtain ⟨w, w', hw', hw1, hw2⟩ := hsurj (pr P B (x - φVB PD (LL := LL) (V := V) x) β)
    (pr P BdR d (ιV PD (LL := LL) (V := V') β))
  have key : ∀ g, ∃ v : LL, pr P B x (b g ⊗ₜ[Qp] 1) +
      (actVB PD (charRep (cycLL PD LL)) g (-w) - (-w)) = v ⊗ₜ[Qp] (1 : B) := by
    intro g
    have e₁ : actVB PD ρ g (x - φVB PD (LL := LL) (V := V) x) = x - φVB PD (LL := LL) (V := V) x :=
      sub_eq_zero.1 ((Submodule.mem_iInf _).1 h₁ g)
    have e₂ : actVdR PD ρ g d = d := sub_eq_zero.1 ((Submodule.mem_iInf _).1 h₂ g)
    have f₁ : pr P B (x - φVB PD (LL := LL) (V := V) x) (b g ⊗ₜ[Qp] 1) =
        actVB PD (charRep (cycLL PD LL)) g (w - φVB PD (LL := LL) (V := LL) w) -
          (w - φVB PD (LL := LL) (V := LL) w) := by
      rw [hw1, pr_act PD hP, e₁, hβ, map_sub (pr P B _)]
    have hιb : (b g ⊗ₜ[Qp] (1 : BdR)) = actVdR PD ρ' g (ιV PD (LL := LL) (V := V') β) -
        ιV PD (LL := LL) (V := V') β := by
      rw [← ιV_actVB', ← map_sub, ← hβ, ιV_tmul', map_one]
    have f₂ : pr P BdR d (b g ⊗ₜ[Qp] 1) =
        actVdR PD (charRep (cycLL PD LL)) g (ιV PD (LL := LL) (V := LL) w - w') -
          (ιV PD (LL := LL) (V := LL) w - w') := by
      rw [hw2, pr_actdR PD hP, e₂, hιb, map_sub (pr P BdR _)]
    apply hker
    · rw [map_sub (pr P B), LinearMap.sub_apply, map_sub] at f₁
      rw [map_add, map_sub, pr_φ, φVB_actVB', map_neg, map_neg, map_neg, ← sub_eq_zero, ← neg_eq_zero,
        ← sub_eq_zero.2 f₁]
      abel
    · have : ιV PD (LL := LL) (V := LL) (pr P B x (b g ⊗ₜ[Qp] 1) +
          (actVB PD (charRep (cycLL PD LL)) g (-w) - (-w))) =
          pr P BdR (ιV PD (LL := LL) (V := V) x - d) (b g ⊗ₜ[Qp] 1) -
            (actVdR PD (charRep (cycLL PD LL)) g w' - w') := by
        rw [map_add, map_sub, pr_ι, ιV_tmul', map_one, ιV_actVB', map_sub (pr P BdR),
          LinearMap.sub_apply, f₂, map_sub, map_neg, map_neg]
        abel
      rw [this]
      exact sub_mem (pr_fil PD 0 _ hd _) (sub_mem (actVdR_mem_FilV' PD _ g 0 _ hw') hw')
  choose f hf using key
  refine ⟨f, -w, fun g => (hf g).symm, ?_⟩
  funext ⟨g, h⟩
  apply tmul_one_injective' PD
  change (charRep (cycLL PD LL) g (f h) - f (g * h) + f g) ⊗ₜ[Qp] (1 : B) =
    P (a g) (ρ' g (b h)) ⊗ₜ[Qp] (1 : B)
  have e : charRep (cycLL PD LL) g (f h) ⊗ₜ[Qp] (1 : B) =
      actVB PD (charRep (cycLL PD LL)) g (f h ⊗ₜ[Qp] (1 : B)) := by
    rw [actVB_tmul', map_one]
  have e' : P (a g) (ρ' g (b h)) ⊗ₜ[Qp] (1 : B) =
      pr P B (a g ⊗ₜ[Qp] (1 : B)) (ρ' g (b h) ⊗ₜ[Qp] (1 : B)) := by rw [pr_tmul, mul_one]
  rw [add_tmul, sub_tmul, e, e', hx, ← hf, ← hf, ← hf, map_add, pr_act PD hP, actVB_tmul', map_one, hb,
    add_tmul, map_add, map_sub, actVB_mul', map_sub (pr P B), LinearMap.sub_apply]
  abel

end Algebra

section Top

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem orthL_of
    (hfund : ∀ (LL : Type) [Field LL] [Algebra Qp LL],
      (∀ (u : LL ⊗[Qp] B) (w : LL ⊗[Qp] BdR), ∃ (x : LL ⊗[Qp] B) (y : LL ⊗[Qp] BdR),
      y ∈ FilV PD (LL := LL) (V := LL) 0 ∧ x - φVB PD (LL := LL) (V := LL) x = u ∧
        ιV PD (LL := LL) (V := LL) x - y = w) ∧
      ∀ x : LL ⊗[Qp] B, φVB PD (LL := LL) (V := LL) x = x →
      ιV PD (LL := LL) (V := LL) x ∈ FilV PD (LL := LL) (V := LL) 0 → ∃ v : LL, x = v ⊗ₜ[Qp] (1 : B))
    (hlift : ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ A : GRep G Qp LL O, IsDR PD A.ρ →
      ∀ (c : G → A.V) (x : A.V ⊗[Qp] B), (∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD A.ρ g x - x) →
      x - φVB PD (LL := LL) (V := A.V) x ∈ Dcris PD A.ρ ∧ ∃ d ∈ DdR PD A.ρ,
        ιV PD (LL := LL) (V := A.V) x - d ∈ FilV PD (LL := LL) (V := A.V) 0)
    (hcont : LocalSituation.contCore PD) : GlobalTheory.CompanionTheory.LocDual.OrthL PD := by
  intro LL _ _ _ O _ _ hO A A' P hP hdR a ha b hb
  obtain ⟨-, x, hx⟩ := ha
  obtain ⟨⟨hbc, hb⟩, β, hβ⟩ := hb
  by_cases h0 : ∀ v v', P v v' = 0
  · refine ⟨0, continuous_const, ?_⟩
    rw [map_zero]
    funext z
    exact (h0 _ _).symm
  push Not at h0
  obtain ⟨v₀, v₀', hv⟩ := h0
  have : IsTopologicalRing LL := hO.2.2.2.1
  have hPc : Continuous fun z : A.V × A'.V => P z.1 z.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left P
  have hχ : Continuous fun g => ((cycLL PD LL g : LLˣ) : LL) := by
    have : (fun g => ((cycLL PD LL g : LLˣ) : LL)) =
        fun g => P (A.ρ g v₀) (A'.ρ g v₀') * (P v₀ v₀')⁻¹ := by
      funext g
      rw [hP.1, mul_inv_cancel_right₀ hv]
    rw [this]
    exact (hPc.comp ((A.cont v₀).prodMk (A'.cont v₀'))).mul continuous_const
  let A1 : GRep G Qp LL O :=
    { V := LL
      ρ := charRep (cycLL PD LL)
      cont := fun y => hχ.mul continuous_const }
  obtain ⟨h₁, d, h₂, hd⟩ := hlift LL O hO A hdR a x hx
  obtain ⟨f, w, hf, hdf⟩ := exists_cochain PD hP.1 (hfund LL).1 (hfund LL).2 a x hx h₁ d h₂ hd b hb β hβ
  refine ⟨f, ?_, hdf⟩
  let e := Module.finBasis LL A'.V
  refine hcont LL O hO A1 _ (fun i => pr P B x (e i ⊗ₜ[Qp] 1)) (fun i g => e.coord i (b g))
    (fun i => (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp hbc) w f (fun g => ?_)
  refine (hf g).trans ?_
  congr 1
  conv_lhs => rw [← e.sum_repr (b g), TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_congr rfl fun i _ => pr_smul_right P x _ _ _

end Top

theorem orthL_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) : GlobalTheory.CompanionTheory.LocDual.OrthL (P.PD K) :=
  orthL_of (P.PD K) (fun LL _ _ => GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K LL LL)
    (fun LL _ _ _ O _ _ hO A => GlobalTheory.CobCrisLift.coboundary_lift l P AI T K LL O hO A)
    (GlobalTheory.FundCont.contCore_tied l P AI T K)

theorem tdOrth : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l),
    GlobalTheory.CompanionTheory.LocDual.OrthL ((D.loc l).PD K) :=
  fun D l _ K => orthL_tied l (D.loc l) (D.locA l) (D.locT l) K

end PositivityTheory.LocalTateOrthogonality.Orth
end
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace PositivityTheory.LocalTateOrthogonality.Bk

section Cochains

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  rintro _ ⟨v, rfl⟩
  refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : cob A.ρ v = fun g => A.ρ g v + -v := funext fun g => sub_eq_add_neg _ _
    rw [this]
    exact (A.cont v).add continuous_const
  · change A.ρ (g * h) v - v = A.ρ g v - v + A.ρ g (A.ρ h v - v)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  · change (A.ρ g v - v) ⊗ₜ[Qp] (1 : B) = A.ρ g v ⊗ₜ[Qp] PD.actB g 1 - _
    rw [map_one, sub_tmul]

theorem lc_mk {V X : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V]
    [TopologicalSpace X] {M : Submodule O V} (hM : IsOpen (M : Set V)) {c : X → V}
    (hc : Continuous c) : IsLocallyConstant fun g => (Submodule.Quotient.mk (c g) : V ⧸ M) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : (fun g => (Submodule.Quotient.mk (c g) : V ⧸ M)) ⁻¹' {Submodule.Quotient.mk y} =
      (fun g => c g + -y) ⁻¹' (M : Set V) := by
    ext g
    simp [Submodule.Quotient.eq, sub_eq_add_neg]
  rw [this]
  exact hM.preimage (hc.add continuous_const)

variable {PD}

theorem cobO_of_cobL [ContinuousAdd LL] {L1 : Lattice (O := O) (charRep (cycLL PD LL))}
    (hL1 : IsOpen (L1.T : Set LL)) {z : G × G → LL} (h : CobL PD z) : CobO PD L1 z := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨fun g => Submodule.Quotient.mk (f g), ⟨lc_mk hL1 hf, fun _ => trivial⟩, rfl⟩

variable {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
  {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} {L1 : Lattice (O := O) (charRep (cycLL PD LL))}

omit [TopologicalSpace G] [TopologicalSpace LL] in
theorem mk_liftD {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    Submodule.Quotient.mk (liftD L c) = c := (Submodule.Quotient.mk_surjective L.T c).choose_spec

def pairD (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) (hm : IsDualLat1 PD LA LA' m) :
    ↥LA.T →+ (A'.V ⧸ LA'.T) →ₗ[O] (LL ⧸ L1.T) :=
  AddMonoidHom.mk' (fun t => LA'.T.mapQ L1.T ((m t.1).restrictScalars O) fun y hy => by
      obtain ⟨a, ha⟩ := (hm.2 y).1 hy t.1 t.2
      rw [hL1]
      exact ⟨a, ha.symm⟩)
    fun t t' => by
      apply Submodule.linearMap_qext
      ext y
      simp

theorem mk_cupLD (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hm : IsDualLat1 PD LA LA' m) (d : G → A.V) (hd : ∀ g, d g ∈ LA.T) (c : G → A'.V ⧸ LA'.T)
    (p : G × G) : (Submodule.Quotient.mk (cupLD LA' m d c p) : LL ⧸ L1.T) =
      pairD hL1 hm ⟨d p.1, hd _⟩ (actD LA' p.1 (c p.2)) := by
  conv_rhs => rw [← mk_liftD LA' (c p.2)]
  rfl

theorem cobO_cup_iff (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hm : IsDualLat1 PD LA LA' m) (d : G → A.V) (hd : ∀ g, d g ∈ LA.T) (b : G → A'.V) :
    CobO PD L1 (cupLD LA' m d fun g => Submodule.Quotient.mk (b g)) ↔
      CobO PD L1 (cupL A'.ρ m d b) := by
  unfold CobO
  simp only [mk_cupLD hL1 hm d hd]
  rfl

theorem exists_of_mem_HfD {c : G → A'.V ⧸ LA'.T} (hc : c ∈ HfD PD LA') :
    ∃ b ∈ finiteCocycles PD A'.ρ, c = fun g => Submodule.Quotient.mk (b g) := by
  obtain ⟨_, ⟨b, hb, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨b + cob A'.ρ x, (finiteCocycles PD A'.ρ).add_mem hb (B1_le_Z1f PD A' ⟨x, rfl⟩), rfl⟩

theorem hfD_le (hT : IsOpen (LA'.T : Set A'.V)) : HfD PD LA' ≤ divisibleCocycles LA' := by
  intro c hc
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_HfD hc
  refine ⟨lc_mk hT hb.1.1, fun g h => ?_⟩
  change _ = Submodule.Quotient.mk (b g + A'.ρ g (b h))
  exact congrArg Submodule.Quotient.mk (hb.1.2 g h)

end Cochains

theorem bkA_core (D : D7) (h8 : LocalSituation.adm8 D) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (hL : DualL ((D.loc l).PD K))
    (hEu : ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
      ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL),
        IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P →
        finrank LL (H1V A.ρ) ≤
          finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V)
    (hdim : LocalSituation.bkADim ((D.loc l).PD K)) : bkACore ((D.loc l).PD K) := by
  intro LL _ _ _ O _ _ hO A A' m hdR hm
  have ho := PositivityTheory.LocalTateOrthogonality.Orth.tdOrth D l K LL O hO A A' m hm hdR
  have hdR' := (h8 l K).1 LL O hO A A' m hdR hm
  have e1 := hdim LL O hO A hdR
  have e2 := hdim LL O hO A' hdR'
  have e3 := (h8 l K).2 LL O hO A A' m hdR hm
  have e4 := hEu LL O hO A A' m hm
  have e6 := hm.2.2.2
  unfold IsDR at hdR hdR'
  rw [← e6] at hdR'
  have hc : finrank LL (H1V A.ρ) ≤
      finrank LL (FiniteCohomology ((D.loc l).PD K) A.ρ) + finrank LL (FiniteCohomology ((D.loc l).PD K) A'.ρ) := by
    omega
  obtain ⟨h1, h2⟩ := hL LL O hO A A' m hm (finiteCocycles ((D.loc l).PD K) A.ρ) (finiteCocycles ((D.loc l).PD K) A'.ρ)
    (B1_le_Z1f _ A) (fun _ h => h.1) (B1_le_Z1f _ A') (fun _ h => h.1) ho hc
  exact ⟨fun a ha => ⟨ho a, h1 a ha⟩, fun b hb => ⟨fun h a ha => ho a ha b h, h2 b hb⟩⟩

theorem bkB_core (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (hD : DualD ((D.loc l).PD K))
    (hC : CobLO ((D.loc l).PD K)) (hA : bkACore ((D.loc l).PD K)) : bkBCore ((D.loc l).PD K) := by
  intro LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdR hm
  obtain ⟨hA1, -⟩ := hA LL O hO A A' m hdR hm.1
  have := hO.2.2.2.1
  have hO' : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hO.2.2.2.2
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hTo : IsOpen (LA'.T : Set A'.V) := (GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A' LA' ϖ hϖ).1
  obtain ⟨-, hF⟩ := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' m hm.1
  have h1 : ∀ d ∈ latticeFiniteCocycles ((D.loc l).PD K) LA, ∀ s ∈ HfD ((D.loc l).PD K) LA',
      CobO ((D.loc l).PD K) L1 (cupLD LA' m d s) := fun d hd s hs => by
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_HfD hs
    rw [cobO_cup_iff hL1 hm d fun g => hd.1.2 g trivial]
    exact cobO_of_cobL hO' ((hA1 d hd.1.1).1 hd.2 b hb)
  have h2 : ∀ d ∈ latticeCocycles LA, (∀ s ∈ HfD ((D.loc l).PD K) LA', CobO ((D.loc l).PD K) L1 (cupLD LA' m d s)) →
      d ∈ latticeFiniteCocycles ((D.loc l).PD K) LA := fun d hd H => by
    refine ⟨hd, (hA1 d hd.1).2 fun b hb => ?_⟩
    refine (hC LL O hO L1 hL1 _ (hF d hd.1 b hb.1).1).2 fun u => ?_
    have h3 := (cobO_cup_iff hL1 hm d (fun g => hd.2 g trivial) (u • b)).1
      (H _ (Submodule.mem_sup_left ⟨u • b, (finiteCocycles ((D.loc l).PD K) A'.ρ).smul_mem u hb, rfl⟩))
    convert h3 using 1
    funext p
    simp [cupL]
  refine ⟨fun s hs => ⟨fun h d hd => h1 d hd s h, fun H => ?_⟩,
    fun d hd => ⟨fun h s _ hs => h1 d h s hs, fun H => h2 d hd fun s hs => H s (hfD_le hTo hs) hs⟩⟩
  exact hD LL O hO L1 hL1 A A' LA LA' m hm _ le_sup_right (hfD_le hTo) s hs
    fun d hd H' => H d (h2 d hd H')



theorem local_bounds_give (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK)
    (hA : ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → LocalSituation.adm8 D → ∀ (l : ℕ) [Fact l.Prime]
      (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) → bkACore ((D.loc l).PD K))
    (hB : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) →
      bkBCore ((D.loc l).PD K)) (D : D7) : LocalSituation.Conclusion5 D := by
  intro l _ K
  have h5 := GlobalTheory.T.localSituation_adm5_of_D7 D
  have h6 := GlobalTheory.T.localSituation_adm6_of_D7 D
  have h7 := GlobalTheory.T.localSituation_adm7_of_D7 D
  have h8 := GlobalTheory.T.localSituation_adm8_forall D
  have hd := GlobalTheory.T.blochKato_dimension_rightExact D h5 h6 h7 l K
  have ha := hA D h5 h6 h7 h8 l K hd.1
  have hb := hB D l K ha
  have hc := GlobalTheory.T.blochKato_cokernel_of_duality_euler hT hE D l K ha hb
  exact ⟨ha, hd.1, hd.2, hb, hc⟩


end PositivityTheory.LocalTateOrthogonality.Bk
end
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem card_pow_le {O M Z N : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Finite N] (a : O) (p : Z → M) (hp : Function.Surjective p)
    (f : Z → N) (hf : ∀ x y, f x = f y → ∃ w, p x - p y = a • w) :
    Nat.card (O ⧸ Ideal.span {a}) ^ finrank O M ≤ Nat.card N := by
  classical
  set I : Ideal O := Ideal.span {a}
  let F := M ⧸ Submodule.torsion O M
  let b := Module.finBasis O F
  have e : finrank O F = finrank O M := finrank_quotient_eq_of_le_torsion le_rfl
  let ψL : M →ₗ[O] (Fin (finrank O F) → O) := b.equivFun.toLinearMap ∘ₗ (Submodule.torsion O M).mkQ
  let ψ : M → (Fin (finrank O F) → O ⧸ I) := fun m i => Ideal.Quotient.mk I (ψL m i)
  have hψ : ∀ x y, (∃ w, x - y = a • w) → ψ x = ψ y := by
    rintro x y ⟨w, hw⟩
    funext i
    refine Ideal.Quotient.eq.mpr ?_
    have h1 : ψL x i - ψL y i = a * ψL w i := by
      rw [← Pi.sub_apply, ← map_sub, hw, map_smul]
      rfl
    rw [h1]
    exact Ideal.mem_span_singleton'.mpr ⟨ψL w i, mul_comm _ _⟩
  have hsurj : Function.Surjective (fun z => ψ (p z)) := by
    intro t
    choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I) (t i)
    obtain ⟨m, hm⟩ := (Submodule.torsion O M).mkQ_surjective (b.equivFun.symm c)
    obtain ⟨z, rfl⟩ := hp m
    refine ⟨z, ?_⟩
    funext i
    simp only [ψ, ψL, LinearMap.coe_comp, Function.comp_apply, hm, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, hc]
  let g : Set.range f → (Fin (finrank O F) → O ⧸ I) := fun n => ψ (p (Classical.choose n.2))
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨z, hz⟩ := hsurj t
    refine ⟨⟨f z, z, rfl⟩, ?_⟩
    have hz' : f (Classical.choose (⟨z, rfl⟩ : ∃ y, f y = f z)) = f z := Classical.choose_spec (⟨z, rfl⟩ : ∃ y, f y = f z)
    simp only [g]
    rw [hψ _ _ (hf _ _ hz')]
    exact hz
  have h1 := Nat.card_le_card_of_surjective g hg
  have h2 : Nat.card (Set.range f) ≤ Nat.card N := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [Nat.card_fun, Nat.card_fin, e] at h1
  exact h1.trans h2

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ)

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem redT_mem {ϖ : O} {r : ℕ} (hW : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds (0 : A.V))
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L)) :
    redT L _ c ∈ quotientCocycles L _ hI := by
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hW' : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds ((c : _ → A.V) g0 + -(c : _ → A.V) g0) := by
      rw [add_neg_cancel]
      exact hW
    filter_upwards [(hcont.tendsto g0).add_const (-(c : _ → A.V) g0) hW'] with g hg
    obtain ⟨x, hx, hxe⟩ := hg
    refine (Submodule.Quotient.eq _).mpr ?_
    have : (evT L g c - evT L g0 c : ↥L.T) = ϖ ^ r • (⟨x, hx⟩ : ↥L.T) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, SetLike.val_smul]
      have hxe' : ϖ ^ r • x = (c : _ → A.V) g + -(c : _ → A.V) g0 := hxe
      rw [hxe', sub_eq_add_neg]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · intro g h
    show Submodule.Quotient.mk (evT L (g * h) c) = Submodule.Quotient.mk (evT L g c) + actQ L _ hI g (Submodule.Quotient.mk (evT L h c))
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact hcoc g h

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem exists_div_class [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0)
    (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L))
    (hc : redT L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) c ∈ BQ L _ hI) :
    ∃ w : LatticeCohomology L, (Submodule.Quotient.mk c : LatticeCohomology L) = a • w := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  have hd : ∀ g, ∃ y : ↥L.T, a • y = evT L g c - (actT L g x - x) := by
    intro g
    have h1 := congrFun ht g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1
    change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x = Submodule.Quotient.mk (evT L g c) at h1
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, eq_comm, Submodule.Quotient.eq,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, _, hy⟩ := h1
    exact ⟨y, hy⟩
  choose y hy using hd
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  set α : LL := algebraMap O LL a with hαdef
  have hα : α ≠ 0 := fun h => ha ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  have hyV : ∀ g, a • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    have := congrArg Subtype.val (hy g)
    exact this
  have hyL : ∀ g, α • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    rw [hαdef, algebraMap_smul]
    exact hyV g
  let e : G → A.V := fun g => (y g : A.V)
  have he_form : e = fun g => α⁻¹ • ((c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V)) := by
    funext g
    have h2 : (c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V) = α • e g := by
      rw [hyL g, neg_one_smul]
      abel
    rw [h2, inv_smul_smul₀ hα]
  have he : e ∈ latticeCocycles L := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he_form]
      exact ((hcont.add ((A.cont (x : A.V)).const_smul (-1 : LL))).add continuous_const).const_smul α⁻¹
    · intro g h
      apply smul_right_injective A.V hα
      simp only [smul_add, e, hyL, ← map_smul, hcoc, map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro g _
      exact (y g).2
  refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨x, x.2, ?_⟩
  funext g
  change A.ρ g (x : A.V) - (x : A.V) = (c : G → A.V) g - a • e g
  rw [show a • e g = a • ((y g : ↥L.T) : A.V) from rfl, hyV g, sub_sub_cancel]

end Gen

theorem card_lower_bound : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), TateFiniteness ((D.loc l).PD K) → FinZQ ((D.loc l).PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank O (LatticeCohomology LA)) ≤ Nat.card (QuotientCohomology LA _ hI) := by
  intro D l _ K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI
  obtain ⟨⟨hD, hV, hF⟩, -⟩ := id hO
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have := hfin LL O hO A LA
  have := hZ LL O hO A LA ϖ hϖ r hI
  have : Finite (QuotientCohomology LA _ hI) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]
  refine card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA))
    (Submodule.Quotient.mk_surjective _)
    (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_
  intro x y h
  rw [← Submodule.Quotient.mk_sub]
  refine exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_
  rw [map_sub]
  have h' := (Submodule.Quotient.eq _).1 h
  exact h'

end PositivityTheory.LocalTateOrthogonality.Bk
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem card_H0_twisted_dual (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G] [Group G']
    (φ : G' ≃* G)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] (χ : G →* (ZMod N)ˣ)
    (rho : Representation (ZMod N) G M) (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m)
    (W' : Type) [AddCommGroup W'] [Finite W'] (a' : G' → W' →+ W') (P : M →+ W' →+ ZMod N)
    (hl : ∀ x, (∀ y, P x y = 0) → x = 0) (hr : ∀ y, (∀ x, P x y = 0) → y = 0)
    (he : ∀ g x y, P (a g x) (a' g y) = (χ (φ g) : ZMod N) * P x y) :
    Nat.card (ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))) =
      Nat.card {y : W' // ∀ g, a' g y = y} := by
  let F : W' → ReciprocityTheory.Gal.TDual (ZMod N) M := fun y =>
    ReciprocityTheory.Gal.TDual.mk (AddMonoidHom.toZModLinearMap N (P.flip y))
  have hF : ∀ y x, F y x = P x y := fun _ _ => rfl
  have hinj : Function.Injective F := fun y y' h => by
    refine sub_eq_zero.1 (hr _ fun x => ?_)
    rw [map_sub, ← hF, ← hF, h, sub_self]
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  have hfin : Finite (W' →+ ZMod N) := DFunLike.finite _
  have hM : Nat.card M ≤ Nat.card (W' →+ ZMod N) :=
    Nat.card_le_card_of_injective P ((injective_iff_map_eq_zero P).2 fun x hx =>
      hl x fun y => by rw [hx, AddMonoidHom.zero_apply])
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (hTc.trans (hM.trans (GlobalTheory.natCard_addMonoidHom_zmod_le N W')))
  have hact : ∀ g y, ReciprocityTheory.Gal.twDual χ rho (φ g) (F y) = F (a' g y) := fun g y => by
    refine DFunLike.ext _ _ fun x => ?_
    have h1 : a g (rho (φ g)⁻¹ x) = x := by
      have := ha (φ g) (rho (φ g)⁻¹ x)
      rw [φ.symm_apply_apply] at this
      rw [← this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [ReciprocityTheory.Gal.twDual_apply, hF, hF, ← he, h1]
  symm
  refine Nat.card_congr ((Equiv.ofBijective F hbij).subtypeEquiv fun y => ?_)
  rw [ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
  constructor
  · intro h g
    obtain ⟨g, rfl⟩ := φ.surjective g
    exact (hact g y).trans (congrArg F (h g))
  · intro h g
    exact hinj ((hact g y).symm.trans (h (φ g)))

theorem count_eq (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    Nat.card {c : G' → M // IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} =
      Nat.card (ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))) *
        Nat.card M ^ (d + 1) := by
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := (GlobalTheory.CocycleCount.card_linear_le N M).1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E2 : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have h2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card A :=
    (Nat.card_congr E2).trans (GlobalTheory.ZModDual.card_dual_eq N A)
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : {c : G' → M // IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        (IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun g h => by
          have := c.2.2 (φ g) (φ h)
          rw [ha, φ.symm_apply_apply, ← map_mul] at this
          exact this⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  rw [Nat.card_congr E, hZ', h2]

section Count

variable {G LL O V : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

omit [TopologicalSpace G] in
theorem coc_actQ_mul (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

theorem card_H1Q_mul (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (hlc : ∀ m, IsLocallyConstant fun g => actQ L I hI g m) :
    Nat.card (QuotientCohomology L I hI) * Nat.card (↥L.T ⧸ I) =
      Nat.card ↥(quotientCocycles L I hI) * Nat.card {x : ↥L.T ⧸ I // ∀ g, actQ L I hI g x = x} := by
  let d0 : (↥L.T ⧸ I) →ₗ[O] (G → ↥L.T ⧸ I) := LinearMap.pi fun g => actQ L I hI g - LinearMap.id
  have hd0 : ∀ m g, d0 m g = actQ L I hI g m - m := fun _ _ => rfl
  have hle : BQ L I hI ≤ quotientCocycles L I hI := by
    rintro _ ⟨m, rfl⟩
    refine ⟨(hlc m).comp (fun x => x - m), fun g h => ?_⟩
    change d0 m (g * h) = d0 m g + actQ L I hI g (d0 m h)
    simp only [hd0, coc_actQ_mul, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card ((BQ L I hI).comap (quotientCocycles L I hI).subtype)
  have h2 : Nat.card ((BQ L I hI).comap (quotientCocycles L I hI).subtype) = Nat.card (BQ L I hI) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : Nat.card (LinearMap.ker d0) = Nat.card {x : ↥L.T ⧸ I // ∀ g, actQ L I hI g x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun m => by
      rw [LinearMap.mem_ker, funext_iff]
      simp only [hd0, Pi.zero_apply, sub_eq_zero])
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker d0)
  have h4 : Nat.card ((↥L.T ⧸ I) ⧸ LinearMap.ker d0) = Nat.card (BQ L I hI) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

end Count

theorem cocycles : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (n : ℕ), 0 < n → ∀ (W : Type) [AddCommGroup W] [Finite W] (a : ↥(GK K) → W →+ W), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) → (∀ m : W, l ^ n • m = 0) → ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : ↥(GK K) → W' →+ W'), (∀ m, a' 1 m = m) → (∀ g h m, a' (g * h) m = a' g (a' h m)) → ∀ P : W →+ W' →+ ZMod (l ^ n), (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (a g x) (a' g y) = (Formalism.GaloisCohomology.cycK l K.1 n (K.1.fixingSubgroupEquiv g) : ZMod (l ^ n)) * P x y) → Nat.card {c : ↥(GK K) → W // IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} = Nat.card {y : W' // ∀ g, a' g y = y} * Nat.card W ^ (finrank ℚ_[l] ↥K.1 + 1) := by
  intro hT hE l _ K n hn M _ _ a h1 hmul hlc hr W' _ _ a' _ _ P hl hrt he
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have _ : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ n)) M := AddCommGroup.zmodModule hr
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK n M rho hn hrho
  have hEu := hE l K.1 hK n M rho hn hrho
  rw [count_eq _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl,
    card_H0_twisted_dual _ _ _ φ M _ rho a (fun _ _ => rfl) W' a' P hl hrt he]

theorem h1count : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I), Finite (↥LA.T ⧸ I) → (∀ m, IsLocallyConstant fun g => actQ LA I hI g m) → Nat.card (QuotientCohomology LA I hI) * Nat.card (↥LA.T ⧸ I) = Nat.card ↥(quotientCocycles LA I hI) * Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} :=
  fun _ _ _ _ _ _ _ _ _ _ _ LA I hI _ hlc => card_H1Q_mul LA I hI hlc

end PositivityTheory.LocalTateOrthogonality.Bk
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

set_option maxHeartbeats 2000000 in
theorem pairO : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ r : ℕ, ∃ B : (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) →ₗ[O] (↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ r}), (∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p → B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p) ∧ (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  intro D l _ K LL _ _ _ O _ _ hG A A' LA LA' P hd ϖ hϖ r
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  have hO : IsDomain O := hG0.choose
  have hF : IsFractionRing O LL := hG0.choose_spec.2
  have h1 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, P x y = algebraMap O LL a := hd.2
  have h2 : ∀ x, x ∈ LA.T ↔ ∀ y ∈ LA'.T, ∃ a : O, P.flip y x = algebraMap O LL a :=
    ((GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hd).2
  simp only [LinearMap.flip_apply] at h2
  exact GlobalTheory.CompanionTheory.LocDual.Q.pairing_exists LL O A.V A'.V LA.T LA'.T P ϖ hϖ.ne_zero r h1 h2

theorem cardQ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ r : ℕ, Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) ∧ Nat.card (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r
  obtain ⟨⟨hO, hD, hF⟩, -⟩ := id hG
  have := hO
  have := hD
  have := hF
  have hq := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.1
  refine ⟨(GlobalTheory.CompanionTheory.LocDual.Q.finite_quot O A.V LA.T ϖ r hq LA.fg).2, ?_⟩
  have : Module.Finite O ↥LA.T := Module.Finite.iff_fg.mpr LA.fg
  have := LA.free
  rw [GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_free (Module.finBasis O ↥LA.T).equivFun,
    GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero, GlobalTheory.H1fGeneratorBoundAlt.finrank_lattice LA, pow_mul]

theorem locconst : ∀ (_D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (m : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g => actQ LA _ hI g m := by
  intro D l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r hI m
  exact GlobalTheory.CompanionTheory.LocDual.Q.act_locConst D l K LL O hG A LA ϖ hϖ r hI m

end PositivityTheory.LocalTateOrthogonality.Bk
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk.Eul

theorem chi_tie (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (n : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧
      PadicInt.toZModPow n u = (Formalism.GaloisCohomology.cycK l K.1 n (K.1.fixingSubgroupEquiv g) : ZMod (l ^ n)) := by
  have hcyc : GlobalTheory.Cyc.IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) =
      ((D.loc l).χQ (K.1.fixingSubgroupEquiv.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [GlobalTheory.Cyc.TwistLift.isCyc_unique hcyc (GlobalTheory.Cyc.isCyc_cycChar l)]; rfl
  refine ⟨(χZ (K.1.fixingSubgroupEquiv g) : ℤ_[l]), ?_, rfl⟩
  have h1 := hχZ (K.1.fixingSubgroupEquiv g)
  rw [show K.1.fixingSubgroupEquiv.symm (K.1.fixingSubgroupEquiv g) = g from K.1.fixingSubgroupEquiv.symm_apply_apply g, ← (D.loc l).PD_χ K g] at h1
  exact h1

section Act

variable {G : Type} [Group G] {Qp LL O V : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O]
  [Algebra O LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
  [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (m : ↥L.T ⧸ I) : actQ L I hI 1 m = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 x) = _
  congr 1
  apply Subtype.ext
  change ρ 1 (x : V) = x
  simp

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (g h : G) (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) x) = Submodule.Quotient.mk (actT L g (actT L h x))
  congr 1
  apply Subtype.ext
  change ρ (g * h) (x : V) = ρ g (ρ h x)
  simp [Module.End.mul_apply]

end Act

theorem psi_unit {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (ι : ℤ_[l] →+* O) (J : Ideal O)
    (n : ℕ) (hN : ((l ^ n : ℕ) : O) ∈ J) (ψ : (O ⧸ J) →+ ZMod (l ^ n)) (u : ℤ_[l]) (p : O) :
    ψ (Ideal.Quotient.mk J (ι u * p)) = PadicInt.toZModPow n u * ψ (Ideal.Quotient.mk J p) := by
  have hl : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set m : ℕ := (PadicInt.toZModPow n u : ZMod (l ^ n)).val with hm
  have hmc : ((m : ℕ) : ZMod (l ^ n)) = PadicInt.toZModPow n u := ZMod.natCast_zmod_val _
  have hk : u - (m : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hmc, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hk
  have hu : u = (m : ℤ_[l]) + v * (l : ℤ_[l]) ^ n := by rw [hv]; ring
  have h2 : Ideal.Quotient.mk J (ι u * p) = m • Ideal.Quotient.mk J p := by
    rw [← map_nsmul, Ideal.Quotient.eq]
    have : ι u * p - m • p = (ι v * p) * ((l ^ n : ℕ) : O) := by
      rw [hu]
      simp only [map_add, map_mul, map_pow, map_natCast, nsmul_eq_mul, Nat.cast_pow]
      ring
    rw [this]
    exact J.mul_mem_left _ hN
  rw [h2, map_nsmul, nsmul_eq_mul, hmc]

theorem equivariant_B (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (ι : ℤ_[l] →+* O)
    (hι : ∀ a, algebraMap O LL (ι a) = algebraMap ℚ_[l] LL a) (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hd : IsDualLat1 ((D.loc l).PD K) LA LA' P) (J : Ideal O) (I : Submodule O ↥LA.T)
    (I' : Submodule O ↥LA'.T) (hI : StableSub LA I) (hI' : StableSub LA' I')
    (B : (↥LA.T ⧸ I) →ₗ[O] (↥LA'.T ⧸ I') →ₗ[O] (O ⧸ J))
    (hB : ∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p →
      B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p)
    (g : ↥(GK K)) (x : ↥LA.T ⧸ I) (y : ↥LA'.T ⧸ I') (u : ℤ_[l])
    (hu : (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) :
    B (actQ LA I hI g x) (actQ LA' I' hI' g y) = Ideal.Quotient.mk _ (ι u) * B x y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective I x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I' y
  obtain ⟨p, hp⟩ := (hd.2 y).1 y.2 x x.2
  have h1 : P (actT LA g x) (actT LA' g y) = algebraMap O LL (ι u * p) := by
    change P (A.ρ g x) (A'.ρ g y) = _
    rw [hd.1.1 g x y, hp, map_mul, hι, hu]
    rfl
  rw [hB x y p hp, ← map_mul]
  exact hB _ _ _ h1

theorem exists_pair {O W W' : Type} [CommRing O] [AddCommGroup W] [Module O W] [AddCommGroup W']
    [Module O W'] (J : Ideal O) (N : ℕ) (B : W →ₗ[O] W' →ₗ[O] (O ⧸ J)) (ψ₀ : (O ⧸ J) →+ ZMod N)
    (hψ : ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBr : ∀ y, (∀ x, B x y = 0) → y = 0) :
    ∃ Pb : W →+ W' →+ ZMod N, (∀ x y, Pb x y = ψ₀ (B x y)) ∧ (∀ x, (∀ y, Pb x y = 0) → x = 0) ∧
      ∀ y, (∀ x, Pb x y = 0) → y = 0 := by
  have hsm : ∀ (o : O) (b : O ⧸ J), Ideal.Quotient.mk J o * b = o • b := fun o b => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    rfl
  refine ⟨AddMonoidHom.mk' (fun x => ψ₀.comp (B x).toAddMonoidHom) (fun x y => by
    ext z
    simp), fun _ _ => rfl, fun x hx => hBl x fun y => hψ _ fun o => ?_,
    fun y hy => hBr y fun x => hψ _ fun o => ?_⟩
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← map_smul]
    exact hx _
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← LinearMap.smul_apply, ← map_smul]
    exact hy _

theorem quot_killed {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (J : Ideal O) (N : ℕ)
    (hN : (N : O) ∈ J) (m : M ⧸ (J • ⊤ : Submodule O M)) : N • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul O]
  exact Submodule.smul_mem_smul hN trivial

theorem final_count (h1 w z h0 h0' q a d : ℕ) (hw : 0 < w) (hq : w = q ^ a)
    (hC : h1 * w = z * h0) (hZ : z = h0' * w ^ (d + 1)) : h1 = h0 * h0' * q ^ (a * d) := by
  apply Nat.eq_of_mul_eq_mul_right hw
  rw [hC, hZ, pow_succ, pow_mul, ← hq]
  ring

set_option maxHeartbeats 4000000 in

theorem euler_quot : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V * finrank ℚ_[l] ↥K.1) := by
  intro hT hE D l _ K LL _ _ _ O _ _ hO A A' LA LA' P hd ϖ hϖ r hI hI'
  obtain ⟨-, hqf, -, ⟨-, hl, -⟩, -, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨ι, hι⟩ := GlobalTheory.TateTop.exists_ringHom hO
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := id hO
  have := hdom
  have := hdvr
  have := hfr
  have := hqf
  have hfinO : Finite (O ⧸ Ideal.span {ϖ ^ r}) := by
    have := Ideal.finite_quotient_pow (I := Ideal.span {ϖ}) ⟨{ϖ}, by simp⟩ r
    rwa [Ideal.span_singleton_pow] at this
  have hpos : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hN : ((l ^ (r + 1) : ℕ) : O) ∈ Ideal.span {ϖ ^ r} := by
    have h1 : (l : O) ^ r ∈ Ideal.span {ϖ ^ r} := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_mem_pow hl r
    rw [Nat.cast_pow, pow_succ]
    exact Ideal.mul_mem_right _ _ h1
  obtain ⟨hW, hcW⟩ := cardQ l K LL O hO A LA ϖ hϖ r
  obtain ⟨hW', -⟩ := cardQ l K LL O hO A' LA' ϖ hϖ r
  obtain ⟨ψ₀, hψ, -⟩ := GlobalTheory.T.exists_perfect_character_quotient O ϖ hϖ r (l ^ (r + 1)) hpos hfinO hN
  obtain ⟨B, hB, hBl, hBr⟩ := pairO D l K LL O hO A A' LA LA' P hd ϖ hϖ r
  obtain ⟨Pb, hPb, hL, hR⟩ := exists_pair _ _ B ψ₀ hψ hBl hBr
  have hlc := locconst D l K LL O hO A LA ϖ hϖ r hI
  have heq : ∀ g x y, Pb ((actQ LA _ hI g).toAddMonoidHom x) ((actQ LA' _ hI' g).toAddMonoidHom y) =
      (Formalism.GaloisCohomology.cycK l K.1 (r + 1) (K.1.fixingSubgroupEquiv g) : ZMod (l ^ (r + 1))) * Pb x y := by
    intro g x y
    obtain ⟨u, hu, hu'⟩ := chi_tie D l K (r + 1) g
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B x y)
    have e1 := equivariant_B D l K LL O ι hι A A' LA LA' P hd _ _ _ hI hI' B hB g x y u hu
    rw [← hb, ← map_mul] at e1
    have e3 := psi_unit ι _ (r + 1) hN ψ₀ u b
    rw [hu', hb, ← hPb, ← e1, ← hPb] at e3
    exact e3
  have hZ := cocycles hT hE l K (r + 1) (Nat.succ_pos r) _
    (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI) (fun g h m => actQ_mul' LA _ hI g h m)
    hlc (quot_killed _ _ hN) _
    (fun g => (actQ LA' _ hI' g).toAddMonoidHom) (actQ_one' LA' _ hI') (fun g h m => actQ_mul' LA' _ hI' g h m)
    Pb hL hR heq
  have hC := h1count l K LL O A LA _ hI hW hlc
  exact final_count _ _ _ _ _ _ _ _ Nat.card_pos hcW hC hZ

end PositivityTheory.LocalTateOrthogonality.Bk.Eul
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem le_of_growth {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  have hq0 : 0 < q := by omega
  have h1 := h C
  have h2 : q ^ (C * (b + 1)) ≤ q ^ (C * a) :=
    Nat.pow_le_pow_right hq0 (Nat.mul_le_mul_left _ hba)
  have h3 : q ^ (C * b) * q ^ C ≤ q ^ (C * b) * C := by
    calc q ^ (C * b) * q ^ C = q ^ (C * (b + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add]
      _ ≤ C * q ^ (C * b) := h2.trans h1
      _ = q ^ (C * b) * C := by ring
  have h4 : q ^ C ≤ C := Nat.le_of_mul_le_mul_left h3 (pow_pos hq0 _)
  have h5 : C < q ^ C := Nat.lt_pow_self (by omega)
  omega

theorem growth_le {q a h h' n m C C' : ℕ} (hq : 2 ≤ q)
    (H : ∀ r : ℕ, ∃ x x' y : ℕ, x ≤ C * q ^ (r * h) ∧ x' ≤ C' * q ^ (r * h') ∧ q ^ (r * a) ≤ y ∧
      y = x * x' * q ^ (r * n * m)) : a ≤ h + h' + n * m := by
  refine le_of_growth (C := C * C') hq fun r => ?_
  obtain ⟨x, x', y, hx, hx', hy, e⟩ := H r
  rw [Nat.mul_assoc r] at e
  calc q ^ (r * a) ≤ y := hy
    _ = x * x' * q ^ (r * (n * m)) := e
    _ ≤ (C * q ^ (r * h)) * (C' * q ^ (r * h')) * q ^ (r * (n * m)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hx')
    _ = C * C' * q ^ (r * (h + h' + n * m)) := by
        rw [Nat.mul_add, Nat.mul_add, pow_add, pow_add]; ring

theorem stable_pow {G : Type} [Group G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) :
    StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  have h := Submodule.mem_map_of_mem (f := actT L g) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem euler_le (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (l : ℕ)
    [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O)
    (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hP : IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P) :
    finrank LL (H1V A.ρ) ≤
      finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  have hZ := GlobalTheory.CompanionTheory.FinCoc.finZQ_of_duality hT hE D l K
  obtain ⟨-, hLat⟩ := GlobalTheory.T.exists_dual_lattices D l K
  obtain ⟨LA, LA', hd, -⟩ := hLat LL O hG A A' P hP
  obtain ⟨hfin, hrank⟩ := FinT.h1_lattice_finite_rank_eq D l K hZ
  obtain ⟨-, hr⟩ := hrank LL O hG A LA
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hG
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hres, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ
  have hq : 2 ≤ Nat.card (O ⧸ Ideal.span {ϖ}) := by
    have : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact hϖ.not_isUnit)
    exact Finite.one_lt_card
  obtain ⟨C, h0⟩ := GlobalTheory.CompanionTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt D l K hfin LL O hG A LA ϖ hϖ
  obtain ⟨C', h0'⟩ := GlobalTheory.CompanionTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt D l K hfin LL O hG A' LA' ϖ hϖ
  have h1 := card_lower_bound D l K hfin hZ LL O hG A LA ϖ hϖ
  have hE' := Eul.euler_quot hT hE D l K LL O hG A A' LA LA' P hd ϖ hϖ
  have key : finrank O (LatticeCohomology LA) ≤ finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) +
      finrank LL A.V * finrank ℚ_[l] ↥K.1 :=
    growth_le (C := C) (C' := C') hq fun r =>
      have hI := stable_pow LA ϖ r
      have hI' := stable_pow LA' ϖ r
      ⟨_, _, _, (h0 r hI).2, (h0' r hI').2, h1 r hI, hE' r hI hI'⟩
  rw [hr, Nat.mul_comm (finrank ℚ_[l] ↥K.1)]
  exact key

open ExactAnn in

theorem dualL_of_fin (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (hZ : FinZQ ((D.loc l).PD K))
    (hTop : TopLine ((D.loc l).PD K)) (hNd : NondegL ((D.loc l).PD K)) : DualL ((D.loc l).PD K) := by
  intro LL _ _ _ O _ _ hO A A' P hP S S' hBS hSZ hBS' hSZ' horth hdim
  obtain ⟨-, hF⟩ := GlobalTheory.T.cup_flip_continuous_cocycle D l K LL O hO A A' P hP
  have hnd := hNd LL O hO A A' P hP
  obtain ⟨LA, LA', -⟩ := (GlobalTheory.T.exists_dual_lattices D l K).2 LL O hO A A' P hP
  have hE1 : Module.Finite LL (H1V A.ρ) := ((FinT.h1_lattice_finite_rank_eq D l K hZ).2 LL O hO A LA).1
  have hE2 : Module.Finite LL (H1V A'.ρ) := ((FinT.h1_lattice_finite_rank_eq D l K hZ).2 LL O hO A' LA').1
  by_cases hall : ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, CobL ((D.loc l).PD K) (cupL A'.ρ P a b)
  · exact ⟨fun a ha _ => hBS (hnd.1 a ha fun b hb => hall a ha b hb),
      fun b hb _ => hBS' (hnd.2 b hb fun a ha => hall a ha b hb)⟩
  push Not at hall
  obtain ⟨a0, ha0, b0, hb0, hz0⟩ := hall
  have : IsTopologicalRing LL := hO.2.2.2.1
  obtain ⟨Φ, hΦ⟩ := exists_pairing (continuousCocycles A.ρ) (continuousCocycles A'.ρ) (cocSub ((D.loc l).PD K) LL)
    (cobSub ((D.loc l).PD K) LL) (cupBil A'.ρ P)
    (fun a ha b hb => ⟨(hF a ha b hb).1, (hF a ha b hb).2.1⟩) (cupL A'.ρ P a0 b0) hz0
    (fun z hz => hTop LL O hO _ z (hF a0 ha0 b0 hb0).1 hz.1 (hF a0 ha0 b0 hb0).2.1 hz.2 hz0)
  have res := ann_of_pairing (continuousCocycles A.ρ) (B1 A.ρ) S (continuousCocycles A'.ρ) (B1 A'.ρ) S' Φ
    (fun a ha b => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inl ha)))
    (fun b hb a => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inr hb)))
    (fun a h => hnd.1 a a.2 fun b hb => (hΦ a ⟨b, hb⟩).1 (h _))
    (fun b h => hnd.2 b b.2 fun a ha => (hΦ ⟨a, ha⟩ b).1 (h _))
    hBS hSZ hBS' hSZ'
    (fun a b ha hb => (hΦ a b).2 (horth a ha b hb)) hdim
  exact ⟨fun a ha h => res.1 ⟨a, ha⟩ fun b hb => (hΦ _ _).2 (h b hb),
    fun b hb h => res.2 ⟨b, hb⟩ fun a ha => (hΦ _ _).2 (h a ha)⟩

theorem forms (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (l : ℕ)
    [Fact l.Prime] (K : FinExt l) :
    FinZQ ((D.loc l).PD K) ∧ TopInj ((D.loc l).PD K) ∧ DualQ ((D.loc l).PD K) ∧
      DualD ((D.loc l).PD K) ∧ CobLO ((D.loc l).PD K) ∧ TopLine ((D.loc l).PD K) ∧
      NondegL ((D.loc l).PD K) ∧ DualL ((D.loc l).PD K) := by
  have hFin : FinZQ ((D.loc l).PD K) := GlobalTheory.CompanionTheory.FinCoc.finZQ_of_duality hT hE D l K
  have hTop : TopInj ((D.loc l).PD K) := TI.main hT D l K
  have hQ : DualQ ((D.loc l).PD K) := Q.dualQ_of_topInj hT D l K hTop
  have hD : DualD ((D.loc l).PD K) := GlobalTheory.CompanionTheory.TdDualD.dualD_of_dualQ D l K hFin hQ
  have hCob : CobLO ((D.loc l).PD K) := CobDetect.cobLO_of_fin_inj D l K hFin hTop
  have hH2 : LocalTateTopDegree ((D.loc l).PD K) := GlobalTheory.Cyc.tateH2_of_finite_duality D hT l K
  have hLine : TopLine ((D.loc l).PD K) := Top.h2_line_of_tate_h2_and_coboundaries D l K hH2 hCob
  have hNd : NondegL ((D.loc l).PD K) := Kernels.nondegL D l K hD hCob
  exact ⟨hFin, hTop, hQ, hD, hCob, hLine, hNd, dualL_of_fin D l K hFin hLine hNd⟩

theorem local_bound_a_dim : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D → LocalSituation.adm8 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), LocalSituation.bkADim ((D.loc l).PD K) → bkACore ((D.loc l).PD K) :=
  fun hT hE D _ _ _ h8 l _ K hdim =>
    bkA_core D h8 l K (forms hT hE D l K).2.2.2.2.2.2.2 (euler_le hT hE D l K) hdim

theorem local_bound_b_of_a : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) → bkBCore ((D.loc l).PD K) :=
  fun hT hE D l _ K hA =>
    bkB_core D l K (forms hT hE D l K).2.2.2.1 (forms hT hE D l K).2.2.2.2.1 hA

theorem Conclusion5 : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.Conclusion5 D :=
  fun hT hE => local_bounds_give hT hE (local_bound_a_dim hT hE) (local_bound_b_of_a hT hE)

end PositivityTheory.LocalTateOrthogonality.Bk
end
