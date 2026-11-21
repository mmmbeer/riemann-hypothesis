import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPoints
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Formalism.LocalToGlobal.Columns.ChainOneOk
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemOfHatCosetIndNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSum
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationEqZpow

section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_nat (n : ℕ) : IntAt P (n : E) := by simpa using IntAt.coe P (n : 𝓞 E)

theorem reduction_natCast (n : ℕ) : redP P (n : E) = (n : 𝓞 E ⧸ P.asIdeal) := by
  simpa using reduction_coe P (n : 𝓞 E)

theorem reduction_natCast_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : redP P (q : E) = 0 := by
  rw [reduction_natCast]
  simpa using Ideal.Quotient.eq_zero_iff_mem.2 hq

theorem pow_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (n : ℕ) :
    IntAt P ((q : E) ^ (n + 1)) ∧ redP P ((q : E) ^ (n + 1)) = 0 := by
  induction n with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_nat q, reduction_natCast_eq_zero hq⟩
  | succ n ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_nat q), by rw [reduction_mul ih.1 (intAt_nat q), ih.2, zero_mul]⟩

theorem valuation_one₂ (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) : LocE.vP P q (1 : E) = 0 := by
  have hI : IntAt P (1 : E) := by simpa using intAt_nat (P := P) 1
  have hU : IsUnit (redP P (1 : E)) := by
    have := reduction_natCast (P := P) 1
    rw [Nat.cast_one, Nat.cast_one] at this
    rw [this]; exact isUnit_one
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (q : E) ^ z)) := ⟨0, by rwa [zpow_zero, div_one]⟩
  have hspec : IsUnit (redP P ((1 : E) / (q : E) ^ LocE.vP P q (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨n, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P q (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (q : E) ^ (k' + 1))
    · have e : (1 : E) = (q : E) ^ (k' + 1) * ((1 : E) / (q : E) ^ (k' + 1)) := by field_simp
      have h0 : redP P (1 : E) = 0 := by
        rw [e, reduction_mul (pow_red hq k').1 hI', (pow_red hq k').2, zero_mul]
      rw [h0] at hU
      exact not_isUnit_zero hU
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, reduction_mul hI (pow_red hq k').1, (pow_red hq k').2,
      mul_zero] at hspec
    exact not_isUnit_zero hspec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def trunc : SymData k s κ :=
  { S with
    μ := fun j => if j ≤ s + 2 then S.μ j else 1
    tame := fun j => by
      split_ifs
      · exact S.tame j
      · exact fun _ _ => rfl }

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

def extChars : Chars (extFields X K') (onePrimes X K' π) R.m where
  psi0 := fun w => (φ : X.K →* K').compAddChar (psi0P Ch w.1)
  chi := fun j w => (Units.map (φ : X.K →* K')).comp (chiP Ch w.1 j)
  muVal := 1
  etaVal := 1

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

def extCst (π : 𝓞 X.E) : LocCst (extFields X K') (rowSG (onePrimes X K' π) sel (mu0 X.F X.E K' S₀)) where
  psi := fun _ a => φ (cst.psi P a)
  D := fun _ => 1
  sq := fun _ => z
  muq := fun j _ => φ (cst.muq j P)
  A := cst.A
  B := cst.B
  M := 1
  sharp := true

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
end
end

section
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopHat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_box [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (c : kˣ) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i * (c : k) ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n c) (Submodule.Quotient.mk y₀)) η =
      ((nabs k c ^ Fintype.card n : ℝ) : ℂ) * ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n c) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => cball c).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n c) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => cball c := by
      simp [Submodule.Quotient.eq, mem_box, cball]
    by_cases h : y ∈ Set.pi Set.univ fun _ => cball c
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := by
        refine mul_mem hε (sum_mem fun i _ => ?_)
        have h1 : valuation k (y i) ≤ valuation k (c : k) := h i trivial
        have h2 := (Valuation.mem_integer_iff _ _).1 (hη i)
        rw [Valuation.mem_integer_iff, map_mul]
        rw [map_mul] at h2
        calc valuation k (η i) * valuation k (y i) ≤ valuation k (η i) * valuation k (c : k) := mul_le_mul' le_rfl h1
          _ ≤ 1 := h2
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_cball c).measurableSet), Measure.real,
    Measure.pi_pi]
  simp only [measure_cball ν c, hν.2, mul_one, Finset.prod_const, Finset.card_univ]
  simp [nabs, ENNReal.toReal_pow]

theorem hat_coset_eq_ftY : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν _ hA hD e' e _ he y y' hy'
  haveI := hν.1
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by
    rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  have hcM : ((W.ϖ ^ cst.M : kˣ) : k) = ι ((qOf P.1 : X.E) ^ cst.M) := by
    rw [Units.val_pow_eq_pow_val, hϖ, map_pow]
  rw [hrow, ftY, if_neg hA.nmem]
  by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))
  · rw [if_pos hη, hat_coset_box W.cond hν (neg_mem (one_mem _)) _ _ (fun a => ?_), hdot]
    · have hres : resCard k = qOf P.1 := ComplRes.resCard_eq hA.compl W.unif
      obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif W.unif
      have hnabs : nabs k W.ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
      have hnM : nabs k (W.ϖ ^ cst.M) = ((qOf P.1 : ℝ) ^ cst.M)⁻¹ := by
        rw [show nabs k (W.ϖ ^ cst.M) = nabs k W.ϖ ^ cst.M by simp [nabs], hnabs, hres, inv_pow]
      have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1)) = R.N (s + 1) := by
        simpa using Fintype.card_congr e'
      have hqi : ∀ j, ι ((qOf P.1 : X.E) ^ j) ∈ 𝒪[k] := fun j => by
        rw [map_pow, map_natCast]; exact pow_mem (natCast_mem _ _) _
      have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + 2 * cst.M := ⟨_, (Nat.sub_add_cancel hD).symm⟩
        have : (qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -((qOf P.1 : X.E) ^ d *
              ∑ i, ((qOf P.1 : X.E) ^ cst.M * y' i) * ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))) := by
          rw [hd, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [epsSg, Int.cast_neg, Int.cast_one]
          ring
        rw [this, map_neg, map_mul, map_sum]
        exact neg_mem (mul_mem (hqi _) (sum_mem fun i _ => by
          rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i))))
      have h1 := hA.psi _ hi
      have h2 : ι ((epsSg : X.E) * η' y') = -1 * ι (η' y') := by simp [epsSg]
      rw [map_mul σ₀, ← h1, h2, map_inv₀, map_pow, map_natCast, hnM, hcard]
      push_cast
      rw [inv_pow, ← pow_mul]
    · rw [show (fun a => ι (η' (Pi.single (e' a) 1))) a * ((W.ϖ ^ cst.M : kˣ) : k) =
        ι ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single (e' a) 1)) by rw [hcM, ← map_mul, mul_comm]]
      exact (hint _).2 (hη _)
  · rw [if_neg hη, map_zero]
    by_contra hne
    have hm := mul_mem_of_hat_cosetInd_ne_zero k W.ψ W.cond ν _ (W.ϖ ^ cst.M) (-1) _ _ hne
    refine hη fun i => (hint _).1 ?_
    have h' := neg_mem (hm (e'.symm i))
    convert h' using 1
    rw [map_mul, ← hcM]
    simp only [Equiv.apply_symm_apply]
    ring

end GlobalTheory.TwBridge.TopHat
end
end

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  atlas_forward_decl GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY
end

section
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopPhi

theorem topPhi : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hA hPhi e' e he' he y
  have hm : R.m = s + 2 := hA.steps
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hc : cOf R (s + 1) = 0 := by unfold cOf; omega
  let E1' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (Equiv.sumEmpty _ _).trans (e'.trans (finCongr (by omega)))
  have hbd : ∀ z, (e (Sum.inl z)).val < R.N R.m - 1 + 0 := fun z => by
    have h1 := (e (Sum.inl z)).isLt
    have h2 : e (Sum.inl z) ≠ e (Sum.inr ()) := e.injective.ne (by simp)
    have h3 : (e (Sum.inl z)).val ≠ R.N R.m - 1 := fun h => h2 (Fin.ext (h.trans hlast.symm))
    omega
  let f1 : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) → Fin (R.N R.m - 1 + 0) :=
    fun z => ⟨(e (Sum.inl z)).val, hbd z⟩
  have hf1 : Function.Bijective f1 := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun z z' h => ?_, ?_⟩
    · have h' := Fin.val_eq_of_eq h
      have : e (Sum.inl z) = e (Sum.inl z') := Fin.ext h'
      exact Sum.inl_injective (e.injective this)
    · have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin] at this ⊢
      omega
  let E1 := Equiv.ofBijective f1 hf1
  have hE1' : IsOrdY E1' := by
    rintro (a | a)
    · exact he' a
    · exact a.elim0
  have hE1 : IsOrd zPos E1 := fun z => he (Sum.inl z)
  have hmat : fromCols (toLoc ι e e' y).toRows₁ 0 =
      toLoc ι E1 E1' (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) := by
    ext z c
    rcases c with c | c
    · simp only [fromCols_apply_inl, toRows₁_apply, toLoc, LinearMap.comp_apply, prXp, LinearMap.funLeft_apply]
      have hs : LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))) (Pi.single (E1' (Sum.inl c)) 1) =
          Pi.single (e' c) 1 := by
        funext i
        simp [E1', Pi.single_apply, Fin.ext_iff]
      rw [hs]
      rfl
    · exact c.elim0
  rw [hmat]
  exact hPhi.2 E1' E1 hE1' hE1 _

end GlobalTheory.TwBridge.TopPhi
end
end

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  atlas_forward_decl GlobalTheory.TwBridge.TopPhi.topPhi
end

section
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem val_unif' {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem sqrt_pow (q : ℝ) (hq : 0 < q) (v : ℤ) (N : ℕ) :
    (q ^ (-v)) ^ ((N : ℝ) / 2) = (Real.sqrt q) ^ (-v * N) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

theorem char_scalar (hok : cst.Ok) (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W) (a : X.E) (u : kˣ)
    (hu : (u : k) = ι a) (N : ℕ) :
    ((W.η (s + 1) * W.δ) u : ℂ) * ((nabs k u ^ ((N : ℝ) / 2) : ℝ) : ℂ) =
      W.sg ^ (LocE.vP P.1 (qOf P.1) a * N) *
        σ₀ (muAt Ch sel mu cst s P a * cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) a) * N)) := by
  have hC := hA.compl
  have hU := W.unif
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := ComplRes.q_ne_zero hC
  have hvalu := val_unif' hU
  have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ z)) := by
    obtain ⟨z, hz⟩ := NormalForm.exists_valuation_eq_zpow hvalu u
    refine ⟨z, ?_⟩
    have hv1 : valuation k (ι (a / ((qOf P.1 : ℕ) : X.E) ^ z)) = 1 := by
      rw [map_div₀, map_zpow₀, ← hC.unif, ← hu, map_div₀, map_zpow₀, hz, div_self]
      exact zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 W.ϖ.ne_zero)
    exact (ComplRes.v_eq_one_iff_red hC hU (ComplRes.intAt_of_v hC hv1.le)).1 hv1
  have hspec : IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
    unfold LocE.vP; exact Classical.epsilon_spec hex
  set v := LocE.vP P.1 (qOf P.1) a with hvdef
  set b := a / ((qOf P.1 : ℕ) : X.E) ^ v with hbdef
  have hbI : IntAt P.1 b := by
    by_contra h; rw [reduction_eq_zero_of_not_integral P.1 h] at hspec; exact not_isUnit_zero hspec
  have hbv : valuation k (ι b) = 1 := (ComplRes.v_eq_one_iff_red hC hU hbI).2 hspec
  have hb0 : ι b ≠ 0 := by intro h; rw [h, map_zero] at hbv; exact zero_ne_one hbv
  set ub : kˣ := Units.mk0 (ι b) hb0 with hubdef
  have hu_eq : u = W.ϖ ^ v * ub := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hu, hC.unif, ← map_zpow₀, ← map_mul, hbdef,
      mul_div_left_comm, div_self (zpow_ne_zero v hq0), mul_one]
  have hη : W.η (s + 1) ub = 1 := W.unr (s + 1) ub hbv
  have hδ : (W.δ ub : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := hA.del b ub hbI hspec rfl
  have hμ : ((W.η (s + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (s + 1) P) := hA.mu s (by rw [hA.steps]; omega)
  have hnU : nabs k ub = 1 := nabs_eq_one_of_valuation_eq_one hbv
  obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif hU
  have hnϖ : nabs k W.ϖ = ((qOf P.1 : ℕ) : ℝ)⁻¹ := by
    rw [nabs_uniformiser hp hpϖ.symm, ComplRes.resCard_eq hC hU]
  have hn : nabs k u = ((qOf P.1 : ℕ) : ℝ) ^ (-v) := by
    rw [hu_eq]
    unfold nabs
    rw [map_mul, map_zpow, NNReal.coe_mul, NNReal.coe_zpow]
    have h1 : ((distribHaarChar k W.ϖ : NNReal) : ℝ) = ((qOf P.1 : ℕ) : ℝ)⁻¹ := hnϖ
    have h2 : ((distribHaarChar k ub : NNReal) : ℝ) = 1 := hnU
    rw [h1, h2, mul_one, _root_.inv_zpow']
  have hsg : W.sg ≠ 0 := by
    intro h0
    have h2 := congrArg σ₀ (hok.sq_sq P)
    rw [map_pow, hA.sq, h0, zero_mul, map_natCast] at h2
    exact hq0 (by exact_mod_cast (zero_pow two_ne_zero).symm.trans h2 |>.symm)
  have hmuAt : muAt Ch sel mu cst s P a = cst.muq (s + 1) P ^ v * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b)⁻¹ := by
    unfold muAt LocE.locChar
    rw [if_neg hA.nmem, ← hvdef, ← hbdef]
    congr 1
    unfold LocE.unitV
    rw [dif_pos hspec, dif_pos hspec, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hchar : ((W.η (s + 1) * W.δ) u : ℂ) = σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := by
    rw [hu_eq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hμ, MonoidHom.mul_apply, Units.val_mul, hη,
      Units.val_one, one_mul, hδ]
  have hq : (0 : ℝ) < ((qOf P.1 : ℕ) : ℝ) := by
    have : (qOf P.1 : ℕ) ≠ 0 := fun h => hq0 (by rw [h, Nat.cast_zero])
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [hchar, hn, sqrt_pow _ hq, hmuAt, map_mul, map_mul, map_zpow₀, map_inv₀, map_zpow₀, hA.sq, mul_zpow]
  push_cast
  have hs1 : W.sg ^ (v * N) * W.sg ^ (-v * N) = 1 := by
    rw [neg_mul, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hsg)]
  linear_combination (σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ *
    (Real.sqrt ((qOf P.1 : ℕ) : ℝ) : ℂ) ^ (-v * N)) * (-hs1)

end GlobalTheory.TwBridge.PsiRat

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

theorem toLoc_comp_rect {E k : Type} [Field E] [Field k] (ι : E →+* k) {A B C : Type} [Fintype B] [DecidableEq B]
    {a b c : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) (eC : C ≃ Fin c) (x : (Fin b → E) →ₗ[E] (Fin a → E))
    (y : (Fin c → E) →ₗ[E] (Fin b → E)) :
    toLoc ι eA eB x * toLoc ι eB eC y = toLoc ι eA eC (x ∘ₗ y) := by
  have h : ∀ {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (z : (Fin b → E) →ₗ[E] (Fin a → E)),
      toLoc ι e e' z = ((LinearMap.toMatrix' z).submatrix e e').map ι := by
    intro A B a b e e' z
    ext i j
    simp [toLoc, LinearMap.toMatrix'_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rw [h, h, h, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ eA eB eC, Matrix.map_mul]

theorem muAt_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
    (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) :
    muAt Ch sel mu cst i P 1 = 1 := by
  unfold muAt LocE.locChar
  rw [PsiStep.valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by rw [PsiStep.reduction_one']; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos h1]
  have : h1.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, PsiStep.reduction_one', Units.val_one])
  rw [this, map_one, Units.val_one]

end GlobalTheory.TwBridge.PsiRat

namespace GlobalTheory.TwBridge

open PsiRat in

theorem psi_rat_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (γ : AutY X R s) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k), IsGL ι γ g →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
      (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
        sgn sel mu P W γ (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P γ x₀ y') := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hok hA hPhi γ g hg e' e he' he x₀ y'
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  obtain ⟨eg, hegO, hgv⟩ := hg
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hegE : eg = E' := Equiv.ext fun a => Fin.ext ((hegO a).trans (hE' a).symm)
  subst hegE
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') :=
    PsiStep.withCol_toLoc ι e e' hc1 hc0 x₀ y'
  have hprod : toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') * toLoc ι E' E' γ.toLinearMap =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) :=
    toLoc_comp_rect ι E₁ E' E' _ _
  have hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι ((LinearEquiv.det γ : X.Eˣ) : X.E) := by
    have h := RingHom.map_det ι ((LinearMap.toMatrix' γ.toLinearMap).submatrix E' E')
    rw [RingHom.mapMatrix_apply] at h
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, toLoc_eq_map_toMatrix', ← h,
      Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0) = R.N (s + 1) + cOf R (s + 1) := by
    rw [Fintype.card_congr E₁, Fintype.card_fin]
  have hPhi1 := hPhi.1 s 0 rfl E' E₁ hegO hE₁ (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)
  have hsc := char_scalar Ch sel mu cst σ₀ P ι s W hok hA _ _ hdet (R.N (s + 1) + cOf R (s + 1))
  have hL : (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      ((W.η (s + 1) * W.δ) (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((R.N (s + 1) + cOf R (s + 1) : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        σ₀ (PhiAt Ch mu cst.sharp s P.1 (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)) := by
    rw [← hPhi1, ← hprod, ← hgv, ← hmat, ← hcard]
    clear hsc hPhi1 hdet hprod hmat hE₁ hE' hegO hPhi hA hok hgv hcard he he'
    unfold Chain.Psi GlobalTheory.SplitWeil.om
    have hn1 : nabs k (1 : kˣ) = 1 := by unfold nabs; rw [map_one, NNReal.coe_one]
    simp only [map_one, inv_one, Units.val_one, hn1, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul]
    rfl
  rw [hL, hsc]
  unfold PsiAt omPhi Loc.om sgn
  simp only [map_one, Units.val_one, PsiStep.valuation_one₂, muAt_one, inv_one, mul_one, zero_mul, zpow_zero]
  have h1 : (LinearEquiv.symm (1 : AutY X R (s + 1))).toLinearMap ∘ₗ
      (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) =
        joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap := by
    ext v; rfl
  rw [h1]
  simp only [map_mul]
  ring

end GlobalTheory.TwBridge
end
end
end

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (γ : AutY X R s) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k), IsGL ι γ g →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
      (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
        sgn sel mu P W γ (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P γ x₀ y') := by
  atlas_forward_decl GlobalTheory.TwBridge.psi_rat_agree
end

section
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

namespace GlobalTheory.DenseBox

theorem isOpen_box_set {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A : Type) [Fintype A] (c : kˣ) : IsOpen ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
  have e : ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) =
      ⋂ i : A, (fun y : A → k => y i) ⁻¹' cball c := by
    ext y; simp [GlobalTheory.StepData.mem_box, cball]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_cball c).preimage (continuous_apply i)

theorem support_invariance_of_dense : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  intro k _ _ _ _ E _ ι hι A B _ _ f hf c hsupp hinv x y
  have hv : DenseRange (fun y : A → E => fun a => ι (y a)) := DenseRange.piMap (fun _ => hι)
  have hM : DenseRange (fun x : Matrix A B E => x.map ι) := by
    have : DenseRange (fun x : A → B → E => fun a b => ι (x a b)) :=
      DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
    exact this
  have hF : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x y} := hf.isOpen_fiber _
  refine ⟨fun hne => ?_, fun z hz => ?_⟩
  ·
    let U : Set (Matrix A B k × (A → k)) :=
      {p | f p.1 p.2 = f x y} ∩ {p | p.2 - y ∈ (GlobalTheory.StepData.box A c⁻¹ : Set (A → k))}
    have hU : IsOpen U := hF.inter ((isOpen_box_set A c⁻¹).preimage (continuous_snd.sub continuous_const))
    have hxy : (x, y) ∈ U := ⟨rfl, by simp⟩
    obtain ⟨⟨x0, y0⟩, hp⟩ := (hM.prodMap hv).exists_mem_open hU ⟨_, hxy⟩
    obtain ⟨h1, h2⟩ := hp
    have hne' : f (x0.map ι) (fun a => ι (y0 a)) ≠ 0 := by
      simp only [Set.mem_setOf_eq, Prod.map] at h1; rw [h1]; exact hne
    have hy0 := hsupp x0 y0 hne'
    have h2' : (fun a => ι (y0 a)) - y ∈ GlobalTheory.StepData.box A c⁻¹ := h2
    have := Submodule.sub_mem _ hy0 h2'
    simpa using this
  ·
    have hG : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x (y + z)} := hf.isOpen_fiber _
    let V : Set (Matrix A B k × (A → k) × (A → k)) :=
      {q | f q.1 q.2.1 = f x y} ∩ {q | f q.1 (q.2.1 + q.2.2) = f x (y + z)} ∩
        {q | q.2.2 ∈ (GlobalTheory.StepData.box A c : Set (A → k))}
    have hV : IsOpen V := by
      refine (IsOpen.inter ?_ ?_).inter ((isOpen_box_set A c).preimage (continuous_snd.comp continuous_snd))
      · exact hF.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      · exact hG.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).add
          (continuous_snd.comp continuous_snd)))
    have hxyz : (x, y, z) ∈ V := ⟨⟨rfl, rfl⟩, hz⟩
    obtain ⟨⟨x0, y0, z0⟩, hp⟩ := (hM.prodMap (hv.prodMap hv)).exists_mem_open hV ⟨_, hxyz⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [Set.mem_setOf_eq, Prod.map] at h1 h2 h3
    have e := hinv x0 y0 z0 h3
    have e' : (fun a => ι (y0 a + z0 a)) = (fun a => ι (y0 a)) + (fun a => ι (z0 a)) := by
      funext a; simp
    rw [e'] at e
    rw [← h2, e, h1]

end GlobalTheory.DenseBox
end

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  atlas_forward_decl GlobalTheory.DenseBox.support_invariance_of_dense
end

section
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.TwLast

theorem toLoc_of_mat {E k A B : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : E →+* k) {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : Matrix A B E) :
    x.map ι = toLoc ι e e' (Matrix.toLin' (Matrix.of fun i j => x (e.symm i) (e'.symm j))) := by
  ext i j
  simp [toLoc, Matrix.toLin'_apply, Matrix.mulVec_single]

theorem psi_isLocallyConstant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (R : Ranks) (W : TwData k) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k) :
    IsLocallyConstant (fun p : Matrix (XIx (Fin R.k) (Fin R.t) (s + 1)) (XIx (Fin R.k) (Fin R.t) s) k × (XIx (Fin R.k) (Fin R.t) (s + 1) → k) =>
      (W.T s R).Psi g p.1 p.2) := by
  have hΦ : (W.T s R).Phi s 0 rfl ∈ SB _ := (Chain.ofTwist_regular _ _ _ _ _).1 s 0 rfl
  unfold Chain.Psi om
  refine (IsLocallyConstant.const _).mul (hΦ.1.comp_continuous ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_pi fun r => continuous_pi fun c => ?_
  rcases r with r | r <;> rcases c with c | c
  · exact (continuous_apply c).comp ((continuous_apply r).comp continuous_fst)
  · exact (continuous_apply r).comp continuous_snd
  · exact r.elim0
  · exact r.elim0

theorem lastAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL
  have hPhi := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  have hnm : P.1 ∉ Pr.vGs := hA.nmem
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  refine ⟨fun al g hg => ⟨fun x₀ y => ?_, fun e' e he' he x₀ y' =>
    GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg e' e he' he x₀ y'⟩, ?_⟩
  · have hrat := GlobalTheory.T.penultimateStepPsi_rationalRep_eq_columnsDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hc hA hPhi _ g hg
      (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.MatchCompare.isOrd_ordX R s) (GlobalTheory.MatchCompare.isOrd_ordX R (s + 1))
    refine GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational k X.E ι hA.compl.dense _ _ ((W.T s R).Psi g) (psi_isLocallyConstant s R W g) (W.ϖ ^ cst.M) ?_ ?_ x₀ y
    · intro x y hne
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x] at hne
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))] at hne
      have hs := hL.psiSupp al P _ _ (fun h => (right_ne_zero_of_mul hne) (by rw [h, map_zero]))
      rw [if_neg hnm] at hs
      rw [mem_box]
      intro a
      have h1 := hs ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)
      simp only [Equiv.symm_apply_apply] at h1
      have h' := (hint _).2 h1
      rw [map_mul, map_pow, ← hϖ] at h'
      have hϖ0 : ((W.ϖ : k) ^ cst.M) ≠ 0 := pow_ne_zero _ W.ϖ.ne_zero
      calc valuation k (ι (y a)) = valuation k (((W.ϖ : k) ^ cst.M)⁻¹ * ((W.ϖ : k) ^ cst.M * ι (y a))) := by
            rw [inv_mul_cancel_left₀ hϖ0]
        _ = valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * valuation k ((W.ϖ : k) ^ cst.M * ι (y a)) := map_mul _ _ _
        _ ≤ valuation k (((W.ϖ : k) ^ cst.M)⁻¹) * 1 := by gcongr; exact (Valuation.mem_integer_iff _ _).1 h'
        _ = valuation k (((W.ϖ ^ cst.M)⁻¹ : kˣ) : k) := by simp
    · intro x y z hz
      rw [toLoc_of_mat ι (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) (GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R s) x]
      have hy : (fun a => ι (y a)) = fun a => ι ((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      have hyz : (fun a => ι (y a + z a)) = fun a => ι (((fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)) +
          (fun i => z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i))) ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)) a)) := by
        simp
      rw [hy, hyz, hrat, hrat _ (fun i => y ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)), hL.psiInv al P _ _ _ ?_]
      rw [if_neg hnm]
      intro i
      apply (hint _).1
      rw [mem_box] at hz
      have h1 := hz ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)
      rw [map_mul, map_inv₀, map_pow, ← hϖ, Valuation.mem_integer_iff, map_mul, map_inv₀]
      have hv0 : valuation k ((W.ϖ : k) ^ cst.M) ≠ 0 := by simp
      calc (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k (ι (z ((GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix.ordX R (s + 1)).symm i)))
          ≤ (valuation k ((W.ϖ : k) ^ cst.M))⁻¹ * valuation k ((W.ϖ : k) ^ cst.M) :=
            by gcongr; simpa using h1
        _ = 1 := inv_mul_cancel₀ hv0
  · intro e' e he' he y y' hy'
    simp only [Chain.xiTop]
    rw [GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hA hPhi e' e he' he y,
      GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA (hL.depthQ P hnm) e' e he' he y y' hy', map_mul]

end GlobalTheory.TwLast
end
end

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  atlas_forward_decl GlobalTheory.TwLast.lastAgree
end
