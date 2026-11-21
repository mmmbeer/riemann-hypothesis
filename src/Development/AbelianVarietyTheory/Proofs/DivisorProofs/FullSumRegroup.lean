import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MkEqIffRelAndOutRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkIffOfRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementSeparableMinpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorsNonzeroTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic

section
namespace GlobalTheory

theorem finsum_regroup_fibre_bij {α ι : Type} {κ : ι → Type} (U : α → ℂ)
    (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i)
    (hU : (Function.support U).Finite)
    (hval : ∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a)
    (hinj : ∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a')
    (hsurj : ∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) :
    ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  classical
  set S : Finset α := hU.toFinset with hS
  have hmem : ∀ a, a ∈ S ↔ U a ≠ 0 := fun a => by simp [hS]
  have hin : ∀ i, ∑ᶠ c, W i c = ∑ a ∈ S.filter (fun a => π a = i), U a := by
    intro i
    have h1 : Function.support (W i) ⊆
        ((S.filter (fun a => π a = i)).image (Φ i) : Finset (κ i)) := by
      intro c hc
      obtain ⟨a, ha, hUa, hac⟩ := hsurj i c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
      exact ⟨a, ⟨(hmem a).2 hUa, ha⟩, hac⟩
    rw [finsum_eq_sum_of_support_subset _ h1, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      subst ha2
      exact hval a ((hmem a).1 ha1)
    · intro a ha a' ha' h
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 ha'
      subst ha2
      exact hinj a a' ((hmem a).1 ha1) ((hmem a').1 ha1') ha2' h
  simp only [hin]
  have h2 : Function.support (fun i => ∑ a ∈ S.filter (fun a => π a = i), U a) ⊆
      (S.image π : Finset ι) := by
    intro i hi
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha1, ha2⟩
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum U hU,
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha)]

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_finsum_of_fibre_bij : ∀ {α ι : Type} {κ : ι → Type} (U : α → ℂ) (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i), (Function.support U).Finite → (∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a) → (∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a') → (∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) → ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  first | (exact @GlobalTheory.finsum_regroup_fibre_bij) | (exact GlobalTheory.finsum_regroup_fibre_bij) | (intros; apply GlobalTheory.finsum_regroup_fibre_bij  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G), Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  first | (exact @GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (exact GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (intros; apply GlobalTheory.LKCx.Form.mk_eq_iff_rel <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pair_conj_mem_grp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  intro p _ G P B y s hs hc hβ
  refine ⟨?_, hc⟩
  change ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) * B * sh G ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) = algebraMap ℚ G.C (P.c : ℚ) * B
  have hmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← hmul, Units.inv_mul]; simp [sh]
  have hs0 : s ≠ 0 := hs.ne'
  have hβ' : (P.β : G.C) = s • ((y : G.C) * B * sh G y) := by rw [hβ, Algebra.smul_def]
  have hY : (y : G.C) * B * sh G y = s⁻¹ • (P.β : G.C) := by
    rw [hβ', smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hsim : (P.γ : G.C) * P.β * sh G P.γ = (P.c : ℚ) • (P.β : G.C) := by
    rw [P.sim, Algebra.smul_def]
  rw [Units.val_mul, Units.val_mul, hmul, hmul, ← Algebra.smul_def]
  calc ((y⁻¹ : G.Cˣ) : G.C) * P.γ * y * B * (sh G y * (sh G P.γ * sh G ((y⁻¹ : G.Cˣ) : G.C)))
      = ((y⁻¹ : G.Cˣ) : G.C) * (P.γ * ((y : G.C) * B * sh G y) * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
        simp only [mul_assoc]
    _ = s⁻¹ • (((y⁻¹ : G.Cˣ) : G.C) * ((P.γ : G.C) * P.β * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hY]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ)) • (((y⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hsim, mul_smul]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ) * s) • ((((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
        rw [hβ', mul_smul (s⁻¹ * (P.c : ℚ)) s]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = (P.c : ℚ) • (B : G.C) := by
        rw [Units.inv_mul, e, one_mul, mul_one, mul_comm (s⁻¹) _, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

end GlobalTheory
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_by_carrying_unit_mem_positiveSimilitudeFormGroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  first | (exact @GlobalTheory.pair_conj_mem_grp) | (exact GlobalTheory.pair_conj_mem_grp) | (intros; apply GlobalTheory.pair_conj_mem_grp  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.RelConj

theorem rel_of_conj_in_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  intro p _ G P P' B y y' g s s' sg hs hs' hsg hβ hβ' hg hγ
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := fun a b => by simp [sh]
  have hyi : ((y⁻¹ : G.Cˣ) : G.C) * y = 1 := Units.inv_mul y
  have hshy : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← shm, hyi]; simp [sh]
  have key : ((y' * g * y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y' * g * y⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (s * sg) * (y' * B * sh G y') := by
    rw [hβ, Units.val_mul, Units.val_mul, shm, shm, ← Algebra.smul_def]
    calc (y' : G.C) * g * ((y⁻¹ : G.Cˣ) : G.C) * (s • ((y : G.C) * B * sh G y)) *
          (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G g * sh G y'))
        = s • ((y' : G.C) * (g * (((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G g) * sh G y') := by
          simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = s • ((y' : G.C) * ((g : G.C) * B * sh G g) * sh G y') := by
          rw [hyi, hshy, mul_one, mul_one]
      _ = s • (sg • ((y' : G.C) * B * sh G y')) := by
          rw [hg, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      _ = _ := by rw [smul_smul, Algebra.smul_def]
  refine ⟨y' * g * y⁻¹, s' / (s * sg), div_pos hs' (mul_pos hs hsg), ?_, ?_⟩
  · rw [key, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (mul_pos hs hsg).ne', hβ']
  · have e : P'.γ = y' * (y'⁻¹ * P'.γ * y') * y'⁻¹ := by group
    rw [e, ← hγ]; group

end GlobalTheory.RelConj
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_of_conj_in_group_of_common_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' g : G.Cˣ) (s s' sg : ℚ), 0 < s → 0 < s' → 0 < sg → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B → g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' → P.Rel P' := by
  first | (exact @GlobalTheory.RelConj.rel_of_conj_in_form) | (exact GlobalTheory.RelConj.rel_of_conj_in_form) | (intros; apply GlobalTheory.RelConj.rel_of_conj_in_form  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ConjR

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_unit_mul_inv (G : HTGroup p) (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul]; simp [sh]

theorem conj_of_rel (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ)
    (hs : 0 < s) (hs' : 0 < s')
    (hP : (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y))
    (hP' : (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y')) (hR : P.Rel P') :
    ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧
      g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  obtain ⟨z, sr, hsr, hβ, hγ⟩ := hR
  refine ⟨y'⁻¹ * z * y, s' / (s * sr), div_pos hs' (mul_pos hs hsr), ?_, ?_⟩
  · rw [← Algebra.smul_def] at hP hP' hβ ⊢
    set a : G.Cˣ := y'⁻¹
    have E : s' • ((y' : G.C) * B * sh G y') = (sr * s) • ((z : G.C) * (y * B * sh G y) * sh G z) := by
      rw [← hP', hβ, hP, mul_smul, mul_smul_comm, smul_mul_assoc]
    have E2 := congrArg (fun X => (a : G.C) * X * sh G a) E
    have ha1 : (a : G.C) * y' = 1 := Units.inv_mul y'
    have ha2 : sh G (y' : G.C) * sh G a = 1 := sh_unit_mul_inv G y'
    have L : (a : G.C) * (s' • ((y' : G.C) * B * sh G y')) * sh G a = s' • (B : G.C) := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      calc (a : G.C) * ((y' : G.C) * B * sh G y') * sh G a = ((a : G.C) * y') * B * (sh G y' * sh G a) := by
            simp only [mul_assoc]
        _ = _ := by rw [ha1, ha2, one_mul, mul_one]
    have R : (a : G.C) * ((sr * s) • ((z : G.C) * (y * B * sh G y) * sh G z)) * sh G a =
        (sr * s) • (((a * z * y : G.Cˣ) : G.C) * B * sh G ((a * z * y : G.Cˣ) : G.C)) := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      simp only [Units.val_mul, sh_mul', mul_assoc]
    rw [L, R] at E2
    have hne : (sr * s) ≠ 0 := (mul_pos hsr hs).ne'
    rw [show s' / (s * sr) = (sr * s)⁻¹ * s' by rw [div_eq_inv_mul, mul_comm s sr], mul_smul, E2, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  · rw [hγ]; group
end ConjR
end LKCx
end GlobalTheory
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_rel_similitude_pairs_same_form : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ), 0 < s → 0 < s' → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y') → P.Rel P' → ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧ g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  first | (exact @GlobalTheory.LKCx.ConjR.conj_of_rel) | (exact GlobalTheory.LKCx.ConjR.conj_of_rel) | (intros; apply GlobalTheory.LKCx.ConjR.conj_of_rel  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

def formOf {G : HTGroup p} (P : Pair G) : Form G := ⟨P.β, P.sym, P.trivAf, P.trivR⟩

def ofGrp {G : HTGroup p} (F : Form G) (r : grp G F.β)
    (h : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

def phi {G : HTGroup p} (q : FCls G) (Q : Cls G) : ConjClasses (grp G (Quot.out q).β) :=
  if h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β
  then ConjClasses.mk ⟨_, h.choose_spec.2⟩ else ConjClasses.mk 1

theorem phi_spec {G : HTGroup p} (q : FCls G) (Q : Cls G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y))
    (hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β) :
    ∃ y₁ : G.Cˣ, ∃ s₁ : ℚ, 0 < s₁ ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s₁ * (y₁ * (Quot.out q).β * sh G y₁) ∧
      ∃ hm₁ : ((y₁⁻¹ * (Quot.out Q).γ * y₁, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm₁⟩ := by
  have h : ∃ y : G.Cˣ, (∃ s : ℚ, 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y)) ∧
      ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β := ⟨y, ⟨s, hs, hβ⟩, hm⟩
  obtain ⟨⟨s₁, hs₁, hβ₁⟩, hm₁⟩ := h.choose_spec
  exact ⟨h.choose, s₁, hs₁, hβ₁, hm₁, by rw [phi, dif_pos h]⟩

end GlobalTheory.LKCx.Regroup
end
end
