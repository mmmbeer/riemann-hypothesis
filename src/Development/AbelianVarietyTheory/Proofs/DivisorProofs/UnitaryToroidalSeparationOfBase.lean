import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatio
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAway
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme

section
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_smooth_subalgebra_of_finset : ∀ (F K : Type) [Field F] [CharZero F] [Field K]
    [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧
      Algebra.Smooth F R := by
  intro F K _ _ _ _ s
  haveI : PerfectField F := PerfectField.ofCharZero
  let C : Subalgebra F K := Algebra.adjoin F (↑s : Set K)
  haveI : Algebra.FiniteType F C :=
    ⟨(Subalgebra.fg_top C).mpr (Subalgebra.fg_adjoin_finset s)⟩
  obtain ⟨f, hf0, hsm, -⟩ := GlobalTheory.SS.exists_smooth_free_away F C C
  have hinjC : Function.Injective (algebraMap C K) := Subtype.val_injective
  have hfK : IsUnit (algebraMap C K f) := by
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    exact hf0 (hinjC (by simpa using h))
  let g : Localization.Away f →ₐ[F] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => by
        show IsLocalization.Away.lift f hfK (algebraMap F (Localization.Away f) r) = algebraMap F K r
        rw [IsScalarTower.algebraMap_apply F C (Localization.Away f),
          IsLocalization.Away.lift_eq]
        rfl }
  have hginj : Function.Injective g := by
    show Function.Injective (IsLocalization.Away.lift f hfK)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0) h]
    · intro h
      have : x = y := hinjC h
      rw [this]
  refine ⟨g.range, ?_, ?_⟩
  · intro x hx
    refine ⟨algebraMap C (Localization.Away f) ⟨x, Algebra.subset_adjoin hx⟩, ?_⟩
    show IsLocalization.Away.lift f hfK _ = x
    rw [IsLocalization.Away.lift_eq]
    rfl
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective g hginj)
end GlobalTheory
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  atlas_forward_decl GlobalTheory.exists_smooth_subalgebra_of_finset
end

section
section
open scoped TensorProduct

namespace GlobalTheory

namespace LocalizationIntegrallyClosedDomain

variable {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]

lemma algebraMap_eq_zero_of_sub (C : Subring B) (c : C)
    (h : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) c = 0) :
    algebraMap B (Localization.AtPrime Q) (c : B) = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl] at h
  obtain ⟨⟨m, hm⟩, hmc⟩ := h
  rw [IsLocalization.map_eq_zero_iff Q.primeCompl]
  refine ⟨⟨(m : B), by exact hm⟩, ?_⟩
  simpa using congrArg Subtype.val hmc

lemma algebraMap_eq_zero_of_witness (C : Subring B) (u e : C) (hu : (u : B) ∉ Q)
    (h : u * e = 0) :
    algebraMap C (Localization.AtPrime (Q.comap C.subtype)) e = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl]
  exact ⟨⟨u, by exact hu⟩, h⟩

variable {Q}

lemma noZeroDivisors
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q)) :
    NoZeroDivisors (Localization.AtPrime Q) := by
  classical
  refine ⟨fun {x y} hxy => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hxy
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨C, hC, hCq⟩ := H {a, c, (u : B)}
  have ha : a ∈ C := hC (by simp)
  have hc : c ∈ C := hC (by simp)
  have hu' : (u : B) ∈ C := hC (by simp)
  haveI := (hCq (Q.comap C.subtype)).1
  have h0 : algebraMap C (Localization.AtPrime (Q.comap C.subtype))
      ((⟨a, ha⟩ : C) * ⟨c, hc⟩) = 0 :=
    algebraMap_eq_zero_of_witness Q C ⟨u, hu'⟩ _ u.2 (Subtype.ext (by simpa using hu))
  rw [map_mul] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · left
    have h1 := algebraMap_eq_zero_of_sub Q C _ h
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h1
  · right
    have h1 := algebraMap_eq_zero_of_sub Q C _ h
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl] at h1
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h1

end LocalizationIntegrallyClosedDomain

end GlobalTheory

namespace GlobalTheory

namespace LocalizationIntegrallyClosedDomain

variable {B : Type} [CommRing B] {Q : Ideal B} [Q.IsPrime]

set_option maxHeartbeats 1600000 in

lemma isIntegrallyClosed
    (H : ∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
      ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧
        IsIntegrallyClosed (Localization.AtPrime q))
    [IsDomain (Localization.AtPrime Q)] :
    IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro z hz
  have hf : ∀ x ∈ Q.primeCompl, algebraMap B (FractionRing (Localization.AtPrime Q)) x ≠ 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))]
    exact ((IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hx⟩ : Q.primeCompl)).map (algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).ne_zero
  have key : ∀ (b : B) (v : Q.primeCompl),
      algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) b v) * algebraMap B (FractionRing (Localization.AtPrime Q)) v = algebraMap B (FractionRing (Localization.AtPrime Q)) b := by
    intro b v
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) v, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) b, ← map_mul,
      IsLocalization.mk'_spec]

  obtain ⟨D, A0, hD, hDz⟩ : ∃ D A0 : B, algebraMap B (FractionRing (Localization.AtPrime Q)) D ≠ 0 ∧
      algebraMap B (FractionRing (Localization.AtPrime Q)) D * z = algebraMap B (FractionRing (Localization.AtPrime Q)) A0 := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := (Localization.AtPrime Q)) z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    have hyK : algebraMap (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) c t) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hcK : algebraMap B (FractionRing (Localization.AtPrime Q)) c ≠ 0 := by
      intro h0
      apply hyK
      have h1 := key c t
      rw [h0] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hf _ t.2)
    refine ⟨c * s, a * t, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hcK (hf _ s.2)
    · have k1 := key a s
      have k2 := key c t
      rw [map_mul, map_mul, ← k1, ← k2]
      field_simp
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
  obtain ⟨p, hpm, hp⟩ := hm
  set A : B := (m : B) * A0 with hA
  have hDA : algebraMap B (FractionRing (Localization.AtPrime Q)) D * (m • z) = algebraMap B (FractionRing (Localization.AtPrime Q)) A := by
    rw [Submonoid.smul_def, Algebra.smul_def, hA, map_mul, ← hDz]; ring
  have hE : algebraMap B (Localization.AtPrime Q) (p.scaleRoots D |>.eval A) = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap B (FractionRing (Localization.AtPrime Q))) (m • z) D
    rw [hp, mul_zero, hDA, Polynomial.eval₂_at_apply, IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q))] at h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)))).mp h1
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).mp hE
  obtain ⟨C, hC, hCq⟩ := H (insert A (insert D (insert (u : B) p.coeffs)))
  have hAC : A ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hDC : D ∈ C := hC (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have huC : (u : B) ∈ C := hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  have hcoef : (↑p.coeffs : Set B) ⊆ (C : Set B) := fun x hx => hC (Finset.mem_coe.mpr
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
  set p' := p.toSubring C hcoef with hp'
  have hp'm : p'.Monic := (Polynomial.monic_toSubring p C hcoef).mpr hpm
  set A' : C := ⟨A, hAC⟩
  set D' : C := ⟨D, hDC⟩
  set u' : C := ⟨u, huC⟩
  haveI : Nontrivial B := (algebraMap B (Localization.AtPrime Q)).domain_nontrivial
  have hlc : C.subtype p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hsub : C.subtype ((p'.scaleRoots D').eval A') = (p.scaleRoots D).eval A := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ hlc,
      Polynomial.map_toSubring]
    rfl
  have hE' : u' * (p'.scaleRoots D').eval A' = 0 := by
    apply Subtype.ext
    have : (u : B) * C.subtype ((p'.scaleRoots D').eval A') = 0 := by rw [hsub]; exact hu
    simpa using this
  haveI := (hCq (Q.comap C.subtype)).1
  haveI := (hCq (Q.comap C.subtype)).2
  have hgE : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) ((p'.scaleRoots D').eval A') = 0 :=
    algebraMap_eq_zero_of_witness Q C u' _ u.2 hE'
  have hgD : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' ≠ 0 := by
    intro h0
    have h1 : algebraMap B (Localization.AtPrime Q) D = 0 := algebraMap_eq_zero_of_sub Q C D' h0
    apply hD
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (FractionRing (Localization.AtPrime Q)), h1, map_zero]
  have hhD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))))).mpr hgD
  set x : (FractionRing (Localization.AtPrime (Q.comap C.subtype))) := algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') / algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') with hx
  have hxD : algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D') * x = algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype))) (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A') := by
    rw [hx]; field_simp
  have hlc2 : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) p'.leadingCoeff ≠ 0 := by
    rw [hp'm.leadingCoeff, map_one]; exact one_ne_zero
  have hxint : IsIntegral (Localization.AtPrime (Q.comap C.subtype)) x := by
    refine ⟨p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype))), hp'm.map _, ?_⟩
    have h2 := Polynomial.scaleRoots_eval₂_mul (p := p'.map (algebraMap C (Localization.AtPrime (Q.comap C.subtype)))) (algebraMap (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))) x
      (algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D')
    rw [hxD, ← Polynomial.map_scaleRoots _ _ _ hlc2, Polynomial.eval₂_at_apply, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hgE, map_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hhD)
  obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Localization.AtPrime (Q.comap C.subtype)) (K := FractionRing (Localization.AtPrime (Q.comap C.subtype)))).mp hxint
  have hwD : w * algebraMap C (Localization.AtPrime (Q.comap C.subtype)) D' = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) A' := by
    apply IsFractionRing.injective (Localization.AtPrime (Q.comap C.subtype)) (FractionRing (Localization.AtPrime (Q.comap C.subtype)))
    rw [map_mul, hw, mul_comm, hxD]
  obtain ⟨⟨e, v⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap C.subtype).primeCompl w
  have hev : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (e * D') = algebraMap C (Localization.AtPrime (Q.comap C.subtype)) (A' * v) := by
    rw [map_mul, map_mul, ← hwD, ← IsLocalization.mk'_spec (Localization.AtPrime (Q.comap C.subtype)) e v]; ring
  obtain ⟨n, hn⟩ := (IsLocalization.eq_iff_exists (Q.comap C.subtype).primeCompl (Localization.AtPrime (Q.comap C.subtype))).mp hev
  have hnB : ((n : C) : B) * ((e : B) * D) = ((n : C) : B) * (A * ((v : C) : B)) := by
    simpa using congrArg Subtype.val hn
  have hK := congrArg (algebraMap B (FractionRing (Localization.AtPrime Q))) hnB
  simp only [map_mul, hA] at hK
  have hfn : algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) ≠ 0 := hf _ (by exact n.2)
  have hfv : algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B) ≠ 0 := hf _ (by exact v.2)
  have hfm : algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) ≠ 0 := hf _ m.2
  let v'' : Q.primeCompl := ⟨((v : C) : B), by exact v.2⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime Q) (e : B) (m * v''), ?_⟩
  have key2 := key (e : B) (m * v'')
  simp only [Submonoid.coe_mul, map_mul] at key2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hfn hD) (mul_ne_zero hfm hfv))
  linear_combination (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) D) * key2
    - (algebraMap B (FractionRing (Localization.AtPrime Q)) ((n : C) : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) (m : B) * algebraMap B (FractionRing (Localization.AtPrime Q)) ((v : C) : B)) * hDz + hK

end LocalizationIntegrallyClosedDomain

theorem localization_isDomain_isIntegrallyClosed_of_finset_subring :
    ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro B _ Q _ H
  haveI : NoZeroDivisors (Localization.AtPrime Q) := LocalizationIntegrallyClosedDomain.noZeroDivisors H
  haveI : IsDomain (Localization.AtPrime Q) := NoZeroDivisors.to_isDomain _
  exact ⟨inferInstance, LocalizationIntegrallyClosedDomain.isIntegrallyClosed H⟩

end GlobalTheory
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  atlas_forward_decl GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring
end

section
section
open scoped TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv {D C : Type*} [CommRing D]
    [CommRing C] (e : D ≃+* C)
    (h : ∀ (q : Ideal D) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (q : Ideal C) [hq : q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let q' : Ideal D := q.comap (e : D →+* C)
  haveI : q'.IsPrime := Ideal.comap_isPrime _ _
  have H : q'.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, q', Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  let f : Localization.AtPrime q' ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q') (Localization.AtPrime q) e H
  obtain ⟨h1, h2⟩ := h q'
  exact ⟨f.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end GlobalTheory

namespace GlobalTheory

open Algebra.TensorProduct in

theorem exists_finset_mem_range_map_val {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field K] [Algebra F K] (x : A ⊗[F] K) :
    ∃ T : Finset K, ∀ R : Subalgebra F K, (↑T : Set K) ⊆ (R : Set K) →
      x ∈ (Algebra.TensorProduct.map (AlgHom.id F A) R.val).range := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun R _ ↦ Subalgebra.zero_mem _⟩
  | tmul a k =>
    refine ⟨{k}, fun R hR ↦ ⟨a ⊗ₜ ⟨k, hR (by simp)⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ ∪ T₂, fun R hR ↦ Subalgebra.add_mem _ (h₁ R ?_) (h₂ R ?_)⟩
    · exact fun z hz ↦ hR (by simp [hz])
    · exact fun z hz ↦ hR (by simp [hz])

theorem isDomain_and_isIntegrallyClosed_atPrime_tensor_field
    (hL1 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K),
      ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R)
    (hL2 : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime],
      (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
        ∀ (q : Ideal C) [q.IsPrime],
          IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A],
      (∀ (P : Ideal A) [P.IsPrime],
        IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime],
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro F K A _ _ _ _ _ _ hA Q _
  classical
  refine hL2 (TensorProduct F A K) Q fun s ↦ ?_
  choose T hT using fun x : A ⊗[F] K ↦ exists_finset_mem_range_map_val (F := F) x
  obtain ⟨R, hR, hsm⟩ := hL1 F K (s.biUnion T)
  let φ : A ⊗[F] R →ₐ[F] A ⊗[F] K := Algebra.TensorProduct.map (AlgHom.id F A) R.val
  have hφ : ⇑φ = ⇑(LinearMap.lTensor A (R.val.toLinearMap)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a k => simp [φ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj : Function.Injective φ := by
    rw [hφ]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  refine ⟨φ.range.toSubring, fun x hx ↦ hT x R (fun z hz ↦ hR ?_), ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩
  · let e : A ⊗[F] R ≃+* φ.range.toSubring := (AlgEquiv.ofInjective φ hinj).toRingEquiv
    exact isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv e fun q _ ↦
      isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall A hA q _

end GlobalTheory
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt : (∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R) → (∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  atlas_forward_decl GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_tensor_field
end

section
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine (GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_
  intro i
  change GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))
  let R := Y.affineOpenCover.X i
  have hR : GlobalTheory.IsNormalScheme (Spec R) :=
    @GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY
  let φ := Spec.preimage (𝒰.f i ≫ g)
  letI : Algebra F R := φ.hom.toAlgebra
  letI : Algebra F K := c.toAlgebra
  have e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R)) :=
    (Spec.map_preimage (𝒰.f i ≫ g)).symm
  have e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K)) := rfl
  rw [e1, e2]
  refine (GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_
  refine (GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_
  exact halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)
end

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme : (∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  atlas_forward_decl GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcRead

variable {D : D7} (O : Setup D)

def LieGen (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (E : D.what₂.Tau × Bool → Bs.Modules)
    {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) : Prop :=
  IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧
    IsFinite πB ∧ Set.range πB = Set.range (O.Φ.C c).π ∧
    ∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a)

def LieFin (P : Finset ℕ) {Bs : Scheme.{0}} (E : D.what₂.Tau × Bool → Bs.Modules)
    {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) : Prop :=
  ∀ a, IsLieLat O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (ArIn.ind P) (fun _ => True) (u a)

def LieInf (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) : Prop :=
  ∃ G : ∀ σ', EigMet O.s.T.Z σ', (∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (G (embOf O.κ.e σ)) n) ∧
    ∀ a, ∃ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a),
      IsLieMet O.s.T.Z O.κ.e q jB πB (E a) _ (embB D a) (!a.2) hr G (h a) (u a)

def LieBaseAt (P : Finset ℕ) (R : ℝ) (c : O.s.Comp) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) : Prop :=
  ∃ (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB),
    LieGen O c q E jB πB u ∧ LieFin O P E jB πB u ∧ LieInf O R c q E h jB πB u

end GlobalTheory.BcRead

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCov

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}

def FlagAgree (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) {Y₀ : Scheme.{0}}
    (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    {G : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y₀) (φ : (O.var c).Fn →+* G.functionField) (jG : G ⟶ Bg)
    (a : D.what₂.Tau × Bool) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)) : Prop :=
  haveI := (hE a).isQuasicoherent
  (∀ (k : Fin (rkB D.what₂.Tau O.N O.j a + 1)) (V : Bs.Opens) (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V))
    (hf : IsFrame f) (W : Y₀.Opens) (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ a).F k, W))
    (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧ ∀ l : Fin (O.S.Dw.mult (embB D a)), (k : ℕ) ≤ l → cf l = 0)
        (∀ (l : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v l) → (l : ℕ) + k < rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b = 0)) ∧
  ∀ (i : Fin (rkB D.what₂.Tau O.N O.j a)) (ch : (((fl₀ a).root i).pull j).ι) (V : Bs.Opens)
    (f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V)) (hf : IsFrame f) (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U)
    (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ a).F i.succ, W)), ((fl₀ a).π i).app W t = Twist.resM _ hW ((ch PUnit.unit).e 0) →
    ∀ (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V),
      let aG : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun b =>
        TangentOrigin.evalPt (genPt G ≫ j) W hx
          (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι i.succ).app W t) b)
      let uu := u a V f hf G.functionField (genPt G ≫ jG) hxV
      let v : Fin (O.S.Dw.mult (embB D a)) → (Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left) :=
        fun l => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) l
      let x := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z
      cond a.2
        (∃ (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
            (cf : Fin (O.S.Dw.mult (embB D a)) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu aG w ∧ IsCombAtG O.s.T.Z.t x v cf w ∧ cf (Fin.cast hr i) ≠ 0)
        (∀ (l : Fin (O.S.Dw.mult (embB D a))) (d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField),
          IsCombAtG O.s.T.Z.t x uu d (v l) → (l : ℕ) + i + 1 = rkB D.what₂.Tau O.N O.j a → ∑ b, aG b * d b ≠ 0)

end GlobalTheory.FlagCov

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

section Bundle

def Adapted {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} (fl : Vert.Flag N r) {W : Y.Opens} (s : Fin r → Γ(N, W)) : Prop :=
  IsFrame s ∧ ∀ k : Fin (r + 1), ∃ t : Fin k → Γ(fl.F k, W), IsFrame t ∧
    ∀ i : Fin k, (fl.ι k).app W (t i) = s (Fin.castLE (Nat.lt_succ_iff.1 k.2) i)

variable {B Y : Scheme.{0}} {M : B.Modules} {r : ℕ} (hM : IsVB M r) (π : Y ⟶ B)

def coordAt {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f) {K : Type} [CommRing K] (y : Sp K ⟶ Y) {W : Y.Opens}
    (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (s : Γ((Scheme.Modules.pullback π).obj M, W)) : Fin r → K :=
  haveI := hM.isQuasicoherent
  fun b => TangentOrigin.evalPt y W hy (((hf.pullback π).basis hWV).repr s b)

def FlagMat (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f)
    {K : Type} [CommRing K] (y : Sp K ⟶ Y) (A : Matrix (Fin r) (Fin r) K) : Prop :=
  IsUnit A.det ∧ ∀ (k : Fin (r + 1)) (W : Y.Opens) (hWV : W ≤ π ⁻¹ᵁ V) (t : Γ(fl.F k, W)) (hy : ⊤ ≤ y ⁻¹ᵁ W),
    ∃ cf : Fin r → K, (∀ l : Fin r, (k : ℕ) ≤ l → cf l = 0) ∧
      coordAt hM π hf y hWV hy ((fl.ι k).app W t) = Matrix.vecMul cf A

def StepIso (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {T : Scheme.{0}} {x : T ⟶ B}
    (fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r) (y : T ⟶ Y) (w : y ≫ π = x) : Prop :=
  ∀ i, ∃ e : (Scheme.Modules.pullback y).obj (fl.F i) ≅ fl'.F i,
    e.hom ≫ fl'.ι i = (Scheme.Modules.pullback y).map (fl.ι i) ≫
      (Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M

variable {hM π}

theorem FlagMat.mul {fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r} {V : B.Opens} {f : Fin r → Γ(M, V)}
    {hf : IsFrame f} {K : Type} [CommRing K] {y : Sp K ⟶ Y} {A T : Matrix (Fin r) (Fin r) K}
    (h : FlagMat hM π fl hf y A) (hT : IsUnit T.det) (hT' : ∀ i j, i < j → T i j = 0) :
    FlagMat hM π fl hf y (T * A) := by
  refine ⟨by rw [Matrix.det_mul]; exact hT.mul h.1, fun k W hWV t hy => ?_⟩
  obtain ⟨cf, h1, h2⟩ := h.2 k W hWV t hy
  have := T.invertibleOfIsUnitDet hT
  have hb : T.BlockTriangular OrderDual.toDual := fun a b hab => hT' a b hab
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.vecMul cf T⁻¹, fun l hl => ?_, ?_⟩
  · rw [Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m l with hm | hm
    · rw [show T⁻¹ m l = 0 from hi hm, mul_zero]
    · rw [h1 m (hl.trans hm), zero_mul]
  · rw [h2, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]

end Bundle

def lieMat (dual : Bool) {r : ℕ} {K : Type} [CommRing K] (d : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  cond dual ((Matrix.transpose d⁻¹).submatrix Fin.rev id) d

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def AgreeAt {Bs Bg Y : Scheme.{0}} {M : Bs.Modules} {r : ℕ} (hM : IsVB M r) (jB : Bg ⟶ Bs) (u : FrAssign Z M r jB)
    (π : Y ⟶ Bs) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (dual : Bool) {K : Type} [CommRing K]
    (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (x : Sp K ⟶ Z.X) (v : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)) : Prop :=
  ∀ (V : Bs.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin r) (Fin r) K),
    (∀ i, IsCombAtG Z.t x (u V f hf K xb hx) (d i) (v i)) → FlagMat hM π fl hf y (lieMat dual d)

def Bears {ι : Type} {rk : ι → ℕ} (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a))
    {Bs Bg Y : Scheme.{0}} {M : ι → Bs.Modules} (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z)
    (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)) {K : Type} [CommRing K]
    (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) {χ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z χ x) : Prop :=
  y ≫ π = xb ≫ jB ∧ x = xb ≫ πB ≫ genι Z ∧ xb ≫ πB ≫ genStr Z = spMap χ ∧
    ∀ a, AgreeAt Z (hM a) jB (u a) π (fl a) (dual a) y xb x fun i => g.v (emb a) (Fin.cast (hr a) i)

end Lie

end GlobalTheory.FlagCls

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

namespace GlobalTheory.FlagCls

theorem isNormalScheme_of_isPreimmersion_of_flat {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isNormalScheme_of_isPullback_fractionField : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N G : Scheme.{0}) (g : N ⟶ Sp R) (j : G ⟶ N) (s : G ⟶ Sp K), IsPullback j s g (spMap (algebraMap R K)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G := by
  intro R K _ _ _ _ _ N G g j s hp hN
  have hb : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) hp.flip hb
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) hp.flip hbf
  exact isNormalScheme_of_isPreimmersion_of_flat j hN

end GlobalTheory.FlagCls
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.GenFibNormal

theorem genFibre_of_fieldChange (hd2 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c))) : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) := by
  intro o K _ _ _ _ b hb Z z L hP hN hL hA
  haveI hsa : IsAffineHom (spMap b) := inferInstance
  haveI : IsAffineHom (pullback.fst z (spMap b)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback z (spMap b)).flip hsa
  refine ⟨ProjSpace.isProjOver_pullback_snd b hP, ?_, LB.isLB_pull hL _, IsAmpleLB.pull_of_isAffineHom hA _⟩
  haveI : CharZero o := ⟨fun m n h => by
    have := congrArg b h; simp only [map_natCast] at this; exact_mod_cast this⟩
  let F := FractionRing o
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective o F)
  let b' : F →+* K := IsFractionRing.lift hb
  have hbb : b'.comp (algebraMap o F) = b := RingHom.ext fun x => IsFractionRing.lift_algebraMap hb x
  have hZF : GlobalTheory.IsNormalScheme (pullback z (spMap (algebraMap o F))) :=
    IsNormalScheme.of_pred (FlagCls.isNormalScheme_of_isPullback_fractionField o F Z _ z
      (pullback.fst z (spMap (algebraMap o F))) (pullback.snd z (spMap (algebraMap o F)))
      (IsPullback.of_hasPullback _ _) ((isNormalScheme_iff_pred Z).mp hN))
  have h1 := hd2 F K b' _ (pullback.snd z (spMap (algebraMap o F))) hZF
  have e := pullbackLeftPullbackSndIso z (spMap (algebraMap o F)) (spMap b')
  have hc : spMap b' ≫ spMap (algebraMap o F) = spMap b := by
    rw [← hbb]
    simp only [spMap, ← Spec.map_comp]
    rfl
  exact (IsNormalScheme.iff_of_iso (e ≪≫ pullback.congrHom rfl hc)).mp h1

theorem genericFibre_normal_projective_ample : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) :=
  genFibre_of_fieldChange (GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme (GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings))

end GlobalTheory.GenFibNormal
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_normal_projective_ample_charZero : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) := by
  atlas_forward_decl GlobalTheory.GenFibNormal.genericFibre_normal_projective_ample
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.NormBlowupField

theorem exists_normBl : ∀ (K : Type) [Field K] [CharZero K] (Z : Scheme.{0}) (z : Z ⟶ Sp K),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ IsProper π ∧
    BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro K _ _ Z z hz hZ J W hWd hWJ
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str K m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of K) V.ι (b ≫ z)
      (fun x _ => charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (V.ι ≫ b ≫ z).appTop ≫ V.toScheme.presheaf.germ ⊤ x trivial ≫ V.toScheme.residue x).hom)
        (RingHom.injective _))
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := GlobalTheory.NormBlowupInt.dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  have hproj : IsProjOver ((ν ≫ b) ≫ z) := by
    rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  have hprop : IsProper (ν ≫ b) := by
    haveI : IsProper z := by
      obtain ⟨m, i, hi, e⟩ := hz
      have := isProper_str K m
      rw [← e]; infer_instance
    haveI : IsProper ((ν ≫ b) ≫ z) := by
      obtain ⟨m, i, hi, e⟩ := hproj
      have := isProper_str K m
      rw [← e]; infer_instance
    exact IsProper.of_comp (ν ≫ b) z
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, hproj, hprop, ?_, ?_, ?_⟩
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupField
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoincTop

theorem uPoinStX_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
      (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S)
      (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD ∧ GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hφ hns l Xo c
  obtain ⟨C⟩ := GlobalTheory.T.unitary_integral_compactifications_exist E H Dw hpq l Xo c
  obtain ⟨d, J₀, hd, hJ₀, hval₀⟩ := GlobalTheory.T.unitaryCompactification_exists_boundary_ideal E H Dw hpq φ hφ l Xo c C
  haveI := C.ded
  haveI := C.iF_open
  have hgen := GlobalTheory.T.generic_fibre_normal_projective_ample_charZero C.o c.F C.b C.inj C.Z C.z C.OZ C.proj C.normal C.OZ_lb C.OZ_ample
  obtain ⟨hprojZ, hnormZ, hOZlb, hOZamp⟩ := hgen
  let Z := pullback C.z (spMap C.b)
  let fZ : Z ⟶ C.Z := pullback.fst C.z (spMap C.b)
  let J : Z.IdealSheafData := J₀.comap fZ
  let W : Z.Opens := C.iF.opensRange
  have hWset : (W : Set Z) = Set.range C.iF := by simp [W]
  have hJ : ∀ x ∈ J.support, x ∉ Set.range C.iF := by
    intro x hx hxr
    rw [Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨y, rfl⟩ := hxr
    exact hJ₀ _ hx ⟨y, rfl⟩
  have hval : UValOn Xo c C.iF φ J d := by
    intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval₀ W' hW ϖ hϖ (χ ≫ fZ) y
      (by rw [UCompact.i, ← Category.assoc, hy, Category.assoc]) t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  obtain ⟨S, π, BD, hbl, hpS, hprop, hBD, hiso, hdS⟩ :=
    GlobalTheory.NormBlowupField.exists_normBl c.F Z (pullback.snd C.z (spMap C.b)) hprojZ hnormZ J W (by rw [hWset]; exact C.iF_dense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : Xo.XF c ⟶ (π ⁻¹ᵁ W).toScheme := C.iF.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : Xo.XF c ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = C.iF := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range C.iF := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  have hjo : IsOpenImmersion j := inferInstance
  refine ⟨Z, pullback.snd C.z (spMap C.b), C.iF, C.OZ.pull fZ, C.N, d, J, S, π, j, BD, ⟨⟨hprojZ, hnormZ, C.iF_open,
    C.iF_dense, C.iF_over, hOZlb, hOZamp⟩, ⟨C.N_pos, ?_⟩, ?_, ⟨hd, hJ, hval⟩, ⟨hbl, hpS, hjo, ?_, hjπ, hrj.symm, hBD, ?_⟩, ?_⟩, ?_⟩
  · intro Y f hf hY
    have h := C.omega Y f hf hY
    exact LBIso.trans (pull_isLB hOZlb f) (pull_isLB C.OZ_lb _) (LB.isLB_linComb hY _ _)
      (LBIso.symm (GlobalTheory.FibreNef.lbIso_pull_comp C.OZ_lb fZ f)) h
  · intro R _ _ _ hR t hP y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := C.ext R hR t hP y hy (σ ≫ spMap C.b) (by rw [← Category.assoc, hσ, Category.assoc])
    refine ⟨pullback.lift ξ₀ σ (by rw [h₂]), ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact h₁
    · simp only [Category.assoc, pullback.lift_snd, C.iF_over]; exact hσ
  · rw [hrj, ← hWset]; exact hdS
  · intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval W' hW ϖ hϖ (χ ≫ π) y (by rw [← Category.assoc, ← hy, Category.assoc, hjπ])
      t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    obtain ⟨T₀, hT⟩ := GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup c.F Z S₀ S (pullback.snd C.z (spMap C.b)) J π₀ ν BD hprojZ hb hfin
      (by rw [hνπ]; exact hBD) (C.OZ.pull fZ) hOZamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h
  · exact GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification E H Dw hpq φ hφ hns l Xo c C d J₀ hd hJ₀ hval₀ S π j hbl hprop hjπ hjo hrj.symm

theorem uStB : GlobalTheory.UChart.UStB := uPoinStX_sep

end GlobalTheory.UPoincTop
end
end

open GlobalTheory.UChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  atlas_forward_decl GlobalTheory.UPoincTop.uStB
end
