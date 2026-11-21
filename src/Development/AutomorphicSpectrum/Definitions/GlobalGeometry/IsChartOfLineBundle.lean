import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LatModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

def frameLat (ξ : Spec (CommRingCat.of Ω) ⟶ X) {r : ℕ} (b : Fin r → E) : Lat ξ E :=
  fun p => Submodule.span (regAt ξ p) (Set.range b)

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}





section Deg
variable {K : Type} [Fintype K] {ι : K → Type}

def seg (y : (Σ k, ι k) → Ω) : ((k : K) → ι k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩

theorem ratio_mem {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {p : Cpt ξ} (h : InChart ξ (seg y) c p)
    (k : K) (i : ι k) : y ⟨k, c k⟩ ≠ 0 ∧ y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h0 : ∀ l, y ⟨l, c l⟩ ≠ 0 := fun l => Finset.prod_ne_zero_iff.1 h.1 l (Finset.mem_univ _)
  refine ⟨h0 k, ?_⟩
  have := h.2 (Function.update c k i)
  have e : seg y (Function.update c k i) / seg y c = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    unfold seg
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      rw [Function.update_of_ne hl, div_self (h0 l)]
    · simp
  rwa [e] at this





end Deg

section Pull
variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

theorem dominates_spec {f : X' ⟶ X} {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (p' : Cpt ξ') :
    genPt ξ ⤳ f p'.1 := by
  have e : f (genPt ξ') = genPt ξ := by
    have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
    have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    exact h1.trans (congrArg ξ h2)
  exact e ▸ p'.2.map f.continuous

theorem dominates_regAt {f : X' ⟶ X} {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (p' : Cpt ξ')
    (hp : genPt ξ ⤳ f p'.1) {a : Ω} (ha : a ∈ regAt ξ ⟨f p'.1, hp⟩) : i a ∈ regAt ξ' p' := by
  obtain ⟨q, hq⟩ := p'
  obtain ⟨s, rfl⟩ := ha
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact ⟨f.stalkMap q s, congrArg (fun g => g.hom s) e⟩

end Pull

section Int

def ξZ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))

def two : PrimeSpectrum ℤ := ⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩

theorem gen_spec (q : PrimeSpectrum ℤ) : genPt ξZ ⤳ (q : Spec (CommRingCat.of ℤ)) := by
  have : PrimeSpectrum.asIdeal (R := ℤ) (genPt ξZ) ≤ q.asIdeal := by
    intro n hn
    have h1 : (n : ℚ) ∈ IsLocalRing.maximalIdeal ℚ := hn
    have : n = 0 := by simpa [IsLocalRing.maximalIdeal_eq_bot] using h1
    rw [this]; exact zero_mem _
  exact (PrimeSpectrum.le_iff_specializes (R := ℤ) _ _).1 this

def pt2 : Cpt ξZ := ⟨two, gen_spec two⟩

theorem half_notMem : (2⁻¹ : ℚ) ∉ regAt ξZ pt2 := by
  rintro ⟨s, hs⟩
  let : Algebra ℤ ((Spec (CommRingCat.of ℤ)).presheaf.stalk pt2.1) := StructureSheaf.stalkAlgebra ℤ two
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of ℤ)).presheaf.stalk pt2.1) two.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk ℤ two
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj two.asIdeal.primeCompl s
  have h := congrArg (genMap ξZ pt2) hab
  rw [map_mul, hs, eq_intCast, eq_intCast, map_intCast, map_intCast] at h
  apply b.2
  have : (b.1 : ℚ) = ((2 * a : ℤ) : ℚ) := by push_cast; simp only at h; linarith
  have hb : b.1 = 2 * a := by exact_mod_cast this
  show b.1 ∈ Ideal.span {2}
  rw [hb]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)




end Int

end GlobalTheory.CompanionTheory.Ar.LatModel
