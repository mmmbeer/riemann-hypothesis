import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]


namespace PolyTower

variable (R : Subring K) [IsLocalRing R] (r : ℕ)

def origin : Ideal (MvPolynomial (Fin r) R) :=
  (IsLocalRing.maximalIdeal R).comap MvPolynomial.constantCoeff

instance : (origin R r).IsPrime := Ideal.comap_isPrime _ _

def topRing : Subring (FractionRing (MvPolynomial (Fin r) R)) :=
  (Localization.subalgebra.ofField (FractionRing (MvPolynomial (Fin r) R))
    (origin R r).primeCompl (origin R r).primeCompl_le_nonZeroDivisors).toSubring

instance : Algebra (MvPolynomial (Fin r) R) (topRing R r) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin r) R)
    (Localization.subalgebra.ofField (FractionRing (MvPolynomial (Fin r) R))
      (origin R r).primeCompl (origin R r).primeCompl_le_nonZeroDivisors))

instance : IsLocalization.AtPrime (topRing R r) (origin R r) :=
  Localization.subalgebra.isLocalization_ofField (FractionRing (MvPolynomial (Fin r) R))
    (origin R r).primeCompl (origin R r).primeCompl_le_nonZeroDivisors

theorem coe_algebraMap (x : MvPolynomial (Fin r) R) :
    ((algebraMap _ (topRing R r) x : topRing R r) : FractionRing (MvPolynomial (Fin r) R)) =
      algebraMap _ _ x := rfl

def incl : R →+* topRing R r := (algebraMap (MvPolynomial (Fin r) R) (topRing R r)).comp MvPolynomial.C

def coord (i : Fin r) : topRing R r := algebraMap (MvPolynomial (Fin r) R) (topRing R r) (MvPolynomial.X i)

theorem unit_const (y : (origin R r).primeCompl) :
    IsUnit (MvPolynomial.constantCoeff (y : MvPolynomial (Fin r) R)) := by
  by_contra h
  exact y.2 h

def sect : topRing R r →+* R := IsLocalization.lift (S := topRing R r) (unit_const R r)

theorem sect_algebraMap (x : MvPolynomial (Fin r) R) :
    sect R r (algebraMap _ (topRing R r) x) = MvPolynomial.constantCoeff x :=
  IsLocalization.lift_eq _ _

theorem eval_eq : MvPolynomial.eval₂Hom (incl R r) (coord R r) =
    algebraMap (MvPolynomial (Fin r) R) (topRing R r) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [incl]
  · intro i; simp [coord]

theorem coord_ne_zero (i : Fin r) : coord R r i ≠ 0 := by
  intro h
  have e := congrArg Subtype.val h
  rw [coord, coe_algebraMap] at e
  exact MvPolynomial.X_ne_zero i ((IsFractionRing.to_map_eq_zero_iff).1 e)

end PolyTower

open PolyTower in

theorem IsEtTower.poly {c : k →+* K} {R : Subring K} [IsLocalRing R] (h : IsLocModel c R)
    (h' : IsIntegrallyClosed R) (r : ℕ) :
    IsEtTower c R ((topRing R r).subtype.comp ((incl R r).comp (c.codRestrict R h.const_mem)))
      (topRing R r) (incl R r) (sect R r) (coord R r) where
  base := h
  normal := h'
  top :=
    { const_mem := fun a => (incl R r _).2
      isLocalRing := IsLocalization.AtPrime.isLocalRing _ (origin R r)
      essFiniteType := by
        have e1 : (MvPolynomial.C : R →+* MvPolynomial (Fin r) R).EssFiniteType :=
          RingHom.essFiniteType_algebraMap.2
            (inferInstance : Algebra.EssFiniteType R (MvPolynomial (Fin r) R))
        have e2 : (algebraMap (MvPolynomial (Fin r) R) (topRing R r)).EssFiniteType :=
          RingHom.essFiniteType_algebraMap.2
            (Algebra.EssFiniteType.of_isLocalization _ (origin R r).primeCompl)
        exact (h.essFiniteType.comp e1).comp e2
      frac := fun f => by
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin r) R) f
        have hb' : algebraMap _ (FractionRing (MvPolynomial (Fin r) R)) b ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        exact ⟨_, (algebraMap _ (topRing R r) a).2, _, (algebraMap _ (topRing R r) b).2, hb',
          div_mul_cancel₀ _ hb'⟩ }
  const _ := rfl
  retr a := by simp [incl, sect_algebraMap]
  zero i := by simp [coord, sect_algebraMap]
  etale := by
    rw [eval_eq]
    have := Algebra.FormallyEtale.of_isLocalization (Rₘ := topRing R r) (origin R r).primeCompl
    exact RingHom.formallyEtale_algebraMap.2 this







example (R : Subring K) : RatRes (RingHom.id K) R :=
  fun r _ => ⟨r, by rw [RingHom.id_apply, sub_self]; exact ⟨R.zero_mem, Or.inl rfl⟩⟩


theorem IsEtTower.exists_deriv {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (v : Fin r → R) : ∃ φ : T →+* DualNumber R, (∀ a, φ (ι a) = TrivSqZeroExt.inl a) ∧
      ∀ i, φ (τ i) = TrivSqZeroExt.inr (v i) := by
  let P := MvPolynomial (Fin r) R
  letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  let g : P →+* DualNumber R :=
    MvPolynomial.eval₂Hom (algebraMap R (DualNumber R)) fun i => TrivSqZeroExt.inr (v i)
  letI : Algebra P (DualNumber R) := g.toAlgebra
  letI : Algebra P R := (MvPolynomial.constantCoeff : P →+* R).toAlgebra
  let ψ' : T →ₐ[P] R :=
    { ψ with
      commutes' := fun x => by
        have : ψ.comp (MvPolynomial.eval₂Hom ι τ) = MvPolynomial.constantCoeff := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [h.retr]
          · intro i; simp [h.zero]
        exact RingHom.congr_fun this x }
  let f : DualNumber R →ₐ[P] R :=
    { (TrivSqZeroExt.fstHom R R R).toRingHom with
      commutes' := fun x => by
        have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp g = MvPolynomial.constantCoeff := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [g]
          · intro i; simp [g]
        exact RingHom.congr_fun this x }
  have hs : Function.Surjective f := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker (f : DualNumber R →+* R)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  let φ := Algebra.FormallySmooth.liftOfSurjective ψ' f hs hn
  refine ⟨φ.toRingHom, fun a => ?_, fun i => ?_⟩
  · have := φ.commutes (MvPolynomial.C a)
    change φ (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C a)) = g (MvPolynomial.C a) at this
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C] at this
    exact this
  · have := φ.commutes (MvPolynomial.X i)
    change φ (MvPolynomial.eval₂Hom ι τ (MvPolynomial.X i)) = g (MvPolynomial.X i) at this
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'] at this
    exact this

theorem IsEtTower.coord_ne_zero {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (j : Fin r) : τ j ≠ 0 := by
  intro e
  obtain ⟨φ, -, h2⟩ := h.exists_deriv (fun _ => 1)
  have := congrArg TrivSqZeroExt.snd (h2 j)
  simp [e] at this

theorem IsEtTower.ker_eq_span {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    RingHom.ker ψ = Ideal.span (Set.range τ) := by
  haveI := h.top.isLocalRing
  haveI : IsNoetherianRing T := by
    letI := (cL.codRestrict T h.top.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType k T := h.top.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k T
  let P := MvPolynomial (Fin r) R
  letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  set I := RingHom.ker ψ
  set J : Ideal T := Ideal.span (Set.range τ)
  have hJI : J ≤ I := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h.zero i)
  have hsub : ∀ x, x - ι (ψ x) ∈ I := fun x => by
    show ψ _ = 0
    rw [map_sub, h.retr, sub_self]
  let Q : Ideal T := J ⊔ I * I
  let g : T →ₐ[P] T ⧸ Q :=
    { (Ideal.Quotient.mk Q).comp (ι.comp ψ) with
      commutes' := fun x => by
        have : ((Ideal.Quotient.mk Q).comp (ι.comp ψ)).comp (MvPolynomial.eval₂Hom ι τ) =
            (Ideal.Quotient.mk Q).comp (MvPolynomial.eval₂Hom ι τ) := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [h.retr]
          · intro i
            have : τ i ∈ Q := Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
            simp [h.zero, Ideal.Quotient.eq_zero_iff_mem.2 this]
        exact RingHom.congr_fun this x }
  have hn : IsNilpotent (I.map (Ideal.Quotient.mk Q)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have he : Ideal.Quotient.mkₐ P Q = g := by
    refine Algebra.FormallyUnramified.ext _ hn fun x => ?_
    rw [Ideal.Quotient.eq]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk Q) (hsub x)
    rw [map_sub] at this
    exact this
  have hIQ : I ≤ J ⊔ I • I := fun x hx => by
    have e := AlgHom.congr_fun he x
    have hx' : ψ x = 0 := hx
    have : Ideal.Quotient.mk Q x = 0 := by
      refine e.trans ?_
      show Ideal.Quotient.mk Q (ι (ψ x)) = 0
      rw [hx', map_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hI : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hI hIQ) hJI

theorem IsEtTower.bijective_of_zero {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {ι : R →+* T} {ψ : T →+* R} {τ : Fin 0 → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Bijective ψ := by
  refine ⟨(RingHom.injective_iff_ker_eq_bot ψ).2 ?_, fun a => ⟨ι a, h.retr a⟩⟩
  rw [h.ker_eq_span, Set.range_eq_empty, Ideal.span_empty]

end GlobalTheory.FieldPair
