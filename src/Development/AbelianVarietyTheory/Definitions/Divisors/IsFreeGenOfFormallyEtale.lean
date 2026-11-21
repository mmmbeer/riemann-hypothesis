import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair.Model

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}






section Scheme

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}



end Scheme

theorem exists_chart [PerfectField k] (E : Place c) {x : Fin 2 → K} (hx : TrBasis c x) :
    ∃ t u : E.ring, Irreducible t ∧ IsUnit u ∧ IsUnit (u - 1) ∧
      IsFreeGen E.ring (dForm E.const ![t, u]) := by
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, hz, hb⟩ := exists_basis_kaehler_uniformiser k ht
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : m = 1 := by
    have : 2 = m + 1 := by exact_mod_cast h2
    omega
  have key (w : E.ring) (hw : KaehlerDifferential.D k E.ring w = b 1) : IsUnit w := by
    by_contra hu
    have hm : w ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hu
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hm
    rw [Derivation.leibniz, ← hz, ← hb 0] at hw
    have := congrArg (fun η => b.repr η 1) hw
    simp at this
    exact ht.not_isUnit (IsUnit.of_mul_eq_one _ (hz ▸ this))
  have ez : z = ![t, z 1] := by
    funext i
    fin_cases i
    · exact hz
    · rfl
  refine ⟨t, z 1, ht, key _ (hb 1).symm, key _ (by simp [hb 1]), ?_⟩
  rw [← ez]
  exact isFreeGen_dForm z b hb



end GlobalTheory.FieldPair.Model
end
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair.AdjModel

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem isUnit_of_ord_eq_zero (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0)
    (h : P.ord (b : K) = 0) : IsUnit b := by
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))


theorem isFreeGen_of_formallyEtale {A B : Type} [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {x : Fin n → A}
    (hω : IsFreeGen A (dForm α x)) : IsFreeGen B (dForm β fun i => ρ (x i)) := by
  rw [← formMap_dForm ρ h]
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) n)


theorem exists_place {Q : Subring K} (hQ : IsLocModel c Q) {t : Q} (ht : Prime t) :
    ∃ S : Place c, S.IsPrimeOf Q ∧ S.ord (t : K) = 1 ∧
      ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ord (t : K) = 0 := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := by
    letI := c0.toAlgebra
    haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k Q
  haveI : IsFractionRing Q K := by
    refine IsFractionRing.of_field Q K fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  let p : Ideal Q := Ideal.span {t}
  haveI : p.IsPrime := (Ideal.span_singleton_prime ht.ne_zero).2 ht
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q K := Localization.subalgebra.ofField K p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField K _ hp
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap Q A t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap Q A t ≠ 0 := fun e => ht.ne_zero (Subtype.ext (congrArg (fun z : A => (z : K)) e))
  have hnf : ¬ IsField A := fun hf => ht0 (by
    have := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hm] at this
    exact Ideal.span_singleton_eq_bot.1 this)
  haveI : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 (show (IsLocalRing.maximalIdeal A).IsPrincipal from ⟨_, hm⟩)
  haveI : IsFractionRing A K := Localization.subalgebra.isFractionRing_ofField K _ hp
  let V : ValuationSubring K :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, ?_, fun P hP hne => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · exact S.ord_irreducible (t := algebraMap Q A t)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm)
  · by_contra h0
    have htK : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
    have h1 : 0 ≤ P.ord (t : K) := (P.ord_nonneg_iff htK).2 (hP.1 _ t.2)
    refine hne (ValuationSubring.eq_of_le_of_ne_top P.ring (fun f hf => ?_) S.ring_ne_top)
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 f hf
    have hbp : (⟨b, hb⟩ : Q) ∉ p := fun h => by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
      have hd' : b = t * d := congrArg Subtype.val hd
      have hd0 : (d : K) ≠ 0 := fun h => hb0 (by rw [hd', h, mul_zero])
      have := (P.ord_nonneg_iff hd0).2 (hP.1 _ d.2)
      rw [hd', P.ord_mul htK hd0] at hbo
      omega
    obtain ⟨g, hg⟩ := (hu _ hbp).exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    have : f = a * g := by rw [← e, mul_assoc, hg', mul_one]
    rw [this]
    exact A.mul_mem (A.algebraMap_mem ⟨a, ha⟩) g.2

open MvPolynomial in

theorem exists_plane (k : Type) [Field k] :
    ∃ (Q : Subring (FractionRing (MvPolynomial (Fin 2) k)))
      (hQ : IsLocModel (algebraMap k _) Q) (x : Fin 2 → Q),
      (∀ i, (x i : FractionRing (MvPolynomial (Fin 2) k)) =
        algebraMap (MvPolynomial (Fin 2) k) _ (X i)) ∧
      Ideal.span {x 0, x 1} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) ∧
      ringKrullDim Q = 2 ∧ (∀ i, Prime (x i)) ∧
      IsFreeGen Q (dForm ((algebraMap k _).codRestrict Q hQ.const_mem) x) := by
  let P := MvPolynomial (Fin 2) k
  let L := FractionRing P
  let q : Ideal P := RingHom.ker (constantCoeff : P →+* k)
  have hs : Function.Surjective (constantCoeff : P →+* k) := fun a => ⟨C a, constantCoeff_C _ a⟩
  haveI : q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hs
  have hq : q.primeCompl ≤ nonZeroDivisors P := q.primeCompl_le_nonZeroDivisors
  let A : Subalgebra P L := Localization.subalgebra.ofField L q.primeCompl hq
  haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq
  let a : P →+* A := algebraMap P A
  have hc : ∀ x, algebraMap k L x ∈ A.toSubring := fun x => A.algebraMap_mem (C x)
  have e : (algebraMap k L).codRestrict A.toSubring hc = a.comp (algebraMap k P) := rfl
  haveI := IsLocalization.AtPrime.isLocalRing A q
  have hX : ∀ i, X i ∈ q := fun i => constantCoeff_X k i
  have hsp : q = Ideal.span {X 0, X 1} := by
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.2 ?_)
    · have : (({X 0, X 1} : Set P)) = X '' (Set.univ : Set (Fin 2)) := by
        ext z; simp [eq_comm]
      rw [this, mem_ideal_span_X_image]
      intro m hm
      by_contra hc
      push Not at hc
      have : m = 0 := Finsupp.ext fun i => hc i trivial
      subst this
      exact (mem_support_iff.1 hm) hf
    · rintro _ (rfl | rfl) <;> exact hX _
  refine ⟨A.toSubring, ⟨hc, ‹IsLocalRing A›, ?_, ?_⟩, fun i => a (X i), fun _ => rfl, ?_, ?_,
    fun i => ?_, ?_⟩
  · rw [e]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType k P)
    · exact (RingHom.essFiniteType_algebraMap (R := P) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)
  · intro f
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := P) f
    have hy' : algebraMap P L y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · change (Ideal.span {a (X 0), a (X 1)} : Ideal A) = IsLocalRing.maximalIdeal A
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q A]
    conv_rhs => rw [hsp]
    rw [Ideal.map_span, Set.image_pair]
  · change ringKrullDim A = 2
    have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k 2 q
    rw [ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient q).1 ‹_›), add_zero] at h
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q A, h]
    rfl
  · change Prime (a (X i))
    have h0 : a (X i) ≠ 0 := fun h => X_ne_zero i
      (IsFractionRing.injective P L ((congrArg (fun z : A => (z : L)) h).trans (map_zero _).symm))
    have hp : (Ideal.span {(X i : P)}).IsPrime :=
      (Ideal.span_singleton_prime (X_ne_zero i)).2 X_prime
    have := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl A _ hp
      (Set.disjoint_left.2 fun z hz hz' => hz (Ideal.span_le.2 (by simpa using hX i) hz'))
    rw [Ideal.map_span, Set.image_singleton] at this
    exact (Ideal.span_singleton_prime h0).1 this
  · exact isFreeGen_of_formallyEtale (α := algebraMap k P) (ρ := a)
      (RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl))
      rfl (isFreeGen_dForm_X k 2)


theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 :=
  ⟨fun h h0 => h (isUnit_of_ord_eq_zero P b hb h0), fun h hu => h (P.ord_eq_zero hu)⟩

theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)



end GlobalTheory.FieldPair.AdjModel
end
end
