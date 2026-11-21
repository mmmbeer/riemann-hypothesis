import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal
open GlobalTheory.AntiRamConj GlobalTheory.Mem.Chr GlobalTheory.AntiLAdic
open scoped Pointwise

namespace GlobalTheory.GalToHecke

section Tame

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : v.valuation L (x : L) ≠ 0 := by simp
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have h1 : v.valuation L (((y * x⁻¹ : Lˣ) : L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
    have : ((y * x⁻¹ : Lˣ) : L) - 1 = ((y : L) - x) * (x : L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ x.ne_zero]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hxy
  have h2 : v.valuation L ((y * x⁻¹ : Lˣ) : L) = 1 := by
    have := Valuation.map_one_add_of_lt (v.valuation L) (h1.trans_lt exp_neg_one_lt_one)
    rwa [add_sub_cancel] at this
  have h3 : χ.locK v (y * x⁻¹) = 1 := by
    refine h (atFin v (y * x⁻¹)) ?_ ?_
    · exact (hval _).trans h2
    · have : ((atFin v (y * x⁻¹) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
          algebraMap L (v.adicCompletion L) (((y * x⁻¹ : Lˣ) : L) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, hval]
      simpa using h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h3

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg (ht v)⟩
  choose n hn using hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]; simp
  have e2 : v.valuation L (t v : L) = v.intValuation (t v) := HeightOneSpectrum.valuation_of_algebraMap (K := L) v _
  rw [e1, e2, hn, ← WithZero.exp_add]
  convert h1 using 2
  push_cast; ring

end Tame

section Basic

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Ideles E →* Gab E Ω}

def IsHeckeOf (art : Ideles E →* Gab E Ω) (r : G E Ω →* ℂˣ) (χ : HChar E) : Prop :=
  ∀ (x : Ideles E) (σ : G E Ω), art x = toAb E Ω σ → χ.1 x = r σ

def heckeOf (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) : HChar E :=
  ⟨(liftAb r (continuous_of_isOpen_ker' r hr)).comp art,
    (continuous_liftAb r (continuous_of_isOpen_ker' r hr)).comp ha.quot.continuous, fun k => by
      have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]⟩

theorem isHeckeOf_heckeOf (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) :
    IsHeckeOf art r (heckeOf ha r hr) := fun x σ h => by
  show liftAb r (continuous_of_isOpen_ker' r hr) (art x) = r σ
  rw [h, liftAb_toAb]

variable {r : G E Ω →* ℂˣ} {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem IsHeckeOf.unique (h : IsHeckeOf art r χ) {χ' : HChar E} (h' : IsHeckeOf art r χ') : χ = χ' :=
  Subtype.ext (MonoidHom.ext fun x => by
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    rw [h x σ hσ.symm, h' x σ hσ.symm])

theorem IsHeckeOf.orderDvd (h : IsHeckeOf art r χ) {m : ℕ} (hm : ∀ σ, r σ ^ m = 1) : χ.OrderDvd m :=
  Subtype.ext (MonoidHom.ext fun x => by
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    show χ.1 x ^ m = 1
    rw [h x σ hσ.symm, hm])

theorem IsHeckeOf.unr_iff (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hA : IsPlaceOver A v) :
    χ.UnrAt v ↔ ∀ σ ∈ Ine (F := E) A, r σ = 1 := by
  constructor
  · intro H σ hσ
    obtain ⟨x, hx, e⟩ := (ha.ine v A hA _).2 ⟨σ, hσ, rfl⟩
    rw [← h _ σ e]
    exact H x hx
  · intro H x hx
    obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    exact (h _ σ e.symm).trans (H σ hσ)

theorem IsHeckeOf.val_eq (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hu : χ.UnrAt v) (hA : IsPlaceOver A v)
    {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) : χ.val v = (r σ)⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩
  rw [← χ.val_eq hu x hx, ← map_inv]
  exact h _ _ e

theorem IsHeckeOf.loc_eq_one (ha : IsGlobalArtin art) (h : IsHeckeOf art r χ) (hA : IsPlaceOver A v)
    (H : ∀ σ ∈ Dec (F := E) A, r σ = 1) (x : (v.adicCompletion E)ˣ) : χ.loc v x = 1 := by
  have hm : art (localIdele E v x) ∈ (Dec (F := E) A).map (toAb E Ω) := by
    rw [← ha.dec v A hA]
    exact Subgroup.le_topologicalClosure _ ⟨x, rfl⟩
  obtain ⟨σ, hσ, e⟩ := hm
  exact (h _ σ e.symm).trans (H σ hσ)

theorem tameAt_of_orderDvd {l k : ℕ} (hl : l.Prime) (h : χ.OrderDvd (l ^ k)) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    χ.TameAt v := by
  intro x _ hx
  have h1 : ∀ y, χ.1 y ^ (l ^ k) = 1 := fun y => congrArg (fun ξ : HChar E => ξ.1 y) h
  have ho := isOpen_ker_of_pow χ.1 χ.2.1 (pow_pos hl.pos k) h1
  let θ : (v.adicCompletion E)ˣ →* rootsOfUnity (l ^ k) ℂ := (χ.loc v).codRestrict _ fun y => h1 _
  have := GlobalTheory.RingCls.tame hl (B := rootsOfUnity (l ^ k) ℂ) (fun z => ⟨k, Subtype.ext z.2⟩) hv θ (by
    convert ho.preimage (Determ.continuous_localIdele v) using 1
    ext y
    exact Subtype.ext_iff) x (hx.trans_lt (by simpa using exp_neg_one_lt_one))
  exact congrArg Subtype.val this

theorem locInf_eq_one [IsTotallyComplex E] {m : ℕ} (hm : 0 < m) (h : χ.OrderDvd m) (w : InfinitePlace E)
    (y : (w.Completion)ˣ) : χ.locInf w y = 1 := by
  have h1 : ∀ y, χ.1 y ^ m = 1 := fun y => congrArg (fun ξ : HChar E => ξ.1 y) h
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e y) hm
  have hy : e.symm z ^ m = y := e.injective (by rw [map_pow, e.apply_symm_apply, hz])
  have h0 : e.symm z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm.ne'] at hy
    exact y.ne_zero hy.symm
  have e1 : y = Units.mk0 _ h0 ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)
  rw [e1, map_pow]
  exact h1 _

end Basic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_aboveF {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem valuation_up (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    P.valuation E (algebraMap F E x) = (P.under (𝓞 F)).valuation F x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hr P (Units.mk0 x hx)
  unfold ordF at h
  have h1 : P.valuation E (algebraMap F E x) ≠ 0 := by simpa using hx
  have h2 : (P.under (𝓞 F)).valuation F x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h1, ← WithZero.exp_log h2]
  exact congrArg WithZero.exp (neg_injective h)

theorem resFin_eq (χ : HChar E) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    χ.resFin v k = ∏ P ∈ aboveF (L := E) F v, χ.locK P (upF F k) := by
  rw [HChar.resFin, MonoidHom.finsetProd_apply]
  rfl

theorem trivOn_of_cofinite (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (χ : HChar E) (htame : ∀ P, χ.TameAt P) (hinf : ∀ w y, χ.locInf w y = 1) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ T → χ.UnrAt P)
    (hv : ∀ v, v ∉ T → ∏ P ∈ aboveF (L := E) F v, χ.val P = 1) : χ.TrivOn F := by
  classical
  have h0 : ∀ v, v ∉ T → ∀ k, χ.resFin v k = 1 := fun v hvT k => by
    rw [resFin_eq, Finset.prod_congr rfl (g := fun P => χ.val P ^ ordF v k) fun P hP => by
      have e := mem_aboveF.1 hP
      rw [GlobalTheory.HeckeProduct.locK_unr χ (hu P (e ▸ hvT)), hr, e], Finset.prod_zpow, hv v hvT, one_zpow]
  have h1 : ∀ k : Fˣ, ∏ v ∈ T, χ.resFin v k = 1 := fun k => by
    let T' := T ∪ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
    have hS : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ T'.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ T' := fun P => by
      simp [Finset.mem_biUnion, mem_aboveF, -Finset.mem_union]
    have h := GlobalTheory.HeckeProduct.productRule χ (T'.biUnion (aboveF (L := E) F))
      (fun P hP => hu P fun hm => hP ((hS P).2 (Finset.mem_union_left _ hm))) (upF F k)
    have hi : χ.inf (upF F k) = 1 := by
      show χ.1 (infDiag _) = 1
      rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
      exact Finset.prod_eq_one fun w _ => hinf w _
    have hf : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ T'.biUnion (aboveF (L := E) F)),
        χ.val P ^ ordF P (upF F k)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun P => ?_
      by_cases hP : P ∈ T'.biUnion (aboveF (L := E) F)
      · exact finprod_eq_if.trans (if_neg (not_not.2 hP))
      rw [finprod_eq_if, if_pos hP]
      have : ordF (P.under (𝓞 F)) k = 0 := by
        by_contra hne
        exact hP ((hS P).2 (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hne)))
      rw [hr, this, zpow_zero]
    rw [hi, hf, one_mul, mul_one, Finset.prod_biUnion (fun v _ v' _ hne => Finset.disjoint_left.2 fun P h1 h2 =>
      hne ((mem_aboveF.1 h1).symm.trans (mem_aboveF.1 h2)))] at h
    rw [← h]
    simp only [← resFin_eq]
    exact Finset.prod_subset Finset.subset_union_left fun v _ hvT => h0 v hvT k
  have h2 : ∀ v (x y : Fˣ), v.valuation F ((y : F) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation F (x : F) →
      χ.resFin v y = χ.resFin v x := fun v x y hxy => by
    rw [resFin_eq, resFin_eq]
    refine Finset.prod_congr rfl fun P hP => locK_eq_of_tame χ (htame P) _ _ ?_
    change P.valuation E (algebraMap F E y - algebraMap F E x) ≤ _ * P.valuation E (algebraMap F E x)
    rw [← map_sub, valuation_up hr, valuation_up hr, mem_aboveF.1 hP]
    exact hxy
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · by_cases hvT : v ∈ T
    swap
    · exact h0 v hvT k
    have key : ∀ (a : 𝓞 F) (ha : (a : F) ≠ 0), χ.resFin v (Units.mk0 (a : F) ha) = 1 := by
      intro a ha
      have ha' : a ≠ 0 := fun h => ha (by simp [h])
      obtain ⟨y, hy⟩ := exists_approx T (fun u => if u = v then a else 1)
        (fun u => by split_ifs; exacts [ha', one_ne_zero])
      have hP := hy v hvT
      simp only [if_true] at hP
      have hy0 : (y : F) ≠ 0 := by
        intro h0
        rw [h0, zero_sub, Valuation.map_neg] at hP
        have hpos : 0 < v.valuation F (a : F) := zero_lt_iff.2 (by simpa using ha')
        have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
        rw [one_mul] at this
        exact absurd hP (not_le.2 this)
      rw [← h2 v (Units.mk0 (a : F) ha) (Units.mk0 (y : F) hy0) hP, ← h1 (Units.mk0 (y : F) hy0)]
      symm
      refine Finset.prod_eq_single_of_mem v hvT fun u hu hne => ?_
      have h3 := hy u hu
      simp only [if_neg hne] at h3
      rw [h2 u 1 _ (by simpa using h3), map_one]
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (k : F)
    have hb0 : (b : F) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
    have ha0 : (a : F) ≠ 0 := by
      intro h
      apply k.ne_zero
      rw [← hab]
      change (a : F) / _ = 0
      rw [h, zero_div]
    have hx : k = Units.mk0 (a : F) ha0 * (Units.mk0 (b : F) hb0)⁻¹ := by
      apply Units.ext
      rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
    rw [hx, map_mul, map_inv, key, key, inv_one, mul_one]
  · rw [HChar.resInf, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun w' _ => hinf w' _

end Adelic

section Galois

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field Ω] [Algebra E Ω]

theorem normV_eq (v : HeightOneSpectrum (𝓞 E)) : normV v = Ideal.absNorm v.asIdeal := rfl

theorem normV_inert (h2 : Module.finrank F E = 2)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    {P : HeightOneSpectrum (𝓞 E)} (hP : ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → P' = P) :
    normV P = normV (P.under (𝓞 F)) ^ 2 := by
  set v := P.under (𝓞 F) with hv
  have := P.isPrime
  have := v.isMaximal
  have : P.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have h := HeightOneSpectrum.valuation_liesOver E v P π
    rw [valuation_up hr, ← hv, hπ, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
    simpa using h
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E v.ne_bot
  have hset : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = {P.asIdeal} := by
    ext Q
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset v.ne_bot, Finset.mem_singleton]
    constructor
    · rintro ⟨hQ, hl⟩
      exact congrArg HeightOneSpectrum.asIdeal
        (hP ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩ (HeightOneSpectrum.ext hl.over.symm))
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  rw [hset, Finset.sum_singleton, he, one_mul, h2] at hs
  rw [normV_eq, normV_eq, ← hs]
  exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot

theorem not_forall_pow_sub_mem {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hq : normV P = q ^ 2) :
    ¬ ∀ x : 𝓞 E, x ^ q - x ∈ P.asIdeal := by
  intro h
  classical
  have := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have hc : Fintype.card (𝓞 E ⧸ P.asIdeal) = q ^ 2 := by rw [← hq, ← Nat.card_eq_fintype_card]; rfl
  have h1 : 1 < q := by
    have : 1 < q ^ 2 := hc ▸ Fintype.one_lt_card
    exact (Nat.one_lt_pow_iff two_ne_zero).1 this
  have h3 := Polynomial.card_le_degree_of_subset_roots
    (p := (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 E ⧸ P.asIdeal))) (Z := Finset.univ) (fun z _ => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ h1)]
      simpa using Ideal.Quotient.eq_zero_iff_mem.2 (h x))
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, Finset.card_univ, hc] at h3
  nlinarith

theorem valuation_pow_sub_pow_lt (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1)
    (h : A.valuation (a - b) < 1) (q : ℕ) : A.valuation (a ^ q - b ^ q) < 1 := by
  rw [A.valuation_le_one_iff] at ha hb
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : A) ⟨b, hb⟩ q
  have e : a ^ q - b ^ q = (a - b) * c := congrArg Subtype.val hc
  rw [e, map_mul]
  exact (mul_le_of_le_one_right' (A.valuation_le_one c)).trans_lt h

theorem exists_frob_inert [IsAlgClosure E Ω] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hinv : ∀ x, c (c x) = x)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (cc : Ω ≃+* Ω) (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hcc2 : ∀ x, cc (cc x) = x)
    {P : HeightOneSpectrum (𝓞 E)} (hP : ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → P' = P)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A P) :
    ∃ g g' : G E Ω, (∀ x, g' x = cc (g (cc.symm x))) ∧ IsFrob (F := E) A (normV P) (g * g') := by
  letI : Algebra F Ω := ((algebraMap E Ω).comp (algebraMap F E)).toAlgebra
  haveI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have : IsGalois F E := inferInstance
  have hall : ∀ σ : E ≃ₐ[F] E, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hne).symm)
  have hAv : IsPlaceOver A (P.under (𝓞 F)) := fun x => hA (algebraMap (𝓞 F) (𝓞 E) x)
  obtain ⟨τ, hτ⟩ := exists_isFrob hAv
  have hq := normV_inert h2 hr hP
  set q := normV (P.under (𝓞 F))
  have hτd : τ ∈ Dec (F := F) A := hτ.1
  have hres : ∀ x : E, τ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormal τ E x) := fun x =>
    (AlgEquiv.restrictNormal_commutes τ E x).symm
  rcases hall (AlgEquiv.restrictNormal τ E) with h | h
  · exfalso
    refine not_forall_pow_sub_mem hq fun x => (hA _).1 ?_
    have hx : A.valuation (algebraMap E Ω (x : E)) ≤ 1 := by
      exact Valuation.Integers.mem_of_integral (Valuation.valuationSubring.integers A.valuation)
        (((RingOfIntegers.isIntegral_coe x).map (algebraMap E Ω).toIntAlgHom).tower_top)
    have h1 := hτ.2 _ hx
    rw [hres, h, ← Valuation.map_neg, neg_sub] at h1
    simpa using h1
  · have hs : ∀ x, cc.symm x = cc x := fun x => by rw [RingEquiv.symm_apply_eq, hcc2]
    let g : G E Ω := { cc.trans (τ : Ω ≃+* Ω) with
      commutes' := fun x => by
        show τ (cc (algebraMap E Ω x)) = _
        rw [hcc, hres, h, hinv] }
    let g' : G E Ω := { (τ : Ω ≃+* Ω).trans cc with
      commutes' := fun x => by
        show cc (τ (algebraMap E Ω x)) = _
        rw [hres, h, hcc, hinv] }
    have e : ∀ x, (g * g') x = τ (τ x) := fun x => by
      show τ (cc (cc (τ x))) = _
      rw [hcc2]
    refine ⟨g, g', fun x => ?_, ?_, fun x hx => ?_⟩
    · show cc (τ x) = cc (τ (cc (cc.symm x)))
      rw [cc.apply_symm_apply]
    · show g * g' ∈ Dec (F := E) A
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
      obtain ⟨z, rfl⟩ := (g * g').surjective x
      have h1 : ((g * g')⁻¹ : G E Ω) ((g * g') z) = z := (g * g').symm_apply_apply z
      rw [h1, e, apply_mem_iff_of_mem_Dec hτd, apply_mem_iff_of_mem_Dec hτd]
    · have hx' : A.valuation (τ x) ≤ 1 := by
        rw [A.valuation_le_one_iff] at hx ⊢
        exact (apply_mem_iff_of_mem_Dec hτd x).2 hx
      have e2 : (g * g') x - x ^ normV P = (τ (τ x) - τ x ^ q) + (τ x ^ q - (x ^ q) ^ q) := by
        rw [e, hq, sq, pow_mul]; ring
      rw [e2]
      exact Valuation.map_add_lt _ (hτ.2 _ hx')
        (valuation_pow_sub_pow_lt A hx' (by rw [map_pow]; exact pow_le_one' hx q) (hτ.2 x hx) q)

theorem IsHeckeOf.trivOn [IsAlgClosure E Ω] [IsTotallyComplex E] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
    (hinv : ∀ x, c (c x) = x)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (cc : Ω ≃+* Ω) (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hcc2 : ∀ x, cc (cc x) = x)
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : HChar E} (h : IsHeckeOf art r χ)
    (hanti : AntiHom cc r) {m : ℕ} (hm : 0 < m) (ho : χ.OrderDvd m) (htame : ∀ P, χ.TameAt P) : χ.TrivOn F := by
  classical
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x =>
    ⟨c x, by rw [RingEquiv.symm_apply_eq, hcc, hinv]⟩
  have hu : ∀ P : HeightOneSpectrum (𝓞 E),
      P.under (𝓞 F) ∉ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset.image (fun P => P.under (𝓞 F)) → χ.UnrAt P := by
    intro P hP
    by_contra hn
    exact hP (Finset.mem_image.2 ⟨P, by simpa using hn, rfl⟩)
  refine trivOn_of_cofinite hr χ htame (locInf_eq_one hm ho) _ hu fun v hv => ?_
  rcases (aboveF (L := E) F v).eq_empty_or_nonempty with h0 | ⟨P, hP⟩
  · rw [h0, Finset.prod_empty]
  obtain rfl := mem_aboveF.1 hP
  obtain ⟨P', hP'⟩ := (existsUnique_conjPl c.toRingEquiv P).exists
  have hs : aboveF (L := E) F (P.under (𝓞 F)) = {P, P'} := by
    ext Q
    rw [mem_aboveF, under_eq_iff_conjPl c h2 hne P Q, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h' => (existsUnique_conjPl _ P).unique h' hP', ?_⟩
    rintro rfl
    exact hP'
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω P
  by_cases e : P = P'
  · subst e
    rw [Finset.pair_eq_singleton] at hs
    obtain ⟨g, g', hg, hσ⟩ := exists_frob_inert c h2 hne hinv hr cc hcc hcc2
      (fun Q hQ => Finset.mem_singleton.1 (hs ▸ mem_aboveF.2 hQ)) hA
    rw [hs, Finset.prod_singleton, h.val_eq ha (hu P hv) hA hσ, map_mul, hanti g g' hg, mul_inv_cancel, inv_one]
  · obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have hA' := isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) hcc hP' hA
    have hσ' := isFrob_conjHom cc hc hσ
    rw [← normV_conjPl hP'] at hσ'
    have hu' : χ.UnrAt P' := hu P' (by
      rwa [mem_aboveF.1 (hs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self P') : P' ∈ aboveF F (P.under (𝓞 F)))])
    rw [hs, Finset.prod_pair e, h.val_eq ha (hu P hv) hA hσ, h.val_eq ha hu' hA' hσ',
      hanti σ _ (conjHom_apply cc hc σ), inv_inv, inv_mul_cancel]

end Galois

end GlobalTheory.GalToHecke

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalToHecke

namespace GlobalTheory.Mem.Top.TwChar

theorem torsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] torsionFree_field

section Roots

variable {O : Type} [CommRing O] [IsDomain O] {n : ℕ}

def rootIso [NeZero n] {ζ : O} (h : IsPrimitiveRoot ζ n) : rootsOfUnity n O ≃* rootsOfUnity n ℂ :=
  mulEquivOfCyclicCardEq
    (h.card_rootsOfUnity.trans (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).card_rootsOfUnity.symm)

variable {Γ : Type} [Group Γ]

def cxChar (ι : rootsOfUnity n O ≃* rootsOfUnity n ℂ) (ψ : Γ →* Oˣ) (h : ∀ g, ψ g ∈ rootsOfUnity n O) : Γ →* ℂˣ :=
  (rootsOfUnity n ℂ).subtype.comp (ι.toMonoidHom.comp (ψ.codRestrict _ h))

variable (ι : rootsOfUnity n O ≃* rootsOfUnity n ℂ) (ψ : Γ →* Oˣ) (h : ∀ g, ψ g ∈ rootsOfUnity n O)

omit [IsDomain O] in
theorem cxChar_apply (g : Γ) : cxChar ι ψ h g = (ι ⟨ψ g, h g⟩ : ℂˣ) := rfl

omit [IsDomain O] in
theorem cxChar_eq_one (g : Γ) : cxChar ι ψ h g = 1 ↔ ψ g = 1 := by
  rw [cxChar_apply, OneMemClass.coe_eq_one, map_eq_one_iff _ ι.injective, Subtype.ext_iff]
  rfl

omit [IsDomain O] in
theorem cxChar_pow (g : Γ) : cxChar ι ψ h g ^ n = 1 := (ι ⟨ψ g, h g⟩).2

theorem exists_exponent [NeZero n] {ζ : O} (hζ : IsPrimitiveRoot ζ n) {L M : Type} [Field L] [Field M] (ε : L →+* ℂ)
    (hL : ∀ z : ℂ, z ^ n = 1 → ∃ x, ε x = z) (e : L →+* M) (j : O →+* M) (hj : Function.Injective j) :
    ∃ a : ℕ, a.Coprime n ∧ ∀ (u : rootsOfUnity n O) (x : L), ε x = ((ι u : ℂˣ) : ℂ) → e x = j (((u : Oˣ) ^ a : Oˣ) : O) := by
  let u0 : rootsOfUnity n O := hζ.toRootsOfUnity
  have h0 : IsPrimitiveRoot u0 n := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
    exact hζ
  have h1 : IsPrimitiveRoot (((ι u0 : rootsOfUnity n ℂ) : ℂˣ) : ℂ) n := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff]
    exact h0.map_of_injective ι.injective
  obtain ⟨x0, hx0⟩ := hL _ h1.pow_eq_one
  have h2 : IsPrimitiveRoot (e x0) n := (IsPrimitiveRoot.of_map_of_injective (hx0 ▸ h1) ε.injective).map_of_injective e.injective
  have h3 : IsPrimitiveRoot (j ζ) n := hζ.map_of_injective hj
  obtain ⟨a, -, ha⟩ := h3.eq_pow_of_pow_eq_one h2.pow_eq_one
  refine ⟨a, (h3.pow_iff_coprime (NeZero.pos n) a).1 (ha ▸ h2), fun u x hx => ?_⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ((u : Oˣ) : O)) (by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one])
  have hu : u = u0 ^ b := Subtype.ext (Units.ext hb.symm)
  have hx' : x = x0 ^ b := ε.injective (by rw [hx, map_pow, hx0, hu, map_pow]; rfl)
  rw [hx', map_pow, ← ha, Units.val_pow_eq_pow_val, ← hb, map_pow, map_pow, ← pow_mul, ← pow_mul, mul_comm]

end Roots

theorem not_mem_sq_of_ramificationIdx {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (he : v.asIdeal.ramificationIdx ℤ = 1) :
    ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := v.isPrime
  have : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal hb] at he
  intro h
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

theorem isPsi_of_isHeckeOf {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]
    {cc : Ω ≃+* Ω} (hcc : IsCMConjOm H.E Ω cc) {art : Ideles H.E →* Gab H.E Ω} (ha : IsGlobalArtin art)
    {r : G H.E Ω →* ℂˣ} {χ : HChar H.E} (h : IsHeckeOf art r χ) {l k : ℕ} (hl : l.Prime) {Q : Finset (PlE H)} {S : Set ℕ}
    (hanti : AntiHom cc r) (hord : ∀ g, r g ^ l ^ k = 1) (hram : RamExactly r (↑Q : Set (PlE H)))
    (hdec : ∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, r σ = 1)
    (hQ : ∀ P ∈ Q, IsSplitPl H P ∧ P.asIdeal.inertiaDeg ℤ = 1 ∧ eWL H.E P = 1)
    (hS : ∀ P ∈ Q, ∀ p ∈ S, p.Prime → P ∉ placesOver H.E p) :
    IsPsi (H := H) l Q χ ∧ χ.OrderDvd (l ^ k) ∧ Chr.IsTwist H S χ := by
  have ho := h.orderDvd hord
  have hatl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1 := fun v hv x =>
    let ⟨A, hA⟩ := exists_isPlaceOver Ω v
    h.loc_eq_one ha hA (hdec v hv A hA) x
  have htame : ∀ v, χ.TameAt v := fun v => by
    by_cases hv : OverP H l v
    · exact fun x _ _ => hatl v hv x
    · exact tameAt_of_orderDvd hl ho hv
  have hunr : ∀ v, χ.UnrAt v ↔ v ∉ Q := fun v => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    rw [h.unr_iff ha hA, ← Finset.mem_coe, ← hram v A hA]
    push Not
    rfl
  have htriv : χ.TrivOn H.F := by
    obtain ⟨c, hc1, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
    obtain ⟨j, hj⟩ := hcc.1
    have h1 : ∀ x : H.E, cc (algebraMap H.E Ω x) = algebraMap H.E Ω (c x) := fun x => by
      apply j.injective
      rw [hj, hc1]
      exact (H.conjE_apply (j.comp (algebraMap H.E Ω)) x).symm
    have h2 : ∀ x, cc (cc x) = x := fun x => j.injective (by rw [hj, hj, Complex.conj_conj])
    have := hcm.cplx
    exact h.trivOn c hcm.rank hcm.ne (fun x => (algebraMap H.E Ω).injective (by rw [← h1, ← h1, h2])) hr cc h1 h2 ha hanti
      (pow_pos hl.pos k) ho htame
  refine ⟨⟨⟨k, ho⟩, htriv, htame, hunr, hatl, fun v hv => (hQ v hv).1⟩, ho, ⟨_, pow_pos hl.pos k, ho⟩, htriv, htame,
    fun v hv => ?_⟩
  have hvQ : v ∈ Q := by_contra fun hn => hv ((hunr v).2 hn)
  obtain ⟨h1, h2, h3⟩ := hQ v hvQ
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 h2
  exact ⟨h1, hp, not_mem_sq_of_ramificationIdx hp v (Ideal.absNorm_mem _) h3,
    fun hm => hS v hvQ _ hm hp (Ideal.absNorm_mem _)⟩

section Pick

variable {D : D7} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {A Q : Finset (PlE D.host)} {k : ℕ}
  {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ}

abbrev RootIso (D : D7) (i : D.ntw.Tw) (k : ℕ) : Type :=
  rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k) ≃* rootsOfUnity (D.ntw.l i ^ k) ℂ

def rootIsoAt (D : D7) (i : D.ntw.Tw) (k : ℕ) : RootIso D i k :=
  haveI : NeZero (D.ntw.l i ^ k) := ⟨pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero⟩
  rootIso (D.ntw.zk_prim i k)

theorem pick_mem (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (g : G D.host.E D.nd.Om) :
    ψ.comp (D.ntw.art i Q) g ∈ rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k) :=
  (Subgroup.zpowers_le.2 (Units.ext (D.ntw.zk_prim i k).pow_eq_one)) (h.2.2.2.2.2.1 g)

def pickGal (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) : G D.host.E D.nd.Om →* ℂˣ :=
  cxChar ι (ψ.comp (D.ntw.art i Q)) (pick_mem h)

theorem isOpen_ker_pickGal (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) :
    IsOpen ((pickGal h ι).ker : Set (G D.host.E D.nd.Om)) := by
  convert h.2.2.2.1 using 1
  ext g
  exact cxChar_eq_one _ _ _ g

def pickChar (ha : IsGlobalArtin art) (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) : HChar D.host.E :=
  heckeOf ha (pickGal h ι) (isOpen_ker_pickGal h ι)

def ReadsPick (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ι : RootIso D i k) (χ : HChar D.host.E) : Prop :=
  ∀ (x : Ideles D.host.E) (σ : G D.host.E D.nd.Om), art x = toAb D.host.E D.nd.Om σ →
    ∃ u : rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k), (u : (D.ntw.Ok i k)ˣ) = ψ (D.ntw.art i Q σ) ∧ χ.1 x = ι u

def FrobPick (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ι : RootIso D i k) (χ : HChar D.host.E) : Prop :=
  ∀ v, v ∉ Q → ∀ A' : ValuationSubring D.nd.Om, IsPlaceOver A' v → ∀ σ : G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) A' (normV v) σ →
    ∃ u : rootsOfUnity (D.ntw.l i ^ k) (D.ntw.Ok i k), (u : (D.ntw.Ok i k)ˣ) = ψ (D.ntw.art i Q σ) ∧
      χ.val v = ((ι u : rootsOfUnity (D.ntw.l i ^ k) ℂ) : ℂˣ)⁻¹

theorem pickChar_spec (ha : IsGlobalArtin art) (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) (ι : RootIso D i k) {S : Set ℕ}
    (hS : ∀ p ∈ S, p.Prime → placesOver D.host.E p ⊆ ↑A) :
    ReadsPick art i Q k ψ ι (pickChar ha h ι) ∧ FrobPick i Q k ψ ι (pickChar ha h ι) ∧
      IsPsi (H := D.host) (D.ntw.l i) Q (pickChar ha h ι) ∧ (pickChar ha h ι).OrderDvd (D.ntw.l i ^ k) ∧
      Chr.IsTwist D.host S (pickChar ha h ι) := by
  classical
  have hH := isHeckeOf_heckeOf ha (pickGal h ι) (isOpen_ker_pickGal h ι)
  have key := isPsi_of_isHeckeOf (S := S) (Q := Q) (k := k) D.ntw.cc_cm ha hH (D.ntw.lPrime i).out
    (fun g g' hg => by
      rw [eq_inv_iff_mul_eq_one, ← map_mul, pickGal, cxChar_eq_one, map_mul, h.2.2.2.2.1 g g' hg, inv_mul_cancel])
    (cxChar_pow _ _ _)
    (fun v A' hA' => by
      rw [← h.2.2.2.2.2.2.1 v A' hA']
      exact exists_congr fun σ => and_congr Iff.rfl (not_congr (cxChar_eq_one _ _ _ σ)))
    (fun v hv A' hA' σ hσ => (cxChar_eq_one _ _ _ σ).2 (h.2.2.2.2.2.2.2 v hv A' hA' σ hσ)) h.1
    (fun P hP p hp hp' hm => Finset.disjoint_left.1 h.2.1 hP (by
      simp only [Finset.mem_union]
      exact Or.inr (hS p hp hp' hm)))
  exact ⟨fun x σ e => ⟨⟨_, pick_mem h σ⟩, rfl, hH x σ e⟩,
    fun v hv A' hA' σ hσ => ⟨⟨_, pick_mem h σ⟩, rfl, hH.val_eq ha ((key.1.ram v).2 hv) hA' hσ⟩, key⟩

theorem pick_not_over (h : BlochKatoReduction.Gen.PsiOk i A Q k ψ) {v : PlE D.host} (hv : v ∈ Q) :
    v ∉ placesOver D.host.E (D.ntw.l i) ∧ v ∉ A := by
  classical
  have := Finset.disjoint_left.1 h.2.1 hv
  simp only [Finset.mem_union, not_or] at this
  exact ⟨fun hm => this.1 (D.ntw.twistExcludedPlaces_contains_residueChar i hm), this.2⟩

end Pick

section Enlarge

variable {B B' : Base}

def incl (h : Enl B B') : B.LL →+* B'.LL :=
  (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
    (B.embLL.codRestrict B'.embLL.fieldRange fun x => h.2.2.2 ⟨x, rfl⟩)

theorem embLL_incl (h : Enl B B') (x : B.LL) : B'.embLL (incl h x) = B.embLL x :=
  congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, h.2.2.2 ⟨x, rfl⟩⟩)

theorem incl_star (h : Enl B B') (x : B.LL) : incl h (star x) = star (incl h x) :=
  B'.embLL.injective (by rw [B'.starLL_cx, embLL_incl, embLL_incl, B.starLL_cx])

def plUnder (h : Enl B B') (w : B'.places.Pl) : B.places.Pl where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingHom (incl h)) (w : HeightOneSpectrum (𝓞 B'.LL)).asIdeal
  isPrime := haveI := (w : HeightOneSpectrum (𝓞 B'.LL)).isPrime; Ideal.comap_isPrime _ _
  ne_bot := fun e => by
    have h1 : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) ∈
        Ideal.comap (RingOfIntegers.mapRingHom (incl h)) (w : HeightOneSpectrum (𝓞 B'.LL)).asIdeal := by
      rw [Ideal.mem_comap, map_natCast]
      exact Examples₂.PlacesToy.resCharW_mem w
    rw [e, Ideal.mem_bot] at h1
    exact (Examples₂.PlacesToy.resCharW_prime w).ne_zero (by exact_mod_cast h1)

theorem mem_plUnder (h : Enl B B') (w : B'.places.Pl) (x : 𝓞 B.LL) :
    x ∈ HeightOneSpectrum.asIdeal (plUnder h w) ↔ RingOfIntegers.mapRingHom (incl h) x ∈ HeightOneSpectrum.asIdeal w := Iff.rfl

theorem resChar_plUnder (h : Enl B B') (w : B'.places.Pl) : B.places.resChar (plUnder h w) = B'.places.resChar w :=
  Examples₂.PlacesToy.prime_mem_unique (plUnder h w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) (by rw [mem_plUnder, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)

theorem plUnder_conj (h : Enl B B') (w : B'.places.Pl) : plUnder h (B'.places.conj w) = B.places.conj (plUnder h w) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have h1 := Examples₂.PlacesToy.mem_conjW_pow (K := B'.LL) w (RingOfIntegers.mapRingHom (incl h) x) 1
  have h2 := Examples₂.PlacesToy.mem_conjW_pow (K := B.LL) (plUnder h w) x 1
  simp only [pow_one] at h1 h2
  have e : RingOfIntegers.mapRingHom (incl h) (Examples₂.PlacesToy.starO x) =
      Examples₂.PlacesToy.starO (RingOfIntegers.mapRingHom (incl h) x) := RingOfIntegers.ext (incl_star h x)
  exact h1.trans (by rw [← e]; exact h2.symm)

theorem plUnder_surjective (h : Enl B B') : Function.Surjective (plUnder h) := fun v => by
  letI : Algebra B.LL B'.LL := (incl h).toAlgebra
  have := (v : HeightOneSpectrum (𝓞 B.LL)).isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver (v : HeightOneSpectrum (𝓞 B.LL)).asIdeal (S := 𝓞 B'.LL)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot (v : HeightOneSpectrum (𝓞 B.LL)).ne_bot Q⟩,
    HeightOneSpectrum.ext hl.over.symm⟩

def tr {P P' : Pre} (e : P' = P) (F : Pre → Type) (x : F P) : F P' := cast (congrArg F e.symm) x

theorem tr_heq {P P' : Pre} (e : P' = P) (F : Pre → Type) (x : F P) : HEq (tr e F x) x := cast_heq _ _

def TwProp (P : Pre) (l k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 P.host.E))) (χ : HChar P.host.E) : Prop :=
  IsPsi (H := P.host) l Q χ ∧ χ.OrderDvd (l ^ k) ∧ Chr.IsTwist P.host (offSet P) χ ∧ ∀ v ∈ Q, ((l : ℕ) : 𝓞 P.host.E) ∉ v.asIdeal

theorem TwProp.tr {P P' : Pre} (e : P' = P) {l k : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 P.host.E))} {χ : HChar P.host.E}
    (h : TwProp P l k Q χ) :
    TwProp P' l k (tr e (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) Q) (tr e (fun P => HChar P.host.E) χ) := by
  subst e
  exact h

theorem twProp (T : TwDat B) (w : B.places.Pl) : TwProp B.toPre (B.places.resChar w) (T.k w) (T.Q w) (T.psi w) :=
  ⟨T.psi_is w, T.psi_ord w, T.psi_tw w, T.Q_l w⟩

theorem tr_one {P P' : Pre} (e : P' = P) : tr e (fun P => HChar P.host.E) 1 = 1 := by
  subst e
  rfl

def pull (h : Enl B B') (T : TwDat B) : TwDat B' where
  pl := T.pl
  Q w := tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) (T.Q (plUnder h w))
  k w := T.k (plUnder h w)
  psi w := tr h.1 (fun P => HChar P.host.E) (T.psi (plUnder h w))
  psi_is w := resChar_plUnder h w ▸ ((twProp T (plUnder h w)).tr h.1).1
  psi_ord w := resChar_plUnder h w ▸ ((twProp T (plUnder h w)).tr h.1).2.1
  psi_tw w := ((twProp T (plUnder h w)).tr h.1).2.2.1
  Q_l w := resChar_plUnder h w ▸ ((twProp T (plUnder h w)).tr h.1).2.2.2
  off w hw := by
    obtain ⟨h1, h2⟩ := T.off (plUnder h w) (by rwa [resChar_plUnder])
    exact ⟨by rw [h1, tr_one], h2⟩
  conj w := by
    rw [plUnder_conj, (T.conj _).1, (T.conj _).2]
    exact ⟨rfl, rfl⟩

theorem set_pull (h : Enl B B') (T : TwDat B) (f : Fr B.toPre) :
    HEq ((pull h T).set (tr h.1 Fr f)) (T.set f) := by
  have key : ∀ (P : Pre) (e : P = B.toPre) (a : B'.places.Pl → HChar P.host.E),
      (∀ w, a w = (if B'.places.resChar w = P.host.pde then (tr e Fr f).del' else (tr e Fr f).del) *
        tr e (fun P => HChar P.host.E) (T.psi (plUnder h w))) →
      HEq ({1, (tr e Fr f).del, (tr e Fr f).del'} ∪ Set.range a : Set (HChar P.host.E)) (T.set f) := by
    intro P e a ha
    subst e
    have : a = T.xiTw f ∘ plUnder h := funext fun w => by
      rw [ha, ← resChar_plUnder h]
      rfl
    rw [this, (plUnder_surjective h).range_comp]
    rfl
  exact key B'.toPre h.1 _ fun _ => rfl

theorem avoids_pull (h : Enl B B') {T : TwDat B} {Av : ℕ → Finset ℕ} (hA : T.Avoids Av) : (pull h T).Avoids Av := by
  have key : ∀ (P : Pre) (e : P = B.toPre) (Q : Finset (HeightOneSpectrum (𝓞 B.host.E))) (s : Finset ℕ),
      (∀ v ∈ Q, Ideal.absNorm v.asIdeal ∉ s) →
      ∀ v ∈ tr e (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) Q, Ideal.absNorm v.asIdeal ∉ s := by
    intro P e Q s hs
    subst e
    exact hs
  intro w
  rw [← resChar_plUnder h]
  exact key _ h.1 _ _ (hA (plUnder h w))

theorem exists_enl_roots (T : TwDat B) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, Enl B B' ∧ (∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z) ∧
      ∀ (w : B.places.Pl) (z : ℂ), z ^ B.places.resChar w ^ T.k w = 1 → ∃ x : B'.LL, B'.embLL x = z := by
  classical
  have hpos : ∀ w, 0 < B.places.resChar w ^ T.k w := fun w => pow_pos (B.places.resChar_prime w).pos _
  obtain ⟨B', h, hS'⟩ := BaseEnl.exists_enl B (S ∪ (TwFin.finite_pl B T.pl).toFinset.biUnion fun w =>
    Polynomial.nthRootsFinset (B.places.resChar w ^ T.k w) (1 : ℂ)) (by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · exact hS z hz
      · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 hz
        rw [Polynomial.mem_nthRootsFinset (hpos w)] at hw
        exact IsAlgebraic.of_pow (hpos w) (hw ▸ isAlgebraic_one))
  refine ⟨B', h, fun z hz => hS' z (Finset.mem_union_left _ hz), fun w z hz => ?_⟩
  by_cases hw : B.places.resChar w ∈ T.pl
  · exact hS' z (Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨w, (Set.Finite.mem_toFinset _).2 hw, (Polynomial.mem_nthRootsFinset (hpos w) _).2 hz⟩))
  · rw [(T.off w hw).2, pow_zero, pow_one] at hz
    exact ⟨1, by rw [map_one, hz]⟩

end Enlarge

section Data

def ofFamily (B : Base) (pl : Finset ℕ) {I : Type} (s : B.places.Pl → I) (Q : I → Finset (HeightOneSpectrum (𝓞 B.host.E)))
    (k : I → ℕ) (χ : I → HChar B.host.E)
    (h : ∀ w, B.places.resChar w ∈ pl → TwProp B.toPre (B.places.resChar w) (k (s w)) (Q (s w)) (χ (s w)))
    (hs : ∀ w, B.places.resChar w ∈ pl → s (B.places.conj w) = s w) : TwDat B where
  pl := pl
  Q w := if B.places.resChar w ∈ pl then Q (s w) else ∅
  k w := if B.places.resChar w ∈ pl then k (s w) else 0
  psi w := if B.places.resChar w ∈ pl then χ (s w) else 1
  psi_is w := by
    split_ifs with hw
    exacts [(h w hw).1, isPsi_one _]
  psi_ord w := by
    split_ifs with hw
    exacts [(h w hw).2.1, one_pow _]
  psi_tw w := by
    split_ifs with hw
    exacts [(h w hw).2.2.1, Chr.isTwist_one _ _]
  Q_l w := by
    split_ifs with hw
    exacts [(h w hw).2.2.2, fun _ h => absurd h (Finset.notMem_empty _)]
  off w hw := ⟨if_neg hw, if_neg hw⟩
  conj w := by
    rw [TwFin.resChar_conj]
    split_ifs with hw
    exacts [by rw [hs w hw]; exact ⟨rfl, rfl⟩, ⟨rfl, rfl⟩]

open Classical in

def avoidPlaces (P : Pre) (s : Finset ℕ) : Finset (HeightOneSpectrum (𝓞 P.host.E)) :=
  (((finite_offSet P).union s.finite_toSet).inter_of_left {p | p.Prime}).toFinset.attach.biUnion fun p =>
    (placesOver_finite_av P.host.E p.1 (((Set.Finite.mem_toFinset _).1 p.2).2.ne_zero)).toFinset

theorem subset_avoidPlaces (P : Pre) (s : Finset ℕ) {p : ℕ} (h : p ∈ offSet P ∨ p ∈ s) (hp : p.Prime) :
    placesOver P.host.E p ⊆ ↑(avoidPlaces P s) := fun v hv => by
  classical
  rw [Finset.mem_coe, avoidPlaces, Finset.mem_biUnion]
  exact ⟨⟨p, (Set.Finite.mem_toFinset _).2 ⟨h, hp⟩⟩, Finset.mem_attach _ _, (Set.Finite.mem_toFinset _).2 hv⟩

end Data

open Classical in

def settingChar {D : D7} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} (ha : IsGlobalArtin art)
    (A Q : D.ntw.Tw → Finset (PlE D.host)) (k : D.ntw.Tw → ℕ) (ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ)
    (ι : ∀ i, RootIso D i (k i)) (i : D.ntw.Tw) : HChar D.host.E :=
  if h : BlochKatoReduction.Gen.PsiOk i (A i) (Q i) (k i) (ψ i) then pickChar ha h (ι i) else 1

open Classical in

def ofFamilyOn (B : Base) (pl : Finset ℕ) (Wt : Set B.places.Pl) (hsub : ∀ w ∈ Wt, B.places.resChar w ∈ pl)
    (hc : ∀ w, B.places.conj w ∈ Wt ↔ w ∈ Wt) {I : Type} (s : B.places.Pl → I)
    (Q : I → Finset (HeightOneSpectrum (𝓞 B.host.E))) (k : I → ℕ) (χ : I → HChar B.host.E)
    (h : ∀ w ∈ Wt, TwProp B.toPre (B.places.resChar w) (k (s w)) (Q (s w)) (χ (s w)))
    (hs : ∀ w ∈ Wt, s (B.places.conj w) = s w) : TwDat B where
  pl := pl
  Q w := if w ∈ Wt then Q (s w) else ∅
  k w := if w ∈ Wt then k (s w) else 0
  psi w := if w ∈ Wt then χ (s w) else 1
  psi_is w := by
    split_ifs with hw
    exacts [(h w hw).1, isPsi_one _]
  psi_ord w := by
    split_ifs with hw
    exacts [(h w hw).2.1, one_pow _]
  psi_tw w := by
    split_ifs with hw
    exacts [(h w hw).2.2.1, Chr.isTwist_one _ _]
  Q_l w := by
    split_ifs with hw
    exacts [(h w hw).2.2.2, fun _ h => absurd h (Finset.notMem_empty _)]
  off w hw := ⟨if_neg fun h => hw (hsub w h), if_neg fun h => hw (hsub w h)⟩
  conj w := by
    by_cases hw : w ∈ Wt
    · have hw' := (hc w).2 hw
      simp only [if_pos hw, if_pos hw', hs w hw, and_self]
    · have hw' := mt (hc w).1 hw
      simp only [if_neg hw, if_neg hw', and_self]

theorem exists_twDat_stagesOn (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (Wt : Set X.B.places.Pl)
    (hsub : ∀ w ∈ Wt, X.B.places.resChar w ∈ pl) (hc : ∀ w, X.B.places.conj w ∈ Wt ↔ w ∈ Wt)
    (s : X.B.places.Pl → X.toD7.ntw.Tw)
    (hl : ∀ w, X.toD7.ntw.l (s w) = X.B.places.resChar w)
    (hs : ∀ w ∈ Wt, s (X.B.places.conj w) = s w)
    (art : Ideles X.toD7.host.E →* Gab X.toD7.host.E X.toD7.nd.Om) (ha : IsGlobalArtin art)
    (A Q : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (k : X.toD7.ntw.Tw → ℕ)
    (ψ : ∀ i, X.toD7.ntw.RCG i (Q i) →* (X.toD7.ntw.Ok i (k i))ˣ) (ι : ∀ i, RootIso X.toD7 i (k i)) (Av : ℕ → Finset ℕ)
    (hA : ∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i))
    (hψ : ∀ w ∈ Wt, BlochKatoReduction.Gen.PsiOk (s w) (A (s w)) (Q (s w)) (k (s w)) (ψ (s w))) :
    (∀ i, BlochKatoReduction.Gen.PsiOk i (A i) (Q i) (k i) (ψ i) →
      ReadsPick art i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      FrobPick i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      IsPsi (H := X.toD7.host) (X.toD7.ntw.l i) (Q i) (settingChar ha A Q k ψ ι i) ∧
      (settingChar ha A Q k ψ ι i).OrderDvd (X.toD7.ntw.l i ^ k i) ∧
      Chr.IsTwist X.toD7.host (offSet X.B.toPre) (settingChar ha A Q k ψ ι i)) ∧
    ∃ T₁ : TwDat X.B, T₁.pl = pl ∧ T₁.Avoids Av ∧
      (∀ w ∈ Wt, T₁.psi w = settingChar ha A Q k ψ ι (s w) ∧ T₁.Q w = Q (s w) ∧ T₁.k w = k (s w)) ∧
      (∀ w, w ∉ Wt → T₁.psi w = 1 ∧ T₁.Q w = ∅ ∧ T₁.k w = 0) ∧
      ∀ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) → ∃ (B' : Base) (h : Enl X.B B'), (∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z) ∧
        (∀ (w : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar w ^ (pull h T₁).k w = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
        HEq ((pull h T₁).set (tr h.1 Fr f)) (T₁.set f) := by
  classical
  have h1 : ∀ i, BlochKatoReduction.Gen.PsiOk i (A i) (Q i) (k i) (ψ i) →
      ReadsPick art i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      FrobPick i (Q i) (k i) (ψ i) (ι i) (settingChar ha A Q k ψ ι i) ∧
      IsPsi (H := X.toD7.host) (X.toD7.ntw.l i) (Q i) (settingChar ha A Q k ψ ι i) ∧
      (settingChar ha A Q k ψ ι i).OrderDvd (X.toD7.ntw.l i ^ k i) ∧
      Chr.IsTwist X.toD7.host (offSet X.B.toPre) (settingChar ha A Q k ψ ι i) := fun i hi => by
    rw [settingChar, dif_pos hi]
    exact pickChar_spec ha hi (ι i) fun p hp => hA i p (Or.inl hp)
  have h2 : ∀ w ∈ Wt,
      TwProp X.B.toPre (X.B.places.resChar w) (k (s w)) (Q (s w)) (settingChar ha A Q k ψ ι (s w)) := fun w hw => by
    obtain ⟨-, -, a, b, c⟩ := h1 _ (hψ w hw)
    rw [← hl w]
    exact ⟨a, b, c, fun v hv => (pick_not_over (hψ w hw) hv).1⟩
  refine ⟨h1, ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs, rfl, fun w v hv hm => ?_,
    fun w hw => ⟨if_pos hw, if_pos hw, if_pos hw⟩, fun w hw => ⟨if_neg hw, if_neg hw, if_neg hw⟩, fun S hS => ?_⟩
  · by_cases hw : w ∈ Wt
    · have hv' : v ∈ Q (s w) :=
        (if_pos hw : (ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs).Q w = _) ▸ hv
      have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified X.toD7.host.E).1 v).2 ((hψ w hw).1 v hv').2.1
      exact (pick_not_over (hψ w hw) hv').2 (hA (s w) _ (Or.inr (hl w ▸ hm)) hp (Ideal.absNorm_mem _))
    · exact Finset.notMem_empty v
        ((if_neg hw : (ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs).Q w = _) ▸ hv)
  · obtain ⟨B', h, a, b⟩ := exists_enl_roots (ofFamilyOn X.B pl Wt hsub hc s Q k (settingChar ha A Q k ψ ι) h2 hs) S hS
    exact ⟨B', h, a, fun w z hz => b (plUnder h w) z (by rwa [resChar_plUnder]), set_pull h _ f⟩

end GlobalTheory.Mem.Top.TwChar

end
end

section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

def SatU {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) : Prop :=
  T = TwDat.untw B T.pl → ∀ v v', OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt

section Slot

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

def Org (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) {D : D7} (Wt : Set B.places.Pl) (nch : NChoice D) : Prop :=
  ∃ (P : Pre2 K w) (x : St P) (l : LC hL x), (ListSt cDep x ∧ SatU P) ∧ Wt = P.Wt ∧ Kept l.c.ch nch

def NEo : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEl hL cDep K B f T w Z Wt p0 t nch n xd c ×
  PLift (Org hL cDep K w Wt nch)

def NEog : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEo hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SFino : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), (ListSt cDep x ∧ SatU P) →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEo hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNo : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEo hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEog hL cDep) S Γ).s K B f T w

end Slot

def ExistsUnlocalizedSaturatedState : Prop := StepW Start fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), SatU P ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure SameGal (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  pl : HEq D.naut.plGw D'.naut.plGw

structure Carried (D D' : D7) : Prop where
  exp : SameExport D D'
  emb : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (x : D.LL0) (x' : D'.LL0),
    D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      HEq (D.ntw.emb0 i x) (D'.ntw.emb0 i' x') ∧ HEq (D.ntw.emb0b i x) (D'.ntw.emb0b i' x')

theorem SameGal.refl (D : D7) : SameGal D D := ⟨(SameExport.refl D).gal, HEq.rfl⟩

theorem Carried.refl (D : D7) : Carried D D := ⟨SameExport.refl D, fun i i' h x x' e => by
  obtain rfl := eq_of_heq h
  obtain rfl : x = x' := Subtype.ext (D.what₂.embLL.injective e)
  exact ⟨HEq.rfl, HEq.rfl⟩⟩

structure Seed (D : D7) (A : D.ntw.Tw → Finset (PlE D.host)) where
  s : D.what₂.places.Pl → D.ntw.Tw
  reads : ∀ v, ∃ b, ReadsAt (s v) b v
  conj : ∀ v, s (D.what₂.places.conj v) = s v
  same : ∀ v v', TwistedAt D v → TwistedAt D v' → OverOne D v v' → s v' = s v
  xd : ThData D
  all : XdAll xd
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)
  Q : D.ntw.Tw → Finset (PlE D.host)
  k : D.ntw.Tw → ℕ
  ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ
  good : ∀ v, TwistedAt D v → TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (s v) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (s v)) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 (s v) (twEps D (s v)) (S (s v)) (A (s v)) (Q (s v)) (k (s v)) (ψ (s v) ^ a)
  sep : ∀ v v', TwistedAt D v → TwistedAt D v' → s v ≠ s v' → Disjoint (Q (s v)) (Q (s v'))

def Seed.pack {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) (v : D.what₂.places.Pl) : TwPack D :=
  ⟨σ.s v, σ.Q (σ.s v), σ.k (σ.s v), σ.ψ (σ.s v)⟩

def TwFrom (X : Stages) {A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)} (σ : Seed X.toD7 A) {B' : Base} (h : Enl X.B B')
    (T' : TwDat B') : Prop :=
  (∀ (v' : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar v' ^ T'.k v' = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
  ∀ v' : B'.places.Pl,
    (TwistedAt X.toD7 (plUnder h v') →
      HEq (T'.Q v') (σ.Q (σ.s (plUnder h v'))) ∧ T'.k v' = σ.k (σ.s (plUnder h v')) ∧
      ∃ (ι : RootIso X.toD7 (σ.s (plUnder h v')) (σ.k (σ.s (plUnder h v')))) (χ : HChar X.toD7.host.E),
        FrobPick (σ.s (plUnder h v')) _ _ (σ.ψ (σ.s (plUnder h v'))) ι χ ∧ HEq (T'.psi v') χ) ∧
    (¬ TwistedAt X.toD7 (plUnder h v') → T'.psi v' = 1)

def BareK : Prop := StepW Start fun K B' f' _ w' => ∀ (P' : Pre2 K w') (X : Stages) (f : Fr X.B.toPre), B'.toPre = X.B.toPre →
  HEq f' f → GrpTrue X.N f → ∃ x' : St P', IsEmpty x'.o.N.nd.Loc ∧ SameGal X.toD7 (Dof x')

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

def SAk : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (LA hL x') ∧ SameGal (Dof x) (Dof x')

def SCk : Prop := AllSt fun _ B _ T _ _ x => ∀ (l : StrictHenselianAcyclic hL x) (s : B.places.Pl → (Dof x).ntw.Tw),
  (∀ v, ∃ b, ReadsAt (D := Dof x) (s v) b v) → (∀ v, s (B.places.conj v) = s v) →
  ∃ c : StC l.mt l.b T.k T.psi, c.ch.twI = s

def MvB : Prop := StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (P : Pre2 K w) (x : St P), StrictHenselianAcyclic hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', LI hL x' → SameGal (Dof x) (Dof x') →
    ∃ x'' : St P', Nonempty (StrictHenselianAcyclic hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x''

end GlobalTheory.HeightCounting.Up

end
end
