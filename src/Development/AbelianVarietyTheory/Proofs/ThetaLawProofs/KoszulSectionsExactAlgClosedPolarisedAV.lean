import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsRegularOfFnOfRingKrullDimQuotientAddLe
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularLocalRingAndRingKrullDimEqOfPolAV
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLeNatCastNeZero

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory

private theorem gs_id_eq_germ (X : Scheme.{0}) (V : X.Opens) (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = X.presheaf.germ V y hy a := by
  rw [gs_eq (𝟙 X) y V hy a]
  rfl

theorem mem_span_of_forall_germ_mem_span : ∀ (X : Scheme.{0}) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (r : Γ(X, V)), IsAffineOpen V → (∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i))) → r ∈ Ideal.span (Set.range f) := by
  intro X V J f r hV h
  rw [hV.mem_ideal_iff]
  intro y hy
  rw [Ideal.map_span, ← Set.range_comp]
  by_cases hz : ∀ i, y ∉ X.basicOpen (f i)
  · have hr := h y hy hz
    simp only [gs_id_eq_germ X V y hy] at hr
    exact hr
  · simp only [not_forall, not_not] at hz
    obtain ⟨i, hi⟩ := hz
    rw [X.mem_basicOpen (f i) y hy] at hi
    have hmem : X.presheaf.germ V y hy (f i) ∈ Ideal.span (Set.range (⇑(X.presheaf.germ V y hy).hom ∘ f)) :=
      Ideal.subset_span ⟨i, rfl⟩
    rw [Ideal.eq_top_of_isUnit_mem _ hmem hi]
    trivial

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.GermInterp

theorem isMaximal_of_finite_primes {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) (Q : Ideal R) (hQ : Q.IsPrime) (hI : I ≤ Q) :
    Q.IsMaximal := by
  have hT : {J : Ideal R | Q ≤ J ∧ J.IsMaximal}.Finite := by
    refine (hfin.image PrimeSpectrum.asIdeal).subset ?_
    rintro J ⟨hQJ, hJ⟩
    exact ⟨⟨J, hJ.isPrime⟩, le_trans hI hQJ, rfl⟩
  have hJac : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  have hinf : hT.toFinset.inf id ≤ Q := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact hJac.le
  obtain ⟨M, hM, hMQ⟩ := hQ.inf_le'.1 hinf
  rw [Set.Finite.mem_toFinset] at hM
  rw [show Q = M from le_antisymm hM.1 hMQ]
  exact hM.2

theorem eq_of_comap_map_le {R : Type*} [CommRing R] (I : Ideal R)
    (hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal) (P : Ideal R) [hP : P.IsPrime] (hI : I ≤ P)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P] (M : Ideal R) (hM : M.IsMaximal)
    (h : (I.map (algebraMap R S)).comap (algebraMap R S) ≤ M) : M = P := by
  by_contra hne
  have hMP : ¬ M ≤ P := fun hle => hne (hM.eq_of_le hP.ne_top hle)
  obtain ⟨m, hmM, hmP⟩ := Set.not_subset.1 hMP
  have hmeet : ¬ Disjoint (I : Set R) (↑(M.primeCompl ⊔ Submonoid.powers m) : Set R) := by
    intro hdis
    obtain ⟨Q, hQ, hIQ, hQdis⟩ := Ideal.exists_le_prime_disjoint I _ hdis
    have hQM : Q ≤ M := by
      intro x hx
      by_contra hxM
      exact Set.disjoint_left.1 hQdis hx
        (Submonoid.mem_sup_left (show x ∈ M.primeCompl from hxM))
    have hmQ : m ∉ Q := fun hm =>
      Set.disjoint_left.1 hQdis hm (Submonoid.mem_sup_right (Submonoid.mem_powers m))
    exact hmQ (((hmax Q hQ hIQ).eq_of_le hM.ne_top hQM) ▸ hmM)
  obtain ⟨w, hwI, hwW⟩ := Set.not_disjoint_iff.1 hmeet
  obtain ⟨v, hv, u, hu, rfl⟩ := Submonoid.mem_sup.1 hwW
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hu
  have hunit : IsUnit (algebraMap R S (m ^ k)) :=
    IsLocalization.map_units S (⟨m ^ k, fun h => hmP (hP.mem_of_pow_mem k h)⟩ : P.primeCompl)
  have hvmap : v ∈ (I.map (algebraMap R S)).comap (algebraMap R S) := by
    rw [Ideal.mem_comap]
    have hw := Ideal.mem_map_of_mem (algebraMap R S) hwI
    rw [map_mul] at hw
    exact (Ideal.mul_unit_mem_iff_mem _ hunit).1 hw
  exact hv (h hvmap)

theorem exists_sub_mem_map {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) {κ : Type*} [Finite κ] (P : κ → PrimeSpectrum R)
    (hinj : Function.Injective P) (hI : ∀ i, I ≤ (P i).asIdeal) (S : κ → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalization.AtPrime (S i) (P i).asIdeal] (a : ∀ i, S i) :
    ∃ r : R, ∀ i, algebraMap R (S i) r - a i ∈ I.map (algebraMap R (S i)) := by
  have hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal :=
    fun Q hQ hIQ => isMaximal_of_finite_primes I hfin Q hQ hIQ
  let N : κ → Ideal R := fun i => (I.map (algebraMap R (S i))).comap (algebraMap R (S i))
  have key : ∀ i (M : Ideal R), M.IsMaximal → N i ≤ M → M = (P i).asIdeal :=
    fun i M hM hle => eq_of_comap_map_le I hmax (P i).asIdeal (hI i) (S i) M hM hle
  have hcop : Pairwise fun i j => IsCoprime (N i) (N j) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have e1 := key i M hM (le_trans le_sup_left hle)
    have e2 := key j M hM (le_trans le_sup_right hle)
    exact hij (hinj (PrimeSpectrum.ext (e1.symm.trans e2)))
  have hfrac : ∀ i, ∃ x : R, ∃ s : (P i).asIdeal.primeCompl, IsLocalization.mk' (S i) x s = a i := by
    intro i
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.mk'_surjective (P i).asIdeal.primeCompl (a i)
    exact ⟨x, s, h⟩
  choose x s hxs using hfrac
  have hinv : ∀ i, ∃ t : R, (s i : R) * t - 1 ∈ N i := by
    intro i
    have hsup : N i ⊔ Ideal.span {(s i : R)} = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      have e := key i M hM (le_trans le_sup_left hle)
      have hsM : (s i : R) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [e] at hsM
      exact (s i).2 hsM
    have h1 : (1 : R) ∈ N i ⊔ Ideal.span {(s i : R)} := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine ⟨t, ?_⟩
    have e : (s i : R) * t - 1 = -y := by rw [← hyz]; ring
    rw [e]
    exact (N i).neg_mem hy
  choose t ht using hinv
  obtain ⟨z, hz⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun i => Ideal.Quotient.mk (N i) (x i * t i))
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨r, fun i => ?_⟩
  have hri : r - x i * t i ∈ N i := by
    have e := congrFun hz i
    rw [Ideal.quotientInfToPiQuotient_mk'] at e
    exact Ideal.Quotient.eq.1 e
  have h1 : algebraMap R (S i) r - algebraMap R (S i) (x i * t i) ∈ I.map (algebraMap R (S i)) := by
    rw [← map_sub]
    exact Ideal.mem_comap.1 hri
  have h2 : algebraMap R (S i) (x i * t i) - a i ∈ I.map (algebraMap R (S i)) := by
    rw [← hxs i]
    have hst : algebraMap R (S i) ((s i : R) * t i - 1) ∈ I.map (algebraMap R (S i)) :=
      Ideal.mem_comap.1 (ht i)
    have hspec := IsLocalization.mk'_spec (S i) (x i) (s i)
    have e : algebraMap R (S i) (x i * t i) - IsLocalization.mk' (S i) (x i) (s i) =
        IsLocalization.mk' (S i) (x i) (s i) * algebraMap R (S i) ((s i : R) * t i - 1) := by
      simp only [map_sub, map_mul, map_one]
      linear_combination (-(algebraMap R (S i) (t i))) * hspec
    rw [e]
    exact Ideal.mul_mem_left _ _ hst
  convert Ideal.add_mem _ h1 h2 using 1
  ring

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (y : X) (hy : y ∈ V)
    (g : Γ(X, V)) : g ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal ↔ y ∉ X.basicOpen g := by
  have h1 : hV.primeIdealOf ⟨y, hy⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g ↔ y ∈ X.basicOpen g := by
    show hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen g ↔ _
    rw [hV.fromSpec_primeIdealOf]
  rw [hV.fromSpec_preimage_basicOpen] at h1
  constructor
  · intro hg hyb
    exact (h1.2 hyb) hg
  · intro hyb
    by_contra hg
    exact hyb (h1.1 hg)

theorem exists_germ_sub_mem : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (a : ∀ y : X, X.presheaf.stalk y), LocallyOfFiniteType p → IsAffineOpen V → Set.Finite {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)} → ∃ r : Γ(X, V), ∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i)) := by
  intro K _ X p V J f a hft hV hfin
  let I : Ideal Γ(X, V) := Ideal.span (Set.range f)
  let Z := {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)}
  have : Finite Z := hfin.to_subtype
  let P : Z → PrimeSpectrum Γ(X, V) := fun k => hV.primeIdealOf ⟨k.1, k.2.1⟩
  have hIP : ∀ k, I ≤ (P k).asIdeal := by
    intro k
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_primeIdealOf_iff hV k.1 k.2.1 (f i)).2 (k.2.2 i)
  have hinj : Function.Injective P := by
    intro k k' e
    apply Subtype.ext
    have e1 := hV.fromSpec_primeIdealOf ⟨k.1, k.2.1⟩
    have e2 := hV.fromSpec_primeIdealOf ⟨k'.1, k'.2.1⟩
    have e3 : hV.primeIdealOf ⟨k.1, k.2.1⟩ = hV.primeIdealOf ⟨k'.1, k'.2.1⟩ := e
    rw [e3] at e1
    exact e1.symm.trans e2
  have hfinR : {Q : PrimeSpectrum Γ(X, V) | I ≤ Q.asIdeal}.Finite := by
    refine (Set.finite_range P).subset ?_
    intro Q hQ
    have hyV : hV.fromSpec Q ∈ V := hV.range_fromSpec.le ⟨Q, rfl⟩
    have hQeq : hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩ = Q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec Q, hyV⟩)
    refine ⟨⟨hV.fromSpec Q, hyV, fun i => ?_⟩, hQeq⟩
    have hfi : f i ∈ (hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩).asIdeal := by
      rw [hQeq]
      exact hQ (Ideal.subset_span ⟨i, rfl⟩)
    exact (mem_primeIdealOf_iff hV _ hyV (f i)).1 hfi
  have : IsJacobsonRing Γ(Sp K, ⊤) :=
    isJacobsonRing_of_surjective ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom,
      RingEquiv.surjective _⟩
  have : IsJacobsonRing Γ(X, V) :=
    RingHom.FiniteType.isJacobsonRing
      (Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp K)) hV (by intro x _; simp))
  letI alg : ∀ k : Z, Algebra Γ(X, V) (X.presheaf.stalk k.1) :=
    fun k => TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨k.1, k.2.1⟩
  have loc : ∀ k : Z, IsLocalization.AtPrime (X.presheaf.stalk k.1) (P k).asIdeal :=
    fun k => hV.isLocalization_stalk ⟨k.1, k.2.1⟩
  obtain ⟨r, hr⟩ := exists_sub_mem_map I hfinR P hinj hIP (fun k => X.presheaf.stalk k.1) (fun k => a k.1)
  refine ⟨r, fun y hy hz => ?_⟩
  let k : Z := ⟨y, hy, hz⟩
  have hgs : ∀ g : Γ(X, V), gs (𝟙 X) y V g = algebraMap Γ(X, V) (X.presheaf.stalk k.1) g := by
    intro g
    rw [gs_eq (𝟙 X) y V hy g]
    rfl
  have hk := hr k
  rw [Ideal.map_span, ← Set.range_comp] at hk
  have e : (fun i => gs (𝟙 X) y V (f i)) = (algebraMap Γ(X, V) (X.presheaf.stalk k.1)) ∘ f := by
    funext i
    exact hgs (f i)
  rw [e, hgs r]
  exact hk

end GlobalTheory.GermInterp
end

section
section
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.KosGr

section Abstract
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]

def dd (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (r : ℕ) (c : Finset (Fin g) → ∀ j, V j)
    (I : Finset (Fin g)) (j : ℕ) : V j :=
  ∑ i : Fin g, if i.val < r ∧ i ∉ I then
    (-1 : K) ^ (I.filter (· < i)).card • x i j (c (insert i I) (j + 1)) else 0

theorem dd_congr (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (r : ℕ) (c c' : Finset (Fin g) → ∀ j, V j)
    (I : Finset (Fin g)) (j : ℕ)
    (h : ∀ i : Fin g, i.val < r → i ∉ I → c (insert i I) (j + 1) = c' (insert i I) (j + 1)) :
    dd x r c I j = dd x r c' I j := by
  unfold dd
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h i hi.1 hi.2]
  · rfl

theorem dd_succ (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (t : Fin g) (c : Finset (Fin g) → ∀ j, V j)
    (I : Finset (Fin g)) (hI : ∀ k ∈ I, k.val < t.val) (j : ℕ) :
    dd x (t.val + 1) c I j
      = dd x t.val c I j + (-1 : K) ^ I.card • x t j (c (insert t I) (j + 1)) := by
  have htI : t ∉ I := fun h => lt_irrefl _ (hI t h)
  have hfil : I.filter (· < t) = I := Finset.filter_true_of_mem fun k hk => hI k hk
  unfold dd
  rw [show (-1 : K) ^ I.card • x t j (c (insert t I) (j + 1)) = ∑ i : Fin g,
      if i = t then (-1 : K) ^ (I.filter (· < i)).card • x i j (c (insert i I) (j + 1)) else 0 by
    rw [Finset.sum_ite_eq' Finset.univ t, if_pos (Finset.mem_univ t), hfil]]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : i = t
  · subst h1
    simp [htI]
  · have h2 : i.val < t.val + 1 ↔ i.val < t.val :=
      ⟨fun h => lt_of_le_of_ne (Nat.lt_succ_iff.mp h) (fun e => h1 (Fin.ext e)), Nat.lt_succ_of_lt⟩
    simp only [h2, h1, if_false, add_zero]

theorem dd_succ_insert (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (t : Fin g)
    (c : Finset (Fin g) → ∀ j, V j) (I : Finset (Fin g)) (j : ℕ) :
    dd x (t.val + 1) c (insert t I) j = dd x t.val (fun J => c (insert t J)) I j := by
  unfold dd
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hit : i.val < t.val
  · have hne : i ≠ t := fun h => by rw [h] at hit; exact lt_irrefl _ hit
    have hf : (insert t I).filter (· < i) = I.filter (· < i) := by
      rw [Finset.filter_insert, if_neg (fun h : t < i => absurd (lt_trans hit h) (lt_irrefl _))]
    have hmem : i ∉ insert t I ↔ i ∉ I := by simp [hne]
    rw [hf, Finset.insert_comm i t]
    simp only [hmem, Nat.lt_succ_of_lt hit, hit, true_and]
  · have h1 : ¬ (i.val < t.val + 1 ∧ i ∉ insert t I) := by
      rintro ⟨h, hi⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact hit h
      · exact hi (Finset.mem_insert.mpr (Or.inl (Fin.ext h)))
    rw [if_neg h1, if_neg (fun h => hit h.1)]

theorem exists_sum_of_mem_iSup {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module K A]
    [Module K B] (f : Fin g → A →ₗ[K] B) (t : Fin g) (y : B)
    (hy : y ∈ ⨆ (i : Fin g) (_ : i < t), LinearMap.range (f i)) :
    ∃ z : Fin g → A, y = ∑ i : Fin g, if i.val < t.val then f i (z i) else 0 := by
  refine Submodule.iSup_induction (fun i => ⨆ (_ : i < t), LinearMap.range (f i))
    (motive := fun y => ∃ z : Fin g → A, y = ∑ i : Fin g, if i.val < t.val then f i (z i) else 0)
    hy ?_ ?_ ?_
  · intro i y hy
    by_cases hi : i < t
    · rw [iSup_pos hi] at hy
      obtain ⟨a, rfl⟩ := hy
      refine ⟨Pi.single i a, ?_⟩
      rw [Finset.sum_eq_single i]
      · rw [if_pos (Fin.lt_def.mp hi), Pi.single_eq_same]
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk, map_zero, ite_self]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [iSup_neg hi, Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · exact ⟨0, by simp⟩
  · rintro y₁ y₂ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩
    refine ⟨z₁ + z₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

theorem card_le_of_lt (I : Finset (Fin g)) (r : ℕ) (hI : ∀ k ∈ I, k.val < r) : I.card ≤ r := by
  calc I.card = (I.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range r).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (hI k hk)
    _ = r := Finset.card_range r

theorem exact_dd (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j)
    (hc : ∀ i i' j (y : V (j + 2)), j + 2 ≤ g → x i j (x i' (j + 1) y) = x i' j (x i (j + 1) y))
    (hr : ∀ (i : Fin g) (j : ℕ) (y : V (j + 1)), j + 1 + i ≤ g →
      x i j y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' j)) →
      y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' (j + 1)))
    (r : ℕ) : ∀ (j₀ : ℕ), j₀ + r ≤ g → ∀ c : Finset (Fin g) → ∀ j, V j,
      (∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ j, j = j₀ + I.card → dd x r c I j = 0) →
      ∃ w : Finset (Fin g) → ∀ j, V j, ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → I ≠ ∅ →
        ∀ j, j = j₀ + I.card → c I j = dd x r w I j := by
  induction r with
  | zero =>
    intro j₀ _ c _
    refine ⟨c, fun I hI hne j _ => ?_⟩
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact absurd (hI k hk) (Nat.not_lt_zero _)
  | succ r ih =>
    intro j₀ hj₀ c hcyc
    obtain ⟨t, htv⟩ : ∃ t : Fin g, t.val = r := ⟨⟨r, by omega⟩, rfl⟩
    have hsub : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ k ∈ I, k.val < r + 1 :=
      fun I hI k hk => Nat.lt_succ_of_lt (hI k hk)
    have hlt : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ k ∈ I, k.val < t.val := by
      intro I hI k hk; rw [htv]; exact hI k hk
    have htI : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → t ∉ I := by
      intro I hI h
      have := hI t h
      rw [htv] at this
      exact lt_irrefl _ this
    have hins : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ k ∈ insert t I, k.val < r + 1 := by
      intro I hI k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [htv]; exact Nat.lt_succ_self r
      · exact Nat.lt_succ_of_lt (hI k hk)
    have hC2 : ∀ J : Finset (Fin g), (∀ k ∈ J, k.val < r) → ∀ j, j = (j₀ + 1) + J.card →
        dd x r (fun J => c (insert t J)) J j = 0 := by
      intro J hJ j hj
      have h1 := hcyc (insert t J) (hins J hJ) j
        (by rw [Finset.card_insert_of_notMem (htI J hJ)]; omega)
      have e := dd_succ_insert x t c J j
      rw [htv] at e
      rw [e] at h1
      exact h1
    obtain ⟨u, hu⟩ := ih (j₀ + 1) (by omega) (fun J => c (insert t J)) hC2
    have h0 := hcyc ∅ (by simp) j₀ (by simp)
    have e0 := dd_succ x t c ∅ (by simp) j₀
    rw [htv, h0] at e0
    have hmem : x t j₀ (c (insert t ∅) (j₀ + 1)) ∈
        ⨆ (i' : Fin g) (_ : i' < t), LinearMap.range (x i' j₀) := by
      have hsum : dd x r c ∅ j₀ ∈ ⨆ (i' : Fin g) (_ : i' < t), LinearMap.range (x i' j₀) := by
        unfold dd
        refine Submodule.sum_mem _ fun i _ => ?_
        split_ifs with hi
        · refine Submodule.smul_mem _ _ ?_
          have hit : i < t := Fin.lt_def.mpr (by rw [htv]; exact hi.1)
          exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hit (LinearMap.mem_range_self _ _))
        · exact Submodule.zero_mem _
      have e1 : x t j₀ (c (insert t ∅) (j₀ + 1)) = -dd x r c ∅ j₀ := by
        rw [Finset.card_empty, pow_zero, one_smul] at e0
        exact eq_neg_of_add_eq_zero_right e0.symm
      rw [e1]
      exact Submodule.neg_mem _ hsum
    have hy := hr t j₀ (c (insert t ∅) (j₀ + 1)) (by rw [htv]; omega) hmem
    obtain ⟨z, hz⟩ := exists_sum_of_mem_iSup (fun i => x i (j₀ + 1)) t _ hy
    let w₁ : Finset (Fin g) → ∀ j, V j := fun J =>
      if J.card = 1 then Function.update (0 : ∀ j, V j) (j₀ + 1 + 1) (∑ i, if J = {i} then z i else 0)
      else u J
    have hw₁ : ∀ J : Finset (Fin g), (∀ k ∈ J, k.val < r) → ∀ j, j = j₀ + 1 + J.card →
        c (insert t J) j = dd x r w₁ J j := by
      intro J hJ j hj
      rcases J.eq_empty_or_nonempty with rfl | hne
      · rw [Finset.card_empty, add_zero] at hj
        subst hj
        rw [hz]
        unfold dd
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i.val < r
        · rw [if_pos (by rw [htv]; exact hi), if_pos ⟨hi, Finset.notMem_empty i⟩]
          simp [w₁]
        · rw [if_neg (by rw [htv]; exact hi), if_neg (fun h => hi h.1)]
      · rw [dd_congr x r w₁ u J j (fun i hi hiJ => ?_)]
        · exact hu J hJ hne.ne_empty j hj
        · have hc1 : (insert i J).card ≠ 1 := by
            rw [Finset.card_insert_of_notMem hiJ]
            have := hne.card_pos
            omega
          simp only [w₁, if_neg hc1]
    let d : Finset (Fin g) → ∀ j, V j := fun I j => c I j - (-1 : K) ^ I.card • x t j (w₁ I (j + 1))
    have hdcyc : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ j, j = j₀ + I.card →
        dd x r d I j = 0 := by
      intro I hI j hj
      have hcI := hcyc I (hsub I hI) j hj
      have e := dd_succ x t c I (hlt I hI) j
      rw [htv, hcI] at e
      have hcw := hw₁ I hI (j + 1) (by rw [hj]; ring)
      rw [hcw] at e
      rw [e]
      unfold dd
      rw [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · have hcard : (insert i I).card ≤ r := card_le_of_lt (insert i I) r (by
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact hi.1
          · exact hI k hk)
        rw [Finset.card_insert_of_notMem hi.2] at hcard
        simp only [d, map_sub, map_smul, Finset.card_insert_of_notMem hi.2]
        rw [hc i t j _ (by omega), pow_succ]
        module
      · simp
    obtain ⟨w₀, hw₀⟩ := ih j₀ (by omega) d hdcyc
    refine ⟨fun I => if t ∈ I then w₁ (I.erase t) else w₀ I, ?_⟩
    intro I hI hne j hj
    by_cases htI' : t ∈ I
    · obtain ⟨J, htJ, rfl⟩ : ∃ J, t ∉ J ∧ I = insert t J :=
        ⟨I.erase t, Finset.notMem_erase t I, (Finset.insert_erase htI').symm⟩
      have hJ : ∀ k ∈ J, k.val < r := by
        intro k hk
        have h1 := hI k (Finset.mem_insert_of_mem hk)
        have h2 : k.val ≠ r := fun h => htJ (by rwa [show k = t from Fin.ext (h.trans htv.symm)] at hk)
        omega
      have e := dd_succ_insert x t (fun I => if t ∈ I then w₁ (I.erase t) else w₀ I) J j
      rw [htv] at e
      rw [e, dd_congr x r _ w₁ J j (fun i hi hiJ => ?_)]
      · exact hw₁ J hJ j (by rw [hj, Finset.card_insert_of_notMem htJ]; ring)
      · have hti : t ∉ insert i J := by
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => ?_, htJ⟩
          rw [← h, htv] at hi
          exact lt_irrefl _ hi
        simp only [Finset.mem_insert_self, ↓reduceIte, Finset.erase_insert hti]
    · have hI' : ∀ k ∈ I, k.val < r := by
        intro k hk
        have h1 := hI k hk
        have h2 : k.val ≠ r := fun h => htI' (by rwa [show k = t from Fin.ext (h.trans htv.symm)] at hk)
        omega
      have e := dd_succ x t (fun I => if t ∈ I then w₁ (I.erase t) else w₀ I) I (hlt I hI') j
      rw [htv] at e
      rw [e, dd_congr x r _ w₀ I j (fun i hi hiI => ?_)]
      · simp only [Finset.mem_insert_self, ↓reduceIte, Finset.erase_insert htI']
        have h1 := hw₀ I hI' hne j hj
        simp only [d] at h1
        rw [← h1, sub_add_cancel]
      · have hti : t ∉ insert i I := by
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => ?_, htI'⟩
          rw [← h, htv] at hi
          exact lt_irrefl _ hi
        simp only [hti, ↓reduceIte]

end Abstract

theorem kosD_mulVec {K : Type} [CommRing K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (w : KIx g 0 N → K)
    (c : Finset (Fin g) → ∀ j, Fin (N j) → K) (h : ∀ I a, w (.inl ⟨I, a⟩) = c I I.card a)
    (I : Finset (Fin g)) (a : Fin (N I.card)) :
    (kosD m (fun _ => 0)).mulVec w (.inl ⟨I, a⟩)
      = dd (V := fun j => Fin (N j) → K) (fun i j => (m i j (j + 1)).mulVecLin) g c I I.card a := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, kosD]
  rw [Fintype.sum_sigma]
  unfold dd
  simp only [Finset.sum_apply, h, Finset.sum_mul, ite_mul, zero_mul]
  have hL : ∀ J : Finset (Fin g), (∑ b : Fin (N J.card), ∑ i : Fin g,
      if i ∉ I ∧ J = insert i I then (-1 : K) ^ (I.filter (· < i)).card * m i I.card J.card a b * c J J.card b
      else 0) = ∑ i : Fin g, if i ∉ I ∧ J = insert i I then
        (-1 : K) ^ (I.filter (· < i)).card * ∑ b : Fin (N J.card), m i I.card J.card a b * c J J.card b
      else 0 := by
    intro J
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rw [Finset.mul_sum]
      simp only [mul_assoc]
    · simp
  rw [Finset.sum_congr rfl fun J _ => hL J, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ I
  · simp [hi]
  · rw [Finset.sum_eq_single (insert i I)]
    · rw [if_pos ⟨hi, rfl⟩, if_pos ⟨i.isLt, hi⟩]
      simp only [Pi.smul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
      rw [Finset.card_insert_of_notMem hi]
    · intro J _ hJ
      rw [if_neg (fun h' => hJ h'.2)]
    · intro h'
      exact absurd (Finset.mem_univ _) h'

theorem koszul_exact_of_graded_regular : ∀ (K : Type) [CommRing K] (g : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K), (∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2)) → (∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g → (m i j (j + 1)).mulVec y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' j (j + 1)).mulVecLin) → y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' (j + 1) (j + 2)).mulVecLin) → ∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w : KIx g 0 N → K, ∀ p : (Σ I : Finset (Fin g), Fin (N I.card)), p.1 ≠ ∅ → v (.inl p) = (kosD m (fun _ => 0)).mulVec w (.inl p) := by
  intro K _ g N m hcomm hreg v hv
  let x : Fin g → ∀ j, (Fin (N (j + 1)) → K) →ₗ[K] (Fin (N j) → K) :=
    fun i j => (m i j (j + 1)).mulVecLin
  have hc : ∀ i i' j (y : Fin (N (j + 2)) → K), j + 2 ≤ g →
      x i j (x i' (j + 1) y) = x i' j (x i (j + 1) y) := by
    intro i i' j y hj
    simp only [x, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hcomm i i' j hj]
  have hr' : ∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g →
      x i j y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' j)) →
      y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' (j + 1)) :=
    fun i j y hj hy => hreg i j y hj hy
  let c : Finset (Fin g) → ∀ j, Fin (N j) → K :=
    fun I => Function.update (0 : ∀ j, Fin (N j) → K) I.card (fun a => v (.inl ⟨I, a⟩))
  have hcv : ∀ (I : Finset (Fin g)) (a : Fin (N I.card)), v (.inl ⟨I, a⟩) = c I I.card a := by
    intro I a
    simp [c]
  have hcyc : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < g) → ∀ j, j = 0 + I.card → dd x g c I j = 0 := by
    intro I _ j hj
    rw [zero_add] at hj
    subst hj
    funext a
    have h1 := kosD_mulVec m v c hcv I a
    rw [hv] at h1
    exact h1.symm
  obtain ⟨w', hw'⟩ := exact_dd x hc hr' g 0 (by simp) c hcyc
  let W : KIx g 0 N → K := fun q => Sum.elim (fun p => w' p.1 p.1.card p.2) (fun _ => 0) q
  refine ⟨W, ?_⟩
  rintro ⟨I, a⟩ hI
  rw [kosD_mulVec m W w' (fun I a => rfl) I a, hcv I a,
    hw' I (fun k _ => k.isLt) hI I.card (by rw [zero_add])]

end GlobalTheory.KeyKa.KosGr
end
end

open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular : ∀ (K : Type) [CommRing K] (g : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K), (∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2)) → (∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g → (m i j (j + 1)).mulVec y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' j (j + 1)).mulVecLin) → y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' (j + 1) (j + 2)).mulVecLin) → ∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w : KIx g 0 N → K, ∀ p : (Σ I : Finset (Fin g), Fin (N I.card)), p.1 ≠ ∅ → v (.inl p) = (kosD m (fun _ => 0)).mulVec w (.inl p) := by
  atlas_forward_decl GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]

abbrev lf (x : KeyIn K) {l : ℕ} (s : RR x l) (c : x.P.L.ι) : Γ(x.P.A.left, x.P.L.U c) := s.f c

def phi (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) (c : x.P.L.ι) :
    Γ(x.P.A.left, x.P.L.U c) := ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * lf x (b k) c

theorem phi_add (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v w : Fin N → K) (c) :
    phi x b (v + w) c = phi x b v c + phi x b w c := by
  simp only [phi, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem phi_zero (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (c) : phi x b 0 c = 0 := by
  simp only [phi, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem phi_sum (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) {A : Type} (S : Finset A)
    (v : A → Fin N → K) (c) : phi x b (∑ i ∈ S, v i) c = ∑ i ∈ S, phi x b (v i) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, phi_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phi_add, ih]

def sec (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) : RR x l where
  f := fun c => phi x b v c
  compat := fun i j => by
    obtain ⟨u, hu⟩ : ∃ u : Γ(x.P.A.left, x.P.L.U i ⊓ x.P.L.U j), u = ((pw x.P.L (l : ℤ)).g i j).val :=
      ⟨_, rfl⟩
    have h : ∀ k, rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) j) :=
      fun k => hu ▸ (b k).compat i j
    have h' : rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v j) := by
      simp only [phi, map_sum, map_mul, rs_cst, h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    subst hu
    exact h'

theorem phi_inj (x : KeyIn K) {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) {v w : Fin N → K}
    (h : ∀ c, phi x b v c = phi x b w c) : v = w :=
  (hb (sec x b v)).unique (fun _ => rfl) h

theorem phi_surj (x : KeyIn K) {l N : ℕ} {b : Fin N → RR x l} (hb : IsBasis x b) (y : RR x l) :
    ∃ v, ∀ c, lf x y c = phi x b v c := (hb y).exists

theorem phi_mulVec (x : KeyIn K) {n l : ℕ} {s : Fin x.P.g → RR x n}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m)
    (i : Fin x.P.g) {j : ℕ} (hj : j < x.P.g) (v) (c) :
    phi x (b j) ((m i j (j + 1)).mulVec v) c = lf x (s i) c * phi x (b (j + 1)) v c := by
  have h : ∀ k, lf x (s i) c * lf x (b (j + 1) k) c =
      ∑ k', cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c :=
    fun k => hm i j hj k c
  calc phi x (b j) ((m i j (j + 1)).mulVec v) c
      = ∑ k', ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) *
          (cst x.P.A.hom (x.P.L.U c) (m i j (j + 1) k' k) * lf x (b j k') c) := by
        simp only [phi, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * (lf x (s i) c * lf x (b (j + 1) k) c) := by
        rw [Finset.sum_comm]
        simp only [h, Finset.mul_sum]
    _ = _ := by
        simp only [phi, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

theorem mem_iff {g : ℕ} {a b : ℕ} (i : Fin g) (M : Fin g → Matrix (Fin a) (Fin b) K) (y : Fin a → K) :
    y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (M i').mulVecLin) ↔
      ∃ t : Fin g → Fin b → K, y = ∑ i' ∈ Finset.univ.filter (· < i), (M i').mulVec (t i') := by
  have e : (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (M i').mulVecLin) =
      ⨆ i' ∈ Finset.univ.filter (· < i), LinearMap.range (M i').mulVecLin := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e, Submodule.mem_iSup_finset_iff_exists_sum]
  constructor
  · rintro ⟨q, h⟩
    choose t ht using fun i' => (q i').2
    refine ⟨t, h.symm.trans (Finset.sum_congr rfl fun i' _ => (ht i').symm)⟩
  · rintro ⟨t, h⟩
    exact ⟨fun i' => ⟨(M i').mulVec (t i'), t i', rfl⟩, h.symm⟩

theorem koszul_exact_of_regular : ∀ (K : Type) [CommRing K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ (i : Fin x.P.g) (j : ℕ), j + 1 + i ≤ x.P.g → ∀ (y : RR x (l - (j + 1) * n)) (ta : Fin x.P.g → RR x (l - (j + 1) * n)), (∀ c, (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) * (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (ta i').f c)) → ∃ tb : Fin x.P.g → RR x (l - (j + 2) * n), ∀ c, (show Γ(x.P.A.left, x.P.L.U c) from y.f c) = ∑ i' ∈ Finset.univ.filter (· < i), (show Γ(x.P.A.left, x.P.L.U c) from (s i').f c) * (show Γ(x.P.A.left, x.P.L.U c) from (tb i').f c)) → ∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  intro K _ x n l s b m _ hb hm hreg
  refine GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular K x.P.g (fun j => (l - j * n) ^ x.P.g) m ?_ ?_
  · intro i i' j hj
    refine Matrix.ext_of_mulVec_single fun k => ?_
    refine phi_inj x (hb j (by omega)) fun c => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, phi_mulVec x hm i (by omega),
      phi_mulVec x hm i' (by omega), phi_mulVec x hm i' (by omega), phi_mulVec x hm i (by omega)]
    ring
  · intro i j y hj hy
    have hjg : j < x.P.g := by omega
    obtain ⟨t, ht⟩ := (mem_iff i (fun i' => m i' j (j + 1)) _).1 hy
    refine (mem_iff i (fun i' => m i' (j + 1) (j + 2)) _).2 ?_
    obtain ⟨tb, htb⟩ := hreg i j hj (sec x (b (j + 1)) y) (fun i' => sec x (b (j + 1)) (t i')) (fun c => by
      change lf x (s i) c * phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * phi x (b (j + 1)) (t i') c
      rw [← phi_mulVec x hm i hjg, ht, phi_sum]
      exact Finset.sum_congr rfl fun i' _ => phi_mulVec x hm i' hjg _ _)
    have htb' : ∀ c, phi x (b (j + 1)) y c =
        ∑ i' ∈ Finset.univ.filter (· < i), lf x (s i') c * lf x (tb i') c := htb
    by_cases h2 : j + 2 ≤ x.P.g
    · choose u hu using fun i' => phi_surj x (hb (j + 2) h2) (tb i')
      refine ⟨u, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', phi_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hu]
      exact (phi_mulVec x hm i' (j := j + 1) (by omega) _ _).symm
    · have he : Finset.univ.filter (· < i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun i' _ h => ?_
        have : (i' : ℕ) < i := h
        omega
      refine ⟨0, phi_inj x (hb (j + 1) (by omega)) fun c => ?_⟩
      rw [htb', he, Finset.sum_empty, Finset.sum_empty, phi_zero]

end GlobalTheory.KeyKa.KosBasis
end
end

section
open CategoryTheory GlobalTheory

namespace GlobalTheory

namespace CubeCut

variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]

def ExactMod (A : Cube.{0} I K) (J : ∀ s, Submodule K (A.obj s)) : Prop :=
  (∀ x : Cube.Term A 0, (∀ s, Cube.d A 0 x s ∈ J s.1) → ∀ s, x s ∈ J s.1) ∧
    ∀ (p : ℕ) (x : Cube.Term A (p + 1)), (∀ s, Cube.d A (p + 1) x s ∈ J s.1) →
      ∃ y : Cube.Term A p, ∀ s, (x - Cube.d A p y) s ∈ J s.1

theorem d_mem {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ {s t : Finset I} (h : s ⊆ t) (x : A.obj s), x ∈ J s → Cube.res A h x ∈ J t)
    {p : ℕ} {x : Cube.Term A p} (hx : ∀ s, x s ∈ J s.1) (t) : Cube.d A p x t ∈ J t.1 := by
  rw [Cube.d_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 : Cube.res A (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) ∈ J t.1 :=
    hJ (Finset.erase_subset i.1 t.1) _ (hx (Cube.eraseIdx t i))
  exact Submodule.smul_of_tower_mem _ _ h1

theorem exactMod_of_exact {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ s, J s = ⊥) (h : ∀ p, (cubeComplex A).ExactAt p) : ExactMod A J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · have h0 : Cube.d A 0 x = 0 := funext fun s => by simpa [hJ] using hx s
    have h1 := (cubeComplex_exactAt_zero_iff' A).1 (h 0) (h0.trans (map_zero _).symm)
    simp [h1, hJ]
  · have h0 : Cube.d A (p + 1) x = 0 := funext fun s => by simpa [hJ] using hx s
    obtain ⟨y, hy⟩ := ((cubeComplex_exactAt_succ_iff A p).1 (h (p + 1)) x).1 h0
    exact ⟨y, fun s => by simp [hy, hJ]⟩

theorem ExactMod.mem_empty {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : A.obj ∅)
    (hy : ∀ a : I, Cube.res A (Finset.empty_subset {a}) y ∈ J {a}) : y ∈ J ∅ := by
  have h1 := h.1 ((Cube.termZeroEquiv A).symm y) (fun s => by
    rw [Cube.d_zero_apply, LinearEquiv.apply_symm_apply, Cube.aug_apply]
    obtain ⟨s, hs⟩ := s
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    exact hy a) ⟨∅, rfl⟩
  simpa using h1

theorem ExactMod.exists_glue {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : ∀ a : I, A.obj {a})
    (hy : ∀ a a' : I, Cube.res A (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) -
      Cube.res A (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ J {a, a'}) :
    ∃ y₀ : A.obj ∅, ∀ a, Cube.res A (Finset.empty_subset {a}) y₀ - y a ∈ J {a} := by
  have key : ∀ i j : I, (hij : i < j) →
      Cube.d A 1 (Cube.termOneEquiv A y) ⟨{i, j}, Finset.card_pair hij.ne⟩ ∈ J {i, j} := by
    intro i j hij
    rw [Cube.d_one_apply_pair A _ hij]
    simp only [Cube.termOneEquiv_apply]
    have h1 := (J {i, j}).neg_mem (hy i j)
    rwa [neg_sub] at h1
  have hx : ∀ s, Cube.d A 1 (Cube.termOneEquiv A y) s ∈ J s.1 := by
    rintro ⟨t, ht⟩
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact key i j h'
    · revert ht
      rw [Finset.pair_comm i j]
      intro ht
      exact key j i h'
  obtain ⟨z, hz⟩ := h.2 0 (Cube.termOneEquiv A y) hx
  refine ⟨Cube.termZeroEquiv A z, fun a => ?_⟩
  have h1 := hz ⟨{a}, Finset.card_singleton a⟩
  rw [Pi.sub_apply, Cube.d_zero_apply, Cube.aug_apply, Cube.termOneEquiv_apply] at h1
  have h2 := (J {a}).neg_mem h1
  rwa [neg_sub] at h2

private theorem exists_term_d_sub_termMap_mem {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) {k : ℕ} (x : Cube.Term B k)
    (hx : ∀ s, Cube.d B k x s ∈ J s.1) :
    ∃ a₁ : Cube.Term A k, ∀ s, Cube.d B k (x - Cube.termMap φ k a₁) s ∈ JB s.1 := by
  have hx' : ∀ t : {s : Finset I // s.card = k + 1},
      ∃ a : A.obj t.1, Cube.d B k x t - (φ.app t.1).hom a ∈ JB t.1 := by
    intro t
    have h1 := hx t
    rw [hJ, Submodule.mem_sup] at h1
    obtain ⟨u, hu, _, ⟨a, rfl⟩, hua⟩ := h1
    refine ⟨a, ?_⟩
    rw [← hua, add_sub_cancel_right]
    exact hu
  choose a ha using hx'
  have hb : ∀ t, (Cube.d B k x - Cube.termMap φ (k + 1) a) t ∈ JB t.1 := fun t => by
    simpa using ha t
  have hda : ∀ u, Cube.d A (k + 1) a u ∈ JA u.1 := by
    intro u
    apply hinj u.1 (Finset.card_pos.1 (by rw [u.2]; omega))
    have h1 := congrFun (Cube.termMap_d φ (k + 1) a) u
    simp only [Cube.termMap_apply] at h1
    have h2 : (φ.app u.1).hom (Cube.d A (k + 1) a u) =
        -Cube.d B (k + 1) (Cube.d B k x - Cube.termMap φ (k + 1) a) u := by
      rw [h1, map_sub, Cube.d_d]
      simp
    rw [h2]
    exact neg_mem (d_mem hJB hb u)
  obtain ⟨a₁, ha₁⟩ := hA.2 k a hda
  refine ⟨a₁, fun s => ?_⟩
  have h1 : Cube.d B k (x - Cube.termMap φ k a₁) s =
      (Cube.d B k x - Cube.termMap φ (k + 1) a) s + (φ.app s.1).hom ((a - Cube.d A k a₁) s) := by
    rw [map_sub, ← Cube.termMap_d]
    simp only [Pi.sub_apply, Cube.termMap_apply, map_sub]
    abel
  rw [h1]
  exact add_mem (hb s) (hφ _ _ (ha₁ s))

theorem ExactMod.cut {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA) (hB : ExactMod B JB)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) : ExactMod B J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    have h1 := hB.1 _ ha₁ s
    have h2 : x s = (x - Cube.termMap φ 0 a₁) s + (φ.app s.1).hom (a₁ s) := by simp
    rw [h2, hJ]
    exact Submodule.add_mem_sup h1 (LinearMap.mem_range_self _ _)
  · obtain ⟨a₁, ha₁⟩ := exists_term_d_sub_termMap_mem φ hA hJB hφ hinj hJ x hx
    obtain ⟨y, hy⟩ := hB.2 p _ ha₁
    refine ⟨y, fun s => ?_⟩
    have h2 : (x - Cube.d B p y) s =
        (x - Cube.termMap φ (p + 1) a₁ - Cube.d B p y) s + (φ.app s.1).hom (a₁ s) := by
      simp only [Pi.sub_apply, Cube.termMap_apply]
      abel
    rw [h2, hJ]
    exact Submodule.add_mem_sup (hy s) (LinearMap.mem_range_self _ _)

section Family

variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))

abbrev imSum (k : ℕ) (s : Finset I) : Submodule K (B.obj s) :=
  ⨆ (j : Fin g) (_ : (j : ℕ) < k), LinearMap.range ((φ j).app s).hom

omit [LinearOrder I] in

theorem res_mem_imSum (k : ℕ) {s t : Finset I} (h : s ⊆ t) (x : B.obj s)
    (hx : x ∈ imSum φ k s) : Cube.res B h x ∈ imSum φ k t := by
  have key : imSum φ k s ≤ (imSum φ k t).comap (Cube.res B h) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_comap, ← Cube.app_res]
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
  exact key hx

omit [LinearOrder I] in

theorem imSum_succ (i : Fin g) (s : Finset I) :
    imSum φ (i + 1) s = imSum φ i s ⊔ LinearMap.range ((φ i).app s).hom := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    by_cases h : (j : ℕ) < i
    · exact le_sup_of_le_left (le_iSup_of_le j (le_iSup_of_le h le_rfl))
    · have hji : j = i := Fin.ext (by omega)
      subst hji
      exact le_sup_right
  · exact sup_le (iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le (by omega) le_rfl))
      (le_iSup_of_le i (le_iSup_of_le (by omega) le_rfl))

end Family

end CubeCut

open CubeCut in

theorem cube_cut_regular_sequence : ∀ (K : Type) [CommRing K] (I : Type) [LinearOrder I] [Fintype I] (g : ℕ) (n : ℤ) (C : ℤ → Cube.{0} I K) (mu : Fin g → ∀ l l', C l ⟶ C l'), 0 < n → (∀ i j l l' l'', l' = l + n → l'' = l' + n → mu i l l' ≫ mu j l' l'' = mu j l l' ≫ mu i l' l'') → (∀ (T : Finset I), T.Nonempty → ∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj T), l' = l + n → ((mu i l l').app T).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app T).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app T).hom) → (∀ l, 0 < l → ∀ p, (cubeComplex (C l)).ExactAt p) → (∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj ∅), l' = l + n → (i : ℕ) * n < l → ((mu i l l').app ∅).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app ∅).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ l : ℤ, g * n < l → (∀ y : (C l).obj ∅, (∀ a : I, Cube.res (C l) (Finset.empty_subset {a}) y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ y : ∀ a : I, (C l).obj {a}, (∀ a a' : I, Cube.res (C l) (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) - Cube.res (C l) (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a, a'}).hom) → ∃ y₀ : (C l).obj ∅, ∀ a, Cube.res (C l) (Finset.empty_subset {a}) y₀ - y a ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom := by
  intro K _ I _ _ g n C mu hn hcomm hreg hac
  have P : ∀ k : ℕ, k ≤ g → ∀ l₀ l : ℤ, l = l₀ + n → (k : ℤ) * n < l →
      CubeCut.ExactMod (C l) (fun s => CubeCut.imSum (fun j => mu j l₀ l) k s) := by
    intro k
    induction k with
    | zero =>
      intro _ l₀ l _ hlt
      refine CubeCut.exactMod_of_exact (fun s => ?_) (hac l (by simpa using hlt))
      simp [CubeCut.imSum]
    | succ k ih =>
      intro hk l₀ l hl hlt
      push_cast at hlt
      have hA := ih (by omega) (l₀ - n) l₀ (by ring) (by linarith)
      have hB := ih (by omega) l₀ l hl (by linarith)
      let i : Fin g := ⟨k, by omega⟩
      refine CubeCut.ExactMod.cut (mu i l₀ l) hA hB
        (fun h x hx => CubeCut.res_mem_imSum _ _ h x hx) ?_
        (fun s hs x hx => hreg s hs i l₀ l x hl hx)
        (fun s => CubeCut.imSum_succ (fun j => mu j l₀ l) i s)
      intro s x hx
      have key : CubeCut.imSum (fun j => mu j (l₀ - n) l₀) k s ≤
          (CubeCut.imSum (fun j => mu j l₀ l) k s).comap ((mu i l₀ l).app s).hom := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap]
        have e := congrArg (fun f => (f.app s).hom z) (hcomm j i (l₀ - n) l₀ l (by ring) hl)
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
        rw [e]
        exact Submodule.mem_iSup_of_mem j
          (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
      exact key hx
  refine ⟨fun i l l' y hl' hlt hy => ?_, fun l hlt => ?_⟩
  · have hE := P i i.2.le (l - n) l (by ring) hlt
    refine hE.mem_empty y fun a => ?_
    refine hreg {a} (Finset.singleton_nonempty a) i l l' _ hl' ?_
    rw [Cube.app_res]
    exact CubeCut.res_mem_imSum _ _ _ _ hy
  · have hE := P g le_rfl (l - n) l (by ring) hlt
    exact ⟨hE.mem_empty, hE.exists_glue⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (n r : ℕ) (s : Fin r → RR x n) (W : Set x.P.A.left), 1 ≤ n → IsClosed W → W.Nonempty → {y ∈ W | ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → topologicalKrullDim W ≤ r := by
  first | exact @GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros | exact GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros | (intros; apply GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem ringKrullDim_localization_quotient_le {R : Type} [CommRing R] {k : ℕ} (f : Fin k → R) (m : Ideal R)
    [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸
        Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range f) : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h₁ := (PrimeSpectrum.localization_comap_isInducing (R := R) (Localization.AtPrime m) m.primeCompl).comp
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk
      (Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))))
      Ideal.Quotient.mk_surjective).isInducing
  refine (h₁.codRestrict (s := PrimeSpectrum.zeroLocus (Set.range f)) fun p => ?_).topologicalKrullDim_le
  rintro _ ⟨j, rfl⟩
  change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime m) (f j)) ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j => algebraMap R (Localization.AtPrime m) (f j)) j))]
  exact p.asIdeal.zero_mem

theorem ofList_take_ofFn {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn f).take i) = Ideal.span (f '' {j | j.val < i}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, by simp only; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := j.2; omega, rfl⟩

theorem isWeaklyRegular_of_dim_zeroLocus {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (hreg : ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = g)
    (hdim : ∀ (k : ℕ) (hk : k ≤ g),
      (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) :
        Set (PrimeSpectrum R)) ≤ ((g - k : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < g := by simpa using hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro a ha
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  have ha' := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) ha
  rw [map_mul] at ha'
  by_cases hall : ∀ j : Fin g, j.val ≤ i → f j ∈ m
  · obtain ⟨h₁, h₂⟩ := hreg m
    have hk : i + 1 ≤ g := hi'
    have hd := (ringKrullDim_localization_quotient_le (fun j => f (Fin.castLE hk j)) m).trans
      (hdim (i + 1) hk ⟨⟨m, hm.isPrime⟩, by
        rintro _ ⟨j, rfl⟩
        exact hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)⟩)
    have hr := GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le (Localization.AtPrime m) g (i + 1)
      (fun j => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) h₂
      (fun j => (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).2
        (hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)))
      ((add_le_add_left hd _).trans (by
        rw [← Nat.cast_add, Nat.sub_add_cancel hk]))
    have h₃ := hr.toIsWeaklyRegular.regular_mod_prev i (by simp)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn] at h₃
    simp only [smul_eq_mul, Ideal.mul_top] at h₃
    have e : Ideal.map (algebraMap R (Localization.AtPrime m)) (Ideal.span (f '' {j | j.val < i})) =
        Ideal.span ((fun j : Fin (i + 1) => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) ''
          {j | j.val < i}) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, ⟨Fin.castLE hk j, hj, rfl⟩, rfl⟩
    rw [e] at ha' ⊢
    exact h₃ _ ha'
  · push Not at hall
    obtain ⟨j, hj, hjm⟩ := hall
    have hu : IsUnit (algebraMap R (Localization.AtPrime m) (f j)) :=
      IsLocalization.map_units _ (⟨f j, hjm⟩ : m.primeCompl)
    rcases hj.eq_or_lt with hj | hj
    · subst hj
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 ha'
    · rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem f (show j ∈ {j : Fin g | j.val < i} from hj)))) hu]
      trivial

theorem isWeaklyRegular_of_finZ : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (V : x.P.A.left.Opens) (c : x.P.L.ι) (h : V ≤ x.P.L.U c), 1 ≤ n → FinZ x s → IsAffineOpen V → RingTheory.Sequence.IsWeaklyRegular Γ(x.P.A.left, V) (List.ofFn fun i => resG x.P.A.left h ((s i).f c)) := by
  intro hL K _ _ x n s V c h hn hZ hV
  refine isWeaklyRegular_of_dim_zeroLocus _ (fun m _ => ?_) fun k hk hne => ?_
  · exact GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV K x.P Γ(x.P.A.left, V) hV.fromSpec m _ inferInstance
  · let W : Set x.P.A.left := {y | ∀ j : Fin k, y ∉ Out.nonzeroLocus (s (Fin.castLE hk j))}
    have hW : IsClosed W := by
      have : W = ⋂ j : Fin k, (Out.nonzeroLocus (s (Fin.castLE hk j)) : Set x.P.A.left)ᶜ := by
        ext y; simp [W]
      rw [this]
      exact isClosed_iInter fun j => (Out.nonzeroLocus _).isOpen.isClosed_compl
    have hmem : ∀ p : (PrimeSpectrum.zeroLocus (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))), hV.fromSpec p.1 ∈ W := by
      intro p j hj
      have hpV : hV.fromSpec p.1 ∈ V := by
        have : hV.fromSpec p.1 ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
        rwa [hV.range_fromSpec] at this
      have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff (𝟙 _) _ _ (h hpV) _).1
        ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s (Fin.castLE hk j)) (𝟙 _) (hV.fromSpec p.1) (k := c) (h hpV)).1 hj)
      have h₂ : hV.fromSpec p.1 ∈ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := by
        have := x.P.A.left.basicOpen_res (show Γ(x.P.A.left, x.P.L.U c) from (s (Fin.castLE hk j)).f c) (homOfLE h).op
        exact this.ge ⟨hpV, h₁⟩
      have h₃ : p.1 ∈ hV.fromSpec ⁻¹ᵁ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := h₂
      rw [hV.fromSpec_preimage_basicOpen] at h₃
      exact h₃ (p.2 ⟨j, rfl⟩)
    have hind : Topology.IsInducing fun p : (PrimeSpectrum.zeroLocus
        (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))) => hV.fromSpec p.1 :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    refine (hind.codRestrict hmem).topologicalKrullDim_le.trans ?_
    obtain ⟨p, hp⟩ := hne
    refine GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros hL K x n (x.P.g - k) (fun j => s ⟨k + j, by have := j.2; omega⟩) W hn hW
      ⟨_, hmem ⟨p, hp⟩⟩ (Set.Finite.subset hZ ?_)
    rintro y ⟨hy₁, hy₂⟩ i
    by_cases hi : i.val < k
    · exact hy₁ ⟨i, hi⟩
    · have := hy₂ ⟨i - k, by have := i.2; omega⟩
      simp only [show k + (i.val - k) = i.val by omega] at this
      exact this

end GlobalTheory.KeyKa
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.KosField

theorem mem_iSup_range_iff {R M N J : Type} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Fintype J] (P : J → Prop) [DecidablePred P] (φ : J → M →ₗ[R] N) (y : N) :
    y ∈ (⨆ (j : J) (_ : P j), LinearMap.range (φ j)) ↔
      ∃ t : J → M, y = ∑ j ∈ Finset.univ.filter P, φ j (t j) := by
  classical
  constructor
  · intro hy
    refine Submodule.iSup_induction (motive := fun y => ∃ t : J → M, y = ∑ j ∈ Finset.univ.filter P, φ j (t j))
      _ hy (fun j z hz => ?_) ⟨0, by simp⟩ ?_
    · by_cases hj : P j
      · rw [iSup_pos hj] at hz
        obtain ⟨w, rfl⟩ := hz
        refine ⟨Pi.single j w, ?_⟩
        rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero])
          (fun h => absurd (by simpa using hj) h), Pi.single_eq_same]
      · rw [iSup_neg hj, Submodule.mem_bot] at hz
        exact ⟨0, by simp [hz]⟩
    · rintro a b ⟨t, rfl⟩ ⟨u, rfl⟩
      exact ⟨t + u, by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨t, rfl⟩
    refine Submodule.sum_mem _ fun j hj => ?_
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (by simpa using hj) ⟨t j, rfl⟩)

theorem regular_step {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (h : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) (i : Fin g) (a : R) (r : Fin g → R)
    (e : f i * a = ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), f j * r j) :
    ∃ r' : Fin g → R, a = ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), f j * r' j := by
  have hi : (i : ℕ) < (List.ofFn f).length := by simp
  have h1 := h.regular_mod_prev i hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 : Ideal.ofList ((List.ofFn f).take i) =
      ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range (LinearMap.mulLeft R (f j)) := by
    apply le_antisymm
    · rw [Ideal.ofList, Ideal.span_le]
      intro z hz
      obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hz
      have hk' : k < g := by simp at hk; omega
      refine Submodule.mem_iSup_of_mem (⟨k, hk'⟩ : Fin g) (Submodule.mem_iSup_of_mem (by simp at hk ⊢; omega) ⟨1, ?_⟩)
      simp
    · refine iSup₂_le fun j hj => ?_
      rintro _ ⟨z, rfl⟩
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
      exact List.mem_take_iff_getElem.2 ⟨j, by simp; omega, by simp⟩
  rw [h2] at h1
  exact (mem_iSup_range_iff _ _ _).1 (h1 a ((mem_iSup_range_iff _ _ _).2 ⟨r, by simpa using e⟩))

variable {X : Scheme.{0}} {L : LB X} {n l l' : ℤ} {V W : X.Opens}

def sf (s : LB.Sec (pw L n)) (k : L.ι) : Γ(X, L.U k) := s.f k

def co (x : SecOn (pw L l) V) (k : L.ι) : Γ(X, V ⊓ L.U k) := GlobalTheory.LB.coord x k

theorem co_ext {x y : SecOn (pw L l) V} (h : ∀ k, co x k = co y k) : x = y := GlobalTheory.LB.sec_ext h

theorem co_add (x y : SecOn (pw L l) V) (k : L.ι) : co (x + y) k = co x k + co y k := rfl
theorem co_sub (x y : SecOn (pw L l) V) (k : L.ι) : co (x - y) k = co x k - co y k := rfl
theorem co_zero (k : L.ι) : co (0 : SecOn (pw L l) V) k = 0 := rfl
theorem co_restrict (h : W ≤ V) (x : SecOn (pw L l) V) (k : L.ι) :
    co (SecOn.restrict _ h x) k = rs X (inf_le_inf_right _ h) (co x k) := rfl
theorem co_ofSec (s : LB.Sec (pw L l)) (k : L.ι) :
    co (GlobalTheory.LB.ofSec s V) k = rs X inf_le_right (sf s k) := rfl
theorem co_sum {J : Type} (T : Finset J) (x : J → SecOn (pw L l) V) (k : L.ι) :
    co (∑ j ∈ T, x j) k = ∑ j ∈ T, co (x j) k := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, co_add, ih]

theorem co_compat (x : SecOn (pw L l) V) (i j : L.ι) {O : X.Opens} (hi : O ≤ V ⊓ L.U i) (hj : O ≤ V ⊓ L.U j)
    (hij : O ≤ L.U i ⊓ L.U j) :
    rs X hi (co x i) = rs X hij (L.g i j ^ l).val * rs X hj (co x j) :=
  SecOn.compat x i j hi hj hij

theorem sf_compat (s : LB.Sec (pw L n)) (i j : L.ι) {O : X.Opens} (hi : O ≤ L.U i) (hj : O ≤ L.U j)
    (hij : O ≤ L.U i ⊓ L.U j) :
    rs X hi (sf s i) = rs X hij (L.g i j ^ n).val * rs X hj (sf s j) :=
  GlobalTheory.LB.sec_rel s i j hi hj hij

def pwMk (l : ℤ) (y : ∀ k : L.ι, Γ(X, V ⊓ L.U k))
    (hy : ∀ (i j : L.ι) (O : X.Opens) (hi : O ≤ V ⊓ L.U i) (hj : O ≤ V ⊓ L.U j) (hij : O ≤ L.U i ⊓ L.U j),
      rs X hi (y i) = rs X hij (L.g i j ^ l).val * rs X hj (y j)) : SecOn (pw L l) V :=
  GlobalTheory.LB.mkSec (L := pw L l) y fun i j => hy i j _ _ _ _

theorem co_pwMk (y : ∀ k : L.ι, Γ(X, V ⊓ L.U k)) (hy) (k : L.ι) : co (pwMk l y hy) k = y k := rfl

def mulEq (s : LB.Sec (pw L n)) (h : l' = l + n) (V : X.Opens) :
    SecOn (pw L l) V →ₗ[Γ(X, V)] SecOn (pw L l') V where
  toFun x := pwMk l' (fun k => rs X inf_le_right (sf s k) * co x k) fun i j O hi hj hij => by
    rw [map_mul, map_mul, rs_rs, rs_rs, co_compat x i j hi hj hij,
      sf_compat s i j _ (hij.trans inf_le_right) hij, h, zpow_add, Units.val_mul, map_mul]
    ring
  map_add' x y := co_ext fun k => by simp only [co_pwMk, co_add, mul_add]
  map_smul' a x := co_ext fun k => mul_left_comm _ _ _

def mulPw (s : LB.Sec (pw L n)) (l l' : ℤ) (V : X.Opens) :
    SecOn (pw L l) V →ₗ[Γ(X, V)] SecOn (pw L l') V :=
  if h : l' = l + n then mulEq s h V else 0

theorem co_mulPw (s : LB.Sec (pw L n)) (h : l' = l + n) (x : SecOn (pw L l) V) (k : L.ι) :
    co (mulPw s l l' V x) k = rs X inf_le_right (sf s k) * co x k := by
  rw [mulPw, dif_pos h]; rfl

theorem mulPw_restrict (s : LB.Sec (pw L n)) (h : W ≤ V) (x : SecOn (pw L l) V) :
    mulPw s l l' W (SecOn.restrict _ h x) = SecOn.restrict _ h (mulPw s l l' V x) := by
  by_cases e : l' = l + n
  · exact co_ext fun k => by simp only [co_mulPw s e, co_restrict, map_mul, rs_rs]
  · simp only [mulPw, dif_neg e, LinearMap.zero_apply, map_zero]

theorem mulPw_comm (s s' : LB.Sec (pw L n)) {l'' : ℤ} (h : l' = l + n) (h' : l'' = l' + n)
    (x : SecOn (pw L l) V) :
    mulPw s' l' l'' V (mulPw s l l' V x) = mulPw s l' l'' V (mulPw s' l l' V x) :=
  co_ext fun k => by
    rw [co_mulPw _ h', co_mulPw _ h', co_mulPw _ h, co_mulPw _ h, mul_left_comm]

def ch (hL : L.IsLB) (l : ℤ) (k : L.ι) (h : V ≤ L.U k) : SecOn (pw L l) V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  SecOn.chart (isLB_pw hL l) k h

theorem ch_apply (hL : L.IsLB) (k : L.ι) (h : V ≤ L.U k) (x : SecOn (pw L l) V) :
    ch hL l k h x = rs X (le_inf le_rfl h) (co x k) := rfl

theorem ch_mulPw (hL : L.IsLB) (k : L.ι) (h : V ≤ L.U k) (s : LB.Sec (pw L n)) (e : l' = l + n)
    (x : SecOn (pw L l) V) : ch hL l' k h (mulPw s l l' V x) = rs X h (sf s k) * ch hL l k h x := by
  rw [ch_apply, ch_apply, co_mulPw s e, map_mul, rs_rs]

theorem sum_mulPw_iff (hL : L.IsLB) (k : L.ι) (h : V ≤ L.U k) {J : Type} (T : Finset J)
    (s : J → LB.Sec (pw L n)) (e : l' = l + n) (y : SecOn (pw L l') V) :
    (∃ t : J → SecOn (pw L l) V, y = ∑ j ∈ T, mulPw (s j) l l' V (t j)) ↔
      ∃ r : J → Γ(X, V), ch hL l' k h y = ∑ j ∈ T, rs X h (sf (s j) k) * r j := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨fun j => ch hL l k h (t j), by simp only [map_sum, ch_mulPw hL k h _ e]⟩
  · rintro ⟨r, hr⟩
    refine ⟨fun j => (ch hL l k h).symm (r j), (ch hL l' k h).injective ?_⟩
    simp only [hr, map_sum, ch_mulPw hL k h _ e, LinearEquiv.apply_symm_apply]

variable {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {κ : Type} (D : κ → X.Opens)

def mulCube (s : LB.Sec (pw L n)) (l l' : ℤ) : secCube f (pw L l) D ⟶ secCube f (pw L l') D :=
  secCubeMap f D (mulPw s l l') (mulPw_restrict s)

theorem mulCube_comm (s s' : LB.Sec (pw L n)) (l l' l'' : ℤ) (h : l' = l + n) (h' : l'' = l' + n) :
    mulCube f D s l l' ≫ mulCube f D s' l' l'' = mulCube f D s' l l' ≫ mulCube f D s l' l'' := by
  ext T x
  exact mulPw_comm s s' h h' x

theorem mem_mulCube_iff {J : Type} [Fintype J] (P : J → Prop) [DecidablePred P] (s : J → LB.Sec (pw L n))
    (T : Finset κ) (y : SecOn (pw L l') (⨅ i ∈ T, D i)) :
    (show (secCube f (pw L l') D).obj T from y) ∈
      (⨆ (j : J) (_ : P j), LinearMap.range ((mulCube f D (s j) l l').app T).hom) ↔
      ∃ t : J → SecOn (pw L l) (⨅ i ∈ T, D i),
        y = ∑ j ∈ Finset.univ.filter P, mulPw (s j) l l' _ (t j) :=
  mem_iSup_range_iff P _ _

theorem exists_sec_sum_of_ofSec_eq_sum (hV : V = ⊤) {J : Type} (T : Finset J) (s : J → LB.Sec (pw L n)) (e : l' = l + n)
    (y : LB.Sec (pw L l')) (h : ∃ t : J → SecOn (pw L l) V,
      (GlobalTheory.LB.ofSec y V : SecOn (pw L l') V) = ∑ j ∈ T, mulPw (s j) l l' V (t j)) :
    ∃ ta : J → LB.Sec (pw L l), ∀ k, sf y k = ∑ j ∈ T, sf (s j) k * sf (ta j) k := by
  obtain ⟨t, ht⟩ := h
  choose ta hta using fun j => (SecOn.ofSec_bijective (M := pw L l) hV).2 (t j)
  refine ⟨ta, fun k => ?_⟩
  have hk : L.U k ≤ V ⊓ L.U k := le_inf (hV ▸ le_top) le_rfl
  have := congrArg (fun z => rs X hk (co z k)) ht
  simp only [co_sum, co_mulPw _ e, ← hta, co_ofSec, map_sum, map_mul, rs_rs, rs_self] at this
  exact this

theorem gs_rs (y : X) (h : W ≤ V) (hy : y ∈ W) (a : Γ(X, V)) :
    gs (𝟙 X) y W (rs X h a) = gs (𝟙 X) y V a := gs_res (𝟙 X) y h hy a

theorem gs_germ (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = (X.presheaf.germ V y hy).hom a := gs_eq (𝟙 X) y V hy a

theorem gs_sub' (y : X) (hy : y ∈ V) (a b : Γ(X, V)) :
    gs (𝟙 X) y V (a - b) = gs (𝟙 X) y V a - gs (𝟙 X) y V b := by
  simp only [gs_germ y hy, map_sub]

theorem gs_co_change (x : SecOn (pw L l) V) (y : X) (hy : y ∈ V) {k k' : L.ι} (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gs (𝟙 X) y (V ⊓ L.U k) (co x k) =
      gs (𝟙 X) y (L.U k ⊓ L.U k') (L.g k k' ^ l).val * gs (𝟙 X) y (V ⊓ L.U k') (co x k') := by
  have hO : y ∈ V ⊓ L.U k ⊓ L.U k' := ⟨⟨hy, hk⟩, hk'⟩
  have := congrArg (gs (𝟙 X) y _) (co_compat x k k' (O := V ⊓ L.U k ⊓ L.U k') inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right))
  rwa [gs_mul _ y _ hO, gs_rs y _ hO, gs_rs y _ hO, gs_rs y _ hO] at this

theorem gs_sf_change (s : LB.Sec (pw L n)) (y : X) {k k' : L.ι} (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gs (𝟙 X) y (L.U k) (sf s k) =
      gs (𝟙 X) y (L.U k ⊓ L.U k') (L.g k k' ^ n).val * gs (𝟙 X) y (L.U k') (sf s k') := by
  have hO : y ∈ L.U k ⊓ L.U k' := ⟨hk, hk'⟩
  have := congrArg (gs (𝟙 X) y _) (sf_compat s k k' inf_le_left inf_le_right le_rfl)
  rwa [gs_mul _ y _ hO, gs_rs y _ hO, gs_rs y _ hO, gs_rs y _ hO] at this

def zI {J : Type} (s : J → LB.Sec (pw L n)) (y : X) (k : L.ι) : Ideal (X.presheaf.stalk y) :=
  Ideal.span (Set.range fun i => gs (𝟙 X) y (L.U k) (sf (s i) k))

theorem zI_le {J : Type} (s : J → LB.Sec (pw L n)) (y : X) {k k' : L.ι} (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    zI s y k ≤ zI s y k' := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  simp only [gs_sf_change (s i) y hk hk']
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem zI_eq {J : Type} (s : J → LB.Sec (pw L n)) (y : X) {k : L.ι} (h : V ≤ L.U k) (hy : y ∈ V) :
    Ideal.span (Set.range fun i => gs (𝟙 X) y V (rs X h (sf (s i) k))) = zI s y k := by
  simp only [gs_rs y h hy, zI]

theorem mem_basicOpen_iff (s : LB.Sec (pw L n)) (y : X) {k : L.ι} (h : V ≤ L.U k) (hy : y ∈ V) :
    y ∈ X.basicOpen (rs X h (sf s k)) ↔ y ∈ Out.nonzeroLocus s := by
  rw [X.mem_basicOpen _ y hy, ← gs_germ y hy, gs_rs y h hy]
  constructor
  · intro hu
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
    rw [gs_germ y (h hy)] at hu
    exact (X.mem_basicOpen (sf s k) y (h hy)).2 hu
  · intro hn
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 hn
    have hy' : y ∈ L.U k' := X.basicOpen_le (sf s k') hk'
    have hu := (X.mem_basicOpen (sf s k') y hy').1 hk'
    rw [← gs_germ y hy', gs_sf_change s y hy' (h hy)] at hu
    exact isUnit_of_mul_isUnit_right hu

theorem gs_ch (hL : L.IsLB) {k : L.ι} (h : V ≤ L.U k) (x : SecOn (pw L l) V) (y : X) (hy : y ∈ V) :
    gs (𝟙 X) y V (ch hL l k h x) = gs (𝟙 X) y (V ⊓ L.U k) (co x k) := gs_rs y _ hy _

theorem gs_sum_mem {J : Type} (T : Finset J) (s : J → LB.Sec (pw L n)) (e : l' = l + n)
    (t : J → SecOn (pw L l) V) (y : X) (hy : y ∈ V) {k : L.ι} (hk : y ∈ L.U k) :
    gs (𝟙 X) y (V ⊓ L.U k) (co (∑ j ∈ T, mulPw (s j) l l' V (t j)) k) ∈ zI s y k := by
  have hO : y ∈ V ⊓ L.U k := ⟨hy, hk⟩
  rw [co_sum, gs_germ y hO, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [co_mulPw _ e, map_mul, ← gs_germ y hO, gs_rs y _ hO]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem sum_of_germs (hL : L.IsLB) (hV : IsAffineOpen V) {k : L.ι} (h : V ≤ L.U k) {g : ℕ}
    (s : Fin g → LB.Sec (pw L n)) (e : l' = l + n) (c : X → L.ι) (hc : ∀ y, y ∈ L.U (c y))
    (σ : SecOn (pw L l') V)
    (hσ : ∀ y : X, y ∈ V → (∀ i, y ∉ Out.nonzeroLocus (s i)) →
      gs (𝟙 X) y (V ⊓ L.U (c y)) (co σ (c y)) ∈ zI s y (c y)) :
    ∃ t : Fin g → SecOn (pw L l) V,
      σ = ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < g), mulPw (s j) l l' V (t j) := by
  rw [sum_mulPw_iff hL k h _ s e, Finset.filter_true_of_mem (fun j _ => j.2)]
  have := GlobalTheory.mem_span_of_forall_germ_mem_span X V (Fin g) (fun i => rs X h (sf (s i) k)) (ch hL l' k h σ) hV fun y hy hz => by
    rw [zI_eq s y h hy, gs_ch hL h σ y hy, gs_co_change σ y hy (h hy) (hc y)]
    exact Ideal.mul_mem_left _ _ (zI_le s y (hc y) (h hy)
      (hσ y hy fun i hi => hz i ((mem_basicOpen_iff (s i) y h hy).2 hi)))
  obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.1 this
  exact ⟨r, by rw [← hr]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _⟩

theorem exists_interp {K : Type} [Field K] (p : X ⟶ Sp K) (hp : LocallyOfFiniteType p)
    (hL : L.IsLB) (hV : IsAffineOpen V) {k : L.ι} (h : V ≤ L.U k) {J : Type}
    (s : J → LB.Sec (pw L n)) (hZ : Set.Finite {y : X | ∀ i, y ∉ Out.nonzeroLocus (s i)})
    (c : X → L.ι) (hc : ∀ y, y ∈ L.U (c y)) (a : ∀ y : X, X.presheaf.stalk y) (l : ℤ) :
    ∃ σ : SecOn (pw L l) V, ∀ y : X, y ∈ V → (∀ i, y ∉ Out.nonzeroLocus (s i)) →
      gs (𝟙 X) y (V ⊓ L.U (c y)) (co σ (c y)) - a y ∈ zI s y (c y) := by
  obtain ⟨r, hr⟩ := GlobalTheory.GermInterp.exists_germ_sub_mem K X p V J (fun i => rs X h (sf (s i) k))
    (fun y => gs (𝟙 X) y (L.U (c y) ⊓ L.U k) ((L.g (c y) k ^ l)⁻¹).val * a y) hp hV
    (hZ.subset fun y hy i hi => hy.2 i ((mem_basicOpen_iff (s i) y h hy.1).2 hi))
  refine ⟨(ch hL l k h).symm r, fun y hy hz => ?_⟩
  have h1 := hr y hy fun i hi => hz i ((mem_basicOpen_iff (s i) y h hy).1 hi)
  have hO : y ∈ L.U (c y) ⊓ L.U k := ⟨hc y, h hy⟩
  rw [zI_eq s y h hy] at h1
  have h2 := Ideal.mul_mem_left _ (gs (𝟙 X) y (L.U (c y) ⊓ L.U k) (L.g (c y) k ^ l).val)
    (zI_le s y (h hy) (hc y) h1)
  rw [mul_sub, ← _root_.mul_assoc, ← gs_mul _ y _ hO, Units.mul_inv, gs_germ y hO 1, map_one, _root_.one_mul] at h2
  rwa [gs_co_change _ y hy (hc y) (h hy), ← gs_ch hL h _ y hy, LinearEquiv.apply_symm_apply]

theorem biInf_empty : (⨅ i ∈ (∅ : Finset κ), D i) = ⊤ := by simp

theorem mem_biInf_of_forall (T : Finset κ) (y : X) (h : ∀ a ∈ T, y ∈ D a) : y ∈ ⨅ i ∈ T, D i := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [biInf_empty]; trivial
  | insert a s _ ih =>
    rw [Finset.iInf_insert]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

theorem regular_cube (hL : L.IsLB) {g : ℕ} (s : Fin g → LB.Sec (pw L n)) (T : Finset κ) (k : L.ι)
    (h : ⨅ i ∈ T, D i ≤ L.U k)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, ⨅ i ∈ T, D i) (List.ofFn fun i => rs X h (sf (s i) k)))
    (i : Fin g) (l l' : ℤ) (y : (secCube f (pw L l) D).obj T) (e : l' = l + n)
    (hy : ((mulCube f D (s i) l l').app T).hom y ∈
      (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mulCube f D (s j) l l').app T).hom)) :
    y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mulCube f D (s j) (l - n) l).app T).hom := by
  obtain ⟨r, hr⟩ := (sum_mulPw_iff hL k h _ s e _).1
    ((mem_mulCube_iff f D (fun j : Fin g => (j : ℕ) < i) s T (mulPw (s i) l l' _ y)).1 hy)
  replace hr := (ch_mulPw hL k h (s i) e y).symm.trans hr
  exact (mem_mulCube_iff f D (fun j : Fin g => (j : ℕ) < i) s T y).2
    ((sum_mulPw_iff hL k h _ s (sub_add_cancel l n).symm y).2 (regular_step _ hreg i _ r hr))

theorem cut_global {K : Type} [Field K] (p : X ⟶ Sp K) [IsSeparated p] (hp : LocallyOfFiniteType p)
    [CompactSpace X] (hL : L.IsLB) {g : ℕ} (s : Fin g → LB.Sec (pw L n)) (hn : 0 < n)
    (hZ : Set.Finite {y : X | ∀ i, y ∉ Out.nonzeroLocus (s i)})
    (hreg : ∀ (V : X.Opens) (k : L.ι) (h : V ≤ L.U k), IsAffineOpen V →
      RingTheory.Sequence.IsWeaklyRegular Γ(X, V) (List.ofFn fun i => rs X h (sf (s i) k)))
    (hvan : ∀ (l : ℤ) (I : Type) [LinearOrder I] [Fintype I] (D : I → X.Opens), 1 ≤ l →
      (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ q, (cubeComplex (secCube p (pw L l) D)).ExactAt q)
    (c : X → L.ι) (hc : ∀ y, y ∈ L.U (c y)) :
    (∀ (i : Fin g) (l : ℤ) (y : LB.Sec (pw L l)) (ta : Fin g → LB.Sec (pw L l)), (i : ℕ) * n < l →
      (∀ k, sf (s i) k * sf y k =
        ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), sf (s j) k * sf (ta j) k) →
      ∀ d : ℤ, d = l - n → ∃ tb : Fin g → LB.Sec (pw L d), ∀ k, sf y k =
        ∑ j ∈ Finset.univ.filter (fun j : Fin g => (j : ℕ) < i), sf (s j) k * sf (tb j) k) ∧
    ∀ l : ℤ, g * n < l →
      (∀ a : ∀ y : X, X.presheaf.stalk y, ∃ sg : LB.Sec (pw L l), ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) →
        gs (𝟙 X) y (L.U (c y)) (sf sg (c y)) - a y ∈ zI s y (c y)) ∧
      ∀ sg : LB.Sec (pw L l), (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) →
        gs (𝟙 X) y (L.U (c y)) (sf sg (c y)) ∈ zI s y (c y)) →
        ∀ d : ℤ, d = l - n → ∃ ta : Fin g → LB.Sec (pw L d), ∀ k, sf sg k = ∑ j, sf (s j) k * sf (ta j) k := by
  classical
  obtain ⟨I, _, D, kk, hD, hle, hcov⟩ := exists_finite_affine_refinement hL
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  haveI : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from p]
    infer_instance
  have haff : ∀ T : Finset I, T.Nonempty → IsAffineOpen (⨅ i ∈ T, D i) := fun T hT =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hT) fun i _ => hD i
  have hin : ∀ (T : Finset I) a, a ∈ T → ⨅ i ∈ T, D i ≤ L.U (kk a) := fun T a ha =>
    (biInf_le _ ha).trans (hle a)
  have htop : ⨆ i, D i = ⊤ := top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hcov y)
  obtain ⟨H1, H2⟩ := GlobalTheory.cube_cut_regular_sequence K I g n (fun l => secCube p (pw L l) D)
    (fun i => mulCube p D (s i)) hn (fun i j => mulCube_comm p D (s i) (s j))
    (fun T hT i l l' y e hy => by
      obtain ⟨a, ha⟩ := hT
      exact regular_cube p D hL s T (kk a) (hin T a ha) (hreg _ _ _ (haff T ⟨a, ha⟩)) i l l' y e hy)
    (fun l hl => hvan l I D hl hD htop)
  refine ⟨fun i l y ta hi e d hd => ?_, fun l hl => ⟨fun a => ?_, fun sg hsg d hd => ?_⟩⟩
  · subst hd
    refine exists_sec_sum_of_ofSec_eq_sum (biInf_empty D) _ s (sub_add_cancel l n).symm y
      ((mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < i) s ∅ _).1
        (H1 i l (l + n) (GlobalTheory.LB.ofSec y _ : SecOn (pw L l) _) rfl hi
          ((mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < i) s ∅
            (mulPw (s i) l (l + n) _ (GlobalTheory.LB.ofSec y _))).2 ⟨fun j => GlobalTheory.LB.ofSec (ta j) _, co_ext fun k => ?_⟩)))
    simp only [co_sum, co_mulPw _ rfl, co_ofSec, ← map_mul, ← map_sum, e k]
  · choose σ hσ using fun b : I => exists_interp p hp hL (haff {b} (by simp)) (hin {b} b (by simp)) s hZ c hc a l
    obtain ⟨y₀, hy₀⟩ := (H2 l hl).2 σ fun b b' => by
      have h1 := iInf_le_iInf_of_subset D (show ({b} : Finset I) ⊆ {b, b'} by simp)
      have h2 := iInf_le_iInf_of_subset D (show ({b'} : Finset I) ⊆ {b, b'} by simp)
      refine (mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s {b, b'}
        (SecOn.restrict _ h1 (σ b) - SecOn.restrict _ h2 (σ b'))).2
        (sum_of_germs hL (haff _ (by simp)) (hin _ b (by simp)) s (sub_add_cancel l n).symm c hc _
          fun y hy hz => ?_)
      have hO : y ∈ (⨅ i ∈ ({b, b'} : Finset I), D i) ⊓ L.U (c y) := ⟨hy, hc y⟩
      rw [co_sub, co_restrict, co_restrict, gs_sub' y hO, gs_rs y _ hO, gs_rs y _ hO]
      have := Ideal.sub_mem _ (hσ b y (h1 hy) hz) (hσ b' y (h2 hy) hz)
      rwa [sub_sub_sub_cancel_right] at this
    obtain ⟨sg, rfl⟩ := (SecOn.ofSec_bijective (M := pw L l) (biInf_empty D)).2 y₀
    refine ⟨sg, fun y hz => ?_⟩
    obtain ⟨b, hb⟩ := hcov y
    have hy : y ∈ ⨅ i ∈ ({b} : Finset I), D i := mem_biInf_of_forall D _ y (by simpa using hb)
    have hO : y ∈ (⨅ i ∈ ({b} : Finset I), D i) ⊓ L.U (c y) := ⟨hy, hc y⟩
    obtain ⟨t, ht⟩ := (mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s {b}
      (SecOn.restrict _ (iInf_le_iInf_of_subset D (Finset.empty_subset {b})) (GlobalTheory.LB.ofSec sg _) - σ b)).1 (hy₀ b)
    have h1 := gs_sum_mem (Finset.univ.filter (fun j : Fin g => (j : ℕ) < g)) s (sub_add_cancel l n).symm t y hy (hc y)
    rw [← ht, SecOn.restrict_ofSec, co_sub, co_ofSec, gs_sub' y hO, gs_rs y _ hO] at h1
    have := Ideal.add_mem _ h1 (hσ b y hy hz)
    rwa [sub_add_sub_cancel] at this
  · subst hd
    have := exists_sec_sum_of_ofSec_eq_sum (biInf_empty D) _ s (sub_add_cancel l n).symm sg
      ((mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s ∅ _).1
        ((H2 l hl).1 (GlobalTheory.LB.ofSec sg _ : SecOn (pw L l) _) fun b => by
          refine (mem_mulCube_iff p D (fun j : Fin g => (j : ℕ) < g) s {b}
            (SecOn.restrict _ (iInf_le_iInf_of_subset D (Finset.empty_subset {b})) (GlobalTheory.LB.ofSec sg _))).2
            (sum_of_germs hL (haff _ (by simp)) (hin _ b (by simp)) s (sub_add_cancel l n).symm c hc _
              fun y hy hz => ?_)
          have hO : y ∈ (⨅ i ∈ ({b} : Finset I), D i) ⊓ L.U (c y) := ⟨hy, hc y⟩
          rw [SecOn.restrict_ofSec, co_ofSec, gs_rs y _ hO]
          exact hsg y hz))
    rwa [Finset.filter_true_of_mem (fun j _ => j.2)] at this

end GlobalTheory.KosField

namespace GlobalTheory

open KosField in

theorem koszul_sections_exact_field : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  intro hlaw K _ _ x n l s b m c hn hl hZ hb hm hc
  haveI := x.P.isAb.proper
  haveI : CompactSpace x.P.A.left := QuasiCompact.compactSpace_of_compactSpace x.P.A.hom
  obtain ⟨H1, H2⟩ := cut_global (n := (n : ℤ)) x.P.A.hom inferInstance x.P.isLB s (by exact_mod_cast hn) hZ
    (fun V k h hV => GlobalTheory.KeyKa.isWeaklyRegular_of_finZ hlaw K x n s V k h hn hZ hV)
    (fun l I _ _ D => GlobalTheory.PolVanishing.exactAt_secCube_pw hlaw K x.P l I D) c hc
  have hl' : (x.P.g : ℤ) * n < l := by exact_mod_cast hl
  refine ⟨GlobalTheory.KeyKa.KosBasis.koszul_exact_of_regular K x n l s b m hl hb hm fun i j hij y ta e => ?_, (H2 l hl').1, fun sg hsg => ?_⟩
  · have h1 : (j + 1 + i) * n < l := lt_of_le_of_lt (Nat.mul_le_mul_right n hij) hl
    have h2 : (i : ℕ) * n < l - (j + 1) * n := by rw [add_mul] at h1; omega
    have H := H1 i _ y ta (by exact_mod_cast h2) e
    rcases Nat.eq_zero_or_pos i with hi | hi
    · obtain ⟨tb, htb⟩ := H _ rfl
      refine ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun k => ?_⟩
      have h0 : Finset.univ.filter (fun j : Fin x.P.g => (j : ℕ) < i) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun j _ => by omega
      have := htb k
      rw [h0, Finset.sum_empty] at this
      refine this.trans (Finset.sum_eq_zero fun j _ => ?_).symm
      exact mul_zero _
    · refine H _ ?_
      have h3 : n ≤ (i : ℕ) * n := Nat.le_mul_of_pos_left n hi
      have h4 : (j + 2) * n = (j + 1) * n + n := by ring
      omega
  · refine (H2 l hl').2 sg hsg _ ?_
    have h3 : n ≤ x.P.g * n := Nat.le_mul_of_pos_left n x.g_pos
    omega

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  atlas_forward_decl GlobalTheory.koszul_sections_exact_field
end
