import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHomogeneousIdealOfEvalZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenNonemptyOfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpressionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialMemRange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegral
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordsOfEtaleBasicOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDim

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem homIdeal_homog : ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_component_mem ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_component_mem <;> assumption)

theorem homIdeal_ne_top [Nonempty X] : homIdeal i ≠ ⊤ := by
  first
    | exact GlobalTheory.T.homogeneous_ideal_ne_top ..
    | (intros; apply GlobalTheory.T.homogeneous_ideal_ne_top <;> assumption)

theorem preimage_basicOpen_nonempty [IsIntegral X] {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hg0 : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  first
    | exact GlobalTheory.T.basic_open_nonempty_of_ne_zero ..
    | (intros; apply GlobalTheory.T.basic_open_nonempty_of_ne_zero <;> assumption)

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem biInf_preimage {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) :
    ⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext x
    simp [yS, Proj.basicOpen]
  | insert a S ha ih =>
    rw [Finset.iInf_insert, ih]
    simp only [yS]
    rw [Finset.prod_insert ha, Proj.basicOpen_mul]
    rfl

theorem isAffineOpen_preimage (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) := by
  haveI := hci
  exact (Proj.isAffineOpen_basicOpen (grK K N) g hg he).preimage i

theorem evV_surjective (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) :
    Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first
    | exact GlobalTheory.T.basic_open_eval_surjective ..
    | (intros; apply GlobalTheory.T.basic_open_eval_surjective <;> assumption)

theorem range_resO_eq (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) {V W : X.Opens} (hW : W = i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : V ≤ W)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) : Set.range (resO h) = Set.range (evV i g V h') := by
  subst hW
  have e0 : i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl ≫ X.presheaf.map (homOfLE h).op = i.appLE _ V h' :=
    Scheme.Hom.appLE_map i _ _
  have hcomp : evV i g V h' = (resO h).comp (evV i g _ le_rfl) := by
    refine RingHom.ext fun a => ?_
    simp only [evV, resO, RingHom.comp_apply, ← e0]
    rfl
  rw [hcomp, RingHom.coe_comp, Set.range_comp, (evV_surjective i hci hg he).range_eq, Set.image_univ]

theorem iSup_preimage_eq_top {m e : ℕ} (he : 0 < e) (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k)))
      (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i)) :
    ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first
    | exact GlobalTheory.T.basic_opens_cover_of_finite ..
    | (intros; apply GlobalTheory.T.basic_opens_cover_of_finite <;> assumption)

theorem finiteType_affine (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}
    (hW : IsAffineOpen W) : letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first
    | exact GlobalTheory.T.affine_open_finiteType ..
    | (intros; apply GlobalTheory.T.affine_open_finiteType <;> assumption)

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
  (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
  (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k))

theorem tV_isUnit (k : Fin d) : IsUnit (tV i y hy V hV k) := by
  first
    | exact GlobalTheory.T.torus_coordinate_isUnit ..
    | (intros; apply GlobalTheory.T.torus_coordinate_isUnit <;> assumption)

theorem tpow_mem_range (he : 0 < e) (S : Finset (Fin (d + 1)))
    (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)) :
    ∀ m ∈ expS S, tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  first
    | exact GlobalTheory.T.torus_monomial_mem_range ..
    | (intros; apply GlobalTheory.T.torus_monomial_mem_range <;> assumption)

theorem isIntegral_torusS (he : 0 < e) (q : X ⟶ Spec (CommRingCat.of K)) (hiq : i ≫ PSpace.str K N = q)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k)))
      (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (ht : ∀ k, IsUnit (tV i y hy V hV k)) :
    letI := (strV q V).toAlgebra
    ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  first
    | exact GlobalTheory.T.noether_normalization_finite ..
    | (intros; apply GlobalTheory.T.noether_normalization_finite <;> assumption)

theorem algebraicIndependent_tV [IsIntegral X] (he : 0 < e) (q : X ⟶ Spec (CommRingCat.of K))
    (hiq : i ≫ PSpace.str K N = q)
    (halg : AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) (hne : (V : Set X).Nonempty) :
    letI := (strV q V).toAlgebra
    AlgebraicIndependent K (tV i y hy V hV) := by
  first
    | exact GlobalTheory.T.algebraically_independent_coords ..
    | (intros; apply GlobalTheory.T.algebraically_independent_coords <;> assumption)

theorem isAlgebraic_of_integral_torusS {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ)
    (h : ∀ r : R, IsIntegral (torusS K t Finset.univ) r) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  first
    | exact GlobalTheory.T.algebraic_over_torus_of_integral ..
    | (intros; apply GlobalTheory.T.algebraic_over_torus_of_integral <;> assumption)

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_etale_away_pf {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale := by
  classical
  letI : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval s).toRingHom.toAlgebra
  have hRA : algebraMap (MvPolynomial (Fin d) K) A = (MvPolynomial.aeval s).toRingHom := rfl
  have : IsScalarTower K (MvPolynomial (Fin d) K) A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hRA, MvPolynomial.algebraMap_eq]
    simp
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) K) A) := by
    intro a b h
    exact hs h
  have : FaithfulSMul (MvPolynomial (Fin d) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) K) A).2 hinj
  have : Algebra.FiniteType (MvPolynomial (Fin d) K) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin d) K) A
  have : Algebra.FinitePresentation (MvPolynomial (Fin d) K) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) A := by
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq hs.aevalEquiv (RingHom.id A)
      hs.aevalEquiv.surjective Function.injective_id ?_
    ext p
    · simp [hRA]
    · simp [hRA]
  have hL : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A
  have : FaithfulSMul (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq (MvPolynomial (Fin d) K) A (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective A _).comp hinj
  letI := FractionRing.liftAlgebra (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A))
  have : Algebra.IsAlgebraic A (Localization.AtPrime (⊥ : Ideal A)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.trans (MvPolynomial (Fin d) K) A _
  have : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : CharZero (FractionRing (MvPolynomial (Fin d) K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial (Fin d) K) _)
  have : Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin d) K)) (Localization.AtPrime (⊥ : Ideal A)) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FormallyEtale (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial (Fin d) K))
  have hE : Algebra.IsEtaleAt (MvPolynomial (Fin d) K) (⊥ : Ideal A) :=
    Algebra.FormallyEtale.comp (MvPolynomial (Fin d) K) (FractionRing (MvPolynomial (Fin d) K)) _
  obtain ⟨g, hg, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial (Fin d) K) (⊥ : Ideal A)
  refine ⟨g, by simpa using hg, ?_⟩
  have heq : (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g) =
      algebraMap (MvPolynomial (Fin d) K) (Localization.Away g) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA, IsScalarTower.algebraMap_apply K A (Localization.Away g)]
    · intro i
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) K) A (Localization.Away g)]
      simp [hRA]
  rw [heq]
  exact RingHom.etale_algebraMap.2 he

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem irreducibleSpace_of_connected_of_locally {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    (h : ∀ x : α, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) : IrreducibleSpace α := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hU, hzU, hUirr⟩ := h z
    refine ⟨U, ?_, hU, hzU⟩
    have h1 : irreducibleComponent x₀ ⊆ closure U :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen isIrreducible_irreducibleComponent.2 hU
        ⟨z, hz, hzU⟩).trans (closure_mono Set.inter_subset_right)
    have h2 : closure U = irreducibleComponent x₀ := eq_irreducibleComponent hUirr.closure.2 h1
    exact subset_closure.trans h2.le
  have hclopen : IsClopen (irreducibleComponent x₀) := ⟨isClosed_irreducibleComponent, hopen⟩
  have huniv : irreducibleComponent x₀ = Set.univ := hclopen.eq_univ ⟨x₀, mem_irreducibleComponent⟩
  have hirr : IsIrreducible (Set.univ : Set α) := huniv ▸ isIrreducible_irreducibleComponent
  exact (irreducibleSpace_def α).2 hirr

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end

section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem isIntegral_of_mul_self_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : S}
    (he : e * e = e) : IsIntegral R e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, mul_sub, he]

theorem exists_tmul_one_eq_of_isIntegral {P A : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [Algebra P A] [Algebra.Smooth P A] (t : A ⊗[P] FractionRing P)
    (ht : IsIntegral A t) : ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = t := by
  obtain ⟨u, hu⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := A)
    (B := FractionRing P)).2 ⟨t, ht⟩
  have key : ∀ u : A ⊗[P] integralClosure P (FractionRing P), ∃ a : A,
      a ⊗ₜ[P] (1 : FractionRing P) =
        ((TensorProduct.toIntegralClosure P A (FractionRing P) u : _) : A ⊗[P] FractionRing P) := by
    intro u
    induction u with
    | zero => exact ⟨0, by simp⟩
    | tmul a y =>
      obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp y.2
      refine ⟨p • a, ?_⟩
      change _ = a ⊗ₜ[P] (y : FractionRing P)
      rw [TensorProduct.smul_tmul, ← hp, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add, Subalgebra.coe_add]⟩
  obtain ⟨a, ha⟩ := key u
  exact ⟨a, by rw [ha, hu]⟩

theorem exists_away_isDomain_of_etale {P A : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [Algebra P A] [Algebra.Etale P A] (q : Ideal A) [q.IsPrime] :
    ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical

  have hι : Function.Injective (fun a : A => a ⊗ₜ[P] (1 : FractionRing P)) := by
    have hinj : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
      IsFractionRing.injective P (FractionRing P)
    have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := A)
      (Algebra.linearMap P (FractionRing P)) hinj
    intro a b hab
    apply (TensorProduct.rid P A).symm.injective
    apply h2
    simpa using hab

  obtain ⟨I, hI, Ai, hAi, hAlg, e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing P) (FractionRing P ⊗[P] A)).mp
      inferInstance
  have := Fintype.ofFinite I
  let φ : A ⊗[P] FractionRing P ≃+* (Π i, Ai i) :=
    (Algebra.TensorProduct.comm P A (FractionRing P)).toRingEquiv.trans e.toRingEquiv

  have hε : ∀ i, ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = φ.symm (Pi.single i 1) := by
    intro i
    refine exists_tmul_one_eq_of_isIntegral _ (isIntegral_of_mul_self_eq ?_)
    rw [← map_mul, ← Pi.single_mul, one_mul]
  choose a ha using hε

  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ∉ q := by
    by_contra! h
    have hsum : (∑ i, a i) ∈ q := Ideal.sum_mem q fun i _ => h i
    have h1 : (∑ i, a i) = 1 := by
      apply hι
      simp only
      rw [TensorProduct.sum_tmul, Finset.sum_congr rfl (fun i _ => ha i), ← map_sum,
        Finset.univ_sum_single]
      exact map_one φ.symm
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).2 (h1 ▸ hsum))
  refine ⟨a i₀, hi₀, ?_⟩

  let F : A →+* Ai i₀ := (Pi.evalRingHom Ai i₀).comp
    (φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom))
  have hF : ∀ x : A, F x = φ (x ⊗ₜ[P] (1 : FractionRing P)) i₀ := fun x => rfl
  have hFg : IsUnit (F (a i₀)) := by
    rw [hF, ha, RingEquiv.apply_symm_apply, Pi.single_eq_same]
    exact isUnit_one
  let ψ : Localization.Away (a i₀) →+* Ai i₀ := IsLocalization.Away.lift (a i₀) hFg
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (a i₀)) x
    have hspec := IsLocalization.mk'_spec (Localization.Away (a i₀)) y s
    have hFy : F y = 0 := by
      have h3 := congrArg ψ hspec
      rw [map_mul, hx, zero_mul] at h3
      have h4 : ψ (algebraMap A (Localization.Away (a i₀)) y) = F y := IsLocalization.lift_eq _ _
      rw [← h4, ← h3]
    have hyg : y * a i₀ = 0 := by
      apply hι
      simp only
      have hmul : (y * a i₀) ⊗ₜ[P] (1 : FractionRing P) =
          (y ⊗ₜ[P] (1 : FractionRing P)) * (a i₀ ⊗ₜ[P] (1 : FractionRing P)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hmul, zero_tmul]
      apply φ.injective
      rw [map_mul, ha, RingEquiv.apply_symm_apply, map_zero]
      funext k
      by_cases hk : k = i₀
      · subst hk
        simp only [Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.zero_apply]
        exact hFy
      · simp [Pi.mul_apply, Pi.single_eq_of_ne hk]
    have hy0 : algebraMap A (Localization.Away (a i₀)) y = 0 := by
      have h5 := congrArg (algebraMap A (Localization.Away (a i₀))) hyg
      rw [map_mul, map_zero] at h5
      exact (IsUnit.mul_left_eq_zero (IsLocalization.Away.algebraMap_isUnit (a i₀))).1 h5
    rw [← hspec] at hy0
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units _ s)).1 hy0
  exact hψ.isDomain ψ

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

section
set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem exists_away_isDomain_of_smooth {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  obtain ⟨ι, σ, _, _, ⟨Pr⟩⟩ := hstd.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension K (Localization.Away g) :=
    ⟨⟨ι, σ, ‹_›, ‹_›, Pr, rfl⟩⟩
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    (n := Pr.dimension) (R := K) (S := Localization.Away g)
  letI : Algebra (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := hφ
  haveI hq : (p.map (algebraMap A (Localization.Away g))).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  obtain ⟨g', hg', hdom⟩ := exists_away_isDomain_of_etale
    (P := MvPolynomial (Fin Pr.dimension) K) (A := Localization.Away g)
    (p.map (algebraMap A (Localization.Away g)))
  refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem => hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap A (Localization.Away g)) hmem
  · intro S _ _ _
    haveI : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : S ≃ₐ[A] Localization.Away g' :=
      IsLocalization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g g').1)) S
        (Localization.Away g')
    exact e.toRingEquiv.toMulEquiv.isDomain

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem exists_integral_nbhd {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [Smooth q]
    (hE : ∀ (A : Type) [CommRing A] [Algebra K A] [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime],
      ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S)
    (x : X) : ∃ W : X.Opens, x ∈ W ∧ IsIntegral W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ q ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hsm := q.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of K))) hV hVU
  let φ : K →+* Γ(X, V) :=
    (q.appLE ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hφ : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    hsm
  let := φ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hφ
  obtain ⟨r, hr, hdom⟩ := hE Γ(X, V) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxW : x ∈ X.basicOpen r := by
    rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hr
  refine ⟨X.basicOpen r, hxW, ?_⟩
  have hW : IsAffineOpen (X.basicOpen r) := hV.basicOpen r
  have : IsAffine (X.basicOpen r) := hW
  have : Nonempty (X.basicOpen r) := ⟨⟨x, hxW⟩⟩
  let := (X.presheaf.map (homOfLE <| X.basicOpen_le r).op).hom.toAlgebra
  have := hV.isLocalization_basicOpen r
  have : IsDomain Γ(X, X.basicOpen r) := hdom _
  have : IsDomain Γ(X.basicOpen r, ⊤) :=
    (X.basicOpen r).topIso.commRingCatIsoToRingEquiv.injective.isDomain
      (X.basicOpen r).topIso.commRingCatIsoToRingEquiv
  exact isIntegral_of_isAffine_of_isDomain _

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIntegral_of_smooth_pf {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension n q] : IsIntegral X := by
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hE : ∀ (A : Type) [CommRing A] [Algebra K A] [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime],
      ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S :=
    fun A _ _ _ p _ => CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.exists_away_isDomain_of_smooth (K := K) p
  choose W hxW hW using fun x => CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.exists_integral_nbhd q hE x
  have hcov : TopologicalSpace.IsOpenCover W :=
    eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  have hredi : ∀ i, IsReduced ((X.openCoverOfIsOpenCover W hcov).X i) := by
    intro i
    rw [Scheme.openCoverOfIsOpenCover_X]
    have := hW i
    exact isReduced_of_isIntegral _
  have hred : IsReduced X := IsReduced.of_openCover X (X.openCoverOfIsOpenCover W hcov)
  have hirr : IrreducibleSpace X := by
    refine CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.irreducibleSpace_of_connected_of_locally fun x => ⟨W x, (W x).isOpen, hxW x, ?_⟩
    have := hW x
    have hi := irreducibleSpace_of_isIntegral (W x : Scheme)
    have h2 := (IrreducibleSpace.isIrreducible_univ (↥(W x : Scheme))).image Subtype.val
      continuous_subtype_val.continuousOn
    rwa [Set.image_univ, Subtype.range_coe] at h2
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIntegral_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension n q] : IsIntegral X :=
  isIntegral_of_smooth_pf q n

theorem exists_etale_away {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale :=
  exists_etale_away_pf s hs halg

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) :=
  GlobalTheory.T.coords_of_etale_basic_open q hW g s

theorem coord_card_eq {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens} (hne : (V : Set X).Nonempty) {m : ℕ} (c : Coord q V m) : m = n :=
  GlobalTheory.T.coord_dim_eq_relative_dim q n hne c

theorem exists_frac_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (hne : (X.basicOpen g : Set X).Nonempty) :
    ∀ r : Γ(X, X.basicOpen g), ∃ b ∈ Set.range (resO (X.basicOpen_le g)), ∃ b' ∈ Set.range (resO (X.basicOpen_le g)),
      b' ≠ 0 ∧ r * b' = b := by
  intro r
  letI := (resO (X.basicOpen_le g)).toAlgebra
  haveI := hW.isLocalization_basicOpen g
  haveI : Nonempty (X.basicOpen g) := hne.to_subtype
  obtain ⟨k, a, hk⟩ := IsLocalization.Away.surj g r
  refine ⟨resO (X.basicOpen_le g) a, ⟨a, rfl⟩, resO (X.basicOpen_le g) (g ^ k), ⟨g ^ k, rfl⟩, ?_, ?_⟩
  · rw [map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen g)) g).pow k).ne_zero
  · rw [map_pow]
    exact hk

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem geo_setup {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension (n + 1) q] (N : ℕ) (i : X ⟶ PSpace K N)
    (hci : IsClosedImmersion i) (hiq : i ≫ PSpace.str K N = q) :
    ∃ (e : ℕ) (_ : 0 < e) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e),
      let U : Fin (n + 2) → X.Opens := fun k => i ⁻¹ᵁ Proj.basicOpen _ (y k)
      (⨆ k, U k) = ⊤ ∧
      (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, U k)) ∧
      ∃ (V : X.Opens) (hV : V ≤ ⨅ k, U k) (c : Coord q V (n + 1)),
        letI := (strV q V).toAlgebra
        IsDomain Γ(X, V) ∧
        (∀ k, c.t k = (i.appLE _ V (hV.trans (iInf_le U 0))).hom (yRatio y hy k)) ∧
        ∃ ht : ∀ k, IsUnit (c.t k),
          AlgebraicIndependent K c.t ∧
          ∃ B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, V),
            (∀ S, S.Nonempty → (B S : Set Γ(X, V)) = Set.range (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → Function.Injective (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → torusS K (fun k => (ht k).unit) S ≤ B S) ∧
            (∀ S, S.Nonempty → (B S).FG) ∧
            (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K (fun k => (ht k).unit) S) b) ∧
            (∀ j, B (Finset.univ.erase j) ≤ B Finset.univ) ∧
            (∀ r : Γ(X, V), ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) := by
  classical
  haveI : IsClosedImmersion i := hci
  haveI hXi : IsIntegral X := isIntegral_of_smooth q (n + 1)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨e, m, y, he, hy, halg, hfin⟩ :=
    GlobalTheory.T.noether_normalization_homogeneous K N (homIdeal i) (homIdeal_ne_top i) (homIdeal_homog i)
  have hcov := iSup_preimage_eq_top i he y hy hfin
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := by
    rcases m with _ | d
    · exfalso
      obtain ⟨x⟩ := (inferInstance : Nonempty X)
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hcov, iSup_of_empty] at hx
      simp at hx
    · exact ⟨d, rfl⟩
  have hpos : ∀ S : Finset (Fin (d + 1)), S.Nonempty → 0 < S.card * e := fun S hS => Nat.mul_pos hS.card_pos he
  have haff : ∀ S : Finset (Fin (d + 1)), S.Nonempty →
      IsAffineOpen (⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) := by
    intro S hS
    rw [biInf_preimage i y S]
    exact isAffineOpen_preimage i hci (yS_mem y hy S) (hpos S hS)
  let W : X.Opens := ⨅ k ∈ (Finset.univ : Finset (Fin (d + 1))), i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)
  have hWaff : IsAffineOpen W := haff _ Finset.univ_nonempty
  have hWV : W ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) := le_iInf fun k => biInf_le _ (Finset.mem_univ k)
  have hWS : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y Finset.univ) := (biInf_preimage i y _).le
  have hWne : (W : Set X).Nonempty := by
    have hne0 : Ideal.Quotient.mk (homIdeal i) (yS y Finset.univ) ≠ 0 := by
      intro h0
      have h1 : MvPolynomial.aeval (fun k => Ideal.Quotient.mk (homIdeal i) (y k))
          (∏ k : Fin (d + 1), (MvPolynomial.X k : MvPolynomial (Fin (d + 1)) K)) = 0 := by
        rw [map_prod]
        simpa [yS, map_prod] using h0
      have h2 := halg (h1.trans (map_zero _).symm)
      exact Finset.prod_ne_zero_iff.2 (fun k _ => MvPolynomial.X_ne_zero k) h2
    have := preimage_basicOpen_nonempty i (hpos _ Finset.univ_nonempty) (yS_mem y hy Finset.univ) hne0
    rwa [← biInf_preimage i y Finset.univ] at this
  letI algW : Algebra K Γ(X, W) := (strV q W).toAlgebra
  have htW : ∀ k, IsUnit (tV i y hy W hWV k) := tV_isUnit i y hy hWV
  have hindW : AlgebraicIndependent K (tV i y hy W hWV) :=
    algebraicIndependent_tV i y hy hWV he q hiq halg hWne
  haveI : Nonempty W := hWne.to_subtype
  have hintW : ∀ r : Γ(X, W), IsIntegral (torusS K (fun k => (htW k).unit) Finset.univ) r := by
    intro r
    have hr : r ∈ Set.range (resO (le_refl W)) := ⟨r, by simp [resO]⟩
    rw [range_resO_eq i hci (yS_mem y hy _) (hpos _ Finset.univ_nonempty) (biInf_preimage i y _) le_rfl hWS] at hr
    obtain ⟨a, rfl⟩ := hr
    exact isIntegral_torusS i y hy hWV he q hiq hfin Finset.univ hWS htW a
  have halgW : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (tV i y hy W hWV))) Γ(X, W) :=
    isAlgebraic_of_integral_torusS (fun k => (htW k).unit) hintW
  haveI hlft : LocallyOfFiniteType q := by
    first
      | infer_instance
      | (haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q; infer_instance)
      | (haveI : Smooth q := inferInstance; haveI : LocallyOfFinitePresentation q := inferInstance; infer_instance)
  haveI : Algebra.FiniteType K Γ(X, W) := finiteType_affine q hWaff
  obtain ⟨g, hg0, het⟩ := exists_etale_away (tV i y hy W hWV) hindW halgW
  obtain ⟨c, hc⟩ := exists_coord_basicOpen q hWaff g (tV i y hy W hWV) het
  have hVne : ((X.basicOpen g : X.Opens) : Set X).Nonempty := by
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    intro h
    exact hg0 ((basicOpen_eq_bot_iff g).1 h)
  have hdn : d = n + 1 := coord_card_eq q (n + 1) hVne c
  subst hdn
  refine ⟨e, he, y, hy, ?_⟩
  intro U
  have hV : X.basicOpen g ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) := (X.basicOpen_le g).trans hWV
  have hct : ∀ k, c.t k = tV i y hy (X.basicOpen g) hV k := by
    intro k
    rw [hc k]
    simp only [tV, resO]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  let c' : Coord q (X.basicOpen g) (n + 1) :=
    ⟨c.affine, tV i y hy (X.basicOpen g) hV, by
      have h := c.etale
      rwa [show c.t = tV i y hy (X.basicOpen g) hV from funext hct] at h⟩
  refine ⟨hcov, fun S hS => haff S hS, X.basicOpen g, hV, c', ?_⟩
  letI algV : Algebra K Γ(X, X.basicOpen g) := (strV q _).toAlgebra
  haveI : Nonempty (X.basicOpen g) := hVne.to_subtype
  refine ⟨inferInstance, fun k => rfl, tV_isUnit i y hy hV, algebraicIndependent_tV i y hy hV he q hiq halg hVne, ?_⟩
  let B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, X.basicOpen g) := fun S =>
    { (resO (le_biInf_of_le hV S)).range with
      algebraMap_mem' := fun a => RingHom.mem_range.2 ⟨strV q _ a,
        (RingHom.congr_fun (strV_res q (le_biInf_of_le hV S)) a).symm⟩ }
  have memB : ∀ S x, x ∈ B S ↔ x ∈ Set.range (resO (le_biInf_of_le hV S)) := fun S x => RingHom.mem_range
  refine ⟨B, fun S _ => Set.ext fun x => memB S x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S _
    exact map_injective_of_isIntegral X (homOfLE (le_biInf_of_le hV S))
  · intro S hS
    have hS' : X.basicOpen g ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) :=
      (le_biInf_of_le hV S).trans (biInf_preimage i y S).le
    refine Algebra.adjoin_le ?_
    rintro _ ⟨m, hm, rfl⟩
    have h1 := tpow_mem_range i y hy hV he S hS' (tV_isUnit i y hy hV) m hm
    rw [← range_resO_eq i hci (yS_mem y hy S) (hpos S hS) (biInf_preimage i y S) (le_biInf_of_le hV S) hS'] at h1
    exact (memB S _).2 h1
  · intro S hS
    letI : Algebra K Γ(X, ⨅ k ∈ S, U k) := (strV q _).toAlgebra
    haveI : Algebra.FiniteType K Γ(X, ⨅ k ∈ S, U k) := finiteType_affine q (haff S hS)
    let φ : Γ(X, ⨅ k ∈ S, U k) →ₐ[K] Γ(X, X.basicOpen g) :=
      { resO (le_biInf_of_le hV S) with
        commutes' := fun a => (RingHom.congr_fun (strV_res q (le_biInf_of_le hV S)) a).symm }
    have hB : B S = φ.range := by
      ext x
      rw [memB, AlgHom.mem_range]
      rfl
    rw [hB, ← Algebra.map_top]
    exact Algebra.FiniteType.out.map φ
  · intro S hS b hb
    have hS' : X.basicOpen g ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) :=
      (le_biInf_of_le hV S).trans (biInf_preimage i y S).le
    rw [memB, range_resO_eq i hci (yS_mem y hy S) (hpos S hS) (biInf_preimage i y S) (le_biInf_of_le hV S) hS'] at hb
    obtain ⟨a, rfl⟩ := hb
    exact isIntegral_torusS i y hy hV he q hiq hfin S hS' (tV_isUnit i y hy hV) a
  · intro j x hx
    rw [memB] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    have hle : (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), U k) ≤ ⨅ k ∈ Finset.univ.erase j, U k :=
      biInf_mono fun k _ => Finset.mem_univ k
    refine ⟨resO hle a, ?_⟩
    simp only [resO]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  · intro r
    obtain ⟨b, hb, b', hb', hne, h⟩ := exists_frac_basicOpen hWaff g hVne r
    exact ⟨b, (memB _ _).2 hb, b', (memB _ _).2 hb', hne, h⟩

end CrystallineSemistableComparison.Pb
end
end
