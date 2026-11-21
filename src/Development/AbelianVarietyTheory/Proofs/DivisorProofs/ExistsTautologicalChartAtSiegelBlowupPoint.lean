import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPart
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtNormalisedBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveIsAffineAndFiniteInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplAtFactorOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautBaseChangeTripleLiftLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_complete_dvr_of_local (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : A →+* W), Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, ?_, PowerSeries.C,
      RingHom.injective _, inferInstance⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, φ, h1, h2⟩

theorem exists_trait_at : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) →
    j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V),
      ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  intro g n F S s _ _ j _ _ hd hjs x
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  obtain ⟨_, ⟨y0, rfl⟩, hw⟩ :=
    GlobalTheory.BlowOpen.exists_specializes_of_dense_scheme S _ j.isOpenEmbedding.isOpen_range hd x
  obtain ⟨y1, hy1, e1⟩ := Flat.generalizingMap F.s (genericPoint_specializes (F.s y0))
  have hη : j y1 ⤳ x := (hy1.map j.continuous).trans hw
  obtain ⟨q, hq⟩ : j y1 ∈ Set.range (S.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hη
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : IsLocalRing (S.presheaf.stalk x ⧸ q.asIdeal) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨W, _, _, _, hWc, ψ, hψi, hψl⟩ := exists_complete_dvr_of_local (S.presheaf.stalk x ⧸ q.asIdeal)
  haveI : IsLocalHom (Ideal.Quotient.mk q.asIdeal) := .of_surjective _ Ideal.Quotient.mk_surjective
  let ψ' : S.presheaf.stalk x →+* W := ψ.comp (Ideal.Quotient.mk q.asIdeal)
  haveI : IsLocalHom ψ' := RingHom.isLocalHom_comp _ _
  let ξ0 : Sp W ⟶ S := spMap ψ' ≫ S.fromSpecStalk x
  have hξc : ξ0 (closedPoint W) = x := by
    show S.fromSpecStalk x (spMap ψ' (closedPoint W)) = x
    have e : spMap ψ' (closedPoint W) = closedPoint (S.presheaf.stalk x) := IsLocalRing.comap_closedPoint ψ'
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have hξg : ξ0 (⊥ : PrimeSpectrum W) = j y1 := by
    show S.fromSpecStalk x (spMap ψ' (⊥ : PrimeSpectrum W)) = j y1
    have : spMap ψ' (⊥ : PrimeSpectrum W) = q := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψ' ⊥ = q.asIdeal
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ hψi, Ideal.mk_ker]
    rw [this, hq]
  have hjKbot : ∀ pt : Sp (FractionRing W), jK W pt = (⊥ : PrimeSpectrum W) := fun pt => by
    apply PrimeSpectrum.ext
    have hpt : pt = (⊥ : PrimeSpectrum (FractionRing W)) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    subst hpt
    show Ideal.comap (algebraMap W (FractionRing W)) ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))
  have hrange : Set.range (jK W ≫ ξ0) ⊆ Set.range j := by
    rintro _ ⟨pt, rfl⟩
    rw [Scheme.Hom.comp_apply, hjKbot, hξg]
    exact ⟨y1, rfl⟩
  let y : Sp (FractionRing W) ⟶ F.X := IsOpenImmersion.lift j (jK W ≫ ξ0) hrange
  have hy : y ≫ j = jK W ≫ ξ0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (ξ0 ≫ s)
  let b0 : cycAway n →+* W := θ.hom
  have hb0 : spMap b0 = ξ0 ≫ s := hθ
  have hb0i : Function.Injective b0 := by
    have h1 : (spMap b0) (⊥ : PrimeSpectrum W) = genericPoint (Sp (cycAway n)) := by
      rw [hb0]
      exact (Scheme.Hom.comp_apply ξ0 s _).trans (by rw [hξg, ← Scheme.Hom.comp_apply, hjs, e1])
    rw [genericPoint_eq_bot_of_affine] at h1
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : CharZero W := charZero_of_injective_ringHom hb0i
  have hBase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hfl, -, hcomp, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F W hBase inferInstance y
  haveI := hfl
  refine ⟨T, spMap f ≫ ξ0, f.comp b0, ?_, ?_, ?_⟩
  · show ξ0 (spMap f (closedPoint T.V)) = x
    have e : spMap f (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    rw [e, hξc]
  · have key : jK T.V ≫ spMap f = spMap fK ≫ jK W := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      exact (hcomp a).symm
    rw [hTy, Category.assoc, hy, ← Category.assoc, key, Category.assoc]
  · rw [Category.assoc, ← hb0]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.TChart
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) → j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V), ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  atlas_forward_decl GlobalTheory.TChart.exists_trait_at
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.ConeMono

variable {X : Type} [AddCommGroup X]

def ev (a b : X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := LinearMap.applyₗ b ∘ₗ LinearMap.applyₗ a

@[simp] theorem ev_apply (a b : X) (β : LinearMap.BilinForm ℤ X) : ev a b β = β a b := rfl

def mono {K : Type} [Field K] (q : X → X → Kˣ) (n : X × X →₀ ℤ) : Kˣ := n.prod fun p k => q p.1 p.2 ^ k

end GlobalTheory.ConeMono
end
end

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ConeMono

noncomputable section

namespace GlobalTheory.MonoHom

variable {X : Type} [AddCommGroup X] {K : Type} [Field K]

def pform {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (e.coord i).smulRight (e.coord j)

@[simp] theorem pform_apply {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) (x y : X) :
    pform e i j x y = e.coord i x * e.coord j y := by
  simp [pform]

end GlobalTheory.MonoHom

namespace GlobalTheory.MonoHom

end GlobalTheory.MonoHom
end
end

section
open GlobalTheory.MonoHom

noncomputable section

namespace GlobalTheory.PerRoot

variable {X : Type} [AddCommGroup X]

def halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) : LinearMap.BilinForm ℤ X :=
  if i < j then pform e i j + pform e j i else if i = j then pform e i i else 0

theorem halfForm_symm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) (x y : X) :
    halfForm e i j x y = halfForm e i j y x := by
  unfold halfForm; split_ifs <;> simp [pform_apply] <;> ring

theorem halfForm_basis {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j i₀ j₀ : Fin r) :
    halfForm e i j (e i₀) (e j₀) = if i = min i₀ j₀ ∧ j = max i₀ j₀ then 1 else 0 := by
  unfold halfForm
  rcases lt_trichotomy i₀ j₀ with h | rfl | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · simp only [min_self, max_self]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega

theorem eq_sum_halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ x y, β x y = β y x) :
    β = ∑ p : Fin r × Fin r, β (e p.1) (e p.2) • halfForm e p.1 p.2 := by
  refine LinearMap.ext_basis e e fun i₀ j₀ => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, halfForm_basis, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (min i₀ j₀, max i₀ j₀)]
  · simp only [and_self, if_true]
    rcases le_total i₀ j₀ with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hβ]
  · intro p _ hp; rw [if_neg]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bimul_ext {G : Type} [CommGroup G] {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (f g : X → X → G)
    (hf : ∀ a a' b, f (a + a') b = f a b * f a' b) (hf' : ∀ a b b', f a (b + b') = f a b * f a b')
    (hg : ∀ a a' b, g (a + a') b = g a b * g a' b) (hg' : ∀ a b b', g a (b + b') = g a b * g a b')
    (h : ∀ i j, f (e i) (e j) = g (e i) (e j)) : f = g := by
  have key : ∀ (φ ψ : X → G), (∀ a a', φ (a + a') = φ a * φ a') → (∀ a a', ψ (a + a') = ψ a * ψ a') →
      (∀ i, φ (e i) = ψ (e i)) → φ = ψ := by
    intro φ ψ hφ hψ hi
    let Φ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (φ a)) (fun a a' => by simp [hφ])
    let Ψ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ψ a)) (fun a a' => by simp [hψ])
    have hL : Φ.toIntLinearMap = Ψ.toIntLinearMap := e.ext fun i => by simp [Φ, Ψ, hi]
    funext a
    have := congrArg (fun L : X →ₗ[ℤ] Additive G => Additive.toMul (L a)) hL
    simpa [Φ, Ψ] using this
  have h1 : ∀ j a, f a (e j) = g a (e j) := fun j => congrFun
    (key (fun a => f a (e j)) (fun a => g a (e j)) (fun a a' => hf a a' _) (fun a a' => hg a a' _) (fun i => h i j))
  funext a
  exact key (f a) (g a) (hf' a) (hg' a) (fun j => h1 j a)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsSymBasis (ε : ι → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ k x y, ε k x y = ε k y x) ∧ LinearIndependent ℤ ε ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → β ∈ Submodule.span ℤ (Set.range ε)

theorem exists_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X) :
    ∃ c : Fin r × Fin r → ι → ℤ, ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2 := by
  have : ∀ p : Fin r × Fin r, ∃ c : ι → ℤ, ∑ k, c k • ε k = halfForm e p.1 p.2 := fun p =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hε.2.2 _ (halfForm_symm e p.1 p.2))
  choose c hc using this
  exact ⟨c, hc⟩

theorem dual_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X)
    {c : Fin r × Fin r → ι → ℤ} (hc : ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2) (k' k : ι) :
    ∑ p, ε k' (e p.1) (e p.2) * c p k = if k' = k then 1 else 0 := by
  have h1 : ε k' = ∑ k, (∑ p, ε k' (e p.1) (e p.2) * c p k) • ε k := by
    conv_lhs => rw [eq_sum_halfForm e (ε k') (hε.1 k')]
    simp_rw [← hc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : ε k' = ∑ k, (if k' = k then (1 : ℤ) else 0) • ε k := by simp
  have h3 : ∑ k, ((∑ p, ε k' (e p.1) (e p.2) * c p k) - (if k' = k then 1 else 0)) • ε k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hε.2.1 _ h3 k)

variable {G : Type} [CommGroup G]

theorem zpow_sumF {κ : Type} (s : Finset κ) (a : G) (f : κ → ℤ) : a ^ (∑ p ∈ s, f p) = ∏ p ∈ s, a ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem eq_one_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (u : ι → G) (h : ∀ x y, ∏ k, u k ^ ε k x y = 1) (k : ι) : u k = 1 := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  calc u k = ∏ k', u k' ^ (if k' = k then (1 : ℤ) else 0) := by simp
    _ = ∏ k', u k' ^ (∑ p, ε k' (e p.1) (e p.2) * c p k) := by simp_rw [dual_coords hε e hc]
    _ = ∏ p, (∏ k', u k' ^ ε k' (e p.1) (e p.2)) ^ c p k := by
      simp_rw [← Finset.prod_zpow, zpow_sumF, ← zpow_mul]
      exact Finset.prod_comm
    _ = 1 := by simp [h]

theorem existsUnique_coeff {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (q : X → X → G) (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃! σ : ι → G, ∀ x y, q x y = ∏ k, σ k ^ ε k x y := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  have hF : ∀ x y, ∏ k, (∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y =
      ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X), q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y := by
    intro x y
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← zpow_sumF, ← hc p]
    simp [LinearMap.sum_apply, mul_comm]
  refine ⟨fun k => ∏ p, q (e p.1) (e p.2) ^ c p k, fun x y => ?_, fun σ hσ => funext fun k => ?_⟩
  · rw [hF]
    have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
        q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
      (fun a a' b => by simp only [map_add, LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
      (fun a b b' => by simp only [map_add, zpow_add, Finset.prod_mul_distrib])
      (fun i j => by
        simp only [halfForm_basis]
        rw [Finset.prod_eq_single (min i j, max i j)]
        · simp only [and_self, if_true, zpow_one]
          rcases le_total i j with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, hsym]
        · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
        · intro h; exact absurd (Finset.mem_univ _) h)
    exact congrFun (congrFun this x) y
  · have h0 : ∀ x y, ∏ k, (σ k / ∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y = 1 := fun x y => by
      simp_rw [div_zpow, Finset.prod_div_distrib, ← hσ, hF]
      rw [div_eq_one]
      have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
          q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
        (fun a a' b => by simp only [map_add, LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
        (fun a b b' => by simp only [map_add, zpow_add, Finset.prod_mul_distrib])
        (fun i j => by
          simp only [halfForm_basis]
          rw [Finset.prod_eq_single (min i j, max i j)]
          · simp only [and_self, if_true, zpow_one]
            rcases le_total i j with h | h
            · rw [min_eq_left h, max_eq_right h]
            · rw [min_eq_right h, max_eq_left h, hsym]
          · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
          · intro h; exact absurd (Finset.mem_univ _) h)
      exact congrFun (congrFun this x) y
    exact div_eq_one.1 (eq_one_of_prod_zpow hε _ h0 k)

theorem eq_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ε k x y = ∏ k, s' k ^ ε k x y) : s = s' := by
  funext k
  refine div_eq_one.1 (eq_one_of_prod_zpow hε (fun k => s k / s' k) (fun x y => ?_) k)
  simp_rw [div_zpow, Finset.prod_div_distrib, h, div_self']

theorem pow_eq_pow_of_prod {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (n : ℕ) (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ((n : ℤ) * ε k x y) = ∏ k, s' k ^ ((n : ℤ) * ε k x y)) (k : ι) :
    s k ^ n = s' k ^ n := by
  have := congrFun (eq_of_prod_zpow hε (fun k => s k ^ n) (fun k => s' k ^ n) fun x y => by
    simp_rw [← zpow_natCast, ← zpow_mul]; exact h x y) k
  exact this

theorem isSymBasis_mul : IsSymBasis (fun _ : Fin 1 => (LinearMap.mul ℤ ℤ : LinearMap.BilinForm ℤ ℤ)) := by
  refine ⟨fun _ x y => mul_comm x y, ?_, fun β _ => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h
    have := LinearMap.congr_fun₂ h 1 1
    simp at this
  · refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun _ => β 1 1, ?_⟩
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    have hx : x = x • (1 : ℤ) := by simp
    have hy : y = y • (1 : ℤ) := by simp
    rw [hx, hy, LinearMap.map_smul₂, LinearMap.map_smul]
    simp only [smul_eq_mul]; ring

example (s s' : ℚˣ) (h : ∀ x y : ℤ, s ^ ((3 : ℤ) * (x * y)) = s' ^ ((3 : ℤ) * (x * y))) : s ^ 3 = s' ^ 3 :=
  pow_eq_pow_of_prod isSymBasis_mul 3 (fun _ => s) (fun _ => s') (fun x y => by simpa using h x y) 0

end GlobalTheory.PerRoot
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerRoot

open IsDedekindDomain Polynomial

theorem exists_ord (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ v : (FractionRing V)ˣ →* Multiplicative ℤ,
      (∀ x : (FractionRing V)ˣ, 0 ≤ (v x).toAdd → ∃ a : V, algebraMap V _ a = (x : FractionRing V)) ∧
      ∀ (x : (FractionRing V)ˣ) (a : V), algebraMap V _ a = (x : FractionRing V) →
        (0 < (v x).toAdd ↔ a ∈ maximalIdeal V) := by
  let w := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hw : ∀ x : (FractionRing V)ˣ, w x ≠ 0 := fun x => by simp [w]
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd (-WithZero.log (w x))) fun x y => ?_, fun x hx => ?_,
    fun x a ha => ?_⟩
  · rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hw x) (hw y), neg_add]
  · refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_nonneg] at hx
    exact (WithZero.log_le_log (hw x) one_ne_zero).1 (by simpa using hx)
  · simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_pos]
    have h1 : WithZero.log (w x) < 0 ↔ w x < 1 := by
      simpa using WithZero.log_lt_log (hw x) one_ne_zero
    rw [h1, ← ha]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem _ a

theorem exists_nthRoots_ext (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {I : Type} [Fintype I] (a : I → V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (f : V →+* W) (s : I → W),
      Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ ∀ k, s k ^ n = f (a k) := by
  classical
  let K := FractionRing V
  haveI : CharZero K := algebraRat.charZero _
  let p : I → K[X] := fun k => X ^ n - C (algebraMap V K (a k))
  have hp : ∀ k, (p k).Monic := fun k => monic_X_pow_sub_C _ (by omega)
  let L := (∏ k, p k).SplittingField
  have hsp : ((∏ k, p k).map (algebraMap K L)).Splits := SplittingField.splits _
  have hroot : ∀ k, ∃ t : L, t ^ n = algebraMap K L (algebraMap V K (a k)) := fun k => by
    have h0 : (∏ k, p k).map (algebraMap K L) ≠ 0 :=
      ((monic_prod_of_monic _ _ fun k _ => hp k).map _).ne_zero
    have h1 : ((p k).map (algebraMap K L)).Splits :=
      hsp.of_dvd h0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
    obtain ⟨t, ht⟩ := h1.exists_eval_eq_zero (by
      rw [(hp k).degree_map, degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : n ≠ 0))
    refine ⟨t, ?_⟩
    simpa [p, sub_eq_zero] using ht
  choose t ht using hroot
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hs : ∀ k, t k ∈ Set.range (algebraMap W L) := fun k => hint _
    ⟨X ^ n - C (a k), monic_X_pow_sub_C _ (by omega), by simp [ht]⟩
  choose s hs using hs
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V W, s, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, fun k => IsFractionRing.injective W L ?_⟩
  rw [map_pow, hs, ht]
  exact (RingHom.congr_fun hc (a k)).symm

theorem exists_form {G X : Type} [CommGroup G] [AddCommGroup X] (v : G →* Multiplicative ℤ) (q : X → X → G)
    (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃ β : LinearMap.BilinForm ℤ X, ∀ x y, β x y = (v (q x y)).toAdd := by
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  let F : X → X →ₗ[ℤ] ℤ := fun x =>
    (AddMonoidHom.mk' (fun y => (v (q x y)).toAdd) fun y y' => by simp [hadd']).toIntLinearMap
  exact ⟨(AddMonoidHom.mk' F fun x x' => LinearMap.ext fun y => by simp [F, hadd]).toIntLinearMap,
    fun x y => rfl⟩

theorem isSymBasis_of_basis {X I : Type} [AddCommGroup X] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) X)) :
    IsSymBasis fun k => (ε k : LinearMap.BilinForm ℤ X) := by
  refine ⟨fun k => mem_balForms_int.1 (ε k).2, ε.linearIndependent.map' (Submodule.subtype _) (by simp),
    fun β hβ => ?_⟩
  have h := Submodule.mem_map_of_mem (f := (balForms (id : ℤ → ℤ) X).subtype)
    (ε.mem_span ⟨β, mem_balForms_int.2 hβ⟩)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

theorem exists_roots_of_periods : ∀ (g n : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → 1 ≤ n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (r : ℕ), r ≤ g → ∀ (q : (Fin r → ℤ) → (Fin r → ℤ) → (FractionRing V)ˣ), (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V, w ≠ 0 ∧ (q a a : FractionRing V) = algebraMap V _ w) → ∃ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))), IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x) ∧ ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (fK : FractionRing V →+* FractionRing V') (s : Fin m ⊕ Fin N → V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ ∀ a b, fK (q a b : FractionRing V) = ∏ k, algebraMap V' _ (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) := by
  intro g n φ hφ hn V _ _ _ hV hD r hr q hsym hadd hpos
  obtain ⟨-, -, hcomp, hchar⟩ := hV
  obtain ⟨v, hv1, hv2⟩ := exists_ord V
  obtain ⟨β, hβ⟩ := exists_form v q hsym hadd
  have hβs : ∀ x y, β x y = β y x := fun x y => by rw [hβ, hβ, hsym]
  have hβp : ∀ x, x ≠ 0 → 0 < β x x := fun x hx => by
    obtain ⟨w, hw, -, h⟩ := hpos x hx
    rw [hβ]
    exact (hv2 _ w h.symm).2 hw
  have hβn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hβp x hx).le
  obtain ⟨m, ga, c, hga, hc, hβc⟩ := GlobalTheory.ConeInterior.exists_pos_comb_int g φ hφ r hr β hβs
    (GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hβs) hβn)
  obtain ⟨N, ε, hε⟩ := hga.basis
  have hεga : ∀ k, (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) = ga k := fun k => by rw [hε]
  have hsb := isSymBasis_of_basis ε
  obtain ⟨u, hu, -⟩ := existsUnique_coeff hsb q hsym hadd
  have hβv : ∀ x y, β x y = ∑ j, (c j : ℤ) * ga j x y := fun x y => by
    rw [hβc]; simp [LinearMap.sum_apply]
  have hvu : (fun k => v (u k)) = fun k => Multiplicative.ofAdd (Sum.elim (fun j => (c j : ℤ)) 0 k) := by
    refine eq_of_prod_zpow hsb _ _ fun x y => ?_
    simp_rw [← map_zpow, ← map_prod, ← hu]
    apply Multiplicative.toAdd.injective
    rw [← hβ, hβv, toAdd_prod, Fintype.sum_sum_type]
    simp [hεga, mul_comm]
  have hvk : ∀ k, (v (u k)).toAdd = Sum.elim (fun j => (c j : ℤ)) 0 k := fun k => by
    rw [congrFun hvu k]; rfl
  choose a ha using fun k => hv1 (u k) (by rw [hvk]; cases k <;> simp)
  have ha0 : ∀ k, a k ≠ 0 := fun k h => (u k).ne_zero (by rw [← ha, h, map_zero])
  obtain ⟨W, _, _, _, _, f, s, hinj, hfin, hloc, hs⟩ := exists_nthRoots_ext V a hn
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hinj
  have hfK : ∀ b, IsFractionRing.lift (K := FractionRing V) hinj' (algebraMap V _ b) =
      algebraMap W (FractionRing W) (f b) := fun b => IsFractionRing.lift_algebraMap hinj' b
  refine ⟨m, N, ε, by simpa only [hεga] using hga, fun x hx => ?_, W, inferInstance, inferInstance, inferInstance, f,
    IsFractionRing.lift hinj', s, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, inferInstance, hinj, hfin, hloc,
    hfK, fun k => ⟨?_, fun h => ?_⟩, fun k => ?_, fun x y => ?_⟩
  · by_contra h
    push_neg at h
    have h1 := hβp x hx
    rw [hβv] at h1
    exact h1.not_ge (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hεga j ▸ h j))
  · exact charZero_of_injective_ringHom hinj
  · have h1 : a (.inl k) ∈ maximalIdeal V := (hv2 _ _ (ha _)).1 (by rw [hvk]; simpa using hc k)
    intro h
    exact h1 (isUnit_of_map_unit f _ (hs _ ▸ h.pow n))
  · refine ha0 (.inl k) (hinj ?_)
    rw [← hs, h, map_zero, zero_pow (by omega)]
  · have h1 : a (.inr k) ∉ maximalIdeal V := fun h => by
      have := (hv2 _ _ (ha _)).2 h
      rw [hvk] at this
      simp at this
    have h2 : IsUnit (s (.inr k) ^ n) := hs _ ▸ (not_not.1 h1 : IsUnit (a (.inr k))).map f
    exact (isUnit_pow_iff (by omega)).1 h2
  · rw [hu, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, hfK, ← hs, map_pow, zpow_mul, zpow_natCast]

end GlobalTheory.PerRoot
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TraitExt

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in

theorem exists_pull_gen {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (U' : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left)
      (πK : pullback ((Over.pullback (spMap g)).obj G).hom (jK R') ⟶ pullback G.hom (jK R)),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      πK ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (spMap g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) ∧
      U'.gen.hom.left ≫ gA = πK ≫ U.gen.hom.left := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hU', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  refine ⟨D', hD, A', U', gA, eA.hom.left ≫ gA ≫ U.gen.inv.left, gpA, LBIso.symm tA, ?_, ?_⟩
  · simpa only [Category.assoc] using heA
  · rw [hU']; simp only [Category.assoc, hgi, Category.comp_id]

end GlobalTheory.TraitExt

namespace GlobalTheory.TraitExt

end GlobalTheory.TraitExt
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.TraitExt

open GlobalTheory.ArcPull in

theorem exists_unifAlong_pullTo : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f : T.V →+* V₂), IsCN V₂ → IsDiscreteValuationRing V₂ → Function.Injective f → f.Finite → IsLocalHom f → ∃ (D' : DegData V₂ (maximalIdeal V₂)) (_ : IsPullDeg f T.D.toPre D'.toPre) (G' : Over (Sp V₂)) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V₂))) (U' : Unif (maximalIdeal V₂) D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' := by
  intro g n F T V₂ _ _ _ f hCN _ hinj hfin hloc
  obtain ⟨hN, hIC, hW, hC⟩ := hCN
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have hR' : AdmBase V₂ (maximalIdeal V₂) := ⟨hN, inferInstance, hIC, hW⟩
  have hI : (maximalIdeal T.V).map f ≤ maximalIdeal V₂ :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit f a ha
  obtain ⟨D', hD, A', U', gA, πK, gpA, tA, hK, hgen⟩ := exists_pull_gen hR hR' f hinj hI T.semi T.U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ T.A.A A'.A gA gpA
  have sq : spMap (fracMap hinj) ≫ jK T.V = jK V₂ ≫ spMap f :=
    (fracMap_sq hinj).symm.trans (Category.id_comp _)
  refine ⟨D', hD, (Over.pullback (spMap f)).obj T.G, inferInstance, inferInstance, pullback.fst T.G.hom (spMap f),
    A', U', ?_⟩
  refine ⟨isGrpPullback_pullback T.G (spMap f), spMap (fracMap hinj), πK, gA ≫ T.α, β₂ ≫ T.α₂, sq, hK,
    gpA.comp T.cart, isSquare_comp hβ₂ T.sq, hΛ T.A.L A'.L _ F.univ.P T.α₂ T.A.isLB A'.isLB F.univ.isLB tA T.lb, ?_⟩
  rw [← Category.assoc, hgen, Category.assoc]

end GlobalTheory.TraitExt
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_degFrom_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  intro g hg φ hφ n hn hodd F T b hb
  have hV : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  let e₀ : (Fin (Module.finrank ℤ T.D.toPre.X) → ℤ) ≃+ T.D.toPre.X :=
    (Module.finBasis ℤ T.D.toPre.X).equivFun.symm.toAddEquiv
  have hc : ∀ a a', T.D.toPre.c (e₀ (a + a')) = T.D.toPre.c (e₀ a) * T.D.toPre.c (e₀ a') := fun a a' => by
    rw [map_add]; exact T.D.toPre.c_add _ _
  obtain ⟨L, V₁, _, _, _, f₁, κ₁, e, hLh, hCN₁, hDVR₁, hi₁, hf₁, hl₁, hκ₁, hb₁, B', _, β', β'', β₂, β₂', p₁, p₂, s₁, s₂,
    lb, pts⟩ := GlobalTheory.T.exists_lower_base_of_trait_abelian_part n hn hodd T.V hV inferInstance b T.D.toPre.P _ (fun a => T.D.toPre.c (e₀ a)) hc
  have hr : L.T.r = Module.finrank ℤ T.D.toPre.X := by
    simpa using LinearEquiv.finrank_eq e.toIntLinearEquiv
  have hgen : L.h + L.T.r = g := by rw [hLh, hr]; exact GlobalTheory.Poinc.Trait.dim_add_rank (by omega) F T
  obtain ⟨q, hqs, hqa, hqp, hq⟩ := GlobalTheory.T.exists_pulledBack_periods_basePeriods_constForm n T.V T.D _ e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV inferInstance hCN₁ hDVR₁ hi₁ hf₁
    hl₁ hκ₁ p₁ p₂ s₁ s₂ lb pts
  obtain ⟨m, N, ε, hcone, hdef, V₂, _, _, _, f₂, fK, s, hCN₂, hDVR₂, hi₂, hf₂, hl₂, hfK, hs₁, hs₂, hqs'⟩ :=
    GlobalTheory.PerRoot.exists_roots_of_periods g n φ hφ (by omega) V₁ hCN₁ hDVR₁ L.T.r (by omega) q hqs hqa hqp
  have hl : IsLocalHom (f₂.comp f₁) := RingHom.isLocalHom_comp f₂ f₁
  have hlκ : IsLocalHom (f₂.comp κ₁) := RingHom.isLocalHom_comp f₂ κ₁
  obtain ⟨D', hD, G', _, _, π, A', U', hU⟩ :=
    GlobalTheory.TraitExt.exists_unifAlong_pullTo F T V₂ (f₂.comp f₁) hCN₂ hDVR₂ (hi₂.comp hi₁) (hf₂.comp hf₁) hl
  refine ⟨L, m, N, ε, V₂, inferInstance, inferInstance, inferInstance, f₂.comp f₁, f₂.comp κ₁, s, D',
    hD.xe.trans (e₀.symm.trans e.symm), G', inferInstance, inferInstance, π, A', U', hgen, hcone, hdef, hCN₂, hDVR₂,
    hi₂.comp hi₁, hf₂.comp hf₁, hl, hlκ, ?_, hs₁, hs₂, hU, ?_⟩
  · rw [RingHom.comp_assoc, hb₁, ← RingHom.comp_assoc]
  · exact hq V₂ f₂ fK s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) hCN₂ hi₂ hf₂ hl₂ hfK hqs' D' hD

end GlobalTheory.TChart
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  atlas_forward_decl GlobalTheory.TChart.exists_degFrom_of_trait
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem lbIso_pull_both {X X' Y Z : Scheme.{0}} {L : LB X} {M : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'}
    (h : LBIso (L.pull a) (M.pull b)) (j : Z ⟶ Y) {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = j ≫ a) (eb : b' = j ≫ b) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => ea)
    (Geo.Tor.chartPullSame M _ (fun _ => b) _ j fun _ => eb) h

theorem isSquare_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ' b) (e : φ = φ') : a = b := by
  subst e
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

set_option backward.isDefEq.respectTransparency false in

theorem IsMumPol.exists_isMumfordFam {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R]
    [IsDomain R] [IsLocalRing R] {Q : Data R} {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] {P : LB (G2 G₁).left}
    (h : IsMumPol Q G₁ P) {T : Scheme.{0}} {i : T ⟶ Sp R} {l : Sp (FractionRing R) ⟶ T} (hl : l ≫ i = jK R)
    {A₀ : Over T} [GrpObj A₀] [IsCommMonObj A₀] {P₀ : LB (G2 A₀).left} (hP₀ : P₀.IsLB)
    {a : A₀.left ⟶ G₁.left} {a₂ : (G2 A₀).left ⟶ (G2 G₁).left} (ha : IsGrpPullback A₀ G₁ i a) (ha₂ : IsSquare a a₂)
    (hPa : LBIso P₀ (P.pull a₂)) {yU : T ⟶ F.X} {φ : A₀.left ⟶ F.univ.A.left} {φ₂ : (G2 A₀).left ⟶ (G2 F.univ.A).left}
    (hφ : IsGrpPullback A₀ F.univ.A yU φ) (hφ₂ : IsSquare φ φ₂) (hPφ : LBIso P₀ (F.univ.P.pull φ₂)) :
    ∃ α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left, IsGenFibre F (l ≫ yU) α₁ ∧ IsMumfordFam F (l ≫ yU) α₁ Q := by
  obtain ⟨hR, hpos, -, hbi, hU⟩ := h
  have w : pullback.fst G₁.hom (jK R) ≫ G₁.hom = (pullback.snd G₁.hom (jK R) ≫ l) ≫ i := by
    rw [Category.assoc, hl, pullback.condition]
  obtain ⟨ω, ω₁, ω₂⟩ : ∃ ω : pullback G₁.hom (jK R) ⟶ A₀.left, ω ≫ a = pullback.fst G₁.hom (jK R) ∧
      ω ≫ A₀.hom = pullback.snd G₁.hom (jK R) ≫ l := ⟨ha.1.lift _ _ w, ha.1.lift_fst _ _ w, ha.1.lift_snd _ _ w⟩
  have h₁ := isGrpPullback_pullback G₁ (jK R)
  have hω : IsGrpPullback ((Over.pullback (jK R)).obj G₁) A₀ l ω := ha.cancel (h₁.congr hl.symm ω₁.symm) ω₂
  refine ⟨ω ≫ φ, hω.comp hφ, hR, hpos, fun R' _ _ _ ρ hR' hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, π₂, A, U, hπ, hπ₂, hL⟩ := hU R' ρ hR' hρ hf D ε hD
  obtain ⟨κ, hκ⟩ := exists_genericMap hρ
  letI := A.isAb.comm
  have w' : (pullback.fst G'.hom (jK R') ≫ π) ≫ G₁.hom = (pullback.snd G'.hom (jK R') ≫ κ) ≫ jK R := by
    rw [Category.assoc, hπ.1.w, Category.assoc, hκ, pullback.condition_assoc]
  obtain ⟨πK, p₁, p₂⟩ : ∃ πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R),
      πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
      πK ≫ pullback.snd G₁.hom (jK R) = pullback.snd G'.hom (jK R') ≫ κ :=
    ⟨pullback.lift _ _ w', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h₂ := isGrpPullback_pullback G' (jK R')
  have hπK : IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G₁) κ πK :=
    h₁.cancel ((h₂.comp hπ).congr hκ.symm p₁.symm) p₂
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hi := isGrpPullback_of_iso U.gen.symm
  have e₁ : U.gen.hom.left ≫ U.gen.symm.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.hom_inv_id, Over.id_left]
  have e₂ : U.gen.symm.hom.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.inv_hom_id, Over.id_left]
  have hβ := hi.comp (hπK.comp hω)
  have hδ := hi.comp h₂
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂, IsSquare _ β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, IsSquare _ δ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hδ.1.w⟩
  have r : LBIso A.L (U.LG.L.pull (U.gen.symm.hom.left ≫ pullback.fst G'.hom (jK R'))) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.chartPull (chartPullId A.L) (Geo.Tor.chartPullPull A.L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl A.isLB))
      (lbIso_pull_both U.ext U.gen.symm.hom.left e₂.symm rfl)
  have l₁ := GlobalTheory.LamPull.lbIso_lam_pull hδ U.LG.isLB A.isLB r hδ₂
  have i₁ : (abelian₂ G' U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have i₀ : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have e₃ : β₂ ≫ a₂ = δ₂ ≫ π₂ := isSquare_eq (isSquare_comp hβ₂ ha₂) (isSquare_comp hδ₂ hπ₂) (by
    simp only [Category.assoc]
    rw [ω₁, p₁])
  have l₂ := lbIso_pull_comp hL δ₂ e₃
  have l₃ := (lbIso_pull_comp hPa β₂ rfl).symm
  have l₄ := lbIso_pull_comp hPφ β₂ rfl
  refine ⟨G', inferInstance, inferInstance, π, A, U, hπ, κ, πK, (U.gen.symm.hom.left ≫ πK ≫ ω) ≫ φ, β₂ ≫ φ₂, hκ, p₁,
    (hβ.comp hφ).congr (by simp only [Category.id_comp, Category.assoc]) rfl, isSquare_comp hβ₂ hφ₂,
    LBIso.trans i₀ (pull_isLB i₁ _) (pull_isLB F.univ.isLB _) l₁
      (LBIso.trans (pull_isLB i₁ _) (pull_isLB hbi.1 _) (pull_isLB F.univ.isLB _) l₂
        (LBIso.trans (pull_isLB hbi.1 _) (pull_isLB hP₀ _) (pull_isLB F.univ.isLB _) l₃ l₄)), ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc, e₁, Category.id_comp]

theorem dense_generic_away {o R : Type} [CommRing o] [CommRing R] [IsDomain R] {b : o →+* R} (hb : Function.Injective b)
    {f : R} (hf : f ≠ 0) :
    Dense {x : Sp (Localization.Away f) | (spMap ((algebraMap R (Localization.Away f)).comp b) x).asIdeal = ⊥} := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective ((algebraMap R (Localization.Away f)).comp b) :=
    (IsLocalization.injective (Localization.Away f) hle).comp hb
  let p : PrimeSpectrum (Localization.Away f) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : Dense ({p} : Set (PrimeSpectrum (Localization.Away f))) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [p]
  refine Dense.mono ?_ hp
  rintro x rfl
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj

set_option backward.isDefEq.respectTransparency false in

theorem Taut.exists_isFam_of_siegPre : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  intro g n φ hn _ F C G₁ _ _ P hM hab c hc ⟨a, a₂, ha, ha₂, hPa⟩
  obtain ⟨-, -, hinj, -, hrel, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  have hf : ∏ k, C.t k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ne_zero_of_isRelParam hrel i
  haveI : IsDomain (Localization.Away (∏ k, C.t k)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  obtain ⟨yU, hs, hPB⟩ := F.rep _ _ c inferInstance (dense_generic_away hinj hf) hc
  have hu : IsUnit (algebraMap C.R (FractionRing C.R) (∏ k, C.t k)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R _)).2 hf)
  let l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R := IsLocalization.Away.lift _ hu
  have hl : l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) :=
    IsLocalization.Away.lift_comp _ hu
  have hl' : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    rw [← Geo.Tor.spMap_comp, hl]
  obtain ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩ := hPB
  obtain ⟨α₁, hα, hF⟩ := hM.exists_isMumfordFam F hl' c.isLB ha ha₂ hPa h₁ h₂ h₃
  refine ⟨spMap l ≫ yU, α₁, yU, l, ⟨hM.2.2.1, hab, hα, hF, ?_⟩, ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩, hl, rfl⟩
  rw [Category.assoc, hs, Geo.Tor.spMap_comp, ← Category.assoc, hl']

end GlobalTheory.TChart
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelLevelStructure_mumfordFamily_tautological : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  atlas_forward_decl GlobalTheory.TChart.Taut.exists_isFam_of_siegPre
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.FromEx

section Base

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev Bp : Over (Sp V) := (Over.pullback (spMap iw)).obj T.B

theorem isAb_Bp : IsAbelianScheme (Bp T iw) := GlobalTheory.isAbelianScheme_pullback_obj _ _ T.isAb

instance : IsCommMonObj (Bp T iw) := (isAb_Bp T iw).comm

theorem cart : IsGrpPullback (Bp T iw) T.B (spMap iw) (pullback.fst T.B.hom (spMap iw)) := isGrpPullback_pullback T.B _

abbrev cm : CubeMap (Bp T iw) T.B := cubeMapOf (cart T iw)

theorem pullSt : ∃ (hL : (T.M.L.pull (cm T iw).F).IsLB) (hr : ((cm T iw).rigPull T.M.L T.M.rig).IsGen),
    (∃ c' : CubicalStr (Bp T iw) ((cm T iw).rigLB T.M hL hr), (cm T iw).IsPullCubical c' T.cub) ∧
      (T.M.IsSymmetric → ((cm T iw).rigLB T.M hL hr).IsSymmetric) :=
  proved_CubePullSt _ _ T.B (Bp T iw) (cm T iw) T.M T.cub

abbrev Mp : RigLB (Bp T iw) := (cm T iw).rigLB T.M (pullSt T iw).fst (pullSt T iw).snd.fst

abbrev cubP : CubicalStr (Bp T iw) (Mp T iw) := CubePf.cubical (cm T iw) T.M T.cub _ _

example : (Mp T iw).L = T.M.L.pull (pullback.fst T.B.hom (spMap iw)) := rfl

end Base

section Pts

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev push (Tt : Over (Sp V)) : (Tt ⟶ Bp T iw) →* (Over.mk (Tt.hom ≫ spMap iw) ⟶ T.B) := pushHom (cart T iw) Tt

theorem push_inj {Tt : Over (Sp V)} {x y : Tt ⟶ Bp T iw} (h : push T iw Tt x = push T iw Tt y) : x = y := by
  apply Over.OverMorphism.ext
  apply (cart T iw).1.hom_ext
  · exact congrArg (fun q => q.left) h
  · rw [Over.w x, Over.w y]

def pullPt {Tt : Over (Sp V)} (q : Over.mk (Tt.hom ≫ spMap iw) ⟶ T.B) : Tt ⟶ Bp T iw :=
  Over.homMk ((cart T iw).1.lift q.left Tt.hom (Over.w q)) ((cart T iw).1.lift_snd _ _ _)

theorem push_pullPt {Tt : Over (Sp V)} (q : Over.mk (Tt.hom ≫ spMap iw) ⟶ T.B) : push T iw Tt (pullPt T iw q) = q :=
  Over.OverMorphism.ext ((cart T iw).1.lift_fst _ _ _)

def cp (a : Fin T.r → ℤ) : 𝟙_ (Over (Sp V)) ⟶ Bp T iw := pullPt T iw (toUnit _ ≫ T.c₀ a)

theorem push_cp (a : Fin T.r → ℤ) : push T iw _ (cp T iw a) = toUnit _ ≫ T.c₀ a := push_pullPt T iw _

theorem cp_add (a a' : Fin T.r → ℤ) : cp T iw (a + a') = cp T iw a * cp T iw a' :=
  push_inj T iw (by rw [map_mul, push_cp, push_cp, push_cp, T.c₀_add, MonObj.comp_mul])

theorem left_of_push {Tt : Over (Sp V)} {z : Tt ⟶ Bp T iw} {z₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (h : push T iw Tt z = toUnit _ ≫ z₀) : z.left ≫ pullback.fst T.B.hom (spMap iw) = (Tt.hom ≫ spMap iw) ≫ z₀.left := by
  have := congrArg (fun q => q.left) h
  simp only [Over.comp_left, TautEx.toUnit_left] at this
  exact this

theorem lam_comm {Tt : Over (Sp V)} {x y : Tt ⟶ Bp T iw} {x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (hx : push T iw Tt x = toUnit _ ≫ x₀) (hy : push T iw Tt y = toUnit _ ≫ y₀) (k : Fin 4) :
    lamPts x y k ≫ pullback.fst T.B.hom (spMap iw) = (Tt.hom ≫ spMap iw) ≫ lamPts x₀ y₀ k := by
  fin_cases k
  · exact left_of_push T iw (by rw [map_mul, hx, hy, MonObj.comp_mul])
  · exact left_of_push T iw hx
  · exact left_of_push T iw hy
  · exact left_of_push T iw (by rw [map_one, MonObj.comp_one])

theorem push_pre {Tt Tt' : Over (Sp V)} (U : Tt' ⟶ Tt) {x : Tt ⟶ Bp T iw} {x₀ : 𝟙_ (Over (Sp W)) ⟶ T.B}
    (hx : push T iw Tt x = toUnit _ ≫ x₀) : push T iw Tt' (U ≫ x) = toUnit _ ≫ x₀ := by
  apply Over.OverMorphism.ext
  have := left_of_push T iw hx
  show (U ≫ x).left ≫ pullback.fst T.B.hom (spMap iw) = _
  rw [Over.comp_left, Over.comp_left, TautEx.toUnit_left, Category.assoc, this, ← Category.assoc, ← Category.assoc,
    Over.w U]
  rfl

end Pts

section Charts

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

open Classical in

def Jd {Tt : Over (Sp V)} (z : Tt.left) (J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι) :
    (Tt.left ⟶ T.B.left) → T.M.L.ι := fun χ =>
  if hχ : χ ≫ T.B.hom = Tt.hom ≫ spMap iw then J ((cart T iw).1.lift χ Tt.hom hχ) PUnit.unit
  else (exists_chart T.M.isLB (χ z)).choose

theorem Jd_eq {Tt : Over (Sp V)} (z : Tt.left) (J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι)
    (ψ : Tt.left ⟶ (Bp T iw).left) (hψ : ψ ≫ (Bp T iw).hom = Tt.hom) :
    Jd T iw z J (ψ ≫ pullback.fst T.B.hom (spMap iw)) = J ψ PUnit.unit := by
  have hχ : (ψ ≫ pullback.fst T.B.hom (spMap iw)) ≫ T.B.hom = Tt.hom ≫ spMap iw := by
    rw [Category.assoc, (cart T iw).1.w, ← Category.assoc, hψ]
  rw [Jd, dif_pos hχ]
  congr 1
  exact (cart T iw).1.hom_ext ((cart T iw).1.lift_fst _ _ _) (((cart T iw).1.lift_snd _ _ _).trans hψ.symm)

theorem Jd_good {Tt : Over (Sp V)} {z : Tt.left} {J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) : Good T.M.L z (Jd T iw z J) := by
  intro χ
  by_cases hχ : χ ≫ T.B.hom = Tt.hom ≫ spMap iw
  · have := mem_pull.1 (hJ ((cart T iw).1.lift χ Tt.hom hχ))
    rw [Jd, dif_pos hχ]
    have h2 : ((cart T iw).1.lift χ Tt.hom hχ ≫ pullback.fst T.B.hom (spMap iw)) z ∈
        T.M.L.U (J ((cart T iw).1.lift χ Tt.hom hχ) PUnit.unit) := this
    rw [(cart T iw).1.lift_fst χ Tt.hom hχ] at h2
    exact h2
  · rw [Jd, dif_neg hχ]
    exact (exists_chart T.M.isLB (χ z)).choose_spec

theorem val_pullAlong {Tt : Over (Sp V)} {Y₀ Y : Scheme.{0}} {K : Type} [Fintype K]
    (h : Y ⟶ Y₀) (φ : K → (Y₀ ⟶ T.B.left)) (ε : K → ℤ) (ψ : K → (Y ⟶ (Bp T iw).left))
    (hψ : ∀ k, ψ k ≫ pullback.fst T.B.hom (spMap iw) = h ≫ φ k) (t : LB.Gen (LB.LinComb T.M.L φ ε)) (r : Tt.left ⟶ Y)
    (hw : ∀ k, r ≫ ψ k ≫ (Bp T iw).hom = Tt.hom) {z : Tt.left} {J : (Tt.left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (spMap iw)) h φ ε ψ hψ t) r z J = val t (r ≫ h) z (Jd T iw z J) := by
  have hz := hJ.mem ψ r
  refine ((gm_res r z _ hz _).trans (gm_pull r h z _ (GeneratorPullback.pullAlong_le T.M.L _ h φ ψ hψ _ hz) _)).trans ?_
  refine (val_of t (r ≫ h) z (Jd T iw z J) _ fun k => ?_).symm
  rw [Category.assoc, ← hψ k, ← Category.assoc, Jd_eq T iw z J _ (by rw [Category.assoc, hw k])]

end Charts

section Tau

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev cK (x : Fin T.r → ℤ) : TK V ⟶ Bp T iw := toUnit _ ≫ cp T iw x

theorem push_cK (x : Fin T.r → ℤ) : push T iw _ (cK T iw x) = toUnit _ ≫ T.c₀ x := push_pre T iw _ (push_cp T iw x)

def uT (x y : Fin T.r → ℤ) : LB.Gen (LB.LinComb (Mp T iw).L (lamPts (cK T iw x) (cK T iw y)) negε) :=
  GeneratorPullback.pullAlong T.M.L (pullback.fst T.B.hom (spMap iw)) ((TK V).hom ≫ spMap iw) (lamPts (T.c₀ x) (T.c₀ y)) negε _
    (lam_comm T iw (push_cK T iw x) (push_cK T iw y)) (T.τ₀ x y)

theorem isGen_uT (x y : Fin T.r → ℤ) : (uT T iw x y).IsGen :=
  LBxP.isGen_pullAlong T.M.L _ _ _ _ _ _ (T.τ₀ x y) (T.τ₀_gen x y)

theorem val_uT (x y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (uT T iw x y) (𝟙 _) z J = val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) := by
  have h₂ := val_pullAlong T iw ((TK V).hom ≫ spMap iw) (lamPts (T.c₀ x) (T.c₀ y)) negε
    (lamPts (cK T iw x) (cK T iw y)) (lam_comm T iw (push_cK T iw x) (push_cK T iw y)) (T.τ₀ x y) (𝟙 _)
    (fun k => by rw [Category.id_comp]; exact TautEx.lamPts_w _ _ k) hJ
  rw [Category.id_comp] at h₂
  exact h₂

theorem uT_symm (x y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) : val (uT T iw x y) (𝟙 _) z J = val (uT T iw y x) (𝟙 _) z J := by
  rw [val_uT T iw x y hJ, val_uT T iw y x hJ, val_corr (Jd_good T iw hJ) (corr_of_val T.M.isLB (T.τ₀_symm x y))]

theorem tautBaseChange_tripleLift_left (x x' y : Fin T.r → ℤ) :
    (lift (cK T iw x) (lift (cK T iw x') (cK T iw y))).left ≫ (cm T iw).F3 =
      ((TK V).hom ≫ spMap iw) ≫ (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left := by
  apply hom_ext_triple
  intro i
  have hL : (lift (cK T iw x) (lift (cK T iw x') (cK T iw y))).left ≫ (x3 (Bp T iw) i).left =
      (lift (cK T iw x) (lift (cK T iw x') (cK T iw y)) ≫ x3 (Bp T iw) i).left := rfl
  have hR : (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left ≫ (x3 T.B i).left =
      (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y)) ≫ x3 T.B i).left := rfl
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, hL, Category.assoc ((TK V).hom ≫ spMap iw), hR]
  obtain ⟨e₀, e₁, e₂⟩ := TautEx.triple_lift_comp_projections (cK T iw x) (cK T iw x') (cK T iw y)
  obtain ⟨f₀, f₁, f₂⟩ := TautEx.triple_lift_comp_projections (T.c₀ x) (T.c₀ x') (T.c₀ y)
  match i with
  | 0 => rw [e₀, f₀]; exact left_of_push T iw (push_cK T iw x)
  | 1 => rw [e₁, f₁]; exact left_of_push T iw (push_cK T iw x')
  | 2 => rw [e₂, f₂]; exact left_of_push T iw (push_cK T iw y)

theorem uT_add (x x' y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (uT T iw (x + x') y) (𝟙 _) z J * cubV (cubP T iw) z J (cK T iw x) (cK T iw x') (cK T iw y) =
      val (uT T iw x y) (𝟙 _) z J * val (uT T iw x' y) (𝟙 _) z J := by
  have hc : cubV (cubP T iw) z J (cK T iw x) (cK T iw x') (cK T iw y) = val T.cub.t
      (((TK V).hom ≫ spMap iw) ≫ (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left) z (Jd T iw z J) := by
    refine (val_pullAlong T iw (cm T iw).F3 (thφ T.B (x3 T.B)) thε (thφ (Bp T iw) (x3 (Bp T iw)))
      (fun I => (cm T iw).psum_comm I.down) T.cub.t (lift (cK T iw x) (lift (cK T iw x') (cK T iw y))).left
      (fun I => ?_) hJ).trans ?_
    · show _ ≫ (psum _ _ _).left ≫ _ = _
      rw [Over.w, Over.w]
    · exact congrArg (fun r => val T.cub.t r z (Jd T iw z J)) (tautBaseChange_tripleLift_left T iw x x' y)
  have corr := corr_of_val T.M.isLB
    (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (x + x') y)
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ x y) (T.τ₀ x' y)) (fun y₁ J' hJ' =>
      (val_mul hJ' _ _ _).trans (Eq.trans (congrArg (_ * ·) ((val_pull hJ' _ _ _).trans
        (congrArg (fun r => val T.cub.t r y₁ J') (Category.id_comp _)))) ((T.τ₀_add x x' y y₁ J' hJ').trans
          (val_mul hJ' _ _ _).symm)))
  have hJd := Jd_good T iw hJ
  have e : val (T.τ₀ (x + x') y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) *
      val T.cub.t (((TK V).hom ≫ spMap iw) ≫ (lift (T.c₀ x) (lift (T.c₀ x') (T.c₀ y))).left) z (Jd T iw z J) =
      val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) *
        val (T.τ₀ x' y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J) :=
    (congrArg (_ * ·) (val_pull hJd _ _ _).symm).trans ((val_mul hJd _ _ _).symm.trans
      ((val_corr hJd corr _).trans (val_mul hJd _ _ _)))
  rw [val_uT T iw _ _ hJ, val_uT T iw _ _ hJ, val_uT T iw _ _ hJ, hc]
  exact e

end Tau

section Periods

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V) {I : Type} [Fintype I] (s : I → V) (hs : ∀ k, s k ≠ 0)
  (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ)

def kU (a b : Fin T.r → ℤ) : (FractionRing V)ˣ :=
  ∏ k, (Units.mk0 (algebraMap V (FractionRing V) (s k)) fun h =>
    hs k (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))) ^ ((n : ℤ) * ε k a b)

theorem kU_val (a b : Fin T.r → ℤ) :
    (kU T s hs ε n a b : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i a b) := by
  simp [kU]

theorem kU_symm (hε : ∀ k a b, ε k a b = ε k b a) (a b : Fin T.r → ℤ) : kU T s hs ε n a b = kU T s hs ε n b a := by
  simp only [kU, hε _ a b]

theorem kU_add (a a' b : Fin T.r → ℤ) : kU T s hs ε n (a + a') b = kU T s hs ε n a b * kU T s hs ε n a' b := by
  simp only [kU, ← Finset.prod_mul_distrib, ← zpow_add, map_add, LinearMap.add_apply, mul_add]

def tauF (a b : Fin T.r → ℤ) :
    LB.Gen (LB.LinComb (Mp T iw).L (lamPts (cK T iw ((n : ℤ) • a)) (cK T iw ((n : ℤ) • b))) negε) :=
  TautEx.mulU (unitOn (kU T s hs ε n a b)) (uT T iw ((n : ℤ) • a) ((n : ℤ) • b))

theorem val_tauF (a b : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) : val (tauF T iw s hs ε n a b) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitOn (kU T s hs ε n a b)) * val (uT T iw ((n : ℤ) • a) ((n : ℤ) • b)) (𝟙 _) z J :=
  TautEx.val_mulU (L := (Mp T iw).L) _ _ (𝟙 _) z J hJ

theorem tauF_add (a a' b : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι}
    (hJ : Good (Mp T iw).L z J) :
    val (tauF T iw s hs ε n (a + a') b) (𝟙 _) z J *
        cubV (cubP T iw) z J (cK T iw ((n : ℤ) • a)) (cK T iw ((n : ℤ) • a')) (cK T iw ((n : ℤ) • b)) =
      val (tauF T iw s hs ε n a b) (𝟙 _) z J * val (tauF T iw s hs ε n a' b) (𝟙 _) z J := by
  have h := uT_add T iw ((n : ℤ) • a) ((n : ℤ) • a') ((n : ℤ) • b) hJ
  rw [← smul_add] at h
  rw [val_tauF T iw s hs ε n _ _ hJ, val_tauF T iw s hs ε n _ _ hJ, val_tauF T iw s hs ε n _ _ hJ, kU_add,
    TautEx.unitOn_mul, map_mul]
  exact TautEx.alg_step h

theorem pGen_Mp : PGen (L := T.M.L) (F := pullback.fst T.B.hom (spMap iw)) (CubePf.idIsoL (Mp T iw).L) :=
  (isGen_iff _).1 (CubePf.idIsoL_isGen (Mp T iw).isLB)

def dataF (hε : ∀ k a b, ε k a b = ε k b a) : Data V where
  B := Bp T iw
  isAb := isAb_Bp T iw
  g := T.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange T.g).of_isPullback (IsPullback.of_hasPullback _ _)
    T.smoothDim
  M := Mp T iw
  cub := cubP T iw
  ample := relAmple_pull (cart T iw).1 T.M.isLB (Mp T iw).isLB (pGen_Mp T iw) ⊤ (isAffineOpen_top _) (fun _ => trivial)
    T.ample
  ktriv := kTriv_pull (cart T iw) T.M.isLB (Mp T iw).isLB (pGen_Mp T iw) T.ktriv
  X := Fin T.r → ℤ
  c a := cp T iw ((n : ℤ) • a)
  c_add a a' := by rw [smul_add]; exact cp_add T iw _ _
  tau := tauF T iw s hs ε n
  tau_gen a b := TautEx.isGen_mulU _ (isGen_uT T iw _ _)
  tau_symm a b _ _ hJ := by
    rw [val_tauF T iw s hs ε n a b hJ, val_tauF T iw s hs ε n b a hJ, kU_symm T s hs ε n hε a b, uT_symm T iw _ _ hJ]
  tau_add a a' b _ _ hJ := tauF_add T iw s hs ε n a a' b hJ

end Periods

section abelian₂

theorem gm_swap {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i j : L.ι} (hi : f y ∈ L.U i)
    (hj : f y ∈ L.U j) : gm f y _ (L.g i j) = (gm f y _ (L.g j i))⁻¹ :=
  eq_inv_of_mul_eq_one_left ((gm_cocycle hL f y hi hj hi).trans (gm_self hL f y hi))

theorem gw_idIsoL {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (j : L.ι) (k : PUnit → L.ι)
    (hj : F (f y) ∈ L.U j) (hk : F (f y) ∈ L.U (k PUnit.unit)) :
    gw (L := L) (F := F) (CubePf.idIsoL (L.pull F)) f y j k = gm (f ≫ F) y _ (L.g j (k PUnit.unit)) := by
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j (k PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U k from ⟨mem_pull.2 hj, mem_pull.2 hk⟩) _).trans
    (gm_pull f F y (L.U j ⊓ L.U (k PUnit.unit)) (show F (f y) ∈ L.U j ⊓ L.U (k PUnit.unit) from ⟨hj, hk⟩) _)

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W)
  (iw : W →+* V)

abbrev vId : LB.Iso (Mp T iw).L (T.M.L.pull (pullback.fst T.B.hom (spMap iw))) := CubePf.idIsoL (Mp T iw).L

abbrev wLam : LB.Iso (abelian₂ (Bp T iw) (Mp T iw).L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf (cart T iw))) :=
  GlobalTheory.HalfBC.lamIso (cart T iw) (vId T iw)

theorem isGen_wLam : (wLam T iw).IsGen :=
  GlobalTheory.HalfBC.isGen_lamIso _ _ ((isGen_iff _).2 (pGen_Mp T iw))

theorem val_trans (x y : Fin T.r → ℤ) {z : (TK V).left} {J : ((TK V).left ⟶ T.B.left) → T.M.L.ι}
    {J' : ((TK V).left ⟶ (Bp T iw).left) → PUnit → T.M.L.ι} (hJ : Good T.M.L z J) (hJ' : Good (Mp T iw).L z J') :
    val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z (Jd T iw z J') =
      lamVal (wLam T iw) (lift (cK T iw x) (cK T iw y)).left z J J' * val (T.τ₀ x y) ((TK V).hom ≫ spMap iw) z J := by
  have hJd := Jd_good T iw hJ'
  have mJ : ∀ q : (TK V).left ⟶ (Bp T iw).left, pullback.fst T.B.hom (spMap iw) (q z) ∈
      T.M.L.U (J (q ≫ pullback.fst T.B.hom (spMap iw))) := fun q => hJ (q ≫ pullback.fst T.B.hom (spMap iw))
  have mJ' : ∀ q : (TK V).left ⟶ (Bp T iw).left, pullback.fst T.B.hom (spMap iw) (q z) ∈
      T.M.L.U (J' q PUnit.unit) := fun q => mem_pull.1 (hJ' q)
  refine (gen_trans (T.τ₀_gen x y) ((TK V).hom ≫ spMap iw) z (hJd.mem _ _) (hJ.mem _ _)).trans
    (congrArg (· * _) ?_)
  let h : ((TK V).left ⟶ (Bp T iw).left) → ((TK V).left.presheaf.stalk z)ˣ := fun q =>
    gm (q ≫ pullback.fst T.B.hom (spMap iw)) z _
      (T.M.L.g (J (q ≫ pullback.fst T.B.hom (spMap iw))) (J' q PUnit.unit))
  have h₁ : trF (lamPts (T.c₀ x) (T.c₀ y)) negε ((TK V).hom ≫ spMap iw) z
      (fun k => Jd T iw z J' (((TK V).hom ≫ spMap iw) ≫ lamPts (T.c₀ x) (T.c₀ y) k))
      (fun k => J (((TK V).hom ≫ spMap iw) ≫ lamPts (T.c₀ x) (T.c₀ y) k)) =
      ∏ k, (h (lamPts (cK T iw x) (cK T iw y) k))⁻¹ ^ negε k := by
    refine Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) ?_
    have e₁ := lam_comm T iw (push_cK T iw x) (push_cK T iw y) k
    beta_reduce
    rw [← e₁, Jd_eq T iw z J' _ (TautEx.lamPts_w _ _ k)]
    exact gm_swap T.M.isLB (lamPts (cK T iw x) (cK T iw y) k ≫ pullback.fst T.B.hom (spMap iw)) z
      (mJ' (lamPts (cK T iw x) (cK T iw y) k)) (mJ (lamPts (cK T iw x) (cK T iw y) k))
  have h₂ : ∏ k, (h (lamPts (cK T iw x) (cK T iw y) k))⁻¹ ^ negε k =
      h (cK T iw x * cK T iw y).left * (h (cK T iw x).left)⁻¹ * (h (cK T iw y).left)⁻¹ *
        h (1 : TK V ⟶ Bp T iw).left := by
    simpa using Wit.prod_neg_lamPts (cK T iw x) (cK T iw y) h
  have h₃ : lamVal (wLam T iw) (lift (cK T iw x) (cK T iw y)).left z J J' =
      ∏ I, h ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) ^ GlobalTheory.PrimCocycle.lamε I := by
    have e : (fun I => J ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.HalfBC.sqOf (cart T iw) ≫
        GlobalTheory.PrimCocycle.lamφ T.B I)) = fun I => J (((lift (cK T iw x) (cK T iw y)).left ≫
          GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) ≫ pullback.fst T.B.hom (spMap iw)) :=
      funext fun I => by rw [GlobalTheory.HalfBC.sqOf_lamφ, Category.assoc]
    show gw (wLam T iw) (lift (cK T iw x) (cK T iw y)).left z
      (fun I => J ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.HalfBC.sqOf (cart T iw) ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
      (fun I => J' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I)) = _
    rw [e, GlobalTheory.HalfBC.gw_lamIso (cart T iw) (vId T iw) (lift (cK T iw x) (cK T iw y)).left z
      (fun I => J (((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) ≫
        pullback.fst T.B.hom (spMap iw)))
      (fun I => J' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
      (fun I => mJ ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
      (fun I => hJ' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))]
    refine Finset.prod_congr rfl fun I _ => congrArg (· ^ GlobalTheory.PrimCocycle.lamε I) ?_
    exact gw_idIsoL ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I) z _ _
      (mJ ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
      (mJ' ((lift (cK T iw x) (cK T iw y)).left ≫ GlobalTheory.PrimCocycle.lamφ (Bp T iw) I))
  refine h₁.trans (h₂.trans ?_)
  rw [h₃, GlobalTheory.PrimCocycle.prod_lam]

end abelian₂

theorem exists_dataFrom : ∀ {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), (∀ k, s k ≠ 0) → (∀ k a b, ε k a b = ε k b a) →
      ∃ (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e := by
  intro o W V _ _ _ _ _ T iw I _ s ε n hs hε
  refine ⟨dataF T iw s hs ε n hε, AddEquiv.refl _, pullback.fst T.B.hom (spMap iw), GlobalTheory.HalfBC.sqOf (cart T iw),
    wLam T iw, cart T iw, GlobalTheory.HalfBC.isSquare_sqOf (cart T iw), isGen_wLam T iw, fun a => ?_,
    fun a b => ⟨kU T s hs ε n a b, kU_val T s hs ε n a b, fun z J J' hJ hJ' => ?_⟩⟩
  · exact (left_of_push T iw (push_cp T iw _)).trans (by rw [TautEx.unit_hom]; simp <;> rfl)
  · exact (val_tauF T iw s hs ε n a b hJ').trans
      (congrArg _ ((val_uT T iw _ _ hJ').trans (val_trans T iw _ _ hJ hJ')))

end GlobalTheory.TChart.FromEx
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem sameFib_trait_chart : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  intro g n φ F C G₁ _ _ P hP hC T V' _ _ _ θ f fK hV' hθ hs hfK D' e hDF G' _ _ πG A' U' hU
  obtain ⟨G'', _, _, π, π₂, A'', U'', hπ, hπ₂, hΛ''⟩ := GlobalTheory.T.unif_pullback_of_canonical_on C G₁ P hP hC V' θ hV' hθ hs D' e hDF
  obtain ⟨hG', κ, πK, α, α₂, hκ, -, hα, hα₂, hΛ', -⟩ := hU

  have hκ' : κ = spMap fK := by
    haveI := GlobalTheory.Mum.EvenDesc.mono_jK T.V
    rw [← cancel_mono (jK T.V), hκ]
    have e₁ : (algebraMap V' (FractionRing V')).comp f = fK.comp (algebraMap T.V (FractionRing T.V)) :=
      RingHom.ext fun a => (hfK a).symm
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) e₁
  subst hκ'
  have hsG'' : IsSemiAbelian G'' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hP.2.2.1
  have hsG' : IsSemiAbelian G' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hG' T.semi
  have hAdm : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  obtain ⟨hD, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self V' _ hAdm D'
  obtain ⟨ψ, hψm, hψL, -⟩ := GlobalTheory.exists_generic_iso_of_unif GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 V'
    (maximalIdeal V') hAdm (maximalIdeal.isMaximal V').ne_top D' D' A'' A' G'' G' hsG'' hsG' U'' U' hD
  haveI := hψm
  haveI := U''.gen_hom
  haveI : IsMonHom U''.gen.symm.hom := inferInstanceAs (IsMonHom U''.gen.inv)

  let b : A'.A.left ⟶ G''.left := ψ.hom.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (jK V')
  have hb : IsGrpPullback A'.A G'' (jK V') b :=
    ((isGrpPullback_of_iso ψ).comp ((isGrpPullback_of_iso U''.gen.symm).comp
      (isGrpPullback_pullback G'' (jK V')))).congr (by simp only [Category.id_comp]) rfl
  obtain ⟨b₂, hb₂, hΛb⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (jK V') G'' A'.A b hb
  have hPLB : P.IsLB := hP.2.2.2.1.1
  have hL : LBIso A'.L (U''.LG.L.pull b) :=
    LBIso.trans A'.isLB (pull_isLB A''.isLB _) (pull_isLB U''.LG.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp (ψ.hom.left ≫ U''.gen.inv.left)
        (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
        (by simp only [b, Category.assoc]) U''.ext)
  have hΛA : LBIso (abelian₂ A'.A A'.L) (P.pull (b₂ ≫ π₂)) :=
    hΛb U''.LG.L A'.L _ P π₂ U''.LG.isLB A'.isLB hPLB hL hΛ''
  have hθK : spMap ((algebraMap V' (FractionRing V')).comp θ) = jK V' ≫ spMap θ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  refine ⟨A'.A, inferInstance, inferInstance, α, α₂, b ≫ π, b₂ ≫ π₂, hα, hα₂,
    (hb.comp hπ).congr hθK.symm rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hπ₂.1, ← Category.assoc, hb₂.1, Category.assoc]
  · rw [Category.assoc, hπ₂.2, ← Category.assoc, hb₂.2, Category.assoc]
  · exact LBIso.trans (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hPLB _) hΛ'.symm hΛA

end GlobalTheory.TChart
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_chart_generic_fibres_same : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  atlas_forward_decl GlobalTheory.TChart.sameFib_trait_chart
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_abelianLocus_toroidalChart : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  first | exact @GlobalTheory.TChart.AbLevel.exists_level | exact GlobalTheory.TChart.AbLevel.exists_level | (intros; apply GlobalTheory.TChart.AbLevel.exists_level <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartHit

theorem setup : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (φ : InvFun ℤ) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → S.IsSeparated ∧ LocallyOfFiniteType (π ≫ z) ∧ IsLocallyNoetherian S ∧ Dense (Set.range j) ∧ j ≫ π ≫ z = F.s := by
  intro g n F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨J, -, -, -, -, hproj, hdense, hji, -, -, -⟩ := hBlow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hMin
  have hP := GlobalTheory.ArithCurve.isProper_of_projOver hproj
  have hlft : LocallyOfFiniteType (π ≫ z) := GlobalTheory.isProjOver_locallyOfFiniteType _ _ _ hproj
  haveI : IsNoetherianRing (cycAway n) := is_noetherian_subring_closure _ (Set.toFinite _)
  refine ⟨⟨by rw [← terminal.comp_from (π ≫ z)]; infer_instance⟩, hlft, LocallyOfFiniteType.isLocallyNoetherian (π ≫ z), hdense, ?_⟩
  rw [← Category.assoc, hji, hiz]

theorem away_hom_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (t : R), t ≠ 0 → ∀ (l : Localization.Away t →+* FractionRing R), l.comp (algebraMap R (Localization.Away t)) = algebraMap R (FractionRing R) → ∀ (S : Scheme.{0}) [S.IsSeparated] (a b : Sp (Localization.Away t) ⟶ S), spMap l ≫ a = spMap l ≫ b → a = b := by
  intro R _ _ t ht l hl S _ a b h
  haveI : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hinj : Function.Injective l := by
    refine (injective_iff_map_eq_zero l).2 fun x hx => ?_
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) x
    have h1 : IsLocalization.mk' (Localization.Away t) r s * algebraMap R _ (s : R) = algebraMap R _ r :=
      IsLocalization.mk'_spec _ r s
    have h2 : algebraMap R (FractionRing R) r = 0 := by
      rw [← hl, RingHom.comp_apply, ← h1, map_mul, hx, zero_mul]
    have h3 : r = 0 := IsFractionRing.injective R (FractionRing R) (by rw [h2, map_zero])
    show IsLocalization.mk' (Localization.Away t) r s = 0
    rw [h3, IsLocalization.mk'_zero]
  have : IsDominant (spMap l) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap l) h

end GlobalTheory.ChartHit

namespace GlobalTheory.ChartHit

theorem lowBase_regular {n : ℕ} (L : LowBase (zetaAway n) n) : IsRegularLocalRing L.W := by
  haveI : IsNoetherianRing L.W := L.noeth
  let y := L.u (closedPoint L.W)
  let φ₀ := (Scheme.stalkClosedPointTo L.u).hom
  haveI : IsRegularLocalRing ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk L.F y
  have het := L.u_et
  letI : Algebra ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := φ₀.toAlgebra
  haveI : Module.Flat ((LowChart.powA L.F L.T.r).left.presheaf.stalk y) L.W := het.1
  exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm

theorem chart : ∀ {g n : ℕ} (φ : InvFun ℤ), 3 ≤ n → ∀ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)), L.h + L.T.r = g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) → (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) → IsCN V' → IsLocalHom κ → (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) → DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e → ∃ (C : Taut (zetaAway n) g n φ) (θ : C.R →+* V') (e' : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), IsLocalHom θ ∧ (∀ k, θ (C.s k) ≠ 0) ∧ θ.comp C.b = κ.comp L.T.b ∧ DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e' := by
  intro g n φ hn L m N ε V' _ _ _ κ sv D' e hgen hcone hdef hV hκ hs1 hs2 hD
  haveI : IsRegularLocalRing L.W := lowBase_regular L
  have hψV : IsLocalHom ((MvPolynomial.eval₂Hom κ sv).comp MvPolynomial.C) := by
    rw [MvPolynomial.eval₂Hom_comp_C]; exact hκ
  obtain ⟨R, _, _, _, ψ, θ, hcompl, hθ, hθψ, hψl⟩ :=
    GlobalTheory.TChart.exists_complAt_factor_of_isAdicComplete L.W (Fin m ⊕ Fin N) V' hV.2.2.1 (MvPolynomial.eval₂Hom κ sv) hψV
  have hθX : ∀ k, θ (ψ (MvPolynomial.X k)) = sv k := fun k => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = κ := by
    rw [← RingHom.comp_assoc, hθψ, MvPolynomial.eval₂Hom_comp_C]
  have hne : ∀ k, ψ (MvPolynomial.X k) ≠ 0 := fun k h => by
    have h' := hθX k
    rw [h, map_zero] at h'
    rcases k with k | k
    · exact (hs1 k).2 h'.symm
    · exact (hs2 k).ne_zero h'.symm
  obtain ⟨Q, eQ, hQ⟩ := GlobalTheory.TChart.FromEx.exists_dataFrom L.T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n hne (fun k a b => (ε k).2.1 a b)
  have hbd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R := fun k =>
    (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 (hs1 k).1 (hθX (.inl k) ▸ hu.map θ)
  have htor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k))) := fun k =>
    isUnit_of_map_unit θ _ (by rw [hθX]; exact hs2 k)
  let C : Taut (zetaAway n) g n φ :=
    { toLowBase := L
      genus := hgen
      m := m
      N := N
      ε := ε
      cone := hcone
      defin := hdef
      R := R
      ψ := ψ
      compl := hcompl
      ψ_loc := hψl
      bd := hbd
      tor := htor
      Q := Q
      e := eQ
      data := hQ }
  refine ⟨C, θ, e, hθ, fun k => ?_, ?_, ?_⟩
  · show θ (ψ (MvPolynomial.X k)) ≠ 0
    rw [hθX]
    rcases k with k | k
    · exact (hs1 k).2
    · exact (hs2 k).ne_zero
  · show θ.comp ((ψ.comp MvPolynomial.C).comp L.T.b) = κ.comp L.T.b
    rw [← RingHom.comp_assoc, hθC]
  · show DegFrom L.T (θ.comp (ψ.comp MvPolynomial.C)) (fun k => θ (ψ (MvPolynomial.X k)))
      (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e
    rw [hθC, show (fun k => θ (ψ (MvPolynomial.X k))) = sv from funext hθX]
    exact hD

end GlobalTheory.ChartHit

theorem GlobalTheory.TChart.exists_chart_at : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, ∃ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ ∧ y ≫ j = jK C.R ≫ ξ ∧ ξ (closedPoint C.R) = x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hMin hBlow x
  obtain ⟨hsep, hlft, hln, hdense, hjs⟩ := GlobalTheory.ChartHit.setup F Z z i OZ φ d S π j BD hMin hBlow
  obtain ⟨T, ξT, b, hx, hTj, hTb⟩ := GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt F S (π ≫ z) j hn hdense hjs x
  have hyb : T.y ≫ F.s = jK T.V ≫ spMap b := by
    rw [← hjs, ← Category.assoc, ← hTj, Category.assoc, hTb]
  obtain ⟨L, m, N, ε, V', _, _, _, f, κ, sv, D', e, G', _, _, πG, A', U', hgen, hcone, hdef, hV', hdvr, hfi, hff, hfl,
    hκl, hκb, hs1, hs2, hU, hD⟩ := GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait g hg φ hφ n hn hodd F T b hyb
  obtain ⟨C, θ, e', hθl, hθs, hθb, hD'⟩ := GlobalTheory.ChartHit.chart φ hn L m N ε V' κ sv D' e hgen hcone hdef hV' hκl hs1 hs2 hD
  obtain ⟨G₁, _, _, P, hMP, hCan, hab, htors⟩ := GlobalTheory.T.exists_mumford_family g n φ hn hodd C
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap f := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi
  let fK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') f hle
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq hle a
  have hprod : θ (∏ k, C.t k) ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun k _ => hθs (.inl k)
  have htne : (∏ k, C.t k) ≠ 0 := fun h => hprod (by rw [h, map_zero])
  have hunit : IsUnit ((algebraMap V' (FractionRing V')).comp θ (∏ k, C.t k)) := by
    refine isUnit_iff_ne_zero.2 ?_
    simpa using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hprod) :
      algebraMap V' (FractionRing V') (θ (∏ k, C.t k)) ≠ 0)
  let κ' : Localization.Away (∏ k, C.t k) →+* FractionRing V' := IsLocalization.Away.lift (∏ k, C.t k) hunit
  have hκ' : κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = (algebraMap V' (FractionRing V')).comp θ :=
    IsLocalization.Away.lift_comp (∏ k, C.t k) hunit
  have hSF := GlobalTheory.T.trait_chart_generic_fibres_same F C G₁ P hMP hCan T V' θ f fK hV' hθl hθs hfK D' e' hD' G' πG A' U' hU
  have hx₀ : (spMap fK ≫ T.y) ≫ F.s = spMap ((κ'.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) := by
    rw [Category.assoc, hyb, hκ', RingHom.comp_assoc, hθb, hκb]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp [hfK]
  rw [← hκ'] at hSF
  obtain ⟨c, hc, hiso, hpt⟩ := GlobalTheory.T.exists_level_abelianLocus_toroidalChart hn hodd F C G₁ P hMP hab htors (FractionRing V') κ' (spMap fK ≫ T.y) hx₀ hSF
  obtain ⟨y, α₁, yU, l, hFam, hSPB, hl, hyl⟩ := GlobalTheory.T.exists_siegelLevelStructure_mumfordFamily_tautological g n φ hn hodd F C G₁ P hMP hab c hc hiso
  obtain ⟨ξ, hξ⟩ := GlobalTheory.T.exists_ext_normalised_blowup g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hMin hBlow C G₁ y α₁ hFam
  have hsA : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl]
  have hyUs : yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl (Sp (cycAway n)) _ _ ?_
    have h := hFam.2.2.2.2
    rw [hyl, Category.assoc] at h
    rw [h, ← hsA]
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.assoc]
  have hκy := hpt yU hSPB hyUs
  have hξU : spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) ≫ ξ = yU ≫ j := by
    refine GlobalTheory.ChartHit.away_hom_ext C.R (∏ k, C.t k) htne l hl S _ _ ?_
    rw [← Category.assoc, hsA, ← hξ, hyl, Category.assoc]
  have hgen' : jK V' ≫ (spMap θ ≫ ξ) = jK V' ≫ (spMap f ≫ ξT) := by
    have e1 : jK V' ≫ spMap θ = spMap κ' ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ']
    have e2 : jK V' ≫ spMap f = spMap fK ≫ jK T.V := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; ext a; simp [hfK]
    rw [← Category.assoc, e1, Category.assoc, hξU, ← Category.assoc, hκy, ← Category.assoc, e2, Category.assoc,
      Category.assoc, hTj]
  have hdom : IsDominant (jK V') := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).le.trans bot_le)⟩
  have hext : spMap θ ≫ ξ = spMap f ≫ ξT :=
    ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (jK V') hgen'
  refine ⟨C, G₁, inferInstance, y, α₁, ξ, hFam, hξ, ?_⟩
  have h1 : (spMap θ).base (closedPoint V') = closedPoint C.R := IsLocalRing.comap_closedPoint θ
  have h2 : (spMap f).base (closedPoint V') = closedPoint T.V := IsLocalRing.comap_closedPoint f
  rw [← hx, ← h1, ← h2]
  show (spMap θ ≫ ξ).base (closedPoint V') = (spMap f ≫ ξT).base (closedPoint V')
  rw [hext]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, ∃ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ ∧ y ≫ j = jK C.R ≫ ξ ∧ ξ (closedPoint C.R) = x := by
  atlas_forward_decl GlobalTheory.TChart.exists_chart_at
end
