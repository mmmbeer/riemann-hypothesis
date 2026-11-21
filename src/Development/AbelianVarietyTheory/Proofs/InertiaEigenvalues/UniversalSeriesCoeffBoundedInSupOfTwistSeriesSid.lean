import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntFormDescentBelow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowestWeightVectorsAtRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelFunctionFiniteRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaWeilTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterQuotientValuesInEmbeddingField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceOfValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayUp

theorem containsRayField_up {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

end GlobalTheory.RayUp
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cmp.SeriesRay

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

section Forms

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)

theorem sum_mem_intForms (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {m : ℕ} (x : Fin m → C.d.c₂.F)
    (hx : ∀ k, ∀ la ∈ S, la.valuation C.d.c₂.F (x k) ≤ 1) (φ : Fin m → GA D (T.V j σ) → ℂ) (hφ : ∀ k, φ k ∈ C.intForms a n S) :
    (∑ k, C.σ₂ (x k) • φ k) ∈ C.intForms a n S := by
  choose f hf e using hφ
  refine ⟨∑ k, x k • f k, ⟨⟨sum_mem fun k _ => Submodule.smul_mem _ _ (hf k).1.1, ?_⟩, fun la hla v hv => ?_⟩, ?_⟩
  · rw [map_sum]
    exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).1.2
  · have hV := isVal_valSet la v hv
    exact GlobalTheory.IdemInt.nonneg_sum hV _ _ fun k _ => GlobalTheory.IdemInt.nonneg_smul hV (hx k la hla) ((hf k).2 la hla v hv)
  · simp only [← e, Cover.rd, map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

variable {T i} in

def FieldRay (Lat : Submodule ℤ (VsV D i ℂ)) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) C.σ₂ ∧
    (∀ v ∈ Lat, ∀ m, ∃ a, C.σ₂ a = MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ IntegralSeries.HasRay C

omit [Algebra T.Q.c.F D.what₂.LL] in

def DescIntAll : Prop :=
  ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, TwistSeries.IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
    TwistSeries.UnramAt C.inc (IntegralSeries.placesOver C.d.c₂.F l) →
      ∀ φ ∈ C.intForms (wtA κ) κ.n (IntegralSeries.placesOver C.d.c₂.F l),
        (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → ℂ) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ a, TwistSeries.IntVal C.σ₂ (IntegralSeries.placesOver C.d.c₂.F l) (x a)) ∧
            (∀ a, ψ a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n (TwistSeries.below C.inc (IntegralSeries.placesOver C.d.c₂.F l))) ∧
            φ = ∑ a, x a • ψ a

section Data

variable {T}

variable {R i}

abbrev sb (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) :=
  GlobalTheory.AdTh.PhaseMap.sub (m := (Wc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1) U

end Data

section First

variable {T R i κ}

def ker1 (s : GA D (Vc D i)) (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] ℂ :=
  LinearMap.proj 0 ∘ₗ R.ωP i A.μ0 (s, g) ∘ₗ
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f

variable {hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i} {v₀ : (R.MW i (sg0 D A)).Vec} {u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ}
  {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} {ka : ℂ} {J : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}

variable (u c0 ka J) in

structure Dict : Prop where
  norm : ‖ka‖ = 1
  rat : ∀ k : Subfield ℂ, (inC T.Q.c).fieldRange ≤ k → ∀ v : VsV D i ℂ,
    (∀ m, MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) ↔ ∀ d, MvPolynomial.coeff d (J v) ∈ k
  eq : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v,
    IntegralSeries.fock R i (R.BV i) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • IntegralSeries.fock R i (fun _ => 1) f (J v)

theorem Dict.series (h : Dict u c0 ka J) {f} (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) (s v g) :
    TwistSeries.series R i u s f (c0 v) g = ka * ker1 (R := R) s g f (J v) := by
  have e := congrArg (fun x => R.ωP i A.μ0 (s, g) x 0) (h.eq f hf v)
  simp only [map_smul] at e
  exact e

end First

end GlobalTheory.Cmp.SeriesRay
end
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerPlace

theorem placeIn_unique : ∀ (Λ : Subring ℂ) [IsDiscreteValuationRing Λ] (l : ℕ), l.Prime → ¬ IsUnit ((l : ℕ) : Λ) → ∃ e : ℕ, ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ), (∀ x, ι x ∈ Λ ∨ (ι x)⁻¹ ∈ Λ) → ∃ la : HeightOneSpectrum (𝓞 L), placesIn ι Λ = {la} ∧ (∀ x, ι x ∈ Λ ↔ la.valuation L x ≤ 1) ∧ ((l : ℕ) : 𝓞 L) ∈ la.asIdeal ∧ ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) := by
  intro Λ _ l hl hlu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Λ
  have hl0 : ((l : ℕ) : Λ) ≠ 0 := by
    intro h
    have h' : ((((l : ℕ) : Λ)) : ℂ) = 0 := by rw [h]; rfl
    push_cast at h'
    exact hl.ne_zero (by exact_mod_cast h')
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨e, fun L _ _ ι hval => ?_⟩
  let B : ValuationSubring L :=
    { toSubring := Λ.comap ι
      mem_or_inv_mem' := fun x => by
        rcases hval x with h | h
        · exact Or.inl h
        · right
          show ι x⁻¹ ∈ Λ
          rw [map_inv₀]; exact h }
  have hint : ∀ x : 𝓞 L, (ι.comp (algebraMap (𝓞 L) L)) x ∈ Λ := fun x => by
    have : IsIntegral B (algebraMap (𝓞 L) L x) := (x.isIntegral_coe).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    show ι (algebraMap (𝓞 L) L x) ∈ Λ
    rw [← hy]; exact y.2
  let g : 𝓞 L →+* Λ := (ι.comp (algebraMap (𝓞 L) L)).codRestrict Λ hint
  have hg : ∀ x : 𝓞 L, ((g x : Λ) : ℂ) = ι (algebraMap (𝓞 L) L x) := fun x => rfl
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal Λ).comap g
  have hlP : ((l : ℕ) : 𝓞 L) ∈ P := by
    show g l ∈ IsLocalRing.maximalIdeal Λ
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hlu
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.ne_zero (by exact_mod_cast hlP)
  let la : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hunit : ∀ s : 𝓞 L, s ∉ la.asIdeal → IsUnit (g s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hsup : ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ := by
    intro x hx
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x hx
    obtain ⟨w, hw⟩ := hunit s s.2
    have h3 : (((w⁻¹ : Λˣ) : Λ) : ℂ) * ι (algebraMap (𝓞 L) L s) = 1 := by
      rw [← hg, ← hw]
      have := congrArg Subtype.val w.inv_mul
      exact this
    have hs0 : ι (algebraMap (𝓞 L) L s) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
    have hw' : (ι (algebraMap (𝓞 L) L s))⁻¹ ∈ Λ := by
      rw [← eq_inv_of_mul_eq_one_left h3]; exact ((w⁻¹ : Λˣ) : Λ).2
    have hx' : ι x = ι (algebraMap (𝓞 L) L a) * (ι (algebraMap (𝓞 L) L s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, h]
    rw [hx']
    exact Λ.mul_mem (hint a) hw'
  have hsub : ∀ x : L, ι x ∈ Λ → la.valuation L x ≤ 1 := by
    intro x hx
    by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hy : la.valuation L x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x⁻¹ hy.le
    have hs1 : la.valuation L (algebraMap (𝓞 L) L s) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la)).2 s.2
    have ha : a ∈ la.asIdeal := by
      refine (la.valuation_lt_one_iff_mem (K := L) a).1 ?_
      show la.valuation L (algebraMap (𝓞 L) L a) < 1
      rw [← h, map_mul, hs1, mul_one]; exact hy
    have h4 : (⟨ι x, hx⟩ : Λ) * g a = g s := Subtype.ext (show ι x * ι (algebraMap (𝓞 L) L a) = ι (algebraMap (𝓞 L) L s) by
      rw [← map_mul, ← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul])
    have hga : g a ∈ IsLocalRing.maximalIdeal Λ := ha
    have := hunit s s.2
    rw [← h4] at this
    exact ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.mul_mem_left _ _ hga)) this
  refine ⟨la, ?_, fun x => ⟨hsub x, hsup x⟩, hlP, ?_⟩
  · ext la'
    constructor
    · intro h'
      rw [Set.mem_singleton_iff]
      have hle : la.asIdeal ≤ la'.asIdeal := by
        intro r hr
        by_contra hr'
        have h1 : la'.valuation L (algebraMap (𝓞 L) L r) = 1 :=
          (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la')).2 hr'
        have h2 : la'.valuation L (algebraMap (𝓞 L) L r)⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
        have h3 := hsub _ (h' _ h2)
        have h5 : la.valuation L (algebraMap (𝓞 L) L r) < 1 := (la.valuation_lt_one_iff_mem (K := L) r).2 hr
        have hr0' : r ≠ 0 := by rintro rfl; exact hr' la'.asIdeal.zero_mem
        have hr0 : la.valuation L (algebraMap (𝓞 L) L r) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hr0')
        rw [map_inv₀] at h3
        have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hr0, h5⟩
        exact absurd h3 (not_le.2 this)
      have hEq : la.asIdeal = la'.asIdeal := la.isMaximal.eq_of_le la'.isPrime.ne_top hle
      exact HeightOneSpectrum.ext hEq.symm
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hsup
  · intro hmem
    have hmap : Ideal.map g (la.asIdeal ^ (e + 1)) ≤ (IsLocalRing.maximalIdeal Λ) ^ (e + 1) := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono Ideal.map_comap_le (e + 1)
    have h5 := hmap (Ideal.mem_map_of_mem g hmem)
    rw [map_natCast, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hu] at h5
    obtain ⟨c, hc⟩ := h5
    have hpe : ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    have hu' : (u : Λ) = ϖ * c := by
      apply mul_right_cancel₀ hpe
      rw [hc]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (hu' ▸ u.isUnit))

end GlobalTheory.TowerPlace
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
  Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
  GlobalTheory.SeriesTie.UnivRat
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem mem_of_pow_eq_one {Λ : Subring ℂ} {z : ℂ} {m : ℕ} (hm : 0 < m) (h : z ^ m = 1) (hz : z ∈ Λ ∨ z⁻¹ ∈ Λ) : z ∈ Λ := by
  rcases hz with h1 | h1
  · exact h1
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk : z ^ k = z⁻¹ := by
      rw [pow_succ] at h; exact eq_inv_of_mul_eq_one_left h
    have : z = (z⁻¹) ^ k := by rw [inv_pow, hk, inv_inv]
    rw [this]; exact Λ.pow_mem h1 k

theorem comap_eq_of_le_one_iff {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L)
    (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : K, la.valuation L (φ x) ≤ 1 ↔ p.valuation K x ≤ 1) :
    la.asIdeal.comap (RingOfIntegers.mapRingHom φ) = p.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← la.valuation_lt_one_iff_mem (K := L), ← p.valuation_lt_one_iff_mem (K := K)]
  change la.valuation L (φ (algebraMap _ K x)) < 1 ↔ p.valuation K (algebraMap _ K x) < 1
  generalize algebraMap _ K x = y
  by_cases hy : y = 0
  · simp [hy]
  have h1 : la.valuation L (φ y) ≠ 0 := by simpa using hy
  have h2 : p.valuation K y ≠ 0 := by simpa using hy
  have := h y⁻¹
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h1), inv_le_one₀ (zero_lt_iff.2 h2)] at this
  rw [← not_le, ← not_le, this]

variable {D : D7}

theorem containsRayField_of_rayIn {N : ℕ} {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) (h : RayIn D N σ.fieldRange) :
    ∃ φ : D.host.K →+* L, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ N := by
  obtain ⟨H, _, _, _, i4, ⟨hun, -, hart⟩, jj, -, hv⟩ := h
  haveI : IsGalois D.host.K H := i4.toIsGalois
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap D.host.K H) N :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := D.host.K) (L := H) N hun (fun I hI hc hχ => (hart I hI hc).1 hχ)
  let τ : H →+* L := (σ.rangeRestrictFieldEquiv.symm : σ.fieldRange →+* L).comp (jj.codRestrict σ.fieldRange hv)
  exact ⟨τ.comp (algebraMap D.host.K H), GlobalTheory.RayUp.containsRayField_up _ τ N hc⟩

section Datum

variable {S T : HSp D}

open Classical in

theorem isLevelFn_datumFn {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (hbad : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ Q →
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (N : ℕ) (hN : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ Q → (N : 𝓞 D.host.E) ∈ PP.asIdeal) (k : Subring ℂ)
    (h1 : ∀ u, ((B.G.P.chi u : ℂˣ) : ℂ) ∈ k) (h2 : ∀ PP ∈ B.G.Pg, ∀ x, ((B.G.muC PP x : ℂˣ) : ℂ) ∈ k)
    (h3 : ∀ PP ∈ B.de.Q, ∀ x, ((B.de.resC PP x : ℂˣ) : ℂ) ∈ k)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h4 : ∀ PP y, φ PP y ∈ k) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (halfIdem B.G.Pg (B.de.Q ∪ Q)) (latO S T B.F.ΛS B.F.ΛT fun _ => True) N
      (B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ)) ∧ ∀ t, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) t ∈ k := by
  have hlat := fun x => @GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem D S T B.F hB.frame _ _ hQ.1 hbad x
  refine ⟨⟨fun t ht => ?_, fun u hu hue t => ?_⟩, fun t => ?_⟩
  · unfold Frame.datumFn at ht
    have c1 := left_ne_zero_of_mul ht
    have c2 := right_ne_zero_of_mul ht
    have d1 := (ite_ne_right_iff.1 c1).1
    have d2 := (ite_ne_right_iff.1 c2).1
    exact ⟨(hlat t d1.1).2 ⟨d1.2, d2.2⟩, d1.1⟩
  · obtain ⟨i1, i2⟩ := (hlat u hue).1 hu
    have e1 : frMapAdj S T B.F.βS B.F.βT (t + N • u) = frMapAdj S T B.F.βS B.F.βT t + N • frMapAdj S T B.F.βS B.F.βT u := by
      rw [GlobalTheory.RefDatumLev.frMapAdj_add', GlobalTheory.RefDatumLev.frMapAdj_nsmul']
    have hKu : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) (N • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hh : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) (t + N • u) ↔ IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    unfold Frame.datumFn
    rw [e1, frMapO_add_nsmul]
    simp only [hh, GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i1, GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i2]
    congr 1
    · refine ite_congr rfl (fun hc => ?_) fun _ => rfl
      exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP =>
        GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i1 _ (hN PP (Or.inl hPP))
    · refine ite_congr rfl (fun hc => ?_) fun _ => rfl
      unfold Base.locFn
      congr 1
      · exact Finset.prod_congr rfl fun PP hPP => by
          beta_reduce
          rw [GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i2 _ (hN PP (Or.inr (Finset.mem_union_left _ hPP)))]
      · exact Finset.prod_congr rfl fun PP _ => by
          beta_reduce
          rw [GlobalTheory.RefDatumLev.redM_add_nsmul PP.1 hc.2 i2 _ (hN PP.1 (Or.inr (Finset.mem_union_right _ PP.2)))]
  · unfold Frame.datumFn
    refine mul_mem ?_ ?_
    · split_ifs
      · unfold omegaG
        split_ifs
        · refine mul_mem (mul_mem (h1 _) (prod_mem fun PP _ => prod_mem fun c hc => absurd hc (Finset.notMem_empty _))) ?_
          refine prod_mem fun PP _ => ?_
          rw [← Units.val_inv_eq_inv_val, ← map_inv]
          exact h2 PP.1 PP.2 _
        · exact zero_mem _
      · exact zero_mem _
    · split_ifs
      · unfold Base.locFn
        refine mul_mem (prod_mem fun PP hPP => ?_) (prod_mem fun PP _ => h4 PP _)
        unfold GlobalTheory.ExportSeries.flat
        split_ifs
        · exact h3 PP hPP _
        · exact zero_mem _
      · exact zero_mem _

end Datum

section Twist

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem theta_twist (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (i : Fin D.R.m) {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    {pd : ℕ} (hodd : Odd pd) {δ : Formalism.L2.Host.HChar D.host.E} {δc : (AE D)ˣ →* Circle} (htw : IsTwist pd σ δ δc)
    {om : PairRep (Vc D i) (Wc D i)}
    (hom : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om) (s : GA D (Vc D i)) :
    ∃ c ∈ σ.fieldRange, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ pd xi ∧
      ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ g : GA D (Wc D i), thetaKO om s g f =
        c * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) * thetaKO (R.ωP i A.μ0) s g f) := by
  obtain ⟨hE, ⟨n, hn, ho⟩, hTriv, htame, hunr, hval⟩ := id htw
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  have hmu : R.toLevCh.mu A.μ0 = Lift.tup R.mu0 (1 : (AE D)ˣ →* Circle) := by
    unfold LevCh.mu
    rw [hxi]
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) := by
    have h := hP.ωP i A.μ0
    rw [hmu, GlobalTheory.SplitChange.chrTh_tup] at h
    simpa only [mul_one] using h
  rw [GlobalTheory.SplitChange.chrTh_tup] at hom
  have hδH : IsHeckeChar D δc := hE.1
  have hδF : ∀ a, δc (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hE hTriv
  have hpow : ∀ x, δc x ^ n = 1 :=
    GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (δc ^ n) ⟨hE.1.1.pow n, fun x => by
      rw [MonoidHom.pow_apply, hE.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D δc δ hE n ho)
  obtain ⟨nV, hnV, -⟩ := GlobalTheory.Member.exists_muVal D (Vc D i) δc hδH hδF
  obtain ⟨nW, hnW, -⟩ := GlobalTheory.Member.exists_muVal D (Wc D i) δc hδH hδF
  obtain ⟨xi, hxiT, hxiV⟩ := GlobalTheory.AntiCycRead.read_anticyc D (Wc D i) _ σ pd hodd δc hδH hδF
    ⟨n, hn, hpow⟩ (GlobalTheory.tame_heckeChar_eq_one_of_finUnit D δc δ hE htame pd hunr)
    (fun x => GlobalTheory.WeilTwistSeries.twist_val_mem htw x)
  obtain ⟨x, hx⟩ := hnV.1 s
  refine ⟨(nV s)⁻¹, ?_, ⟨n, hn, ?_⟩, xi, hxiT, fun f hf g => ?_⟩
  · rw [hnV.2 s x hx]
    exact inv_mem (GlobalTheory.WeilTwistSeries.twist_val_mem htw x)
  · rw [hnV.2 s x hx, inv_pow, ← Circle.coe_pow, hpow x, Circle.coe_one, inv_one]
  · obtain ⟨y, hy⟩ := hnW.1 g
    rw [GlobalTheory.SplitChange.thetaKO_twist hω hδH hδF hom hnV hnW s g hf, hxiV g y hy, ← hnW.2 g y hy]
    ring

end Twist

section Cover

variable {T : CoreJ D} {j : Fin D.R.m} {C : Cover T ((j : ℕ) + 1) T.σ₀}

open Classical in

theorem intForms_fibre (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (hU : C.IsUnif)
    (hray : RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange) {A : Type} [AddCommGroup A] {u : UnivTwist D A}
    {Q : Finset (Pl D.host.E)} (hu : u.Good Q) (hQ : ∀ PP ∈ Q, ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (a : ↥Q → A) (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)))
    {ψ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ} (h : ψ ∈ C.intForms w n S) :
    (fun g => (if Multiplicative.toAdd (detChar _ (u.delQ Q) g) = a then 1 else 0) * ψ g) ∈ C.intForms w n S := by
  have hM : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have h3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  rw [← hM] at hray hQ
  obtain ⟨l1, l2, l3⟩ := delQ_det_laws hu (T.V ((j : ℕ) + 1) T.σ₀) C.d.l₂.odd hQ
  have key := (GlobalTheory.T.levelCover_forms_mul_componentFunction D T hT _ (inR j) T.σ₀ T.toCore.good_σ₀ C hU C.d.l₂.M (by omega) dvd_rfl
    (Or.inr (GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hT.pins.1 _ h3 _ C.σ₂ hray))
    (fun g => if Multiplicative.toAdd (detChar _ (u.delQ Q) g) = a then 1 else 0)
    (fun g g' e => by rw [l1 g g' e]) (fun γ hγ g => by rw [l2 γ hγ g]) (fun k _ hk g => by rw [l3 k hk g])
    w n).2 S (fun la _ g => by split_ifs <;> simp) ψ h
  convert key using 1
  funext g
  split_ifs <;> simp

end Cover

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {ρ : Setup D.ntw} (hρ : ρ.Good)
  (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem coprime_pDel (l : ℕ) (hl : l.Prime) : Nat.Coprime (pDel D l) l := by
  unfold pDel
  split_ifs with h
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 fun e => D.host.pde_ne (h.symm.trans e.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 fun e => h e.symm

include YS hρ in

theorem exists_cover_coprime (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (halg : AlgTie T) (hgal : IsGalois ℚ D.LL0)
    (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) (hU : ρ.LevelOf D.nexp)
    (Q : Finset (Pl D.host.E)) (hcls : Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q) (hS : Disjoint Q (D.ntw.S0 i)) (n : ℕ) :
    ∃ C : Cover T ((j : ℕ) + 1) T.σ₀, GoodCover T Rl.toRealDat j C n ∧ Nat.Coprime C.d.pd (D.ntw.l i) ∧
      (embLL0 D).fieldRange ≤ C.σ₂.fieldRange ∧
      C.σ₂.fieldRange ≤ (ρ.e i b).fieldRange ∧ pDel D (D.ntw.l i) ∣ C.d.pd ∧
      (∀ P ∈ Q, ((C.d.pd : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
      (∀ g, (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange) ∧
      ∀ PP ∈ (ρ.B i j b).de.Q, ∀ x, (((ρ.B i j b).de.resC PP x : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange := by
  have hB := hρ.base i j b
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  obtain ⟨N, hN0, hNl, haux, hNQ⟩ := exists_auxiliary_squarefree_level_twistPlaces hρ hde i Q hcls hS
  obtain ⟨L₀, i1, i2, h1, h2, h3, h4⟩ := GlobalTheory.RayInFrac.exists_field D ρ hρ i b hRF hray
    (D.host.g 0 * D.host.g 1 * pDel D (D.ntw.l i)) N (dvd_mul_right _ _) (by
      rcases pDel_cases (D := D) (D.ntw.l i) with e | e <;> rw [e]
      · exact dvd_mul_right _ _
      · rw [mul_right_comm _ D.host.pde]; exact dvd_mul_right _ _) hN0 hNl
  haveI : Normal ℚ L₀ := (i2 hgal).to_normal
  haveI : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hord : ∀ {H : Type} [Group H] [Finite H] (f : H →* ℂˣ) (x : H), IsOfFinOrder ((f x : ℂˣ) : ℂ) := fun f x =>
    MonoidHom.isOfFinOrder ((Units.coeHom ℂ).comp f) (isOfFinOrder_of_finite x)
  obtain ⟨L, i3, i4, h5, h6, h7⟩ := exists_field_adjoin_roots (ρ.e i b).fieldRange
    (Z := Set.range (fun g => (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ)) ∪
      ⋃ PP ∈ (ρ.B i j b).de.Q, Set.range fun x => (((ρ.B i j b).de.resC PP x : ℂˣ) : ℂ))
    ((Set.finite_range _).union ((ρ.B i j b).de.Q.finite_toSet.biUnion fun _ _ => Set.finite_range _)) (by
      rintro z (⟨g, rfl⟩ | hz)
      · exact ⟨type_mem_range i j b hU g, hord _ _⟩
      · obtain ⟨PP, hPP, x, rfl⟩ := Set.mem_iUnion₂.1 hz
        refine ⟨?_, hord _ _⟩
        obtain ⟨y, hy⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hB.de.split.isIdemAt hPP) x
        obtain ⟨hx, hr⟩ := hy.res
        obtain ⟨a, ha⟩ := GlobalTheory.DeltaRange.delta_value_mem_range hρ i j b y
        rw [hB.de.res PP hPP y hy.off hx x hr] at ha
        exact ⟨a, ha⟩) L₀ h2
  have h8 : (embLL0 D).fieldRange ≤ L.toSubfield := fun z hz => h5 (h1 hz)
  rw [← hMg] at haux
  obtain ⟨I, hK, hprod, hsup⟩ := GlobalTheory.HalfCharacter.exists_half_of_auxiliary_split_level D T hT _ haux
  have hMN : T.Q.l.M * (pDel D (D.ntw.l i) * N) = D.host.g 0 * D.host.g 1 * pDel D (D.ntw.l i) * N := by
    rw [hMg, mul_assoc (D.host.g 0 * D.host.g 1)]
  have hne : T.Q.l.M * (pDel D (D.ntw.l i) * N) ≠ 0 :=
    mul_ne_zero (by have := T.Q.l.three_le; omega) fun h0 => Nat.not_odd_zero (h0 ▸ haux.1)
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hT j (inR j) n _ I haux hK hprod hsup L
    (fun z hz => h8 (GlobalTheory.CoverSmall.core_le_small T Rl cG S YS hT halg j hz))
    (h5 (h4 _ (by rw [← hMN]; exact (Complex.isPrimitiveRoot_exp _ hne).pow_eq_one)))
    ⟨fun v hv => by
        obtain ⟨y, hy⟩ := hval.mu0 j v hv
        exact ⟨⟨embLL0 D y, h8 ⟨y, rfl⟩⟩, hy⟩,
      fun v hv => by
        obtain ⟨y, hy⟩ := hval.eta v hv
        exact ⟨⟨embLL0 D y, h8 ⟨y, rfl⟩⟩, hy⟩⟩
    (by
      obtain ⟨H, j1, j2, j3, j4, hH, jj, hjj, hv⟩ := h3
      rw [hMN]
      exact ⟨H, j1, j2, j3, j4, hH, jj, hjj, fun x => h5 (hv x)⟩)
  refine ⟨C, hG, ?_, hfr ▸ h8, hfr ▸ h6, hpd ▸ dvd_mul_right _ _, fun P hP => ?_, fun g => ?_, fun PP hPP x => ?_⟩
  · rw [hpd]
    exact Nat.Coprime.mul_left (coprime_pDel _ (D.ntw.lPrime i).out) hNl
  · rw [hpd]
    exact GlobalTheory.HalfCompare.mem_of_dvd (hNQ P hP) (dvd_mul_left _ _)
  · rw [hfr]
    exact h7 _ (Or.inl ⟨g, rfl⟩)
  · rw [hfr]
    exact h7 _ (Or.inr (Set.mem_iUnion₂.2 ⟨PP, hPP, x, rfl⟩))

end Main

end GlobalTheory.XiIntSteps
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
  Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
  GlobalTheory.SeriesTie.UnivRat
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntSteps

variable {D : D7}

theorem castDict_smul {V W : HSp D} (e : V = W) (z : ℂ) (ψ : GA D V → ℂ) : castDict e (z • ψ) = z • castDict e ψ := by
  subst e
  rfl

theorem sum_mem_intForms' {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {ι : Type} [Fintype ι] (φ : ι → GA D (T.V j σ) → ℂ)
    (hφ : ∀ k, φ k ∈ C.intForms a n S) : (∑ k, φ k) ∈ C.intForms a n S := by
  have h := GlobalTheory.Cmp.SeriesRay.sum_mem_intForms C a n S (fun _ : Fin (Fintype.card ι) => 1) (fun _ _ _ => by simp)
    (fun k => φ ((Fintype.equivFin ι).symm k)) fun k => hφ _
  simp only [map_one, one_smul] at h
  rwa [Equiv.sum_comp (Fintype.equivFin ι).symm φ] at h

theorem exists_sum_fibres {T : CoreJ D} {j : Fin D.R.m} {C : Cover T ((j : ℕ) + 1) T.σ₀} {W : HSp D}
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = W) (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (hU : C.IsUnif)
    (hray : RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange) {A : Type} [AddCommGroup A] [Fintype A] {u : UnivTwist D A}
    {Q : Finset (Pl D.host.E)} (hu : u.Good Q) (hQ : ∀ PP ∈ Q, ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (a : ↥Q → A) (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)))
    (φ : (↥Q → A) → GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ) (hφ : ∀ a', φ a' ∈ C.intForms w n S) :
    ∃ Φ ∈ C.intForms w n S, ∀ g, castDict hV Φ g =
      castDict hV (φ (a - Multiplicative.toAdd (detChar W (u.delQ Q) g))) g := by
  classical
  subst hV
  refine ⟨_, sum_mem_intForms' C _ _ _ _ fun a' => intForms_fibre hRF hT hU hray hu hQ a' _ _ _ (hφ (a - a')), fun g => ?_⟩
  change (∑ a', _ : GA D _ → ℂ) g = φ _ g
  rw [Finset.sum_apply, Finset.sum_eq_single (Multiplicative.toAdd (detChar _ (u.delQ Q) g))
    (fun a' _ ha' => by rw [if_neg (Ne.symm ha'), zero_mul]) (fun h0 => absurd (Finset.mem_univ _) h0), if_pos rfl, one_mul]

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A} (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good)
  (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

include YS hρ in

theorem xi_int_of_ties (hRF : GlobalTheory.NT.RayField) (hSI : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j)
    (hpin : RealPin Rl cG ρ) (hU : ρ.LevelOf D.nexp) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hstd : VStd D j) (hfr : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV)
    (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (ρ.B i j b).w.lam,
      harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
        coefFn (embLL0 D) (ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) →
      ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → ∀ a, ∃ la : HeightOneSpectrum (𝓞 T.Q.c.F),
        (∀ x : T.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, ρ.eO i b o = T.σ₀ x) ∧
        ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ k, ψ k ∈ baseInt T ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) (κ j).n {la}) ∧
          (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • ρ.xi i j b D.nexp Q M h P a = castDict hV (∑ k, ρ.eO i b (o k) • ψ k) := by
  classical
  have hT := hti.laws
  have hB := hρ.base i j b
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  obtain ⟨c₀, hc₀, gramR, c0R, c0L, hft, u, hu, hsc⟩ := exists_isScale Rl cG v₀ hρ hpin hcore.lev hcore.fam.tie
    hcore.models.cV hcore.thP hio i j b (hti.hv₀ j _)
  obtain ⟨cC, hcC⟩ := GlobalTheory.ExtCoeff.exists_ext_map D.what₂.embLL (VV D.what₂.LL (lamV D j)) (VV ℂ (lamV D j)) (c0L j)
  have hCM : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap Rl.toRealDat j cC := ⟨gramR, c0R, c0L, hft, fun v =>
    ⟨⟨MvPolynomial.map D.what₂.embLL v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ v.2⟩, rfl, hcC v _ rfl⟩⟩
  obtain ⟨ph, hph, hS⟩ := (hSI D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hT hcore.lev hcore.grp hcore.fam hcore.models hcore.thP
    hti j hstd hV hfr).1 u hu cC hCM
  have hph0 : ph ≠ 0 := fun e => by simp [e] at hph

  let Λ : Subring ℂ := (ρ.eO i b).range
  let eΛ : D.ntw.O i ≃+* Λ := RingEquiv.ofBijective (ρ.eO i b).rangeRestrict
    ⟨fun x y e => ρ.eO_injective i b (congrArg Subtype.val e), (ρ.eO i b).rangeRestrict_surjective⟩
  haveI : IsDiscreteValuationRing Λ := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eΛ
  have hlu : ¬ IsUnit ((D.ntw.l i : ℕ) : Λ) := fun e => by
    have := e.map eΛ.symm
    rw [map_natCast] at this
    exact D.ntw.O_l i this
  have hΛ : ∀ z ∈ (ρ.e i b).fieldRange, z ∈ Λ ∨ z⁻¹ ∈ Λ := by
    rintro _ ⟨y, rfl⟩
    rcases ValuationRing.isInteger_or_isInteger (D.ntw.O i) y with ⟨o, ho⟩ | ⟨o, ho⟩
    · exact Or.inl ⟨o, congrArg (ρ.e i b) ho⟩
    · exact Or.inr ⟨o, (congrArg (ρ.e i b) ho).trans (map_inv₀ _ _)⟩
  obtain ⟨e, he⟩ := GlobalTheory.TowerPlace.placeIn_unique Λ _ hl hlu
  obtain ⟨c₁, hc₁⟩ := intForm_descent_below _ e hl
  refine ⟨ph * c₀, mul_ne_zero hph0 hc₀, fun P' hP' F' hF => ?_⟩
  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (ρ.B i j b).F.BS hB.wt hm
  have hlam : (ρ.B i j b).w.lam = lamV D j :=
    GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 Rl.toLevCh A3.A.μ0 j _ hcore.lev hB (hpin.mu0 i j b) (hpin.ap i j b) (hpin.am i j b)
  obtain ⟨v, hvc, hv⟩ := exists_vec_of_small j hlam F'
  have hio' : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j v) = c₀ • P' := by
    obtain ⟨u', w₀, hu', -, hw⟩ := IsChosenExtremalVector.io _ (hti.hv₀ j _) hio
    obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
    exact IsScaleAt.ioP_eq (Rl := Rl) (c0 := c0L j) hsc hinj hP' (ioP_mem_harmonic hcore.lev hcore.thP (hcore.models.cV j) hB
      (hpin.psi i j b) (hpin.inf i j b)
      (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
      _ w₀ hw _) (hF.trans hv)
  let v' : VsV D j ℂ := ⟨MvPolynomial.map D.what₂.embLL v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ v.2⟩
  have hv' : cC v' = c0L j v := hcC v _ rfl
  obtain ⟨c₂, hc₂⟩ := hS _ hl h hh (Submodule.span ℤ {v'}) (Submodule.fg_span_singleton _)
  refine ⟨c₁ + c₂, fun Q M hQ a => ?_⟩
  have hsub : half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) ⊆ Q := fun P hP => admissibleConjugatePairPlaces_subset i Q M (mem_half.1 hP).1
  have hgood := GlobalTheory.UnivGood.univOf_good D D.nd D.ntw ρ hρ D.nexp i Q M
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) := GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D D.nd D.ntw ρ hρ i j b _
    (fun P hP => hQ.1 P (admissibleConjugatePairPlaces_subset i Q M hP)) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))

  obtain ⟨C, hG, hcl, hL0, hLe, hpd, hQpd, hchi, hres⟩ := exists_cover_coprime YS hρ i j b hRF hT hti.alg hgal hval hray hde hU
    (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (fun P hP => hQ.2.1 P (hsub hP)) (hQ.2.2.mono_left hsub) (κ j).n
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hG.1.2.2.1
  obtain ⟨la, -, hla, hl1, hl2⟩ := he _ C.σ₂ fun x => hΛ _ (hLe ⟨x, rfl⟩)
  obtain ⟨p, -, hp, -, -⟩ := he _ T.σ₀ fun x => hΛ _ (hLe ⟨C.inc x, hσ₂ x⟩)
  have hpla := comap_eq_of_le_one_iff C.inc p la fun x => by rw [← hla, ← hp, hσ₂]
  refine ⟨p, fun x => by rw [GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff, ← hp]; rfl, ?_⟩
  have hM : C.d.l₂.M = T.Q.l.M * C.d.pd := hG.1.1.2.1
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have hPg : ∀ PP ∈ (ρ.B i j b).G.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hρ.Pg i j b
  have hN : ∀ PP, PP ∈ (ρ.B i j b).G.Pg ∨ PP ∈ (ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) →
      ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rintro PP (hP | hP)
    · obtain ⟨k, hk⟩ := hPg PP hP
      refine GlobalTheory.HalfCompare.mem_of_dvd hk (Dvd.dvd.mul_right ?_ _)
      rw [hMg]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    · rcases Finset.mem_union.1 hP with hP | hP
      · rw [hρ.delta] at hP
        exact GlobalTheory.HalfCompare.mem_of_dvd ((mem_pD_iff i PP).1 (mem_half.1 hP).1) (hpd.mul_left _)
      · exact GlobalTheory.HalfCompare.mem_of_dvd (hQpd PP hP) (dvd_mul_left _ _)
  have hcop : Nat.Coprime (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK) (T.Q.l.M * C.d.pd) := by
    refine Nat.Coprime.mul_right ?_ hG.2.2.1.2.2.2.2.symm
    rw [hMg]
    exact Nat.Coprime.mul_right (GlobalTheory.CoverHalf.g_coprime D 0).symm (GlobalTheory.CoverHalf.g_coprime D 1).symm
  have hδ := isDelta_delAt Rl.C (D.ntw.l i)
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi :=
    ⟨hpin.delta i j b, hδ.fin, hδ.triv, hδ.tame, fun w hw => hδ.unr w fun h0 => hw (GlobalTheory.HalfCompare.mem_of_dvd h0 hpd),
      fun w hw => by
        obtain ⟨y, hy⟩ := valuesIn_delAt hval _ w hw
        obtain ⟨z, hz⟩ := hL0 ⟨y, rfl⟩
        exact ⟨z, hz.trans hy⟩⟩
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at h1
    exact h1
  obtain ⟨_, ⟨z, rfl⟩, ⟨mz, hmz, hz⟩, xi, hxi, hθ⟩ := theta_twist (R := Rl.toRealDat) hcore.lev hcore.thP j C.σ₂ hG.2.2.1.1 htw hω' h
  have hzi : la.valuation _ z ≤ 1 := (hla z).1 (mem_of_pow_eq_one hmz hz (hΛ _ (hLe ⟨z, rfl⟩)))
  have hTC : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T j (D.ntw.l i) C := ⟨hG.1, hG.2.2.1.2.1, hcl, hG.2.2.1.2.2.2.2⟩
  have hFB : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.FieldBig Rl.toRealDat (Submodule.span ℤ {v'}) C := by
    refine ⟨GlobalTheory.Member.character_quotient_values_in_embedding_field.small_quot_values D Γ Pl0 T0 A3.A _ Rl.toRealDat j _ C.σ₂ hG.2.2.2.1, fun w hw m => ?_,
      hM ▸ containsRayField_of_rayIn C.σ₂ hG.2.2.2.2⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 : MvPolynomial.coeff m (v' : Pol ℂ D.what₂.Tau (Vc D j).rank) ∈ C.σ₂.fieldRange := by
      change MvPolynomial.coeff m (MvPolynomial.map D.what₂.embLL v.1) ∈ _
      rw [MvPolynomial.coeff_map]
      exact hL0 (hvc m)
    have h2 := zsmul_mem h1 r
    rw [← MvPolynomial.coeff_smul] at h2
    exact h2

  let k : Subring ℂ := C.σ₂.range ⊓ Λ
  have hk : ∀ {H : Type} [Group H] [Finite H] (f : H →* ℂˣ) (x : H), ((f x : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange →
      ((f x : ℂˣ) : ℂ) ∈ k := fun {H} _ _ f x hx => ⟨hx, mem_of_pow_eq_one (m := Nat.card H) Nat.card_pos
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]) (hΛ _ (hLe hx))⟩
  haveI : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

  have hser : ∀ a', ∃ φ ∈ C.intForms (wtA (κ j)) (κ j).n {la}, castDict hV φ =
      (((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * c₀)) • series (ρ.B i j b).F (ρ.om i j b 1)
      ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') h P' := fun a' => by
    obtain ⟨hd1, hd2⟩ := isLevelFn_datumFn hB hadm (fun PP hP => GlobalTheory.HalfCompare.not_mem_of_coprime PP hcop (hN PP hP)) _ hN
      k (fun g => hk _ _ (hchi g)) (fun PP hP x => by
        obtain ⟨k, hk'⟩ := hPg PP hP
        exact hk _ _ (hL0 (char_mem_of_over hroots hk' _ x))) (fun PP hP x => hk _ _ (hres PP hP x))
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))
      fun PP y => ⟨SubfieldClass.ratCast_mem C.σ₂.fieldRange _, by
        have h1 := GlobalTheory.NormUnit.normProd_inv_mem D ρ i b {PP.1} (Finset.disjoint_singleton_left.2
          (Finset.disjoint_left.1 hQ.2.2 (hsub PP.2)))
        rw [normProd, Finset.prod_singleton] at h1
        rw [Base.univFam, univCoef_eq]
        push_cast
        rw [← inv_pow]
        exact mul_mem (pow_mem h1 _) (natCast_mem Λ _)⟩
    have hth := Base.isThetaAt_vecAt hB hadm
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))
    have hft := Base.isThetaFunO_fock_vecAt hB hadm
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ)) (c₀ • P')
    have hLV : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelVec Rl.toRealDat j C.d.l₂.M
        ((ρ.B i j b).F.datumFn (ρ.B i j b).G ((ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          ((ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
            fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ)))
        ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') := by
      refine ⟨_, _, GlobalTheory.RefDatumLev.isIdemSum_conjPl (isIdemSum_halfIdem hadm.1), fun PP hPP => ?_, ?_, ?_⟩
      · obtain ⟨P1, hP1, rfl⟩ := Finset.mem_image.1 hPP
        show Formalism.L2.DIV.starOHom ((C.d.l₂.M : ℕ) : 𝓞 D.host.E) ∈ P1.asIdeal
        rw [map_natCast, hM]
        rcases Finset.mem_union.1 hP1 with h1 | h1
        · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 h1
          show Formalism.L2.DIV.starOHom ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
          rw [map_natCast]
          exact hN P0 (Or.inl hP0)
        · exact hN P1 (Or.inr h1)
      · rw [Formalism.L2.Theta.cA_cA, hM]
        rw [hpin.latS, hpin.latT] at hd1
        exact hd1
      · rw [Formalism.L2.Theta.cA_cA]
        unfold Frame.lat at hth
        rw [hpin.psi, hpin.latS, hpin.latT, hpin.vac] at hth
        exact hth
    obtain ⟨φ, hφ, hφg⟩ := hc₂ C hTC hG.2.1 hFB {la} (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hl1) xi hxi _ _ hLV
      (fun t => by
        obtain ⟨⟨y, hy⟩, h2⟩ := hd2 t
        exact ⟨y, hy, fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact (hla y).1 (hy ▸ h2)⟩)
      v' (Submodule.mem_span_singleton_self _)
    have h3 := GlobalTheory.Cmp.SeriesRay.sum_mem_intForms C _ _ {la} (fun _ : Fin 1 => z)
      (fun _ q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hzi) (fun _ => φ) fun _ => hφ
    rw [Fin.sum_univ_one] at h3
    refine ⟨_, h3, ?_⟩
    rw [castDict_smul, mul_smul, ← hpin.phase_mul_thetaKO i b hio']
    funext g
    have e1 : harmVec Rl.toRealDat j u (c0L j v) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') = (ρ.B i j b).F.fock
        ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') (c₀ • P') := by
      rw [← hio', GlobalTheory.ExportSeries.Frame.fock, hpin.psi, hpin.inf, hpin.cartT, hpin.onbT, funext (hpin.onbS i j b)]
      rfl
    rw [hpin.psi] at hft
    have e2 := hθ _ (e1.symm ▸ hft : IsThetaFunO _ _ _ (harmVec Rl.toRealDat j u (c0L j v) _)) g
    have e3 : castDict hV φ g = ((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D j) g)) : ℂˣ) : ℂ) *
        thetaKO (Rl.toRealDat.ωP j A3.A.μ0) h g (harmVec Rl.toRealDat j u (c0L j v)
          ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a')))) :=
      (hφg g).trans (congrArg (fun w => ((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph *
        (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D j) g)) : ℂˣ) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.series Rl.toRealDat j u h
          ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
          (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') w g))) hv')
    rw [Pi.smul_apply, Pi.smul_apply, e3, smul_eq_mul, smul_eq_mul]
    beta_reduce
    rw [e2]
    ring

  have hsum : ∃ φ ∈ C.intForms (wtA (κ j)) (κ j).n {la}, castDict hV φ =
      (((D.ntw.l i : ℕ) : ℂ) ^ c₂ * (ph * c₀)) • ρ.xi i j b D.nexp Q M h P' a := by
    choose φ hφ hφe using hser
    obtain ⟨Φ, h1, h2⟩ := exists_sum_fibres hV hRF hT hG.1 hG.2.2.2.2 hgood
      (fun PP hP => hN PP (Or.inr (Finset.mem_union_right _ hP))) a _ _ _ φ hφ
    refine ⟨Φ, h1, funext fun g => ?_⟩
    rw [h2, hφe, Pi.smul_apply, Pi.smul_apply]
    exact congrArg _ (Base.xiCoef_apply _ _ _ _ _ _ _ _ _).symm
  obtain ⟨φ, hφ, hφe⟩ := hsum

  have hlast : (κ j).LastPos := fun τ k hk => by
    rw [(hti.kap j τ).1 k]
    exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n := by
    rw [(hti.kap j (D.eTau.symm 1)).2.2]
    exact hnV
  have hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n) ≤
      Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
        rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
          (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)}) := by
    refine (GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ (inR j) (κ j) hlast hn T.σ₀ T.toCore.good_σ₀).trans
      (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))
    · exact ((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀
    · exact Formalism.L2.Pj.rdU_mem_offZero _ _
  have hinv : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := fun k hk g => by
    rw [LevelInv.apply_eq_castDict hV φ (g * k), LevelInv.apply_eq_castDict hV φ g, LevelInv.cast_mul hV g k, hφe]
    have hlift := (GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV
      (cast (congrArg (GA D) hV) k)).2 (by rw [cast_cast, cast_eq]; exact hk)
    rw [Pi.smul_apply, Pi.smul_apply]
    refine congrArg _ (DualType.xiCoef_mul_right_of_red hB (D.sp.V_sig _) hgood hadm (Base.isAdmFam_univFam _ _ _) hω
      hlift.1 ?_ (fun PP hPP => ?_) h P' a _)
    · rw [hpin.frT]
      exact parLev_St hlift.2.1
    · rw [hpin.frT]
      exact (GlobalTheory.PrincipalLevel.upperLeftBlock_eq_one_iff_of_mem_blockTri _ (rank_Wc j).symm _).1 (congrFun hlift.2.2 ⟨PP, (hpin.Pg i j b ▸ hPP : PP ∈ Rl.Pg)⟩)
  obtain ⟨m, x, ψ, hx, hψ, hsum⟩ := hc₁ D T hT _ (inR j) (κ j) hlast (dom_wtA _) hspan (mu_mul_level hcore.lev hti j) C hG.1
    (hG.2.1 _ (dom_wtA _)) la p hpla hl1 hl2 φ hφ hinv
  choose o ho using fun k => (hla (x k)).2 (hx k)
  refine ⟨m, o, ψ, hψ, ?_⟩
  rw [pow_add, mul_assoc, mul_smul, ← hφe, ← castDict_smul, hsum]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [ho k])

end Main

end GlobalTheory.XiIntSteps

section Bundles
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)

theorem GlobalTheory.XiIntSteps.xi_int_core_forms : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∀ hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j, ∃ la : HeightOneSpectrum (𝓞 X.core.Q.c.F), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) ∧ ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) := by
  intro hA _ hSI D X E Y hF hP hde i _ j b s h hd
  have hC := X.char
  have ht : Formalism.IndefR.FWT.TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hpb : X.core.pb = X.R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs X.core.toCore X.R.toRealDat X.geo.fw.laws.toLawsM hC.lev ((X.geo.pins j).2.tuple ()).half
  have hV₀ : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
    X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀
  obtain ⟨u, hu, H⟩ := GlobalTheory.XiIntSteps.xi_int_of_ties (F := X.F.lv2) Y.YS X.geo.κ X.geo.v₀ Y.Z.good i j b
    (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hA) hSI hV₀ Y.Z.pin
    ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩ X.size
    ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ ht hio hpb (X.std j) (hP j hV₀) hF.galois hF.vals hF.ray hF.roots hde hd.fin
  refine ⟨u, hu, fun P hP F hPF => ?_⟩
  obtain ⟨c, hc⟩ := H P hP F hPF
  exact ⟨c, fun Q M hQ _ a _ => hc Q M hQ a⟩

end Bundles
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_series_coefficients_integral_core_forms : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∀ hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j, ∃ la : HeightOneSpectrum (𝓞 X.core.Q.c.F), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) ∧ ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) := by
  atlas_forward_decl GlobalTheory.XiIntSteps.xi_int_core_forms
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DictionaryCast
open Formalism.IndefR.FWT Formalism.L2.Pj
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem evW_smul (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (j : Fin D.R.m) (a : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (a • x) = sg0 D A3.A a • evW YS v₀ j x := by
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ, map_smul]
  rfl

theorem castDict_sum_smul' {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ' {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

end GlobalTheory.DictionaryCast

theorem GlobalTheory.XiIntCore.supLattice_comb_of_baseInt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) (b : Bool) (hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j) (la : HeightOneSpectrum (𝓞 X.core.Q.c.F)), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) → ∀ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) → ∃ (n' : ℕ) (o' : Fin n' → D.ntw.O i) (m : Fin n' → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) = ∑ k, Y.Z.ρ.eO i b (o' k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hA hR hI D X E Y hF hP i hi j b hV la hla n o ψ hψ
  have hev : X.geo.fw.Evaluates := X.geo.fw.evaluates_of_lUnif X.unif
  have hσ : FWT.res X.core (sg0 D X.A3.A) = X.core.σ₀ := by
    rw [show sg0 D X.A3.A = D.what₂.embLL from sgAt_mk _ X.R.hv0]
    exact FWT.res_embLL X.core X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1
  have hV' : X.core.V ((j : ℕ) + 1) (FWT.res X.core (sg0 D X.A3.A)) = Wc D j := by rw [hσ]; exact hV
  have hlast : (X.geo.κ j).LastPos := fun τ k hk => by
    rw [(X.geo.fw.kap j τ).1 k]; exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hinR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have key : ∀ k, ∃ (o'' : D.ntw.O i) (m : NX.FmK Y.S ((j : ℕ) + 1)), Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK ∧
      FWT.castDict hV (ψ k) = Y.Z.ρ.eO i b o'' • evW Y.YS X.geo.v₀ j (Subtype.val m) := by
    intro k
    obtain ⟨f, ⟨hsec, hhol, hint⟩, hfk⟩ := hψ k
    have hcu := GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D X.core X.geo.fw.laws _ hinR (X.geo.κ j) hlast f hsec hhol
    let fc : FWT.Cu X.core X.geo.κ j := ⟨f, hcu⟩
    have hball : ∀ y : (X.R.FW j).Pt la, (X.R.FW j).nrm la y (X.geo.fw.e j fc) ≤ 1 := fun y => by
      rw [X.geo.fw.nrm_eq]
      exact (X.core.nrmM_le_one_iff _ la _ _).2 (hint la rfl _ (X.geo.fw.pt j la y).2)
    obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (X.R.FW j) (X.integral j).2.1.2 la _ hball
    set w := X.geo.fw.e j fc with hw
    have hx₀ : evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) =
        FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      refine Eq.trans ?_ (hev j (sg0 D X.A3.A) (by rw [hσ]; exact X.core.toCore.good_σ₀) hV' fc)
      simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hsm : s • (w : Fin (X.R.nW j) → D.what₂.LL) =
        algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F) • (w : Fin (X.R.nW j) → D.what₂.LL) := by
      rw [algebraMap_smul]
      exact (algebraMap_smul X.core.Q.c.F s _).symm
    let m : NX.FmK Y.S ((j : ℕ) + 1) := ⟨(Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL)),
      ((Y.YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM.fst)⟩
    have hmK : Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK :=
      ((Y.YS.fi j).mkK _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM)
    have hsσ : sg0 D X.A3.A (algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F)) = X.core.σ₀ (s : X.core.Q.c.F) :=
      congrArg (fun τ : X.core.Q.c.F →+* ℂ => τ (s : X.core.Q.c.F)) hσ
    have hevm : evW Y.YS X.geo.v₀ j (Subtype.val m) =
        X.core.σ₀ (s : X.core.Q.c.F) • evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) := by
      change evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL))) = _
      rw [hsm, LinearEquiv.map_smul, GlobalTheory.DictionaryCast.evW_smul, hsσ]
    have hs0 : (s : X.core.Q.c.F) ≠ 0 := fun h => hs (by
      rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact la.asIdeal.zero_mem)
    have hinv : FinitePlace.mk la ((s : X.core.Q.c.F)⁻¹) ≤ 1 := by
      rw [map_inv₀, FinitePlace.mk_apply, (FinitePlace.norm_eq_one_iff_notMem X.core.Q.c.F la s).mpr hs, inv_one]
    obtain ⟨o'', ho''⟩ := (hla _).1 hinv
    refine ⟨o'', m, hmK, ?_⟩
    have hc : FWT.castDict hV (ψ k) = FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      rw [← hfk]
      funext g
      exact (GlobalTheory.DictionaryCast.castDict_phiJ' hσ hV' hV _ _ g).symm
    rw [hc, ← hx₀, hevm, ho'', smul_smul, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hs0), one_smul]
  choose o'' m hm he using key
  refine ⟨n, fun k => o k * o'' k, m, hm, ?_⟩
  funext g
  rw [GlobalTheory.DictionaryCast.castDict_sum_smul', Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.XiIntCore.xi_int_core : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h hd
  obtain ⟨u, hu, hA⟩ := GlobalTheory.T.universal_series_coefficients_integral_core_forms hAR hSR hSI D X E Y hF hFP hF.split i hi j b s h hd
  refine ⟨u, hu, fun P hP F hPF => ?_⟩
  obtain ⟨c, hc⟩ := hA P hP F hPF
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨la, hla, n, o, ψ, hψ, he⟩ := hc Q M hQ hs a (X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀)
  obtain ⟨n', o', m, hm, he'⟩ := GlobalTheory.XiIntCore.supLattice_comb_of_baseInt hAR hSR hSI D X E Y hF hFP i hi j b _ la hla n o ψ hψ
  exact ⟨n', o', m, hm, he.trans he'⟩
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integral_core_supLattice_combination : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  atlas_forward_decl GlobalTheory.XiIntCore.xi_int_core
end

section
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntExpOnto

theorem exists_harm_complex {D : D7} (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    (F : Pol ℂ D.what₂.Tau n) (hF : F ∈ VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam F := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • Onto.coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [Onto.coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (Onto.coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, Onto.invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle ⟨F, hF, rfl⟩

theorem exists_harm {D : D7} (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (F : VV K w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn σ w.lam (F : Pol K D.what₂.Tau n) := by
  obtain ⟨P, hP, e⟩ := exists_harm_complex m n w B hw hm (MvPolynomial.map σ F.1) (GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F.2)
  refine ⟨P, hP, e.trans (funext fun x => ?_)⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

theorem onto : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  intro _ _ _ D X E Y _ _ i _ j b F
  have hB := Y.Z.good.base i j b
  refine exists_harm _ _ _ _ hB.wt (fun τ => ?_) _ F
  have h1 := hB.sig τ
  have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
  rw [← h1] at h2
  exact h2.le

end GlobalTheory.IntExpOnto
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  atlas_forward_decl GlobalTheory.IntExpOnto.onto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.XiIntComb

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

def Good (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)
    (P : PolF D (Wc D j).rank (Vc D j).rank) : Prop :=
  ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a,
    ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧
      (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a =
        ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k))

variable (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (u : ℂ)

theorem xi_eq_lin (Q : Finset (Pl D.host.E)) (M : ℕ) (P : PolF D (Wc D j).rank (Vc D j).rank) (a) :
    Y.Z.ρ.xi i j b D.nexp Q M h P a = xiLin Y.Z.ρ D.nexp i j b Q M h a P := rfl

theorem good_zero : Good Y i j b s h u 0 := by
  refine ⟨0, fun Q M _ _ a => ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, ?_⟩⟩
  rw [xi_eq_lin, map_zero, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]

theorem good_smul {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (o : D.ntw.O i) :
    Good Y i j b s h u (Y.Z.ρ.eO i b o • P) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o', m, hm, he⟩ := hc Q M hQ hs a
  refine ⟨n, fun k => o * o' k, m, hm, ?_⟩
  rw [xi_eq_lin, map_smul, smul_comm, ← xi_eq_lin, he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, map_mul]

theorem good_add {P P' : PolF D (Wc D j).rank (Vc D j).rank} (hP : Good Y i j b s h u P) (hP' : Good Y i j b s h u P') :
    Good Y i j b s h u (P + P') := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨c', hc'⟩ := hP'
  refine ⟨c + c', fun Q M hQ hs a => ?_⟩
  obtain ⟨n, o, m, hm, he⟩ := hc Q M hQ hs a
  obtain ⟨n', o', m', hm', he'⟩ := hc' Q M hQ hs a
  have hl : Y.Z.ρ.eO i b ((D.ntw.l i : ℕ) : D.ntw.O i) = ((D.ntw.l i : ℕ) : ℂ) := map_natCast _ _
  refine ⟨n + n', Fin.append (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c' * o k)
    (fun k => ((D.ntw.l i : ℕ) : D.ntw.O i) ^ c * o' k), Fin.append m m', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · rw [Fin.append_left]; exact hm k
    · rw [Fin.append_right]; exact hm' k
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [xi_eq_lin, map_add, smul_add, ← xi_eq_lin, ← xi_eq_lin]
    congr 1
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c' * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) by ring,
        mul_smul, he, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]
    · rw [show (((D.ntw.l i : ℕ) : ℂ) ^ (c + c') * u) = ((D.ntw.l i : ℕ) : ℂ) ^ c * (((D.ntw.l i : ℕ) : ℂ) ^ c' * u) by ring,
        mul_smul, he', Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, map_mul, map_pow, hl]

end GlobalTheory.XiIntComb

open GlobalTheory.XiIntComb in
theorem GlobalTheory.XiIntComb.xi_int_comb : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, Y.Z.ρ.IsDatum i j b s h P → ∃ (u : ℂ) (c : ℕ), u ≠ 0 ∧ ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h P hd
  obtain ⟨u, hu0, hgen⟩ := GlobalTheory.T.thetaSeries_integral_core_supLattice_combination hAR hSR hSI D X E Y hF hFP i hi j b s h ⟨hd.split, hd.off, hd.fin, hd.supp, zero_mem _⟩
  have hB := Y.Z.good.base i j b
  have hm : ∀ τ, (Y.Z.ρ.B i j b).w.p τ + (Y.Z.ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (Y.Z.ρ.B i j b).F.BS hB.wt hm
  have key : ∀ φ ∈ coefLatFn (Formalism.L2.Host.embLL0 D) (labLL0 D) (Y.Z.ρ.eO i b).range (Y.Z.ρ.B i j b).w.lam
      ((Y.Z.ρ.B i j b).latAt (finPt _ h)), ∃ P' ∈ (Y.Z.ρ.B i j b).valSpace,
        harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P' = φ ∧ Good Y i j b s h u P' := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h1 =>
      obtain ⟨F, -, rfl⟩ := h1
      obtain ⟨P', h2, h3⟩ := GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions hAR hSR hSI D X E Y hF hFP i hi j b F
      exact ⟨P', h2, h3, hgen P' h2 F h3⟩
    | zero => exact ⟨0, zero_mem _, map_zero _, good_zero Y i j b s h u⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨P₂, a2, rfl, g2⟩ := h2
      exact ⟨P₁ + P₂, add_mem a1 a2, map_add _ _ _, good_add Y i j b s h u g1 g2⟩
    | smul c _ _ h1 =>
      obtain ⟨P₁, a1, rfl, g1⟩ := h1
      obtain ⟨_, o, rfl⟩ := c
      exact ⟨Y.Z.ρ.eO i b o • P₁, Submodule.smul_mem _ _ a1, map_smul _ _ _, good_smul Y i j b s h u g1 o⟩
  obtain ⟨P', h1, h2, ⟨c, hc⟩⟩ := key _ hd.mem.2
  obtain rfl : P = P' := sub_eq_zero.1 (hinj (P - P') (sub_mem hd.mem.1 h1) (by rw [map_sub, h2]; exact sub_self _))
  exact ⟨u, c, hu0, hc⟩
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section
namespace GlobalTheory.XiBound

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {l : O} (hl : l ∈ IsLocalRing.maximalIdeal O) (z : K) :
    ∃ (n : ℕ) (o : O), algebraMap O K o = algebraMap O K (l ^ n) * z := by
  by_cases h0 : l = 0
  · exact ⟨1, 0, by simp [h0]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨⟨a, d⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors O) z
  have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw
    exact (IsLocalRing.mem_maximalIdeal _).1 hl (hw ▸ w.isUnit)
  have hdvd : (d : O) ∣ l ^ k := by
    rw [hv, hw, mul_pow, ← pow_mul]
    exact mul_dvd_mul (Units.isUnit v).dvd (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero he)))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨k, a * t, ?_⟩
  simp only at hz
  rw [ht, map_mul, map_mul, ← hz]
  ring

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  intro hA hR hI D X E Y hF hP i hi j b s h P hd
  classical
  obtain ⟨u, c, hu, hK⟩ := GlobalTheory.XiIntComb.xi_int_comb hA hR hI D X E Y hF hP i hi j b s h P hd
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hFa : Faithful (Y.Z.rd i j b) :=
    realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
      hν X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  have hinj := hFa.injective
  set lam : ℂ := (Y.Z.ν i j b)⁻¹ * (((D.ntw.l i : ℕ) : ℂ) ^ c * u) with hlam

  have step : ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x,
      Y.Z.rd i j b x = Y.Z.ρ.xi i j b D.nexp Q M h P a →
      ∃ x' ∈ D.nexp.Bsup i ((j : ℕ) + 1) b, Y.Z.rd i j b x' = lam • Y.Z.rd i j b x := by
    intro Q M hQ hs a x hx
    obtain ⟨n, o, m, hm, he⟩ := hK Q M hQ hs a
    let y : NX.Fm Y.S i ((j : ℕ) + 1) b :=
      ∑ k, ((show NX.KB Y.S i b from algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) :
        NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1))
    have hy : y ∈ NX.Bsup Y.S i ((j : ℕ) + 1) b := by
      refine Submodule.sum_mem _ fun k _ => ?_
      exact (NX.Bsup Y.S i ((j : ℕ) + 1) b).smul_mem (o k) (Submodule.subset_span ⟨m k, hm k, rfl⟩)
    have hey : evK Y.YS X.geo.v₀ Y.Z.good i j b y = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
      refine (map_sum (evK Y.YS X.geo.v₀ Y.Z.good i j b) (fun k => ((show NX.KB Y.S i b from algebraMap (D.ntw.O i)
        (FractionRing (D.ntw.O i)) (o k)) • ((1 : NX.KB Y.S i b) ⊗ₜ[Y.S.Ks] m k) : NX.KB Y.S i b ⊗[Y.S.Ks] NX.FmK Y.S ((j : ℕ) + 1)))
        Finset.univ).trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [TensorProduct.smul_tmul', evK_tmul, smul_eq_mul, mul_one]
      rfl
    let x' := (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y
    refine ⟨x', (Y.sup i _ b (Nat.le_add_left _ _) j.2 x').2 (by simp only [x', LinearEquiv.apply_symm_apply]; exact hy), ?_⟩
    change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b (Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x') = _
    rw [show Y.YS.eF i _ b (Nat.le_add_left _ _) j.2 x' = y from LinearEquiv.apply_symm_apply _ _, hey, ← he, hx, hlam,
      smul_smul]
  by_cases hex : ∃ μ : FractionRing (D.ntw.O i), Y.Z.ρ.e i b μ = lam
  · obtain ⟨μ, hμ⟩ := hex
    obtain ⟨N, o, ho⟩ := exists_pow_mul_mem (K := FractionRing (D.ntw.O i)) (D.ntw.O_l i) μ⁻¹
    refine ⟨N, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', hx'B, hx'⟩ := step Q M hQ hs a x hx
    have hμx : x' = μ • x := hinj (by rw [hx', map_smulₛₗ, hμ])
    by_cases hμ0 : μ = 0
    · exfalso
      rw [hμ0, map_zero, hlam] at hμ
      have hl : ((D.ntw.l i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero
      exact mul_ne_zero (inv_ne_zero hν) (mul_ne_zero (pow_ne_zero _ hl) hu) hμ.symm
    have : ((D.ntw.l i : D.ntw.O i) ^ N) • x = o • x' := by
      rw [hμx, ← algebraMap_smul (FractionRing (D.ntw.O i)) o, ← algebraMap_smul (FractionRing (D.ntw.O i)) ((D.ntw.l i : D.ntw.O i) ^ N),
        smul_smul, ho, mul_assoc, inv_mul_cancel₀ hμ0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hx'B
  · refine ⟨0, fun Q M hQ hs a x hx => ?_⟩
    obtain ⟨x', -, hx'⟩ := step Q M hQ hs a x hx
    by_cases h0 : Y.Z.rd i j b x = 0
    · rw [hinj (h0.trans (map_zero _).symm), smul_zero]
      exact Submodule.zero_mem _
    · exact absurd (hFa.mem_range_of_smul h0 ⟨x, rfl⟩ ⟨x', hx'⟩) hex

end GlobalTheory.XiBound
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalSeriesCoeff_boundedInSup_of_twistSeriesSideData : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → XiBdd Y.Z.rd := by
  atlas_forward_decl GlobalTheory.XiBound.main
end
