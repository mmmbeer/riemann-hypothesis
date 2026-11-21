import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsChartEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToGradedModelFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.DescGraded

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _

theorem theta_c₀ (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    have e1 : spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) = spMap (Desc.cst (σ.C x).G.hom) ≫ spMap (σ.ρ x) := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc, (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem c₀_mem_W (σ : Setup) (x : Sp σ.R) (r : σ.R) : σ.c₀ r ∈ σ.W x := fun z _ => by
  have := RingHom.congr_fun (theta_c₀ σ x) r
  simp only [RingHom.comp_apply] at this
  rw [this]
  exact regAt_cst _ _ _

theorem W_mul (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a * b ∈ σ.W x := fun z hz => by
  rw [map_mul]; exact (ha z hz).mul (hb z hz)

theorem W_add (σ : Setup) (x : Sp σ.R) {a b : σ.A.left.functionField} (ha : a ∈ σ.W x) (hb : b ∈ σ.W x) :
    a + b ∈ σ.W x := fun z hz => by
  rw [map_add]; exact (ha z hz).add (hb z hz)

theorem sec_mul_left {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) {a b : X.functionField}
    (ha : ∀ x, RegAt x a) (hb : b ∈ Sec D k) : a * b ∈ Sec D k := fun x => by
  obtain ⟨g, hg, h⟩ := hb x
  exact ⟨g, hg, _root_.mul_assoc a b g ▸ (ha x).mul h⟩

theorem finite_height_one {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {f : R} (hf : f ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).preimage
    (f := fun p : PrimeSpectrum R => p.asIdeal) (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset ?_
  rintro p ⟨hp, hfp⟩
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hfp) ?_
  rw [hp]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf)

theorem c₀_f_ne_zero (σ : Setup) : σ.c₀ σ.f ≠ 0 := by
  have e : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    have e2 : spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) =
        spMap (Desc.cst σ.A.hom) ≫ Desc.awayMap σ.f := by
      rw [← Spec.map_comp]; rfl
    have e : spMap σ.c₀ = spMap ((Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f))) := by
      rw [e2, Setup.c₀, spMap_cst, spMap_cst, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e, RingHom.comp_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit σ.f).map _).ne_zero

theorem gradedFam_and_ne_zero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  intro σ
  refine ⟨⟨⟨fun x => ?_, fun x => ?_⟩, fun k => ⟨fun x => ?_, fun x => ?_⟩,
    fun k a ha b hb => ⟨fun x => (ha.1 x).add (hb.1 x), fun x => W_add σ x (ha.2 x) (hb.2 x)⟩,
    fun k r a ha => ⟨sec_mul_left _ _ (fun x => regAt_cst _ x r) ha.1, fun x => W_mul σ x (c₀_mem_W σ x r) (ha.2 x)⟩,
    fun k l a ha b hb => ⟨fun x => ?_, fun x => W_mul σ x (ha.2 x) (hb.2 x)⟩⟩, ?_⟩
  · rw [zero_nsmul]
    exact ⟨1, CartierDiv.isEqn_zero x, by simpa using (unitAt_one x).regAt⟩
  · simpa using c₀_mem_W σ x 1
  · exact (CartierDiv.vanishesAt_zero _ x).regularAt
  · simpa using c₀_mem_W σ x 0
  · rw [add_nsmul]
    exact (ha.1 x).mul (hb.1 x)
  · obtain ⟨k, hk, u, hu, U, -, hU, hx⟩ := σ.amp (genericPoint _)
    have hu0 : u ≠ 0 := by
      have : genericPoint σ.A.left ∈ locus σ.D k u := hU ▸ hx
      exact CartierDiv.GeneratesAt.ne_zero this
    choose m hm using fun x => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ x u
    obtain ⟨M, hM⟩ := ((finite_height_one σ.hf).image m).bddAbove
    refine ⟨k, hk, σ.c₀ σ.f ^ M * u, ⟨?_, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ _).2 fun p hp hfp => ?_⟩,
      mul_ne_zero (pow_ne_zero _ (c₀_f_ne_zero σ)) hu0⟩
    · rw [← map_pow]
      exact sec_mul_left _ _ (fun x => regAt_cst _ x _) hu
    · have hle : m p ≤ M := hM ⟨p, ⟨hp, hfp⟩, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [pow_add, _root_.mul_assoc, ← map_pow]
      exact W_mul σ p (c₀_mem_W σ p _) (hm p)

end GlobalTheory.DescGraded
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDescent_gradedFamily_nonzero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  atlas_forward_decl GlobalTheory.DescGraded.gradedFam_and_ne_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescSpan

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (g : S →+* T) (h : R →+* S) :
    spMap (g.comp h) = spMap g ≫ spMap h := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (Desc.cst p) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, gp, Scheme.fromSpecStalk_appTop]
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.ΓSpecIso_naturality]
  ext r
  simp [Desc.cst, Cartier.fnOf]

theorem cst_comp_spMap {X : Scheme.{0}} [IsIntegral X] {R S : Type} [CommRing R] [CommRing S] (p : X ⟶ Sp S)
    (g : R →+* S) : Desc.cst (p ≫ spMap g) = (Desc.cst p).comp g := by
  have h : spMap (Desc.cst (p ≫ spMap g)) = spMap ((Desc.cst p).comp g) := by
    rw [spMap_comp', ← gp_comp, ← gp_comp, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (q : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst q r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem theta_c₀ (σ : Setup) (x : Sp σ.R) (r : σ.R) :
    σ.θ x (σ.c₀ r) = Desc.cst (σ.C x).G.hom (σ.ρ x r) := by
  obtain ⟨l, h1, h2⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, ← gp_comp, ← gp_comp, ← Category.assoc, ← h2, Category.assoc,
      (σ.cart x).w, ← Category.assoc, ← Category.assoc, h1, Category.assoc]
  exact congrArg (fun q : σ.R →+* _ => q r) (congrArg CommRingCat.Hom.hom (Spec.map_injective e))

theorem mem_W_mul (σ : Setup) (x : Sp σ.R) {u : σ.A.left.functionField} (hu : u ∈ σ.W x) (r : σ.R) :
    σ.c₀ r * u ∈ σ.W x := fun z hz => by
  rw [map_mul, theta_c₀]
  exact (regAt_cst _ _ _).mul (hu z hz)

section Sec

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {k : ℕ}

theorem sec_zero : (0 : X.functionField) ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [zero_mul]; exact regAt_zero x)

theorem sec_add {u v : X.functionField} (hu : u ∈ Sec D k) (hv : v ∈ Sec D k) : u + v ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [add_mul]; exact (hg.regularAt_iff.1 (hu x)).add (hg.regularAt_iff.1 (hv x)))

theorem sec_mul {u c : X.functionField} (hu : u ∈ Sec D k) (hc : ∀ x, RegAt x c) : c * u ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [_root_.mul_assoc]; exact (hc x).mul (hg.regularAt_iff.1 (hu x)))

end Sec

theorem finite_vert (σ : Setup) :
    {p : Sp σ.R | p.asIdeal.height = 1 ∧ σ.f ∈ p.asIdeal}.Finite := by
  have hfin := (Ideal.span {σ.f}).finite_minimalPrimes_of_isNoetherianRing
  refine (hfin.preimage fun a _ b _ h => PrimeSpectrum.ext h).subset fun p hp => ?_
  obtain ⟨h1, hf⟩ := hp
  have : p.asIdeal.FiniteHeight := (Ideal.finiteHeight_iff _).2 (Or.inr (by rw [h1]; exact ENat.one_ne_top))
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hf) ?_
  rw [h1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero σ.hf)

end GlobalTheory.DescSpan

open GlobalTheory.DescSpan in

theorem GlobalTheory.Desc.sec_eq_spanBy_N : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  intro σ k
  have hc₀ : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := cst_comp_spMap _ _
  ext u
  constructor
  · intro hu
    choose m hm using fun p : Sp σ.R => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ p u
    let M := ∑ p ∈ (finite_vert σ).toFinset, m p
    let v := σ.c₀ (σ.f ^ M) * u
    have hv : v ∈ σ.N k := by
      refine ⟨sec_mul hu fun x => by rw [hc₀]; exact regAt_cst _ _ _, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ v).2 fun p h1 hf => ?_⟩
      have hle : m p ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        ((finite_vert σ).mem_toFinset.2 ⟨h1, hf⟩)
      have e : v = σ.c₀ (σ.f ^ (M - m p)) * (σ.c₀ σ.f ^ m p * u) := by
        simp only [v, map_pow]
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact mem_W_mul σ p (hm p) _
    refine ⟨1, fun _ => IsLocalization.Away.invSelf σ.f ^ M, fun _ => v, fun _ => hv, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [v, hc₀, RingHom.comp_apply, map_pow]
    rw [← _root_.mul_assoc, ← mul_pow, ← map_mul, mul_comm (IsLocalization.Away.invSelf σ.f),
      IsLocalization.Away.mul_invSelf, map_one, one_pow, _root_.one_mul]
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Finset.sum_induction _ (· ∈ Sec σ.D k) (fun _ _ => sec_add) sec_zero
      fun i _ => sec_mul (ht i).1 fun x => regAt_cst _ _ _
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  atlas_forward_decl GlobalTheory.Desc.sec_eq_spanBy_N
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem unitAt_of_mul_right {X : Scheme.{0}} [IsIntegral X] {x : X} {a b : X.functionField}
    (ha : RegAt x a) (hb : RegAt x b) (h : UnitAt x (a * b)) : UnitAt x b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨w, hw, e⟩ := h
  rw [← map_mul] at e
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField e
  exact ⟨b', isUnit_of_mul_isUnit_right hw, rfl⟩

theorem regAt_cst {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (cst p r) :=
  regAt_fnOf (x := x) (U := ⊤) trivial trivial _

theorem exists_locus_of_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  intro R₁ F _ _ Y _ q θ N D₁ hA hS y
  obtain ⟨k, hk, u, hu, U, -, hU, hy⟩ := hA y
  have hyu : y ∈ locus D₁ k u := hU ▸ hy
  have hu' : u ∈ spanBy (cst q) (θ '' N k) := hS k ▸ hu
  obtain ⟨n, r, t, ht, rfl⟩ := hu'
  obtain ⟨g, hg⟩ := (k • D₁).exists_isEqn y
  have hunit : UnitAt y ((∑ i, cst q (r i) * t i) * g) := hg.generatesAt_iff.1 hyu
  have hsec : ∀ i, RegAt y (t i * g) := fun i => by
    have : t i ∈ Sec D₁ k := by rw [hS k]; exact subset_spanBy _ _ (ht i)
    exact hg.regularAt_iff.1 (this y)
  by_contra hne
  push_neg at hne
  apply (zeroAt_iff.1 ?_).2 hunit
  rw [Finset.sum_mul]
  refine Finset.sum_induction _ (ZeroAt y) (fun _ _ => ZeroAt.add) (zeroAt_zero y) fun i _ => ?_
  rw [_root_.mul_assoc]
  refine zeroAt_iff.2 ⟨(regAt_cst q y (r i)).mul (hsec i), fun hu => ?_⟩
  obtain ⟨b, hb, hbt⟩ := ht i
  apply hne k hk b hb
  show (k • D₁).GeneratesAt y (θ b)
  rw [hg.generatesAt_iff, hbt]
  exact unitAt_of_mul_right (regAt_cst q y (r i)) (hsec i) hu

end GlobalTheory.Desc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierSectionLocus_of_ample_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  atlas_forward_decl GlobalTheory.Desc.exists_locus_of_span
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GenGlue

lemma isDominant_of_spec {K : Type} [Field K] {W : Scheme.{0}} (v : Sp K ⟶ W)
    (h : ∀ (q : Sp K) (z : W), v q ⤳ z) : IsDominant v :=
  ⟨fun z => closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (IsLocalRing.closedPoint K)))
    (specializes_iff_mem_closure.1 (h _ z))⟩

theorem exists_glue : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) →
    ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P),
    (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) →
    ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  intro Y P _ _ U hU f w hw
  have hgp : ∀ q, gp Y q = genericPoint Y := fun q => by
    obtain rfl : q = IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
    exact Scheme.fromSpecStalk_closedPoint
  have hgen : ∀ (V : Y.Opens) (y : Y), y ∈ V → genericPoint Y ∈ V := fun V y hy =>
    ((genericPoint_spec Y).mem_open_set_iff V.2).2 ⟨y, trivial, hy⟩
  have hlift : ∀ V : Y.Opens, genericPoint Y ∈ V →
      ∃ l : Sp Y.functionField ⟶ V.toScheme, l ≫ V.ι = gp Y := fun V hV =>
    ⟨IsOpenImmersion.lift V.ι (gp Y) (by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨q, rfl⟩; rw [hgp]; exact hV), IsOpenImmersion.lift_fac _ _ _⟩
  have hdom : ∀ (V : Y.Opens) (l : Sp Y.functionField ⟶ V.toScheme), l ≫ V.ι = gp Y → IsDominant l := by
    intro V l hl
    refine isDominant_of_spec l fun q z => ?_
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e1 : V.ι (l q) = gp Y q := by rw [← hl]; rfl
    rw [e1, hgp]
    exact (genericPoint_spec Y).specializes trivial
  let g : Y → Y.PartialMap P := fun y => ⟨U y, (U y).2.dense ⟨y, hU y⟩, f y⟩
  have heq : ∀ y y', (g y).toRationalMap = (g y').toRationalMap := by
    intro y y'
    rw [Scheme.PartialMap.toRationalMap_eq_iff]
    let V := U y ⊓ U y'
    have hV : genericPoint Y ∈ V := ⟨hgen _ y (hU y), hgen _ y' (hU y')⟩
    obtain ⟨l, hl⟩ := hlift V hV
    haveI := hdom V l hl
    refine ⟨V, V.2.dense ⟨_, hV⟩, inf_le_left, inf_le_right, ?_⟩
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
    refine ext_of_isDominant l ?_
    rw [← Category.assoc, ← Category.assoc,
      hw y _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl]),
      hw y' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl])]
  let y0 := genericPoint Y
  let F := (g y0).toRationalMap
  have htop : F.domain = ⊤ :=
    top_le_iff.1 fun z _ => Scheme.RationalMap.mem_domain.2 ⟨g z, hU z, heq z y0⟩
  have htop' : F.toPartialMap.domain = ⊤ := htop
  let k : Y ⟶ F.toPartialMap.domain.toScheme := IsOpenImmersion.lift F.toPartialMap.domain.ι (𝟙 Y)
    (by rw [Scheme.Opens.range_ι, htop']; simp)
  have hk : k ≫ F.toPartialMap.domain.ι = 𝟙 Y := IsOpenImmersion.lift_fac _ _ _
  have hgpm : gp Y ≫ k ≫ F.toPartialMap.hom = w := by
    obtain ⟨l, hl⟩ := hlift (U y0) (hU y0)
    have h2 : (g y0).domain.ι ≫ k = Y.homOfLE (g y0).le_domain_toRationalMap := by
      apply (cancel_mono F.toPartialMap.domain.ι).1
      rw [Category.assoc, hk, Category.comp_id]
      exact (Scheme.homOfLE_ι _ _).symm
    rw [← hl]
    rw [Category.assoc, reassoc_of% h2]
    exact (congrArg (l ≫ ·) (g y0).toPartialMap_toRationalMap_restrict).trans (hw y0 l hl)
  refine ⟨k ≫ F.toPartialMap.hom, fun y => ?_, hgpm⟩
  obtain ⟨l, hl⟩ := hlift (U y) (hgen _ y (hU y))
  haveI := hdom _ l hl
  refine ext_of_isDominant l ?_
  rw [reassoc_of% hl, hgpm, hw y l hl]

end GlobalTheory.Desc.GenGlue
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) → ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P), (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) → ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  atlas_forward_decl GlobalTheory.Desc.GenGlue.exists_glue
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.StalkMap

variable {X : Scheme.{0}}

theorem top_le_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem appLE_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (top_le_fromSpecStalk x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (top_le_fromSpecStalk x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

def val {R : Type} [CommRing R] (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

theorem val_congr {R : Type} [CommRing R] {g g' : Sp R ⟶ X} (e : g = g') (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(X, V)) : val g V h u = val g' V h' u := by
  subst e; rfl

theorem val_gp [IsIntegral X] (V : X.Opens) (hV : genericPoint X ∈ V) (h : ⊤ ≤ gp X ⁻¹ᵁ V) (u : Γ(X, V)) :
    val (gp X) V h u = GlobalTheory.Cartier.fnOf V hV u := by
  have : (gp X).appLE V ⊤ h = X.presheaf.germ V _ hV ≫ (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv :=
    appLE_fromSpecStalk (genericPoint X) V hV
  unfold val
  rw [RingHom.comp_apply, this]
  exact (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv_hom_id_apply _

end GlobalTheory.Desc.StalkMap

namespace GlobalTheory.Desc.StalkMap

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem val_appLE (g : Sp R ⟶ X) (φ : X ⟶ X') (V : X'.Opens) (W : X.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(X', V)) :
    val g W h ((φ.appLE V W e).hom u) = val (g ≫ φ) V h' u :=
  congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u))
    (Scheme.Hom.appLE_comp_appLE g φ V W ⊤ e h)

theorem val_top (g : Sp R ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(X, ⊤)) :
    val g ⊤ h u = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  have : g.appLE ⊤ ⊤ h = g.appTop := Scheme.Hom.appLE_eq_app g
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u)) this

theorem val_spMap (σ : R →+* R') (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ (spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(X, V)) : val (spMap σ ≫ g) V h' u = σ (val g V h u) := by
  refine (val_appLE (spMap σ) g V ⊤ h le_top h' u).symm.trans ((val_top (spMap σ) le_top _).trans ?_)
  exact congrArg (fun q => CommRingCat.Hom.hom q ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem fnOf_app_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField) (hm : gp Y ≫ m = spMap φ ≫ gp P) {W : P.Opens}
    (hY : genericPoint Y ∈ m ⁻¹ᵁ W) (hP : genericPoint P ∈ W) (s : Γ(P, W)) :
    GlobalTheory.Cartier.fnOf (m ⁻¹ᵁ W) hY ((m.app W).hom s) = φ (GlobalTheory.Cartier.fnOf W hP s) := by
  have h1 : ⊤ ≤ gp Y ⁻¹ᵁ (m ⁻¹ᵁ W) := top_le_fromSpecStalk _ _ hY
  have h2 : ⊤ ≤ gp P ⁻¹ᵁ W := top_le_fromSpecStalk _ _ hP
  have h3 : ⊤ ≤ (gp Y ≫ m) ⁻¹ᵁ W := h1
  have h4 : ⊤ ≤ (spMap φ ≫ gp P) ⁻¹ᵁ W := hm ▸ h3
  rw [← val_gp _ hY h1, ← val_gp _ hP h2, ← val_spMap φ (gp P) W h2 h4,
    ← val_congr hm W h3 h4, ← val_appLE (gp Y) m W (m ⁻¹ᵁ W) le_rfl h1 h3, Scheme.Hom.app_eq_appLE]

end GlobalTheory.Desc.StalkMap

open GlobalTheory.Desc.StalkMap in

theorem GlobalTheory.Desc.regAt_map_of_gp : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField),
    RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  intro Y P _ _ m φ hm y v hv
  obtain ⟨W, hW, s, rfl⟩ := hv.exists_fnOf
  have hy : y ∈ m ⁻¹ᵁ W := hW
  have hY : genericPoint Y ∈ m ⁻¹ᵁ W := gen_mem hy
  rw [← fnOf_app_eq m φ hm hY (gen_mem hW) s]
  refine ⟨regAt_fnOf hy hY _, ?_⟩
  rw [unitAt_fnOf_iff hy hY, unitAt_fnOf_iff hW (gen_mem hW), ← Scheme.preimage_basicOpen]
  rfl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P) (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField), RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  atlas_forward_decl GlobalTheory.Desc.regAt_map_of_gp
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp_eq_spMap_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (cst p) := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  conv_lhs => rw [h]
  rw [gp]
  erw [Scheme.fromSpecStalk_toSpecΓ_assoc]
  erw [← Spec.map_comp]
  rfl

end GlobalTheory.Desc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R), gp X ≫ p = spMap (cst p) := by
  atlas_forward_decl GlobalTheory.Desc.gp_comp_eq_spMap_cst
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_ringHom_fnOf_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] {U : Y.Opens}
    (hU : genericPoint Y ∈ U) {V : P.Opens} (hVη : genericPoint P ∈ V)
    (φ : P.functionField →+* Y.functionField) (h : ∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) :
    ∃ ψ : Γ(P, V) →+* Γ(Y, U), ∀ s, fnOf U hU (ψ s) = φ (fnOf V hVη s) := by
  choose t ht using fun s => exists_fnOf_eq hU (h s)
  refine ⟨⟨⟨⟨t, ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, ht⟩ <;> apply fnOf_injective U hU
  · rw [ht, map_one, map_one, map_one]
  · rw [map_mul, ht, ht, ht, map_mul, map_mul]
  · exact (ht 0).trans (by rw [map_zero, map_zero, map_zero])
  · exact (ht (a + b)).trans (((congrArg φ (map_add _ a b)).trans (map_add φ _ _)).trans
      ((congrArg₂ (· + ·) (ht a) (ht b)).symm.trans (map_add (fnOf U hU) (t a) (t b)).symm))

set_option backward.isDefEq.respectTransparency false in

theorem exists_hom_of_regAt_fnOf : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  intro Y P _ _ U hU V hV hVη φ h
  obtain ⟨ψ, hψ⟩ := exists_ringHom_fnOf_eq hU hVη φ h
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, fun y => ?_, fun l hl => ?_⟩
  · rw [← Category.assoc, Scheme.Hom.comp_apply]
    change _ ∈ (V : Set P)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  · obtain rfl : l = U.fromSpecStalkOfMem (genericPoint Y) hU := by
      rw [← cancel_mono U.ι, hl]
      exact (Scheme.Opens.fromSpecStalkOfMem_ι U _ hU).symm
    have e : CommRingCat.ofHom ψ ≫ Y.presheaf.germ U (genericPoint Y) hU =
        P.presheaf.germ V (genericPoint P) hVη ≫ CommRingCat.ofHom φ := by
      ext s
      exact hψ s
    have e₁ := Scheme.Opens.fromSpecStalkOfMem_toSpecΓ_assoc U (genericPoint Y) hU
      (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec)
    refine e₁.trans ?_
    rw [← Spec.map_comp_assoc]
    refine (congrArg (fun z => Spec.map z ≫ hV.fromSpec) e).trans ?_
    rw [gp, ← hV.fromSpecStalk_eq_fromSpecStalk hVη, IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc]

end GlobalTheory.Desc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  atlas_forward_decl GlobalTheory.Desc.exists_hom_of_regAt_fnOf
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ToModel

theorem sep (R : Type) [CommRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) [IsSeparated p] : P.IsSeparated := by
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from P) (p ≫ terminal.from _)]
  infer_instance

theorem gp_dom (Y : Scheme.{0}) [IsIntegral Y] : IsDominant (gp Y) := by
  refine ⟨?_⟩
  have h : genericPoint Y ∈ Set.range (gp Y) := ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  refine Dense.mono (Set.singleton_subset_iff.2 h) ?_
  rw [dense_iff_closure_eq, (genericPoint_spec Y).def]

theorem regAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) (m : ℕ) :
    RegAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact (unitAt_one y).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem reg_div (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k m : ℕ) (u a : Y.functionField) (y : Y)
    (ha : a ∈ Sec D (k * m)) (hu : y ∈ locus D k u) : RegAt y (a / u ^ m) := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h1 := ((hg.nsmul (k * m)).regularAt_iff).1 (ha y)
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have e : a / u ^ m = (a * ((g ^ (k * m) : Y.functionFieldˣ) : Y.functionField)) *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ m := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, ← pow_mul]
    field_simp
  rw [e]
  exact h1.mul (regAt_pow h2.inv.regAt m)

theorem locus_open (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k : ℕ) (u : Y.functionField) :
    IsOpen (locus D k u) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨g, hg, hu⟩ := hy
  obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
  obtain ⟨V, hyV, hV⟩ := hu.exists_nhds
  exact ⟨(U ⊓ V : Y.Opens), fun z hz => ⟨g, hU z hz.1, hV z hz.2⟩, (U ⊓ V).2, ⟨hyU, hyV⟩⟩

theorem unitAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : UnitAt y x) (m : ℕ) :
    UnitAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact unitAt_one y
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) {n : ℕ}
    (hn : 1 ≤ n) (hu : UnitAt y (x ^ n)) : UnitAt y x := by
  have hx : x ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_pow (by omega)])
  refine (unitAt_iff hx).2 ⟨h, ?_⟩
  have e : x⁻¹ = x ^ (n - 1) * (x ^ n)⁻¹ := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [e]
  exact (regAt_pow h _).mul hu.inv.regAt

theorem locus_iff {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {k k' : ℕ} (hk : 1 ≤ k)
    {u u' : Y.functionField} {y : Y} (hu : y ∈ locus D k u) (hu' : u' ∈ Sec D k') :
    y ∈ locus D k' u' ↔ UnitAt y (u' ^ k / u ^ k') := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have h1 := ((hg.nsmul k').regularAt_iff).1 (hu' y)
  have e : u' ^ k / u ^ k' = (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k' := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k' k]
    field_simp
  show (k' • D).GeneratesAt y u' ↔ _
  rw [(hg.nsmul k').generatesAt_iff, e]
  constructor
  · intro h
    exact (unitAt_pow h k).mul (unitAt_pow h2.inv k')
  · intro h
    refine unitAt_of_pow h1 hk ?_
    have e2 : (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k =
        ((u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
          ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k') *
        (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ^ k' := by
      have h0 : (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ≠ 0 := h2.ne_zero
      rw [inv_pow, _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.mul_one]
    rw [e2]
    exact h.mul (unitAt_pow h2 k')

theorem pow_mem {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)
    {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : b ^ n ∈ N (k * n) := by
  induction n with
  | zero => simpa using hN.one
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact hN.mul _ _ _ ih _ hb

theorem exists_map_to_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ ρ Y _ q θ D₁ hc hsec hcov
  haveI : IsSeparated p := hM.sep
  haveI : P.IsSeparated := sep R P p
  choose k hk b hb hy using hcov
  have hb0 : ∀ y, b y ≠ 0 := fun y h => (hy y).ne_zero (by rw [h, map_zero])
  let U : Y → Y.Opens := fun y => ⟨locus D₁ (k y) (θ (b y)), locus_open Y D₁ _ _⟩
  have hyU : ∀ y, y ∈ U y := hy
  have hgen : ∀ y, genericPoint Y ∈ U y := fun y => gen_mem (hyU y)
  have hPη : ∀ y, genericPoint P ∈ Dp (k y) (b y) := fun y => (hM.gen _ (hk y) _ (hb y)).2 (hb0 y)
  have hreg : ∀ y (s : Γ(P, Dp (k y) (b y))), ∀ z ∈ U y, RegAt z ((θ.comp ψ) (fnOf _ (hPη y) s)) := by
    intro y s z hz
    obtain ⟨m, a, ha, he⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (ψ (fnOf _ (hPη y) s))).1
      ⟨_, fun z' hz' => regAt_fnOf hz' _ s, rfl⟩
    show RegAt z (θ (ψ _))
    rw [he, map_div₀, map_pow]
    exact reg_div Y D₁ (k y) m (θ (b y)) (θ a) z (hsec _ a ha) hz
  choose f hfV hf using fun y => GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular Y P (U y) (hgen y) (Dp (k y) (b y)) (hM.affine _ (hk y) _ (hb y)) (hPη y)
    (θ.comp ψ) (hreg y)
  obtain ⟨m, hmU, hmg⟩ := GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint Y P U hyU f (spMap (θ.comp ψ) ≫ gp P) hf
  refine ⟨m, ?_, ⟨gp Y, Category.comp_id _, hmg⟩, ?_⟩
  · haveI := gp_dom Y
    refine ext_of_isDominant (gp Y) ?_
    rw [reassoc_of% hmg, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants P R p, ← Category.assoc, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants Y R₁ q, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change θ (ψ (cst p x)) = cst q (ρ x)
    have h1 := congrArg (fun g => g x) hc
    have h2 := congrArg (fun g => g x) hM.const
    simp only [RingHom.comp_apply] at h1 h2
    rw [h2, h1]
  · intro k' hk' b' hb' y
    have hmy : m y ∈ Dp (k y) (b y) := by
      have h1 := hfV y ⟨y, hyU y⟩
      rw [← hmU y] at h1
      exact h1
    rw [hM.mem _ (hk y) _ (hb y) _ hmy k' hk' b' hb']
    obtain ⟨v₀, hv₀, hψ⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (b' ^ (k y) / b y ^ k')).2
      ⟨k', b' ^ (k y), by rw [mul_comm]; exact pow_mem hN hb' _, rfl⟩
    have hst := GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible Y P m (θ.comp ψ) hmg y v₀ (hv₀ _ hmy)
    have hl := locus_iff D₁ (hk y) (hy y) (hsec _ _ hb')
    have e : (θ.comp ψ) v₀ = θ b' ^ (k y) / θ (b y) ^ k' := by
      rw [RingHom.comp_apply, hψ, map_div₀, map_pow, map_pow]
    rw [hl, ← e]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain rfl : v = v₀ := ψ.injective (hvw.trans hψ.symm)
      exact hst.2.2 hv
    · intro h
      exact ⟨v₀, hst.2.1 h, hψ⟩

end GlobalTheory.Desc.ToModel
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  atlas_forward_decl GlobalTheory.Desc.ToModel.exists_map_to_model
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial HomogeneousLocalization
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Desc.GrSpec

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}

def ring (hN : GradedFam c₀ N) : Subring F[X] where
  carrier := {p | ∀ k, p.coeff k ∈ N k}
  mul_mem' {p q} hp hq k := by
    rw [coeff_mul]
    refine Finset.sum_induction _ (· ∈ N k) (fun a b ha hb => hN.add k a ha b hb) (hN.zero k) ?_
    rintro ⟨i, j⟩ hij
    have hij' : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
    subst hij'
    exact hN.mul i j _ (hp i) _ (hq j)
  one_mem' k := by
    rw [coeff_one]
    split_ifs with h
    · subst h; exact hN.one
    · exact hN.zero k
  add_mem' {p q} hp hq k := by rw [coeff_add]; exact hN.add k _ (hp k) _ (hq k)
  zero_mem' k := by rw [coeff_zero]; exact hN.zero k
  neg_mem' {p} hp k := by
    rw [coeff_neg]
    have := hN.smul k (-1) _ (hp k)
    simpa using this

theorem monomial_mem (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) : monomial k b ∈ ring hN := by
  intro j
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact hb
  · exact hN.zero j

def piece (hN : GradedFam c₀ N) (k : ℕ) : AddSubgroup (ring hN) where
  carrier := {p | ∀ j, j ≠ k → (p : F[X]).coeff j = 0}
  add_mem' {p q} hp hq j hj := by
    rw [Subring.coe_add, coeff_add, hp j hj, hq j hj, add_zero]
  zero_mem' j _ := by rw [Subring.coe_zero, coeff_zero]
  neg_mem' {p} hp j hj := by rw [Subring.coe_neg, coeff_neg, hp j hj, neg_zero]

theorem mem_piece_iff (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} :
    p ∈ piece hN k ↔ (p : F[X]) = monomial k ((p : F[X]).coeff k) := by
  constructor
  · intro hp
    ext j
    rw [coeff_monomial]
    split_ifs with h
    · rw [h]
    · exact hp j (Ne.symm h)
  · intro hp j hj
    rw [hp, coeff_monomial, if_neg (Ne.symm hj)]

def hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : ring hN := ⟨monomial k b, monomial_mem hN hb⟩

@[simp] theorem coe_hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) :
    (hel hN k b hb : F[X]) = monomial k b := rfl

theorem hel_mem (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : hel hN k b hb ∈ piece hN k := by
  rw [mem_piece_iff, coe_hel, coeff_monomial, if_pos rfl]

theorem hel_ne_zero (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) (h : b ≠ 0) : hel hN k b hb ≠ 0 := by
  intro e
  have := congrArg (fun p : ring hN => (p : F[X]).coeff k) e
  simp [coeff_monomial] at this
  exact h this

def comp (hN : GradedFam c₀ N) (k : ℕ) : ring hN →+ piece hN k where
  toFun p := ⟨⟨monomial k ((p : F[X]).coeff k), monomial_mem hN (p.2 k)⟩, by
    intro j hj; simp [coeff_monomial, Ne.symm hj]⟩
  map_zero' := by ext; simp
  map_add' p q := by ext; simp

theorem comp_eq_zero (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : (p : F[X]).coeff k = 0) : comp hN k p = 0 := by
  ext; simp [comp, h]

theorem comp_of_mem (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : p ∈ piece hN k) : (comp hN k p : ring hN) = p := by
  ext1; exact ((mem_piece_iff hN).1 h).symm

def dec (hN : GradedFam c₀ N) (p : ring hN) : DirectSum ℕ (fun k => piece hN k) :=
  ∑ k ∈ (p : F[X]).support, DirectSum.of (fun k => piece hN k) k (comp hN k p)

theorem dec_eq (hN : GradedFam c₀ N) (p : ring hN) (S : Finset ℕ) (hS : (p : F[X]).support ⊆ S) :
    dec hN p = ∑ k ∈ S, DirectSum.of (fun k => piece hN k) k (comp hN k p) := by
  refine Finset.sum_subset hS fun k _ hk => ?_
  rw [comp_eq_zero hN (notMem_support_iff.1 hk), map_zero]

def decHom (hN : GradedFam c₀ N) : ring hN →+ DirectSum ℕ (fun k => piece hN k) where
  toFun := dec hN
  map_zero' := by simp [dec]
  map_add' p q := by
    classical
    set S := (p : F[X]).support ∪ (q : F[X]).support ∪ ((p + q : ring hN) : F[X]).support
    rw [dec_eq hN _ S (fun x hx => Finset.mem_union_right _ hx),
      dec_eq hN p S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)),
      dec_eq hN q S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]

instance gradedMonoid (hN : GradedFam c₀ N) : SetLike.GradedMonoid (piece hN) where
  one_mem j hj := by
    change (1 : F[X]).coeff j = 0
    rw [coeff_one, if_neg hj]
  mul_mem i j a b ha hb := by
    rw [mem_piece_iff] at ha hb
    intro l hl
    rw [Subring.coe_mul, ha, hb, monomial_mul_monomial, coeff_monomial, if_neg (Ne.symm hl)]

instance gradedRing (hN : GradedFam c₀ N) : GradedRing (piece hN) :=
  { gradedMonoid hN with
    toDecomposition := DirectSum.Decomposition.ofAddHom (piece hN) (decHom hN)
      (by
        refine AddMonoidHom.ext fun p => Subtype.ext ?_
        change (((DirectSum.coeAddMonoidHom (piece hN)) (dec hN p) : ring hN) : F[X]) = p
        rw [dec, map_sum]
        simp only [DirectSum.coeAddMonoidHom_of]
        rw [AddSubmonoidClass.coe_finset_sum]
        exact (as_sum_support _).symm)
      (by
        refine DirectSum.addHom_ext fun k y => ?_
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
        change dec hN (y : ring hN) = DirectSum.of _ k y
        rw [dec_eq hN _ {k} (fun j hj => by
          by_contra h'
          exact (mem_support_iff.1 hj) (y.2 j (by simpa using h')))]
        rw [Finset.sum_singleton]
        congr 1
        exact Subtype.ext (comp_of_mem hN y.2)) }

section Frac

variable (F) in

def cL : F →+* FractionRing F[X] := (algebraMap F[X] (FractionRing F[X])).comp C

theorem cL_injective : Function.Injective (cL F) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp C_injective

def toL (hN : GradedFam c₀ N) : ring hN →+* FractionRing F[X] :=
  (algebraMap F[X] (FractionRing F[X])).comp (ring hN).subtype

theorem toL_injective (hN : GradedFam c₀ N) : Function.Injective (toL hN) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp Subtype.val_injective

variable (hN : GradedFam c₀ N) (P : Ideal (ring hN)) [P.IsPrime]

def liftAt : Localization.AtPrime P →+* FractionRing F[X] :=
  IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) (g := toL hN) fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (toL_injective hN)).2 fun h => s.2 (h ▸ P.zero_mem))

def valL : AtPrime (piece hN) P →+* FractionRing F[X] :=
  (liftAt hN P).comp (algebraMap (AtPrime (piece hN) P) (Localization.AtPrime P))

theorem valL_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    valL hN P (mk g) = cL F (((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg) := by
  have hnum := (mem_piece_iff hN).1 g.num.2
  have hden := (mem_piece_iff hN).1 g.den.2
  have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
    intro h0
    apply g.den_mem
    have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
    rw [this]; exact P.zero_mem
  change liftAt hN P (mk g).val = _
  rw [val_mk, Localization.mk_eq_mk', liftAt, IsLocalization.lift_mk'_spec]
  change algebraMap F[X] _ ((g.num : ring hN) : F[X]) =
    algebraMap F[X] _ ((g.den : ring hN) : F[X]) * algebraMap F[X] _ (C _)
  rw [← map_mul]
  congr 1
  rw [hnum, hden, coeff_monomial, if_pos rfl, coeff_monomial, if_pos rfl, monomial_mul_C, mul_div_cancel₀ _ hs]

variable (F) in

def eqR : F ≃+* (cL F).range :=
  RingEquiv.ofBijective (cL F).rangeRestrict
    ⟨fun a b h => cL_injective (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

def valR : AtPrime (piece hN) P →+* (cL F).range :=
  (valL hN P).codRestrict (cL F).range fun y => by
    obtain ⟨g, rfl⟩ := mk_surjective y
    exact ⟨_, (valL_mk hN P g).symm⟩

def psiAt : AtPrime (piece hN) P →+* F := (eqR F).symm.toRingHom.comp (valR hN P)

theorem cL_psiAt (y : AtPrime (piece hN) P) : cL F (psiAt hN P y) = valL hN P y :=
  congrArg Subtype.val ((eqR F).apply_symm_apply (valR hN P y))

theorem psiAt_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    psiAt hN P (mk g) = ((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg :=
  cL_injective (by rw [cL_psiAt, valL_mk])

end Frac

section Scheme

variable (hN : GradedFam c₀ N)

instance isPrime_point (x : Proj (piece hN)) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x

def gen {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : Proj (piece hN) :=
  ⟨⊥, Ideal.isPrime_bot, fun h => hel_ne_zero hN hb h0 (by
    have : hel hN k b hb ∈ HomogeneousIdeal.irrelevant (piece hN) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (piece hN) (hel_mem hN k b hb) (by omega)]
    exact h this)⟩

theorem isIntegral {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : IsIntegral (Proj (piece hN)) := by
  have hred : IsReduced (Proj (piece hN)) := by
    have (x : Proj (piece hN)) : _root_.IsReduced ((Proj (piece hN)).presheaf.stalk x) := by
      let x' : ProjectiveSpectrum (piece hN) := x
      have h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime (piece hN) x'.asHomogeneousIdeal.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (Proj.stalkIso' (piece hN) x') (Proj.stalkIso' (piece hN) x').injective
    exact isReduced_of_isReduced_stalk _
  have hcl : closure ({gen hN hk hb h0} : Set (ProjectiveSpectrum (piece hN))) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure (piece hN) (gen hN hk hb h0) y).1 (by
      show (⊥ : HomogeneousIdeal (piece hN)) ≤ y.asHomogeneousIdeal
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum (piece hN)) := by
    refine (irreducibleSpace_def _).2 ?_
    rw [Set.top_eq_univ, ← hcl]
    exact (isIrreducible_singleton (x := gen hN hk hb h0)).closure
  have : IrreducibleSpace (Proj (piece hN)) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def toZero : R →+* piece hN 0 where
  toFun r := ⟨⟨C (c₀ r), by
      have : c₀ r * 1 ∈ N 0 := hN.smul 0 r 1 hN.one
      rw [mul_one] at this
      exact monomial_mem hN (k := 0) this⟩, by
    intro j hj; simp [coeff_C, hj]⟩
  map_one' := by ext1; ext1; simp
  map_mul' a b := by ext1; ext1; simp
  map_zero' := by ext1; ext1; simp
  map_add' a b := by ext1; ext1; simp

def Dp (k : ℕ) (b : F) : (Proj (piece hN)).Opens := by
  classical exact if hb : b ∈ N k then Proj.basicOpen (piece hN) (hel hN k b hb) else ⊥

theorem Dp_of_mem {k : ℕ} {b : F} (hb : b ∈ N k) : Dp hN k b = Proj.basicOpen (piece hN) (hel hN k b hb) := by
  rw [Dp, dif_pos hb]

def psi [IsIntegral (Proj (piece hN))] : (Proj (piece hN)).functionField →+* F :=
  (psiAt hN _).comp (Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))).toRingHom

theorem psi_algebraMap [IsIntegral (Proj (piece hN))] (x : Proj (piece hN)) (w : (Proj (piece hN)).presheaf.stalk x) :
    psi hN (algebraMap _ _ w) = psiAt hN _ (Proj.stalkIso' (piece hN) x w) := by
  obtain ⟨g, hg⟩ := mk_surjective (Proj.stalkIso' (piece hN) x w)
  have hw : w = (Proj.stalkIso' (piece hN) x).symm (mk g) :=
    ((Proj.stalkIso' (piece hN) x).symm_apply_apply w).symm.trans (congrArg _ hg.symm)
  subst hw
  have hsp : genericPoint (Proj (piece hN)) ⤳ x := genericPoint_specializes x
  have hle : (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal :=
    (ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ _).2 (specializes_iff_mem_closure.1 hsp)
  have key : Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))
      ((Proj (piece hN)).presheaf.stalkSpecializes hsp ((Proj.stalkIso' (piece hN) x).symm (mk g))) =
      mk (⟨g.deg, g.num, g.den, fun hy => g.den_mem (hle hy)⟩ :
        NumDenSameDeg (piece hN) (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl) := by
    erw [Proj.stalkIso'_symm_mk, TopCat.Presheaf.germ_stalkSpecializes_apply, Proj.stalkIso'_germ]
    rfl
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.stalkSpecializes hsp _)) = _
  rw [key, RingEquiv.apply_symm_apply, psiAt_mk, psiAt_mk]

end Scheme

end GlobalTheory.Desc.GrSpec
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GrSpec

open Polynomial HomogeneousLocalization

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)

theorem coe_hel_pow {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) :
    ((hel hN k b hb ^ n : ring hN) : F[X]) = monomial (k * n) (b ^ n) := by
  rw [SubmonoidClass.coe_pow, coe_hel, monomial_pow]

theorem hel_pow_mem {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : hel hN k b hb ^ n ∈ piece hN (k * n) := by
  have := SetLike.pow_mem_graded n (hel_mem hN k b hb)
  rwa [smul_eq_mul, mul_comm] at this

theorem isUnit_mk_iff (P : Ideal (ring hN)) [P.IsPrime] (g : NumDenSameDeg (piece hN) P.primeCompl) :
    IsUnit (mk g : AtPrime (piece hN) P) ↔ (g.num : ring hN) ∉ P := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem affine {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) : IsAffineOpen (Dp hN k b) := by
  rw [Dp_of_mem hN hb]
  exact Proj.isAffineOpen_basicOpen _ _ (hel_mem hN k b hb) (by omega)

theorem cover (z : Proj (piece hN)) : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp hN k b := by
  classical
  obtain ⟨y, hy, hyz⟩ := Set.not_subset.1 z.not_irrelevant_le
  have : ∃ j, (DirectSum.decompose (piece hN) y j : ring hN) ∉ z.asHomogeneousIdeal := by
    by_contra hc
    push_neg at hc
    apply hyz
    rw [← DirectSum.sum_support_decompose (piece hN) y]
    exact Ideal.sum_mem _ fun j _ => hc j
  obtain ⟨j, hj⟩ := this
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hj
    have : (DirectSum.decompose (piece hN) y 0 : ring hN) = 0 := by
      rw [← GradedRing.proj_apply]; exact (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hy
    rw [this]; exact zero_mem _
  set c := DirectSum.decompose (piece hN) y j
  have hb : ((c : ring hN) : F[X]).coeff j ∈ N j := (c : ring hN).2 j
  refine ⟨j, by omega, _, hb, ?_⟩
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen]
  have : hel hN j _ hb = (c : ring hN) := Subtype.ext ((mem_piece_iff hN).1 c.2).symm
  rw [this]; exact hj

theorem ideal_gen [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) :
    (genericPoint (Proj (piece hN))).asHomogeneousIdeal = ⊥ :=
  le_bot_iff.1 ((ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ (gen hN hk hb h0)).2
    (specializes_iff_mem_closure.1 (genericPoint_specializes (show Proj (piece hN) from gen hN hk hb h0))))

theorem genMem [IsIntegral (Proj (piece hN))] (h : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) {k : ℕ} {b : F} (hb : b ∈ N k) :
    genericPoint (Proj (piece hN)) ∈ Dp hN k b ↔ b ≠ 0 := by
  obtain ⟨k', hk', b', hb', h0'⟩ := h
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen, ideal_gen hN hk' hb' h0']
  change ¬ (hel hN k b hb = 0) ↔ _
  rw [not_iff_not, Subtype.ext_iff]
  simp

theorem hel_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k} (n : ℕ)
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : hel hN k b hb ^ n ∉ z.asHomogeneousIdeal.toIdeal :=
  fun h => hz (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)

theorem ne_zero_of_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k}
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : b ≠ 0 := by
  rintro rfl
  apply hz
  have : hel hN k 0 hb = 0 := Subtype.ext (by simp)
  rw [this]; exact zero_mem _

theorem mem [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (z : Proj (piece hN))
    (hz : z ∈ Dp hN k b) {l : ℕ} {a : F} (ha : a ∈ N l) :
    z ∈ Dp hN l a ↔ ∃ v, UnitAt z v ∧ psi hN v = a ^ k / b ^ l := by
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen] at hz
  rw [Dp_of_mem hN ha, Proj.mem_basicOpen]
  have hfz := hel_notMem hN l hz
  have hb0 := ne_zero_of_notMem hN hz
  constructor
  · intro hg
    let nd : NumDenSameDeg (piece hN) z.asHomogeneousIdeal.toIdeal.primeCompl :=
      ⟨l * k, ⟨_, hel_pow_mem hN ha k⟩, ⟨_, by rw [mul_comm]; exact hel_pow_mem hN hb l⟩, hfz⟩
    refine ⟨algebraMap ((Proj (piece hN)).presheaf.stalk z) _ ((Proj.stalkIso' (piece hN) z).symm (mk nd)), ⟨_, ?_, rfl⟩, ?_⟩
    · exact ((isUnit_mk_iff hN _ nd).2 (hel_notMem hN k hg)).map (Proj.stalkIso' (piece hN) z).symm
    · refine (psi_algebraMap hN z _).trans ?_
      erw [RingEquiv.apply_symm_apply]
      rw [psiAt_mk]
      simp only [nd, coe_hel_pow, coeff_monomial, if_pos (mul_comm k l), if_pos rfl, ↓reduceIte]
  · rintro ⟨v, ⟨w, hwu, rfl⟩, hv⟩ hg
    rw [psi_algebraMap] at hv
    obtain ⟨g, hg'⟩ := mk_surjective (Proj.stalkIso' (piece hN) z w)
    rw [← hg', psiAt_mk] at hv
    have hu : IsUnit (mk g : AtPrime (piece hN) z.asHomogeneousIdeal.toIdeal) := by
      rw [hg']; exact hwu.map (Proj.stalkIso' (piece hN) z)
    rw [isUnit_mk_iff] at hu
    have hnum := (mem_piece_iff hN).1 g.num.2
    have hden := (mem_piece_iff hN).1 g.den.2
    have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
      intro h0
      apply g.den_mem
      have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
      rw [this]; exact zero_mem _
    have key : (g.num : ring hN) * hel hN k b hb ^ l = hel hN l a ha ^ k * (g.den : ring hN) := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_mul, coe_hel_pow, coe_hel_pow, hnum, hden, monomial_mul_monomial,
        monomial_mul_monomial, show l * k + g.deg = g.deg + k * l by ring]
      congr 1
      rw [div_eq_div_iff hs (pow_ne_zero _ hb0)] at hv
      exact hv
    have : (g.num : ring hN) * hel hN k b hb ^ l ∈ z.asHomogeneousIdeal.toIdeal := by
      rw [key]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hg _ (by omega))
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h | h
    · exact hu h
    · exact hfz h

def fracAt {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F} (ha : a ∈ N (k * m)) (x : Proj (piece hN))
    (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) : NumDenSameDeg (piece hN) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨k * m, ⟨hel hN (k * m) a ha, hel_mem hN _ _ ha⟩, ⟨_, hel_pow_mem hN hb m⟩, hel_notMem hN m hx⟩

theorem psi_fracAt [IsIntegral (Proj (piece hN))] {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F}
    (ha : a ∈ N (k * m)) (x : Proj (piece hN)) (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) :
    psi hN (algebraMap ((Proj (piece hN)).presheaf.stalk x) _
      ((Proj.stalkIso' (piece hN) x).symm (mk (fracAt hN hb m ha x hx)))) = a / b ^ m := by
  refine (psi_algebraMap hN x _).trans ?_
  erw [RingEquiv.apply_symm_apply]
  rw [psiAt_mk]
  simp only [fracAt, coe_hel, coe_hel_pow, coeff_monomial, ↓reduceIte]

theorem ringChar [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (hb0 : b ≠ 0) (u : F) :
    (∃ v, (∀ z ∈ Dp hN k b, RegAt z v) ∧ psi hN v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m := by
  have h1 : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0 := ⟨k, hk, b, hb, hb0⟩
  have hgen : genericPoint (Proj (piece hN)) ∈ Dp hN k b := (genMem hN h1 hb).2 hb0
  rw [Dp_of_mem hN hb] at hgen ⊢
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, rfl⟩ := exists_fnOf_eq hgen hv
    obtain ⟨y, rfl⟩ : ∃ y, Proj.awayToSection (piece hN) (hel hN k b hb) y = s := by
      refine ⟨(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv s, ?_⟩
      rw [← Proj.basicOpenIsoAway_hom (piece hN) _ (hel_mem hN k b hb) (by omega)]
      exact (Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv_hom_id_apply s
    obtain ⟨nd, rfl⟩ := mk_surjective y
    obtain ⟨m, hm⟩ := nd.den_mem
    have hdeg : nd.deg = k * m := by
      have hne : (nd.den : ring hN) ≠ 0 := by
        rw [← hm]; exact pow_ne_zero _ (hel_ne_zero hN hb hb0)
      exact DirectSum.degree_eq_of_mem_mem (piece hN) nd.den.2 (hm ▸ hel_pow_mem hN hb m) hne
    refine ⟨m, ((nd.num : ring hN) : F[X]).coeff nd.deg, hdeg ▸ (nd.num : ring hN).2 nd.deg, ?_⟩
    change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hgen
      (Proj.awayToSection (piece hN) (hel hN k b hb) (mk nd)))) = _
    erw [Proj.stalkIso'_germ]
    have key : ∀ (h : Submonoid.powers (hel hN k b hb) ≤
        (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl),
        psiAt hN _ (HomogeneousLocalization.mapId (piece hN) h (mk nd)) =
          ((nd.num : ring hN) : F[X]).coeff nd.deg / ((nd.den : ring hN) : F[X]).coeff nd.deg := by
      intro h
      exact psiAt_mk hN _ ⟨nd.deg, nd.num, nd.den, h nd.den_mem⟩
    refine (key _).trans ?_
    rw [← hm, coe_hel_pow, coeff_monomial, if_pos hdeg.symm]
  · rintro ⟨m, a, ha, rfl⟩
    refine ⟨_, fun z hz => ⟨_, (psi hN).injective ((psi_fracAt hN hb m ha z hz).trans
      (psi_fracAt hN hb m ha _ hgen).symm)⟩, psi_fracAt hN hb m ha _ hgen⟩

def gR : CommRingCat.of R ⟶ Γ(Proj (piece hN), ⊤) :=
  CommRingCat.ofHom ((fromZeroRingHom (piece hN) _).comp (toZero hN)) ≫ Proj.awayToSection (piece hN) 1 ≫
    (Proj (piece hN)).presheaf.map (homOfLE (Proj.basicOpen_one (piece hN)).ge).op

def pstr : Proj (piece hN) ⟶ Sp R := (Proj (piece hN)).toSpecΓ ≫ Spec.map (gR hN)

theorem sep : IsSeparated (pstr hN) := inferInstance

theorem const [IsIntegral (Proj (piece hN))] : (psi hN).comp (cst (pstr hN)) = c₀ := by
  ext r
  have hg : genericPoint (Proj (piece hN)) ∈ Proj.basicOpen (piece hN) 1 := by
    rw [Proj.basicOpen_one]; trivial
  have e0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop = gR hN := by
    rw [pstr, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  change psi hN (fnOf ⊤ trivial (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop) r)) = c₀ r
  rw [e0]
  change psi hN (fnOf ⊤ trivial (resG (Proj (piece hN)) (Proj.basicOpen_one (piece hN)).ge
    (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = c₀ r
  rw [fnOf_resG (Proj.basicOpen_one (piece hN)).ge trivial]
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hg
      (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = _
  erw [Proj.stalkIso'_germ]
  refine (psiAt_mk hN _ ⟨0, toZero hN r, 1, fun h => ?_⟩).trans ?_
  · exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)
  · simp [toZero]

end GlobalTheory.Desc.GrSpec

namespace GlobalTheory.Desc

theorem exists_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F),
    GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R)
      (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  intro R F _ _ _ c₀ N hN h
  obtain ⟨k₀, hk₀, b₀, hb₀, h₀⟩ := h
  haveI := GrSpec.isIntegral hN hk₀ hb₀ h₀
  refine ⟨Proj (GrSpec.piece hN), inferInstance, GrSpec.pstr hN, GrSpec.psi hN, GrSpec.Dp hN, ?_⟩
  exact
    { sep := GrSpec.sep hN
      const := GrSpec.const hN
      affine := fun k hk b hb => GrSpec.affine hN hk hb
      cover := GrSpec.cover hN
      gen := fun k _ b hb => GrSpec.genMem hN ⟨k₀, hk₀, b₀, hb₀, h₀⟩ hb
      ring := fun k hk b hb hb0 u => GrSpec.ringChar hN hk hb hb0 u
      mem := fun k hk b hb z hz l _ a ha => GrSpec.mem hN hk hb z hz ha }

end GlobalTheory.Desc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  atlas_forward_decl GlobalTheory.Desc.exists_model
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.EmbeddingLemmas

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]; rfl

theorem cst_comp {X : Scheme.{0}} [IsIntegral X] {R R' : Type} [CommRing R] [CommRing R'] (q : X ⟶ Sp R') (ρ : R →+* R') :
    Desc.cst (q ≫ spMap ρ) = (Desc.cst q).comp ρ := by
  have e : spMap (Desc.cst (q ≫ spMap ρ)) = spMap ((Desc.cst q).comp ρ) := by
    rw [spMap_comp', spMap_cst, spMap_cst, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem cst_inj {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] [IsDomain R] (p : X ⟶ Sp R) [Flat p] :
    Function.Injective (Desc.cst p) := by
  have h1 : Flat (gp X) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X _
  have h2 : Flat (spMap (Desc.cst p)) := by rw [spMap_cst]; infer_instance
  have h3 : (Desc.cst p).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  algebraize [Desc.cst p]
  exact FaithfulSMul.algebraMap_injective R X.functionField

theorem baseIndexConstant_injective (σ : Setup) : Function.Injective σ.c₀ := by
  haveI := σ.ab.smooth
  exact cst_inj _

theorem abelianSchemeDescent_chart_baseConstants_comp (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc,
      (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem linDisj_A (σ : Setup) : LinDisj σ.c₀ (Desc.cst σ.A.hom) (RingHom.id _) := by
  haveI := σ.ab.proper
  have hfl : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  refine (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ _ hfl σ.A.left σ.A.left σ.A.left (σ.A.hom ≫ awayMap σ.f) σ.A.hom (𝟙 _) (𝟙 _)
    (RingHom.id _) inferInstance inferInstance ?_ ⟨gp _, by simp, ?_⟩ σ.D σ.D ?_).1
  · rw [Category.id_comp]
    exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  · have : spMap (RingHom.id σ.A.left.functionField) = 𝟙 _ := Spec.map_id _
    rw [this]; simp
  · intro v g h
    exact h

theorem linDisj_C (σ : Setup) (x : Sp σ.R) : LinDisj σ.c₀ (Desc.cst (σ.C x).G.hom) (σ.θ x) := by
  haveI := σ.ab.proper
  exact (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ _ (σ.flat x) σ.A.left (σ.C x).G.left (σ.V x).toScheme (σ.A.hom ≫ awayMap σ.f) (σ.C x).G.hom
    (σ.V x).ι (σ.φ x) (σ.θ x) inferInstance inferInstance (σ.cart x) (σ.hθ x) σ.D (σ.D₁ x) (σ.pull x)).1

theorem compact_A (σ : Setup) : CompactSpace σ.A.left := by
  haveI := σ.ab.proper
  exact QuasiCompact.compactSpace_of_compactSpace σ.A.hom

theorem qsep_A (σ : Setup) : QuasiSeparatedSpace σ.A.left := by
  haveI := σ.ab.proper
  exact quasiSeparatedSpace_of_quasiSeparated σ.A.hom

theorem compact_C (σ : Setup) (x : Sp σ.R) : CompactSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom

theorem qsep_C (σ : Setup) (x : Sp σ.R) : QuasiSeparatedSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.separated
  exact quasiSeparatedSpace_of_quasiSeparated (σ.C x).G.hom

theorem cartA_of_openIn (σ : Setup) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (i : σ.A.left ⟶ P) (h : OpenIn i σ.A.hom p (awayMap σ.f)) : IsPullback i σ.A.hom p (awayMap σ.f) := by
  obtain ⟨w, ho⟩ := h
  haveI := σ.ab.proper
  set g := pullback.lift i σ.A.hom w with hg
  have hsnd : g ≫ pullback.snd p (awayMap σ.f) = σ.A.hom := pullback.lift_snd _ _ _
  haveI : IsProper (g ≫ pullback.snd p (awayMap σ.f)) := by rw [hsnd]; infer_instance
  haveI : IsProper g := IsProper.of_comp g (pullback.snd p (awayMap σ.f))
  haveI : Nonempty (pullback p (awayMap σ.f) : Scheme.{0}) := ⟨g (genericPoint σ.A.left)⟩
  haveI : IsIntegral (pullback p (awayMap σ.f)) := isIntegral_of_isOpenImmersion (pullback.fst p (awayMap σ.f))
  have hclo : IsClopen (Set.range g) := ⟨g.isClosedMap.isClosed_range, g.isOpenEmbedding.isOpen_range⟩
  have hs : Surjective g := ⟨Set.range_eq_univ.1 (hclo.eq_univ (Set.range_nonempty _))⟩
  haveI : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).2 ⟨ho, hs⟩
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso g) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem onV_of (σ : Setup) (x : Sp σ.R) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (ψ : P.functionField →+* σ.A.left.functionField) (i : σ.A.left ⟶ P) (hi : i ≫ p = σ.A.hom ≫ awayMap σ.f)
    (hfA : PFF (𝟙 _) i ψ) (e : (σ.C x).G.left ⟶ P) (he : e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x))
    (hf : PFF (𝟙 _) e ((σ.θ x).comp ψ)) : σ.φ x ≫ i = (σ.V x).ι ≫ e := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  obtain ⟨a, ha, ha'⟩ := hfA
  obtain ⟨b, hb, hb'⟩ := hf
  rw [Category.comp_id] at ha hb
  subst ha hb
  haveI : IsDominant (l ≫ (σ.V x).ι) := by
    rw [hl]
    refine ⟨?_⟩
    have hm : genericPoint (σ.C x).G.left ∈ Set.range (gp (σ.C x).G.left) :=
      ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense {genericPoint (σ.C x).G.left} := by
      rw [dense_iff_closure_eq]; exact (genericPoint_spec _).def.trans rfl
    exact hd.mono (Set.singleton_subset_iff.2 hm)
  haveI : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l (σ.V x).ι
  refine ext_of_isDominant_of_isSeparated p ?_ l ?_
  · rw [Category.assoc, Category.assoc, hi, he, (σ.cart x).w, Category.assoc]
  · rw [← Category.assoc, hl', ← Category.assoc, hl, hb', Category.assoc, ha', spMap_comp', Category.assoc]

end GlobalTheory.Desc.EmbeddingLemmas

namespace GlobalTheory.Desc

open GlobalTheory.Desc.EmbeddingLemmas in

theorem nonempty_emb : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  intro σ _
  obtain ⟨hG, k₀, hk₀, b₀, hb₀, hb₀0⟩ := GlobalTheory.T.abelianSchemeDescent_gradedFamily_nonzero σ
  obtain ⟨P, hPi, p, ψ, Dp, hM⟩ := GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions σ.R _ σ.c₀ σ.N hG ⟨k₀, hk₀, b₀, hb₀, hb₀0⟩
  have hinj := baseIndexConstant_injective σ

  haveI : IsDomain (Localization.Away σ.f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf)
  have hcA : (RingHom.id _).comp σ.c₀ = (cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    rw [RingHom.id_comp]; exact cst_comp σ.A.hom _
  have hspA : ∀ k, Sec σ.D k = spanBy (cst σ.A.hom) ((RingHom.id _) '' σ.N k) := by
    intro k; rw [RingHom.coe_id, Set.image_id]; exact GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice σ k
  have hsecA : ∀ k, ∀ a ∈ σ.N k, (RingHom.id _) a ∈ Sec σ.D k := fun k a ha => ha.1
  have hcovA := GlobalTheory.T.exists_cartierSectionLocus_of_ample_span _ _ σ.A.left σ.A.hom (RingHom.id _) σ.N σ.D σ.amp hspA
  obtain ⟨m, hm, hmf, hml⟩ := GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) σ.A.left σ.A.hom (RingHom.id _) σ.D hcA hsecA hcovA
  haveI := compact_A σ
  haveI := qsep_A σ
  have hflA : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  have hoA := GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) hflA hinj σ.A.left σ.A.hom (RingHom.id _) σ.D hcA (linDisj_A σ) σ.amp hspA
    m hm hmf hml
  have hcart := cartA_of_openIn σ P p hM.sep m hoA

  have hC : ∀ x, ∃ e : (σ.C x).G.left ⟶ P, e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x) ∧ PFF (𝟙 _) e ((σ.θ x).comp ψ) ∧
      OpenIn e (σ.C x).G.hom p (spMap (σ.ρ x)) := by
    intro x
    have hsp := GlobalTheory.T.cartierMultipleGlobalSections_chart_eq_span σ x
    have hsec : ∀ k, ∀ a ∈ σ.N k, σ.θ x a ∈ Sec (σ.D₁ x) k := fun k a ha => by
      rw [hsp k]; exact subset_spanBy _ _ (Set.mem_image_of_mem _ ha)
    have hcov := GlobalTheory.T.exists_cartierSectionLocus_of_ample_span _ _ (σ.C x).G.left (σ.C x).G.hom (σ.θ x) σ.N (σ.D₁ x) (σ.amp₁ x) hsp
    obtain ⟨e, he, hef, hel⟩ := GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) hsec hcov
    haveI := compact_C σ x
    haveI := qsep_C σ x
    exact ⟨e, he, hef, GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.flat x) hinj (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) (linDisj_C σ x) (σ.amp₁ x) hsp e he hef hel⟩
  choose e he hef heo using hC
  have hm' : m ≫ p = σ.A.hom ≫ awayMap σ.f := hm
  have hmf' : PFF (𝟙 _) m ψ := by simpa using hmf
  exact ⟨{
    P := P
    p := p
    sep := hM.sep
    ψ := ψ
    ιA := m
    cartA := hcart
    ffA := hmf'
    emb := e
    openIn := heo
    ff := hef
    onV := fun x => onV_of σ x P p hM.sep ψ m hm' hmf' (e x) (he x) (hef x) }⟩

end GlobalTheory.Desc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_descentSeparatedEmbedding : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  atlas_forward_decl GlobalTheory.Desc.nonempty_emb
end
