import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuative_extension_point : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), ∃ yt : Sp e.O ⟶ M.X, spMap e.O.subtype ≫ yt = y.1 ≫ M.j ∧ ∀ U : M.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U → ⊤ ≤ yt ⁻¹ᵁ U ∧ y.1 (IsLocalRing.closedPoint _) ∈ M.j ⁻¹ᵁ U := by
  first | exact @GlobalTheory.TrueGeo.exists_valuationRing_point | exact GlobalTheory.TrueGeo.exists_valuationRing_point | (intros; apply GlobalTheory.TrueGeo.exists_valuationRing_point <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

namespace GlobalTheory.SmallInduced

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h]
  congr 1
  exact IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    TrueGeo.valAt y (f * g) = TrueGeo.valAt y f * TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_ne_zero {f : Z.functionField} (hf : UnitAt (below y) f) : TrueGeo.valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

omit [IsIntegral Z] in

theorem top_le_of_below {U : Z.Opens} (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    TrueGeo.valAt y (fnOf U h a) = valR y U a := by
  rw [← algebraMap_germ hy, valAt_algebraMap, valR, dif_pos (top_le_of_below y hy)]
  have := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  exact this

end Val

theorem valR_spMap_comp {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) {X : Scheme.{0}}
    (x : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valR (spMap φ ≫ x) U a = φ (valR x U a) := by
  rw [← valR_appLE (spMap φ) x h le_top, valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from le_top), valR, dif_pos h]
  have := congrArg (fun ψ => ψ.hom ((x.appLE U ⊤ h).hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  refine Eq.trans ?_ this
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (ψ.hom ((x.appLE U ⊤ h).hom a)))
    (Scheme.Hom.appLE_eq_app (spMap φ) (U := ⊤))


end GlobalTheory.SmallInduced
end

section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem Ext.w_le_one_of_isIntegral {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    {x : AlgebraicClosure F} (hx : IsIntegral ℤ x) : e.w x ≤ 1 := by
  rw [← e.mem_O]
  have h : IsIntegral e.O x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := e.O) (K := AlgebraicClosure F)).1 h
  rw [← hy]
  exact y.2

theorem finite_ext_one_lt (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, 1 < e.w a}.Finite := by
  have hQ : IsAlgebraic ℚ a :=
    (Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)).isAlgebraic a
  have hZ : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 hQ
  obtain ⟨d, hd, hi⟩ := hZ.exists_integral_multiple
  have hd' : (Ideal.span {(d : 𝓞 F)}) ≠ 0 := by
    simpa using hd
  refine (Ideal.finite_factors hd').subset ?_
  rintro v ⟨e, he⟩
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hv
  have h1 : NumberField.HeightOneSpectrum.adicAbv F v ((d : 𝓞 F) : F) = 1 :=
    (v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv
  have h2 := e.w_le_one_of_isIntegral hi
  have h3 : e.w (d : AlgebraicClosure F) = 1 := by
    rw [← h1, ← e.w_alg]
    simp
  rw [zsmul_eq_mul, map_mul, h3, one_mul] at h2
  exact absurd he (not_lt.2 h2)

theorem finite_ext_ne_one (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) (ha : a ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, e.w a ≠ 1}.Finite := by
  refine ((finite_ext_one_lt F a).union (finite_ext_one_lt F a⁻¹)).subset ?_
  rintro v ⟨e, he⟩
  rcases lt_or_gt_of_ne he with h | h
  · refine Or.inr ⟨e, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ (e.w.pos ha)).2 h
  · exact Or.inl ⟨e, h⟩

end GlobalTheory.TrueGeo
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem finite_places_lg_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ y : AlgPt Y, {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, A.lg v e y ≠ 0}.Finite := by
  intro F _ _ C Y A M L k cf hI y
  obtain ⟨hcf, r, -, -, hfin⟩ := hI
  have := M.ar.isNoetherian
  have hcov : (Set.univ : Set M.X) ⊆ ⋃ i, (L.B.U i : Set M.X) := by
    intro x _
    have hx : x ∈ (⨆ i, L.B.U i : M.X.Opens) := by rw [L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.B.U i : Set M.X))
    (fun i => (L.B.U i).isOpen) hcov
  let a : L.B.ι → AlgebraicClosure F := fun i =>
    valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r (fun _ => i) : Y.Fnˣ) : Y.Fn)
  have hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | a i ≠ 0 ∧ ∃ e : Ext v, e.w (a i) ≠ 1}.Finite := by
    intro i
    by_cases h : a i = 0
    · simp [h]
    · exact (GlobalTheory.TrueGeo.finite_ext_ne_one F (a i) h).subset fun v hv => hv.2
  refine (hcf.union (S.finite_toSet.biUnion fun i _ => hB i)).subset ?_
  rintro v ⟨e, he⟩
  obtain ⟨yt, hyt, hU⟩ := GlobalTheory.TrueGeo.exists_valuationRing_point F Y M v e y
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h := hfin v e y yt (fun _ => i) hyt (hU _ hi).1
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h1' : cf v = 0 := by simpa using h1
  have hlog : Real.log (e.w (a i)) = 0 := by
    by_cases h0 : a i = 0
    · simp [h0]
    · have : e.w (a i) = 1 := by
        by_contra hne
        exact h2 (Set.mem_iUnion₂.mpr ⟨i, hiS, h0, e, hne⟩)
      simp [this]
  have h3 : ((k : ℕ) : ℝ) * A.lg v e y = 0 := by
    rw [h, h1', mul_zero, sub_zero]
    exact hlog
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  exact he ((mul_eq_zero.mp h3).resolve_left hk)

end GlobalTheory.TrueGeo
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

theorem valAt_eq_of_residueField_hom {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (x : Z)
    (σ : Z.residueField x ⟶ CommRingCat.of K) (hy : Spec.map σ ≫ Z.fromSpecResidueField x = y)
    (a : Z.presheaf.stalk x) :
    valAt y (algebraMap _ Z.functionField a) = σ.hom ((Z.residue x).hom a) := by
  have hx : below y = x := by
    rw [← hy]
    exact Scheme.fromSpecResidueField_apply x _
  subst hx
  have hσ : σ = Z.descResidueField (Scheme.stalkClosedPointTo y) := by
    rw [← Spec.map_inj, ← cancel_mono (Z.fromSpecResidueField _), hy]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z y).symm
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  have e : h.choose = a := IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec
  rw [valAt, dif_pos h, e, hσ]
  rfl

theorem exists_finprod_valAt_eq (F : Type) [Field F] [NumberField F] (Y : Var F) (x : Y.X)
    (hx : IsClosed ({x} : Set Y.X)) (f : Y.Fn) (hf : UnitAt x f) :
    ∃ N : F, N ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : F →+* K),
      {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x}.Finite ∧
      ∏ᶠ (y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ}) (_ : below y.1 = x), valAt y.1 f = φ N := by
  obtain ⟨a, ha, rfl⟩ := hf
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.X.fromSpecResidueField x ≫ Y.str)
  have hfin : IsFinite (Spec.map ψ) := by
    rw [hψ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (Y.X.residueField x) := ψ.hom.toAlgebra
  haveI : Module.Finite F (Y.X.residueField x) := (IsFinite.SpecMap_iff ψ).1 hfin
  have hα : (Y.X.residue x).hom a ≠ 0 := (ha.map _).ne_zero
  refine ⟨Algebra.norm F ((Y.X.residue x).hom a), Algebra.norm_ne_zero_iff.2 hα, fun K _ _ φ => ?_⟩
  letI : Algebra F K := φ.toAlgebra
  let g : (Y.X.residueField x →ₐ[F] K) → {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} := fun σ =>
    ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Y.X.fromSpecResidueField x, by
      rw [Category.assoc, ← hψ, ← Spec.map_comp]
      congr 1
      ext c
      exact σ.commutes c⟩
  have hinj : Function.Injective g := fun σ τ h => by
    have h1 := congrArg Subtype.val h
    simp only [g, cancel_mono, Spec.map_inj] at h1
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)
  have hr : {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x} = Set.range g := by
    ext ⟨y, hy⟩
    constructor
    · intro h
      change below y = x at h
      have h2 : Spec.map ((Y.X.residueFieldCongr h.symm).hom ≫
          Y.X.descResidueField (Scheme.stalkClosedPointTo y)) ≫ Y.X.fromSpecResidueField x = y := by
        rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
        exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y.X y
      generalize (Y.X.residueFieldCongr h.symm).hom ≫
          Y.X.descResidueField (Scheme.stalkClosedPointTo y) = s at h2
      have h3 : ψ ≫ s = CommRingCat.ofHom φ := by
        rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, h2, hy]
      exact ⟨⟨s.hom, fun c => congrArg (fun t => t.hom c) h3⟩, Subtype.ext h2⟩
    · rintro ⟨σ, hσ⟩
      rw [← hσ]
      exact Scheme.fromSpecResidueField_apply x _
  refine ⟨hr ▸ Set.finite_range g, ?_⟩
  have key := finprod_mem_range (f := fun y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} =>
    valAt y.1 (algebraMap _ Y.X.functionField a)) hinj
  rw [← hr] at key
  refine Eq.trans key ?_
  rw [finprod_eq_prod_of_fintype]
  refine Eq.trans ?_ (Algebra.norm_eq_prod_embeddings F K ((Y.X.residue x).hom a)).symm
  exact Finset.prod_congr rfl fun σ _ => valAt_eq_of_residueField_hom _ x _ rfl a

end GlobalTheory.TrueGeo
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjOrigin

open ProjSpace

theorem chartι_mem_chart_iff (R : Type) [CommRing R] (N : ℕ) (i : Fin (N + 1)) (j : {j // j ≠ i})
    (p : Sp (MvPolynomial {j // j ≠ i} R)) :
    chartι R N i p ∈ chart R N j.1 ↔ (X j : MvPolynomial {j // j ≠ i} R) ∉ p.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen (grading R N) (X_mem R N i) one_pos (X_mem R N j.1) one_pos
  have e : awayToPoly R N i (HomogeneousLocalization.Away.isLocalizationElem (X_mem R N i) (X_mem R N j.1))
      = X j := by
    refine (awayToPoly_mk R N i _ _ _).trans ?_
    rw [pow_one, dehom_X_of_ne]
  rw [← e]
  exact (congrArg (spMap (awayToPoly R N i) p ∈ ·) h).to_iff

def origin {R K : Type} [CommRing R] [Field K] (N : ℕ) (φ : R →+* K) : Sp K ⟶ PSpace R N :=
  spMap (eval₂Hom φ fun _ : {j : Fin (N + 1) // j ≠ 0} => 0) ≫ chartι R N 0

end GlobalTheory.ProjOrigin
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ProjTest

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z]

theorem valAt_algebraMap (y : Sp K ⟶ Z) (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h, IsFractionRing.injective _ _ h.choose_spec]

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ)
    {f : Z.functionField} (hf : RegAt (under y) f) : ratVal f y = valAt y.1 f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have h := CxPts.mem_ptsIn.2 hU
  rw [ratVal_fnOf h, ← algebraMap_germ hU, valAt_algebraMap, CxPts.ev, valR,
    dif_pos (show ⊤ ≤ y.1 ⁻¹ᵁ U from h)]
  have e := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U hU)
  refine Eq.trans ?_ e.symm
  simp [Scheme.Hom.appLE]
  rfl

end Val

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

omit [NumberField F] in

theorem isEqn_eqn (Δ : Y.Dv) (x : Y.X) : Δ.IsEqn x (eqn Δ x) := (Δ.exists_isEqn x).choose_spec

variable (F) (n : ℕ)

def pick (i : Fin n) (l : Fin (n + 1)) : 𝓞 F := if l = i.succ then 1 else 0

end GlobalTheory.TrueGeo.ProjTest

namespace GlobalTheory.TrueGeo

end GlobalTheory.TrueGeo
end
end
