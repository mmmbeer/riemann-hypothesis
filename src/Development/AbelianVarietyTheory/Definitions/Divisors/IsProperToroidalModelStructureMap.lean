import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.TrFormBaseChangeNondegenerate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj

namespace GlobalTheory.Toroidal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Forms

variable (H : Host E) (N : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]

def levelForms : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | (∀ y z, β y z = β z y) ∧ (∀ (a : 𝓞 E) y z, β (a • y) z = β y (H.bar a • z)) ∧ ∀ y z, (N : ℤ) ∣ β y z}
  add_mem' := by
    rintro β γ ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun y z => ?_, fun a y z => ?_, fun y z => ?_⟩
    · simp only [LinearMap.add_apply, h1 y z, k1 y z]
    · simp only [LinearMap.add_apply, h2 a y z, k2 a y z]
    · exact dvd_add (h3 y z) (k3 y z)
  zero_mem' := by simp
  smul_mem' := by
    rintro n β ⟨h1, h2, h3⟩
    refine ⟨fun y z => ?_, fun a y z => ?_, fun y z => ?_⟩
    · simp only [LinearMap.smul_apply, h1 y z]
    · simp only [LinearMap.smul_apply, h2 a y z]
    · exact Dvd.dvd.mul_left (h3 y z) n

variable {H N X}

theorem mem_levelForms {β : LinearMap.BilinForm ℤ X} : β ∈ levelForms H N X ↔
    (∀ y z, β y z = β z y) ∧ (∀ (a : 𝓞 E) y z, β (a • y) z = β y (H.bar a • z)) ∧ ∀ y z, (N : ℤ) ∣ β y z := Iff.rfl

theorem mem_levelForms_iff_smul (hN : N ≠ 0) {β : LinearMap.BilinForm ℤ X} :
    β ∈ levelForms H N X ↔ ∃ γ ∈ levelForms H 1 X, β = (N : ℤ) • γ := by
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose g hg using h3
    have inj : ∀ {a b : ℤ}, (N : ℤ) * a = N * b → a = b := fun h => mul_left_cancel₀ hN' h
    let γ : LinearMap.BilinForm ℤ X := LinearMap.mk₂ ℤ g
      (fun a b c => inj (by rw [mul_add, ← hg, ← hg, ← hg, map_add, LinearMap.add_apply]))
      (fun n a b => inj (by rw [smul_eq_mul, mul_left_comm, ← hg, ← hg, map_smul, LinearMap.smul_apply, smul_eq_mul]))
      (fun a b c => inj (by rw [mul_add, ← hg, ← hg, ← hg, map_add]))
      (fun n a b => inj (by rw [smul_eq_mul, mul_left_comm, ← hg, ← hg, map_smul, smul_eq_mul]))
    refine ⟨γ, ⟨fun y z => inj ?_, fun a y z => inj ?_, fun y z => by simp⟩, ?_⟩
    · exact (hg y z).symm.trans ((h1 y z).trans (hg z y))
    · exact (hg _ z).symm.trans ((h2 a y z).trans (hg y _))
    · ext y z
      exact hg y z
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2, -⟩ := (levelForms H 1 X).smul_mem (N : ℤ) hγ
    exact ⟨h1, h2, fun y z => Dvd.intro _ rfl⟩

theorem apply_self_eq_two_mul {β : LinearMap.BilinForm ℤ X} (h : β ∈ levelForms H N X) (y : X) :
    β y y = 2 * β y (H.w0 • y) := by
  have e : β y (H.bar H.w0 • y) = β y (H.w0 • y) := (h.2.1 _ _ _).symm.trans (h.1 _ _)
  rw [HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub] at e
  linarith

variable (H N X) in

def toSymB : levelForms H N X →ₗ[ℤ] Formalism.MainNotions.ModuliIntegralCharts.SymB (fun x : E => IsCMField.complexConj E x) X where
  toFun β := ⟨(β : LinearMap.BilinForm ℤ X).compr₂ (Algebra.linearMap ℤ ℝ), fun a b => by
      simp only [LinearMap.compr₂_apply, β.2.1 a b], fun c c' h a b => by
      have : c' = H.bar c := RingOfIntegers.ext (h.trans (H.bar_eq c).symm)
      simp only [LinearMap.compr₂_apply, this, β.2.2.1 c a b]⟩
  map_add' β γ := by ext a b; simp
  map_smul' n β := by ext a b; simp

@[simp] theorem toSymB_apply (β : levelForms H N X) (a b : X) :
    (toSymB H N X β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = ((β : LinearMap.BilinForm ℤ X) a b : ℝ) := by
  simp [toSymB]




end Forms

section Part

variable {L : Type} [AddCommGroup L] {m : ℕ}

def IsPartOfBasis (v : Fin m → L) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin m ⊕ Fin n) ℤ L), ∀ i, b (Sum.inl i) = v i

theorem IsPartOfBasis.linearIndependent {v : Fin m → L} (h : IsPartOfBasis v) : LinearIndependent ℤ v := by
  obtain ⟨n, b, hb⟩ := h
  have := b.linearIndependent.comp Sum.inl Sum.inl_injective
  rwa [show b ∘ Sum.inl = v from funext hb] at this

theorem IsPartOfBasis.isUnit_of_smul {v : Fin m → L} (h : IsPartOfBasis v) {i : Fin m} {k : ℤ} {w : L}
    (hw : k • w = v i) : IsUnit k := by
  obtain ⟨n, b, hb⟩ := h
  have := congrArg (fun x => b.repr x (Sum.inl i)) (hw.trans (hb i).symm)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_eq_same] at this
  exact IsUnit.of_mul_eq_one _ this

theorem IsPartOfBasis.exists_dual {v : Fin m → L} (h : IsPartOfBasis v) :
    ∃ φ : Fin m → (L →ₗ[ℤ] ℤ), ∀ i j, φ i (v j) = if i = j then 1 else 0 := by
  obtain ⟨n, b, hb⟩ := h
  refine ⟨fun i => b.coord (Sum.inl i), fun i j => ?_⟩
  rw [← hb j, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]


example (w : L) : ¬ IsPartOfBasis ![(2 : ℤ) • w] := fun h => by
  have := h.isUnit_of_smul (i := 0) (k := 2) (w := w) rfl
  rcases Int.isUnit_iff.1 this with h | h <;> omega

example : IsPartOfBasis ![(Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin 1 → ℤ)] :=
  ⟨1, Pi.basisFun ℤ _, fun i => by fin_cases i; simp⟩

end Part

section Monomial

variable {R : Type} [CommRing R] [IsDomain R] {m : ℕ}

def IsMonomial (Dg : DegPre R) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Dg.X) : Prop :=
  ∀ y, ∃ (u : Rˣ) (n : Fin m → ℕ), (∀ i, β i y y = 2 * n i) ∧ PsiCoord Dg y (u * ∏ i, t i ^ n i)

variable {Dg : DegPre R} {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ Dg.X}

theorem IsMonomial.nonneg (h : IsMonomial Dg t β) (i : Fin m) (y : Dg.X) : 0 ≤ β i y y := by
  obtain ⟨u, n, hn, -⟩ := h y
  rw [hn]; positivity

theorem IsMonomial.coord (h : IsMonomial Dg t β) {y : Dg.X} {r : R} (hr : PsiCoord Dg y r) :
    ∃ (u : Rˣ) (n : Fin m → ℕ), (∀ i, β i y y = 2 * n i) ∧ r = u * ∏ i, t i ^ n i := by
  obtain ⟨u, n, hn, hc⟩ := h y
  obtain ⟨v, hv⟩ := PsiCoordLocal.exists_unit_of_coord hc hr
  exact ⟨v * u, n, hn, by rw [hv, Units.val_mul, mul_assoc]⟩

theorem IsMonomial.exists_pos {I : Ideal R} (hI : I ≠ ⊤) {Dd : DegData R I}
    {β : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X} (h : IsMonomial Dd.toPre t β) {y : Dd.toPre.X} (hy : y ≠ 0) :
    ∃ i, 0 < β i y y := by
  obtain ⟨u, n, hn, hc⟩ := h y
  have hm := (PeriodFormEdge.psiIn_iff hc I).1 (Dd.psi_pos y hy)
  by_contra hne
  have h0 : ∀ i, n i = 0 := fun i => by
    have := not_exists.1 hne i
    rw [hn] at this
    omega
  simp only [h0, pow_zero, Finset.prod_const_one, mul_one] at hm
  exact hI (Ideal.eq_top_of_isUnit_mem _ hm u.isUnit)

theorem IsMonomial.tau (h : IsMonomial Dg t β) (hs : ∀ i y z, β i y z = β i z y) (ht : ∀ i, t i ≠ 0) {a b : Dg.X}
    {r r' r'' : R} (ha : PsiCoord Dg a r) (hb : PsiCoord Dg b r') (hab : PsiCoord Dg (a + b) r'') :
    ∃ u : Rˣ, algebraMap R (FractionRing R) r'' / (algebraMap R _ r * algebraMap R _ r') =
      algebraMap R _ u * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b := by
  obtain ⟨u, n, hn, rfl⟩ := h.coord ha
  obtain ⟨u', n', hn', rfl⟩ := h.coord hb
  obtain ⟨u'', n'', hn'', rfl⟩ := h.coord hab
  have ne : ∀ {x : R}, x ≠ 0 → algebraMap R (FractionRing R) x ≠ 0 := fun hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hx
  have e : ∀ i, (n'' i : ℤ) = β i a b + n i + n' i := fun i => by
    have := hn'' i
    simp only [map_add, LinearMap.add_apply, hs i b a, hn i, hn' i] at this
    omega
  refine ⟨u'' * u⁻¹ * u'⁻¹, ?_⟩
  have hu := ne u.ne_zero
  have hu' := ne u'.ne_zero
  have hp : ∀ k : Fin m → ℕ, ∏ i, algebraMap R (FractionRing R) (t i) ^ k i ≠ 0 := fun k =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ne (ht i))
  have e' : ∏ i, algebraMap R (FractionRing R) (t i) ^ n'' i = (∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) *
      (∏ i, algebraMap R (FractionRing R) (t i) ^ n i) * ∏ i, algebraMap R (FractionRing R) (t i) ^ n' i := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, e, zpow_add₀ (ne (ht i)), zpow_add₀ (ne (ht i)), zpow_natCast, zpow_natCast]
  simp only [map_mul, map_prod, map_pow, Units.val_mul, map_units_inv, e']
  have := hp n
  have := hp n'
  field_simp


theorem psiUnitOn_of_coord {y : Dg.X} {r : R} (hr : PsiCoord Dg y r) {U : Set (Sp R)}
    (hU : ∀ p ∈ U, r ∉ p.asIdeal) : PsiUnitOn Dg y U := by
  intro j' V hV hVU hj' h'
  obtain ⟨j, hj, h, e⟩ := hr
  have h₂ : V ≤ (Dg.c y).left ⁻¹ᵁ Dg.P.L.U (j PUnit.unit) := le_top.trans hj
  have k : ((jK R).app V).hom (DegPre.toOpen (R := R) V r) =
      ((TK R).left.presheaf.map (homOfLE (PsiCoordLocal.generic_le Dg y j h₂)).op).hom ((Dg.psi y).s j).val := by
    have := congrArg ((TK R).left.presheaf.map (homOfLE ((jK R).preimage_mono (le_top : V ≤ ⊤))).op).hom e
    rw [Cartier.resG_resG] at this
    rw [← this]
    refine Eq.trans ?_ (Cartier.app_resG (jK R) (le_top : V ≤ ⊤) _)
    exact congrArg _ (Cartier.resG_resG (X := Sp R) (le_top : (⊤ : (Sp R).Opens) ≤ ⊤) (le_top : V ≤ ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)).symm
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_trans Dg y j' j hj' h₂ h' (PsiCoordLocal.generic_le Dg y j h₂)
  refine ⟨u * DegPre.toOpen (R := R) V r, u.isUnit.mul ?_, ?_⟩
  · refine (Sp R).toRingedSpace.isUnit_of_isUnit_germ V _ fun x hx => ?_
    refine ((Sp R).mem_basicOpen _ x hx).1 ?_
    have c : (Sp R).basicOpen (DegPre.toOpen (R := R) V r) =
        V ⊓ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := (Sp R).basicOpen_res _ _
    rw [c, basicOpen_eq_of_affine]
    exact ⟨hx, hU x (hVU hx)⟩
  · rw [map_mul, k]
    exact (congrArg Units.val hu).symm

theorem IsMonomial.psiUnitOn (h : IsMonomial Dg t β) (y : Dg.X) {U : Set (Sp R)}
    (hU : ∀ p ∈ U, ∏ i, t i ∉ p.asIdeal) : PsiUnitOn Dg y U := by
  obtain ⟨u, n, -, hc⟩ := h y
  refine psiUnitOn_of_coord hc fun p hp hm => hU p hp ?_
  have hpr := p.isPrime
  rcases hpr.mem_or_mem hm with hm | hm
  · exact absurd (Ideal.eq_top_of_isUnit_mem _ hm u.isUnit) hpr.ne_top
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff).1 hm
    exact (Ideal.IsPrime.prod_mem_iff).2 ⟨i, Finset.mem_univ _, hpr.mem_of_pow_mem _ hi⟩



end Monomial

section Charts

def IsEtaleCompletion {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R) : Prop :=
  φ.Flat ∧ (maximalIdeal A).map φ = maximalIdeal R ∧ ((residue R).comp φ).Finite


variable {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F}

abbrev gen (Y : Model Xo c β) : Scheme.{0} := pullback Y.s (spMap β)

abbrev genι (Y : Model Xo c β) : gen Y ⟶ Y.X := pullback.fst Y.s (spMap β)

abbrev genStr (Y : Model Xo c β) : gen Y ⟶ Sp c.F := pullback.snd Y.s (spMap β)

def genBd (Y : Model Xo c β) : Closeds (gen Y) :=
  ⟨(Set.range Y.jQ)ᶜ, (haveI := Y.jQ_open; Y.jQ.isOpenEmbedding.isOpen_range).isClosed_compl⟩

abbrev genBdIdeal (Y : Model Xo c β) : (gen Y).IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (genBd Y)

theorem mem_genBd {Y : Model Xo c β} {x : gen Y} : x ∈ genBd Y ↔ x ∉ Set.range Y.jQ := Iff.rfl

theorem mem_genBd_iff {Y : Model Xo c β} {x : gen Y} : x ∈ genBd Y ↔ genι Y x ∉ abLocus Y.t.G := by
  rw [mem_genBd, ← Y.ab_gen]; rfl

abbrev ChartRing (k : Type) [Field k] (m d : ℕ) : Type := MvPowerSeries (Fin m ⊕ Fin d) k

instance isDomain_chartRing (k : Type) [Field k] (m d : ℕ) : IsDomain (ChartRing k m d) := NoZeroDivisors.to_isDomain _

abbrev bdParam (k : Type) [Field k] (m d : ℕ) (i : Fin m) : ChartRing k m d := MvPowerSeries.X (Sum.inl i)

def IsToricChart (Z : Model Xo c β) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ gen Z)
    {t : SAB H (Sp (ChartRing k m d))} (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H l.M' P.D.toPre.X) : Prop :=
  IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
  (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
    Ideal.span {∏ i, bdParam k m d i} ∧
  (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) ∧
  Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧ P.TorsionIso ∧
  IsMonomial P.D.toPre (bdParam k m d) (fun i => γ i) ∧ IsPartOfBasis γ

def HasToricChart (Z : Model Xo c β) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m d)))
    (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (γ : Fin m → levelForms H l.M' P.D.toPre.X),
    ξ (closedPoint _) = x ∧ IsToricChart Z ξ P γ

namespace IsToricChart

variable {Z : Model Xo c β} {k : Type} [Field k] {m d : ℕ} {ξ : Sp (ChartRing k m d) ⟶ gen Z}
  {t : SAB H (Sp (ChartRing k m d))} {P : PELUnif (maximalIdeal (ChartRing k m d)) t}
  {γ : Fin m → levelForms H l.M' P.D.toPre.X}

theorem mem_abLocus_iff (h : IsToricChart Z ξ P γ) (p : Sp (ChartRing k m d)) :
    p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  obtain ⟨-, -, h3, ⟨μ⟩, -⟩ := h
  rw [← h3, mem_genBd_iff, not_not, ← abLocus_pullback abLocusOne Z.t.semi μ.cart.1 p]
  rfl


theorem centre_mem_iff (h : IsToricChart Z ξ P γ) : ξ (closedPoint _) ∈ genBd Z ↔ m ≠ 0 := by
  refine (h.2.2.1 _).trans ?_
  change _ ∈ maximalIdeal _ ↔ _
  rw [Ideal.IsPrime.prod_mem_iff]
  constructor
  · rintro ⟨i, -⟩ rfl
    exact i.elim0
  · intro hm
    refine ⟨⟨0, Nat.pos_of_ne_zero hm⟩, Finset.mem_univ _, ?_⟩
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp

theorem forms (h : IsToricChart Z ξ P γ) :
    (∀ i y, 0 ≤ (γ i : LinearMap.BilinForm ℤ P.D.toPre.X) y y) ∧ (∀ i, γ i ≠ 0) ∧
      ∀ y, y ≠ 0 → ∃ i, 0 < (γ i : LinearMap.BilinForm ℤ P.D.toPre.X) y y :=
  ⟨h.2.2.2.2.2.1.nonneg, h.2.2.2.2.2.2.linearIndependent.ne_zero,
    fun _ hy => h.2.2.2.2.2.1.exists_pos (maximalIdeal.isMaximal _).ne_top hy⟩

theorem nontrivial (h : IsToricChart Z ξ P γ) (hx : ξ (closedPoint _) ∈ genBd Z) : Nontrivial P.D.toPre.X := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  refine h.forms.2.1 ⟨0, Nat.pos_of_ne_zero (h.centre_mem_iff.1 hx)⟩ ?_
  ext a b
  simp [Subsingleton.elim a 0]

end IsToricChart

def IsArcBase (O' : Type) [CommRing O'] [IsDomain O'] (ϖ : O') : Prop :=
  (IsField O' ∧ ϖ = 1) ∨ (IsDiscreteValuationRing O' ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) O')

def IsArcChart (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) (ϖ : O')
    (χ : Sp (PowerSeries O') ⟶ Y.X) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧
  (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
  (∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) ∧
  Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ

theorem arcChart_iff (Y : Model Xo c β) : Y.N4 ↔
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : O →+* O') (ϖ : O') (a : ArcIn D l β O' b),
      IsArcBase O' ϖ → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, (∀ χ', χ' = χ ↔ IsArcChart Y a ϖ χ') ∧
        (Irreducible ϖ → ∀ (y' : Sp O' ⟶ Y.X) (ev : PowerSeries O' →+* O'), y' ≫ Y.s = spMap b →
          Set.range (Out.jK O' ≫ y') ⊆ Set.range Y.j →
          Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id O') ϖ y' →
          (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → spMap ev ≫ χ = y') := Iff.rfl

end Charts

section Model

variable {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F}

structure TorModel (Y : Model Xo c β) where

  Z : Model Xo c β

  b : Z.X ⟶ Y.X

  b_s : b ≫ Y.s = Z.s

  j_b : Z.j ≫ b = Y.j

  pull : SABMap Z.t Y.t b

  pull_univ : ∀ (T : Scheme.{0}) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
    g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g₁ ≫ Z.m.φ ≫ pull.φ = g₂ ≫ Y.m.φ

  smooth : SmoothOfRelativeDimension D.dim (genStr Z)

  snc : FinalTheorems.Snc (genBdIdeal Z)

  toric : ∀ x ∈ genBd Z, HasToricChart Z x

  lifts : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : O →+* O') (ϖ : O') (a : ArcIn D l β O' b')
    (χ : Sp (PowerSeries O') ⟶ Y.X), IsArcBase O' ϖ → IsArcChart Y a ϖ χ → ∃ χ'' : Sp (PowerSeries O') ⟶ Z.X, χ'' ≫ b = χ

  BD : EffCartierData Z.X

  BD_supp : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G

  BD_pos : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support

  m0 : ℕ

  torModel_multiplicity_pos : 0 < m0

theorem isProper_toroidalModel_structureMap (Y : Model Xo c β) : IsProper Y.s := by
  obtain ⟨N, i, hi, e⟩ := Y.proj
  have := isProper_str O N
  rw [← e]
  infer_instance

theorem isProper_genStr (Y : Model Xo c β) : IsProper (genStr Y) :=
  haveI := isProper_toroidalModel_structureMap Y
  inferInstance

namespace TorModel

variable {Y : Model Xo c β} (T : TorModel Y)

instance isProper_b : IsProper T.b := by
  have := isProper_toroidalModel_structureMap Y
  have : IsProper (T.b ≫ Y.s) := T.b_s ▸ isProper_toroidalModel_structureMap T.Z
  exact IsProper.of_comp T.b Y.s

theorem b_mem_abLocus (x : T.Z.X) : T.b x ∈ abLocus Y.t.G ↔ x ∈ abLocus T.Z.t.G :=
  abLocus_pullback abLocusOne Y.t.semi T.pull.cart.1 x

def bQ : gen T.Z ⟶ gen Y :=
  pullback.map _ _ _ _ T.b (𝟙 _) (𝟙 _) (by rw [Category.comp_id, T.b_s]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)] theorem bQ_genι : T.bQ ≫ genι Y = genι T.Z ≫ T.b := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem bQ_genStr : T.bQ ≫ genStr Y = genStr T.Z :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

instance isProper_bQ : IsProper T.bQ := by
  have := isProper_genStr Y
  have : IsProper (T.bQ ≫ genStr Y) := T.bQ_genStr ▸ isProper_genStr T.Z
  exact IsProper.of_comp T.bQ (genStr Y)

@[reassoc (attr := simp)] theorem jQ_bQ : T.Z.jQ ≫ T.bQ = Y.jQ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bQ_genι, ← Category.assoc]
    exact T.j_b
  · rw [Category.assoc, bQ_genStr, T.Z.jQ_over, Y.jQ_over]





theorem mem_support_BD_iff (x : gen T.Z) : genι T.Z x ∈ T.BD.idealSheaf.support ↔ x ∈ genBd T.Z :=
  ⟨fun h => mem_genBd_iff.2 (T.BD_supp _ h), T.BD_pos x⟩


theorem n3 (h : Y.N3) : T.Z.N3 := by
  intro R _ _ _ _ h1 h2 h3 ξ t μ hne hs
  obtain ⟨ν, -⟩ := ObjMaps.exists_sab_comp T.pull μ
  have e : (ξ ≫ T.b) ⁻¹' abLocus Y.t.G = ξ ⁻¹' abLocus T.Z.t.G := Set.ext fun x => T.b_mem_abLocus (ξ x)
  exact e ▸ h R h1 h2 h3 (ξ ≫ T.b) t ν (e ▸ hne) hs

theorem lift_spec {O' : Type} [CommRing O'] [IsDomain O'] {b' : O →+* O'} {a : ArcIn D l β O' b'} {ϖ : O'}
    {χ'' : Sp (PowerSeries O') ⟶ T.Z.X} (h : IsArcChart Y a ϖ (χ'' ≫ T.b)) :
    χ'' ≫ T.Z.s = spMap (PowerSeries.C (R := O')) ≫ spMap b' ∧
      ∀ x : Sp (PowerSeries O'), χ'' x ∈ abLocus T.Z.t.G ↔ PowerSeries.X ∉ x.asIdeal :=
  ⟨by rw [← T.b_s, ← Category.assoc]; exact h.1, fun x => (T.b_mem_abLocus (χ'' x)).symm.trans (h.2.1 x)⟩

end TorModel

theorem smooth_of_surjective (Y : Model Xo c β) (h : Function.Surjective Y.jQ) :
    SmoothOfRelativeDimension D.dim (genStr Y) := by
  have := Y.jQ_open
  have : Surjective Y.jQ := ⟨h⟩
  have : IsIso Y.jQ := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    ext x; simpa using h x)
  have := Xo.smooth
  have e : genStr Y = inv Y.jQ ≫ pullback.snd _ _ := by rw [IsIso.eq_inv_comp, Y.jQ_over]
  have hs : SmoothOfRelativeDimension D.dim
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  rw [e]
  have := smoothOfRelativeDimension_comp 0 D.dim (inv Y.jQ)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  rwa [Nat.zero_add] at this

def TorModel.ofNoBoundary (Y : Model Xo c β) (h : Function.Surjective Y.jQ) : TorModel Y where
  Z := Y
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Y.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Y.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := smooth_of_surjective Y h
  snc x := by
    have := smooth_of_surjective Y h
    have : Smooth (genStr Y) := SmoothOfRelativeDimension.smooth D.dim _
    have hr := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth c.F (genStr Y) x
    exact sncAt_of_not_mem _ x (fun hx => hx (h x)) (IsRegularLocalRing.of_isRegularRing_of_isLocalRing _)
  toric x hx := (hx (h x)).elim
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := EffCartierData.zero _
  BD_supp x hx := by
    refine (((EffCartierData.zero Y.X).mem_support_iff PUnit.unit (x := x) trivial).1 hx ?_).elim
    change x ∈ Y.X.basicOpen (1 : Γ(Y.X, ⊤))
    simp
  BD_pos x hx := (hx (h x)).elim
  m0 := 1
  torModel_multiplicity_pos := one_pos



end Model

end GlobalTheory.Toroidal
