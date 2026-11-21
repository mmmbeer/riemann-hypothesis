import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj UpperHalfPlane
open GlobalTheory.CM

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.EllipticFibrePrincipalData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def chi (H : Host E) : DirichletCharacter ℂ H.d :=
  (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

def logOm (H : Host E) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) -
    (deriv (DirichletCharacter.LFunction (chi H)) 1 / DirichletCharacter.LFunction (chi H) 1).re

structure IsEllFibre {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ω : R} {ω' : R'} (C : Ell H R ω)
    (C' : Ell H R' ω') (φ : C'.P.A.left ⟶ C.P.A.left) : Prop where
  val : ω' = f ω
  fib : IsPolFibre f C.P C'.P φ
  act : ∀ a, (C'.act.act a).left ≫ φ = φ ≫ (C.act.act a).left
  vec : IsVecOver f φ C.v C'.v

variable {K : Type} [Field K] [NumberField K]

def IsLogPeriod {ω : 𝓞 K} (C : Ell H (𝓞 K) ω) (x : ℝ) : Prop :=
  ∃ n : (K →+* ℂ) → ℝ, (∀ s, 0 < n s ∧ IsLieNormSq C.P C.v (s.comp (algebraMap (𝓞 K) K)) (n s)) ∧ x = -meanLog K n

def HasPeriod {ω : 𝓞 K} (C : Ell H (𝓞 K) ω) : Prop :=
  IsLogPeriod C (logOm H + Real.log (rootDiscr E / √H.d))

def wSide (H : Host E) (lin : Bool) : OK H := if lin then wK H else 1 - wK H

def kForm (D : Datum H) (ε : ℤˣ) (lin : Bool) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wSide H lin

def IsPrincipalDatum (D : Datum H) : Prop :=
  D.p = 1 ∧ D.q = 0 ∧ ∃ (I : Ideal (𝓞 E)) (emb : D.La →ₗ[𝓞 E] E),
    I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ Function.Injective emb ∧
    (∀ z : E, z ∈ LinearMap.range emb ↔ ∀ a ∈ I, ∃ b : 𝓞 E, (b : E) = (a : E) * z) ∧
    ∀ x y, (D.EF x y : ℝ) = 2 / √H.d *
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), (τ (emb x) * starRingEnd ℂ (τ (emb y))).im

def IsConjDatum (D D' : Datum H) : Prop :=
  D'.p = D.q ∧ D'.q = D.p ∧ ∃ e : D.La ≃ₗ[𝓞 E] D'.La, ∀ x y, D'.EF (e x) (e y) = -D.EF x y

structure IsHomFam {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (t : SAB H (Sp R)) {D : Datum H}
    (L : Submodule (𝓞 E) D.La) (ε : ℤˣ) (lin : Bool) (φ : L → (C.P.A ⟶ t.G)) : Prop where
  hom : ∀ a, IsMonHom (φ a)
  add : ∀ a b, φ (a + b) = φ a * φ b
  smul : ∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s
  side : ∀ a, C.act.act (wSide H lin) ≫ φ a = φ a ≫ t.act.act H.w0
  lam : ∀ a b : L, LamEq t.PP.L (φ a) (φ b) C.P.L (C.act.act (kForm D ε lin a b)) (𝟙 C.P.A)


structure IsExp {S : Scheme.{0}} (t : SAB H S) (y : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (ex : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop where
  period : IsPeriod D ty Pe
  add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ z ∈ Pe.range
  lin : ∀ (a : 𝓞 E) z, ex (fun k => ty k (a : E) * z k) = ex z ≫ t.act.act a
  hol : IsHolTo Set.univ (fun z => (ex z).left)
  diff : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (ex z).left) w v.left
  diff_onto : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (ex 0).left →
    ∃! w, IsDerivAt0 (fun z => (ex z).left) w v.left
  weil : ∀ (n : ℕ) (a b : D.La) (c : ℂˣ), 0 < n →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / n) →
    Out.WeilIs t.G t.PP.L n (ex ((n : ℂ)⁻¹ • Pe a)) (ex ((n : ℂ)⁻¹ • Pe b)) (unitOn c)

theorem isHolTo_slice {g : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (h : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ))) fun bz => e bz.2) :
    IsHolTo Set.univ e := by
  intro U f
  obtain ⟨h₁, h₂⟩ := h U f
  have hd : Differentiable ℂ fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z) := by fun_prop
  refine ⟨?_, ?_⟩
  · have e₁ : {b ∈ Set.univ | ⊤ ≤ e b ⁻¹ᵁ U} = (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) ⁻¹'
        {b ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b.2 ⁻¹ᵁ U} :=
      Set.ext fun z => ⟨fun h => And.intro (And.intro trivial trivial) h.2, fun h => And.intro trivial h.2⟩
    rw [e₁]
    exact h₁.preimage hd.continuous
  · have := h₂.comp (s := {b ∈ Set.univ | ⊤ ≤ e b ⁻¹ᵁ U}) hd.differentiableOn
      fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩
    exact this

theorem isExp_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) : IsExp Xo.univ.t (FU.u i Pe) (FU.Di i) ty Pe (FU.ex i Pe) where
  period := hP
  add := FU.ex_add i Pe hP
  onto := FU.ex_onto i Pe hP
  ker := FU.ex_ker i Pe hP
  lin := FU.ex_lin i Pe hP
  hol := isHolTo_slice (e := fun z => (FU.ex i Pe z).left) (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ
      ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  diff := (FU.ex_diff i Pe hP).1
  diff_onto := (FU.ex_diff i Pe hP).2
  weil := FU.ex_weil i Pe hP

structure IsLatData (D₁ D₂ D : Datum H) {p q : ℕ} (lp : Fin p → (D₁.La →ₗ[𝓞 E] D.La))
    (lm : Fin q → (D₂.La →ₗ[𝓞 E] D.La)) (hp : Fin p → 𝓞 E) (hm : Fin q → 𝓞 E) (La : ℝ) : Prop where
  sig₁ : D₁.p = 1 ∧ D₁.q = 0
  sig₂ : D₂.p = 0 ∧ D₂.q = 1
  sig : D.p = p ∧ D.q = q
  inj : Function.Injective fun x : (Fin p → D₁.La) × (Fin q → D₂.La) => ∑ j, lp j (x.1 j) + ∑ j, lm j (x.2 j)
  span : ∀ z : D.La, ∃ n : ℕ, 0 < n ∧ ∃ (x : Fin p → D₁.La) (y : Fin q → D₂.La),
    n • z = ∑ j, lp j (x j) + ∑ j, lm j (y j)
  orth : ∀ i j x y, D.EF (lp i x) (lm j y) = 0
  pos : ∀ x : Fin p → D₁.La, x ≠ 0 → 0 < H.rt0.im * D.EF (H.w0 • ∑ j, lp j (x j)) (∑ j, lp j (x j))
  neg : ∀ y : Fin q → D₂.La, y ≠ 0 → H.rt0.im * D.EF (H.w0 • ∑ j, lm j (y j)) (∑ j, lm j (y j)) < 0
  LocFacts₂ : ∀ j x y, D.EF (lp j x) (lp j y) = D₁.EF (hp j • x) y
  formM : ∀ j x y, D.EF (lm j x) (lm j y) = D₂.EF (hm j • x) y
  boundP : ∀ j (τ : E →+* ℂ), √‖τ (hp j : E)‖ ≤ La
  boundM : ∀ j (τ : E →+* ℂ), √‖τ (hm j : E)‖ ≤ La

def IsPointOf {D₁ D₂ D : Datum H} {p q : ℕ} (lp : Fin p → (D₁.La →ₗ[𝓞 E] D.La))
    (lm : Fin q → (D₂.La →ₗ[𝓞 E] D.La)) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) : Prop :=
  IsTypeFn H D.p D.q ty ∧ ∃ hP : IsPeriod D ty Pe,
    (∀ j x, lp j x ∈ PureType.lat hP H.rt0) ∧ ∀ j y, lm j y ∈ PureType.lat hP (-H.rt0)

theorem im_mul_form_pos {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) {ρ : ℂ} (hρ : ρ ^ 2 = -(H.d : ℂ)) {a : D.La} (ha : a ∈ PureType.lat hP ρ) (h0 : a ≠ 0) :
    0 < ρ.im * D.EF (H.w0 • a) a := by
  have hne := PureType.form_w0_ne_zero hP hρ ha h0
  obtain ⟨Hm, -, hpos, hE⟩ := hP.2.2.2.2
  have hz : Pe a ≠ 0 := fun h => h0 (hP.2.1 (h.trans (map_zero Pe).symm))
  have h1 := hE (H.w0 • a) a
  have h2 := hE a a
  rw [D.alt] at h2
  have h3 : hermForm Hm (Pe (H.w0 • a)) (Pe a) = ((1 + ρ) / 2) * hermForm Hm (Pe a) (Pe a) := by
    rw [PureType.period_w0_smul hP ha, hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  have h4 : ((1 + ρ) / 2).im = ρ.im / 2 := by simp
  rw [h3, Complex.mul_im, h2, h4, Int.cast_zero, mul_zero, zero_add] at h1
  have h5 := hpos _ hz
  have h6 : ρ.im ≠ 0 := fun h => hne (by rw [h] at h1; exact_mod_cast (by simpa using h1.symm))
  rw [← h1]
  have := mul_self_pos.2 h6
  nlinarith [mul_pos this h5]


def IsThetaDegOn (x : KeyIn K) (δ : ℝ) : Prop :=
  ∃ (oa : HeightOneSpectrum (𝓞 K) → ℤ) (nth : (K →+* ℂ) → ℝ),
    (∀ 𝔭, ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x 𝔭 a M ∧
      𝔭.valuation K a = WithZero.exp (-oa 𝔭)) ∧ (Function.support oa).Finite ∧
    (∀ σ, 0 < nth σ ∧ ∃ (x' : KeyIn ℂ) (nη : ℝ), KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) nη) ∧
    δ = ((∑ σ, Real.log (nth σ)) / 2 + ∑ᶠ 𝔭, (oa 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal)) / Module.finrank ℚ K

def IsThetaDeg (P : Out.PolAV (Sp (𝓞 K))) (δ : ℝ) : Prop :=
  ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left), IsPolFibre (algebraMap (𝓞 K) K) P x.P φ ∧ IsThetaDegOn x δ

end GlobalTheory.IndefiniteRowSideFullHecke.EllipticFibrePrincipalData
end
