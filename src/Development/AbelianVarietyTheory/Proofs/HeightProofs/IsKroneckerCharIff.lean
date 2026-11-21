import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LinePeriodExponential
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexConjugate

noncomputable section
namespace GlobalTheory.CM.Compare

open GlobalTheory.IndefiniteRowSideFullHecke

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem conj_LFunction_conj {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (h₁ : χ ≠ 1)
    (hr : ∀ a, conj (χ a) = χ a) : (conj ∘ χ.LFunction ∘ conj : ℂ → ℂ) = χ.LFunction := by
  have hd := DirichletCharacter.differentiable_LFunction h₁
  have hd' : Differentiable ℂ (conj ∘ χ.LFunction ∘ conj : ℂ → ℂ) := fun z =>
    differentiableAt_conj_conj_iff.mpr (hd _)
  refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (fun z _ => hd'.analyticAt z) (fun z _ => hd.analyticAt z) ?_
  refine Filter.eventuallyEq_of_mem
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num))
    fun z (hz : 1 < z.re) => ?_
  simp only [Function.comp]
  rw [χ.LFunction_eq_LSeries hz, χ.LFunction_eq_LSeries (by rwa [Complex.conj_re]), LSeries, LSeries,
    Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hr,
      ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity), Complex.conj_natCast]

theorem logDeriv_im {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (h₁ : χ ≠ 1) (hr : ∀ a, conj (χ a) = χ a) :
    (((deriv χ.LFunction 1 / χ.LFunction 1).re : ℝ) : ℂ) = deriv χ.LFunction 1 / χ.LFunction 1 := by
  have e := conj_LFunction_conj h₁ hr
  have e₀ : conj (χ.LFunction 1) = χ.LFunction 1 := by simpa using congrFun e 1
  have e₁ : conj (deriv χ.LFunction 1) = deriv χ.LFunction 1 := by
    have := congrFun (deriv_conj_conj (f := χ.LFunction)) 1
    rw [e] at this
    simpa using this.symm
  rw [← Complex.conj_eq_iff_re, map_div₀, e₀, e₁]

theorem isKroneckerChar_iff (χ : DirichletCharacter ℂ H.d) : IsKroneckerChar χ ↔ χ = LogarithmicDifferentialCharacter.chi H := by
  have h₀ : IsKroneckerChar (LogarithmicDifferentialCharacter.chi H) := isKroneckerChar_quadraticChar (by have := H.d_mod; omega)
  refine ⟨fun h => MulChar.ext' fun a => ?_, fun h => h ▸ h₀⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
  rcases Nat.even_or_odd n with hn | hn
  · have ho : Odd (n + H.d) := hn.add_odd (Nat.odd_iff.2 (by have := H.d_mod; omega))
    have := (h _ ho).trans (h₀ _ ho).symm
    simpa using this
  · exact (h n hn).trans (h₀ n hn).symm

theorem dlogL_eq [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) :
    (LogarithmicDifferentialCharacter.dlogL H : ℂ) = deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain rfl := (isKroneckerChar_iff χ).1 h
  exact logDeriv_im (LogarithmicDifferentialCharacter.chi_ne_one H) fun a => by simp [LogarithmicDifferentialCharacter.chi]

theorem logOm_eq [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) :
    logOm E χ = (LogarithmicDifferentialCharacter.logOm H : ℝ) := by
  rw [logOm, LogarithmicDifferentialCharacter.logOm, Complex.ofReal_sub, dlogL_eq h]

theorem logOm_eq_logOmCurve [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (h : IsKroneckerChar χ) {K : Type} [Field K]
    [NumberField K] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -H.d) : logOm K χ = (LogarithmicDifferentialCharacter.logOmCurve H : ℝ) := by
  rw [logOm_of_finrank_eq_two h2 hD, LogarithmicDifferentialCharacter.logOmCurve, Complex.ofReal_sub, dlogL_eq h]

section Curve

variable {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'}

end Curve

theorem hasPeriod_iff {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) :
    C.HasPeriod x ↔ LogarithmicDifferentialCharacter.HasPeriod C x :=
  exists_congr fun _ => and_congr_right fun _ => eq_comm

section Family

variable {R : Type} [CommRing R] {ω : R} {C : Ell H R ω} {T : PAT H (Sp R)} {D : Datum H} {L : Submodule (𝓞 E) D.La}
  {φ : L → (C.P.A ⟶ T.t.G)}

end Family

section Lattice

theorem span_iff {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {I : Type}
    [Fintype I] {N : I → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module O (N i)] (f : ∀ i, N i →ₗ[O] M) :
    (∃ n : ℕ, 0 < n ∧ ∀ a : M, ∃ x : ∀ i, N i, n • a = ∑ i, f i (x i)) ↔
      ∀ a : M, ∃ n : ℕ, 0 < n ∧ n • a ∈ ⨆ i, LinearMap.range (f i) := by
  classical
  have key : ∀ a : M, a ∈ ⨆ i, LinearMap.range (f i) ↔ ∃ x : ∀ i, N i, a = ∑ i, f i (x i) := fun a => by
    refine ⟨fun h => ?_, ?_⟩
    · refine Submodule.iSup_induction _ (motive := fun a => ∃ x : ∀ i, N i, a = ∑ i, f i (x i)) h ?_ ⟨0, by simp⟩ ?_
      · rintro i _ ⟨b, rfl⟩
        refine ⟨Pi.single i b, ?_⟩
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
          Pi.single_eq_same]
      · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, by simp [Finset.sum_add_distrib]⟩
    · rintro ⟨x, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩
  simp only [← key]
  refine ⟨fun ⟨n, hn, h⟩ a => ⟨n, hn, h a⟩, fun h => ?_⟩
  choose n hn h using h
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∏ a ∈ s, n a, Finset.prod_pos fun a _ => hn a, fun a => ?_⟩
  have : Submodule.span O (s : Set M) ≤
      (⨆ i, LinearMap.range (f i)).comap ((∏ a ∈ s, n a) • (LinearMap.id : M →ₗ[O] M)) :=
    Submodule.span_le.2 fun b hb => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (show b ∈ s from hb)
      show (∏ a ∈ s, n a) • b ∈ ⨆ i, LinearMap.range (f i)
      rw [hc, mul_comm, mul_smul]
      exact nsmul_mem (h b) c
  exact this (hs ▸ Submodule.mem_top)

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

def latEquiv (Λ : ℝ) : LogarithmicDifferentialCharacter.LatData hP Λ ≃
    {Z : CMLat hP D.p D.q // 1 ≤ Λ ∧ ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ Λ ^ 2} where
  toFun X := ⟨⟨X.A, X.sigP, X.sigM, X.ψ, X.pure, X.hh, X.form, (haveI := D.fin; span_iff X.ψ).2 X.span⟩,
    X.one_le, X.bound⟩
  invFun Z := ⟨Z.1.D₁, Z.1.sigP, Z.1.sigM, Z.1.f, Z.1.hh, Z.1.pure, Z.1.form,
    (haveI := D.fin; span_iff Z.1.f).1 Z.1.span, Z.2.1, Z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem latEquiv_D₁ {Λ : ℝ} (X : LogarithmicDifferentialCharacter.LatData hP Λ) : (latEquiv hP Λ X).1.D₁ = X.A := rfl

end Lattice

variable {K : Type} [Field K] [NumberField K]

theorem isThetaDeg_iff (x : KeyIn K) (δ : ℝ) : IsThetaDeg x δ ↔ LogarithmicDifferentialCharacter.IsDegDe x δ := by
  refine exists₂_congr fun oa nth => ⟨fun ⟨a, b, c, d⟩ => ⟨a, c, fun σ => ⟨?_, b σ⟩, d⟩,
    fun ⟨a, c, b, d⟩ => ⟨a, fun σ => (b σ).2, c, d⟩⟩
  obtain ⟨x', nη, -, h⟩ := b σ
  exact (LamF.KeyArch.pos_of_isArchNorm thetaUnifAV_all x' h).1

theorem exists_key_iff (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) :
    (∃ (F : GenFib P) (hg : _) (rig : _) (hr : _) (th : _) (hth : _), F.key hg rig hr th hth = x) ↔
      ∃ φ : x.P.A.left ⟶ P.A.left, IsPolFibre (algebraMap (𝓞 K) K) P x.P φ := by
  constructor
  · rintro ⟨F, hg, rig, hr, th, hth, rfl⟩
    exact ⟨F.φ, F.fib⟩
  · rintro ⟨φ, h⟩
    exact ⟨⟨x.P, φ, h, x.v, x.basis⟩, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, rfl⟩

theorem isDegDeOf_iff (P : Out.PolAV (Sp (𝓞 K))) (δ : ℝ) :
    (∃ (F : GenFib P) (hg : _) (rig : _) (hr : _) (th : _) (hth : _), IsThetaDeg (F.key hg rig hr th hth) δ) ↔
      LogarithmicDifferentialCharacter.IsDegDeOf P δ := by
  constructor
  · rintro ⟨F, hg, rig, hr, th, hth, h⟩
    exact ⟨_, F.φ, F.fib, (isThetaDeg_iff _ _).1 h⟩
  · rintro ⟨x, φ, h, hδ⟩
    obtain ⟨F, hg, rig, hr, th, hth, rfl⟩ := (exists_key_iff P x).2 ⟨φ, h⟩
    exact ⟨F, hg, rig, hr, th, hth, (isThetaDeg_iff _ _).2 hδ⟩

end GlobalTheory.CM.Compare
end
