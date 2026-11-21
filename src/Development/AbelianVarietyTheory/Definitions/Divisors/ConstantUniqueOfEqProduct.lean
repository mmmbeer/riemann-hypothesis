import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.PairModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hecke_pow {η : (AE D)ˣ →* Circle} (hη : IsHeckeChar D η) (n : ℕ) : IsHeckeChar D (η ^ n) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact hη.1.pow n
  · rw [MonoidHom.pow_apply, hη.2 x, one_pow]

theorem res_pow {η : (AE D)ˣ →* Circle} (hη : ResEta D η 1) (n : ℕ) : ResEta D (η ^ n) n :=
  ⟨hη.1, fun e he a => by rw [MonoidHom.pow_apply, hη.2 e he a, pow_one]⟩

theorem exp_pow {η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) :
    HasInfExp D (η ^ n) τ ((n : ℚ) / 2) := by
  obtain ⟨m, hm, h1, h2⟩ := hη
  have hm1 : m = 1 := by
    have : (m : ℚ) = 1 := by rw [hm]; norm_num
    exact_mod_cast this
  subst hm1
  refine ⟨n, by push_cast; ring, h1, fun θ hθ x hx hx' => ?_⟩
  rw [MonoidHom.pow_apply, Circle.coe_pow, h2 θ hθ x hx hx', zpow_one, zpow_natCast]

theorem unramAt_of_everywhere {η : (AE D)ˣ →* Circle} (hη : UnramEverywhere D η) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : UnramAt ε η := by
  intro x h1 h2 h3
  refine hη x ?_ h2 h3
  obtain ⟨α, rfl, -⟩ := hε
  have h4 := congrArg (infPart D) h1
  have h5 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show infPart D ((pairA D.host.F 0 α) ⊗ₜ 1) = 0
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [map_mul, h5, zero_mul, map_sub, map_one] at h4
  exact (sub_eq_zero.1 h4.symm)

theorem isPair_pow {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (k : ℕ) (W : HSp D) (hW : W.SigOK)
    (om : GA D (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) × GA D W →*
      Module.End ℂ (WO (D := D) (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W → ℂ))
    (hom : IsWeilDatumO ψ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W (η ^ (2 * k)) (η ^ W.rank) om) :
    IsPair ψ θ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W (η ^ (2 * k)) (η ^ W.rank) om where
  weil := hom
  inf := hθ
  std := Matrix.ext fun i j => by
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral (2 * k) (fun _ => false) (2 * k) 0 i j).trans ?_
    exact (Matrix.one_apply (i := i) (j := j)).symm
  even := ⟨k, two_mul k⟩
  sigV := Examples₂.posSpace_sigOK _ _
  sigW := hW
  expV τ := ⟨k, by have := exp_pow (hη.2.2.2 τ) (2 * k); convert this using 1; push_cast; ring⟩
  expW τ := ⟨0, by have := exp_pow (hη.2.2.2 τ) W.rank; convert this using 1; push_cast; ring⟩
  unr v ε h := by
    have h1 := unramAt_of_everywhere hη.2.1 h.1
    exact ⟨fun x a b c => by rw [MonoidHom.pow_apply, h1 x a b c, one_pow],
      fun x a b c => by rw [MonoidHom.pow_apply, h1 x a b c, one_pow]⟩
  eta := ⟨η, hη⟩

theorem exists_isPair (hη : ∃ η, IsEtaTilde D η)
    (hex : ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
      IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om)
    (k : ℕ) (W : HSp D) (hW : W.SigOK) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle)
      (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), V.rank = 2 * k ∧ IsPair ψ θ V W χV χW om := by
  obtain ⟨η, hη⟩ := hη
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨om, hom⟩ := hex ψ hψ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W (η ^ (2 * k)) (η ^ W.rank)
    (hecke_pow hη.1 _) (hecke_pow hη.1 _) (res_pow hη.2.2.1 _) (res_pow hη.2.2.1 _)
  exact ⟨ψ, θ, _, _, _, om, rfl, isPair_pow hη hθ k W hW om hom⟩



theorem finite_levQc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (l : Level H) : Finite (LevQc Dw l) := by
  have hM : Mfr l ≠ ⊥ := by
    intro h
    have h₁ : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := (Mfr l).finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul (Mfr l) (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem hatC_phiHat {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}
    (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    inC c (phiHat c φ q) = hatC l (fun x => inC c (φ x)) q := by
  haveI := finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  have hz : inC c (zetaM c) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    rw [zetaM, map_pow]
    show zeta l.M' ^ (l.M' / l.M) = _
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have h0 : 0 < l.M := by have := l.three_le; omega
    have h1 : l.M' ≠ 0 := Nat.lcm_ne_zero h0.ne' l.A_pos.ne'
    have h2 : (m : ℂ) ≠ 0 := by rintro h; apply h1; rw [hm, Nat.cast_eq_zero.1 h, mul_zero]
    have h3 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [zeta, ← Complex.exp_nat_mul, hm, Nat.mul_div_cancel_left _ h0]
    congr 1
    push_cast
    field_simp
  rw [phiHat, hatC, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀, hz]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

end

end GlobalTheory.AdTh.PairModel
