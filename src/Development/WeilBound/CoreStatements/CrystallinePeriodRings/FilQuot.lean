import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

section SlopeTestRemainingChoices

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem filq_ker_eq : RingHom.ker (Per6.θD l) = IsLocalRing.maximalIdeal (Per6.BdRp l) :=
  (IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

theorem filq_tiltMap_ε1 (AI : LocAinf l P) : Per6.tiltMap l AI.ε1 =
    (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm (Per6.tiltMap l AI.ε) := by
  apply (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow, LocAinf.ε1,
    frobeniusEquiv_symm_pow_p]

theorem filq_ainfMap_ξ (AI : LocAinf l P) :
    Per6.ainfMap l AI.ξ = AInf.xi (K := ℂ_[l]) (Per6.tiltMap l AI.ε) := by
  rw [LocAinf.ξ, map_sum, AInf.xi]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, frob_ainfMap_teich, filq_tiltMap_ε1]

theorem filq_aD_mem_iff (AI : LocAinf l P) (a : Ainf l) (n : ℕ) :
    Per6.aD l a ∈ RingHom.ker (Per6.θD l) ^ n ↔ AI.ξ ^ n ∣ a := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi (untilt_ε AI) (untilt_ε_root_ne_one AI)
  have h1 : Per6.aD l a ∈ RingHom.ker (Per6.θD l) ^ n ↔
      Per6.ainfMap l a ∈ Ideal.span {ACris.xiGen ℂ_[l] l ^ n} := by
    rw [filq_ker_eq, IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span ACris.ker_eq_span_xiGen,
      Ideal.span_singleton_pow, ← ACris.algebraMap_dvd_iff, map_pow,
      ← toBDeRhamPlus_mem_span_pow_iff ACris.ker_eq_span_xiGen]
    exact Iff.rfl
  rw [h1, ← Ideal.span_singleton_pow, ← ACris.ker_eq_span_xiGen, hξ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← filq_ainfMap_ξ, ← map_pow]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := ainfMap_surjective c
    exact ⟨b, ainfMap_injective (hc.trans (map_mul _ _ _).symm)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Per6.ainfMap l b, map_mul _ _ _⟩

theorem filq_θD_π₁ (AI : LocAinf l P) :
    Per6.θD l (Per6.aD l AI.π₁) = ((AI.ζ 1 : OC l) : ℂ_[l]) - 1 := by
  rw [LocAinf.π₁, map_sub, map_sub, map_one, map_one, θD_aD, frob_ainfMap_teich,
    WittVector.fontaineTheta_teichmuller, filq_tiltMap_ε1, untilt_ε_root]
  rfl

theorem filq_tie_fil (T : LocTied6 l P AI) (K : FinExt l) (n : ℕ) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) :
    x ∈ (P.PD K).Fil (n : ℤ) ↔ y ∈ RingHom.ker (Per6.θD l) ^ n := by
  rw [T.fil, h, fil_nat]

theorem filq_θ_eq (T : LocTied6 l P AI) (J : ThetaL P AI) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) {z : Om l}
    (hz : Per6.θD l y = (z : ℂ_[l])) : J.θ x = (z : ℂ_[l]) := by
  obtain ⟨v, hv, hθ⟩ := T.om z
  have hd : T.eD (x - algebraMap (Om l) P.R.BdR z) =
      algebraMap (Per6.BdRp l) (Per6.BdR l) (y - v) := by
    rw [map_sub, map_sub, h, hv]
  have h0 := (tie_fil_zero T (botExt l) _).2 ⟨_, hd⟩
  have h0' := (tie_fil_zero T (botExt l) _).2 ⟨_, hv⟩
  have h1 : x - algebraMap (Om l) P.R.BdR z ∈ (P.PD (botExt l)).Fil 1 :=
    (filq_tie_fil T (botExt l) 1 hd).2 (by
      rw [pow_one, RingHom.mem_ker, map_sub, hz, hθ, sub_self])
  have h2 := J.θ_add _ h0 _ h0'
  rwa [sub_add_cancel, (J.θ_ker _ h0).2 h1, zero_add, J.θ_Om] at h2

end SlopeTestRemainingChoices

end PositivityTheory.LocInh
