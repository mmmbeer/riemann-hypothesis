import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts GlobalTheory.AdTh
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh

theorem unr_of {D : D7} {χ : (AE D)ˣ →* Circle} (h : UnramEverywhere D χ) {v ε} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  refine h x ?_ h1 h2
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem isPair_pow (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (V W : HSp D) (h1 : V.gram = 1) (h2 : Even V.rank) (h3 : V.SigOK) (h4 : W.SigOK) (η) (hη : IsEtaTilde D η) :
    ∃ om, IsPair ψ θ V W (η ^ V.rank) (η ^ W.rank) om := by
  have hH : ∀ n : ℕ, IsHeckeChar D (η ^ n) := fun n =>
    ⟨by
      have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by funext x; simp
      rw [this]; exact hη.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hR : ∀ n : ℕ, ResEta D (η ^ n) n := fun n =>
    ⟨hη.2.2.1.1, fun e he a => by rw [MonoidHom.pow_apply, hη.2.2.1.2 e he a, pow_one]⟩
  have hE : ∀ (n : ℕ) τ, HasInfExp D (η ^ n) τ ((n : ℚ) / 2) := fun n τ => by
    obtain ⟨m, hm, ha, hb⟩ := hη.2.2.2 τ
    have hm1 : m = 1 := by
      have : (m : ℚ) = 1 := by rw [hm]; norm_num
      exact_mod_cast this
    subst hm1
    refine ⟨n, by push_cast; ring, ha, fun θ' hθ' x hx hx' => ?_⟩
    rw [MonoidHom.pow_apply, Circle.coe_pow, hb θ' hθ' x hx hx', zpow_one, zpow_natCast]
  have hU : ∀ n : ℕ, UnramEverywhere D (η ^ n) := fun n x a b c => by
    rw [MonoidHom.pow_apply, hη.2.1 x a b c, one_pow]
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hψ V W _ _ ⟨η, hη⟩ (hH _) (hH _) (hR _) (hR _)
  refine ⟨om, hom, hθ, h1, h2, h3, h4, fun τ => ?_, fun τ => ⟨0, by simpa using hE W.rank τ⟩,
    fun v ε h => ⟨unr_of (hU _) h.1, unr_of (hU _) h.1⟩, ⟨η, hη⟩⟩
  obtain ⟨a, ha⟩ := h2
  refine ⟨a, ?_⟩
  have := hE V.rank τ
  rwa [show ((V.rank : ℚ) / 2) = ((a : ℤ) : ℚ) by rw [ha]; push_cast; ring] at this


end GlobalTheory.AdTh
