import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models
open scoped CategoryTheory.Obj

namespace GlobalTheory.GlobalClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_factor {l : Level H} (c : Coeff l) {R : Type} [CommRing R] [IsLocalRing R] (φ : 𝓞 c.F →+* R) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
      (ψ : c.V W →+* R), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) ∧ ψ.comp b = φ := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal R).comap φ)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top)
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)
  haveI : Finite (𝓞 c.F ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm0
  obtain ⟨p, hchar⟩ := CharP.exists (𝓞 c.F ⧸ m)
  have hp : p.Prime := CharP.char_is_prime (𝓞 c.F ⧸ m) p
  have hpm : (p : 𝓞 c.F) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]
  let ι : 𝓞 c.F →+* ℂ := c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)
  have hι : Function.Injective ι := Subtype.val_injective.comp (RingOfIntegers.coe_injective)
  have hbij : Function.Bijective ι.rangeRestrict :=
    ⟨fun a b h => hι (congrArg (fun z : ι.range => (z : ℂ)) h), ι.rangeRestrict_surjective⟩
  have hne : m.map ι.rangeRestrict ≠ ⊤ := (Ideal.map_isMaximal_of_equiv (RingEquiv.ofBijective _ hbij) (p := m)).ne_top
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hnon : ∀ x ∈ m, ι x ∈ W.nonunits := fun x hx => hW ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have hpW : (p : ℂ) ∈ W.nonunits := map_natCast ι p ▸ hnon _ hpm
  obtain ⟨b, hb, -⟩ := GlobalModelGuards.exists_incl c W
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hpW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  have hu : ∀ s : v.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    by_contra h
    have h1 := hnon _ (hle (show (s : 𝓞 c.F) ∈ (IsLocalRing.maximalIdeal R).comap φ from h))
    obtain ⟨u, hu⟩ := (IsLocalization.map_units (v.valuationSubringAtPrime c.F) s).exists_right_inv
    have h2 : ((u : c.F) : ℂ) ∈ W := (hv ▸ u.2 : (u : c.F) ∈ c.V W)
    have h3 : ι s * ((u : c.F) : ℂ) = 1 := congrArg (fun z : v.valuationSubringAtPrime c.F => ((z : c.F) : ℂ)) hu
    rw [ValuationSubring.mem_nonunits_iff] at h1
    have h4 := congrArg W.valuation h3
    rw [map_mul, map_one] at h4
    exact (mul_lt_one_of_lt_of_le h1 ((W.valuation_le_one_iff _).2 h2)).ne h4
  refine ⟨p, W, hp, hpW, b, (IsLocalization.lift (S := v.valuationSubringAtPrime c.F) hu).comp
    (ValuationSubring.inclusion _ _ hv.ge), hb, RingHom.ext fun x => ?_⟩
  have e : ValuationSubring.inclusion _ _ hv.ge (b x) = algebraMap _ (v.valuationSubringAtPrime c.F) x :=
    Subtype.ext (hb x)
  rw [RingHom.comp_apply, RingHom.comp_apply, e, IsLocalization.lift_eq]

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {s : Sys Xo} {l : Level H} {c : Coeff l}
  {hg : ∀ p : ℕ, p.Prime → l.GoodAt p} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}

end GlobalTheory.GlobalClauses
