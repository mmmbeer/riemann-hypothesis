import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

def CoverVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ThVal Δ.cov.Xo₂ Δ.cov.c₂ Δ.nab₂ y₂ Λ N (Δ.cov.incl β) (Δ.combinedCoeff x₀) a (MvPolynomial.map Δ.cov.incl P) v

def IsShortRule {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R),
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra Δ.cov.c₂.F S') (φ : p.R →+* S')
      (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'), φ.FaithfullyFlat ∧ Δ.cov.LiesOver φ y₂ y) ∧
    ∀ (S' : Type) [CommRing S'] [Algebra Δ.cov.c₂.F S'] (φ : p.R →+* S') (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'),
      Δ.cov.LiesOver φ y₂ y → ∃ v, CoverVal Δ y₂ Λ N β x₀ a P v ∧ φ (f p y) = v * Δ.fnVal y₂

def ramPart (E : Type) [Field E] [NumberField E] : ℕ := 2 * (discr E).natAbs

def reps (n : ℕ) (s : ℕ+) : Set (Lat E n) :=
  {Λ | Λ.InGenus ∧ Λ.StdAt (ramPart E * Δ.a.l₂.M * s)}

def IsSeriesData {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ ∈ reps Δ n 1 ∧ Λ.Admissible Δ.a.l₂.M N ∧ IsBeLat Dw c Λ β ∧ P ∈ harmLat Dw c a Λ

def shortGen (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}

def CoverTot : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∀ (S : Type) [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S),
      ∃! v, CoverVal Δ y₂ Λ N β x₀ a P v

def Descends : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∃ f ∈ sec Xo c a n, IsShortRule Δ Λ N β x₀ a P f

def ShortRat : Prop := CoverTot Δ ∧ Descends Δ

def OnePos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∃ τ : E →+* ℂ, InPsi H τ ∧ (0 < Dw.p → 1 ≤ a (τ, Dw.p - 1))

def ShortInCusp (hK : ReflexLe Dw c) (nV : ℕ)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a → ∀ f ∈ shortGen Δ hK nV a n, f ∈ cusp a n

variable (Xo c) in

def ShortRatCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ Δ : DeltaDatum Xo c nab, ShortRat Δ

variable (Xo c) in

def ShortInCuspCanonical (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ),
    ShortInCusp Δ hK nV cusp

theorem IsShortRule.unique (h : CoverTot Δ) {n N : ℕ} {Λ : Lat E n} {β : c.F} {x₀ : Fin n → ConjCl Dw l}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hd : IsSeriesData Δ Λ N β a P) {f g : Rul Xo c}
    (hf : IsShortRule Δ Λ N β x₀ a P f) (hg : IsShortRule Δ Λ N β x₀ a P g) : f = g := by
  funext p y
  obtain ⟨⟨S', _, _, φ, y₂, hff, hl⟩, hf2⟩ := hf p y
  obtain ⟨v, hv, hfv⟩ := hf2 S' φ y₂ hl
  obtain ⟨w, hw, hgw⟩ := (hg p y).2 S' φ y₂ hl
  obtain ⟨u, -, hu⟩ := h n N Λ β x₀ a P hd S' y₂
  have hvw : v = w := (hu v hv).trans (hu w hw).symm
  apply hff.injective
  rw [hfv, hgw, hvw]

private theorem eqAtPrime_refl {n : ℕ} (p : ℕ) (hp : p.Prime) (L : Submodule (𝓞 E) (Fin n → E)) :
    EqAtPrime p L L :=
  ⟨fun x hx => ⟨1, hp.not_dvd_one, by simpa using hx⟩, fun x hx => ⟨1, hp.not_dvd_one, by simpa using hx⟩⟩

theorem std_mem_reps (n : ℕ) (s : ℕ+) : Lat.std E n ∈ reps Δ n s := by
  refine ⟨fun p hp => ⟨LinearEquiv.refl E _, fun x y => rfl, ?_⟩, fun p hp _ => eqAtPrime_refl p hp _⟩
  have hm : ((Lat.std E n).map (LinearEquiv.refl E _)).L = (Lat.std E n).L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hm]
  exact eqAtPrime_refl p hp _

theorem exists_inPsi (H : Host E) : ∃ τ : E →+* ℂ, InPsi H τ := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have e : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h0 := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simpa using h0
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (e.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨τ, h⟩
  · refine ⟨(starRingEnd ℂ).comp τ, ?_⟩
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h, map_neg]
    have hs := H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h1 := congrArg Complex.re hs
    have h2 := congrArg Complex.im hs
    simp [sq] at h1 h2
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by nlinarith [h2]) with h3 | h3
      · exact h3
      · rw [h3] at h1
        nlinarith [sq_nonneg H.rt0.re]
    apply Complex.ext <;> simp [hre]

end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c}

def RankRange (Dw : Datum H) (n : ℕ) : Prop :=
  3 ≤ Dw.p + Dw.q ∧ 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n

def SpanRange (Dw : Datum H) (l : Level H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  l.A = 1 ∧ Dom a n ∧ RankRange Dw n

section Span

variable (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))

def shortSpanK (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  Submodule.span c.F (shortGen Δ hK nV a n)

def CuspLeSpan : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → cusp a n ≤ shortSpanK Δ hK nV a n

def CuspEqSpan : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → OnePos Dw a → cusp a n = shortSpanK Δ hK nV a n

end Span

section Std

variable (Xo c nab)

def IsTranslateFamily {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (w : (Fin n → NamedCl Dw l) → Rul Xo c) : Prop :=
  ∀ x : Fin n → Dw.La, IsThRule Xo c nab x P (w fun b => Submodule.Quotient.mk (x b))

def fourierComb {n : ℕ} (x₀ : Fin n → ConjCl Dw l) (w : (Fin n → NamedCl Dw l) → Rul Xo c) : Rul Xo c :=
  fun p y => ∑ t ∈ levelIndex Dw l n, algebraMap c.F p.R (indCoeff c x₀ t) * w t p y

def StdFourier : Prop :=
  ∀ (n N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData (DeltaDatum.triv Xo c nab) (Lat.std E n) N β a P →
    (∃ w, IsTranslateFamily Xo c nab P w) ∧
    ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
      IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
        f = fun p y => algebraMap c.F p.R β⁻¹ * fourierComb Xo c x₀ w p y

def StdFourierUnit : Prop :=
  ∀ (n N : ℕ) (β : c.F), (Lat.std E n).Admissible l.M N → IsBeLat Dw c (Lat.std E n) β →
    ∃ u : (𝓞 c.F)ˣ, ∀ (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
      P ∈ harmLat Dw c a (Lat.std E n) →
      (∃ w, IsTranslateFamily Xo c nab P w) ∧
      ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
        IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
          f = fun p y => algebraMap c.F p.R ((u : 𝓞 c.F) : c.F) * fourierComb Xo c x₀ w p y

end Std

section Canonical

variable (Xo c)

end Canonical

section Basic₂

variable {Δ : DeltaDatum Xo c nab} {hK : ReflexLe Dw c} {nV : ℕ}
  {cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)}

theorem StdFourier.unit (h : StdFourier Xo c nab) : StdFourierUnit Xo c nab := by
  intro n N β hN hβ
  obtain ⟨b, hb, hs⟩ := hβ.1
  have hu : IsUnit b := by
    rw [latIdeal_std] at hs
    rw [← Ideal.span_singleton_eq_top, hs]
    simp only [reflexIdeal, Ideal.map_top]
    simp [← Ideal.one_eq_top]
  obtain ⟨u, rfl⟩ := hu
  refine ⟨u⁻¹, fun x₀ a P hP => ?_⟩
  have e : (((u⁻¹ : (𝓞 c.F)ˣ) : 𝓞 c.F) : c.F) = β⁻¹ := by
    rw [← hb]
    refine eq_inv_of_mul_eq_one_left ?_
    exact (map_mul (algebraMap (𝓞 c.F) c.F) _ _).symm.trans (by rw [Units.inv_mul, map_one])
  rw [e]
  exact h n N β x₀ a P ⟨std_mem_reps _ n 1, hN, hβ, hP⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
end
end
