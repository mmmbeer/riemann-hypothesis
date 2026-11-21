import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HookProductDictionary

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hookProduct (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range (a i), ((a i - j) + ((Finset.Ioo i n).filter fun l => j < a l).card)


example : hookProduct 2 (fun i => if i = 0 then 2 else 1) = 3 := by decide

example : hookProduct 2 (fun _ => 2) = 12 := by decide

def mainTerm (D : D7) (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log
    ((hookProduct ((Wc D i).sig (tauE D ρ)).1 (aPl D i ((Wc D i).sig (tauE D ρ)).1 ρ) *
      hookProduct ((Wc D i).sig (tauE D ρ)).2 (aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 ρ) : ℕ) : ℝ)

def Sizes (D : D7) (b : ℝ) : Prop :=
  1 ≤ b ∧ (∀ i, ((D.R.k : ℝ) * b) ^ 8 ≤ D.host.g i) ∧ ∀ ρ : D.what₂.Tau,
    (∀ j, 0 < (D.hc ρ).e j ∧ (((D.hc ρ).e j : ℚ) : ℝ) ≤ 2 * b) ∧
    (∀ l, 0 ≤ (D.hc ρ).v l ∧ (((D.hc ρ).v l : ℚ) : ℝ) ≤ b) ∧
    ∀ l j, |(((D.hc ρ).b l - (D.hc ρ).e j : ℚ) : ℝ)| ≤ b

theorem finite_levelPlaces (D : D7) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have h1 : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h0
  refine (Ideal.finite_factors h1).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

def levelPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (finite_levelPlaces D).toFinset

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def adelicPart (c : EigSys D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv))
      (levelPlaces D) c).comap (R.HW i (sg0 D A)).e

def IsAdelicScalar (c : EigSys D) (l : ℝ) : Prop :=
  adelicPart R i c ≠ ⊥ ∧ ∀ x ∈ adelicPart R i c, R.thG i A.μ0 (LinearMap.adjoint (R.thG i A.μ0) x) = (l : ℂ) • x

end Adelic

section Geo

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

abbrev Sec : Type := FDSec (C.U ((i : ℕ) + 1) O.s0).X

def dl : Sec O →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) • adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc)

def pet (P : LevelP R.Pg D.R.r ℂ) (s s' : Sec O) : ℂ :=
  ((Nat.card P.H : ℕ) : ℂ)⁻¹ * (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
    ∫ g in R.fdW i, dl O κ cc s g * star (dl O κ cc s' g) ∂(R.νW i)

def IsReps (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
    ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

end Geo

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit fun _ => A.μ0)

theorem IsAdelicScalar.unique {i : Fin D.R.m} {c : EigSys D} {l l' : ℝ} (h : IsAdelicScalar R i c l)
    (h' : IsAdelicScalar R i c l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.1
  have h2 : (l : ℂ) • x = (l' : ℂ) • x := (h.2 x hx).symm.trans (h'.2 x hx)
  exact Complex.ofReal_injective (smul_left_injective ℂ hx0 h2)

end Main

end GlobalTheory.IndefiniteRowSideFullHecke.HookProductDictionary
