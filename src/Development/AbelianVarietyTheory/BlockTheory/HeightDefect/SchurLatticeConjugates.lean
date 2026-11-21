import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable def ord_vw {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  multiplicity la.asIdeal I

noncomputable def conjDifferent {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : Ideal (𝓞 K) :=
  (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom σ)

theorem conjDifferent_ne_bot {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ≠ ⊥ := by
  have hinj : Function.Injective (RingOfIntegers.mapRingHom σ) := by
    intro x y h
    apply RingOfIntegers.ext
    apply σ.injective
    simpa using congrArg (fun z : 𝓞 K => (z : K)) h
  unfold conjDifferent
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  exact differentIdeal_ne_bot

theorem span_natCast_ne_bot {K : Type} [Field K] [NumberField K] (n' : ℕ+) :
    Ideal.span {((n' : ℕ) : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast n'.ne_zero

noncomputable def defectAt_vw {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  a * max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}))

noncomputable def defect_vw (E : Type) {K : Type} [Field E] [NumberField E] [Field K]
    [NumberField K] (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Finset.univ.sup fun σ : E →+* K => defectAt_vw σ n' a la

noncomputable def lrd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (rootDiscr E)

noncomputable def logNorm {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal)

theorem defectAt_vw_le {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defectAt_vw σ n' a la ≤ defect_vw E n' a la :=
  Finset.le_sup (f := fun σ : E →+* K => defectAt_vw σ n' a la) (Finset.mem_univ σ)


end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
