import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TauOneCharacter

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.DepthZeroTypeModel
open GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem v_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {k : ℚ_[g]} (hk : ‖k‖ < 1) :
    Valued.v (i k) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (i k) ^ n) Filter.atTop (nhds 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hk)
    simpa [Function.comp_def] using this
  have h2 : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) := by
    have : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      simpa using Valued.isOpen_ball (w.adicCompletion E) 1
    exact this.mem_nhds (by simp)
  obtain ⟨n, hn⟩ := (h1.eventually h2).exists
  simp only [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

end GlobalTheory.Published.DepthZeroTypeModel
