import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LbcOfCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardPrimesOverThreeZ
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSmallStable

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ArthurClozelLocalSC : Prop := LocalBC lbc

end GlobalTheory.Published

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.FunExt
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.LocalSCModel

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)}

omit [NumberField K] [NumberField L] in

theorem liesOver (h : CycAt v u) : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h.2.2.1]; rfl⟩

theorem stab (h : CycAt v u) (σ : L ≃ₐ[K] L) : σ • u.asIdeal = u.asIdeal := by
  have := liesOver h
  have hp : (σ • u.asIdeal).IsPrime := u.isPrime.smul σ
  have hl : (σ • u.asIdeal).LiesOver v.asIdeal := inferInstance
  have hne : σ • u.asIdeal ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  have := h.2.2.2 ⟨_, hp, hne⟩ (HeightOneSpectrum.ext hl.over.symm)
  exact congrArg HeightOneSpectrum.asIdeal this

theorem local_cyclic (h : CycAt v u) (f : v.adicCompletion K →+* u.adicCompletion L) (hf : Continuous f)
    (hK : ∀ z : K, f (algebraMap K _ z) = algebraMap L _ (algebraMap K L z)) :
    letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
    IsGalois (v.adicCompletion K) (u.adicCompletion L) ∧
      Module.finrank (v.adicCompletion K) (u.adicCompletion L) = Module.finrank K L := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
  have := liesOver h
  have := h.1
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion L) :=
    ⟨(hf.comp continuous_fst).mul continuous_snd⟩
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun z => by
      rw [IsScalarTower.algebraMap_apply K L (u.adicCompletion L)]; exact (hK z).symm
  have htop : MulAction.stabilizer (L ≃ₐ[K] L) u.asIdeal = ⊤ := by
    ext σ; simpa using stab h σ
  refine ⟨GroundTheory.Global.isGalois_adicCompletion v u, ?_⟩
  rw [GroundTheory.Global.finrank_adicCompletion v u, ← GroundTheory.Global.card_decompositionGroup v u, htop,
      Subgroup.card_top, IsGalois.card_aut_eq_finrank]


theorem lbc_ofChar (h : CycAt v u) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ∃ (N : (u.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ) (hN : IsSmoothChar (χ.comp N)),
      lbc K L v u (IrrGL.ofChar χ hχ) (IrrGL.ofChar (χ.comp N) hN) := by
  have := liesOver h
  let f := GroundTheory.Global.adicCompletionMap v u
  have hf : Continuous f := GroundTheory.Global.continuous_adicCompletionMap v u
  have hK := GroundTheory.Global.adicCompletionMap_algebraMap v u
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := f.toAlgebra
  obtain ⟨hG, hd⟩ := local_cyclic h f hf hK
  have hp := h.2.1.one_lt
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion L) := Module.finite_of_finrank_pos (by omega)
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K L v u f hf hfd).2
  have hN : IsSmoothChar (χ.comp (Units.map (Algebra.norm (v.adicCompletion K) : u.adicCompletion L →* v.adicCompletion K))) := by
    unfold IsSmoothChar at hχ ⊢
    rw [← MonoidHom.comap_ker]
    exact hχ.preimage (Continuous.units_map _ hc)
  refine ⟨_, hN, f, hf, hK, fun s hs => ⟨1, _, _, rfl, rfl, ?_⟩⟩
  have : Fact (Module.finrank K L).Prime := ⟨h.2.1⟩
  exact GlobalTheory.LBC.Model.isLBC_det (fun t => mem_zpowers_of_prime_card (p := Module.finrank K L)
    (by rw [IsGalois.card_aut_eq_finrank, hd]) hs) 1 hχ hN

end GlobalTheory.Published.LocalSCModel

end
end
