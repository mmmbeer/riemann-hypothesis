import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.IdeleCovolume

namespace GlobalTheory.DiscSpec.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

theorem eq_one_of_isAbsPow {ν : HChar E} (h : ν.IsAbsPow 0) : ν = 1 :=
  GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val E ν (fun k => Units.ext (by simpa using h.2.2 k)) fun v _ => Units.ext (by simpa using h.2.1 v)

theorem eq_of_iso {π π' : CuspSub E 1} (h : π.Iso π') : π = π' := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  obtain ⟨χ', rfl⟩ := RankOne.exists_eq_twist π'
  rw [CG.ofChar_injective (Quotient.sound h)]


def toCusp {V : Submodule ℂ (Sm E 1)} (h : IsDiscrete V) : CuspSub E 1 :=
  ⟨V, fun φ hφ => ⟨h.aut φ hφ, fun r h0 h1 => by omega⟩, h.stable, h.ne_bot, h.irred⟩


theorem left_lattice {a : ℕ} {π : CuspSub E a} (h : IsNormalised π) {φ : Sm E a} (hφ : φ ∈ π.V) :
    ∀ γ ∈ latticeGL E a, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E a) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E a ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact (π.cusp φ hφ).1.left γ)
    (Subgroup.zpowers_le.2 (h φ hφ 1))
  exact this

theorem continuous_form (π : CuspSub E 1) {φ : Sm E 1} (hφ : φ ∈ π.V) : Continuous φ.1 := by
  obtain ⟨ω, h⟩ := RankOne.exists_char π
  have e : φ.1 = fun g => ((ω g : ℂˣ) : ℂ) * φ.1 1 := funext fun g => by
    have h1 : φ.1 (1 * g) = ((ω g : ℂˣ) : ℂ) * φ.1 1 := congrFun (congrArg Subtype.val (h g φ hφ)) 1
    rwa [one_mul] at h1
  rw [e]
  exact (Units.continuous_val.comp (RankOne.continuous_char π ω h)).mul continuous_const

theorem isDiscrete_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : IsDiscrete π.V := by
  refine ⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ⟨h φ hφ, ?_⟩, π.stable, π.ne_bot, π.irred⟩
  obtain ⟨-, μ, 𝓕, hμ, hF, -⟩ := isSqInt_const E 1
  refine ⟨μ, 𝓕, hμ, hF, ?_⟩
  letI : MeasurableSpace (GA E 1) := borel _
  haveI : BorelSpace (GA E 1) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E 1) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := discrete_latticeGL E
  haveI : Countable (latticeGL E 1) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  have h2 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (latticeGL E 1) K hK hcov μ hμ 𝓕 hF
    (fun g => φ.1 g ^ 2) ((continuous_form π hφ).pow 2) fun γ hγ g => by rw [left_lattice h hφ γ hγ]
  simpa only [HasFiniteIntegral, enorm_pow] using h2.2

theorem isUnitary_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  refine (CG.isUnitary_mk _).1 ((CG.isUnitary_ofChar_iff χ).2 ?_)
  have hφ : mulChi 1 χ (oneFn E 1) ∈ ((CuspSub.triv E le_rfl).twist χ).V :=
    ⟨_, Submodule.mem_span_singleton_self _, rfl⟩
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_form _ hφ).continuousOn
  have hb : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov (CG.oneByOne x)
    have h1 := hC _ hk
    rw [left_lattice h hφ γ hγ, mulChi_apply] at h1
    change ‖1 * ((χ.1 (GeneralLinearGroup.det (CG.oneByOne x)) : ℂˣ) : ℂ)‖ ≤ C at h1
    rwa [CG.det_oneByOne, one_mul] at h1
  have hle : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    have := hb (x ^ n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  intro x
  refine le_antisymm (hle x) ?_
  have := hle x⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this




end GlobalTheory.DiscSpec.Model

end
