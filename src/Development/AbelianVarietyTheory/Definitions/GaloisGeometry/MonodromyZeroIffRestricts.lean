import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsLAdicCharOfUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsLocCompTrivIff

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL.Model

section Tower

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}



theorem ineTriv_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) :
    IneTriv (WD.mk a) ↔ ∀ τ : Ine (F := K) A, a.ρ (ineIncl h τ) = 1 := by
  refine forall_congr' fun τ => ?_
  rw [WD.charPol_mk, WD.lpDim_mk]
  refine ⟨fun e => ?_, fun e => by rw [e, LinearMap.charpoly_one]⟩
  have h1 := LinearMap.aeval_self_charpoly (a.ρ (ineIncl h τ))
  rw [e, map_pow, map_sub, Polynomial.aeval_X, map_one] at h1
  have h2 : Module.End.IsSemisimple (a.ρ (ineIncl h τ) - 1) := by
    have := (Module.End.isSemisimple_sub_algebraMap_iff (f := a.ρ (ineIncl h τ)) (μ := (1 : ℂ))).2 (a.semisimple _)
    simpa using this
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ h2)

theorem unr_iff (x : WD h) : x.unr ↔ x.mono0 ∧ IneTriv x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.unr_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, ineTriv_mk]; rfl



variable [Algebra K L] [IsScalarTower K L Ω]

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in

theorem continuous_restr : Continuous (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis K M
  have hint : ∀ i, IsIntegral L ((b i : M) : Ω) := fun i =>
    ((IsIntegral.of_finite K (b i)).map (IsScalarTower.toAlgHom K M Ω)).tower_top
  have hN : ⋂ i, ((IntermediateField.adjoin L {((b i : M) : Ω)}).fixingSubgroup : Set (Ω ≃ₐ[L] Ω))
      ∈ nhds (1 : Ω ≃ₐ[L] Ω) := Filter.iInter_mem.mpr fun i => by
    haveI := IntermediateField.adjoin.finiteDimensional (hint i)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hN ?_
  intro σ hσ
  apply hMs
  simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, σ ((b i : M) : Ω) = ((b i : M) : Ω) := fun i =>
    hσ i _ (IntermediateField.mem_adjoin_simple_self L _)
  obtain ⟨y, rfl⟩ : ∃ y : M, (y : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr y]
  change (AlgEquiv.restrictScalars K σ) _ = _
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgEquiv.restrictScalars_apply, hb]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
include h h' in

theorem normV_pow : normV v' = normV v ^ v'.asIdeal.inertiaDeg (𝓞 K) := by
  have e : v = v'.under (𝓞 K) := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [← h x]
    change _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ v'.asIdeal
    rw [← h', IsScalarTower.algebraMap_apply K L Ω]
    rfl)
  subst e
  have : v'.asIdeal.LiesOver (v'.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := v'.isMaximal
  have := (v'.under (𝓞 K)).isMaximal
  show Ideal.absNorm v'.asIdeal = Ideal.absNorm (v'.under (𝓞 K)).asIdeal ^ v'.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) v'.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal (v'.under (𝓞 K)).asIdeal, map_pow]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
include h h' in

theorem actsAs_restr {σ : G L Ω} {a b : ℕ} (H : ActsAs A (normV v') σ a b) :
    ActsAs A (normV v) (σ.restrictScalars K : G K Ω) (v'.asIdeal.inertiaDeg (𝓞 K) * a) (v'.asIdeal.inertiaDeg (𝓞 K) * b) := by
  refine ⟨H.1, fun x hx => ?_⟩
  rw [pow_mul, pow_mul, ← normV_pow (h := h) (h' := h')]
  exact H.2 x hx

variable (h h') in

def weilRes : Weil h' →* Weil h :=
  ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω).comp (Weil h').subtype).codRestrict _ fun σ =>
    let ⟨_, _, H⟩ := σ.2; ⟨_, _, actsAs_restr (h := h) (h' := h') H⟩

theorem deg_weilRes (σ : Weil h') : deg (weilRes h h' σ) = v'.asIdeal.inertiaDeg (𝓞 K) * deg σ := by
  obtain ⟨a, b, H⟩ := σ.2
  rw [deg_eq H, deg_eq (σ := weilRes h h' σ) (actsAs_restr (h := h) (h' := h') H)]
  push_cast; ring

variable (h') in

def repRes {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp (weilRes h h')
  N := a.N
  smooth := by
    let i : Ine (F := L) A → Ine (F := K) A := fun τ => ⟨AlgEquiv.restrictScalarsHom K τ.1, τ.2⟩
    have hi : Continuous i := (continuous_restr.comp continuous_subtype_val).subtype_mk _
    exact a.smooth.preimage hi
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have := a.comm (weilRes h h' σ)
    rw [deg_weilRes, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_pow (h := h) (h' := h')] at this
    exact this

theorem restricts_mk_iff {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (x' : WD h') :
    Restricts (WD.mk a) x' ↔ x' = WD.mk (repRes h' a) := by
  constructor
  · rintro ⟨n, a₁, b, h1, rfl, h3, h4⟩
    obtain ⟨e, e1, e2⟩ := WD.mk_eq_mk.1 h1
    refine WD.sound ⟨e, fun σ u => ?_, fun u => ?_⟩
    · rw [h4 (weilRes h h' σ) σ fun _ => rfl]; exact e1 _ u
    · rw [h3]; exact e2 u
  · rintro rfl
    let e := (Module.finBasis ℂ V).equivFun
    refine ⟨_, a.transport e, (repRes h' a).transport e, WD.sound (a.iso_transport e).symm,
      WD.sound ((repRes h' a).iso_transport e).symm, rfl, fun σ σ' hσ => ?_⟩
    rw [show σ = weilRes h h' σ' from Subtype.ext (AlgEquiv.ext hσ)]
    rfl

variable (h') in

theorem existsUnique_restricts (x : WD h) : ∃! x' : WD h', Restricts x x' := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  simp only [restricts_mk_iff]
  exact existsUnique_eq



end Tower


section Aut

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}






end Aut

end GlobalTheory.AboveL.Model

end
