import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ω χ : HChar E}
  {V : Submodule ℂ (Sm E a)}

structure IsDiscreteWith (ω : HChar E) (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  central : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ
  sqInt : ∀ φ ∈ V, IsSqInt fun g => ((‖φ.1 g‖ : ℝ) : ℂ)
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

variable (a) in

def detLine (χ : HChar E) : Submodule ℂ (Sm E a) := Submodule.span ℂ {mulChi a χ (oneFn E a)}

theorem mem_detLine {φ : Sm E a} :
    φ ∈ detLine a χ ↔ ∃ c : ℂ, ∀ g, φ.1 g = c * (χ.1 (GeneralLinearGroup.det g) : ℂˣ) :=
  Submodule.mem_span_singleton.trans <| exists_congr fun c =>
    ⟨fun e g => e ▸ congrArg (c * ·) (one_mul _),
      fun e => Subtype.ext (funext fun g => ((e g).trans (congrArg (c * ·) (one_mul _).symm)).symm)⟩


theorem chiDet_scalar (χ : HChar E) (z : Neutral.B1.Ideles E) :
    chiDet a χ (GeneralLinearGroup.scalar (Fin a) z) = (χ ^ a).1 z := by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin a) z) = z ^ a := Units.ext (by
    change (Matrix.scalar (Fin a) (z : Ad E)).det = _
    simp)
  exact (congrArg χ.1 this).trans ((map_pow _ _ _).trans (MonoidHom.pow_apply χ.1 a z).symm)

abbrev expId (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (t : ℝ) : Neutral.B1.Ideles E :=
  infId E (expU fun _ : InfinitePlace E => (t : ℂ))


theorem IsDiscreteWith.apply (h : IsDiscreteWith ω V) {φ : Sm E a} (hφ : φ ∈ V) (z : Neutral.B1.Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  rw [CuspRep.scalar_comm]
  exact congrFun (congrArg Subtype.val (h.central z φ hφ)) g

theorem IsDiscreteWith.unique {ω' : HChar E} (h : IsDiscreteWith ω V) (h' : IsDiscreteWith ω' V) : ω = ω' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 h.ne_bot
  exact Subtype.ext (MonoidHom.ext fun z =>
    Units.ext (smul_left_injective ℂ h0 ((h.central z φ hφ).symm.trans (h'.central z φ hφ))))

theorem enorm_ofReal_norm (z : ℂ) : ‖((‖z‖ : ℝ) : ℂ)‖ₑ = ‖z‖ₑ := by simp [enorm]

theorem IsDiscreteWith.isDiscrete (h : IsDiscreteWith ω V) (hω : ∀ t, ω.1 (expId E t) = 1) : IsDiscrete V :=
  ⟨h.aut, fun φ hφ => ⟨fun t g => by rw [splitCentre_eq_scalar, h.apply hφ, hω, Units.val_one, one_mul], by
    simpa only [enorm_ofReal_norm] using (h.sqInt φ hφ).2⟩, h.stable, h.ne_bot, h.irred⟩

theorem isDiscreteWith_of_isDiscrete (h : IsDiscrete V) (hc : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ) : IsDiscreteWith ω V :=
  ⟨h.aut, hc, fun φ hφ => ⟨fun t g => by simp only [(h.sqInt φ hφ).1 t g], by
    simpa only [enorm_ofReal_norm] using (h.sqInt φ hφ).2⟩, h.stable, h.ne_bot, h.irred⟩

theorem isSqInt_of_bounded {f : GA E a → ℂ} (h : ∀ t g, f (splitCentre E a t * g) = f g) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) : IsSqInt f := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) (Measure.haar : Measure (GA E a))
  have hf := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a Measure.haar
  refine ⟨h, Measure.haar, _, inferInstance, hd, ?_⟩
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal C ^ 2) fun g => ?_).trans_lt ?_
  · exact pow_le_pow_left' ((ofReal_norm_eq_enorm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC g))) 2
  · rw [setLIntegral_const, ← quotMeasure_univ hd]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

theorem IsDiscreteWith.twist (h : IsDiscreteWith ω V) {ν : HChar E} (hν : ν.IsUnitary) :
    IsDiscreteWith (ω * ν ^ a) (V.map (mulChi a ν).toLinearMap) where
  aut := by rintro _ ⟨φ, hφ, rfl⟩; exact (h.aut φ hφ).mulChi ν
  central := by
    rintro z _ ⟨φ, hφ, rfl⟩
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * _) * (chiDet a ν (g * _) : ℂ) = ((ω.1 z * (ν ^ a).1 z : ℂˣ) : ℂ) * (φ.1 g * (chiDet a ν g : ℂ))
    rw [← CuspRep.scalar_comm, h.apply hφ, map_mul, chiDet_scalar, Units.val_mul, Units.val_mul]
    ring
  sqInt := by
    rintro _ ⟨φ, hφ, rfl⟩
    convert h.sqInt φ hφ using 3 with g
    change ‖φ.1 g * (ν.1 _ : ℂ)‖ = _
    rw [norm_mul, hν, mul_one]
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (h.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi ν o φ).symm⟩
  ne_bot e := h.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a ν)).1 e)
  irred W hW hs := by
    have h := h.irred (W.comap (mulChi a ν).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a ν).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a ν).toLinearMap := (act_mulChi ν o φ) ▸ hs o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul ν o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a ν).toLinearMap) (mulChi a ν).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isDiscreteWith_detLine (hχ : χ.IsUnitary) : IsDiscreteWith (χ ^ a) (detLine a χ) := by
  have h1 : IsDiscreteWith 1 (Submodule.span ℂ {oneFn E a}) :=
    isDiscreteWith_of_isDiscrete ⟨fun _ => isAutForm_const, fun φ hφ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        exact isSqInt_of_bounded (f := fun _ => c * 1) (fun _ _ => rfl) fun _ => le_rfl,
      isStable_const, fun e => oneFn_ne_zero (Submodule.span_singleton_eq_bot.1 e),
      fun W hW _ => (nonzero_span_atom _ oneFn_ne_zero).le_iff.1 hW⟩ fun z φ hφ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        exact (one_smul ℂ _).symm
  have h2 := h1.twist hχ
  rwa [one_mul, Submodule.map_span, Set.image_singleton] at h2


theorem detLine_ne_cusp (ha : 1 < a) (χ : HChar E) (π : CuspSub E a) : detLine a χ ≠ π.V := fun e => by
  have h := (π.cusp _ (e.le (Submodule.mem_span_singleton_self _))).mulChi χ⁻¹
  rw [← mulChi_mul, mul_inv_cancel, mulChi_one] at h
  exact GlobalTheory.ConstNotCusp.not_isCuspidal_oneFn E a ha h.2

section Local

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


end GlobalTheory.DiscChar

namespace GlobalTheory.Published

open GlobalTheory.DiscChar

def DiscreteSpectrumGLTwo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ω : HChar E), ω.IsUnitary →
    ∀ V : Submodule ℂ (Sm E 2), IsDiscreteWith ω V ↔
      (∃ π : CuspSub E 2, π.HasCentral ω ∧ V = π.V) ∨ ∃ χ : HChar E, χ ^ 2 = ω ∧ V = detLine 2 χ

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]




theorem DiscreteSpectrumGLTwo.exists_char (H : DiscreteSpectrumGLTwo) {ω : HChar E} (hω : ω.IsUnitary)
    {V : Submodule ℂ (Sm E 2)} (hV : IsDiscreteWith ω V) {φ : Sm E 2} (hφ : φ ∈ V) (hc : ¬ IsCuspidal φ.1) :
    ∃ χ : HChar E, χ ^ 2 = ω ∧ χ.IsUnitary ∧ ∀ ψ ∈ V, ∃ c : ℂ, ∀ g, ψ.1 g = c * (χ.1 (GeneralLinearGroup.det g) : ℂˣ) := by
  obtain ⟨π, -, rfl⟩ | ⟨χ, rfl, rfl⟩ := (H E ω hω V).1 hV
  · exact absurd (π.cusp φ hφ).2 hc
  · exact ⟨χ, rfl, isUnitary_of_pow two_ne_zero hω, fun _ => mem_detLine.1⟩

example : IsDiscreteWith (1 ^ 2) (detLine 2 (1 : HChar E)) ∧ ∀ π : CuspSub E 2, detLine 2 (1 : HChar E) ≠ π.V :=
  ⟨isDiscreteWith_detLine isUnitary_one, detLine_ne_cusp one_lt_two 1⟩

end GlobalTheory.Published

end
