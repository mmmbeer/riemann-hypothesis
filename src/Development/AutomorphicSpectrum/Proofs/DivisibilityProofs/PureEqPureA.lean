import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Inj

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

abbrev PiT (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F)) : Type :=
  R.Pi ⊗[ℂ] PiTensorProduct ℂ fun v : T => Rf.Pi v

section Model
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)

theorem std_of_cof (hM : M.IsGood ψ) {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
  (h2.and hM.std).mono fun _ h => h.1.trans h.2

theorem pure_eq_pureA (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∃ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∀ f : SInf F (Fin n × Fin d), pure f φ = pureA F f g :=
  ⟨_, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h1 (std_of_cof M ψ hM h2),
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 (std_of_cof M ψ hM h2)⟩, fun _ => rfl⟩

theorem pure_at (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) (f : SInf F (Fin n × Fin d)) (v : Pl F) :
    ∃ r : (Fin n × Fin d → AF F) → ℂ, (∀ x z, At (evFin F v) z → r (x + z) = r x) ∧
      ∀ φ₂ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ w, w ≠ v → φ₂ w = φ w) →
        pure f φ₂ = tens (evFin F v) (φ₂ v) r := by
  classical
  obtain ⟨r, hr, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (std_of_cof M ψ hM h2)
  refine ⟨r, hr, fun φ₂ h => ?_⟩
  have : φ₂ = Function.update φ v (φ₂ v) := by
    funext w
    by_cases hw : w = v
    · subst hw
      simp
    · rw [Function.update_of_ne hw, h w hw]
  rw [e (φ₂ v), ← this]
end Model

variable {B : Base F E} {Γ : Geo σ a a'} {X : Chars F E} {om : Rep σ Γ.V Γ.W} {om' : Rep σ Γ.V' Γ.W}

theorem om_schA (ht : IsTriple B Γ X om om') (p : UA σ Γ.V.J × UA σ Γ.W.J)
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} (hΦ : Φ ∈ schA F _) : om p Φ ∈ schA F _ :=
  (ht.weil.isUSplitting).pres p Φ hΦ

theorem theta_add (ht : IsTriple B Γ X om om') {Φ Ψ : (Fin a × Fin (a + a') → AF F) → ℂ} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _)
    (g : UA σ Γ.V.J) (h : UA σ Γ.W.J) : theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add]
  exact thetaSum_add F (om_schA ht _ hΦ) (om_schA ht _ hΨ)

theorem theta_smul (c : ℂ) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (g : UA σ Γ.V.J) (h : UA σ Γ.W.J) :
    theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul]
  exact thetaSum_smul F c _

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem exists_ext {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (T T₁ : Finset ι) (hT : T ⊆ T₁) (s : ∀ i, X i) :
    ∃ e : (PiTensorProduct ℂ fun v : T => X v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => X v,
      ∀ u : ∀ i, X i, (∀ i ∉ T, u i = s i) →
        e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v := by
  let ext : (∀ v : T, X v) → ∀ v : T₁, X v := fun w v => if h : (v : ι) ∈ T then w ⟨v, h⟩ else s v
  have hupd : ∀ (inst : DecidableEq T) (w : ∀ v : T, X v) (i : T) (z : X i),
      ext (@Function.update _ _ inst w i z) = Function.update (ext w) ⟨i.1, hT i.2⟩ z := by
    intro inst w i z
    funext v
    by_cases hv : v = ⟨i.1, hT i.2⟩
    · subst hv
      simp [ext]
    · rw [Function.update_of_ne hv]
      by_cases h : (v : ι) ∈ T
      · have hne : (⟨v, h⟩ : T) ≠ i := fun e => hv (Subtype.ext (show (v : ι) = i.1 by rw [← e]))
        simp only [ext, dif_pos h]
        rw [Function.update_of_ne hne]
      · simp only [ext, dif_neg h]
  let m : MultilinearMap ℂ (fun v : T => X v) (PiTensorProduct ℂ fun v : T₁ => X v) :=
    { toFun := fun w => PiTensorProduct.tprod ℂ (ext w)
      map_update_add' := fun {inst} w i x y => by
        simp only [hupd inst]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun {inst} w i c x => by
        simp only [hupd inst]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  refine ⟨PiTensorProduct.lift m, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ (ext fun v : T => u v) = _
  congr 1
  funext v
  by_cases h : (v : ι) ∈ T
  · simp [ext, h]
  · simp only [ext, dif_neg h]
    exact (hu _ h).symm

end GlobalTheory.CompanionTheory.Ar.RT.Inj

end
