import Formalism.LocalToGlobal.IndefiniteReal.SEEofApply
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

section Halves

variable (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
  (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
  (c : ℝ) (v₀ : M.Vec)

end Halves

open Classical in

def sEEofT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
    (c : ℝ) : E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  if h : EvalTie M μ 𝓕 E X G ι c then sEEof h else 0

end Formalism.IndefR.AutomorphicEvaluation

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open Formalism.L2.Theta

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem countable_GQ (V : HSp D) : Countable (GQ V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem borel_GA (V : HSp D) : BorelSpace (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem petPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) : PetPos V μ 𝓕 := by
  intro F hc hinv hne hint
  have := countable_GQ V
  have := measurableMul_GA V
  have := borel_GA V
  have := hH
  set U : Set (GA D V) := {g | F g ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUne : U.Nonempty := by
    by_contra h
    apply hne
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  have hUpos : 0 < μ U := hUo.measure_pos μ hUne
  have hnn : 0 ≤ᵐ[μ.restrict 𝓕] fun g => ‖F g‖ ^ 2 := ae_of_all _ (fun g => by positivity)
  refine lt_of_le_of_ne (integral_nonneg fun g => by positivity) ?_
  intro h0
  have hz : (fun g => ‖F g‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have hset : {g : GA D V | ¬ (‖F g‖ ^ 2 = (0 : GA D V → ℝ) g)} = U := by
    ext g
    simp [hUdef]
  have hFU : μ (U ∩ 𝓕) = 0 := by
    have h1 := ae_iff.1 hz
    rw [hset, Measure.restrict_apply hUo.measurableSet] at h1
    exact h1
  have key : U ≤ᵐ[μ] (⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) : Set (GA D V)) := by
    filter_upwards [hF.ae_covers] with x hx hxU
    obtain ⟨γ, hγ⟩ := hx
    refine Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩
    · show F ((γ : GA D V) * x) ≠ 0
      rw [hinv _ γ.2 x]
      exact hxU
    · exact hγ
  have hU0 : μ U = 0 := by
    refine le_antisymm ((measure_mono_ae key).trans ?_) bot_le
    refine (measure_iUnion_le _).trans ?_
    simp only [measure_preimage_mul, hFU, tsum_zero, le_refl]
  exact hUpos.ne' hU0

end Formalism.IndefR.PeterssonHilbertSpace

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

section Pieces

variable (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
  (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
  (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec)

def SquareIntegrableTransfer : Prop :=
  ∀ F : GA D (D.sp.Y 0) → ℂ, Continuous F → (∀ γ ∈ GQ (D.sp.Y 0), ∀ x, F (γ * x) = F x) →
    MemLp F 2 (μ.restrict 𝓕) →
      MemLp (fun x => F (ι.symm x * t)) 2 (muX X) ∧
        ∫ x, ‖F (ι.symm x * t)‖ ^ 2 ∂(muX X) = c * ∫ x in 𝓕, ‖F x‖ ^ 2 ∂μ

def RphFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    X.Rph (star (hF.toLp _)) = star (hF.toLp _)

def ReFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    X.B.Re (star (hF.toLp _)) = star (hF.toLp _)

def RgFix : Prop :=
  ∀ T ∈ E, ∀ hF : MemLp (fun x => ev M v₀ T (ι.symm x * t)) 2 (muX X),
    G.Rg (star (hF.toLp _)) = star (hF.toLp _)

def EvalIntoT : Prop :=
  ∀ T ∈ E, ∃ F : EEC X G, ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)) ∧
    ‖(F : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 T T).re

def EvalOntoT : Prop :=
  ∀ F : EEC X G, ∃ T ∈ E, (F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x * t)

def EvalInjT : Prop :=
  ∀ T ∈ E, ((fun x => ev M v₀ T (ι.symm x * t)) =ᵐ[muX X] 0) → T = 0

end Pieces

theorem evalTieT_of (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
    (t : GA D (D.sp.Y 0)) (c : ℝ) (v₀ : M.Vec) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1)
    (hI : EvalIntoT M μ 𝓕 E X G ι t c v₀) (hO : EvalOntoT M E X G ι t v₀) (hJ : EvalInjT M E X ι t v₀) :
    EvalTieT M μ 𝓕 E X G ι t c := by
  classical
  choose Φ hΦ using fun T : E => hI T T.2
  have key : ∀ (T : E) (F : EEC X G), ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) →
      Φ T = F := by
    intro T F hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ T).1.trans hF.symm
  let L : E →ₗ[ℂ] EEC X G :=
    { toFun := Φ
      map_add' := fun T T' => by
        apply key
        have h1 := (hΦ T).1
        have h2 := (hΦ T').1
        have h3 := Lp.coeFn_add ((Φ T : EEC X G) : L2X X) ((Φ T' : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a T => by
        rw [RingHom.id_apply]
        apply key
        have h1 := (hΦ T).1
        have h3 := Lp.coeFn_smul a ((Φ T : EEC X G) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hinj : Function.Injective L := by
    intro T T' h
    have hd : L (T - T') = 0 := by rw [map_sub, h, sub_self]
    have h1 := (hΦ (T - T')).1
    have h0 : ((fun x => ev M v₀ ((T - T' : E) : MMap M) (ι.symm x * t)) =ᵐ[muX X] 0) := by
      have hz : ((Φ (T - T') : EEC X G) : L2X X) = 0 := by
        have : Φ (T - T') = 0 := hd
        rw [this]; rfl
      have := Lp.coeFn_zero ℂ 2 (muX X)
      rw [← hz] at this
      exact h1.symm.trans this
    have := hJ ((T - T' : E) : MMap M) (T - T').2 h0
    exact sub_eq_zero.mp (Subtype.ext this)
  have hsurj : Function.Surjective L := by
    intro F
    obtain ⟨T, hT, hF⟩ := hO F
    exact ⟨⟨T, hT⟩, key ⟨T, hT⟩ F hF⟩
  exact ⟨v₀, hv, LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun T => hΦ T⟩

section Assembly

variable {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
  {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA}
  {t : GA D (D.sp.Y 0)} {c : ℝ} {v₀ : M.Vec}

theorem norm_sq_toLp {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

theorem re_ipM_eq {T : MMap M} (hT : ∃ c', IsMultIP M μ 𝓕 T T c') (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    (ipM M μ 𝓕 T T).re = ∫ x in 𝓕, ‖T v₀ x‖ ^ 2 ∂μ := by
  unfold ipM
  rw [dif_pos hT]
  obtain ⟨-, heq⟩ := hT.choose_spec v₀ v₀
  have hprod : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  rw [hprod, mul_one] at heq
  rw [← heq]
  have hpt : ∀ g, star (T v₀ g) * T v₀ g = ((‖T v₀ g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  simp



end Assembly

end Formalism.IndefR.AutomorphicEvaluation

end
end
