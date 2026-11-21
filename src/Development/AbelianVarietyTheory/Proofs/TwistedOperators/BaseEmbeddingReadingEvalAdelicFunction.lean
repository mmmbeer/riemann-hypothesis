import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionThirdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

section Lin

open Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

theorem baseChange_mem {K K' M : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup M] [Module K M]
    (φ : M →ₗ[K] M) (V : Submodule K M) (h : ∀ x ∈ V, φ x ∈ V) : ∀ x ∈ V.baseChange K', φ.baseChange K' x ∈ V.baseChange K' := by
  intro x hx
  rw [Submodule.baseChange_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ v, h v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem span_mem {K' M : Type} [Field K'] [AddCommGroup M] [Module K' M] (O : ValuationSubring K')
    (φ : M →ₗ[K'] M) (S : Set M) (h : ∀ x ∈ S, φ x ∈ S) : ∀ x ∈ Submodule.span O S, φ x ∈ Submodule.span O S := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : φ (a • x) = a • φ x := φ.map_smul (a : K') x
    rw [this]; exact Submodule.smul_mem _ _ hx

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

theorem keeps_of (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK)
    (hs : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1)
    (hr : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL) : Keeps Φ la hL hW := by
  have he : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL := fun eC => by
    ext x
    simp only [FormsL.eOp, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun g _ => congrArg _ (LinearMap.congr_fun (hr g) x)
  have ht : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam := fun J lam x hx p => by
    have h1 : Φ.ρ p (hL x) = hL (Φ.ρ p x) := (LinearMap.congr_fun (hr p) x).symm
    rw [h1, hx p, map_smul]
  have hg : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC := by
    rintro eC _ ⟨x, rfl⟩
    exact ⟨hL x, (LinearMap.congr_fun (he eC) x).symm⟩
  have hw : ∀ (J : Subgroup G) (lam : J →* LLˣ) (eC : G → LL), ∀ x ∈ Φ.Wgood J lam eC, hL x ∈ Φ.Wgood J lam eC :=
    fun J lam eC x hx => ⟨ht J lam x hx.1, hg eC x hx.2⟩
  refine ⟨hs, hr, he, ht, hg, fun K' _ _ O _ => ?_, fun K' _ _ _ _ O _ => ?_⟩
  · have h1 : ∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O := by
      refine span_mem O _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨hL f, hW f f.2⟩, hs f hf, rfl⟩
    have h2 : ∀ V : Submodule LL WL, (∀ x ∈ V, hL x ∈ V) →
        ∀ x ∈ latKIn Φ la O V, (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O V := fun V hV x hx =>
      ⟨h1 x hx.1, baseChange_mem (resW Φ hL hW) _ (fun y hy => hV _ hy) x hx.2⟩
    exact ⟨h1, fun J lam => ⟨h2 _ (ht J lam), fun eC => h2 _ (hw J lam eC)⟩⟩
  · have h1 : ∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O := by
      refine span_mem O _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨hL f, hW f f.2⟩, hs f hf, rfl⟩
    have h2 : ∀ V : Submodule LL WL, (∀ x ∈ V, hL x ∈ V) →
        ∀ x ∈ latLIn Φ la O V, hL.baseChange K' x ∈ latLIn Φ la O V := fun V hV x hx =>
      ⟨h1 x hx.1, baseChange_mem hL _ hV x hx.2⟩
    exact ⟨h1, fun J lam => ⟨h2 _ (ht J lam), fun eC => h2 _ (hw J lam eC)⟩⟩

end Lin

section Grp

open Formalism.IndefR.Bridge GlobalTheory.HeckeModel

theorem exists_local_isDC {G : Type} [Group G] {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC J x A) : ∃ A₀, IsDC K x A₀ := by
  classical
  have hex : ∀ a : G, ∃ b : G, a ∈ A → (∃ k ∈ K, b = k * x) ∧ b⁻¹ * a ∈ J := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
      refine ⟨a₁ * x, fun _ => ⟨⟨a₁, ha₁, rfl⟩, ?_⟩⟩
      have : (a₁ * x)⁻¹ * ((k₁ : G) * x * k₂) = b₁ * k₂ := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem hb₁ k₂.2
    · exact ⟨1, fun h => absurd h ha⟩
  choose f hf using hex
  refine ⟨A.image f, fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, hk, e⟩ := (hf a ha).1
    exact ⟨⟨k, hk⟩, 1, by simp [e]⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, hag⟩, hu⟩ := hA.2 ((k₁ : G) * x * k₂) ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
    refine ⟨f a, ⟨Finset.mem_image_of_mem f ha, ?_⟩, ?_⟩
    · obtain ⟨k, hk, e⟩ := (hf a ha).1
      refine (hs.mem _ ?_).1 ?_
      · rw [e]
        exact L.mul_mem (L.inv_mem (L.mul_mem (hs.le hk) hx)) (L.mul_mem (L.mul_mem (hs.le k₁.2) hx) (hs.le k₂.2))
      · have := J.mul_mem (hf a ha).2 hag
        simpa [mul_assoc] using this
    · rintro b ⟨hb, hbg⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hb
      rw [hu a' ⟨ha', ?_⟩]
      have := J.mul_mem (J.inv_mem (hf a' ha').2) (hs.le' hbg)
      simpa [mul_assoc] using this

end Grp

section Geo

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem nval_nonneg_of_int {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] (e : ℕ) (a : V) : 0 ≤ nval V e (algebraMap V K' a) := by
  by_cases h0 : algebraMap V K' a = 0
  · rw [h0, nval_zero]; exact le_top
  rw [nval_of_ne h0]
  have hne : valV V (algebraMap V K' a) ≠ 0 := valV_ne_zero h0
  have hle : valV V (algebraMap V K' a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
  have hlog : WithZero.log (valV V (algebraMap V K' a)) ≤ 0 := by
    have := (WithZero.log_le_log hne one_ne_zero).2 hle
    simpa using this
  have hv : (0 : ℝ) ≤ (vV V (algebraMap V K' a) : ℝ) := by
    have : (0 : ℤ) ≤ vV V (algebraMap V K' a) := by simp only [vV]; omega
    exact_mod_cast this
  exact EReal.coe_nonneg.2 (div_nonneg hv (Nat.cast_nonneg e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transform_integral (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeValueInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c))
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {P : Ideal (𝓞 E)} {p i : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p) (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i)
    {la : HeightOneSpectrum (𝓞 c.F)} (hp : (p : 𝓞 c.F) ∉ la.asIdeal) {s : c.F} (hs : la.valuation c.F s ≤ 1)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c a n) (hg : g ∈ sec Xo c a n)
    (hr : HkRel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) s f g)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v g := by
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  show 0 ≤ nval T.V e (evI y g)
  letI := io.toAlgebra
  let Ω := AlgebraicClosure T.Fr
  letI : Algebra c.F Ω := ((algebraMap T.Fr Ω).comp io).toAlgebra
  let k : T.Fr →ₐ[c.F] Ω := ⟨algebraMap T.Fr Ω, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ k y.1
  have e1 : evR Xo c g z = k (evI y g) := evR_frMap hWD g hg.1 k y.1 y.2.1 z hz
  have e2 := hr Ω z
  haveI := hF Ω z
  set x := hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) f z with hx
  have halg : (letI := k.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr Ω) := by
    have hA : k.toRingHom.toAlgebra = (inferInstance : Algebra T.Fr Ω) := Algebra.algebra_ext _ _ fun _ => rfl
    rw [hA]
    exact AlgebraicClosure.isAlgebraic T.Fr
  have hint : IsIntegral T.V x := by
    rw [hx, hkVal]
    refine finsum_induction (IsIntegral T.V) isIntegral_zero (fun _ _ => IsIntegral.add) fun C => ?_
    unfold hkTerm
    split_ifs with h
    · exact (hI la P p i hP hp T io e ho y hy trivial Ω k halg z hz C _ h.choose_spec).2
        a n f hf h0
    · exact isIntegral_zero
  by_cases hs0 : s = 0
  · have : evI y g = 0 := by
      apply k.toRingHom.injective
      show k _ = k _
      rw [← e1, map_zero]
      refine e2.trans ?_
      rw [hs0, map_zero, zero_mul]
    rw [this, nval_zero]; exact le_top
  have e3 : algebraMap T.Fr Ω ((io s)⁻¹ * evI y g) = x := by
    rw [map_mul, map_inv₀]
    show (algebraMap c.F Ω s)⁻¹ * k _ = x
    rw [← e1]
    have : evR Xo c g z = algebraMap c.F Ω s * x := e2
    rw [this, inv_mul_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [← e3, isIntegral_algebraMap_iff (algebraMap T.Fr Ω).injective] at hint
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have e4 : evI y g = io s * algebraMap T.V T.Fr w := by
    rw [hw, mul_inv_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [e4, nval_smul ho hs0]
  refine add_nonneg ?_ (nval_nonneg_of_int e w)
  have h5 := (WithZero.log_le_log ((la.valuation c.F).ne_zero_iff.2 hs0) one_ne_zero).2 hs
  rw [WithZero.log_one] at h5
  have : (0 : ℤ) ≤ vLa la s := by unfold vLa; omega
  exact_mod_cast this

end Geo

end GlobalTheory.HeckeSup
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {Γ G : Type} [Group Γ] [Group G] (L : G → Γ → Prop) (u : Γ → ℂ)

def liftSub : Submodule ℂ (Γ → ℂ) where
  carrier := {Φ | (∀ g k, L g k → ∀ h, u (h * k) * Φ (h * k) = u h * Φ (h * k)) ∧
    ∀ g k k', L g k → L g k' → ∀ h, Φ (h * k) = Φ (h * k')}
  add_mem' := by
    rintro Φ Ψ ⟨a1, a2⟩ ⟨b1, b2⟩
    refine ⟨fun g k hk h => ?_, fun g k k' hk hk' h => ?_⟩
    · simp only [Pi.add_apply, mul_add, a1 g k hk h, b1 g k hk h]
    · simp only [Pi.add_apply, a2 g k k' hk hk' h, b2 g k k' hk hk' h]
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c Φ ⟨a1, a2⟩
    refine ⟨fun g k hk h => ?_, fun g k k' hk hk' h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, a1 g k hk h, mul_left_comm]
    · simp only [Pi.smul_apply, a2 g k k' hk hk' h]

def shiftSub (c : ℂ) (k₀ : Γ) : Submodule ℂ (Γ → ℂ) :=
  liftSub L u ⊓
    { carrier := {Φ | ∀ h, Φ h = c * u h * Φ (h * k₀)}
      add_mem' := fun {Φ Ψ} a b h => by
        simp only [Pi.add_apply, mul_add]
        rw [← a h, ← b h]
      zero_mem' := fun _ => by simp
      smul_mem' := fun a Φ b h => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [mul_left_comm, ← b h] }

variable {L u}

theorem shiftSub_translate (hmul : ∀ g g' k k', L g k → L g' k' → L (g * g') (k * k')) {c : ℂ} {z : G}
    (hz : z ∈ Subgroup.center G) {k₀ : Γ} (h₀ : L z k₀) {Φ : Γ → ℂ} (hΦ : Φ ∈ shiftSub L u c k₀) {g : G} {k : Γ}
    (hk : L g k) : (fun h => Φ (h * k)) ∈ shiftSub L u c k₀ := by
  obtain ⟨⟨a1, a2⟩, a3⟩ := hΦ
  have key : ∀ g' k', L g' k' → ∀ h, u (h * k') * Φ (h * k' * k) = u h * Φ (h * k' * k) := fun g' k' hk' h => by
    rw [← a1 g k hk, mul_assoc, a1 _ _ (hmul _ _ _ _ hk' hk)]
  refine ⟨⟨key, fun g' k' k'' h1 h2 h => ?_⟩, fun h => ?_⟩
  · show Φ (h * k' * k) = Φ (h * k'' * k)
    rw [mul_assoc, mul_assoc, a2 _ _ _ (hmul _ _ _ _ h1 hk) (hmul _ _ _ _ h2 hk)]
  · show Φ (h * k) = c * u h * Φ (h * k₀ * k)
    have e : L (z * g) (k * k₀) := (Subgroup.mem_center_iff.1 hz g) ▸ hmul _ _ _ _ hk h₀
    rw [a3 (h * k), mul_assoc c, ← a1 z k₀ h₀, mul_assoc h, a1 _ _ e, a2 _ _ _ e (hmul _ _ _ _ h₀ hk), mul_assoc h, mul_assoc c]

omit [Group G] in
theorem shift_eq {n : ℕ} {θ : Γ → ℂ} {a : Fin n → ℂ} {p pE : Fin n → Γ → ℂ} {k g : Γ} {c ph : ℂ} (hph : ph ≠ 0)
    (e1 : θ = ∑ j, a j • p j) (hr : ∀ j h, pE j h = u h * p j h) (hu : u (g * k) * θ (g * k) = u g * θ (g * k))
    (e3 : ph * θ g = c * ∑ j, a j * pE j (g * k)) : θ g = c / ph * u g * θ (g * k) := by
  have e4 : ∑ j, a j * pE j (g * k) = u g * θ (g * k) := by
    rw [← hu, e1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, hr]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e4] at e3
  field_simp
  linear_combination e3

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem eq_of_out {W : HSp D} (Φ Ψ : GA D W → ℂ) (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) (g : GA D W) : Φ g = Ψ g := by
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h]

section Lift

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev LiftW (g : G) (k : GA D (Wc D i)) : Prop := IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k

theorem liftW_mul (g g' : G) (k k' : GA D (Wc D i)) (h : LiftW R i g k) (h' : LiftW R i g' k') : LiftW R i (g * g') (k * k') := by
  refine ⟨mul_mem h.1 h'.1, by rw [map_mul]; exact mul_mem h.2.1 h'.2.1, ?_⟩
  rw [map_mul, Formalism.L2.DIV.rTup_mul h.2.1 h'.2.1, h.2.2, h'.2.2, map_mul]
  rfl

theorem levChi_flagW (k : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) k = 1 := by
  unfold levChi levFn
  have h : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  rw [h]
  show (((1 * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ ∅, _ : ℂˣ)) : ℂ) = 1
  simp

theorem exists_liftW_act {g : G} (hk : ∃ k, LiftW R i g k) : ∃ k, LiftW R i g k ∧
    ∀ Φ h, Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h = Φ (h * k) := by
  refine ⟨hk.choose, hk.choose_spec, fun Φ h => ?_⟩
  refine (GlobalTheory.SecLift.actL_apply (L := R.datWp i R.triv) hk Φ h).trans ?_
  rw [levChi_flagW, inv_one, one_mul]

theorem chiC_coe (g : G) : ((chiC R i g : ℂˣ) : ℂ) =
    ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := Units.coe_prod _ _

end Lift

section Shift

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ}

def ratio (cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (h : GA D (Wc D i)) : ℂ := cE (O.dict h).1 / c0 (O.dict h).1

theorem phi_apply (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi cc f h = cc (O.dict h).1 * O.mu h * rdU (C.U ((i : ℕ) + 1) O.s0) f (O.dict h).1 (O.dict h).2 := rfl

theorem phi_ratio (h0 : ∀ k, c0 k ≠ 0) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi cE f h = ratio O cE c0 h * O.phi c0 f h := by
  rw [phi_apply, phi_apply, ratio]
  have := h0 (O.dict h).1
  field_simp

theorem phi_mem_liftSub (h0 : ∀ k, c0 k ≠ 0) (hE : O.EquivAt κ cE) (hE0 : O.EquivAt κ c0) {f : C.R ((i : ℕ) + 1)}
    (hf : f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) : O.phi c0 f ∈ liftSub (LiftW R i) (ratio O cE c0) := by
  refine ⟨fun g k hk h => ?_, fun g k k' hk hk' h => ?_⟩
  · have e1 := (hE g k hk f hf).2 h
    have e2 := (hE0 g k hk f hf).2 h
    rw [← chiC_coe] at e1 e2
    rw [phi_ratio O h0, phi_ratio O h0 f, e2, mul_left_comm] at e1
    exact (mul_left_cancel₀ (chiC R i g).ne_zero e1).symm
  · have e1 := (hE0 g k hk f hf).2 h
    have e2 := (hE0 g k' hk' f hf).2 h
    rw [← chiC_coe] at e1 e2
    exact mul_left_cancel₀ (chiC R i g).ne_zero (e1.symm.trans e2)

set_option maxHeartbeats 4000000 in

theorem shift_of_span (hP : O.Pins κ v₀ ι x₀) (hn : κ.n = (Vc D i).rank) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0) {ph : ℂ} (hE : O.OneMapOf κ v₀ cE ph)
    (hE0 : O.EquivAt κ c0) (hS : GlobalTheory.AdTh.SerOf O κ v₀ c0 1)
    (hW : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∃ U ∈ R.Wall i (sg0 D A), ∀ h,
      U v₀ h = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cE f h) :
    ∃ (z : G) (c : ℂ), c ≠ 0 ∧ (∃ k, LiftW R i z k) ∧ ∀ k, LiftW R i z k →
      ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ h, O.phi c0 f h = c * O.phi cE f (h * k) := by
  obtain ⟨hEq, ⟨-, hBC, hAct, hcE, hph, z, hz, hrow⟩, -⟩ := hE
  obtain ⟨ze, -, ⟨m, hm, hze⟩, hrow⟩ := hrow ()
  have hze0 : ze ≠ 0 := fun h => by
    rw [h, zero_pow hm.ne'] at hze
    exact zero_ne_one hze
  have hph0 : ph ≠ 0 := fun h => by simp [h] at hph
  have h0 : ∀ k, c0 k ≠ 0 := fun k h => by simpa [h] using hS.1 k
  have hE0' : ∀ k, cE k ≠ 0 := fun k h => by simpa [h] using hcE k
  have hl : ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hlift : ∀ g, ∃ k, LiftW R i g k := fun g => (hP.lift.lev g).imp fun _ h => h.1
  have hinvW : ∀ U ∈ R.Wall i (sg0 D A), ∀ γ ∈ GQ (Wc D i), ∀ g, U v₀ (γ * g) = U v₀ g := fun U hU =>
    (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ U hU v₀).1
  have hinv : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, ∀ γ ∈ GQ (Wc D i), ∀ g, O.phi cE f (γ * g) = O.phi cE f g := by
    intro f hf γ hγ g
    obtain ⟨U, hU, e⟩ := hW f hf
    exact mul_left_cancel₀ hl (by rw [← e, ← e, hinvW U hU γ hγ])
  refine ⟨z, ze * chiC R i z / ph, div_ne_zero (mul_ne_zero hze0 (chiC R i z).ne_zero) hph0, hlift z, fun k hk => ?_⟩
  have hbase : ∀ y, R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈
      shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k := by
    intro y
    obtain ⟨hh, J', hrep, hPl, hth, hpl⟩ := (hP.tuple ()).reps
    obtain ⟨x, hx⟩ := hPl y
    obtain ⟨⟨f', hf', hcl⟩, hid⟩ := hrow x ((hpl x).2 ⟨y, hx⟩)
    have hs := hS.2.2 () hh J' hrep _ x hx f' hf'.1 hcl
    have hq := hid f' hf'.1 hcl
    have hth' : ∀ q : AutQ (Wc D i), O.thAd () x q = R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out := fun q => congrFun (hth _ x hx) q
    have hf'' : f' ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank := hf'
    have hb := hBC (wtA κ) (Vc D i).rank f' hf''
    obtain ⟨n, as, fs, hfs, hbc⟩ := hb
    have hbc' := hAct _ _ z n as fs f' hf'.1 (fun j => (hfs j).1) hbc
    have hfs' : ∀ j, fs j ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun j => by rw [hn]; exact hfs j
    have r1 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc
    have r2 := rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') hbc'
    have e1 : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ = ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        inC O.c' (as j)) • O.phi c0 (fs j) := by
      funext g
      have := hs g
      rw [one_mul, r1] at this
      rw [this]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, phi_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hmemL : R.thF i A.μ0 (jVx R i A.μ0 y) v₀ ∈ liftSub (LiftW R i) (ratio O cE c0) := by
      rw [e1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (phi_mem_liftSub O h0 hEq hE0 (hfs' j))
    refine ⟨hmemL, fun g => ?_⟩
    have e2 : ∀ q : AutQ (Wc D i), ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (q.out * k) := by
      intro q
      have h3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ q.out = ze * cE (O.dict q.out).1 *
          (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f') (O.dict q.out).1 (O.dict q.out).2) :=
        (congrArg (ph * ·) (hth' q)).symm.trans (hq q)
      rw [h3, r2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 := (hEq z k hk (fs j) (hfs' j)).2 q.out
      rw [← chiC_coe, phi_apply] at h2
      linear_combination (ze * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * h2
    have e3 : ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g =
        ze * chiC R i z * ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) *
          O.phi cE (fs j) (g * k) := by
      refine eq_of_out (fun g => ph * R.thF i A.μ0 (jVx R i A.μ0 y) v₀ g) (fun g => ze * chiC R i z *
        ∑ j, ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * inC O.c' (as j)) * O.phi cE (fs j) (g * k))
        (fun γ hγ g => congrArg (ph * ·) (hinvW _ (hmem i A.μ0 _) γ hγ g)) (fun γ hγ g => ?_) e2 g
      refine congrArg (ze * chiC R i z * ·) (Finset.sum_congr rfl fun j _ => ?_)
      rw [mul_assoc γ, hinv _ (hfs' j) γ hγ]
    exact shift_eq (pE := fun j => O.phi cE (fs j)) hph0 e1 (fun j h => phi_ratio O h0 (fs j) h) (hmemL.1 z k hk g) e3
  let ev : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun U => U v₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hall : ∀ y, R.thF i A.μ0 y v₀ ∈ shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k :=
    GlobalTheory.SecLift.span_of_pres (R.B.L i A.μ0).pres (R.HV i A.μ0).e (hHV i A.μ0).1 (hHV i A.μ0).2.1 (jVx R i A.μ0) (hjV i A.μ0)
      ((shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap (ev ∘ₗ R.thF i A.μ0)) hbase
  have hWall : R.Wall i (sg0 D A) ≤ (shiftSub (LiftW R i) (ratio O cE c0) (ze * chiC R i z / ph) k).comap ev := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, y, rfl⟩
    obtain ⟨k', hk', e⟩ := exists_liftW_act R i (hlift g)
    have h1 := shiftSub_translate (liftW_mul R i) hz hk (hall y) hk'
    rw [← funext (e (R.thF i A.μ0 y v₀))] at h1
    exact h1
  intro f hf h
  obtain ⟨U, hU, e⟩ := hW f hf
  have h1 : U v₀ h = ze * chiC R i z / ph * ratio O cE c0 h * U v₀ (h * k) := (hWall hU).2 h
  rw [e, e, phi_ratio O h0 f h] at h1
  have hr : ratio O cE c0 h ≠ 0 := div_ne_zero (hE0' _) (h0 _)
  refine mul_left_cancel₀ (mul_ne_zero hl hr) ?_
  linear_combination h1

end Shift

end GlobalTheory.HeckeSup
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev Formalism.L2.NTheta
open GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Comm

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem levChi_datWp (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := by
  have h : ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi
      (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h]
  simp [LevCh.datWp, datY]

theorem model_inv_cl (hHW : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (z : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv), ∀ h, (R.HW i σ).e z v (h * k) = (R.HW i σ).e z v h := by
  intro k hk h
  have hz : (R.HW i σ).e z ∈ R.Wall i σ := (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z
  rw [((GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ _ _ _ _).1 hz).lev v k hk h, levChi_datWp, one_mul]

theorem heckeOn_actW_cl {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hd : IsHkData R i P k α Rc) (g : G) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc (actW R i σ g ((R.HW i σ).e z)) = actW R i σ g (heckeOn (R.MW i σ) Rc ((R.HW i σ).e z)) := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hoF := GlobalTheory.HeckeModel.offAt_of_place (L := flagL (R.datWp i R.triv)) hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := exists_local_isDC hoL.splits hαL hR
  have key : ∀ (w : (R.HW i σ).H) v, heckeLin (Wc D i) Rc ((R.HW i σ).e w v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e w v) :=
    fun w v => funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (model_inv_cl hHW i σ w v) h
  have hg : actW R i σ g ((R.HW i σ).e z) = (R.HW i σ).e (R.gW i σ g z) := (hgW i σ g z).symm
  ext v : 1
  show heckeLin (Wc D i) Rc (actW R i σ g ((R.HW i σ).e z) v) =
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (heckeLin (Wc D i) Rc ((R.HW i σ).e z v))
  rw [hg, key, key, ← hg]
  exact (GlobalTheory.HeckeModel.heckeLin_actL hoF hαL hA₀ (fun k hk => model_inv_cl hHW i σ z v k hk.1) (R.eG g)).symm

theorem comm_rho_cl {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hd : IsHkData R i P k α Rc)
    (hinj : Function.Injective ((R.FW i).j σ))
    (hρ : RhoIs σ ((R.FW i).j σ) (R.HW i σ).e (actW R i σ) (R.FW i).chi (R.FW i).ρ) {c : ℂ}
    {hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hH : HeckeJ.IsHkJ σ ((R.FW i).j σ) (R.HW i σ).e (heckeOn (R.MW i σ) Rc) c hL) (g : G) :
    hL ∘ₗ (R.FW i).ρ g = (R.FW i).ρ g ∘ₗ hL := by
  refine LinearMap.ext fun x => hinj ((hHW i σ).1 ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hH, hρ, hρ, hH, map_smul, map_smul,
    heckeOn_actW_cl hβ' hSb hHW hgW σ hd, smul_comm]

end Comm

section Prime

theorem exists_prime_under {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p f : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ Nat.card (𝓞 E ⧸ P.asIdeal) = p ^ f := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  obtain ⟨f, hp, hf⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))
  refine ⟨_, f, hp, ?_, by rw [Nat.card_eq_fintype_card, hf]⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem split_of_ne {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {P : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) :
    P.asIdeal ⊔ P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  by_contra hne
  have hsub : P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ P.asIdeal :=
    le_sup_right.trans (P.isMaximal.eq_of_le hne le_sup_left).ge
  apply h
  rw [Formalism.L2.Col.conjIdeal_asIdeal]
  refine (P.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_).symm
  rw [Formalism.L2.Col.mem_conjP]
  have : Formalism.L2.Col.cO D.host.E a = H.bar a := RingOfIntegers.ext (H.bar_eq a).symm
  rw [this]
  exact hsub (Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ha)

theorem valuation_natCast_pow {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {p : ℕ}
    (hp : (p : 𝓞 K) ∉ la.asIdeal) (f : ℕ) : la.valuation K ((p ^ f : ℕ) : K) = 1 := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K p) = 1 := by
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hp ?_)
    exact (la.valuation_lt_one_iff_mem _).1 h
  rw [map_natCast] at h1
  rw [Nat.cast_pow, map_pow, h1, one_pow]

end Prime

section Sup

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiW_eq (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (f : T.R ((i : ℕ) + 1)) : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV a f = phiC T hV a f := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W), castDict hV (T.phiJ ((i : ℕ) + 1) σ a f) = phiC T hV a f := by
    intro W hV
    subst hV
    rfl
  exact key _ hV

variable {T R κ v₀}

theorem baseEmbedding_reading_eval_adelicFunction (fw : FWTie T R κ v₀) {i : Fin D.R.m} (hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i)
    (hex : JEvAt T R κ v₀ i (sg0 D A) hV) (f : Cu T κ i) :
    evAt R i _ (v₀ i _) (fw.jK i (sg0 D A) f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) := by
  obtain ⟨jK, hjK⟩ := hex
  obtain ⟨j', hj'⟩ := exists_ext_of_isKsForm (R.FW i) (fw.ks i) (fw.e i) (sg0 D A) jK
  exact fw.ev i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV
    ⟨j', fun f => (congrArg (evAt R i _ (v₀ i _)) (hj' f)).trans (hjK f)⟩ f

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem not_dvd_level (hL : LawsJ T) {P : Formalism.L2.DIV.Pl D.host.E} {p : ℕ} (hpP : (p : 𝓞 D.host.E) ∈ P.asIdeal)
    (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : ¬ p ∣ T.Q.l.M' := by
  intro h
  have e : T.Q.l.M' = D.host.g 0 * D.host.g 1 := by
    show Nat.lcm T.Q.l.M T.Q.l.A = _
    rw [hL.pins.2.1.1, hL.pins.2.1.2, Nat.lcm_one_right]
  obtain ⟨u, hu⟩ := e ▸ h
  apply hP
  rw [hu, Nat.cast_mul]
  exact P.asIdeal.mul_mem_right _ hpP

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem exists_transform (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) (hL : LawsJ T)
    (i : Fin D.R.m) {P : Ideal (𝓞 D.host.E)} {p k : ℕ} (hSO : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsSplitOff T.Q.l P p) (hk : k ≤ D.R.r)
    (cq : T.Q.c.F) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : Dom a n) :
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n, ∃ g ∈ T.cuspA ((i : ℕ) + 1) a n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P p k (hkScal T.Q.c cq P k n) f g := by
  have hpq : (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q = D.R.r := by
    have h1 := hL.pins.2.2.2 _ (inR i)
    rw [h1.1, h1.2.1]
    have := D.R.m_add_three_le_k
    have := i.2
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hE := hT.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P p k cq a n (hpq ▸ hr1) hSO (hpq ▸ hk) ha.2
  have hD : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.Detects (T.Q.Xo ((i : ℕ) + 1)) T.Q.c a n := hP.2.2.2 _ _ _ _ _ _ _ _
  have hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P p k :=
    hP.1 _ _ _ _ _ _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨hSO.max, hSO.split, hSO.prime, hSO.under, hSO.off⟩)
  exact (GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.keepsCusp_iff_exists hE hD hF).1
    (hT.2 D T.toCore hL.toLawsM _ (inR i) P p k cq _ _ hSO hk ha)

theorem apply_eq_of_read_cl (hHW : R.models_HW) (fw : FWTie T R κ v₀) {i : Fin D.R.m}
    (hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i) (hex : JEvAt T R κ v₀ i (sg0 D A) hV)
    (hinj : Function.Injective ((R.FW i).j (sg0 D A))) {Rc : Finset (GA D (Wc D i))} {c : ℂ}
    {hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hH : HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) c hL)
    {f g : Cu T κ i} (hfg : ∀ h, phiC T hV (wtA (κ i)) (g : T.R ((i : ℕ) + 1)) h =
      c * ∑ a ∈ Rc, phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * a)) :
    hL (fw.e i f : (R.FW i).WK) = (fw.e i g : (R.FW i).WK) := by
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  refine hinj (hEI ?_)
  refine Eq.trans ?_ (baseEmbedding_reading_eval_adelicFunction fw hV hex g).symm
  funext h
  rw [hfg h, ← baseEmbedding_reading_eval_adelicFunction fw hV hex f]
  unfold evAt
  rw [hH]
  rfl

theorem hkC_eq (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * (Nat.card (kP P) : ℂ)⁻¹ ^ (k * D.R.nV / 2) = hkC R i P k := by
  have e2 : k * D.R.nV / 2 = k * (D.R.nV / 2) := Nat.mul_div_assoc _ (even_iff_two_dvd.1 (kapDom D).2)
  rw [e2, inv_pow, inv_pow]
  rfl

variable (T R κ) in

def ReadsCusp (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHkData R i P k α Rc →
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g →
      ∀ h, phiC T hV (wtA (κ i)) g h = hkC R i P k * ∑ a ∈ Rc, phiC T hV (wtA (κ i)) f (h * a)

theorem readsCusp_of_readsAt {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ} {hV : T.V ((i : ℕ) + 1) σ = Wc D i}
    (hR : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt T R i σ hV (κ i)) : ReadsCusp T R κ i σ hV := by
  intro P p k α Rc _ hs f hf g hg hfg
  have hread := hR.modulus hs hf.1 hg.1 hfg
  simp only [phiW_eq, hkC_eq] at hread
  exact hread

theorem hkSupAt_of_readsCusp (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) (fw : FWTie T R κ v₀)
    (hex : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV)
    (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (hρ : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ)
    (hR : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, ReadsCusp T R κ i _ hV) :
    HkSupAt T R i := by
  intro P k α Rc hd hL hH hW la hla
  refine keeps_of _ la hL hW ?_ (comm_rho_cl hβ hSb hHW hgW _ hd hinj hρ hH)
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, hq⟩ := exists_prime_under P
  have hoff := not_dvd_level fw.laws hpP hd.2.1
  have hsp := split_of_ne (H := T.Q.H) hd.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  intro x hx
  obtain ⟨f, rfl⟩ := (fw.e i).surjective x
  obtain ⟨g, hg, hfg⟩ := exists_transform hT hP fw.laws i ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hd.2.2.1
    ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
  rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
    hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
  have hread := hR hV P p k α Rc hd ⟨hd.1, hp, hpP, hoff, hd.2.2⟩ f f.2 g hg hfg
  have heq : (⟨hL (fw.e i f), hW _ (fw.e i f).2⟩ : (R.FW i).WK) = fw.e i ⟨g, hg⟩ :=
    Subtype.ext (apply_eq_of_read_cl hHW fw hV (hex hV) hinj hH (f := f) (g := ⟨g, hg⟩) hread)
  rw [heq]
  intro y
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  refine transform_integral (hI _ _ _ _ _ _).2.2 (fw.laws.evalWD _ (inR i)) ⟨P.isMaximal, hsp, hp, hpP, hoff⟩
    (hP.1 _ _ _ _ _ _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsp, hp, hpP, hoff⟩))
    (hla p hp hpP) ?_ f.2.1 hg.1 hfg (fun v hv => ?_) _ (fw.pt i la y).2
  · have e1 : Ideal.absNorm P.asIdeal = p ^ m := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq]
    have e2 : Nat.card (kP P) = p ^ m := hq
    rw [hkScal, e1, e2, map_mul, map_pow, map_inv₀, valuation_natCast_pow (hla p hp hpP)]
    simp
  · have := hx ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Equiv.apply_symm_apply, Core.nrmM_le_one_iff] at this
    exact this

end Sup

section Pin

abbrev withConst (T : CoreJ D) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D := { T with cE := c' }

variable (T : CoreJ D) [iA : Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}

omit iA in
theorem phiC_withConst {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {f : T.R j} (h : (withConst T c').phiJ j σ a f = T.phiJ j σ a f) :
    phiC (withConst T c') hV a f = phiC T hV a f := by
  subst hV
  exact h

set_option maxHeartbeats 1600000 in

def tieWithConst (fw : FWTie T R κ v₀) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
    (h1 : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ))
    (h2 : ∀ (i' : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), ∀ f ∈ T.cuspA ((i' : ℕ) + 1) (wtA (κ i')) (κ i').n,
      (withConst T c').phiJ ((i' : ℕ) + 1) σ (wtA (κ i')) f = T.phiJ ((i' : ℕ) + 1) σ (wtA (κ i')) f) :
    @FWTie D G _ _ Pl0 T0 A (withConst T c') iA R κ v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (withConst T c') iA R κ v₀ fw.alg_eq fw.e fw.ks fw.kap fw.pt fw.nrm_eq
    ⟨fw.laws.toLawsM, h1, fw.laws.muVal, fw.laws.muConj, fw.laws.intAll, fw.laws.modelW, fw.laws.familyUniformisationBasePointOrthogonal, fw.laws.kfHalf,
      fw.laws.adPin⟩
    fw.chiR fw.hv₀ fw.x0
    (fun i σ hσ hV h => fw.ev0 i σ hσ hV fun ⟨j', hj'⟩ => h ⟨j', fun f => (hj' f).trans (phiC_withConst (T := T) (c' := c') hV (h2 i _ f f.2)).symm⟩)
    (fun i σ hσ hV h f =>
      (fw.ev i σ hσ hV (h.imp fun _ hj' f => (hj' f).trans (phiC_withConst (T := T) (c' := c') hV (h2 i _ f f.2))) f).trans
        (phiC_withConst (T := T) (c' := c') hV (h2 i _ f f.2)).symm)

omit iA in
theorem phiC_congr {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W) (hV' : T.V j σ' = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

omit iA in
theorem phiC_apply {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j)
    (h : GA D W) : phiC T hV a f h = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ)) (rdU (T.U j σ) f) h := by
  subst hV
  rfl

omit iA in

theorem exists_withConst (hL : LawsJ T) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c0 : (T.U j σ).Comp → ℂ) (h0 : CUnit c0) :
    ∃ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, c' j σ = c0 ∧ LawsJ (withConst T c') := by
  classical
  let Φ : ∀ p : ℕ × (T.Q.c.F →+* ℂ), (T.U p.1 p.2).Comp → ℂ := Function.update (fun p => T.cE p.1 p.2) (j, σ) c0
  have h1 : ∀ p : ℕ × (T.Q.c.F →+* ℂ), InR D p.1 → GoodEmb T.Q.c p.2 → CUnit (Φ p) := fun p h h' => by
    by_cases e : p = (j, σ)
    · subst e
      simpa only [Φ, Function.update_self] using h0
    · simpa only [Φ, Function.update_of_ne e] using hL.cUnit _ h _ h'
  exact ⟨fun j σ => Φ (j, σ), Function.update_self _ _ _,
    hL.toLawsM, fun j hj σ hσ => h1 (j, σ) hj hσ, hL.muVal, hL.muConj, hL.intAll, hL.modelW, hL.familyUniformisationBasePointOrthogonal, hL.kfHalf, hL.adPin⟩

theorem readsCusp_of_shift {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hHW : R.models_HW) (hgW : R.models_gW) {σ : T.Q.c.F →+* ℂ} {hV : T.V ((i : ℕ) + 1) σ = Wc D i}
    (hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f)
    {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ}
    (hR : @ReadsCusp D G _ _ Pl0 T0 A (withConst T c') iA R κ i σ hV) {z : G} {c : ℂ} (hc : c ≠ 0) (hz : ∃ k, LiftW R i z k)
    (hs : ∀ k, LiftW R i z k → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ h,
      phiC (withConst T c') hV (wtA (κ i)) f h = c * phiC T hV (wtA (κ i)) f (h * k)) : ReadsCusp T R κ i σ hV := by
  intro P p k α Rc hd hset f hf g hg hfg h
  obtain ⟨kz, hkz, e⟩ := exists_liftW_act R i hz
  obtain ⟨y, hy⟩ := hev f hf
  have h1 := hR P p k α Rc hd hset f hf g hg hfg (h * kz⁻¹)
  have h2 : ∑ a ∈ Rc, Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) ((R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)))
      (h * kz⁻¹ * a) = Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z)
        (fun x => ∑ a ∈ Rc, (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) (x * a)) (h * kz⁻¹) :=
    congrFun (congrArg (fun U : MMap (R.MW i (sg0 D A)) => U (v₀ i (sg0 D A)))
      (heckeOn_actW_cl hβ hSb hHW hgW (sg0 D A) hd z y)) (h * kz⁻¹)
  simp only [e, hy, inv_mul_cancel_right] at h2
  rw [hs kz hkz g hg, inv_mul_cancel_right, Finset.sum_congr rfl fun a _ => hs kz hkz f hf _, ← Finset.mul_sum, h2,
    mul_left_comm] at h1
  exact mul_left_cancel₀ hc h1

set_option maxHeartbeats 1600000 in

theorem readsCusp_of_clauses {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hinf : R.models_inf) (hHW : R.models_HW) (hgW : R.models_gW) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (fw : FWTie T R κ v₀) (hV₁ : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i)
    (hex : JEvAt T R κ v₀ i (sg0 D A) hV₁) (hpin₀ : ConstPinned T R κ v₀ i) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0)
    (hom : ∀ O : OMDat T.toCore R i Unit (fun _ => A.μ0),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
      ∃ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧
          GlobalTheory.AdTh.SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1)
    (hR : ∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, LawsJ (withConst T c') →
      ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV →
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV (κ i)) :
    ReadsCusp T R κ i (res T (sg0 D A)) hV₁ := by
  have hσ : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  obtain ⟨O, ph, -, hpins, hrow⟩ := hpin₀
  obtain ⟨cc, hcc, u, hu, hE0, hS⟩ := hom O hpins
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := O.hV
  have hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f := fun f hf =>
    ⟨_, (baseEmbedding_reading_eval_adelicFunction fw hV₁ hex ⟨f, hf⟩).trans (phiC_congr hσ hV₁ hV _ _)⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  have hphi : ∀ f h, phiC T hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) f h :=
    fun f h => phiC_apply hV _ f h
  obtain ⟨z, c, hc, hz, hs⟩ := shift_of_span O hpins hn hHV hjV hmem hsp hrow hE0 hS fun f hf => by
    obtain ⟨y, hy⟩ := hev f hf
    exact ⟨_, (hHW i _).2.1.le (LinearMap.mem_range_self _ y), fun h => (congrFun hy h).trans (hphi f h)⟩
  obtain ⟨c', hc', hL'⟩ := exists_withConst fw.laws ((i : ℕ) + 1) T.σ₀ cc hcc.1
  have hx0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) :=
    hσ ▸ fw.x0 i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hpin := @GlobalTheory.FrameConst.framePin_of_ccIs D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV rfl hL' hinf hpins.lift.std hx0
    (by subst hc'; exact hcc)
  have hphi' : ∀ f h, phiC (withConst T c') hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * O.phi cc f h := fun f h => by
    subst hc'
    exact phiC_apply (T := withConst T c') hV _ f h
  have key : ReadsCusp T R κ i T.σ₀ hV := by
    refine readsCusp_of_shift (v₀ := v₀) hβ hSb hHW hgW hev
      (@readsCusp_of_readsAt D G _ _ Pl0 T0 A (withConst T c') iA R κ i _ hV (hR c' hL' hV hpin))
      (div_ne_zero hc hu0) hz fun k hk f hf h => ?_
    have h1 := hs k hk f hf h
    have h2 : O.phi (u • cc) f h = u * O.phi cc f h := by
      rw [phi_apply, phi_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hphi', hphi]
    field_simp
    rw [h2] at h1
    linear_combination (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * h1
  have gen : ∀ (σ : T.Q.c.F →+* ℂ) (hW : T.V ((i : ℕ) + 1) σ = Wc D i), σ = T.σ₀ → ReadsCusp T R κ i σ hW := by
    rintro _ _ rfl
    exact key
  exact gen _ hV₁ hσ

theorem hkSupAt_of_clauses (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt) (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws) {i : Fin D.R.m} (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb)
    (hinf : R.models_inf) (hHW : R.models_HW) (hgW : R.models_gW) (hHV : R.models_HV) (hjV : R.models_jV)
    (hmem : R.thP_thF_mem) (fw : FWTie T R κ v₀) (h0 : ReadAt0 T R κ v₀ i) (hsp : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SpanAt R i A.μ0)
    (hom : ∀ O : OMDat T.toCore R i Unit (fun _ => A.μ0),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) →
      ∃ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧
          GlobalTheory.AdTh.SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1)
    (hR : ∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, LawsJ (withConst T c') →
      ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV →
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV (κ i)) :
    HkSupAt T R i :=
  hkSupAt_of_readsCusp hI hT hP hβ hSb hHW hgW fw h0.ex h0.inj h0.rho fun hV =>
    readsCusp_of_clauses hβ hSb hinf hHW hgW hHV hjV hmem fw hV (h0.ex hV) h0.const hsp hom hR

end Pin

end GlobalTheory.HeckeSup
end
end
