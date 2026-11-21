import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelPreservingLatticeIsoOfMembers
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStalkNormalNoetherianFractionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkHomStalkMapEqFunctionFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStalkGermQuotientIntegralUnitDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMemberThroughModelPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtendingModelAboveThetaSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaloisFractionRingOfIsFractionRing

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_opens_R_le_O : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧
    ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  intro X₁
  obtain ⟨s, hs⟩ := X₁.S.fg
  refine ⟨⟨⋂ x ∈ s, {z | x ∈ X₁.M.O z}, isOpen_biInter_finset fun x _ => X₁.M.isOpen_setOf_mem_O x⟩,
    ⟨genericPoint X₁.M.Z, ?_⟩, ?_⟩
  · show genericPoint X₁.M.Z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z}
    refine Set.mem_iInter₂.2 fun x _ => ?_
    show x ∈ X₁.M.O (genericPoint X₁.M.Z)
    rw [RatModel.O_genericPoint]
    exact Algebra.mem_top
  · intro z hz
    have hz' : z ∈ ⋂ x ∈ s, {z | x ∈ X₁.M.O z} := hz
    rw [← hs]
    exact Algebra.adjoin_le fun x hx => Set.mem_iInter₂.1 hz' x hx

end GlobalTheory.GSep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_open_thetaRing_regular : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧ ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  atlas_forward_decl GlobalTheory.GSep.exists_opens_R_le_O
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_div_torsion : ∀ (X₁ : GlobalTheory.GSep.GSet) (z : X₁.M.Z) (k : ℕ), 2 ≤ k → k ∣ X₁.S.r * X₁.S.N →
    ∃ a : X₁.S.Gam, k • a = 0 ∧ X₁.M.Div X₁.S.th a z := by
  intro X z₀ k hk hd
  haveI := X.M.qc
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z, hz', hcl⟩ := (isClosed_closure (s := {z₀})).exists_closed_singleton ⟨z₀, subset_closure rfl⟩
  have hsp : z₀ ⤳ z := specializes_iff_mem_closure.2 hz'
  obtain ⟨U, hne, hU⟩ := GlobalTheory.T.exists_nonempty_open_thetaRing_regular X
  obtain ⟨p, _, y, hy, hyU⟩ := exists_cen_main _ _ X.M z hcl U hne
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hTU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hle : X.S.R ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hU _ (hyU ⟨_, rfl⟩)
  have hsw : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (closedPoint (PadicAlgCl p)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]
  let y₀ : X.S.R →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ y) _ hsw).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.S.R, y₀ a = X.M.val (gPt p ≫ y) a := fun _ => rfl
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ X.S.R a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hy ((X.M.O z).algebraMap_mem a)
  obtain ⟨u, l, τ, hτ, -⟩ :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hTU hL hL2 hUT X.o₁ X.Ω₁ X.S X.ρ).2 p y₀ ∅ hint
  have hq : ∀ w, 0 ≤ l.q w := fun w => by
    obtain ⟨e, he, -⟩ := hτ
    have h := τ.q_nonneg (e.symm w)
    rwa [he, AddEquiv.apply_symm_apply] at h
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale hL hL2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ _ X.ρ p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    exact hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (hq w) (by positivity)))))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, RatModel.Div.of_specializes ?_ hsp⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hy (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hy
  have e : ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ =
      ‖y₀ ⟨X.S.th d, X.S.th_mem d⟩‖ * ‖X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul hsw (hle (X.S.th_mem d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have b₁ := RatModel.norm_val_le_one hy (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)))
  nlinarith

end GlobalTheory.GSep
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DeepDivG


variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem exists_stalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) (x : Ω)
    (hx : x ∈ M.O z) : ∃ s : M.Z.presheaf.stalk z, M.stalkHom z s = x := by
  obtain ⟨s, hs⟩ := (M.stalkEquiv z).surjective ⟨x, hx⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

end GlobalTheory.GSep.DeepDivG

namespace GlobalTheory.GSep.DeepDivG

theorem tower_same {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) :
    GlobalTheory.Poinc.Same X₁.ρ (fun _ => 𝟙 _) 𝔗.X₂.ρ (fun _ => 𝟙 _) 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let P₀ := GlobalTheory.StrictPull.polPull 𝔗.X₂.ρ.P f₂
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun _ => 𝟙 _, ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    exact ⟨by simp, by simp⟩
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _

end GlobalTheory.GSep.DeepDivG

open GlobalTheory.GSep.DeepDivG in

theorem GlobalTheory.GSep.DeepDivG.div_lam : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  intro I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := GlobalTheory.GSep.exists_div_torsion 𝔗.X₂ z₂ _ (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.GSep.DeepDivG.tower_same 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTower_dividing_label_stays_dividing : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  atlas_forward_decl GlobalTheory.GSep.DeepDivG.div_lam
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.TermsLabel

theorem yy_zero_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  intro I X₁ z₁ act x₀ V _ _ _ ev X _ t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, -⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨⟨o, ho₁, ho₂⟩, hwc, hov⟩ := hg c
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (AlgebraicClosure (FractionRing V))
  have hkg : (X₁.S.r * X₁.S.N) • g' c = 0 :=
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  set gb := GlobalTheory.TorusExt.gtExt 𝔪.D.toPre (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))
    (RingHom.comp_id _) (g' c) with hgb
  have hkgb : (X₁.S.r * X₁.S.N) • gb = GlobalTheory.TorusExt.iota hB (AlgebraicClosure (FractionRing V)) 0 := by
    rw [hgb, ← map_nsmul, hkg, map_zero, map_zero]

  let p := GlobalTheory.TorusExt.qkMk hB 0 gb hkgb
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x (lab c)
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ (g' c) (w c) (x (lab c)) (fr (lab c)) hwc (hfr _).1 hov xb rfl

  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have hq := (f₁ p (f' p)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V))
    w₀ hw₀ _ hk p (f' p) rfl hq

  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀ hw₀ p.g wb w' xb
    (f' p) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, xb, (map_zero 𝔪.e₈).symm, e ▸ hq, ?_⟩
  have e₁ : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
    (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  rw [← e₁, Category.assoc, ← hx (lab c)]
  rfl

end GlobalTheory.GSep.TermsLabel
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeClass_zero_of_member_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  atlas_forward_decl GlobalTheory.GSep.TermsLabel.yy_zero_of_terms
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_centred_ext_tower : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), (∀ m : ℕ, m ≠ 0 → IsUnit (m : V)) → IsCN V → IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ J : Ideal V, (J.map io).comap io = J) ∧ 𝔗.Ext ev io ev₂ := by
  intro I X₁ z₁ act _ 𝔗 z₂ hz V _ _ _ ev hunit hV hev _
  subst hz
  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ := (X₁.M.stalkHom (𝔗.p z₂)).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := stalk_isNoetherian_normal_fractionRing X₁ (𝔗.p z₂)
  letI : Algebra (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := (𝔗.X₂.M.stalkHom z₂).toAlgebra
  obtain ⟨hdom₂, hfr₂, hic₂, -⟩ := stalk_isNoetherian_normal_fractionRing 𝔗.X₂ z₂
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.Poinc.integralClosure_galois_finite_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁
  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom (𝔗.p z₂))).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdom; haveI := hfr; haveI := hic; haveI := hdom₂; haveI := hfr₂; haveI := hic₂
  haveI : Algebra.IsInvariant (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) :=
    ⟨fun b hb => hfix b hb⟩
  haveI : Module.Finite (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfin
  haveI : Finite (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfinA

  haveI : CharZero V := hV.2.2.2
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨K', _, _, β, hK'fd, -, hβ⟩ := GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) hinj (FractionRing V)
    ((algebraMap V (FractionRing V)).comp ev)
  haveI := hK'fd

  have hK'u : IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) := hunit _ Module.finrank_pos.ne'
  obtain ⟨V', _, _, _, io, j, hV', hioi, hiof, hiol, hcon, hjinj, hj, hjr⟩ := GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank V hV K' hK'u
  have hβmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, β b ∈ j.range := by
    intro b
    obtain ⟨P, hPm, hP⟩ := integralClosure.isIntegral b
    obtain ⟨y, hy⟩ := hjr (β b) ⟨P.map ev, hPm.map ev, by
      rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hβ, ← Polynomial.hom_eval₂, hP, map_zero]⟩
    exact ⟨y, hy⟩
  let jr : V' ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hjinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let β' : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* V' := jr.symm.toRingHom.comp (β.codRestrict j.range hβmem)
  have hβ' : ∀ b, j (β' b) = β b := fun b => congrArg Subtype.val (jr.apply_symm_apply ⟨β b, hβmem b⟩)

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) := (𝔗.p.stalkMap z₂).hom.toAlgebra
  have hg1 : ∀ x : (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), 𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) :=
    fun x => (GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p 𝔗.p_pt z₂ x)
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq fun x => (hg1 x).symm
  have hinj₂ := 𝔗.X₂.M.stalkHom_injective z₂
  have hBmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, (b : 𝔗.X₂.Ω₁) ∈ (𝔗.X₂.M.stalkHom z₂).range := fun b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (𝔗.X₂.M.Z.presheaf.stalk z₂)) (K := 𝔗.X₂.Ω₁)).1
      (IsIntegral.tower_top (A := (𝔗.X₂.M.Z.presheaf.stalk z₂)) b.2)
    exact ⟨y, hy⟩
  let e₂ : (𝔗.X₂.M.Z.presheaf.stalk z₂) ≃+* (𝔗.X₂.M.stalkHom z₂).range := RingEquiv.ofBijective (𝔗.X₂.M.stalkHom z₂).rangeRestrict
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), (𝔗.X₂.M.stalkHom z₂).rangeRestrict_surjective⟩
  let f : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* (𝔗.X₂.M.Z.presheaf.stalk z₂) :=
    e₂.symm.toRingHom.comp (((integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁).val : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] 𝔗.X₂.Ω₁).toRingHom.codRestrict _ hBmem)
  have hf : ∀ b, 𝔗.X₂.M.stalkHom z₂ (f b) = b := fun b => congrArg Subtype.val (e₂.apply_symm_apply ⟨_, hBmem b⟩)
  have hfB : ∀ (t : (𝔗.X₂.M.Z.presheaf.stalk z₂)) (h : 𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁), f ⟨_, h⟩ = t :=
    fun t h => hinj₂ (hf _)
  have hloc : IsLocalHom (f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁))) := by
    have h : f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = (𝔗.p.stalkMap z₂).hom :=
      RingHom.ext fun a => hinj₂ (by rw [RingHom.comp_apply, hf, hg1]; rfl)
    rw [h]; infer_instance
  have hint : ∀ t : (𝔗.X₂.M.Z.presheaf.stalk z₂), (∃ P : Polynomial (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), P.Monic ∧ P.eval₂ (𝔗.p.stalkMap z₂).hom t = 0) →
      𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := by
    rintro t ⟨P, hPm, hP⟩
    refine ⟨P, hPm, ?_⟩
    have h : algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ = (𝔗.X₂.M.stalkHom z₂).comp (𝔗.p.stalkMap z₂).hom := RingHom.ext fun x => (hg1 x).symm
    rw [h, ← Polynomial.hom_eval₂, hP, map_zero]
  have hsurj : ∀ y : (𝔗.X₂.M.Z.presheaf.stalk z₂), ∃ b s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ y * f s = f b := by
    intro y
    obtain ⟨b, s, hs, hys, hb, hs'⟩ := GlobalTheory.Poinc.finite_stalk_quot_integral _ _ 𝔗.p 𝔗.p_fin z₂ y
    refine ⟨⟨_, hint b hb⟩, ⟨_, hint s hs'⟩, ?_, ?_⟩
    · rw [hfB]; exact hs
    · rw [hfB, hfB]; exact hys
  have hker : ∀ b, f b = 0 → ∃ s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ s * b = 0 := fun b hb =>
    ⟨1, by rw [map_one]; exact isUnit_one, by
      rw [_root_.one_mul]; exact Subtype.ext (by rw [← hf b, hb, map_zero]; rfl)⟩
  haveI := hiol; haveI := hev
  have hβ'A : β'.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = io.comp ev := RingHom.ext fun a =>
    hjinj ((hβ' _).trans ((RingHom.congr_fun hβ a).trans (RingHom.congr_fun hj (ev a)).symm))
  obtain ⟨ev₂, hev₂, hcomp⟩ := GlobalTheory.twisted_lift_to_localisation (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (𝔗.X₂.M.Z.presheaf.stalk z₂)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) f hloc hsurj hker V' (io.comp ev) β' inferInstance hβ'A
  refine ⟨V', inferInstance, inferInstance, inferInstance, io, ev₂, hV', hioi, hiof, hiol, hcon, hev₂, fun x x₂ hx => ?_⟩
  have h : x₂ = f (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) x) := hinj₂ (by rw [hf]; exact hx)
  rw [h]
  exact RingHom.congr_fun hcomp x

end GlobalTheory.GSep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centred_pure_extension_tower_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), (∀ m : ℕ, m ≠ 0 → IsUnit (m : V)) → IsCN V → IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ J : Ideal V, (J.map io).comap io = J) ∧ 𝔗.Ext ev io ev₂ := by
  atlas_forward_decl GlobalTheory.GSep.exists_centred_ext_tower
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.GSep.div_lam_and_lam_mem_HH : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ ∧ ∀ a ∈ X₁.S.HH X₁.M z₁, 𝔗.lam a ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := by
  intro I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx₀ V _ _ _ ev X _ t δ 𝔪
  refine ⟨GlobalTheory.T.galoisTower_dividing_label_stays_dividing I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx₀ V ev X t δ 𝔪, ?_⟩
  intro a ha
  have hunitV : ∀ m : ℕ, m ≠ 0 → IsUnit (m : V) := fun m hm => by
    simpa using (hunit m hm).map ev
  obtain ⟨V', _, _, _, io, ev₂, hcn', hinj, hfin, -, -, hext⟩ := GlobalTheory.T.exists_centred_pure_extension_tower_member I X₁ z₁ act hact 𝔗 z₂ hz₂ V ev hunitV
    𝔪.cn 𝔪.loc 𝔪.reg
  obtain ⟨u, hT, -, -⟩ := GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift I X₁ z₁ act x₀ hx₀ V ev X t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val
    Subtype.range_coe
  obtain ⟨eps, hbc⟩ := GlobalTheory.T.exists_galoisTower_baseChange_thetaMember I X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀
  obtain ⟨𝔪₂, hterms, -⟩ := hbc V ev X t δ 𝔪 _ Subtype.val _ hT V' io hcn' hinj hfin
  let zt : 𝔗.X₂.M.Z.presheaf.stalk z₂ := (𝔗.X₂.M.stalkEquiv z₂).symm
    ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, (𝔗.X₂.M.O z₂).algebraMap_mem _⟩
  have hzt : 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ :=
    congrArg Subtype.val ((𝔗.X₂.M.stalkEquiv z₂).apply_symm_apply _)
  have hyy := GlobalTheory.T.latticeClass_zero_of_member_terms I 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) V' ev₂ X (fun k => io (t k)) δ (𝔪₂ ev₂ hext) _ _ _
    (hterms ev₂ hext zt hzt) ⟨a, ha⟩
  obtain ⟨x₂, hx₂⟩ := 𝔗.X₂.div z₂
  exact (GlobalTheory.T.mem_dividingLabels_iff_class_zero I 𝔗.X₂ z₂ 𝔗.act₂ x₂ hx₂ V' ev₂ X (fun k => io (t k)) δ (𝔪₂ ev₂ hext) (𝔗.lam a)).2 hyy
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperModel_dividing_label_and_shifts_preserved : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ ∧ ∀ a ∈ X₁.S.HH X₁.M z₁, 𝔗.lam a ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := by
  atlas_forward_decl GlobalTheory.GSep.div_lam_and_lam_mem_HH
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem zhAbove_surjective {X₁ : GSet} {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} (h : ZHAbove X₁ Y πY) :
    Function.Surjective πY := by
  obtain ⟨-, -, -, -, -, hH, hP⟩ := h
  haveI := hP
  have hc : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
  have hg : genericPoint X₁.M.Z ∈ Set.range πY := by
    refine ⟨Y.pt (IsLocalRing.closedPoint X₁.Ω₁), ?_⟩
    have e := congrArg (fun f : Sp X₁.Ω₁ ⟶ X₁.M.Z => f (IsLocalRing.closedPoint X₁.Ω₁)) hH
    simp only [Scheme.Hom.comp_apply] at e
    exact e.trans (X₁.M.pt_apply _)
  intro z
  have : z ∈ closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) := by
    rw [genericPoint_spec X₁.M.Z |>.def]; trivial
  exact (closure_minimal (Set.singleton_subset_iff.2 hg) hc) this

theorem exists_gMem_injective : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact
  obtain ⟨Y, πY, hY⟩ := GlobalTheory.T.exists_semiAbelianExtendingModel_above_thetaSystem X₁
  obtain ⟨y, hy⟩ := zhAbove_surjective hY z₁
  obtain ⟨V, i1, i2, i3, -, ev, X, i4, t, δ, 𝔫, -, -, -, hinj⟩ := GlobalTheory.T.exists_thetaMember_through_model_point I X₁ z₁ act hact Y πY hY y hy
  exact ⟨V, i1, i2, i3, ev, X, i4, t, δ, hinj, ⟨𝔫⟩⟩

end GlobalTheory.GSep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaMember_injective_evaluation : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  atlas_forward_decl GlobalTheory.GSep.exists_gMem_injective
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

open GlobalTheory.Poinc.RingSide in

theorem GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  intro I X₁ act 𝔗 z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ x =
      algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
  have hnorm := (GlobalTheory.isNormalScheme_iff_pred _).1 𝔗.X₂.normal
  obtain ⟨h1, h2, -, -⟩ := integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p hnorm
    𝔗.p_fin 𝔗.p_pt z₁
  obtain ⟨𝔷, h𝔷⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁)
  obtain ⟨z₂, hz₂, h𝔷z⟩ := h2 𝔷 h𝔷
  have hB : ∀ b ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, b ∈ 𝔗.X₂.M.O z₂ :=
    fun b hb => (h1 b).1 hb z₂ hz₂
  have hloc := GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p hnorm
    𝔗.p_fin 𝔗.p_pt z₁ z₂ hz₂
  have hcomap : (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap (jMap z₂ hB) = 𝔷 := by
    ext b
    rw [Ideal.mem_comap, jMap_mem_max_iff, h𝔷z]
    tauto
  refine ⟨z₂, jMap z₂ hB, hz₂, stalkHom_jMap z₂ hB, hcomap ▸ h𝔷, fun x hx => (h1 x).2 hx,
    fun σ H => exists_stalk_ringEquiv halg z₂ hB hloc σ H,
    fun V _ ev V' _ io ev₂ hev hio hE => injective_of_ext halg hB hloc ev io ev₂ hev hio hE.2⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_stalk : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  atlas_forward_decl GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.GSep.ClassSumFun

section SumILemmas
variable {R : Type} [CommRing R] {I : Ideal R} {E Ix : Type} [AddCommGroup E] [Module R E]

theorem sumI_zero : SumI I (fun _ : Ix => (0 : E)) 0 :=
  ⟨⊥, Submodule.fg_bot, Submodule.zero_mem _, fun _ => Submodule.zero_mem _,
    fun _ => ⟨∅, fun T _ => by simp⟩⟩

theorem sumI_add {x y : Ix → E} {s t : E} (hx : SumI I x s) (hy : SumI I y t) :
    SumI I (fun i => x i + y i) (s + t) := by
  obtain ⟨N₁, f₁, hs₁, hx₁, h₁⟩ := hx
  obtain ⟨N₂, f₂, hs₂, hx₂, h₂⟩ := hy
  refine ⟨N₁ ⊔ N₂, f₁.sup f₂, Submodule.add_mem_sup hs₁ hs₂, fun i => Submodule.add_mem_sup (hx₁ i) (hx₂ i),
    fun n => ?_⟩
  obtain ⟨S₁, hS₁⟩ := h₁ n
  obtain ⟨S₂, hS₂⟩ := h₂ n
  classical
  refine ⟨S₁ ∪ S₂, fun T hT => ?_⟩
  have e : s + t - ∑ i ∈ T, (x i + y i) = (s - ∑ i ∈ T, x i) + (t - ∑ i ∈ T, y i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS₁ T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS₂ T (Finset.union_subset_right hT)))

theorem sumI_smul (c : R) {x : Ix → E} {s : E} (hx : SumI I x s) : SumI I (fun i => c • x i) (c • s) := by
  obtain ⟨N, f, hs, hxN, h⟩ := hx
  refine ⟨N, f, N.smul_mem c hs, fun i => N.smul_mem c (hxN i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.smul_sum, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ c (hS T hT)

theorem sumI_sum {κ : Type} (F : Finset κ) (x : κ → Ix → E) (s : κ → E) (h : ∀ j ∈ F, SumI I (x j) (s j)) :
    SumI I (fun i => ∑ j ∈ F, x j i) (∑ j ∈ F, s j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (sumI_zero (I := I) (E := E) (Ix := Ix))
  | insert a F ha ih =>
    simp only [Finset.sum_insert ha]
    exact sumI_add (h a (Finset.mem_insert_self a F)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem sumI_comp {Ix' : Type} {e : Ix' → Ix} (he : Function.Injective e) {x : Ix → E} {s : E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) (hx : SumI I x s) : SumI I (fun j => x (e j)) s := by
  classical
  obtain ⟨N, f, hs, hxN, h⟩ := hx
  refine ⟨N, f, hs, fun j => hxN (e j), fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
  have hsum : ∑ j ∈ T, x (e j) = ∑ i ∈ T.map ⟨e, he⟩ ∪ S, x i := by
    rw [show ∑ j ∈ T, x (e j) = ∑ i ∈ T.map ⟨e, he⟩, x i from (Finset.sum_map T ⟨e, he⟩ x).symm]
    refine Finset.sum_subset Finset.subset_union_left fun i hi hni => ?_
    refine h0 i fun ⟨j, hj⟩ => hni ?_
    subst hj
    have hjS : e j ∈ S := by
      rcases Finset.mem_union.1 hi with h1 | h1
      · exact absurd h1 hni
      · exact h1
    exact Finset.mem_map_of_mem _ (hT (Finset.mem_preimage.2 hjS))
  rw [hsum]
  exact hS _ Finset.subset_union_right

end SumILemmas

theorem pow_val_mul_pow_val {M : Type} [Monoid M] {m : ℕ} [NeZero m] {q : M} (hq : q ^ m = 1) (x y : ZMod m) :
    q ^ x.val * q ^ y.val = q ^ (x + y).val := by
  rw [← pow_add, ZMod.val_add]
  conv_lhs => rw [← Nat.div_add_mod (x.val + y.val) m, pow_add, pow_mul, hq, one_pow, _root_.one_mul]

theorem sum_pow_val_eq_zero {V : Type} [CommRing V] [IsDomain V] {m : ℕ} [NeZero m] {q : V}
    (hq : IsPrimitiveRoot q m) {G : Type} [AddCommGroup G] [Fintype G] (k : G → ZMod m)
    (hk : ∀ x y, k (x + y) = k x + k y) (τ₀ : G) (h₀ : k τ₀ ≠ 0) : ∑ τ, q ^ (k τ).val = 0 := by
  have hsh : ∑ τ, q ^ (k τ).val = (∑ τ, q ^ (k τ).val) * q ^ (k τ₀).val := by
    rw [Finset.sum_mul]
    refine (Fintype.sum_equiv (Equiv.addRight τ₀) _ _ fun τ => ?_).symm
    rw [pow_val_mul_pow_val hq.pow_eq_one, Equiv.coe_addRight, hk]
  have hne : q ^ (k τ₀).val ≠ 1 :=
    hq.pow_ne_one_of_pos_of_lt (by rwa [Ne, ZMod.val_eq_zero]) (ZMod.val_lt _)
  have h2 : (∑ τ, q ^ (k τ).val) * (q ^ (k τ₀).val - 1) = 0 := by
    rw [mul_sub, _root_.mul_one, ← hsh, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hne)

theorem isPrimitiveRoot_map {o V : Type} [CommRing o] [IsDomain o] [CommRing V] [IsDomain V] (φ : o →+* V)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem eStd_sub_right (g m : ℕ) (x a b : Fin g ⊕ Fin g → ZMod m) :
    eStd g m x (a - b) = eStd g m x a - eStd g m x b := by
  simp only [eStd, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem eStd_add_left (g m : ℕ) (x y a : Fin g ⊕ Fin g → ZMod m) :
    eStd g m (x + y) a = eStd g m x a + eStd g m y a := by
  simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.GSep.ClassSumFun

namespace GlobalTheory.GSep.ClassSumFun
open Classical

theorem exists_classSum_fun : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ f : X₁.S.Gam → X₁.S.Gam → X₁.Ω₁, (∀ a b, ∀ w : X₁.M.Z, X₁.M.Div X₁.S.th x₀ w → f a b ∈ X₁.M.O w) ∧ (∀ a a' b, a - a' ∈ X₁.S.HH X₁.M z₁ → f a b = f a' b) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C) (a : X₁.S.Gam) (κ : X), 𝔪.YY a κ → ∀ h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ h = f a (lab c) → SumI (maximalIdeal V) (fun nu : X => T (κ + (X₁.S.r * X₁.S.N) • nu) c) (ev h) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, eps, hlink⟩ := GlobalTheory.T.thetaConstants_translate_eq_twisted_sums I X₁ z₁ act x₀ hdiv
  have hm0 : 0 < X₁.S.r * X₁.S.N :=
    Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨hm0.ne'⟩
  haveI := ArithBase.ded (o := X₁.o₁) X₁.Ω₁
  have hcard : IsUnit ((Nat.card (X₁.S.TT X₁.M z₁) : ℕ) : X₁.o₁) := by
    have hdvd : Nat.card (X₁.S.TT X₁.M z₁) ∣ (X₁.S.r * X₁.S.N) ^ Nat.card (Fin X₁.S.g ⊕ Fin X₁.S.g) := by
      have h1 := AddSubgroup.card_addSubgroup_dvd_card (X₁.S.TT X₁.M z₁)
      have h2 : Nat.card X₁.S.Gam = (X₁.S.r * X₁.S.N) ^ Nat.card (Fin X₁.S.g ⊕ Fin X₁.S.g) := by
        rw [Nat.card_fun, Nat.card_zmod]
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := hdvd
    have hu : IsUnit ((((X₁.S.r * X₁.S.N) ^ Nat.card (Fin X₁.S.g ⊕ Fin X₁.S.g) : ℕ)) : X₁.o₁) := by
      rw [Nat.cast_pow]; exact X₁.S.unit.pow _
    rw [hk, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  set u : X₁.o₁ := ↑hcard.unit⁻¹ with hu_def
  have hu1 : u * (Nat.card (X₁.S.TT X₁.M z₁) : X₁.o₁) = 1 := hcard.val_inv_mul
  set K : X₁.S.Gam → X₁.S.TT X₁.M z₁ → ZMod (X₁.S.r * X₁.S.N) :=
    fun a τ => (-(sg : ℤ)) • eStd X₁.S.g _ (τ : X₁.S.Gam) a with hK
  refine ⟨fun a b => ∑ τ : X₁.S.TT X₁.M z₁, algebraMap X₁.o₁ X₁.Ω₁ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val) *
      (algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps b τ) * X₁.S.th (b + τ) / X₁.S.th x₀), ?_, ?_, ?_⟩
  · intro a b w hw
    refine Subalgebra.sum_mem _ fun τ _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    rw [mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hw.2 _)
  · intro a a' b hab
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h0 : eStd X₁.S.g _ (τ : X₁.S.Gam) (a - a') = 0 := τ.2 _ hab
    rw [eStd_sub_right, sub_eq_zero] at h0
    have : K a τ = K a' τ := by simp only [hK, h0]
    rw [this]
  · intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c a κ hκ h hh
    obtain ⟨hex, hsurj, hcong, hadd⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
    have hint := GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hdiv V ev X t δ 𝔪
    have hY0 : 𝔪.YY 0 0 := (hint 0).1 (AddSubgroup.zero_mem _)
    have hneg : ∀ a mu, 𝔪.YY a mu → 𝔪.YY (-a) (-mu) := by
      intro a mu ha
      obtain ⟨mu', hmu'⟩ := hex (-a)
      have h1 := hadd a (-a) mu mu' ha hmu'
      rw [add_neg_cancel] at h1
      have hc := (hcong 0 0 (mu + mu') hY0).1 h1
      refine (hcong (-a) mu' (-mu) hmu').2 ?_
      obtain ⟨w, hw⟩ := hc
      refine ⟨-w, ?_⟩
      simp only [zero_add] at hw
      rw [smul_neg, ← hw]
      abel
    have hsub : ∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a - a') (mu - mu') := by
      intro a a' mu mu' ha ha'
      simpa [sub_eq_add_neg] using hadd _ _ _ _ ha (hneg _ _ ha')
    choose A hA using hsurj
    have hdiff : ∀ a' mu, 𝔪.YY a' mu → ∀ τ ∈ X₁.S.TT X₁.M z₁, eStd X₁.S.g _ τ a' = eStd X₁.S.g _ τ (A mu) := by
      intro a' mu ha' τ hτ
      have h1 : a' - A mu ∈ X₁.S.HH X₁.M z₁ := (hint _).2 (by simpa using hsub _ _ _ _ ha' (hA mu))
      have h2 : eStd X₁.S.g _ τ (a' - A mu) = 0 := hτ _ h1
      rwa [eStd_sub_right, sub_eq_zero] at h2
    set ι₀ : X₁.o₁ →+* X₁.M.Z.presheaf.stalk z₁ :=
      (X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁)) with hι₀
    have hι : ∀ x, X₁.M.stalkHom z₁ (ι₀ x) = algebraMap X₁.o₁ X₁.Ω₁ x := by
      intro x
      rw [← RatModel.coe_stalkEquiv, hι₀, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
      rfl
    have hmemτ : ∀ τ : X₁.S.TT X₁.M z₁, algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ ∈
        X₁.M.O z₁ := by
      intro τ
      rw [mul_div_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hdiv.2 _)
    choose hτ hhτ using fun τ => (X₁.M.stalkEquiv z₁).surjective ⟨_, hmemτ τ⟩
    have hhτ' : ∀ τ, X₁.M.stalkHom z₁ (hτ τ) =
        algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := fun τ => by
      rw [← RatModel.coe_stalkEquiv, hhτ τ]
    have hzt : X₁.M.stalkHom z₁ (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) =
        algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := hι _
    set wt : X₁.S.TT X₁.M z₁ → X → ZMod (X₁.S.r * X₁.S.N) :=
      fun τ mu => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (A mu) with hwt
    have hS : ∀ τ : X₁.S.TT X₁.M z₁, SumI (maximalIdeal V)
        (fun mu => ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (wt τ mu).val * T mu c) (ev (hτ τ)) := fun τ =>
      hlink V ev X t δ 𝔪 C lab hlab T hT c τ τ.2 _ (hτ τ) hzt (hhτ' τ) (wt τ)
        (fun a' mu ha' => by simp only [hwt]; rw [hdiff a' mu ha' τ τ.2])
    have hhe : h = ∑ τ : X₁.S.TT X₁.M z₁, ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val) * hτ τ := by
      apply X₁.M.stalkHom_injective z₁
      rw [hh, map_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [(X₁.M.stalkHom z₁).map_mul, hι, hhτ']
    have hsum := sumI_sum (I := maximalIdeal V) Finset.univ
      (fun τ mu => ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) •
        (ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (wt τ mu).val * T mu c))
      (fun τ => ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) • ev (hτ τ)) (fun τ _ => sumI_smul _ (hS τ))
    have hev : ∑ τ ∈ Finset.univ, ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) • ev (hτ τ) = ev h := by
      rw [hhe, map_sum]
      exact Finset.sum_congr rfl fun τ _ => by simp only [smul_eq_mul, map_mul]
    rw [hev] at hsum
    set q := ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) with hq_def
    have hq : IsPrimitiveRoot q (X₁.S.r * X₁.S.N) :=
      isPrimitiveRoot_map (ev.comp ι₀) hm0 (X₁.S.prim.pow (by positivity) (sq _)) X₁.S.unit
    have hpt : ∀ mu, (∑ τ ∈ Finset.univ, ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) •
        (q ^ (wt τ mu).val * T mu c)) =
        ev (ι₀ u) * (∑ τ : X₁.S.TT X₁.M z₁, q ^ ((sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (A mu - a)).val) * T mu c := by
      intro mu
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have e1 : K a τ + wt τ mu = (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (A mu - a) := by
        simp only [hK, hwt, eStd_sub_right, smul_sub, neg_smul]
        abel
      rw [← e1, ← pow_val_mul_pow_val hq.pow_eq_one, smul_eq_mul]
      rw [map_mul ι₀, map_mul ev, map_pow ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)), map_pow ev (ι₀ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))),
        ← hq_def]
      ring
    have hchar : ∀ d : X₁.S.Gam, (∑ τ : X₁.S.TT X₁.M z₁, q ^ ((sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) d).val) =
        if d ∈ X₁.S.HH X₁.M z₁ then (Nat.card (X₁.S.TT X₁.M z₁) : V) else 0 := by
      intro d
      split_ifs with hd
      · have h0 : ∀ τ : X₁.S.TT X₁.M z₁, eStd X₁.S.g _ (τ : X₁.S.Gam) d = 0 := fun τ => τ.2 d hd
        simp [h0, Nat.card_eq_fintype_card]
      · have hd' : d ∉ X₁.S.perp (X₁.S.TT X₁.M z₁) := by
          rwa [show X₁.S.TT X₁.M z₁ = X₁.S.perp (X₁.S.HH X₁.M z₁) from rfl, TestBasis.perp_perp]
        have hex' : ∃ τ ∈ X₁.S.TT X₁.M z₁, eStd X₁.S.g _ d τ ≠ 0 := by
          by_contra hc
          push_neg at hc
          exact hd' hc
        obtain ⟨τ₀, hτ₀, h₀⟩ := hex'
        have h₀' : eStd X₁.S.g _ τ₀ d ≠ 0 := by
          rw [Weights.eStd_swap]; exact neg_ne_zero.2 h₀
        refine sum_pow_val_eq_zero hq (fun τ : X₁.S.TT X₁.M z₁ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) d)
          (fun x y => by simp only [AddSubgroup.coe_add, eStd_add_left, smul_add]) ⟨τ₀, hτ₀⟩ ?_
        rcases Int.units_eq_one_or sg with hs | hs <;> simpa [hs] using h₀'
    have hucard : ev (ι₀ u) * (Nat.card (X₁.S.TT X₁.M z₁) : V) = 1 := by
      rw [← map_natCast ev (Nat.card _), ← map_mul, ← map_natCast ι₀ (Nat.card _), ← map_mul, hu1, map_one, map_one]
    have hfam : ∀ mu, (∑ τ ∈ Finset.univ, ev (ι₀ (u * (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (K a τ).val)) •
        (q ^ (wt τ mu).val * T mu c)) = if A mu - a ∈ X₁.S.HH X₁.M z₁ then T mu c else 0 := by
      intro mu
      rw [hpt, hchar]
      split_ifs
      · rw [hucard, _root_.one_mul]
      · simp
    have hin : ∀ nu : X, A (κ + (X₁.S.r * X₁.S.N) • nu) - a ∈ X₁.S.HH X₁.M z₁ := by
      intro nu
      refine (hint _).2 ((hcong _ _ 0 (hsub _ _ _ _ (hA _) hκ)).2 ⟨-nu, ?_⟩)
      simp
    have hinj : Function.Injective fun nu : X => κ + (X₁.S.r * X₁.S.N) • nu := by
      intro nu nu' he
      have h1 : (X₁.S.r * X₁.S.N) • nu = (X₁.S.r * X₁.S.N) • nu' := add_left_cancel he
      apply 𝔪.e₈.injective
      have h2 : ((X₁.S.r * X₁.S.N : ℕ) : ℤ) • (𝔪.e₈ nu - 𝔪.e₈ nu') = 0 := by
        rw [natCast_zsmul, smul_sub, ← map_nsmul, ← map_nsmul, h1, sub_self]
      rw [smul_eq_zero] at h2
      exact sub_eq_zero.1 (h2.resolve_left (by exact_mod_cast hm0.ne'))
    have key := sumI_comp hinj (fun mu hmu => ?_) hsum
    · simp only [hfam, hin, ite_true] at key
      exact key
    · rw [hfam, if_neg]
      intro hd
      apply hmu
      have h1 := (hcong _ _ 0 (hsub _ _ _ _ (hA mu) hκ)).1 ((hint _).1 hd)
      obtain ⟨w, h2⟩ := h1
      refine ⟨-w, ?_⟩
      simp only [smul_neg]
      calc κ + -((X₁.S.r * X₁.S.N) • w) = κ + -((X₁.S.r * X₁.S.N) • w) + (mu - κ + (X₁.S.r * X₁.S.N) • w) := by
            rw [← h2, add_zero]
        _ = mu := by abel

end GlobalTheory.GSep.ClassSumFun
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_class_sum_functions_theta_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ f : X₁.S.Gam → X₁.S.Gam → X₁.Ω₁, (∀ a b, ∀ w : X₁.M.Z, X₁.M.Div X₁.S.th x₀ w → f a b ∈ X₁.M.O w) ∧ (∀ a a' b, a - a' ∈ X₁.S.HH X₁.M z₁ → f a b = f a' b) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C) (a : X₁.S.Gam) (κ : X), 𝔪.YY a κ → ∀ h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ h = f a (lab c) → SumI (maximalIdeal V) (fun nu : X => T (κ + (X₁.S.r * X₁.S.N) • nu) c) (ev h) := by
  atlas_forward_decl GlobalTheory.GSep.ClassSumFun.exists_classSum_fun
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelStalk_normal_noetherian_fractionRing : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.GSep.stalk_isNoetherian_normal_fractionRing <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.GSep.DeepSums

theorem congMod_of_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {L d : ℕ} (hd : 0 < d) {x y : X}
    (h : CongMod (L * d) (d • x) (d • y)) : CongMod L x y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  have hd' : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  apply smul_right_injective X hd'
  simp only [natCast_zsmul, smul_add]
  rw [hw, mul_comm, mul_nsmul]
  congr 1
  exact smul_comm _ _ _

theorem congMod_fin_one {X : Type} [AddCommGroup X] {N : ℕ} {κ κ' : Fin 1 → X} (h : ∀ v, CongMod N (κ v) (κ' v)) :
    CongMod N κ κ' := by
  obtain ⟨w, hw⟩ := h 0
  refine ⟨fun _ => w, funext fun v => ?_⟩
  rw [Subsingleton.elim v 0]
  simpa using hw

theorem sumI_smul {R E Ix : Type} [CommRing R] {I : Ideal R} [AddCommGroup E] [Module R E] (c : R) {x : Ix → E} {s : E}
    (hx : SumI I x s) : SumI I (fun i => c • x i) (c • s) := by
  obtain ⟨N, f, hs, hxN, h⟩ := hx
  refine ⟨N, f, N.smul_mem c hs, fun i => N.smul_mem c (hxN i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.smul_sum, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ c (hS T hT)

def one {A B : Type} [AddCommGroup A] [AddCommGroup B] (K : (Fin 1 → A) ≃+ (Fin 1 → B)) : A ≃+ B :=
  ((LinearEquiv.funUnique (Fin 1) ℤ A).toAddEquiv.symm.trans K).trans (LinearEquiv.funUnique (Fin 1) ℤ B).toAddEquiv

theorem one_apply {A B : Type} [AddCommGroup A] [AddCommGroup B] (K : (Fin 1 → A) ≃+ (Fin 1 → B)) (x : A) :
    one K x = K (fun _ => x) 0 := rfl

theorem apply_eq_one {A B : Type} [AddCommGroup A] [AddCommGroup B] (K : (Fin 1 → A) ≃+ (Fin 1 → B)) (κ : Fin 1 → A) :
    K κ = fun v => one K (κ v) := by
  funext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  have e : κ = fun _ => κ 0 := funext fun v => by rw [Subsingleton.elim v 0]
  rw [one_apply]
  exact congrArg (fun z => K z 0) e

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem yy_sub_zero (𝔪 : GMem X₁ z₁ act V ev X t δ) {a a' : X₁.S.Gam} {κ κ' : X} (h : 𝔪.YY a κ)
    (h' : 𝔪.YY a' κ') (hc : CongMod (X₁.S.r * X₁.S.N) κ κ') : 𝔪.YY (a - a') 0 := by
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨mu, hmu⟩ := h1 (a - a')
  have hs := h4 _ _ _ _ hmu h'
  rw [sub_add_cancel] at hs
  have hc2 := (h3 a κ (mu + κ') h).1 hs
  refine (h3 _ mu 0 hmu).2 ?_
  obtain ⟨w1, hw1⟩ := hc2
  obtain ⟨w2, hw2⟩ := hc
  refine ⟨-(w1 + w2), ?_⟩
  have e : mu = (X₁.S.r * X₁.S.N) • w1 + (X₁.S.r * X₁.S.N) • w2 := by
    have h5 : mu = mu + κ' - κ' := by abel
    rw [h5, hw1, hw2]
    abel
  rw [e, smul_neg, smul_add]
  abel

theorem yy_nsmul (𝔪 : GMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} {κ : X} (h : 𝔪.YY a κ) (d : ℕ) :
    𝔪.YY (d • a) (d • κ) := by
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  induction d with
  | zero =>
    have := yy_sub_zero 𝔪 h h ⟨0, by simp⟩
    rw [sub_self] at this
    rwa [zero_nsmul, zero_nsmul]
  | succ d ih =>
    rw [succ_nsmul, succ_nsmul]
    exact h4 _ _ _ _ ih h

theorem comap_maximalIdeal_of_isLocalHom {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R := by
  ext x
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f x]

theorem isLocalHom_comp_equiv {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) [IsLocalHom f]
    (e : R ≃+* S) : IsLocalHom (f.comp e.toRingHom) :=
  ⟨fun a ha => by
    have h1 : IsUnit (e a) := IsLocalHom.map_nonunit (f := f) _ ha
    simpa using h1.map e.symm.toRingHom⟩

end GlobalTheory.GSep.DeepSums

namespace GlobalTheory.GSep.DeepSums

open Classical in

theorem classSums_deeper : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (W : Matrix (Fin 1) (Fin 1) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → GlobalTheory.GSep.Deep X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  intro O _ bar q W X₁ z₁ act hact hdeep hunit x₀ Φ lab _ hgeo
  obtain ⟨hdiv, hrange, hmem⟩ := hgeo
  choose 𝔪 h𝔪 using hmem
  intro y₀ N₀
  obtain ⟨𝔗, hN₀⟩ := hdeep N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨-, hfr, -, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  haveI := hfr
  letI algAL : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨algFL, tower, hfd, hgal, hfix⟩ :=
    GlobalTheory.finiteGalois_fractionRing_of_isFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ 𝔗.X₂.Ω₁ (fun _ => rfl)
  obtain ⟨z₂, j₂, hz₂, hj₂, hmax, hint, hσ₂, hinj⟩ := GlobalTheory.T.exists_deeperPoint_integralClosure_stalk O X₁ act 𝔗 z₁
  have hdiv₂ : ∀ w, 𝔗.p w = z₁ → 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) w := fun w hw =>
    (GlobalTheory.T.deeperModel_dividing_label_and_shifts_preserved O X₁ z₁ act hact hunit 𝔗 w hw x₀ hdiv (Φ.V y₀) (Φ.ev y₀) _ _ _ (𝔪 y₀)).1
  have hlab : ∀ c, 𝔗.lam (lab c) ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := fun c =>
    (GlobalTheory.T.deeperModel_dividing_label_and_shifts_preserved O X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hdiv (Φ.V y₀) (Φ.ev y₀) _ _ _ (𝔪 y₀)).2 _
      (by rw [← SetLike.mem_coe, ← hrange]; exact ⟨c, rfl⟩)
  obtain ⟨f₂, hf₂O, hf₂per, hf₂sum⟩ := GlobalTheory.T.exists_class_sum_functions_theta_members O 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂)
  obtain ⟨eps, hsbc⟩ := GlobalTheory.T.exists_galoisTower_baseChange_thetaMember O X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv

  set L₂ := 𝔗.X₂.S.r * 𝔗.X₂.S.N with hL₂
  have hL₂pos : 1 ≤ L₂ := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  set ζ₂ : 𝔗.X₂.Ω₁ := algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ with hζ₂
  have hζO : ∀ w, ζ₂ ∈ 𝔗.X₂.M.O w := fun w => Subalgebra.algebraMap_mem _ _
  have hsurj : ∀ x ∈ 𝔗.X₂.M.O z₂, ∃ h, 𝔗.X₂.M.stalkHom z₂ h = x := fun x hx =>
    let ⟨h, hh⟩ := (𝔗.X₂.M.stalkEquiv z₂).surjective ⟨x, hx⟩
    ⟨h, by rw [← RatModel.coe_stalkEquiv, hh]⟩
  obtain ⟨zt, hzt⟩ := hsurj ζ₂ (hζO z₂)
  have hztM : zt ^ (L₂ ^ 2) = 1 := 𝔗.X₂.M.stalkHom_injective z₂ (by
    rw [map_pow, hzt, map_one, hζ₂, ← map_pow, 𝔗.X₂.S.prim.pow_eq_one, map_one])
  set M := L₂ ^ 2 with hM
  have hMpos : 1 ≤ M := Nat.one_le_pow _ _ hL₂pos
  let Fv : 𝔗.X₂.S.Gam → Φ.Q → 𝔗.X₂.Ω₁ := fun a c => ζ₂ ^ ((M - 1) * eps (lab c)) * f₂ a (𝔗.lam (lab c))
  have hFB : ∀ a c, Fv a c ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := fun a c =>
    hint _ fun w hw => mul_mem (pow_mem (hζO w) _) (hf₂O _ _ w (hdiv₂ w hw))
  have hunitV : ∀ {V : Type} [CommRing V] (e : X₁.M.Z.presheaf.stalk z₁ →+* V) (m : ℕ), m ≠ 0 → IsUnit (m : V) :=
    fun e m hm => by simpa using (hunit m hm).map e
  have hext : ∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : Φ.V y →+* V')
      (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧
        (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧ 𝔗.Ext (Φ.ev y) io ev₂ := fun y =>
    GlobalTheory.T.exists_centred_pure_extension_tower_member O X₁ z₁ act hact 𝔗 z₂ hz₂ (Φ.V y) (Φ.ev y) (hunitV (Φ.ev y)) (Φ.cn y) (Φ.ev_loc y) (𝔪 y).reg
  choose V' iR iD iL io ev₂ hcn hioi hiof hiol hioI hExt using hext
  have hmem₂ := fun y => hsbc (Φ.V y) (Φ.ev y) _ _ _ (𝔪 y) Φ.Q lab (Φ.term y) (h𝔪 y)
    (V' y) (io y) (hcn y) (hioi y) (hiof y)
  choose 𝔪₂ h𝔪₂T h𝔪₂G using hmem₂

  let M₂ := fun y => 𝔪₂ y (ev₂ y) (hExt y)
  have hyy := fun y => GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O 𝔗.X₂ z₂ 𝔗.act₂ (V' y) (ev₂ y) _ _ _ (M₂ y)
  have hint₂ := fun y => GlobalTheory.T.mem_dividingLabels_iff_class_zero O 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) (hdiv₂ z₂ hz₂) (V' y) (ev₂ y) _ _ _ (M₂ y)
  have hK := fun y => GlobalTheory.T.exists_labelPreserving_latticeIso_of_members O 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct (V' y₀) (ev₂ y₀) _ _ _ (M₂ y₀) (V' y) (ev₂ y) _ _ _ (M₂ y)
  choose K hKlin hKyy using hK
  let kk : ∀ y, Φ.X y₀ ≃+ Φ.X y := fun y => if h : y₀ = y then h ▸ AddEquiv.refl (Φ.X y₀) else one (K y)
  have hkk₀ : kk y₀ = AddEquiv.refl _ := by simp [kk]
  have hkk : ∀ y a κ, (M₂ y₀).YY a κ → (M₂ y).YY a (fun u => kk y (κ u)) := by
    intro y a κ h
    by_cases hy : y₀ = y
    · subst hy
      rw [hkk₀]
      exact h
    · have := hKyy y a κ h
      rw [apply_eq_one] at this
      simpa [kk, hy] using this
  have hklin : ∀ y (c : O) x, kk y (c • x) = c • kk y x := by
    intro y c x
    by_cases hy : y₀ = y
    · subst hy
      rw [hkk₀]
      rfl
    · have := congrFun (hKlin y c (fun _ => x)) 0
      simp only [kk, hy, dif_neg, not_false_eq_true, one_apply]
      exact this
  choose aκ haκ using (hyy y₀).2.1
  have hper : ∀ κ κ' c, (∀ v, CongMod L₂ (κ v) (κ' v)) → Fv (aκ κ) c = Fv (aκ κ') c := by
    intro κ κ' c h
    have h0 := yy_sub_zero (M₂ y₀) (haκ κ) (haκ κ') (congMod_fin_one h)
    simp only [Fv]
    rw [hf₂per _ _ _ ((hint₂ y₀ _).2 h0)]
  refine ⟨L₂, hN₀, hL₂pos, ⟨𝔗.d, 𝔗.lev⟩, fun y => (kk y).toIntLinearEquiv.toLinearMap, ?_, ?_,
    𝔗.X₂.Ω₁, inferInstance, algFL, algAL, tower, hfd, hgal, (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂,
    fun κ c => ⟨Fv (aκ κ) c, hFB _ _⟩, hmax, fun κ κ' c h => Subtype.ext (hper κ κ' c h), ?_, ?_⟩
  · show (kk y₀).toIntLinearEquiv.toLinearMap = LinearMap.id
    rw [hkk₀]; rfl
  · intro y
    refine ⟨fun c x => ⟨0, ?_⟩, (kk y).symm.toIntLinearEquiv, ?_⟩
    · rw [smul_zero, add_zero]
      exact hklin y c x
    · have : ((kk y).symm.toIntLinearEquiv.toLinearMap ∘ₗ (kk y).toIntLinearEquiv.toLinearMap) = LinearMap.id := by
        ext x; simp
      rw [this, LinearMap.det_id, sub_self]
      exact dvd_zero _
  · intro y
    have hzu : IsUnit (ev₂ y zt) := by
      exact IsUnit.of_pow_eq_one (n := M) (by rw [← map_pow, hztM, map_one]) (by omega)
    refine ⟨V' y, inferInstance, inferInstance, io y, (ev₂ y).comp j₂, hiof y, hiol y, hioI y, ?_, ?_, ?_⟩
    · ext x
      exact (hExt y).2 x _ (by rw [hj₂]; rfl)
    · haveI := (hExt y).1
      rw [← Ideal.comap_comap, comap_maximalIdeal_of_isLocalHom]
    · intro κ c
      obtain ⟨h, hh⟩ := hsurj _ (hf₂O (aκ κ) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      have hs := hf₂sum (V' y) (ev₂ y) _ _ _ (M₂ y) Φ.Q (fun c => 𝔗.lam (lab c)) hlab
        (fun mu c => ev₂ y zt ^ eps (lab c) * io y (Φ.term y mu c)) (h𝔪₂T y (ev₂ y) (hExt y) zt hzt) c (aκ κ) _
        (hkk y _ κ (haκ κ)) h hh
      let e : (V' y)ˣ := hzu.unit ^ eps (lab c)
      have hcs := GlobalTheory.Poinc.isClassSum_of_sumI O bar q 1 W _ Φ y L₂ hL₂pos (fun v => kk y (κ v)) c (V' y) (io y) e
        (ev₂ y h) (by convert hs using 3; simp [e])
      have hj : j₂ ⟨Fv (aκ κ) c, hFB _ _⟩ = zt ^ ((M - 1) * eps (lab c)) * h := 𝔗.X₂.M.stalkHom_injective z₂ (by
        rw [hj₂, map_mul, map_pow, hzt, hh])
      have hval : ((ev₂ y).comp j₂) ⟨Fv (aκ κ) c, hFB _ _⟩ = ↑e⁻¹ * ev₂ y h := by
        rw [RingHom.comp_apply, hj, map_mul, map_pow]
        congr 1
        refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
        have hMe : eps (lab c) + (M - 1) * eps (lab c) = M * eps (lab c) := by
          have h1 : M - 1 + 1 = M := by omega
          calc eps (lab c) + (M - 1) * eps (lab c) = (M - 1 + 1) * eps (lab c) := by ring
            _ = M * eps (lab c) := by rw [h1]
        rw [show (e : V' y) = ev₂ y zt ^ eps (lab c) by simp [e], ← pow_add, hMe, pow_mul, ← map_pow, hztM, map_one,
          one_pow]
      convert hcs using 1 <;> first | exact hval | rfl
  · intro σ hσ
    let σ' : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hfix σ x)
    obtain ⟨σ₂, hσ₂'⟩ := hσ₂ σ' (fun b b' hb => by
      have := hσ b b' hb
      simpa only [Ideal.mem_comap] using this)
    have hExtσ : ∀ {V V' : Type} [CommRing V] [CommRing V'] [IsLocalRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
        (io : V →+* V') (e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), 𝔗.Ext ev io e₂ →
        𝔗.Ext ev io (e₂.comp σ₂.toRingHom) := by
      intro V V' _ _ _ ev io e₂ he
      haveI := he.1
      refine ⟨isLocalHom_comp_equiv e₂ σ₂, fun x x₂ hx => he.2 x (σ₂ x₂) ?_⟩
      rw [hσ₂', hx]
      exact σ'.commutes _
    have hgl : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) {X : Type}
        [AddCommGroup X] {t : X → V} {δ : O → X → X}
        {V' : Type} [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V')
        (𝔫 : ∀ e₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io e₂ →
          GMem 𝔗.X₂ z₂ 𝔗.act₂ V' e₂ X (fun k => io (t k)) δ),
        (∀ e₂ h e₂' h' (τ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁),
          (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = τ (𝔗.X₂.M.stalkHom z₂ x) → e₂' x = e₂ x') →
          (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = τ (𝔗.X₂.M.stalkHom z₂ x)) →
          ∀ a mu, (𝔫 e₂' h').YY a mu ↔ (𝔫 e₂ h).YY (𝔗.gl τ a) mu) →
        ∀ e₂ (h : 𝔗.Ext ev io e₂) a mu,
          (𝔫 (e₂.comp σ₂.toRingHom) (hExtσ ev io e₂ h)).YY a mu ↔ (𝔫 e₂ h).YY (𝔗.gl σ' a) mu := by
      intro V _ _ _ ev X _ t δ V' _ _ _ io 𝔫 hG e₂ h a mu
      refine hG e₂ h _ _ σ' (fun x x' hx => ?_) (fun x => ⟨σ₂ x, hσ₂' x⟩) a mu
      simp only [RingHom.comp_apply]
      congr 1
      exact 𝔗.X₂.M.stalkHom_injective z₂ (by show 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = _; rw [hσ₂', hx])
    have hext₀ := hExtσ (Φ.ev y₀) (io y₀) (ev₂ y₀) (hExt y₀)
    obtain ⟨Kσ, hKσlin, hKσyy⟩ := GlobalTheory.T.exists_labelPreserving_latticeIso_of_members O 𝔗.X₂ z₂ 𝔗.act₂ 𝔗.isAct
      (V' y₀) (ev₂ y₀) _ _ _ (M₂ y₀) (V' y₀) ((ev₂ y₀).comp σ₂.toRingHom) _ _ _
      (𝔪₂ y₀ ((ev₂ y₀).comp σ₂.toRingHom) hext₀)
    let gk : Φ.X y₀ ≃+ Φ.X y₀ := one Kσ
    have hga : ∀ a κ, (M₂ y₀).YY a κ → (M₂ y₀).YY (𝔗.gl σ' a) (fun u => gk (κ u)) := fun a κ h => by
      have := hKσyy a κ h
      rw [apply_eq_one] at this
      exact (hgl (Φ.ev y₀) (io y₀) (𝔪₂ y₀) (h𝔪₂G y₀) (ev₂ y₀) (hExt y₀) a _).1 this
    have hL₁ : 3 ≤ X₁.S.r * X₁.S.N := by
      obtain ⟨k, hk⟩ := GlobalTheory.ZH.TestVal.odd_level X₁.ρ
      have := Nat.mul_le_mul X₁.S.r_pos X₁.S.N_ge
      omega
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (gk x) x := by
      intro x
      obtain ⟨a', ha'⟩ := (hyy y₀).2.1 (fun _ => x)
      have h1 := yy_nsmul (M₂ y₀) ha' 𝔗.d
      obtain ⟨a'', ha''⟩ := 𝔗.lam_range a'
      rw [← ha''] at h1
      have h2 := hga _ _ h1
      rw [𝔗.gl_lam] at h2
      obtain ⟨w, hw⟩ := ((hyy y₀).2.2.1 _ _ _ h1).1 h2
      have h3 := congrFun hw 0
      simp only [Pi.smul_apply, map_nsmul, Pi.add_apply] at h3
      exact congMod_of_nsmul 𝔗.d_pos ⟨w 0, by rw [← 𝔗.lev]; exact h3⟩
    have hdet : LinearMap.det (gk.toIntLinearEquiv : Φ.X y₀ →ₗ[ℤ] Φ.X y₀) = 1 :=
      GlobalTheory.Poinc.det_eq_one_of_congMod (Φ.X y₀) gk _ hL₁ hcong
    have hFσ : ∀ a c, σ' (Fv a c) = Fv (𝔗.gl σ' a) c := by
      obtain ⟨Vr, _, _, _, evr, Xr, _, tr, δr, hevr, ⟨𝔪r⟩⟩ := GlobalTheory.T.exists_thetaMember_injective_evaluation O X₁ z₁ act hact
      obtain ⟨ur, hur, -, -⟩ := GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift O X₁ z₁ act x₀ hdiv Vr evr Xr tr δr 𝔪r Φ.Q lab hrange
      obtain ⟨Vr', _, _, _, ior, evr₂, hcnr, hior, hiorf, -, -, hExtr⟩ := GlobalTheory.T.exists_centred_pure_extension_tower_member O X₁ z₁ act hact 𝔗 z₂ hz₂
        Vr evr (hunitV evr) 𝔪r.cn 𝔪r.loc 𝔪r.reg
      have hinjr : Function.Injective evr₂ := hinj Vr evr Vr' ior evr₂ hevr hior hExtr
      obtain ⟨𝔫, h𝔫T, h𝔫G⟩ := hsbc Vr evr Xr tr δr 𝔪r Φ.Q lab _ hur Vr' ior hcnr hior hiorf
      haveI : IsNoetherianRing Vr' := hcnr.1
      intro a c
      have hextr := hExtσ evr ior evr₂ hExtr
      obtain ⟨mu, hmu⟩ := (GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O 𝔗.X₂ z₂ 𝔗.act₂ Vr' _ Xr _ _ (𝔫 _ hextr)).1 a
      have hmu' := (hgl evr ior 𝔫 h𝔫G evr₂ hExtr a mu).1 hmu
      obtain ⟨h, hh⟩ := hsurj _ (hf₂O a (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      obtain ⟨h', hh'⟩ := hsurj _ (hf₂O (𝔗.gl σ' a) (𝔗.lam (lab c)) z₂ (hdiv₂ z₂ hz₂))
      have s1 := hf₂sum Vr' _ Xr _ _ (𝔫 _ hextr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hextr zt hzt) c a mu
        hmu h hh
      have s2 := hf₂sum Vr' _ Xr _ _ (𝔫 _ hExtr) Φ.Q (fun c => 𝔗.lam (lab c)) hlab _ (h𝔫T _ hExtr zt hzt) c
        (𝔗.gl σ' a) mu hmu' h' hh'
      have key : ∀ (u : Vr'), u ^ M = 1 → ∀ (x : Vr'), u ^ ((M - 1) * eps (lab c)) • (u ^ eps (lab c) * x) = x := by
        intro u hu x
        have h1 : (M - 1) * eps (lab c) + eps (lab c) = M * eps (lab c) := by
          have h2 : M - 1 + 1 = M := by omega
          calc (M - 1) * eps (lab c) + eps (lab c) = (M - 1 + 1) * eps (lab c) := by ring
            _ = M * eps (lab c) := by rw [h2]
        rw [smul_eq_mul, ← _root_.mul_assoc, ← pow_add, h1, pow_mul, hu, one_pow, _root_.one_mul]
      have t1 := sumI_smul ((evr₂ (σ₂ zt)) ^ ((M - 1) * eps (lab c))) s1
      have t2 := sumI_smul ((evr₂ zt) ^ ((M - 1) * eps (lab c))) s2
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at t1
      have hu1 : (evr₂ (σ₂ zt)) ^ M = 1 := by rw [← map_pow, ← map_pow, hztM, map_one, map_one]
      have hu2 : (evr₂ zt) ^ M = 1 := by rw [← map_pow, hztM, map_one]
      simp only [key _ hu1, key _ hu2] at t1 t2
      have heq := GlobalTheory.Poinc.sumI_maximalIdeal_unique Vr' _ _ _ _ t1 t2
      have heq' : σ₂ (zt ^ ((M - 1) * eps (lab c)) * h) = zt ^ ((M - 1) * eps (lab c)) * h' :=
        hinjr (by simpa only [map_mul, map_pow, smul_eq_mul] using heq)
      have := congrArg (𝔗.X₂.M.stalkHom z₂) heq'
      rw [hσ₂'] at this
      simp only [map_mul, map_pow, hzt, hh, hh'] at this
      simp only [Fv, map_mul, map_pow]
      exact this
    refine ⟨gk.toIntLinearEquiv.toLinearMap, fun b x => ⟨0, ?_⟩, ?_, hcong, fun κ c => ?_⟩
    · rw [smul_zero, add_zero]
      exact congrFun (hKσlin b (fun _ => x)) 0
    · rw [hdet, sub_self]
      exact dvd_zero _
    · show σ (Fv (aκ κ) c) = Fv (aκ (fun v => gk (κ v))) c
      have e1 : σ (Fv (aκ κ) c) = σ' (Fv (aκ κ) c) := rfl
      rw [e1, hFσ]
      simp only [Fv]
      rw [hf₂per _ _ _ ((hint₂ y₀ _).2 (yy_sub_zero (M₂ y₀) (hga _ _ (haκ κ)) (haκ _) ⟨0, by rw [smul_zero, add_zero]⟩))]

end GlobalTheory.GSep.DeepSums
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_class_sums_unbounded_levels_one_index : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (W : Matrix (Fin 1) (Fin 1) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → GlobalTheory.GSep.Deep X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  atlas_forward_decl GlobalTheory.GSep.DeepSums.classSums_deeper
end
