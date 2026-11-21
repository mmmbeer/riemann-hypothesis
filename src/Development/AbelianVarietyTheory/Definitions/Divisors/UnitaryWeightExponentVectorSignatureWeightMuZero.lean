import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppLEInjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

section
noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Glue

theorem exists_algHom_of_comp {K S A B : Type} [CommRing K] [CommRing S] [Algebra K S] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (f : S →ₐ[K] A) (g : S →ₐ[K] B) (χ : A →+* B) (h : ∀ r, χ (f r) = g r) :
    ∃ χ' : A →ₐ[K] B, (∀ a, χ' a = χ a) ∧ χ'.comp f = g :=
  ⟨{ χ with commutes' := fun r => by rw [← f.commutes, ← g.commutes]; exact h _ }, fun _ => rfl, AlgHom.ext h⟩

theorem glue_val {K S : Type} [CommRing K] [CommRing S] [Algebra K S] {Z : Scheme.{0}} (z : Sp S ⟶ Z) {J : Type}
    {U : J → Z.Opens} (hc : ⨆ k, U k = ⊤)
    (val : ∀ (S' : Type) [CommRing S'] [Algebra K S'] (ψ : S →ₐ[K] S') (k : J),
      ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k → S')
    (nat : ∀ (S' S'' : Type) [CommRing S'] [Algebra K S'] [CommRing S''] [Algebra K S''] (ψ : S →ₐ[K] S')
      (χ : S' →ₐ[K] S'') (k k' : J) (h : ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k)
      (h' : ⊤ ≤ (spMap (χ.comp ψ).toRingHom ≫ z) ⁻¹ᵁ U k'), val S'' (χ.comp ψ) k' h' = χ (val S' ψ k h)) :
    ∃! a : S, ∀ (S' : Type) [CommRing S'] [Algebra K S'] (ψ : S →ₐ[K] S') (k : J)
      (h : ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k), ψ a = val S' ψ k h := by
  let lo (f : S) : S →ₐ[K] Localization.Away f := IsScalarTower.toAlgHom K S (Localization.Away f)
  let t : Set S := {f | ∃ k, ⊤ ≤ (spMap (lo f).toRingHom ≫ z) ⁻¹ᵁ U k}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum S := ⟨m, hm.isPrime⟩
    have : z p ∈ ⨆ k, U k := by rw [hc]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ ((z ⁻¹ᵁ U k : (Sp S).Opens) : Set (Sp S)) from hk) (z ⁻¹ᵁ U k).isOpen
    refine hf (hle (Ideal.subset_span ⟨k, fun q _ => hsub ?_⟩))
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le ⟨q, rfl⟩
  have comp : ∀ {S' S'' : Type} [CommRing S'] [Algebra K S'] [CommRing S''] [Algebra K S''] (ψ : S →ₐ[K] S')
      (χ : S' →ₐ[K] S'') (k : J), ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k →
      ⊤ ≤ (spMap (χ.comp ψ).toRingHom ≫ z) ⁻¹ᵁ U k := fun ψ χ k h => by
    rw [show spMap (χ.comp ψ).toRingHom = spMap χ.toRingHom ≫ spMap ψ.toRingHom from (spMap_comp' _ _).symm,
      Category.assoc]
    exact le_preimage_comp _ h
  have vcongr : ∀ {S' : Type} [CommRing S'] [Algebra K S'] (ψ ψ' : S →ₐ[K] S') (e : ψ = ψ') k k' h h',
      val S' ψ k h = val S' ψ' k' h' := by
    intro S' _ _ ψ ψ' e k k' h h'
    subst e
    exact nat S' S' ψ (AlgHom.id K S') k' k h' h
  obtain ⟨a, ha, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top t ht
    (fun f => val _ (lo f.1) f.2.choose f.2.choose_spec) (fun f g => by
      obtain ⟨χ₁, h₁, e₁⟩ := exists_algHom_of_comp (K := K) (lo f.1) (lo (f.1 * g.1))
        (IsLocalization.Away.awayToAwayRight f.1 g.1) (fun r => IsLocalization.Away.awayToAwayRight_eq f.1 g.1 r)
      obtain ⟨χ₂, h₂, e₂⟩ := exists_algHom_of_comp (K := K) (lo g.1) (lo (f.1 * g.1))
        (IsLocalization.Away.awayToAwayLeft g.1 f.1) (fun r => IsLocalization.Away.awayToAwayLeft_eq g.1 f.1 r)
      have a1 := nat _ _ (lo f.1) χ₁ f.2.choose f.2.choose f.2.choose_spec (comp _ χ₁ _ f.2.choose_spec)
      have a2 := nat _ _ (lo g.1) χ₂ g.2.choose g.2.choose g.2.choose_spec (comp _ χ₂ _ g.2.choose_spec)
      rw [← h₁, ← h₂, ← a1, ← a2]
      exact vcongr _ _ (e₁.trans e₂.symm) _ _ _ _)
  refine ⟨a, fun S' _ _ ψ k h => ?_, fun b hb => hu b fun f => hb _ (lo f.1) _ _⟩
  have ht' : Ideal.span (ψ '' t) = ⊤ := by
    rw [← Ideal.map_span ψ t, ht, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ ht'
  funext ⟨_, f, hf, rfl⟩
  let lo' : S' →ₐ[K] Localization.Away (ψ f) := IsScalarTower.toAlgHom K S' _
  let χ : Localization.Away f →ₐ[K] Localization.Away (ψ f) := IsLocalization.Away.mapₐ _ _ ψ f
  have e : χ.comp (lo f) = lo'.comp ψ := AlgHom.ext fun r => by simp [χ, lo, lo', IsLocalization.Away.map]
  show lo' (ψ a) = lo' (val S' ψ k h)
  rw [← nat _ _ ψ lo' k k h (comp _ _ _ h), ← vcongr _ _ e _ _ (comp _ _ _ hf.choose_spec),
    nat _ _ _ χ _ _ hf.choose_spec, ← ha ⟨f, hf⟩]
  exact (congrArg (fun g : S →ₐ[K] _ => g a) e).symm

end Glue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

section ToModel

variable {S S' : Type} [CommRing S] [CommRing S']

variable (Y) in

def liftTan (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt (y ≫ pullback.fst _ _) w) :
    Sp (DualNumber S) ⟶ Y.oF.t.G.left :=
  Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ y) (by rw [hw.1, Category.assoc])

theorem liftTan_univ (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt (y ≫ pullback.fst _ _) w) : liftTan Y y hw ≫ Y.m0.toSABMap.φ = w := Y.m0.cart.1.lift_fst _ _ _

theorem liftTan_over (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt (y ≫ pullback.fst _ _) w) :
    liftTan Y y hw ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y := Y.m0.cart.1.lift_snd _ _ _

theorem isTanAtG_liftTan (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt (y ≫ pullback.fst _ _) w) : IsTanAtG Y.t (y ≫ Y.j) (liftTan Y y hw ≫ Y.m.φ) := by
  have h1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ liftTan Y y hw = (1 : Over.mk y ⟶ Y.oF.t.G).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, liftTan_univ, hw.2]
      exact grpPull_one Y.m0.cart (Over.mk y)
    · have hid : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
        RingHom.ext fun r => by simp
      rw [Category.assoc, liftTan_over, ← Category.assoc, spMap_comp', hid, Over.w]
      exact (congrArg (· ≫ y) (Spec.map_id _)).trans (Category.id_comp _)
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Y.m.cart.1.w, ← Category.assoc, liftTan_over, Category.assoc]
    rfl
  · rw [← Category.assoc, h1]
    exact (grpPull_one Y.m.cart (Over.mk y)).symm

variable (Y) in

def toModel (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) : TanM x Y.t.G :=
  mkT (ovT (t := Y.t) (v := liftTan Y y (h₀ ▸ hw) ≫ Y.m.φ) (hx ▸ isTanAtG_liftTan y (h₀ ▸ hw))) (smT_zero_ovT _)

theorem toModel_left (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) :
    (tv (toModel Y y h₀ hx hw)).left = liftTan Y y (h₀ ▸ hw) ≫ Y.m.φ := rfl

theorem toModel_eq_iff (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) (v : TanM x Y.t.G) :
    toModel Y y h₀ hx hw = v ↔ ∃ u : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
      u ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y ∧ u ≫ Y.m0.toSABMap.φ = w ∧
        u ≫ Y.m.φ = (tv v).left := by
  constructor
  · rintro rfl
    exact ⟨_, liftTan_over _ _, liftTan_univ _ _, rfl⟩
  · rintro ⟨u, h1, h2, h3⟩
    apply tan_ext_left
    rw [toModel_left, ← h3]
    congr 1
    exact Y.m0.cart.1.hom_ext ((liftTan_univ _ _).trans h2.symm) ((liftTan_over _ _).trans h1.symm)

theorem toModel_injective (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) (hw' : IsTanAt x₀ w')
    (e : toModel Y y h₀ hx hw = toModel Y y h₀ hx hw') : w = w' := by
  have h : liftTan Y y (h₀ ▸ hw) = liftTan Y y (h₀ ▸ hw') :=
    Y.m.cart.1.hom_ext (congrArg (fun v => (tv v).left) e) ((liftTan_over _ _).trans (liftTan_over _ _).symm)
  exact (liftTan_univ y _).symm.trans ((congrArg (· ≫ Y.m0.toSABMap.φ) h).trans (liftTan_univ y _))

theorem tanPull_toModel (φ : S →+* S') (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀)
    {x : Sp S ⟶ Y.X} (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w)
    {y' : Sp S' ⟶ Xo.XF c} (ey : spMap φ ≫ y = y') {x₀' : Sp S' ⟶ Xo.X} (h₀' : y' ≫ pullback.fst _ _ = x₀')
    {x' : Sp S' ⟶ Y.X} (hx' : y' ≫ Y.j = x') (e : spMap φ ≫ x = x') {w' : Sp (DualNumber S') ⟶ Xo.univ.t.G.left}
    (hw' : IsTanAt x₀' w') (ew : w' = spMap (dualMap φ) ≫ w) :
    tanPull φ e (toModel Y y h₀ hx hw) = toModel Y y' h₀' hx' hw' := by
  refine ((toModel_eq_iff y' h₀' hx' hw' _).2 ⟨spMap (dualMap φ) ≫ liftTan Y y (h₀ ▸ hw), ?_, ?_, ?_⟩).symm
  · rw [Category.assoc, liftTan_over, ← ey, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp',
      dualMap_comp_alg]
  · rw [Category.assoc, liftTan_univ, ew]
  · rw [Category.assoc]; rfl

variable [Algebra c.F S]

theorem xF_ext {y y' : Sp S ⟶ Xo.XF c} (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S))
    (hy' : y' ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (e : y ≫ Y.j = y' ≫ Y.j) : y = y' := by
  have := Y.jQ_open
  rw [← cancel_mono Y.jQ]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]; exact e
  · rw [Category.assoc, Category.assoc, Y.jQ_over, hy, hy']

theorem vec_iff_toModel {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {x₀ : Sp S ⟶ Xo.X}
    (Λ : M.Lift (ev x M.U h) x₀) {y : Sp S ⟶ Xo.XF c} (ey : Λ.xF = y) (h₀ : y ≫ pullback.fst _ _ = x₀)
    (hx : y ≫ Y.j = x) (cv : Fin M.n → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) :
    Λ.Vec cv w ↔ toModel Y y h₀ hx hw = vec M x h cv := by
  have fwd : ∀ w (hw : IsTanAt x₀ w), Λ.Vec cv w → toModel Y y h₀ hx hw = vec M x h cv := by
    rintro _ hw ⟨v', u', h1, h2, rfl⟩
    refine (toModel_eq_iff y h₀ hx hw _).2 ⟨u'.left ≫ Λ.m'.φ, ?_, ?_, ?_⟩
    · rw [Category.assoc, Λ.m'.cart.1.w, ← Category.assoc, Over.w, ey]; rfl
    · rw [Category.assoc, ← Λ.liftedChartMap_eq]
    · rw [Category.assoc, ← Λ.matrix_two_by_two_congr]
      have e := congrArg (fun V => V.left) ((PullbackSections.isLieComb_iff Λ.m2.cart cv v' u').1 h2)
      refine e.trans ?_
      have hid : spMap (RingHom.id S) ≫ x = spMap (ev x M.U h) ≫ M.hU.fromSpec :=
        ((congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)).trans (spMap_ev x M.hU h).symm
      have hl : ∀ v : TanM x Y.t.G, (tv (tanPull (RingHom.id S) hid v)).left = (tv v).left := fun v =>
        (congrArg (· ≫ (tv v).left) (GlobalTheory.ModelChart.spMap_dualMapR_id S)).trans (Category.id_comp _)
      rw [← hl, vec_apply, map_sum, tv_sum']
      refine congrArg Over.Hom.left (Finset.prod_congr rfl fun j _ => ?_)
      rw [map_smulₛₗ, PullbackSections.tv_smul]
      congr 1
      apply Over.OverMorphism.ext
      rw [hl, lieBasis_left]
      exact h1 j
  refine ⟨fwd w hw, fun e => ?_⟩
  obtain ⟨b1, b2, -⟩ := vec_bijective E H Dw l Xo c O β Y M S _ x₀ Λ
  obtain ⟨w', hw', -⟩ := b1 cv
  rwa [toModel_injective y h₀ hx hw (b2 _ _ hw') (e.trans (fwd w' _ hw').symm)]

def frX (P : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift P.x (spMap (algebraMap c.F S)) (P.x_over.trans (spMap_comp' _ _).symm)

theorem frX_fst (P : FrPt Xo c S) : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _

theorem frX_snd (P : FrPt Xo c S) : frX P ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem eq_frX (P : FrPt Xo c S) {y : Sp S ⟶ Xo.XF c} (h₁ : y ≫ pullback.fst _ _ = P.x)
    (h₂ : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) : y = frX P :=
  pullback.hom_ext (h₁.trans (frX_fst P).symm) (h₂.trans (frX_snd P).symm)

theorem frX_frMap [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    spMap ψ.toRingHom ≫ frX P = frX P' :=
  eq_frX P' (by rw [Category.assoc, frX_fst, h.1]) (by
    rw [Category.assoc, frX_snd, spMap_comp']
    exact congrArg spMap ψ.comp_algebraMap)

variable (Y) in

def frVec (P : FrPt Xo c S) {x : Sp S ⟶ Y.X} (hx : frX P ≫ Y.j = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TanM x Y.t.G := toModel Y (frX P) (frX_fst P) hx (P.tan σ i)

theorem tanPull_frVec [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P')
    {x : Sp S ⟶ Y.X} (hx : frX P ≫ Y.j = x) {x' : Sp S' ⟶ Y.X} (hx' : frX P' ≫ Y.j = x')
    (e : spMap ψ.toRingHom ≫ x = x') (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    tanPull ψ.toRingHom e (frVec Y P hx σ i) = frVec Y P' hx' σ i :=
  tanPull_toModel _ _ _ _ _ (frX_frMap h) _ _ _ _ (h.2.1 σ i)

variable (c) in

def eigLie (x : Sp S ⟶ Y.X) (σ : E →+* ℂ) : Submodule S (TanM x Y.t.G) where
  carrier := {v | ∀ a : 𝓞 E, actR Y.t.act a v = algebraMap c.F S (embK c σ a) • v}
  zero_mem' := fun a => by rw [map_zero, smul_zero]
  add_mem' := fun hu hv a => by rw [map_add, hu a, hv a, smul_add]
  smul_mem' := fun r v hv a => by rw [map_smul, hv a, smul_comm]

theorem vec_mem_eigLie (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (σ : E →+* ℂ) (cv : Fin M.n → S) :
    vec M x h cv ∈ eigLie c x σ ↔ M.Eig (ev x M.U h) σ cv :=
  forall_congr' fun a => by rw [actR_vec, ← map_smul, (vec M x h).injective.eq_iff]

end ToModel

section Theta

variable {S T : Type} [CommRing S] [CommRing T]

theorem ev_appTop {Z Z' : Scheme.{0}} (z : Sp S ⟶ Z') (π : Z' ⟶ Z) (a : Γ(Z, ⊤)) :
    ev z ⊤ le_top (π.appTop.hom a) = ev (z ≫ π) ⊤ le_top a :=
  (congrArg (fun f => ev z ⊤ le_top (CommRingCat.Hom.hom f a)) (Scheme.Hom.appLE_eq_app (f := π) (U := ⊤)).symm).trans
    (ev_appLE z π le_rfl le_top le_top a)

theorem spMap_ev_top (ρ : Sp T ⟶ Sp S) : spMap ((ev ρ ⊤ le_top).comp (toΓ S)) = ρ := by
  have h := spMap_ev ρ (isAffineOpen_top (Sp S)) le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← spMap_comp']
  exact h

def secMul {Z : Scheme.{0}} {L : LB Z} (g : Γ(Z, ⊤)) (s : L.Sec) : L.Sec where
  f i := resG Z le_top g * s.f i
  compat i j := by
    have e : resG Z (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
      (L.g i j).val * resG Z (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s.f j) := s.compat i j
    show resG Z inf_le_left (resG Z le_top g * s.f i) = (L.g i j).val * resG Z inf_le_right (resG Z le_top g * s.f j)
    rw [map_mul, map_mul, resG_resG, resG_resG, e]
    ring

theorem isoMaps_secMul {Z : Scheme.{0}} {L N : LB Z} (w : LB.Iso L N) {s : L.Sec} {s' : N.Sec} (h : IsoMaps w s s')
    (g : Γ(Z, ⊤)) : IsoMaps w (secMul g s) (secMul g s') := by
  intro i k
  have e1 : resG Z inf_le_left (s'.f i) =
    (show Γ(Z, N.U i ⊓ L.U k) from (w.s (i, k)).val) * resG Z inf_le_right (s.f k) := h i k
  show resG Z inf_le_left (resG Z le_top g * s'.f i) =
    (show Γ(Z, N.U i ⊓ L.U k) from (w.s (i, k)).val) * resG Z inf_le_right (resG Z le_top g * s.f k)
  rw [map_mul, map_mul, resG_resG, resG_resG, e1]
  exact mul_left_comm _ _ _

theorem ev_res_secMul {Z : Scheme.{0}} {L : LB Z} (g : Γ(Z, ⊤)) (s : L.Sec) (k : L.ι) {W : Z.Opens} (h : W ≤ L.U k)
    (r : Sp T ⟶ Z) (hr : ⊤ ≤ r ⁻¹ᵁ W) :
    ev r W hr (resG Z h ((secMul g s).f k)) = ev r ⊤ le_top g * ev r W hr (resG Z h (s.f k)) := by
  show ev r W hr (resG Z h (resG Z le_top g * s.f k)) = _
  rw [map_mul, map_mul, resG_resG, ev_res r _ hr le_top]

theorem appLE_res_appTop {Z Z' B : Scheme.{0}} (g : Z' ⟶ Z) (p : Z ⟶ B) (p' : Z' ⟶ B) (e : g ≫ p = p') {U : Z.Opens}
    {V : Z'.Opens} (h : V ≤ g ⁻¹ᵁ U) (b : Γ(B, ⊤)) :
    resG Z' le_top (p'.appTop.hom b) = (g.appLE U V h).hom (resG Z le_top (p.appTop.hom b)) := by
  subst e
  refine ext_ev fun T _ r hr => ?_
  rw [ev_res r _ hr le_top, ev_appTop, ev_appLE r g h hr (le_preimage_map _ h hr), ev_res _ _ _ le_top,
    ev_appTop, Category.assoc]

def ThRel {x₀ : Sp S ⟶ Xo.X} {x : Sp S ⟶ Y.X} {t' : SAB H (Sp S)} (m1 : SABMap t' Xo.univ.t x₀) (m2 : SABMap t' Y.t x)
    (U : Y.X.Opens) (θ : ∀ i, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U i)) (s : LB.Sec (PPx x₀)) : Prop :=
  ∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (Y.t.PP.L.pull m2.φ))
    (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)),
    RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧
    (∀ (j : Y.t.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens)
      (h₁ : W ≤ m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j))
      (h₂ : W ≤ (Y.t.PP.L.pull m2.φ).U (fun _ => j) ⊓ t'.PP.L.U k),
      (m2.φ.appLE _ _ h₁).hom (θ j) =
        resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k)) ∧
    ∀ g : t'.G.left ⟶ Gx x₀, g ≫ (CartesianMonoidalCategory.snd (Over.mk x₀) Xo.univ.t.G).left = m1.φ →
      g ≫ (CartesianMonoidalCategory.fst (Over.mk x₀) Xo.univ.t.G).left = t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x₀).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

theorem thRel_cast {x₀ : Sp S ⟶ Xo.X} {x x' : Sp S ⟶ Y.X} (e : x = x') {t' : SAB H (Sp S)}
    (m1 : SABMap t' Xo.univ.t x₀) (m2 : SABMap t' Y.t x) : ∃ m2' : SABMap t' Y.t x', m2'.φ = m2.φ ∧
      ∀ U θ s, ThRel m1 m2 U θ s → ThRel m1 m2' U θ s := by
  subst e
  exact ⟨m2, rfl, fun _ _ _ h => h⟩

theorem thRel_change (M M' : GChart Y) {x : Sp S ⟶ Y.X} (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) {x₀ : Sp S ⟶ Xo.X}
    {t' : SAB H (Sp S)} (m1 : SABMap t' Xo.univ.t x₀) (m2 : SABMap t' Y.t x) {s : LB.Sec (PPx x₀)}
    (hs : ThRel m1 m2 M.U M.θ s) : ThRel m1 m2 M'.U M'.θ
      (secMul ((fst (Over.mk x₀) Xo.univ.t.G).left.appTop.hom (toΓ S (ev x _ hh (thRat M M')))) s) := by
  have hw : m2.φ ≫ Y.t.G.hom = t'.G.hom ≫ x := m2.cart.1.w
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, a, d⟩ := hs
  refine ⟨w1, w2, secMul (t'.G.hom.appTop.hom (toΓ S (ev x _ hh (thRat M M')))) σ, secMul _ s1, r1, r2,
    isoMaps_secMul w1 i1 _, fun j k W h₁ h₂ => ?_, fun g g1 g2 j hj => ?_⟩
  · have h₁' : W ≤ m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := fun q hq =>
      ⟨by
        show (m2.φ ≫ Y.t.G.hom) q ∈ M.U
        rw [hw]
        exact (hh (Set.mem_univ (t'.G.hom q))).1, (h₁ hq).2⟩
    refine ext_ev fun T _ r hr => ?_
    have e1 := congrArg (ev r W hr) (a j k W h₁' h₂)
    have hx : (r ≫ m2.φ) ≫ Y.t.G.hom = spMap ((ev (r ≫ t'.G.hom) ⊤ le_top).comp (toΓ S)) ≫ x := by
      rw [spMap_ev_top, Category.assoc, hw, Category.assoc]
    have hm : ⊤ ≤ ((r ≫ m2.φ) ≫ Y.t.G.hom) ⁻¹ᵁ (M.U ⊓ M'.U) := by rw [hx]; exact le_preimage_comp _ hh
    have e2 := ev_thRat M M' (r ≫ m2.φ) j (le_preimage_map _ h₁' hr) (le_preimage_map _ h₁ hr) hm
    rw [ev_appLE r _ h₁' hr (le_preimage_map _ h₁' hr)] at e1
    rw [ev_congr hx _ hm (le_preimage_comp _ hh), ev_spMap _ x _ hh, e1] at e2
    rw [ev_appLE r _ h₁ hr (le_preimage_map _ h₁ hr), e2, map_mul, map_mul, ev_res_secMul, ev_appTop]
    exact mul_left_comm _ _ _
  · exact (congrArg₂ (· * ·) (appLE_res_appTop g _ _ g2 hj _) (d g g1 g2 j hj)).trans (map_mul _ _ _).symm

variable [Algebra c.F S]

theorem thTie_change (M M' : GChart Y) {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) {x₀ : Sp S ⟶ Xo.X} (Λ : M.toMChart.Lift (ev x M.U h) x₀)
    (Λ' : M'.toMChart.Lift (ev x M'.U h') x₀) {s s' : LB.Sec (PPx x₀)} (hs : Λ.ThTie s) (hs' : Λ'.ThTie s')
    (i : (PPx x₀).ι) : s'.f i = scal x₀ (ev x _ hh (thRat M M')) i * s.f i := by
  obtain ⟨n, hn, hn'⟩ := thRel_cast (spMap_ev x M.hU h) Λ.m1 Λ.m2
  obtain ⟨n', hm, hm'⟩ := thRel_cast (spMap_ev x M'.hU h').symm Λ.m1 n
  have key := hm' _ _ _ (thRel_change M M' hh Λ.m1 n (hn' _ _ _ hs))
  let Λ'' : M'.toMChart.Lift (ev x M'.U h') x₀ :=
    ⟨Λ.xF, Λ.xF_fst, Λ.xF_snd, Λ.xF_j.trans ((spMap_ev x M.hU h).trans (spMap_ev x M'.hU h').symm), Λ.t', Λ.m', Λ.m1,
      n', Λ.liftedChartMap_eq, hm.trans (hn.trans Λ.matrix_two_by_two_congr)⟩
  rw [TieUniq.thTie_unique Λ'' (LiftUnique.thTie Λ' Λ'' s' hs') key]
  rfl

theorem frPt_eq_of_tie {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    {u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) S} {P Q : FrPt Xo c S} (hP : M.Comparison₂ (ev x M.U h) u P)
    (hQ : M.Comparison₂ (ev x M.U h) u Q) : P = Q := by
  obtain ⟨x₀, xo, v, t1, t2, t3, s, t4⟩ := P
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q
  obtain ⟨Λ, hv, hs⟩ := hP
  obtain ⟨Λ', hv', hs'⟩ := hQ
  obtain rfl : x₀ = x' := Λ.xF_fst.symm.trans
    ((congrArg (· ≫ pullback.fst _ _) (xF_ext Λ.xF_snd Λ'.xF_snd (Λ.xF_j.trans Λ'.xF_j.symm))).trans Λ'.xF_fst)
  obtain ⟨k1, k2⟩ := LiftUnique.lift_indep E H Dw l Xo c O β Y M S _ x₀ Λ' Λ
  obtain rfl : v = v' := by
    funext τ i
    exact ((vec_bijective E H Dw l Xo c O β Y M S _ x₀ Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))
  obtain rfl : s = s' := TieUniq.thTie_unique Λ hs (k2 _ hs')
  rfl

theorem frBor_of_frVec {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) (t : Ix Dw → Sˣ)
    (b : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (hb : ∀ σ, (b σ).BlockTriangular id)
    (hd : ∀ σ i, b σ i i = t (some ⟨σ, i⟩)) (hv : ∀ σ i, frVec Y P' hx' σ i = ∑ j, b σ j i • frVec Y P hx σ j)
    (hs : ∀ e : P'.x = P.x, ∀ i, (e ▸ P'.s).f i = scal P.x (t none : S) i * P.s.f i) : FrBor t P P' := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := by rw [← frX_fst, eX, frX_fst]
  have hs' := hs e
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have hv' : ∀ σ i, IsCombAt P.x (P.u σ) (fun j => b σ j i) (P'.u σ i) := fun σ i => by
    refine (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).2 ?_
    refine (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).2 ?_
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    rw [← hv]
    obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
    exact (toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  refine ⟨rfl, fun σ i => ⟨fun j => b σ j i, hd σ i, fun j hj => hb σ hj, hv' σ i⟩, 𝟙 _, Category.id_comp _,
    Category.id_comp _, fun i hi => (id_appLE_apply _ _ hi _).trans (hs' i).symm⟩

theorem frVec_of_frBor {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) {t : Ix Dw → Sˣ} (hB : FrBor t P P') (σ : E →+* ℂ) :
    ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, b i i = t (some ⟨σ, i⟩)) ∧
      ∀ i, frVec Y P' hx' σ i = ∑ j, b j i • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := hB.1
  choose cf h1 h2 h3 using hB.2.1 σ
  refine ⟨fun j i => cf i j, fun j i hj => h2 i j hj, h1, fun i => ?_⟩
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1 (h3 i)
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

theorem frX_frBor {P P' : FrPt Xo c S} {t : Ix Dw → Sˣ} (hB : FrBor t P P') : frX P' = frX P :=
  eq_frX P ((frX_fst P').trans hB.1) (frX_snd P')

end Theta

end GlobalTheory.FlagMod
end
end

section
noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AllWt (secZ Weight exOf Psi)

section PullLB

variable {Z Z' : Scheme.{0}} {S : Type} [CommRing S] (L : LB Z) (f : Z' ⟶ Z)

theorem le_pull_chart {w : Sp S ⟶ Z'} {j : PUnit → L.ι} (hz : ⊤ ≤ (w ≫ f) ⁻¹ᵁ L.U (j PUnit.unit)) :
    ⊤ ≤ w ⁻¹ᵁ (L.pull f).U j := fun p hp => mem_pull.2 (hz hp)

theorem ev_pull_g (j j' : PUnit → L.ι) (w : Sp S ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ ((L.pull f).U j ⊓ (L.pull f).U j'))
    (hh : ⊤ ≤ (w ≫ f) ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    ev w _ hw ((L.pull f).g j j').val = ev (w ≫ f) _ hh (L.g (j PUnit.unit) (j' PUnit.unit)).val := by
  have hg : (L.pull f).g j j' =
      res (show (L.pull f).U j ⊓ (L.pull f).U j' ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) from
        fun p hp => ⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩) (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    show ∏ _k : PUnit.{1}, _ ^ (1 : ℤ) = _
    rw [Fintype.prod_unique]
    exact zpow_one _
  rw [hg]
  exact ev_appLE w f _ hw hh _

variable {L} in

def secPull (s : L.Sec) : (L.pull f).Sec where
  f j := (f.appLE (L.U (j PUnit.unit)) _ (fun _ hp => mem_pull.1 hp)).hom (s.f (j PUnit.unit))
  compat j j' := ext_ev fun S _ w hw => by
    have hh : ⊤ ≤ (w ≫ f) ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun p hp => ⟨(mem_pull (F := f)).1 (hw hp).1, (mem_pull (F := f)).1 (hw hp).2⟩
    have h := congrArg (ev (w ≫ f) _ hh) (s.compat (j PUnit.unit) (j' PUnit.unit))
    have a := le_preimage_mono inf_le_left hh
    have b := le_preimage_mono inf_le_right hh
    rw [map_mul, ev_res _ _ hh a, ev_res _ _ hh b] at h
    rw [map_mul, ev_res w _ hw (le_pull_chart L f a), ev_res w _ hw (le_pull_chart L f b)]
    exact ((ev_appLE w f _ _ a _).trans h).trans
      (congrArg₂ (· * ·) (ev_pull_g L f j j' w hw hh).symm (ev_appLE w f _ _ b _).symm)

end PullLB

section Tri

variable {R : Type} [CommRing R] {m : ℕ} {N : Type} [AddCommGroup N] [Module R N]

theorem exists_tri_of_le {v v' : Fin m → N} (h : ∀ i, initSpan R v' i ≤ initSpan R v i) :
    ∃ b : Matrix (Fin m) (Fin m) R, b.BlockTriangular id ∧ ∀ i, v' i = ∑ j, b j i • v j := by
  have ex : ∀ i : Fin m, ∃ a : Fin m → R, (∀ j : Fin m, (i : ℕ) + 1 ≤ j → a j = 0) ∧ ∑ j, a j • v j = v' i :=
    fun i => mem_initSpan.1 (h _ (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩))
  choose a ha ha' using ex
  exact ⟨fun j i => a i j, fun j i hj => ha i j hj, fun i => (ha' i).symm⟩

theorem exists_tri_of_eq {v v' : Fin m → N} (hv : LinearIndependent R v) (h : ∀ i, initSpan R v' i = initSpan R v i) :
    ∃ b : Matrix (Fin m) (Fin m) R, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ ∀ i, v' i = ∑ j, b j i • v j := by
  obtain ⟨b, hb, e⟩ := exists_tri_of_le fun i => (h i).le
  obtain ⟨b', hb', e'⟩ := exists_tri_of_le fun i => (h i).ge
  refine ⟨b, hb, fun i => IsUnit.of_mul_eq_one (b' i i) ?_, e⟩
  have h1 := e' i
  simp only [e, Finset.smul_sum, smul_smul] at h1
  rw [Finset.sum_comm] at h1
  simp only [← Finset.sum_smul] at h1
  have h2 := (Fintype.linearIndependent_iffₛ.1 hv) (fun j => (1 : Matrix (Fin m) (Fin m) R) j i)
    (fun j => ∑ k, b' k i * b j k) (by rw [← h1]; simp [Matrix.one_apply]) i
  rw [← tri_mul_diag hb hb', Matrix.mul_apply]
  simp only [Matrix.one_apply_eq] at h2
  rw [h2]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem linearIndependent_of_tri {v v' : Fin m → N} (hv : LinearIndependent R v) {b : Matrix (Fin m) (Fin m) R}
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) (e : ∀ i, v' i = ∑ j, b j i • v j) :
    LinearIndependent R v' := by
  have hd : IsUnit b.det := by
    rw [Matrix.det_of_upperTriangular hb]
    exact IsUnit.prod_univ_iff.2 hu
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro a ha
  simp only [e, Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simp only [← Finset.sum_smul] at ha
  have h1 : b.mulVec a = 0 := funext fun j => (Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _).trans (hv _ ha j)
  have := congrArg b⁻¹.mulVec h1
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hd, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact congrFun this

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem frBor_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem exists_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) : ∃ z, FrMap φ y z := (evLaws_genFr_atlas E H Dw l Xo c).1.bc S T φ y

theorem frMap_refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : FrMap (AlgHom.id c.F S) y y :=
  (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y).2.1

theorem frMap_unique {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y z') : z = z' :=
  (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S T φ y).1 z z' h h'

theorem spMap_algId {S : Type} [CommRing S] [Algebra c.F S] {Z : Scheme.{0}} (z : Sp S ⟶ Z) :
    spMap (AlgHom.id c.F S).toRingHom ≫ z = z := (congrArg (· ≫ z) (Spec.map_id _)).trans (Category.id_comp _)

theorem spMap_algComp {S S' S'' : Type} [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] [CommRing S'']
    [Algebra c.F S''] (ψ : S →ₐ[c.F] S') (χ : S' →ₐ[c.F] S'') {Z : Scheme.{0}} (z : Sp S ⟶ Z) :
    spMap (χ.comp ψ).toRingHom ≫ z = spMap χ.toRingHom ≫ spMap ψ.toRingHom ≫ z := by
  rw [← Category.assoc, spMap_comp']; rfl

namespace Frames

variable {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {S S' : Type} [CommRing S] [Algebra c.F S] [CommRing S']
  [Algebra c.F S']

def Lies (z : Sp S ⟶ Z) (P : FrPt Xo c S) : Prop :=
  z ≫ π = frX P ≫ Y.j ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (P' : FrPt Xo c S'),
    FrMap ψ P P' → ∀ (k : F.J) (z' : Sp S' ⟶ Z) (_ : spMap ψ.toRingHom ≫ z = z') (hz : ⊤ ≤ z' ⁻¹ᵁ F.U k)
      (hx : z' ≫ π = frX P' ≫ Y.j) (σ : E →+* ℂ) (i : ℕ),
      initSpan S' (frVec Y P' rfl σ) i = initSpan S' (F.vecAt k z' hz hx σ) i

def TopEigen : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : Sp S ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) →
    ∀ (z : Sp S ⟶ Z) (hx : z ≫ π = y ≫ Y.j) (k : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (σ : E →+* ℂ),
      initSpan S (F.vecAt k z hz hx σ) (Dw.mult σ) = eigLie c (y ≫ Y.j) σ

def ChartFr (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (Q : FrPt Xo c S) : Prop :=
  (F.M k).toMChart.Comparison₂ (ev (z ≫ π) (F.M k).U (F.inM hz rfl)) (F.uAt k z hz) Q

variable {F}

theorem ChartFr.over {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q) :
    frX Q ≫ Y.j = z ≫ π := by
  obtain ⟨Λ, -⟩ := h
  rw [← eq_frX Q Λ.xF_fst Λ.xF_snd, Λ.xF_j, spMap_ev]

theorem ChartFr.frVec_eq {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q)
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hQ : frX Q ≫ Y.j = x) (σ : E →+* ℂ) :
    frVec Y Q hQ σ = F.vecAt k z hz hx σ := by
  subst hx
  obtain ⟨Λ, h1, -⟩ := h
  exact funext fun i => (vec_iff_toModel _ Λ (eq_frX Q Λ.xF_fst Λ.xF_snd) (frX_fst Q) hQ _ (Q.tan σ i)).1 (h1 σ i)

theorem ChartFr.unique {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q Q' : FrPt Xo c S} (h : F.ChartFr k z hz Q)
    (h' : F.ChartFr k z hz Q') : Q = Q' := frPt_eq_of_tie _ h h'

theorem ChartFr.frMap {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q)
    {ψ : S →ₐ[c.F] S'} {Q' : FrPt Xo c S'} (hQ : FrMap ψ Q Q') {z' : Sp S' ⟶ Z} (ez : spMap ψ.toRingHom ≫ z = z')
    (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) : F.ChartFr k z' hz' Q' := by
  subst ez
  have := MChart.tie_baseChange E H Dw l Xo c O β Y _ S S' _ ψ _ Q Q' h hQ
  unfold ChartFr
  rw [ev_congr (Category.assoc _ _ _) _ _ (le_preimage_comp _ (F.inM hz rfl)), ev_spMap _ _ _ (F.inM hz rfl),
    funext (F.uAt_spMap k _ z hz hz')]
  exact this

theorem ChartFr.frBor {k k' : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {hz' : ⊤ ≤ z ⁻¹ᵁ F.U k'}
    {Q Q' : FrPt Xo c S} (h : F.ChartFr k z hz Q) (h' : F.ChartFr k' z hz' Q') (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) :
    FrBor (F.TAt k k' z hh) Q Q' := by
  refine frBor_of_frVec (F.inM hz rfl) h.over h'.over _ (fun σ => (F.B k k' σ).map (ev z _ hh))
    (fun σ => F.B_map_tri k k' σ _) (fun σ i => rfl) (fun σ i => ?_) (fun e i => ?_)
  · rw [h.frVec_eq rfl, h'.frVec_eq rfl]
    exact F.vecAt_eq_sum k k' z hz hz' hh rfl σ i
  · obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q'
    dsimp only at e
    subst e
    obtain ⟨Λ, -, hs⟩ := h
    obtain ⟨Λ', -, hs'⟩ := h'
    have hM := le_preimage_inf (F.inM hz rfl) (F.inM hz' rfl)
    exact (thTie_change _ _ _ _ hM Λ Λ' hs hs' i).trans
      (congrArg (fun a => scal Q.x a i * Q.s.f i) (F.ev_T_none k k' z hh rfl hM).symm)

theorem TopEigen.exists_chartFr (hT : F.TopEigen) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) {z : Sp S ⟶ Z} (hx : z ≫ π = y ≫ Y.j) (k : F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) : ∃ Q : FrPt Xo c S, F.ChartFr k z hz Q := by
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y (F.M k).toMChart S _ y hy
    (hx.symm.trans (spMap_ev (z ≫ π) (F.M k).hU (F.inM hz rfl)).symm)
  have hE : ∀ σ cv, (F.M k).toMChart.Eig (ev (z ≫ π) (F.M k).U (F.inM hz rfl)) σ cv ↔
      ∃ a : Fin (Dw.mult σ) → S, (F.uAt k z hz σ).mulVec a = cv := fun σ cv => by
    rw [ev_congr hx _ _ (F.inM hz hx), ← vec_mem_eigLie, ← hT S y hy z hx k hz σ, mem_initSpan]
    simp only [sum_vecAt, (vec _ _ _).injective.eq_iff]
    exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj), h⟩⟩
  obtain ⟨Q, -, hQ⟩ := exists_frPt_tie GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c O β Y _ S _ _ Λ
    (F.uAt k z hz) (fun σ i => (hE σ _).2 ⟨Pi.single i 1, by rw [Matrix.mulVec_single_one]; rfl⟩)
    (fun σ cv h => by
      obtain ⟨a, ha⟩ := (hE σ cv).1 h
      obtain ⟨w, hw⟩ := F.uAt_split k z hz σ
      refine ⟨a, ha, fun b hb => ?_⟩
      have := congrArg w.mulVec (hb.trans ha.symm)
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hw, Matrix.one_mulVec, Matrix.one_mulVec] at this)
  exact ⟨Q, hQ⟩

theorem Lies.frMap {z : Sp S ⟶ Z} {P : FrPt Xo c S} (h : F.Lies z P) {ψ : S →ₐ[c.F] S'} {P' : FrPt Xo c S'}
    (hP : FrMap ψ P P') : F.Lies (spMap ψ.toRingHom ≫ z) P' :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, frX_frMap hP], fun S'' _ _ χ P'' hP' k z' ez =>
    h.2 S'' (χ.comp ψ) P'' (PullbackSections.frMap_trans ψ χ hP hP') k z' ((spMap_algComp ψ χ z).trans ez)⟩

theorem Lies.frBor {z : Sp S ⟶ Z} {P P₁ : FrPt Xo c S} (h : F.Lies z P) {t : Ix Dw → Sˣ} (hB : FrBor t P P₁) :
    F.Lies z P₁ := by
  refine ⟨by rw [h.1, frX_frBor hB], fun S' _ _ ψ P₁' hP₁ k z' ez hz hx σ i => ?_⟩
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  have hB' := frBor_baseChange ψ hB hP hP₁
  have hB'' := (BorelGroupoid.frBor_groupoid E H Dw l Xo c S').2.2.1 _ _ _ hB'
  have eX : frX P' ≫ Y.j = frX P₁' ≫ Y.j := by rw [frX_frBor hB']
  have key : ∀ (x : Sp S' ⟶ Y.X) (e : frX P' ≫ Y.j = x) (hx' : z' ≫ π = x),
      initSpan S' (frVec Y P' e σ) i = initSpan S' (F.vecAt k z' hz hx' σ) i := by
    rintro _ rfl hx'
    exact h.2 S' ψ P' hP k z' ez hz hx' σ i
  rw [← key _ eX hx]
  obtain ⟨b, hb, -, e⟩ := frVec_of_frBor (F.inM hz hx) eX rfl hB' σ
  obtain ⟨b', hb', -, e'⟩ := frVec_of_frBor (F.inM hz hx) rfl eX hB'' σ
  exact le_antisymm (initSpan_le_of_tri hb e i) (initSpan_le_of_tri hb' e' i)

theorem ChartFr.lies {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q : FrPt Xo c S} (h : F.ChartFr k z hz Q) :
    F.Lies z Q := by
  refine ⟨h.over.symm, fun S' _ _ ψ Q' hQ k' z' ez hz' hx σ i => ?_⟩
  have hk : ⊤ ≤ z' ⁻¹ᵁ F.U k := ez ▸ le_preimage_comp _ hz
  rw [(h.frMap hQ ez hk).frVec_eq hx rfl, F.initSpan_vecAt_eq k k' z' hk hz']

theorem Lies.initSpan_eq {z : Sp S ⟶ Z} {P : FrPt Xo c S} (h : F.Lies z P) {k : F.J} (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hP : frX P ≫ Y.j = x) (σ : E →+* ℂ) (i : ℕ) :
    initSpan S (frVec Y P hP σ) i = F.step z hx σ i := by
  subst hP
  rw [F.step_eq k z hz]
  exact h.2 S (AlgHom.id c.F S) P (frMap_refl P) k z (spMap_algId z) hz hx σ i

theorem ChartFr.exists_frBor {k : F.J} {z : Sp S ⟶ Z} {hz : ⊤ ≤ z ⁻¹ᵁ F.U k} {Q P : FrPt Xo c S}
    (h : F.ChartFr k z hz Q) (hP : F.Lies z P) : ∃ t, FrBor t Q P := by
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y P hP.1.symm σ i = ∑ j, b j i • frVec Y Q h.over σ j := fun σ => by
    rw [h.frVec_eq rfl]
    exact exists_tri_of_eq (F.linearIndependent_vecAt k z hz rfl σ) fun i =>
      (hP.initSpan_eq hz rfl _ σ i).trans (F.step_eq k z hz rfl σ i)
  choose b hb hu hv using ex
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) (hP.1.symm.trans h.over.symm)]
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
  dsimp only at e
  subst e
  obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
  exact ⟨_, frBor_of_frVec (F.inM hz rfl) h.over hP.1.symm
    (fun ix => match ix with | none => u0 | some p => (hu p.1 p.2).unit) b hb (fun _ _ => rfl) hv fun _ => hu0⟩


theorem TopEigen.diag_unit (hT : F.TopEigen) {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K]
    [Algebra c.F K] (φ : V →+* K) (hφ : Function.Injective φ) (z : Sp V ⟶ Z) {k : F.J} (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    {P Q : FrPt Xo c K} (hP : F.Lies (spMap φ ≫ z) P) (e : spMap φ ≫ z ≫ π = frX P ≫ Y.j) (σ : E →+* ℂ)
    (ub : Fin (Dw.mult σ) → TanM (z ≫ π) Y.t.G) (hub : ∀ i, tanPull φ e (ub i) = frVec Y P rfl σ i)
    (hsp : ∀ v, tanPull φ e v ∈ eigLie c (frX P ≫ Y.j) σ → ∃ a : Fin (Dw.mult σ) → V, ∑ i, a i • ub i = v)
    (hQ : F.ChartFr k (spMap φ ≫ z) (le_preimage_comp _ hz) Q) {t : Ix Dw → Kˣ} (ht : FrBor t Q P) :
    (∀ i, initSpan V ub i = F.step z rfl σ i) ∧ ∀ i, ∃ u : Vˣ, φ u = t (some ⟨σ, i⟩) := by
  have hz' := le_preimage_comp (spMap φ) hz
  have hx : (spMap φ ≫ z) ≫ π = frX P ≫ Y.j := hP.1
  obtain ⟨b', hb', hd', e'⟩ := frVec_of_frBor (F.inM hz' hx) (hQ.over.trans hx) rfl ht σ
  rw [hQ.frVec_eq hx] at e'
  have hK := F.linearIndependent_vecAt k _ hz' hx σ
  have hli := linearIndependent_of_tri hK hb' (fun i => by rw [hd']; exact Units.isUnit _) e'
  have h1 : ∀ i, initSpan V ub i = F.step z rfl σ i := fun i => by
    refine le_antisymm (Submodule.span_le.2 ?_) fun v hv => ?_
    · rintro _ ⟨j, hj, rfl⟩
      refine (F.mem_step_iff_of_injective φ hφ z rfl rfl hx e σ i _).2 ?_
      rw [hub, ← hP.initSpan_eq hz' hx rfl]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    · have h2 := F.tanPull_mem_step φ z rfl rfl hx e σ i hv
      obtain ⟨a, rfl⟩ := hsp v (by
        rw [← hT K _ (frX_snd P) _ hx k hz']
        rw [F.step_eq k _ hz'] at h2
        obtain ⟨d, -, hd⟩ := mem_initSpan.1 h2
        exact mem_initSpan.2 ⟨d, fun j hj => absurd j.2 (not_lt.2 hj), hd⟩)
      rw [← hP.initSpan_eq hz' hx rfl, map_sum] at h2
      simp only [map_smulₛₗ, hub] at h2
      obtain ⟨d, hd, h3⟩ := mem_initSpan.1 h2
      refine mem_initSpan.2 ⟨a, fun j hj => hφ ?_, rfl⟩
      rw [map_zero, ← hd j hj]
      exact ((Fintype.linearIndependent_iffₛ.1 hli) _ _ h3 j).symm
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨b, -, hu, eb⟩ := exists_tri_of_eq (F.linearIndependent_vecAt k z hz rfl σ)
    fun i => (h1 i).trans (F.step_eq k z hz rfl σ i)
  refine ⟨(hu i).unit, ?_⟩
  have h4 := congrArg (tanPull (G := Y.t.G) φ e) (eb i)
  rw [hub, e', map_sum] at h4
  simp only [map_smulₛₗ, F.tanPull_vecAt k φ z hz hz' rfl hx e] at h4
  rw [← hd']
  exact ((Fintype.linearIndependent_iffₛ.1 hK) _ _ h4 i).symm

def coord (M : GChart Y) (h : ∀ σ, Dw.mult σ ≤ M.n) : Frames Y M.U.ι where
  J := Unit
  U _ := ⊤
  cover := iSup_const
  M _ := M
  le _ := fun p _ => p.2
  u _ σ := (1 : Matrix _ _ _).submatrix id (Fin.castLE (h σ))
  split _ σ := ⟨(1 : Matrix _ _ _).submatrix (Fin.castLE (h σ)) id, by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.one_mul,
      Matrix.submatrix_one _ (Fin.castLE_injective _)]⟩
  tri _ _ σ := ⟨1, Matrix.blockTriangular_one, by
    have e : chg M.toMChart M.toMChart = 1 := Module.Basis.toMatrix_self _
    rw [e, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Matrix.one_mul _).trans (Matrix.mul_one _).symm⟩

example (M : GChart Y) (h : ∀ σ, Dw.mult σ ≤ M.n) (z : Sp S ⟶ M.U.toScheme) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    (coord M h).vecAt () z le_top rfl σ i =
      lieBasis M.toMChart _ ((coord M h).inM (k := ()) le_top rfl) (Fin.castLE (h σ) i) := by
  have hu : ∀ j : Fin M.n, (coord M h).uAt () z le_top σ j i = if j = Fin.castLE (h σ) i then 1 else 0 := fun j => by
    show ev z ⊤ le_top ((1 : Matrix (Fin M.n) (Fin M.n) _) j (Fin.castLE (h σ) i)) = _
    rw [Matrix.one_apply, apply_ite (ev z ⊤ le_top), map_one, map_zero]
  refine (congrArg (vec M.toMChart _ ((coord M h).inM (k := ()) le_top rfl)) (funext hu)).trans ?_
  exact (vec_apply _ _ _ _).trans (by simp)

open Classical in

theorem LL_single_one (F : Frames Y π) (ix : Ix Dw) : F.LL (Pi.single ix 1) = GlobalTheory.CechPic.dual (F.line ix) := by
  unfold LL line GlobalTheory.CechPic.dual
  congr 1
  funext k k'
  rw [Finset.prod_eq_single ix (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp) (by simp)]
  simp

end Frames

section Weights

theorem mult_of_mem (τ : Psi H) : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]

theorem mult_conj (τ : Psi H) : Dw.mult (conjEmb τ.1) = Dw.q := by simp [Datum.mult, GlobalTheory.AllWt.conj_not_mem τ]

theorem exOf_none (la : Weight Dw) : exOf Dw la 0 none = 0 := rfl

theorem exOf_big (la : Weight Dw) (τ : Psi H) (i : Fin (Dw.mult τ.1)) :
    exOf Dw la 0 (some ⟨τ.1, i⟩) = la τ ⟨i, by have := i.2; have := mult_of_mem (Dw := Dw) τ; omega⟩ :=
  (GlobalTheory.AllWt.wtOf_big la 0 τ i (mult_of_mem (Dw := Dw) τ ▸ i.2)).trans (sub_zero _)

theorem exOf_small (la : Weight Dw) (τ : Psi H) (i : Fin (Dw.mult (conjEmb τ.1))) :
    exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) =
      -la τ ⟨Dw.p + (Dw.q - 1 - i), by have := i.2; have := mult_conj (Dw := Dw) τ; omega⟩ :=
  (GlobalTheory.AllWt.wtOf_small la 0 τ i (mult_conj (Dw := Dw) τ ▸ i.2)).trans (sub_zero _)

theorem exOf_ext {la : Weight Dw} {e : Ix Dw → ℤ} (h0 : e none = 0)
    (h1 : ∀ (τ : Psi H) (i : Fin (Dw.mult τ.1)) hi, la τ ⟨i, hi⟩ = e (some ⟨τ.1, i⟩))
    (h2 : ∀ (τ : Psi H) (i : Fin (Dw.mult (conjEmb τ.1))) hi,
      -la τ ⟨Dw.p + (Dw.q - 1 - i), hi⟩ = e (some ⟨conjEmb τ.1, i⟩)) : exOf Dw la 0 = e := by
  funext ix
  rcases ix with _ | ⟨σ, i⟩
  · exact h0.symm
  · by_cases h : σ (H.rt : E) = H.rt0
    · exact (exOf_big la ⟨σ, h⟩ i).trans (h1 ⟨σ, h⟩ i _)
    · obtain ⟨τ, rfl⟩ : ∃ τ : Psi H, σ = conjEmb τ.1 :=
        ⟨⟨conjEmb σ, GlobalTheory.AllWt.conj_mem h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩
      exact (exOf_small la τ i).trans (h2 τ i _)

variable (Dw) in

def mu0 : Weight Dw := fun _ i => if (i : ℕ) < Dw.p then 1 else -1

theorem unitaryWeightExponentVector_signatureWeightMuZero : exOf Dw (mu0 Dw) 0 = fun ix => ix.elim 0 fun _ => 1 :=
  exOf_ext rfl (fun τ i _ => if_pos (i.2.trans_eq (mult_of_mem τ)))
    fun τ i _ => by simp [mu0]

end Weights

def genMap {Z : Scheme.{0}} (π : Z ⟶ Y.X) : pullback (π ≫ Y.s) (spMap β) ⟶ pullback Y.s (spMap β) :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])

structure FlagCover (Y : Model Xo c β) where
  YY : Scheme.{0}
  π : YY ⟶ Y.X
  proper : IsProper π
  normal : Geo.Tor.IsNormalScheme YY
  flat : Flat (π ≫ Y.s)
  F : Frames Y π
  dense : Dense (genMap π ⁻¹' Set.range Y.jQ)
  top : F.TopEigen
  rep : ∀ (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), ∃! z : Sp S ⟶ YY, F.Lies z P

structure FlagModel (Y : Model Xo c β) extends FlagCover Y where
  fin : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ YY),
    {z' : Sp K ⟶ YY | ∃ hx : z' ≫ π = z ≫ π, ∀ σ i, F.step z' hx σ i = F.step z rfl σ i}.Finite

namespace FlagCover

variable (X : FlagCover Y) {S S' : Type} [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S']

abbrev Yo : Scheme.{0} := pullback X.π Y.j

abbrev inc : X.Yo ⟶ X.YY := pullback.fst X.π Y.j

abbrev gr (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : LB X.YY := X.F.gr σ i

abbrev LL (e : Ix Dw → ℤ) : LB X.YY := X.F.LL e

abbrev de : LB X.YY := X.F.de

abbrev detOm : LB X.YY := X.F.detOm

def Llam (la : Weight Dw) : LB X.YY := X.F.LL (exOf Dw la 0)

theorem isLB_Llam (la : Weight Dw) : (X.Llam la).IsLB := X.F.isLB_LL _

def ptY (P : FrPt Xo c S) : Sp S ⟶ X.YY := (X.rep S P).exists.choose

theorem lies_ptY (P : FrPt Xo c S) : X.F.Lies (X.ptY P) P := (X.rep S P).exists.choose_spec

variable {X} in
theorem eq_ptY {P : FrPt Xo c S} {z : Sp S ⟶ X.YY} (h : X.F.Lies z P) : z = X.ptY P :=
  (X.rep S P).unique h (X.lies_ptY P)

def pt (P : FrPt Xo c S) : Sp S ⟶ X.Yo := pullback.lift (X.ptY P) (frX P) (X.lies_ptY P).1

theorem pt_inc (P : FrPt Xo c S) : X.pt P ≫ X.inc = X.ptY P := pullback.lift_fst _ _ _

theorem pt_snd (P : FrPt Xo c S) : X.pt P ≫ pullback.snd _ _ = frX P := pullback.lift_snd _ _ _

theorem ptY_frMap {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    spMap ψ.toRingHom ≫ X.ptY P = X.ptY P' := eq_ptY ((X.lies_ptY P).frMap h)

theorem pt_frMap {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    spMap ψ.toRingHom ≫ X.pt P = X.pt P' :=
  pullback.hom_ext (by rw [Category.assoc, pt_inc, pt_inc, X.ptY_frMap h])
    (by rw [Category.assoc, pt_snd, pt_snd, frX_frMap h])

theorem ptY_frBor {t : Ix Dw → Sˣ} {P P' : FrPt Xo c S} (h : FrBor t P P') : X.ptY P = X.ptY P' :=
  eq_ptY ((X.lies_ptY P).frBor h)

theorem pt_frBor {t : Ix Dw → Sˣ} {P P' : FrPt Xo c S} (h : FrBor t P P') : X.pt P = X.pt P' :=
  pullback.hom_ext (by rw [pt_inc, pt_inc, X.ptY_frBor h]) (by rw [pt_snd, pt_snd, frX_frBor h])

theorem exists_chartFr (w : Sp S ⟶ X.Yo) (hw : w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F S))
    (k : X.F.J) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ∃ Q : FrPt Xo c S, X.F.ChartFr k (w ≫ X.inc) hz Q ∧ X.pt Q = w := by
  have hx : (w ≫ X.inc) ≫ X.π = (w ≫ pullback.snd _ _) ≫ Y.j := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hy : (w ≫ pullback.snd _ _) ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by rw [Category.assoc, hw]
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hx k hz
  exact ⟨Q, hQ, pullback.hom_ext (by rw [pt_inc, ← eq_ptY hQ.lies])
    (by rw [pt_snd]; exact xF_ext (Y := Y) (frX_snd Q) hy (hQ.over.trans hx))⟩

theorem points [IsLocalRing S] :
    (∀ w : Sp S ⟶ X.Yo, w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F S) ↔ ∃ P, X.pt P = w) ∧
      ∀ P P' : FrPt Xo c S, X.pt P = X.pt P' ↔ ∃ t, FrBor t P P' := by
  refine ⟨fun w => ⟨fun hw => ?_, ?_⟩, fun P P' => ⟨fun e => ?_, fun ⟨t, h⟩ => X.pt_frBor h⟩⟩
  · obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (w ≫ X.inc)
    exact (X.exists_chartFr w hw k hz).imp fun _ h => h.2
  · rintro ⟨P, rfl⟩
    rw [← Category.assoc, pt_snd, frX_snd]
  · have e' : X.ptY P = X.ptY P' := by rw [← pt_inc, e, pt_inc]
    obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (X.ptY P)
    obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (frX_snd P) (X.lies_ptY P).1 k hz
    obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY P)
    obtain ⟨t', ht'⟩ := hQ.exists_frBor (e' ▸ X.lies_ptY P')
    obtain ⟨-, g1, g2, -⟩ := BorelGroupoid.frBor_groupoid E H Dw l Xo c S
    exact ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩

abbrev SecO (e : Ix Dw → ℤ) : Type := ((X.F.LL e).pull X.inc).Sec

variable {X} {e : Ix Dw → ℤ}

omit [Algebra c.F S] in
theorem le_pull {w : Sp S ⟶ X.Yo} {k : X.F.J} (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ⊤ ≤ w ⁻¹ᵁ ((X.F.LL e).pull X.inc).U (fun _ => k) := fun p hp => mem_pull.2 (hz hp)

def coef (s : X.SecO e) (k : X.F.J) (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) : S :=
  ev w _ (le_pull hz) (s.f fun _ => k)

def resO (s : (X.F.LL e).Sec) : X.SecO e := secPull X.inc s

omit [Algebra c.F S] in
theorem coef_resO (s : (X.F.LL e).Sec) (k : X.F.J) (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    coef (resO s) k w hz = ev (w ≫ X.inc) (X.F.U k) hz (s.f k) := ev_appLE w X.inc _ _ hz _

omit [Algebra c.F S] in
open Classical in
theorem coef_change (s : X.SecO e) (k k' : X.F.J) (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k)
    (hz' : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k') (hh : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    coef s k w hz = (∏ ix, X.F.TAt k k' (w ≫ X.inc) hh ix ^ (-e ix)).val * coef s k' w hz' := by
  have hw := le_preimage_inf (le_pull (e := e) hz) (le_pull (e := e) hz')
  have h := congrArg (ev w _ hw) (s.compat (fun _ => k) (fun _ => k'))
  rw [map_mul] at h
  refine (ev_res w _ hw _ _).symm.trans (h.trans (congrArg₂ (· * ·) ?_ (ev_res w _ hw _ _)))
  rw [← X.F.ev_LL_g e k k' _ hh]
  exact ev_pull_g (X.F.LL e) X.inc (fun _ => k) (fun _ => k') w hw hh

omit [Algebra c.F S] [Algebra c.F S'] in
theorem coef_spMap (s : X.SecO e) (k : X.F.J) (φ : S →+* S') (w : Sp S ⟶ X.Yo) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k)
    {w' : Sp S' ⟶ X.Yo} (ew : spMap φ ≫ w = w') (hz' : ⊤ ≤ (w' ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    coef s k w' hz' = φ (coef s k w hz) := by
  subst ew
  rw [coef, ev_spMap φ w _ (le_pull hz)]
  rfl

open Classical in

def IsValAt (s : X.SecO e) (P : FrPt Xo c S) (a : S) : Prop :=
  ∀ (k : X.F.J) (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c S) (t : Ix Dw → Sˣ),
    X.F.ChartFr k (X.pt P ≫ X.inc) hz Q → FrBor t Q P → a = (∏ ix, t ix ^ e ix).val * coef s k (X.pt P) hz

def IsVal (s : X.SecO e) (P : FrPt Xo c S) (a : S) : Prop :=
  ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P P' →
    IsValAt s P' (ψ a)

variable (X) in
theorem exists_chartFr_frBor (P : FrPt Xo c S) (k : X.F.J) (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ∃ (Q : FrPt Xo c S) (t : Ix Dw → Sˣ), X.F.ChartFr k (X.pt P ≫ X.inc) hz Q ∧ FrBor t Q P := by
  have hl : X.F.Lies (X.pt P ≫ X.inc) P := by rw [pt_inc]; exact X.lies_ptY P
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (frX_snd P) hl.1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  exact ⟨Q, t, hQ, ht⟩

open Classical in

theorem isValAt_of_chart (s : X.SecO e) {P Q : FrPt Xo c S} {k : X.F.J} {hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k}
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k (X.pt P ≫ X.inc) hz Q) (ht : FrBor t Q P) :
    IsValAt s P ((∏ ix, t ix ^ e ix).val * coef s k (X.pt P) hz) := by
  intro k' hz' Q' t' hQ' ht'
  obtain ⟨-, g1, -, g3⟩ := BorelGroupoid.frBor_groupoid E H Dw l Xo c S
  have hh := le_preimage_inf hz hz'
  rw [g3 _ _ _ _ ht (g1 _ _ _ _ _ (hQ.frBor hQ' hh) ht'), coef_change s k k' _ hz hz' hh, ← _root_.mul_assoc,
    ← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 2
  exact Finset.prod_congr rfl fun ix _ => by
    rw [Pi.mul_apply, mul_zpow, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, _root_.one_mul]

theorem existsUnique_isValAt (s : X.SecO e) (P : FrPt Xo c S) (k : X.F.J) (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) :
    ∃! a, IsValAt s P a := by
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P k hz
  exact ⟨_, isValAt_of_chart s hQ ht, fun a ha => ha k hz Q t hQ ht⟩

theorem IsValAt.frMap {s : X.SecO e} {P : FrPt Xo c S} {a : S} (h : IsValAt s P a) {k : X.F.J}
    (hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k) {ψ : S →ₐ[c.F] S'} {P' : FrPt Xo c S'} (hP : FrMap ψ P P') :
    IsValAt s P' (ψ a) := by
  classical
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P k hz
  obtain ⟨Q', hQQ⟩ := exists_frMap ψ Q
  have ez : spMap ψ.toRingHom ≫ X.pt P ≫ X.inc = X.pt P' ≫ X.inc := by rw [← Category.assoc, X.pt_frMap hP]
  have hz' : ⊤ ≤ (X.pt P' ≫ X.inc) ⁻¹ᵁ X.F.U k := ez ▸ le_preimage_comp _ hz
  have := isValAt_of_chart s (hQ.frMap hQQ ez hz') (frBor_baseChange ψ ht hQQ hP)
  convert this using 1
  rw [h k hz Q t hQ ht, map_mul, coef_spMap s k ψ.toRingHom _ hz (X.pt_frMap hP) hz']
  congr 1
  show (Units.map (ψ : S →* S') (∏ ix, t ix ^ e ix)).val = _
  simp only [map_prod, map_zpow]

theorem existsUnique_isVal (s : X.SecO e) (P : FrPt Xo c S) : ∃! a, IsVal s P a := by
  have tr : ∀ {S' : Type} [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {P' : FrPt Xo c S'}, FrMap ψ P P' →
      ∀ k, ⊤ ≤ (spMap ψ.toRingHom ≫ X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k ↔ ⊤ ≤ (X.pt P' ≫ X.inc) ⁻¹ᵁ X.F.U k :=
    fun hP k => by rw [← Category.assoc, X.pt_frMap hP]
  have ex : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (k : X.F.J),
      ⊤ ≤ (spMap ψ.toRingHom ≫ X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k → ∃ b : S', ∀ P', FrMap ψ P P' → IsValAt s P' b := by
    intro S' _ _ ψ k h
    obtain ⟨P', hP⟩ := exists_frMap ψ P
    obtain ⟨b, hb, -⟩ := existsUnique_isValAt s P' k ((tr hP k).1 h)
    exact ⟨b, fun P'' hP'' => frMap_unique hP hP'' ▸ hb⟩
  choose val hval using ex
  obtain ⟨a, ha, hu⟩ := glue_val (X.pt P ≫ X.inc) X.F.cover val (fun S' S'' _ _ _ _ ψ χ k k' h h' => by
    obtain ⟨P', hP⟩ := exists_frMap ψ P
    obtain ⟨P'', hP'⟩ := exists_frMap χ P'
    have hP'' := PullbackSections.frMap_trans ψ χ hP hP'
    exact (existsUnique_isValAt s P'' k' ((tr hP'' k').1 h')).unique (hval _ _ k' h' P'' hP'')
      ((hval _ _ k h P' hP).frMap ((tr hP k).1 h) hP'))
  refine ⟨a, fun S' _ _ ψ P' hP k hz => ?_, fun b hb => hu b fun S' _ _ ψ k h => ?_⟩
  · rw [ha S' ψ k ((tr hP k).2 hz)]
    exact hval _ _ k _ P' hP k hz
  · obtain ⟨P', hP⟩ := exists_frMap ψ P
    exact (existsUnique_isValAt s P' k ((tr hP k).1 h)).unique (hb S' ψ P' hP) (hval _ _ k h P' hP)

def val (s : X.SecO e) (P : FrPt Xo c S) : S := (existsUnique_isVal s P).exists.choose

theorem isVal_val (s : X.SecO e) (P : FrPt Xo c S) : IsVal s P (val s P) := (existsUnique_isVal s P).exists.choose_spec

theorem IsVal.eq_val {s : X.SecO e} {P : FrPt Xo c S} {a : S} (h : IsVal s P a) : a = val s P :=
  (existsUnique_isVal s P).unique h (isVal_val s P)

open Classical in

theorem val_eq (s : X.SecO e) {P Q : FrPt Xo c S} {k : X.F.J} {hz : ⊤ ≤ (X.pt P ≫ X.inc) ⁻¹ᵁ X.F.U k}
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k (X.pt P ≫ X.inc) hz Q) (ht : FrBor t Q P) :
    val s P = (∏ ix, t ix ^ e ix).val * coef s k (X.pt P) hz :=
  isVal_val s P S (AlgHom.id c.F S) P (frMap_refl P) k hz Q t hQ ht

theorem val_chartFr (s : X.SecO e) {Q : FrPt Xo c S} {k : X.F.J} {hz : ⊤ ≤ (X.pt Q ≫ X.inc) ⁻¹ᵁ X.F.U k}
    (hQ : X.F.ChartFr k (X.pt Q ≫ X.inc) hz Q) : val s Q = coef s k (X.pt Q) hz := by
  rw [val_eq s hQ ((BorelGroupoid.frBor_groupoid E H Dw l Xo c S).1 Q)]
  simp

theorem val_frMap (s : X.SecO e) {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    val s P' = ψ (val s P) :=
  (IsVal.eq_val fun S'' _ _ χ P'' h' => isVal_val s P S'' (χ.comp ψ) P'' (PullbackSections.frMap_trans ψ χ h h')).symm

open Classical in
theorem val_frBor (s : X.SecO e) {t : Ix Dw → Sˣ} {P P₁ : FrPt Xo c S} (h : FrBor t P P₁) :
    val s P₁ = (∏ ix, t ix ^ e ix).val * val s P := by
  refine (IsVal.eq_val fun S' _ _ ψ P₁' h₁ k hz Q t' hQ ht' => ?_).symm
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  have hB := frBor_baseChange ψ h hP h₁
  obtain ⟨-, g1, g2, -⟩ := BorelGroupoid.frBor_groupoid E H Dw l Xo c S'
  have key : ∀ (w : Sp S' ⟶ X.Yo) (_ : X.pt P' = w) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k (w ≫ X.inc) hz Q → ψ (val s P) =
        (∏ ix, (t' * (fun i => Units.map (ψ : S →* S') (t i))⁻¹) ix ^ e ix).val * coef s k w hz := by
    rintro _ rfl hz hQ
    exact isVal_val s P S' ψ P' hP k hz Q _ hQ (g1 _ _ _ _ _ ht' (g2 _ _ _ hB))
  rw [map_mul, key _ (X.pt_frBor hB) hz hQ, ← _root_.mul_assoc]
  congr 1
  show (Units.map (ψ : S →* S') (∏ ix, t ix ^ e ix) * _).val = _
  rw [map_prod, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun ix _ => by
    rw [map_zpow, Pi.mul_apply, Pi.inv_apply, ← mul_zpow, mul_comm (t' ix), mul_inv_cancel_left]

def toRule (s : X.SecO e) : Rul Xo c := fun _ P => val s P

theorem toRule_mem_secZ (s : X.SecO e) : toRule s ∈ secZ Xo c e :=
  ⟨fun _ _ _ _ _ h => val_frMap s h, fun _ _ _ _ h => by
    show val s _ = _ * val s _
    convert val_frBor s h⟩

theorem evR_toRule (s : X.SecO e) (P : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) P) :
    evR Xo c (toRule s) P = val s P := by
  unfold evR evalAt
  rw [dif_pos h]
  exact (val_frMap s h.choose_spec.choose_spec.choose_spec).symm

theorem evR_toRule_of_isReduced [_root_.IsReduced S] (s : X.SecO e) (P : FrPt Xo c S) :
    evR Xo c (toRule s) P = val s P := evR_toRule s P ((evLaws_genFr_atlas E H Dw l Xo c).1.test S P)

theorem val_add {s s₁ s₂ : X.SecO e} (h : ∀ j, s.f j = s₁.f j + s₂.f j) (P : FrPt Xo c S) :
    val s P = val s₁ P + val s₂ P := by
  refine (IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
  rw [map_add, isVal_val s₁ P S' ψ P' hP k hz Q t hQ ht, isVal_val s₂ P S' ψ P' hP k hz Q t hQ ht, ← mul_add]
  exact congrArg _ ((congrArg _ (h _)).trans (map_add _ _ _)).symm

theorem val_mul {e₁ e₂ : Ix Dw → ℤ} {s : X.SecO (e₁ + e₂)} {s₁ : X.SecO e₁} {s₂ : X.SecO e₂}
    (h : ∀ j, s.f j = (show Γ(X.Yo, ((X.F.LL (e₁ + e₂)).pull X.inc).U j) from s₁.f j) *
      (show Γ(X.Yo, ((X.F.LL (e₁ + e₂)).pull X.inc).U j) from s₂.f j)) (P : FrPt Xo c S) :
    val s P = val s₁ P * val s₂ P := by
  refine (IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
  have hc : coef s k (X.pt P') hz = coef s₁ k (X.pt P') hz * coef s₂ k (X.pt P') hz :=
    (congrArg _ (h _)).trans (map_mul _ _ _)
  rw [map_mul, isVal_val s₁ P S' ψ P' hP k hz Q t hQ ht, isVal_val s₂ P S' ψ P' hP k hz Q t hQ ht, hc]
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring

variable (X)

open Classical in

theorem Llam_single_big (τ : Psi H) (i : Fin (Dw.mult τ.1)) (hi : (i : ℕ) < Dw.p + Dw.q) :
    X.Llam (Pi.single τ (Pi.single ⟨i, hi⟩ (-1))) = X.gr τ.1 i := by
  have hp := mult_of_mem (Dw := Dw) τ
  refine (congrArg X.F.LL (exOf_ext (by simp) (fun τ' j hj => ?_) fun τ' j hj => ?_)).trans (X.F.LL_single_neg _)
  · by_cases e : τ' = τ
    · subst e
      simp [Pi.single_apply, Fin.ext_iff]
    · have : τ'.1 ≠ τ.1 := fun h => e (Subtype.ext h)
      simp [Pi.single_apply, e, this]
  · have : conjEmb τ'.1 ≠ τ.1 := fun h => GlobalTheory.AllWt.conj_not_mem τ' (h ▸ τ.2)
    have h2 : Dw.p + (Dw.q - 1 - j) ≠ i := by have := i.2; omega
    by_cases e : τ' = τ
    · subst e
      simp [Pi.single_apply, Fin.ext_iff, this, h2]
    · simp [Pi.single_apply, e, this]

open Classical in

theorem Llam_single_small (τ : Psi H) (i : Fin (Dw.mult (conjEmb τ.1)))
    (hi : Dw.p + (Dw.q - 1 - i) < Dw.p + Dw.q) :
    X.Llam (Pi.single τ (Pi.single ⟨_, hi⟩ (-1))) = GlobalTheory.CechPic.dual (X.gr (conjEmb τ.1) i) := by
  have hq := mult_conj (Dw := Dw) τ
  refine (congrArg X.F.LL (exOf_ext (by simp) (fun τ' j hj => ?_) fun τ' j hj => ?_)).trans (X.F.LL_single_one _)
  · have : τ'.1 ≠ conjEmb τ.1 := fun h => GlobalTheory.AllWt.conj_not_mem τ (h ▸ τ'.2)
    have h2 : (j : ℕ) ≠ Dw.p + (Dw.q - 1 - i) := by have := j.2; have := mult_of_mem (Dw := Dw) τ'; omega
    by_cases e : τ' = τ
    · subst e
      simp [Pi.single_apply, Fin.ext_iff, this, h2]
    · simp [Pi.single_apply, e, this]
  · by_cases e : τ' = τ
    · subst e
      have : Dw.q - 1 - j = Dw.q - 1 - i ↔ (j : ℕ) = i := by have := i.2; have := j.2; omega
      by_cases h : (j : ℕ) = i <;> simp [Pi.single_apply, Fin.ext_iff, this, h]
    · have : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← GlobalTheory.AllWt.conjEmb_conjEmb τ'.1, h, GlobalTheory.AllWt.conjEmb_conjEmb]))
      simp [Pi.single_apply, e, this]

example (k k' : X.F.J) : (X.LL 0).g k k' = 1 := Finset.prod_eq_one fun _ _ => zpow_zero _

end FlagCover

end GlobalTheory.FlagMod
end
end
