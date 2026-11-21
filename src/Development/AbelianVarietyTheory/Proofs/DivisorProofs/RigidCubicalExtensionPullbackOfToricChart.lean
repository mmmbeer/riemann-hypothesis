import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.TransSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

section
noncomputable section

namespace GlobalTheory.ChartCubExt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Exist.CubicalExtension

def ExtendGenAt (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (eA : Sp K ⟶ pullback G.hom (spMap (algebraMap V K))),
      eA ≫ pullback.fst G.hom (spMap (algebraMap V K)) = spMap (algebraMap V K) ≫ eSec G →
    ∀ (N : RigLB G) (r : LB.Gen (N.L.pull (pullback.fst G.hom (spMap (algebraMap V K))))), r.IsGen →
    LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (spMap (algebraMap V K))) →
    ∃ r' : LB.Gen N.L, r'.IsGen ∧ LB.genPull N.L r' (pullback.fst G.hom (spMap (algebraMap V K))) = r

section Group

variable {T K : Type} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K]

theorem isPullCubical_of_generic_of_ext (hE : ExtendGenAt T K) {S : Scheme.{0}} {G₀ : Over S} {G : Over (Sp T)}
    {GK : Over (Sp K)} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G] [IsCommMonObj G] [GrpObj GK] [IsCommMonObj GK]
    (hG : IsSemiAbelian G) {L₀ : RigLB G₀} {L : RigLB G} {LK : RigLB GK} (c₀ : CubicalStr G₀ L₀)
    (c : CubicalStr G L) (cK : CubicalStr GK LK) (n : CubeMap G G₀) (m : CubeMap GK G) (m' : CubeMap GK G₀)
    (hp : IsPullback m.F GK.hom G.hom (spMap (algebraMap T K))) (he : m.e = spMap (algebraMap T K))
    (h₁ : m'.F = m.F ≫ n.F) (h₂ : m'.F3 = m.F3 ≫ n.F3) (h₃ : m'.e = m.e ≫ n.e)
    (H' : m.IsPullCubical cK c) (H'' : m'.IsPullCubical cK c₀) : n.IsPullCubical c c₀ := by
  obtain ⟨F, F3, e, he', hp'⟩ := m'
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rw [isPullCubical_iff] at H' H'' ⊢
  obtain ⟨w', g', r', q'⟩ := H'
  obtain ⟨w'', g'', r'', q''⟩ := H''
  have := hG.smooth
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have a₂ : eSec GK ≫ GK.hom = 𝟙 _ := Over.w η[GK]
  obtain ⟨κ, κ', hκ, hκ'⟩ : ∃ (κ : pullback G.hom (spMap (algebraMap T K)) ⟶ GK.left)
      (κ' : GK.left ⟶ pullback G.hom (spMap (algebraMap T K))),
      κ ≫ m.F = pullback.fst G.hom (spMap (algebraMap T K)) ∧ κ' ≫ κ = 𝟙 _ :=
    ⟨hp.isoPullback.inv, hp.isoPullback.hom, hp.isoPullback_inv_fst, hp.isoPullback.hom_inv_id⟩
  have hj : κ' ≫ pullback.fst G.hom (spMap (algebraMap T K)) = m.F := by rw [← hκ, ← Category.assoc, hκ', Category.id_comp]
  obtain ⟨r, hr, vr⟩ := exists_quot_of_isos L₀.isLB L.isLB LK.isLB w' w'' g' g'' κ (pullback.fst G.hom (spMap (algebraMap T K))) hκ
  obtain ⟨ρ, hρ, vρ⟩ := exists_quot_of_gens n.e_comm L₀.rig L.rig L₀.rigGen L.rigGen
  have heA : (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K)) = spMap (algebraMap T K) ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm, he]
  have heA' : (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K)) = m.e ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm]
  have heκ : (eSec GK ≫ κ') ≫ κ = eSec GK := by rw [Category.assoc, hκ', Category.comp_id]
  obtain ⟨w, hw, hwr⟩ := hE G hG (eSec GK ≫ κ') heA
    ⟨LB.div (L₀.L.pull n.F) L.L, ρ, LB.isLB_div (pull_isLB L₀.isLB _) L.isLB, hρ⟩ r hr (by
      intro J J' _ _ hJ
      obtain rfl : J = J' := funext fun _ => hJ PUnit.unit PUnit.unit heA
      refine unit_ext fun y hy => ?_
      refine (gm_res _ y _ hy _).trans (Eq.trans ?_ (gm_res _ y _ hy _).symm)
      refine (gm_pullGen _ _ _ r _ (𝟙 _) y J hy.1).trans (Eq.trans ?_ (gm_pullGen _ _ _ ρ _ (𝟙 _) y J hy.2).symm)
      obtain ⟨k, hk⟩ := exists_chart LK.isLB (eSec GK y)
      have hm := (mem_qchart (j := (eSec GK ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K))) (a := (J PUnit.unit).1 PUnit.unit)
        (i := (J PUnit.unit).2)).1 hy.1
      have hm' := hm
      have hm'' := hm
      rw [heA'] at hm'
      rw [Category.assoc, hj] at hm''
      have e₁ := vr _ (eSec GK ≫ κ') y _ _ k hm.1 hm.2 (by
        show ((eSec GK ≫ κ') ≫ κ) y ∈ _
        rw [heκ]; exact hk)
      have e₂ := vρ _ m.e y _ _ hm'.1 hm'.2
      have e₃ := r'' _ (𝟙 _) y (fun _ => (J PUnit.unit).1 PUnit.unit) (fun _ => k) (fun _ => hm''.1) (fun _ => hk)
      have e₄ := r' _ (𝟙 _) y (fun _ => (J PUnit.unit).2) (fun _ => k) (fun _ => hm''.2) (fun _ => hk)
      rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₃ e₄
      rw [heκ] at e₁
      rw [e₃, e₄, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one] at e₂
      rw [Category.id_comp, Category.id_comp]
      refine e₁.trans (e₂.symm.trans ?_)
      rw [he]
      rfl)
  have tri : Tri (L := L₀.L) (L' := L.L) (F := n.F) w w' w'' := by
    intro Y f y a i k ha hi hk
    have p₁ : pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y)) = m.F (f y) := congrArg (fun g => g (f y)) hj
    have p₂ : κ (κ' (f y)) = f y := congrArg (fun g => g (f y)) hκ'
    have ha' : n.F (pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y))) ∈ L₀.L.U a := by rw [p₁]; exact ha
    have hi' : pullback.fst G.hom (spMap (algebraMap T K)) (κ' (f y)) ∈ L.L.U i := by rw [p₁]; exact hi
    have e₁ := vr _ (f ≫ κ') y a i k ha' hi' (by
      show κ (κ' (f y)) ∈ _
      rw [p₂]; exact hk)
    have hy : (f ≫ κ') y ∈ qchart L₀.L L.L n.F (pullback.fst G.hom (spMap (algebraMap T K))) a i := mem_qchart.2 ⟨ha', hi'⟩
    have e₂ : gm (f ≫ κ') y (qchart L₀.L L.L n.F (pullback.fst G.hom (spMap (algebraMap T K))) a i) (r.s (fun _ => (fun _ => a, i))) =
        gw (L := L₀.L) (L' := L.L) (F := n.F) w ((f ≫ κ') ≫ pullback.fst G.hom (spMap (algebraMap T K))) y a i := by
      rw [← hwr]
      exact (gm_res _ y _ hy _).trans (gm_pull (f ≫ κ') (pullback.fst G.hom (spMap (algebraMap T K))) y
        ((L₀.L.pull n.F).U (fun _ => a) ⊓ L.L.U i) ⟨mem_pull.2 ha', hi'⟩ _)
    rw [e₂, Category.assoc, Category.assoc, hj, hκ', Category.comp_id] at e₁
    rw [e₁, inv_mul_cancel_right]
  refine ⟨w, (isGen_iff _).1 hw, ?_, ?_⟩
  · refine pmaps_of_tri tri LK.isLB (fun _ => n.e_comm) (fun _ => m.e_comm) r' r'' (𝟙 _) ?_
    rw [Category.id_comp, he]
    exact app_injective_generic (p := 𝟙 _) (q := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  · have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    let P : Over (Sp K) := Over.mk (pullback.snd (G3 G).hom (spMap (algebraMap T K)))
    let x : Fin 3 → (P ⟶ GK) := fun i => Over.homMk
      (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ m.F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 GK := lift (x 0) (lift (x 1) (x 2))
    have hl : l.left ≫ m.F3 = pullback.fst (G3 G).hom (spMap (algebraMap T K)) := hom_ext_triple _ fun i => by
      have : l ≫ x3 GK i = x i := by fin_cases i <;> simp [l, x3]
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, this, hx]
    refine pmaps_of_tri tri LK.isLB (fun I => n.psum_comm I.down) (fun I => m.psum_comm I.down) q' q'' l.left ?_
    rw [hl]
    exact app_injective_generic (IsPullback.of_hasPullback _ _)

end Group

end GlobalTheory.ChartCubExt
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBEx

section Generic

variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {X : Scheme.{0}} (F : A.left ⟶ X) (M : LB X)

abbrev ThGen : Type := LB.Gen (LB.LinComb M (fun I : thK.{0} => thφ A (x3 A) I ≫ F) thε)

variable {A F M}

def pt3 (x y z : 𝟙_ (Over (Sp K)) ⟶ A) : Sp K ⟶ (G3 A).left := (lift x (lift y z)).left

def cv (t : ThGen A F M) (j : thK.{0} → M.ι) (x y z : 𝟙_ (Over (Sp K)) ⟶ A) : K :=
  valR (pt3 x y z) (LB.wchart M (fun I : thK.{0} => thφ A (x3 A) I ≫ F) j) (t.s j).val

variable [IsCommMonObj A]

def GCub (t : ThGen A F M) : Prop :=
  t.IsGen ∧ ∀ (T : Over (Sp K)) (z : T.left) (J : (T.left ⟶ X) → M.ι), Good M z J →
    IsCub fun a b c : T ⟶ A => val t (lift a (lift b c)).left z J

end Generic

def UnitAt {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {P : PolAV (Sp K)} {N : ℕ} (m : TGrp R K P N) {M : LB m.AA.left} (t : ThGen P.A m.φ M) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (z : Sp R) (x y w : Tor P N) (j : thK.{0} → M.ι),
    z.asIdeal = v.asIdeal →
    (lift (m.τ x) (lift (m.τ y) (m.τ w))).left z ∈ LB.wchart M (thφ m.AA (x3 m.AA)) j →
    v.valuation K (cv t j x.1 y.1 w.1) = 1

end GlobalTheory.MBEx

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX GlobalTheory.MBEx
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.OpenPartUnit

section General

variable {X Y Y' G B Z : Scheme.{0}}

theorem gs_appLE (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (h : r z ∈ W)
    (a : Γ(X, U)) : gs r z W ((f.appLE U W e).hom a) = gs (r ≫ f) z U a :=
  (gs_res r z e h _).trans (gs_pull r f z U (e h) a)

end General

end GlobalTheory.OpenPartUnit
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem exists_fibre_generic_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  intro R _ _ _ _ X _ q _ _ π hπp
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  let v : Sp R := ⟨Ideal.span {π}, hP⟩
  let V := Localization.AtPrime v.asIdeal
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {algebraMap R V π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hne : algebraMap R V π ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective V v.asIdeal.primeCompl_le_nonZeroDivisors)).2 hπp.ne_zero
  have : IsNoetherianRing V := IsLocalization.isNoetherianRing v.asIdeal.primeCompl V inferInstance
  have hnf : ¬ IsField V := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hpr : Submodule.IsPrincipal (IsLocalRing.maximalIdeal V) := ⟨⟨_, hmax⟩⟩
  have : IsDiscreteValuationRing V :=
    ((IsDiscreteValuationRing.TFAE V hnf).out 0 4).mpr hpr
  have hπ : Irreducible (algebraMap R V π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  let l := spMap (algebraMap R V)
  have : Flat l := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsPreimmersion l := IsPreimmersion.of_isLocalization v.asIdeal.primeCompl
  have H := IsPullback.of_hasPullback q l
  set ψ := pullback.fst q l
  set f := pullback.snd q l
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks ψ
  obtain ⟨h₁, h₂⟩ := DvrModel.isDiscreteValuationRing_stalk_generic hπ hs
  have h₃ := DvrModel.notMem_basicOpen_iff_specializes hπ hs
  have hlv : l (IsLocalRing.closedPoint V) = v :=
    PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := v.asIdeal))
  have h₄ := (DvrModel.notMem_basicOpen_iff f hπ _).1 ((h₃ _).2 specializes_rfl)
  generalize (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) (genericPoint _) = ξ
    at h₁ h₂ h₃ h₄
  let E := (asIso (ψ.stalkMap ξ)).commRingCatIsoToRingEquiv
  refine ⟨ψ ξ, ?_, fun x hx => ?_,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, h₄, hlv]
  · obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H x (IsLocalRing.closedPoint V)
      ((PrimeSpectrum.ext hx).trans hlv.symm)
    exact ((h₃ y).1 ((DvrModel.notMem_basicOpen_iff f hπ y).2 hy)).map ψ.continuous
  · rw [← MulEquiv.irreducible_iff E.toMulEquiv]
    convert h₂ using 1
    exact (ψ.germ_stalkMap_apply ⊤ ξ trivial _).trans
      (congrArg _ ((app_constFn H.w π).trans (constFn_top _ _)))

end GlobalTheory.VerticalUnit
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  atlas_forward_decl GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_eq_span_of_coheight_le_one (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R) (hq : GeneralizingMap q)
    (x : X) (hx : Order.coheight x ≤ 1) (hne : (q x).asIdeal ≠ ⊥) :
    ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  obtain ⟨π, hπP, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (q x).isPrime hne
  refine ⟨π, hπ, ?_⟩
  by_contra hQP
  have hQle : Ideal.span {π} ≤ (q x).asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπP
  have hQprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  let Q : PrimeSpectrum R := ⟨_, hQprime⟩
  have hQsp : Q ⤳ q x := (PrimeSpectrum.le_iff_specializes Q (q x)).1 hQle
  obtain ⟨x', hx'x, hqx'⟩ := hq hQsp
  let B : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hBQ : B ⤳ Q := (PrimeSpectrum.le_iff_specializes B Q).1 bot_le
  obtain ⟨x'', hx''x', hqx''⟩ := hq (hqx' ▸ hBQ)
  have h1 : x < x' := by
    refine lt_of_le_not_ge hx'x ?_
    intro h
    have h' : q x ⤳ q x' := h.map q.continuous
    rw [hqx'] at h'
    exact hQP (le_antisymm ((PrimeSpectrum.le_iff_specializes (q x) Q).2 h') hQle)
  have h2 : x' < x'' := by
    refine lt_of_le_not_ge hx''x' ?_
    intro h
    have h' : q x' ⤳ q x'' := h.map q.continuous
    rw [hqx', hqx''] at h'
    have hle : Ideal.span {π} ≤ ⊥ := (PrimeSpectrum.le_iff_specializes Q B).2 h'
    exact hπ.ne_zero (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hle))
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have : (2 : ℕ∞) ≤ Order.coheight x := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x'' + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight x' + 1 := by gcongr
      _ ≤ Order.coheight x := c1
  have := this.trans hx
  norm_num at this

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' : ∀ (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R), GeneralizingMap q → ∀ x : X, Order.coheight x ≤ 1 → (q x).asIdeal ≠ ⊥ → ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  atlas_forward_decl GlobalTheory.exists_prime_eq_span_of_coheight_le_one
end

section
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.VerticalUnit

theorem finite_coheight_one_notMem (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (S : Set X) (hS : IsOpen S) (hη : genericPoint X ∈ S) :
    {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  refine (hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_
  rintro x ⟨h1, hxS⟩
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
  set z := (hi Z hZ).genericPoint
  have hzS : z ∉ S := hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)
  have hxz : x ≤ z := hg.specializes hxZ
  have hzη : z < genericPoint X := lt_of_le_not_ge (genericPoint_specializes z)
    fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)
  refine ⟨Z, hZ, ?_⟩
  simp only [dif_pos (hi Z hZ)]
  by_contra hne
  have hxlt : x < z := lt_of_le_not_ge hxz fun h =>
    hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm
  have a1 := Order.coheight_add_one_le hxlt
  have a2 := Order.coheight_add_one_le hzη
  rw [h1] at a1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ 1 := a1
  exact absurd this (by decide)

end GlobalTheory.VerticalUnit
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (S : Set X), IsOpen S → genericPoint X ∈ S → {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  atlas_forward_decl GlobalTheory.VerticalUnit.finite_coheight_one_notMem
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem UnitAt.zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {s : X.functionField} (hs : UnitAt x s) (n : ℤ) :
    UnitAt x (s ^ n) := by
  obtain ⟨u, rfl⟩ := hs
  refine ⟨u ^ n, ?_⟩
  have := congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map] at this
  exact this

theorem UnitAt.prod {X : Scheme.{0}} [IsIntegral X] {x : X} {ι : Type} (s : Finset ι) (f : ι → X.functionField)
    (h : ∀ b ∈ s, UnitAt x (f b)) : UnitAt x (∏ b ∈ s, f b) :=
  Finset.prod_induction f (UnitAt x) (fun _ _ => UnitAt.mul) ⟨1, by simp⟩ h

theorem eq_of_specializes_of_coheight {X : Scheme.{0}} {x y : X} (h : y ⤳ x) (hx : Order.coheight x = 1)
    (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm (show x ⤳ y from h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [hx, hy] at this
  exact absurd this (by decide)

theorem unitAt_constFn {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Sp R) (x : X) (b : R)
    (hb : b ∉ (q x).asIdeal) : IsUnit (X.presheaf.germ ⊤ x trivial (constFn q ⊤ b)) := by
  rw [← Scheme.mem_basicOpen_top, constFn_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hb

theorem exists_const_mul_unitAt_coheight_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  intro R K _ _ _ _ _ _ _ X _ _ q _ _ κ hκ I U t hcov ht0 htr hgen
  classical
  have hgz : GeneralizingMap q := Flat.generalizingMap q
  have hinj := IsFractionRing.injective R K
  have hunit : ∀ (x : X) (b : R), b ∉ (q x).asIdeal → UnitAt x (κ (algebraMap R K b)) := fun x b hb =>
    ⟨(unitAt_constFn q x b hb).unit, by
      rw [IsUnit.unit_spec, hκ]
      exact X.presheaf.germ_stalkSpecializes_apply _ _ _⟩
  let S : Set X := {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
  have hS : IsOpen S := by
    change IsOpen {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => (U i).isOpen.inter (isOpen_unitAt _)
  have hg : genericPoint X ∈ S := by
    let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
    obtain ⟨y, -, hy⟩ := hgz ((PrimeSpectrum.le_iff_specializes p₀ (q (genericPoint X))).1 bot_le)
    exact (genericPoint_specializes y).mem_open hS (hgen y (by rw [hy]))
  have hB := GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint X S hS hg
  set B : Set X := {x : X | Order.coheight x = 1 ∧ x ∉ S} with hBdef
  have key : ∀ b ∈ B, ∃ π : R, Prime π ∧ (q b).asIdeal = Ideal.span {π} ∧
      (∀ x : X, (q x).asIdeal = Ideal.span {π} → b ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk b) ∧
      Irreducible (X.presheaf.germ ⊤ b trivial (constFn q ⊤ π)) := by
    rintro b ⟨h1, hbS⟩
    have hb0 : (q b).asIdeal ≠ ⊥ := fun h => hbS (hgen b h)
    obtain ⟨π, hπ, hqb⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz b h1.le hb0
    obtain ⟨ξ, -, hξ, hd, hirr⟩ := GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime R X q π hπ
    have hξ1 : Order.coheight ξ = 1 := by
      have e := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk ξ)
      rw [ringKrullDim_stalk_eq_coheight] at e
      exact_mod_cast e
    obtain rfl : b = ξ := eq_of_specializes_of_coheight (hξ b hqb) h1 hξ1
    exact ⟨π, hπ, hqb, hξ, hd, hirr⟩
  choose! π hπ hqπ hsp hdvr hirr using key
  have hstar : ∀ b ∈ B, ∀ x : X, Order.coheight x = 1 → π b ∈ (q x).asIdeal → x = b := by
    intro b hb x hx hmem
    have hx0 : (q x).asIdeal ≠ ⊥ := fun h => (hπ b hb).ne_zero (by rw [h, Ideal.mem_bot] at hmem; exact hmem)
    obtain ⟨π', hπ', hqx⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz x hx.le hx0
    have hdvd : π' ∣ π b := Ideal.mem_span_singleton.1 (hqx ▸ hmem)
    have hq : (q x).asIdeal = Ideal.span {π b} :=
      hqx.trans (Ideal.span_singleton_eq_span_singleton.2 (hπ'.associated_of_dvd (hπ b hb) hdvd))
    exact eq_of_specializes_of_coheight (hsp b hb x hq) hx hb.1
  have hne : ∀ b ∈ B, algebraMap R K (π b) ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).2 (hπ b hb).ne_zero
  have key2 : ∀ b ∈ B, ∃ (i : I) (n : ℤ), b ∈ U i ∧ UnitAt b (κ (algebraMap R K (π b)) ^ (-n) * t i) := by
    intro b hb
    obtain ⟨i, hi⟩ := hcov b
    have := hdvr b hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (hirr b hb) (ht0 i b hi)
    have e : algebraMap _ X.functionField (X.presheaf.germ ⊤ b trivial (constFn q ⊤ (π b))) =
        κ (algebraMap R K (π b)) := by
      rw [hκ]; exact X.presheaf.germ_stalkSpecializes_apply _ _ _
    have hπ' : κ (algebraMap R K (π b)) ≠ 0 := (map_ne_zero κ).2 (hne b hb)
    refine ⟨i, n, hi, u, ?_⟩
    rw [hu, e, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hπ', neg_add_cancel, zpow_zero,
      _root_.mul_one]
  have : Nonempty I := ⟨(hcov (genericPoint X)).choose⟩
  choose! ib n hUi hunitb using key2
  let F := hB.toFinset
  let a : Kˣ := ∏ b ∈ F.attach, (Units.mk0 _ (hne b.1 (hB.mem_toFinset.1 b.2))) ^ (-n b.1)
  have hκa : κ (a : K) = ∏ b ∈ F, κ (algebraMap R K (π b)) ^ (-n b) := by
    simp only [a, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
    exact Finset.prod_attach F (fun b => κ (algebraMap R K (π b)) ^ (-n b))
  refine ⟨a, fun i x hx h1 => ?_⟩
  rw [hκa]
  have hother : ∀ b ∈ F, b ≠ x → UnitAt x (κ (algebraMap R K (π b)) ^ (-n b)) := fun b hb hbx =>
    (hunit x (π b) fun hm => hbx (hstar b (hB.mem_toFinset.1 hb) x h1 hm).symm).zpow _
  by_cases hxS : x ∈ S
  · obtain ⟨j, hj, hu⟩ := hxS
    refine htr i j x _ hx hj ((UnitAt.prod F _ fun b hb => hother b hb ?_).mul hu)
    rintro rfl
    exact (hB.mem_toFinset.1 hb).2 ⟨j, hj, hu⟩
  · have hxB : x ∈ B := ⟨h1, hxS⟩
    have hxF : x ∈ F := hB.mem_toFinset.2 hxB
    rw [← Finset.mul_prod_erase F (fun b => κ (algebraMap R K (π b)) ^ (-n b)) hxF]
    refine htr i (ib x) x _ hx (hUi x hxB) ?_
    rw [mul_comm (κ (algebraMap R K (π x)) ^ (-n x)), mul_assoc]
    exact (UnitAt.prod _ _ fun b hb => hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).mul
      (hunitb x hxB)

end GlobalTheory.VerticalUnit
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_mul_unitAt_codimOne_of_factorialBase : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  atlas_forward_decl GlobalTheory.VerticalUnit.exists_const_mul_unitAt_coheight_one
end

section
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GlobalVerticalUnit
open GlobalTheory.VerticalUnit

theorem exists_const_mul_eq_gen : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∃ (a : Kˣ) (u : LB.Gen M), u.IsGen ∧ ∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val := by
  intro R K _ _ _ _ _ _ _ X Y φ p M c hsm hqc hgc H hM hc
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hsm hgc
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsIntegral Y := DvrModel.isIntegral_of_geometricallyIntegral H
  have := isNormalScheme_of_smooth X.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : AlgebraicGeometry.IsNoetherian X.left := {}
  have hinj := IsFractionRing.injective R K
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) H.flip
    (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip
    (IsPreimmersion.of_isLocalization (nonZeroDivisors R))
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks φ
  have lift : ∀ x : X.left, (X.hom x).asIdeal = ⊥ → ∃ y, φ y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum K)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective _ hinj).symm))
    exact ⟨y, hy⟩
  have hφ : φ (genericPoint Y) ⤳ genericPoint X.left := by
    obtain ⟨y, hy⟩ := (Flat.generalizingMap φ).stableUnderGeneralization_range
      (genericPoint_specializes (φ (genericPoint Y))) ⟨_, rfl⟩
    exact hy ▸ (genericPoint_specializes y).map φ.continuous
  have hne : ∀ (V : X.left.Opens) [Nonempty V], Nonempty (φ ⁻¹ᵁ V) := fun V _ =>
    ⟨⟨_, hφ.mem_open V.isOpen (genericPoint_mem_opens V)⟩⟩
  have hne' : ∀ i [Nonempty (M.U i)], Nonempty ((M.pull φ).U fun _ => i) := fun i _ => by
    rw [DvrModel.pull_U]; exact hne _
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hb := ffMap_bijective φ hφ
  obtain ⟨r, hr⟩ : ∃ r : M.ι → X.left.functionField, ∀ i [Nonempty ((M.pull φ).U fun _ => i)],
      ffMap φ hφ (r i) = Y.germToFunctionField _ (c.s fun _ => i).val := by
    have : ∀ i, ∃ t : X.left.functionField, ∀ [Nonempty ((M.pull φ).U fun _ => i)],
        ffMap φ hφ t = Y.germToFunctionField _ (c.s fun _ => i).val := fun i => by
      by_cases h : Nonempty ((M.pull φ).U fun _ => i)
      · exact (hb.2 (Y.germToFunctionField _ (c.s fun _ => i).val)).imp fun _ h => h
      · exact ⟨0, @fun h' => (h h').elim⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  let k : K →+* Γ(Y, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let κ : K →+* X.left.functionField := (RingEquiv.ofBijective (ffMap φ hφ).hom hb).symm.toRingHom.comp
    ((Y.germToFunctionField ⊤).hom.comp k)
  have hκ : ∀ a, ffMap φ hφ (κ a) = Y.germToFunctionField ⊤ (constFn p ⊤ a) := fun a =>
    (RingEquiv.ofBijective (ffMap φ hφ).hom hb).apply_symm_apply _
  have hr0 : ∀ i x, x ∈ M.U i → r i ≠ 0 := fun i x hx h => by
    have : Nonempty (M.U i) := ⟨⟨x, hx⟩⟩
    have := hne' i
    have e := hr i
    rw [h, map_zero] at e
    exact ((Units.isUnit _).map _).ne_zero e.symm
  have hg : ∀ i j (x : X.left) (hi : x ∈ M.U i) (hj : x ∈ M.U j),
      haveI : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      r i = X.left.germToFunctionField (M.U i ⊓ M.U j) (M.g i j).val * r j := by
    intro i j x hi hj
    have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
    have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
    have := hne' i
    have := hne' j
    have := nonempty_inf_of_isIntegral ((M.pull φ).U fun _ => i) ((M.pull φ).U fun _ => j)
    refine hb.1 ?_
    have e := congrArg (Y.germToFunctionField _) (congrArg Units.val (hc (fun _ => i) fun _ => j))
    rw [Units.val_mul, map_mul, DvrModel.coe_pull_g, ← ffMap_germ φ hφ] at e
    rw [map_mul, hr, hr]
    exact (germToFunctionField_res _ _).symm.trans (e.trans (congrArg _ (germToFunctionField_res _ _)))
  have htr : ∀ i j x t, x ∈ M.U i → x ∈ M.U j → UnitAt x (t * r j) → UnitAt x (t * r i) := by
    intro i j x t hi hj h
    rw [hg i j x hi hj, mul_left_comm]
    exact UnitAt.mul ⟨Units.map (X.left.presheaf.germ (M.U i ⊓ M.U j) x ⟨hi, hj⟩).hom (M.g i j),
      X.left.presheaf.germ_stalkSpecializes_apply _ _ _⟩ h
  have hκR : ∀ b : R, κ (algebraMap R K b) = X.left.presheaf.germ ⊤ (genericPoint X.left) trivial (constFn X.hom ⊤ b) := fun b => hb.1 (by
    rw [hκ, ← app_constFn H.w, ← φ.appLE_eq_app]
    exact (ffMap_germ φ hφ ⊤ ⊤ le_top _).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_const_mul_unitAt_codimOne_of_factorialBase R K X.left X.hom κ hκR M.ι M.U r (LB.mem_of_cover hM) (fun i x hx => hr0 i x hx) htr (fun x hx => by
    obtain ⟨y, rfl⟩ := lift x hx
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM (φ y)
    have : Nonempty (M.U i) := ⟨⟨_, hi⟩⟩
    have := hne' i
    exact ⟨i, hi, unitAt_of_isUnit φ hφ (Units.isUnit _) ((DvrModel.pull_U M φ _).ge hi) (hr i)⟩)
  have hu : ∀ i, ∃ v : Γ(X.left, M.U i)ˣ, ∀ [Nonempty (M.U i)],
      X.left.germToFunctionField (M.U i) v.val = κ a * r i := fun i => by
    by_cases h : Nonempty (M.U i)
    · obtain ⟨v, hv⟩ := exists_unit_eq (M.U i) (κ a * r i)
        (mul_ne_zero ((map_ne_zero κ).2 a.ne_zero) (hr0 i _ h.some.2)) (ha i)
      exact ⟨v, @fun _ => hv⟩
    · exact ⟨1, @fun h' => (h h').elim⟩
  choose u hu using hu
  refine ⟨a, ⟨u⟩, fun i j => ?_, fun i Z rr z hz => ?_⟩
  · by_cases h : Nonempty (M.U i ⊓ M.U j : X.left.Opens)
    · obtain ⟨⟨x, hi, hj⟩⟩ := h
      have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
      have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
      have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      refine Units.ext (X.left.germToFunctionField_injective (M.U i ⊓ M.U j) ?_)
      show X.left.germToFunctionField _ (X.left.presheaf.map (homOfLE _).op (u i).val) =
        X.left.germToFunctionField _ ((M.g i j).val * X.left.presheaf.map (homOfLE _).op (u j).val)
      rw [map_mul, germToFunctionField_res, germToFunctionField_res, hu, hu, hg i j x hi hj]
      ring
    · exact unit_ext fun x hx => (h ⟨⟨x, hx⟩⟩).elim
  · have hm : rr z ∈ (M.pull φ).U fun _ => i := mem_pull.2 hz
    have h₂ : ((M.pull φ).U fun _ => i) ≤ φ ⁻¹ᵁ M.U i := fun y hy => mem_pull.1 hy
    have : Nonempty ((M.pull φ).U fun _ => i) := ⟨⟨_, hm⟩⟩
    have : Nonempty (M.U i) := ⟨⟨_, hz⟩⟩
    have hW : (φ.appLE (M.U i) _ h₂).hom (u i).val = constFn p _ (a : K) * (c.s fun _ => i).val := by
      refine Y.germToFunctionField_injective _ ((ffMap_germ φ hφ _ _ h₂ _).symm.trans ?_)
      rw [hu, map_mul, map_mul, hκ, hr]
      refine congrArg₂ (· * ·) ?_ rfl
      exact (germToFunctionField_res (le_top : ((M.pull φ).U fun _ => i) ≤ ⊤) _).symm.trans
        (congrArg _ (res_appLE_apply p _ _ _))
    show (gm (rr ≫ φ) z (M.U i) (u i)).val = _
    rw [← gs_unit (rr ≫ φ) z _ hz, ← gs_unit rr z _ hm, ← GlobalTheory.OpenPartUnit.gs_appLE rr φ z _ _ h₂ hm, hW,
      gs_mul rr z _ hm]
    refine congrArg (· * _) ?_
    exact GlobalTheory.OpenPartUnit.gs_appLE rr p z ⊤ _ _ hm _

end GlobalTheory.GlobalVerticalUnit
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_mul_eq_generator_factorial_base : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∃ (a : Kˣ) (u : LB.Gen M), u.IsGen ∧ ∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val := by
  atlas_forward_decl GlobalTheory.GlobalVerticalUnit.exists_const_mul_eq_gen
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rigUnit_exists_ratio {X Y : Scheme.{0}} (M : LB X) (hM : M.IsLB) (f : Y ⟶ X)
    (t t' : LB.Gen (M.pull f)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → M.ι), r z ∈ (M.pull f).U j →
      gm r z ((M.pull f).U j) (t.s j) = gm r z ⊤ w * gm r z ((M.pull f).U j) (t'.s j) := by
  obtain ⟨w, hw⟩ := glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM (f y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      have h1 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      have h2 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans
        (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rfl)
  refine ⟨w, fun Z r z j hj => ?_⟩
  have e := (gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))
  rw [e, map_mul, map_inv, inv_mul_cancel_right]

theorem rigUnit_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  intro R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H
  obtain ⟨w, hw⟩ := rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig
  haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by
    have := IsLocalization.epi (nonZeroDivisors R) K
    exact this
  haveI : Mono (spMap (algebraMap R K)) := by
    exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
  have hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _ := by
    rw [← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA,
      Category.assoc, he, Category.comp_id, Category.id_comp]
  let z : Sp K := (⊥ : PrimeSpectrum K)
  choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)
  have hG : Good M z J := hJ
  have hv := val_corr hG hcorr (𝟙 _)
  rw [val_pull hG, val_pull hG, Category.id_comp, Category.id_comp,
    val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]),
    val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)] at hv
  have hi := hJ (spMap (algebraMap R K) ≫ e)
  generalize J (spMap (algebraMap R K) ≫ e) = i at hv hi
  have h1 := H i _ eA z (by
    have : (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i := by rw [heA]; exact hi
    exact this)
  rw [heA, hsnd] at h1
  have hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i) := mem_pull.2 hi
  have h2 := hw _ (spMap (algebraMap R K)) z (fun _ => i) hm
  have h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) =
      gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i) :=
    (gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)
  have h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val =
      gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
    have h5 := (congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))
    rw [Units.val_mul] at h5
    exact (Units.mul_left_inj _).1 h5
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  apply φ.injective
  rw [gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at h4
  refine Eq.trans ?_ h4
  change ((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _
  congr 1
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n
  exact n

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  atlas_forward_decl GlobalTheory.rigUnit_exists
end

section
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DivConst

theorem gs_const {R K : Type} [CommRing R] [CommRing K] (g : R →+* K) {X Y : Scheme.{0}} {q : X ⟶ Sp R}
    {p : Y ⟶ Sp K} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (y : Y) (b : R) :
    gs φ y ⊤ (q.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) =
      gs p y ⊤ ((Scheme.ΓSpecIso (.of K)).inv.hom (g b)) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp R ↦ φ.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) w
  have h₂ := congrArg (fun φ : CommRingCat.of R ⟶ Γ(Spec (.of K), ⊤) ↦ φ.hom b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [gs_eq φ y ⊤ trivial, gs_eq p y ⊤ trivial]
  exact congrArg (Y.presheaf.germ ⊤ y trivial).hom (h₁.trans (congrArg p.appTop.hom h₂.symm))

theorem exists_genPull_eq : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  intro R K _ _ _ X Y φ p w M c a b hab u hu H
  let β : Γ(X.left, ⊤)ˣ := Units.map (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toMonoidHom b
  refine ⟨⟨fun i => u.s i * (res le_top β)⁻¹⟩, fun i j => unit_ext fun x hx => ?_, ?_⟩
  · have e := congrArg (gm (𝟙 X.left) x (M.U i ⊓ M.U j)) (hu i j)
    simp only [map_mul, map_inv] at e ⊢
    rw [e, gm_res _ x _ hx (res le_top β), gm_res _ x _ hx (res le_top β), gm_res _ x _ hx.1 β,
      gm_res _ x _ hx.2 β, mul_assoc]
  · obtain ⟨s⟩ := c
    refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
    have hy' : φ y ∈ M.U (j PUnit.unit) := mem_pull.1 hy
    refine (gm_res _ y _ hy _).trans ((gm_pull (𝟙 Y) φ y _ hy' _).trans ?_)
    have e := H (j PUnit.unit) Y (𝟙 Y) y hy'
    have e' : (gm (𝟙 Y ≫ φ) y ⊤ β).val = gs (𝟙 Y ≫ p) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
      rw [← gs_unit _ y ⊤ trivial, ← hab, Category.id_comp, Category.id_comp]
      exact gs_const _ w y b
    rw [← e', ← Units.val_mul] at e
    rw [map_mul, map_inv, gm_res (𝟙 Y ≫ φ) y _ hy' β, Units.ext e, mul_inv_cancel_comm]
    rfl

end GlobalTheory.DivConst
end

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  atlas_forward_decl GlobalTheory.DivConst.exists_genPull_eq
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem extendGenAt_chartRing : ∀ (k : Type) [Field k] (m n : ℕ),
    GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  intro k _ m n
  have : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  have := GlobalTheory.isRegularRing_of_isRegularLocalRing (ChartRing k m n)
  have : IsDomain (ChartRing k m n) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).1
  have : UniqueFactorizationMonoid (ChartRing k m n) := GlobalTheory.ThetaExtend.ufd_of_regular _
  intro G _ _ hG eA heA N r hr hc
  have := hG.smooth
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨a, u, hu, hf⟩ := GlobalTheory.T.exists_const_mul_eq_generator_factorial_base _ _ G _ _ _ N.L r inferInstance inferInstance inferInstance
    (IsPullback.of_hasPullback _ _) N.isLB hr
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator _ _ G (eSec G) (Over.w η[G]) eA heA N.L N.rig r N.isLB N.rigGen hc a u hu hf
  exact GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic _ _ G _ _ _ pullback.condition N.L r a b hb u hu hf

end GlobalTheory.ChartCubExt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing : ∀ (k : Type) [Field k] (m n : ℕ), GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  atlas_forward_decl GlobalTheory.ChartCubExt.extendGenAt_chartRing
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem cube_pull_of_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  intro E _ _ _ H k _ m n tC S G _ _ ξ πC hG hπ PP cub X' tF j e cm hcF hce hcm y hy tK a b hab
  refine ⟨cubeMapOf hπ, rfl, rfl, ?_⟩
  let c2 : CubeMap tK.G G :=
    { F := b.cm.F ≫ cm.F, F3 := b.cm.F3 ≫ cm.F3, e := b.cm.e ≫ cm.e
      e_comm := by rw [← Category.assoc, b.cm.e_comm, Category.assoc, cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, b.cm.psum_comm, Category.assoc, cm.psum_comm, Category.assoc] }
  let c3 : CubeMap tK.G G :=
    { F := a.cm.F ≫ (cubeMapOf hπ).F, F3 := a.cm.F3 ≫ (cubeMapOf hπ).F3, e := a.cm.e ≫ (cubeMapOf hπ).e
      e_comm := by rw [← Category.assoc, a.cm.e_comm, Category.assoc, (cubeMapOf hπ).e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, a.cm.psum_comm, Category.assoc, (cubeMapOf hπ).psum_comm, Category.assoc] }
  have H2 : c2.IsPullCubical tK.cub cub :=
    pullCubComp _ _ _ _ _ _ cm b.cm c2 _ _ _ _ _ _ rfl rfl rfl hcm b.lin
  have h₁ : c2.F = a.cm.F ≫ (cubeMapOf hπ).F := by
    show b.cm.F ≫ cm.F = a.cm.F ≫ πC
    rw [hcF]; exact hab.symm
  have h₂ : c2.F3 = a.cm.F3 ≫ (cubeMapOf hπ).F3 := by
    show c2.F3 = c3.F3
    refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three c2 i, cubeMap_comp_proj_three c3 i]
    exact congrArg (fun z => (x3 tK.G i).left ≫ z) h₁
  have h₃ : c2.e = a.cm.e ≫ (cubeMapOf hπ).e := by
    show b.cm.e ≫ cm.e = a.cm.e ≫ ξ
    rw [b.base, hce, a.base, hy]
  exact GlobalTheory.ChartCubExt.isPullCubical_of_generic_of_ext (GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing k m n) tC.semi cub tC.cub tK.cub
    (cubeMapOf hπ) a.cm c2 a.cart.1 a.base h₁ h₂ h₃ a.lin H2

end GlobalTheory.ChartCubExt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidCubicalExtension_pullback_of_toricChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  atlas_forward_decl GlobalTheory.ChartCubExt.cube_pull_of_chart
end
