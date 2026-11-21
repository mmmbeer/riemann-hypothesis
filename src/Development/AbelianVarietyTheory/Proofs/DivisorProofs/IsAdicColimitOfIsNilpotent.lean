import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneNonproperPowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SplitMultiplicative

open IsLocalRing

section Curve

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.WeierstrassCurve GlobalTheory.MultiplicativeReduction

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem isUnit_one_sub {a : V} (ha : a ∈ maximalIdeal V) : IsUnit (1 - 64 * a) :=
  isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left (maximalIdeal V) 64 ha)

theorem isElliptic_generic {a : V} (ha : a ∈ maximalIdeal V) (ha0 : a ≠ 0) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve V).map (algebraMap _ (FractionRing V))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  have : (⟨1, 0, 0, a, 0⟩ : WeierstrassCurve V).Δ = a ^ 2 * (1 - 64 * a) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [this]
  exact mul_ne_zero (pow_ne_zero _ ha0) (isUnit_one_sub ha).ne_zero

theorem isSemiAbelian_and_specialFibre {a : V} (ha : a ∈ maximalIdeal V) : ∀ (W : WeierstrassCurve V), W = ⟨1, 0, 0, a, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : V →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : V →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField V))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : V →+* K), f a = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : V →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f a = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = a ^ 2 * (1 - 64 * a) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * a : V) := isUnit_one_sub ha
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · exact (IsLocalRing.residue_eq_zero_iff a).2 ha

theorem exists_semiAbelian_polarised {a : V} (ha : a ∈ maximalIdeal V) (ha0 : a ≠ 0) : ∃ (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (eA : (Over.pullback (jK V)).obj G ≅ A.A) (i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField V))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj G), IsSemiAbelian G ∧ IsMonHom eA.hom ∧ IsMonHom i.hom ∧ A.g = 1 ∧ ∃ (LG : RigLB G) (_c : CubicalStr G LG) (s : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen ∧ LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ s (eSec G)) (LB.oneGen LG.L) ∧ (∃ w : LB.Iso (A.L.pull eA.hom.left) (LG.L.pull (pullback.fst G.hom (jK V))), w.IsGen) ∧ ∃ θ : H0 LG.L 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨W, hW⟩ : ∃ W : WeierstrassCurve V, W = ⟨1, 0, 0, a, 0⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU, hsm, hqc, hgi⟩ := exists_smoothLocus _ W
  have hs : Smooth (U.ι ≫ toSpec W) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, _, hη, hmul⟩ := GlobalTheory.exists_grpObj_smoothLocus _ W U hU hs hgi
  obtain ⟨hG, i, hi⟩ := isSemiAbelian_and_specialFibre ha W hW U hU hs hgi hqc hmul
  let f := algebraMap V (FractionRing V)
  have : (W.map f).IsElliptic := hW ▸ isElliptic_generic ha ha0
  obtain ⟨φ, hφ⟩ := exists_iso_schemeOver f W U hU
  let G := Over.mk (U.ι ≫ toSpec W)
  let j := pullback.fst G.hom (jK V)
  have hη' : (η[(Over.pullback (jK V)).obj G]).left ≫ j ≫ U.ι = jK _ ≫ zero W := by
    rw [← hη, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U.ι) (one_pullback_fst _ G)
  have hP : IsUnimodularSol (W.map f) ![0, 0, 1] := hW ▸ isUnimodularSol_twoPt _ _
  have hX : f a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha0
  have hPU := (hU _ f _ hP).2 (hW ▸ (nonsingular_twoPt _ f).2 hX)
  have hr : Set.range (ptHom W f _ hP) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hPU (Set.mem_univ y)
  have hb := IsOpenImmersion.lift_fac U.ι (ptHom W f _ hP) hr
  have hb' : IsOpenImmersion.lift U.ι (ptHom W f _ hP) hr ≫ U.ι ≫ toSpec W = jK _ := by
    rw [← Category.assoc, hb, ptHom_toSpec]
  let b : Over.mk (jK V) ⟶ G := Over.homMk _ hb'
  let x : 𝟙_ _ ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift b.left (𝟙 _) (hb'.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  have hxa : x.left ≫ j = b.left := pullback.lift_fst _ _ _
  have hx : x * x = 1 := by
    have h₁ : (1 : 𝟙_ _ ⟶ (Over.pullback (jK V)).obj G) = η[_] := by rw [Hom.one_def]; simp
    rw [h₁]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have h₂ := SmoothLocusBaseChange.lift_mul_pullback_fst (jK V) G x x (𝟙 _) b b
      (hxa.symm.trans (Category.id_comp _).symm) (hxa.symm.trans (Category.id_comp _).symm)
    obtain ⟨h, h₃⟩ := hmul _ f b b _ _ hP hP hb hb
    refine (cancel_mono U.ι).1 ?_
    refine Eq.trans ?_ (hη'.symm.trans (Category.assoc _ _ _).symm)
    refine (congrArg (· ≫ U.ι) (h₂.trans (Category.id_comp _))).symm.trans (h₃.trans ?_)
    rw [SpecMap_zero, ptHom_eq_ptHom_iff_minors]
    obtain ⟨h₄, h₅⟩ := add_twoPt a f
    rw [← hW] at h₄ h₅
    intro m l
    fin_cases m <;> fin_cases l <;> simp [h₄, h₅]
  have hz : (η[(Over.pullback (jK V)).obj G]).left ≫ φ.hom.left = zero (W.map f) := by
    apply (isPullback_mapHom W f rfl).hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hφ).trans (hη'.trans (zero_mapHom W f rfl).symm))
    · exact (Over.w (η[(Over.pullback (jK V)).obj G] ≫ φ.hom)).trans (zero_toSpec _).symm
  obtain ⟨A, eA, θ, heA, hg, hθ⟩ := exists_pol_twoTorsion hL (W.map f) _ φ hz x hx
  obtain ⟨LG, c, s, hs₁, hs₂, w, hw⟩ := PolExtension.exists_cubical_symmetric_extension hL _ G hG A eA heA
  refine ⟨G, inferInstance, inferInstance, A, eA, i, hG, heA, hi, hg, LG, c, s, hs₁, hs₂, ⟨w, hw⟩, ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_of_iso A.isLB (pull_isLB LG.isLB j) eA.hom.left ⟨w, hw⟩ θ
  have ht' : ∀ z, z ∈ nonzeroLocus t ↔ z ∉ Set.range x.left := fun z => (ht z).trans (hθ z)
  refine exists_sec_generates_specialFibre _ G hG LG.L LG.isLB t
    ⟨(η[(Over.pullback (jK V)).obj G]).left (IsLocalRing.closedPoint _), (ht' _).2 ?_⟩ ?_
  · rintro ⟨p, hp⟩
    have h₁ : ptHom W f _ hP p ∈ coordOpen W 2 := (ptHom_preimage_coordOpen W f _ hP 2).ge
      (PrimeSpectrum.basicOpen_one.ge (Set.mem_univ p))
    have h₂ : ptHom W f _ hP p = zero W (jK _ (IsLocalRing.closedPoint _)) :=
      (congrArg (fun q => q p) ((congrArg (· ≫ U.ι) hxa).trans hb)).symm.trans
        ((congrArg (j ≫ U.ι) hp).trans (congrArg (fun q => q (IsLocalRing.closedPoint _)) hη'))
    rw [h₂] at h₁
    exact (zero_preimage_coordOpen_two W).le h₁
  · have e : j '' {z | z ∉ nonzeroLocus t} = Set.range b.left := by
      rw [← hxa]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := not_not.1 (mt (ht' z).2 hz)
        exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨x.left p, fun h => (ht' _).1 h ⟨p, rfl⟩, rfl⟩
    exact e ▸ isClosed_twoPt ha W hW U hU b.left hP hb

end Curve

open GlobalTheory.UU GlobalTheory.MultiplicativeTorusSetting GlobalTheory.TateUnif

theorem not_isProper_torus_of_infinite (k : Type) [Field k] [Infinite k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h => by
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, hp, h0⟩ := isIntegral_appTop_of_universallyClosed (splitTorus (Spec (CommRingCat.of k)) ℤ).hom
    (charUnit (Spec (CommRingCat.of k)) ℤ 1).val
  have root : ∀ a : kˣ, (p.map e.symm.toRingHom).IsRoot a.val := fun a => by
    let t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ splitTorus (Spec (CommRingCat.of k)) ℤ :=
      (splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ (Units.map e.toMonoidHom a))
    have h₁ : t.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) ℤ 1).val = e a.val := by
      rw [← chV_val, chV, MulEquiv.apply_symm_apply]
      exact congrArg Units.val (zpow_one (Units.map e.toMonoidHom a))
    have h₂ : t.left.appTop.hom.comp (splitTorus (Spec (CommRingCat.of k)) ℤ).hom.appTop.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]
      exact congrArg CommRingCat.Hom.hom Scheme.Hom.id_appTop
    have h₃ := congrArg t.left.appTop.hom h0
    rw [Polynomial.hom_eval₂, h₂, h₁, map_zero] at h₃
    have h₄ := congrArg e.symm.toRingHom h₃
    rw [Polynomial.hom_eval₂, map_zero] at h₄
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h₄
  have inf : Set.Infinite {x | (p.map e.symm.toRingHom).IsRoot x} :=
    (Set.finite_singleton (0 : k)).infinite_compl.mono fun x hx => root (Units.mk0 x hx)
  exact (hp.map _).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ inf)

theorem not_isProper_torus (k : Type) [Field k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h =>
  not_isProper_torus_of_infinite (AlgebraicClosure k) (MorphismProperty.of_isPullback (P := @IsProper)
    (SplitTorus.isGrpPullback_bcMap (spMap (algebraMap k (AlgebraicClosure k))) ℤ).1 h)

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]

theorem exists_setting (hV : CDVR V) : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (s : HidaSetting V A G), A.g = 1 ∧ Module.finrank ℤ s.X = 1 ∧ ¬ IsProper (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom := by
  obtain ⟨laws, laws₂, -⟩ := GlobalTheory.allSixLaws
  have := hV.1
  obtain ⟨a, ha'⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨G, _, _, A, eA, i, hG, hA, hi, hg, L, -, -, -, -, hw, θ, hθ⟩ :=
    exists_semiAbelian_polarised (a := a) ha'.not_isUnit ha'.ne_zero
  obtain ⟨P, rfl⟩ := CubicalPackage.exists_package laws _ hV A G hG eA hA L hw
  have := hG.smooth
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK _) (eA.inv.left ≫ pullback.fst G.hom (jK _)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK _))).congr (Category.id_comp _) rfl
  have hinv : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨s, hs⟩ := exists_even_sec laws₂.secTwist A gp P
    (LBIso.chartPull (chartPullSec A.L _ eA.inv.left hinv) (chartPullSame P.L.L _ _ _ eA.inv.left fun _ => rfl) hw) θ
    (hθ _ (congrArg (fun q => q (IsLocalRing.closedPoint V)) (Over.w η[G])))
  obtain ⟨r, hr⟩ := thick_zero_factor V
  obtain ⟨i₀, hi₀, -⟩ := grpPullback_iso
    (((SplitTorus.isGrpPullback_bcMap r ℤ).comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G _))).congr
      ((congrArg (r ≫ ·) (Category.id_comp _)).trans hr.symm) rfl)
    (isGrpPullback_pullback G (thick _ (IsLocalRing.maximalIdeal V) 0))
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  obtain ⟨wA, hwA⟩ := hw
  refine ⟨A, G, inferInstance, inferInstance, ⟨hV, hG, eA, hA, P, wA, hwA, ℤ, tqOfIso i₀, P₀, ⟨w₀, h₀⟩,
    exists_even_cubTriv i₀ h₀ s (fun y J hJ => (hs _ _ y J hJ).1 (hθ _ ?_)) fun Z r z J hJ => (hs Z r z J hJ).2⟩,
    hg, Module.finrank_self ℤ, fun h => not_isProper_torus
      (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) ?_⟩
  · exact (congrArg (fun q => q y) (pullback.condition.trans (congrArg (_ ≫ ·) hr))).trans
      (IsLocalRing.PrimeSpectrum.comap_residue _ (r (pullback.snd G.hom _ y)))
  · have : IsIso i₀.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i₀.hom))
    rw [← Over.w i₀.hom]
    infer_instance

end GlobalTheory.SplitMultiplicative

end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

def pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y =>
    ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem actPull_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {Λ : Type} [Ring Λ]
    (ρ : RingAct G Λ) (a : Λ) :
    ((actPull f ρ).act a).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ρ.act a).left :=
  pullback.lift_fst _ _ _

variable {p : ℕ} {R : Type} [CommRing R] {I : Ideal R} {O : Type} [CommRing O]

theorem isAdicColimit_of_isNilpotent {f : R →+* O} (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) :
    IsAdicColimit I (Over.mk ((specO O S).hom ≫ spMap f)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hS
  have e : (specO O S).hom ≫ spMap f = Spec.map (CommRingCat.ofHom ((algebraMap O S).comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  rw [e]
  refine isAdicColimit_of_pow I _ (n * m) fun a ha => ?_
  have h₁ : (I ^ n).map f ≤ Ideal.span {(p : O)} := Ideal.map_le_iff_le_comap.2 hn
  have h₂ : f a ∈ Ideal.span {(p : O) ^ m} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono h₁ m ?_
    rw [← Ideal.map_pow, ← pow_mul]
    exact Ideal.mem_map_of_mem f ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h₂
  rw [RingHom.comp_apply, ← hc, map_mul, map_pow, map_natCast, hm, mul_zero]

variable [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem spMap_comp_algebraMap (f : R →+* O) :
    spMap ((algebraMap O C).comp f) = spMap (algebraMap O C) ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def ofCompletion (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (ιG : RingAct G Λ)
    {E : SplitExt (Sp R)} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] (d : E.GtDatum H) (ρ : RingAct H Λ)
    (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)))
    (hnat : ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x)
    (hlin : ∀ T hT (x : T ⟶ H) (a : Λ), J T hT (x ≫ ρ.act a) = J T hT x ≫ ιG.act a)
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) : Point p v O Λ where
  integers := hv
  eps := ε
  A := A'
  oA := oA'
  G := (Over.pullback (spMap f)).obj G
  semi := IsSemiAbelian.pullback _ G hG
  gen := pullback.lift j (A'.A.hom ≫ spMap (algebraMap O C))
    (by rw [hj.1.w, spMap_comp_algebraMap, Category.assoc])
  gen_pull := (isGrpPullback_pullback G (spMap f)).cancel
    (hj.congr (spMap_comp_algebraMap f) (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  oG := actPull (spMap f) ιG
  gen_act a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hact, Category.assoc, actPull_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.lift_snd, Over.w_assoc, Category.assoc]
      exact ((congrArg (_ ≫ ·) (Over.w ((actPull (spMap f) ιG).act a))).trans (pullback.lift_snd _ _ _)).symm
  Ext := GtBaseChange.extBC (spMap f) E
  Gt := (Over.pullback (spMap f)).obj H
  D := (GtBaseChange.isGt_extBC (spMap f) E H d).some
  oGt := actPull (spMap f) ρ
  cmp S _ _ hS := (pushEquiv (isGrpPullback_pullback H (spMap f)) _).trans
    ((J _ (isAdicColimit_of_isNilpotent hf S hS)).trans (pushEquiv (isGrpPullback_pullback G (spMap f)) _).symm)
  cmp_nat S S' _ _ _ _ hS hS' φ x := by
    let k : Over.mk ((specO O S').hom ≫ spMap f) ⟶ Over.mk ((specO O S).hom ≫ spMap f) :=
      Over.homMk (ptMap φ).left (Over.w_assoc (ptMap φ) _)
    have e : ∀ {X : Over (Sp R)} [GrpObj X] (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (ptMap φ ≫ y) =
          k ≫ pushEquiv (isGrpPullback_pullback X (spMap f)) _ y := fun y =>
      Over.OverMorphism.ext (Category.assoc _ _ _)
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hnat]
  cmp_act S _ _ hS a x := by
    have e : ∀ {X : Over (Sp R)} [GrpObj X] [IsCommMonObj X] (α : RingAct X Λ)
        (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (y ≫ (actPull (spMap f) α).act a) =
          pushEquiv (isGrpPullback_pullback X (spMap f)) _ y ≫ α.act a := fun α y =>
      Over.OverMorphism.ext ((Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) (actPull_fst _ α a)).trans (Category.assoc _ _ _).symm))
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hlin]

section Unif

variable [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_comparison : ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H)
    (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T) (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G))),
    (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ T hT w x, J T hT w = x ↔ FormalPoint.IsPointOf U (Φ T w) x) ∧
      ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hL (Φ := Φ) hΦ
  exact ⟨H, inferInstance, inferInstance, Φ, J, hH, hΦ, hJ, fun T T' hT hT' k x =>
    (hJ _ hT' _ _).2 (((hJ _ hT x _).1 rfl).pull k (hΦ.1 _ _ k _))⟩

theorem exists_point_of_unif (hG : IsSemiAbelian G) [Module Λ D.toPre.X] {ιD : D.OAct Λ} {ιA : A.OAct Λ}
    {ιG : RingAct G Λ} (hO : U.OLinear Λ ιD ιA ιG) (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) :
    ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T)
      (ρ : RingAct H Λ) (P : Point p v O Λ),
      (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ (a : Λ) T (x : T ⟶ H), FormalPoint.IsSmulPt ιD a (Φ T x) (Φ T (x ≫ ρ.act a))) ∧
      P.eps = ε ∧ P.A = A' ∧ HEq P.oA oA' ∧ P.G = (Over.pullback (spMap f)).obj G ∧
      P.Ext = GtBaseChange.extBC (spMap f) (splitExt D.toPre) ∧ P.Gt = (Over.pullback (spMap f)).obj H ∧
      ∃ (πG : P.G.left ⟶ G.left) (πH : P.Gt.left ⟶ H.left) (hπG : IsGrpPullback P.G G (spMap f) πG)
        (hπH : IsGrpPullback P.Gt H (spMap f) πH),
        HEq πG (pullback.fst G.hom (spMap f)) ∧ HEq πH (pullback.fst H.hom (spMap f)) ∧
        HEq (P.gen ≫ πG) j ∧
        (∀ a, (P.oG.act a).left ≫ πG = πG ≫ (ιG.act a).left) ∧
        (∀ a, (P.oGt.act a).left ≫ πH = πH ≫ (ρ.act a).left) ∧
        ∀ (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) (x : specO O S ⟶ P.Gt),
          FormalPoint.IsPointOf U (Φ _ (pushPt hπH.1.w x)) (pushPt hπG.1.w (P.cmp S hS x)) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, Φ, J, ⟨d⟩, hΦ, hJ, hnat⟩ := exists_comparison U
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL ιD (Φ := Φ) hΦ
  refine ⟨H, inferInstance, inferInstance, Φ, ρ, ofCompletion hv ε f hf hG ιG d ρ J hnat
      (fun T hT x a => (hJ _ hT _ _).2 (((hJ _ hT x _).1 rfl).smul hL hO a (hρ a _ _))) A' oA' j hj hact,
    ⟨d⟩, hΦ, hρ, rfl, rfl, HEq.rfl, rfl, rfl, rfl, _, _, isGrpPullback_pullback G _, isGrpPullback_pullback H _,
    HEq.rfl, HEq.rfl, heq_of_eq (pullback.lift_fst _ _ _), actPull_fst _ ιG, actPull_fst _ ρ, fun S _ _ hS x => ?_⟩
  exact (hJ _ (isAdicColimit_of_isNilpotent hf S hS) _ _).1
    ((pushEquiv (isGrpPullback_pullback G (spMap f)) _).apply_symm_apply _).symm

end Unif

end GlobalTheory.HTLat
end
end
