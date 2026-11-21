import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.UnifBaseChangeInjOfSeamsCS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

structure IsPullGt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg φ D D') {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) {e : ℕ} (g : GtCoord I D e G)
    (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) : Prop where
  h_fst : h ≫ (fstG I e G).left = (fstG I' e G').left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)
  h_pG : g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left
  h_t : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4,
      D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        h ≫ D.Oφ g.pG (hD.xe x) k,
    LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ
        (g.t (hD.xe x)))

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.PullGtPf

open Semi Geo.Tor

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)

include hφ in
lemma pow_le : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
  intro x hx
  rw [Ideal.mem_comap]
  have h1 : φ x ∈ (I ^ (e + 1)).map φ := Ideal.mem_map_of_mem φ hx
  rw [Ideal.map_pow] at h1
  first
  | exact Ideal.pow_right_mono hφ (e + 1) h1
  | exact pow_le_pow_left' hφ (e + 1) h1

def φe : R ⧸ I ^ (e + 1) →+* R' ⧸ I' ^ (e + 1) := Ideal.quotientMap _ φ (pow_le φ hφ e)

def sE : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (φe φ hφ e))

lemma sE_thick : sE φ hφ e ≫ thick R I e = thick R' I' e ≫ specOf φ := by
  simp only [sE, thick, specOf, ← Spec.map_comp]
  congr 1
  all_goals first | rfl | (ext x; simp [φe])

variable {φ hφ e}

def hMap (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    (thickObj R' I' e Y').left ⟶ (thickObj R I e Y).left :=
  pullback.lift (pullback.fst Y'.hom (thick R' I' e) ≫ b.left ≫ pullback.fst Y.hom (specOf φ))
    (pullback.snd Y'.hom (thick R' I' e) ≫ sE φ hφ e) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc b.left,
        show b.left ≫ pullback.snd Y.hom (specOf φ) = Y'.hom from Over.w b, ← Category.assoc,
        pullback.condition, Category.assoc, Category.assoc, sE_thick])

lemma hMap_fst (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    hMap (hφ := hφ) (e := e) Y Y' b ≫ pullback.fst Y.hom (thick R I e) =
      pullback.fst Y'.hom (thick R' I' e) ≫ b.left ≫ pullback.fst Y.hom (specOf φ) := by
  first
  | exact pullback.lift_fst _ _ _
  | simp [hMap]

lemma hMap_snd (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    hMap (hφ := hφ) (e := e) Y Y' b ≫ pullback.snd Y.hom (thick R I e) =
      pullback.snd Y'.hom (thick R' I' e) ≫ sE φ hφ e := by
  first
  | exact pullback.lift_snd _ _ _
  | simp [hMap]

lemma sE_trans : thickTrans R' I' e ≫ sE φ hφ (e + 1) = sE φ hφ e ≫ thickTrans R I e := by
  simp only [sE, thickTrans, ← Spec.map_comp]
  congr 1
  all_goals first | rfl | (ext x; simp [φe])

lemma hMap_thick (Y : Over (Spec (CommRingCat.of R))) (Y' : Over (Spec (CommRingCat.of R')))
    (b : Y' ⟶ (Over.pullback (specOf φ)).obj Y) :
    thickMap R' I' e Y' ≫ hMap (hφ := hφ) (e := e + 1) Y Y' b =
      hMap (hφ := hφ) (e := e) Y Y' b ≫ thickMap R I e Y := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hMap_fst]
    simp only [thickMap, pullback.map]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    simp only [Category.comp_id, Category.id_comp]
    rw [hMap_fst]
  · rw [Category.assoc, Category.assoc, hMap_snd]
    simp only [thickMap, pullback.map]
    erw [pullback.lift_snd_assoc, pullback.lift_snd]
    simp only [Category.assoc, sE_trans]
    simp only [← Category.assoc]
    rw [hMap_snd]

lemma isGrpPullback_hMap (Y : Over (Spec (CommRingCat.of R))) [GrpObj Y]
    (Y' : Over (Spec (CommRingCat.of R'))) [GrpObj Y']
    (b : Y' ≅ (Over.pullback (specOf φ)).obj Y) [IsMonHom b.hom] :
    IsGrpPullback (thickObj R' I' e Y') (thickObj R I e Y) (sE φ hφ e) (hMap (hφ := hφ) Y Y' b.hom) := by
  have A := isGrpPullback_pullback Y' (thick R' I' e)
  have B := ((isGrpPullback_of_iso b).comp (isGrpPullback_pullback Y (specOf φ))).congr
    (Category.id_comp _) rfl
  have C := A.comp B
  have D := isGrpPullback_pullback Y (thick R I e)
  exact D.cancel (C.congr (sE_thick φ hφ e).symm (by rw [hMap_fst])) (hMap_snd Y Y' b.hom)

section MonHom

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

lemma isMonHom_of_grpPullback {G B : Over S} [GrpObj G] [GrpObj B] {G' B' : Over S'} [GrpObj G']
    [GrpObj B'] {φG : G'.left ⟶ G.left} {φB : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φG)
    (hB : IsGrpPullback B' B f φB) (q : G ⟶ B) [IsMonHom q] (q' : G' ⟶ B')
    (hq : q'.left ≫ φB = φG ≫ q.left) : IsMonHom q' := by
  have mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ q' = (x ≫ q') * (y ≫ q') := by
    intro T x y
    have hx : (pushPt hG.1.w x ≫ q).left = (x ≫ q').left ≫ φB := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hq]; rfl
    have hy : (pushPt hG.1.w y ≫ q).left = (y ≫ q').left ≫ φB := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hq]; rfl
    have e2 := hB.2 T (x ≫ q') (y ≫ q') (pushPt hG.1.w x ≫ q) (pushPt hG.1.w y ≫ q) hx hy
    have e1 := hG.2 T x y (pushPt hG.1.w x) (pushPt hG.1.w y) rfl rfl
    apply Over.OverMorphism.ext
    apply hB.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hq, ← Category.assoc, ← e1, ← Over.comp_left,
        MonObj.mul_comp, e2]
    · rw [Over.w, Over.w]
  refine ⟨?_, ?_⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G') ≫ q' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

end MonHom

section Q

variable (hφ e)
variable {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom]
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom]

abbrev hGm : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left := hMap (hφ := hφ) (e := e) G G' bc.hom

abbrev hBm : (thickObj R' I' e D'.P.A).left ⟶ (thickObj R I e D.P.A).left :=
  hMap (hφ := hφ) (e := e) D.P.A D'.P.A eB.hom

omit [IsCommMonObj G] [IsCommMonObj G'] in
lemma grpG : IsGrpPullback (thickObj R' I' e G') (thickObj R I e G) (sE φ hφ e) (hGm hφ e bc) :=
  isGrpPullback_hMap (hφ := hφ) (e := e) G G' bc

lemma grpB : IsGrpPullback (thickObj R' I' e D'.P.A) (thickObj R I e D.P.A) (sE φ hφ e) (hBm hφ e eB) :=
  isGrpPullback_hMap (hφ := hφ) (e := e) D.P.A D'.P.A eB

variable {e} (g : GtCoord I D e G)

def qL : (thickObj R' I' e G').left ⟶ (thickObj R' I' e D'.P.A).left :=
  (grpB hφ e eB).1.lift (hGm hφ e bc ≫ g.q.left) (thickObj R' I' e G').hom (by
    rw [Category.assoc, Over.w g.q]; exact hMap_snd (hφ := hφ) G G' bc.hom)

def qP : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A :=
  Over.homMk (qL hφ eB bc g) ((grpB hφ e eB).1.lift_snd _ _ _)







end Q

section Torus

variable (hφ e) {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ X)

def ψB : AddMonoidAlgebra ZU.{0} X →ₐc[ZU.{0}] AddMonoidAlgebra ZU.{0} X' :=
  AddMonoidAlgebra.mapDomainBialgHom ZU.{0} xe.symm.toAddMonoidHom

abbrev ψR : AddMonoidAlgebra ZU.{0} X →+* AddMonoidAlgebra ZU.{0} X' := (ψB xe : _ →+* _)

def specψ : splitTorusAff ZU X' ⟶ splitTorusAff ZU X :=
  ((bialgSpec ZU).map (CommBialgCat.ofHom (ψB xe)).op).hom

instance specψ_hom : IsMonHom (specψ xe) :=
  ((bialgSpec ZU).map (CommBialgCat.ofHom (ψB xe)).op).isMonHom_hom

def hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X').left ⟶
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).left :=
  pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (ψR xe))) (pullback.snd _ _ ≫ sE φ hφ e)
    (specULiftZIsTerminal.hom_ext _ _)

lemma ψB_left_inv : (ψR xe).comp (ψR xe.symm) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => rw [map_add, map_add, ha, hc]
  | single a r => simp [ψB, AddMonoidAlgebra.mapDomainBialgHom, AddMonoidAlgebra.mapDomainAlgHom_apply]

lemma ψB_right_inv : (ψR xe.symm).comp (ψR xe) = RingHom.id _ := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => rw [map_add, map_add, ha, hc]
  | single a r => simp [ψB, AddMonoidAlgebra.mapDomainBialgHom, AddMonoidAlgebra.mapDomainAlgHom_apply]

lemma specψ_left : (specψ xe).left = Spec.map (CommRingCat.ofHom (ψR xe)) := rfl

instance : IsIso (specψ xe).left := by
  rw [specψ_left]
  have : IsIso (CommRingCat.ofHom (ψR xe)) :=
    ⟨⟨CommRingCat.ofHom (ψR xe.symm), by
      rw [← CommRingCat.ofHom_comp, ψB_right_inv]; rfl, by
      rw [← CommRingCat.ofHom_comp, ψB_left_inv]; rfl⟩⟩
  exact (inferInstance : IsIso (Scheme.Spec.map (CommRingCat.ofHom (ψR xe)).op))

def eψ : splitTorusAff ZU X' ≅ splitTorusAff ZU X :=
  Over.isoMk (asIso (specψ xe).left) (Over.w (specψ xe))

lemma eψ_hom : (eψ xe).hom = specψ xe := by
  first
  | rfl
  | (ext1; rfl)

instance : IsMonHom (eψ xe).hom := by rw [eψ_hom]; infer_instance

lemma grpT : IsGrpPullback (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X')
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X) (sE φ hφ e) (hT hφ e xe) := by
  have A := isGrpPullback_pullback (splitTorusAff ZU X') (toZ (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))))
  have B := isGrpPullback_of_iso (eψ xe)
  have C := A.comp B
  have D := isGrpPullback_pullback (splitTorusAff ZU X) (toZ (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  exact D.cancel (C.congr (specULiftZIsTerminal.hom_ext _ _) ((pullback.lift_fst _ _ _).trans
    (congrArg (pullback.fst _ _ ≫ ·) (specψ_left xe).symm)).symm) (pullback.lift_snd _ _ _)


lemma appTop_eq_appLE {A B : Scheme.{0}} (f : A ⟶ B) : f.appTop = f.appLE ⊤ ⊤ (TorusInj.tle f) := by
  first
  | exact f.app_eq_appLE
  | (rw [Scheme.Hom.appLE]; simp)
  | simp [Scheme.Hom.appLE]


end Torus

section Unit

lemma toUnit_left' {S : Scheme.{0}} (Z : Over S) : (toUnit Z).left = Z.hom := by
  first
  | rfl
  | (have h := Over.w (toUnit Z); simpa using h)

lemma IsGrpPullback.one_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) :
    η[G'].left ≫ φ = f ≫ η[G].left := by
  have h := hG.2 (𝟙_ _) 1 1 (pushPt hG.1.w 1) (pushPt hG.1.w 1) rfl rfl
  rw [_root_.mul_one] at h
  have h3 : pushPt hG.1.w (1 : 𝟙_ (Over S') ⟶ G') * pushPt hG.1.w 1 = pushPt hG.1.w 1 :=
    Over.OverMorphism.ext h
  have h2 := congrArg Over.Hom.left (mul_eq_left.1 h3)
  simp only [pushPt, Over.homMk_left, Hom.one_def, Over.comp_left, toUnit_left'] at h2
  simpa using h2

end Unit

section IK

variable (hφ) {D : DegPre R} {D' : DegPre R'} (eB : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A)
  [IsMonHom eB.hom] (xe : D'.X ≃+ D.X)
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G) [IsMonHom bc.hom] {e : ℕ} (g : GtCoord I D e G)

def iL : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (thickObj R' I' e G').left :=
  (grpG hφ e bc).1.lift (hT hφ e xe ≫ g.i.left) (splitTorus _ D'.X).hom (by
    rw [Category.assoc, Over.w g.i]; exact pullback.lift_snd _ _ _)

def iP : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G' :=
  Over.homMk (iL hφ xe bc g) ((grpG hφ e bc).1.lift_snd _ _ _)




end IK

end ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
end
end
