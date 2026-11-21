import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace Formalism.L2.Pj.GSR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Corr

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [CommRing k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)

abbrev viaT (X : Over (Spec (CommRingCat.of k))) : Over S' := Over.mk (X.hom ≫ tk)

def Rel {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) : Prop :=
  w.left ≫ F = v.left ≫ pullback.fst G.hom g

def liftT {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) : viaT tk Y ⟶ viaT tk X :=
  Over.homMk φ.left (by
    show φ.left ≫ X.hom ≫ tk = Y.hom ≫ tk
    rw [← Category.assoc, Over.w φ])

variable {tk g}

theorem one_left' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  exact ReciprocityTheory.ChartRestriction.G.Chart.one_left'

include hc in
theorem rel_uniq_w {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  have e : w.left ≫ F = w'.left ≫ F :=
    (h : w.left ≫ F = _).trans (h' : w'.left ≫ F = _).symm
  exact Over.OverMorphism.ext (hc.1.hom_ext e (by rw [Over.w w, Over.w w']))

theorem rel_uniq_v {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  have e : v.left ≫ pullback.fst G.hom g = v'.left ≫ pullback.fst G.hom g :=
    (h : _ = v.left ≫ pullback.fst G.hom g).symm.trans (h' : _ = v'.left ≫ pullback.fst G.hom g)
  refine Over.OverMorphism.ext (pullback.hom_ext e ?_)
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have hv' : v'.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v'
  rw [hv, hv']

include hc hg in
theorem rel_exists_w {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ (Over.pullback g).obj G) :
    ∃ w : viaT tk X ⟶ G', Rel (F := F) tk g w v := by
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := by simpa using Over.w v
  have cond : (v.left ≫ pullback.fst G.hom g) ≫ G.hom = (X.hom ≫ tk) ≫ f := by
    rw [Category.assoc, pullback.condition, reassoc_of% hv, Category.assoc, hg]
  exact ⟨Over.homMk (hc.1.lift _ _ cond) (hc.1.lift_snd _ _ cond), hc.1.lift_fst _ _ cond⟩

include hc hg in
theorem rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  have cond : (w.left ≫ F) ≫ G.hom = X.hom ≫ g := by
    rw [Category.assoc, hc.1.w, reassoc_of% hw, hg]
  exact ⟨Over.homMk (pullback.lift _ _ cond) (pullback.lift_snd _ _ cond), (pullback.lift_fst _ _ cond).symm⟩

def iota2 (hg : tk ≫ f = g) (X : Over (Spec (CommRingCat.of k))) :
    Over.mk (X.hom ≫ g) ⟶ Over.mk ((viaT tk X).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (X.hom ≫ tk) ≫ f = X.hom ≫ g
    rw [Category.id_comp, Category.assoc, hg])

theorem rel_iff {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    ext
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact (h : w.left ≫ F = _).symm
  · intro h
    have e : (pushPt (isGrpPullback_pullback G g).1.w v).left = (iota2 hg X ≫ pushPt hc.1.w w).left := by
      rw [h]
    simp only [pushPt, iota2, Over.comp_left, Over.homMk_left, Category.id_comp] at e
    exact e.symm

include hc hg in
theorem rel_mul {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg] at h h' ⊢
  have e1 := map_mul (pushHom (isGrpPullback_pullback G g) X) v v'
  have e2 := map_mul ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X))) w w'
  exact e1.trans ((congrArg₂ (· * ·) h h').trans e2.symm)

include hc hg in
theorem rel_one {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  rw [Formalism.L2.Pj.GSR.rel_iff hc hg]
  exact (map_one (pushHom (isGrpPullback_pullback G g) X)).trans
    (map_one ((preHom (iota2 hg X)).comp (pushHom hc (viaT tk X)))).symm

include hc hg in
theorem rel_prod : ∀ {N : ℕ} {X : Over (Spec (CommRingCat.of k))} (u : Fin N → (viaT tk X ⟶ G'))
    (u' : Fin N → (X ⟶ (Over.pullback g).obj G)), (∀ i, Rel (F := F) tk g (u i) (u' i)) →
    Rel (F := F) tk g (List.ofFn u).prod (List.ofFn u').prod
  | 0, X, u, u', _ => by simpa using rel_one hc hg (X := X)
  | N + 1, X, u, u', h => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact rel_mul hc hg (h 0) (rel_prod (fun i => u i.succ) (fun i => u' i.succ) fun i => h i.succ)

theorem rel_pre {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) {w : viaT tk X ⟶ G'}
    {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) : Rel (F := F) tk g (liftT tk φ ≫ w) (φ ≫ v) := by
  show (φ.left ≫ w.left) ≫ F = (φ.left ≫ v.left) ≫ pullback.fst G.hom g
  rw [Category.assoc, Category.assoc, (h : w.left ≫ F = _)]

theorem rel_act (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) {X : Over (Spec (CommRingCat.of k))}
    {w : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) :
    Rel (F := F) tk g (w ≫ a) (v ≫ (Over.pullback g).map b) := by
  have h' : w.left ≫ F = v.left ≫ pullback.fst G.hom g := h
  show (w ≫ a).left ≫ F = (v ≫ (Over.pullback g).map b).left ≫ pullback.fst G.hom g
  first
  | (simp [hab, reassoc_of% h']; erw [pullback.lift_fst])
  | exact ReciprocityTheory.ChartRestriction.G.Chart.rel_act (F := F) a b hab (show ReciprocityTheory.ChartRestriction.G.Chart.Rel (F := F) tk g w v from h)

end Corr

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {k : Type} [CommRing k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)

include hc in
theorem rel_eq_iff {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact Formalism.L2.Pj.GSR.rel_uniq_v h₁ h₂
  · rintro rfl
    exact Formalism.L2.Pj.GSR.rel_uniq_w hc h₁ h₂

include hc hg in
theorem tan_iff {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have h1 := rel_pre (spMap (fstD k)) h
  have h2 := rel_one hc hg (X := sp (R₀ := k) k)
  have hid : (sp (R₀ := k) k).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e1 : (1 : viaT tk (sp (R₀ := k) k) ⟶ G').left = (1 : Over.mk tk ⟶ G').left := by
    rw [one_left', one_left']
    show ((sp (R₀ := k) k).hom ≫ tk) ≫ _ = tk ≫ _
    rw [hid, Category.id_comp]
  rw [ReciprocityTheory.ChartRestriction.G.Chart.IsTan, ← rel_eq_iff hc h1 h2]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    exact e.trans e1.symm
  · intro e
    exact (congrArg (fun q => q.left) e).trans e1

include hc in
theorem eig_iff (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by
  rw [← rel_eq_iff hc (rel_act a b hab h) (rel_pre (spMap (scaleD s)) h)]
  constructor
  · intro e
    exact Over.OverMorphism.ext e
  · intro e
    exact congrArg (fun q => q.left) e

end Count

end Formalism.L2.Pj.GSR
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart scaleD)
open Formalism.L2.Pj.GSR (Rel viaT liftT)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

instance gsvActHom (a : 𝓞 E) : IsMonHom (Xo.univ.t.act.act a) := Xo.univ.t.act.hom a

theorem gsv_hcId : IsGrpPullback Xo.univ.t.G Xo.univ.t.G (𝟙 Xo.X) (𝟙 Xo.univ.t.G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : Over.mk (T.hom ≫ 𝟙 Xo.X) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have h1 : x₀ = e ≫ x := by
    apply Over.OverMorphism.ext
    simpa [e] using hx
  have h2 : y₀ = e ≫ y := by
    apply Over.OverMorphism.ext
    simpa [e] using hy
  subst h1 h2
  rw [← comp_mul]
  simp [e]

def gsvVec {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {n : ℕ}
    (xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G)
    (cc : Fin n → L) : Sp (DualNumber L) ⟶ Xo.univ.t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x

section V

variable {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gsvVec_w (cc : Fin n → L) :
    gsvVec x xc cc ≫ Xo.univ.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ x := by
  have h1 := Over.w (tvec (x := xc) cc)
  rw [gsvVec, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) h1

variable (xc) in

def gsvW (cc : Fin n → L) : tEps x ⟶ Xo.univ.t.G := Over.homMk (gsvVec x xc cc) (gsvVec_w cc)

variable (xc) in
theorem gsv_rel (cc : Fin n → L) :
    Rel (F := 𝟙 Xo.univ.t.G.left) x x
      (gsvW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) (tvec (x := xc) cc) := by
  show (gsvW xc cc).left ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

theorem gsv_tan (hx : IsUnivChart _ n xc) (cc : Fin n → L) : IsTanAt x (gsvVec x xc cc) := by
  refine ⟨gsvVec_w cc, ?_⟩
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc = 1 :=
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc
  have hr := Formalism.L2.Pj.GSR.rel_pre
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) (gsv_rel xc cc)
  rw [ht] at hr
  have h1 : Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫
      gsvW xc cc = 1 := by
    first
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hc htk hr (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hc hr (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hr (Formalism.L2.Pj.GSR.rel_one hc htk)
  calc spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ gsvVec x xc cc
      = (Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫
          gsvW xc cc).left := rfl
    _ = (1 : _ ⟶ Xo.univ.t.G).left := congrArg Over.Hom.left h1
    _ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
      let e : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) ⟶ Over.mk x :=
        Over.homMk (𝟙 _) (by simp [ReciprocityTheory.ChartRestriction.G.Chart.sp])
      rw [← comp_one e]
      simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]
      try rfl

theorem gsv_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) :
    ∃ cc, w = gsvVec x xc cc := by
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let W : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G := Over.homMk w hw.1
  obtain ⟨v, hv⟩ : ∃ v, Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x W v := by
    first
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc htk W
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc htk
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc W
    | exact Formalism.L2.Pj.GSR.rel_exists_v W
  have hone : Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫ W = 1 := by
    apply Over.OverMorphism.ext
    let e : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simp [ReciprocityTheory.ChartRestriction.G.Chart.sp])
    rw [← comp_one e]
    simp only [e, W, Formalism.L2.Pj.GSR.liftT, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact hw.2
  have hv1 := Formalism.L2.Pj.GSR.rel_pre (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) hv
  rw [hone] at hv1
  have htan : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ v = 1 := by
    first
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hc htk hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hc hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v htan, ?_⟩
  have hs := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v htan
  have hv' : w ≫ 𝟙 _ = v.left ≫ pullback.fst Xo.univ.t.G.hom x := hv
  rw [Category.comp_id] at hv'
  rw [hv']
  exact congrArg (fun f => f.left ≫ pullback.fst Xo.univ.t.G.hom x) hs

theorem gsv_inj (hx : IsUnivChart _ n xc) {c₁ c₂ : Fin n → L} (h : gsvVec x xc c₁ = gsvVec x xc c₂) : c₁ = c₂ := by
  have ht : tvec (x := xc) c₁ = tvec (x := xc) c₂ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact h
    · exact (Over.w (tvec (x := xc) c₁)).trans (Over.w (tvec (x := xc) c₂)).symm
  first
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj ht
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx ht

theorem gsv_eig_iff [Algebra c.F L] (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) (cc : Fin n → L) :
    IsEigAt c τ (gsvVec x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a)) := by
  have e1 : ∀ a : 𝓞 E, ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    intro a
    simp
    first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  have key : ∀ a : 𝓞 E, (gsvVec x xc cc ≫ (Xo.univ.t.act.act a).left =
      spMap (epsMul (algebraMap c.F L (embK c τ a))) ≫ gsvVec x xc cc) ↔
      (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) =
        ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (algebraMap c.F L (embK c τ a))) ≫ tvec (x := xc) cc) := by
    intro a
    constructor
    · intro h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp only [Over.comp_left, Category.assoc, e1]
        simp only [gsvVec] at h
        rw [← Category.assoc, h]
        rfl
      · exact (Over.w _).trans (Over.w _).symm
    · intro h
      have h' := congrArg (fun f => f.left ≫ pullback.fst Xo.univ.t.G.hom x) h
      simp only [Over.comp_left, Category.assoc, e1] at h'
      simp only [gsvVec, Category.assoc]
      exact h'
  simp only [IsEigAt, key, eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff ..

theorem gsv_tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → L) (e : Fin m → Fin n → L) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    simp only [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil]
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      List.ofFn_succ, List.prod_cons, ih (fun j => a j.succ) (fun j => e j.succ)]

theorem gsv_comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → L) (a : Fin m → L) (cc : Fin n → L) :
    IsCombAt x (fun j => gsvVec x xc (e j)) a (gsvVec x xc cc) ↔ cc = ∑ j, a j • e j := by
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let u0 : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j =>
    Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫ gsvW xc (e j)
  have hrel : ∀ j, Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x (u0 j)
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) :=
    fun j => Formalism.L2.Pj.GSR.rel_pre _ (gsv_rel xc (e j))
  have hprod : Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x (List.ofFn u0).prod
      (tvec (x := xc) (∑ j, a j • e j)) := by
    rw [gsv_tvec_sum hx]
    first
    | exact Formalism.L2.Pj.GSR.rel_prod hc htk u0 _ hrel
    | exact Formalism.L2.Pj.GSR.rel_prod hc u0 _ hrel
    | exact Formalism.L2.Pj.GSR.rel_prod u0 _ hrel
  have hleft : ((List.ofFn u0).prod).left = gsvVec x xc (∑ j, a j • e j) := by
    have h : ((List.ofFn u0).prod).left ≫ 𝟙 _ =
        (tvec (x := xc) (∑ j, a j • e j)).left ≫ pullback.fst Xo.univ.t.G.hom x := hprod
    rw [Category.comp_id] at h
    exact h
  constructor
  · rintro ⟨u, hu, hprodu⟩
    have hue : u = u0 := by
      funext j
      apply Over.OverMorphism.ext
      rw [hu j]
      rfl
    subst hue
    exact gsv_inj hx (hprodu.symm.trans hleft)
  · intro h
    subst h
    exact ⟨u0, fun j => rfl, hleft⟩

end V

end Formalism.L2.Pj
end
end

section
noncomputable section

namespace Formalism.L2.Pj.LocFrM

open TensorProduct

variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

theorem range_projective (e : Module.End O V) (he : IsIdempotentElem e) :
    Module.Projective O (LinearMap.range e) := by
  refine Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show e (e y) = e y
  exact LinearMap.congr_fun he y

theorem range_free (e : Module.End O V) (he : IsIdempotentElem e) : Module.Free O (LinearMap.range e) := by
  haveI := range_projective e he
  haveI : Module.FinitePresentation O (LinearMap.range e) := Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

section Split

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

end Formalism.L2.Pj.LocFrM
end
end

section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

set_option maxHeartbeats 400000 in

theorem locFrGen_of {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwG, -, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).mp hwG
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s0, hs0⟩ := thf_secUp hw hL hL' σ'
  have P' := m1.cart.1
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧ h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨P'.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm),
      P'.lift_fst _ _ _, P'.lift_snd _ _ _⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : t'.G.left ⟶ Gx x, k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F :=
    ⟨(CartesianMonoidalCategory.lift
        (Over.homMk t'.G.hom P'.w.symm : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Over.mk x)
        (Over.homMk m1.cm.F rfl : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Xo.univ.t.G)).left,
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst _ _),
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd _ _)⟩
  have gext : ∀ u v : Gx x ⟶ Gx x, u ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left → u ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left → u = v := by
    intro u v e1 e2
    have e3 : (Over.homMk u rfl : Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G) =
        Over.homMk (U := Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom)) (V := Over.mk x ⊗ Xo.univ.t.G) v (by
          show v ≫ _ = u ≫ _
          rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G), ← Category.assoc,
            ← Category.assoc, e1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · first | exact Over.OverMorphism.ext e1 | exact Over.Hom.ext e1 | (ext; exact e1)
      · first | exact Over.OverMorphism.ext e2 | exact Over.Hom.ext e2 | (ext; exact e2)
    exact congrArg Over.Hom.left e3
  have hhk : h ≫ k = 𝟙 _ := gext _ _ (by rw [Category.assoc, hk1, hS, Category.id_comp])
    (by rw [Category.assoc, hk2, hF, Category.id_comp])
  have hkh : k ≫ h = 𝟙 _ := P'.hom_ext (by rw [Category.assoc, hF, hk2, Category.id_comp])
    (by rw [Category.assoc, hS, hk1, Category.id_comp])
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j z hz =>
    Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp
      (chart_le_pullback_open Xo.univ.t.PP.L k hk2 (fun _ => j) (Set.mem_iInter.mpr fun _ => hz)) PUnit.unit
  have hpre : ∀ (z : t'.G.left) j, z ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) →
      z ∈ m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z j hz => Set.mem_iInter.mp hz PUnit.unit
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s0, fun s'' => ?_⟩
  obtain ⟨σ'', hσ''⟩ := sec_down hw hL hL'
    (fun j => (k.appLE ((PPx x).U (fun _ => j)) (m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j) (hle j)).hom
      (s''.f (fun _ => j))) (by
      intro y j j' hj hj'
      try beta_reduce
      have h1 : k y ∈ (PPx x).U (fun _ => j) := hle j hj
      have h2 : k y ∈ (PPx x).U (fun _ => j') := hle j' hj'
      have hg : gm (𝟙 _ ≫ k) y ((PPx x).U (fun _ => j) ⊓ (PPx x).U (fun _ => j'))
          ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1) (𝟙 _ ≫ k) y
          (fun _ => j) (fun _ => j') h1 h2).trans (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hk2])
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, gs_appLE k _ _ (hle j') (𝟙 _) y hj',
        gs_compat s'' (𝟙 _ ≫ k) y h1 h2, hg])
  obtain ⟨a, ha, hau⟩ := hgen σ''
  refine ⟨a, fun J => ?_, fun b hb => hau b fun i => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, J = fun _ => j := ⟨J 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    apply fn_ext
    intro y hy
    have hyh : h y ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) :=
      chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy
    obtain ⟨i, hi⟩ : ∃ i, h y ∈ t'.PP.L.U i := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL'.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have e1 := gs_appLE k _ _ (hle j) h y (hpre _ _ hyh) (s''.f (fun _ => j))
    rw [hhk] at e1
    have e2 := hσ'' _ h y j i (hpre _ _ hyh) hi
    have e3 := hs0 _ h y (fun _ => j) i hyh hi
    have e4 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs (𝟙 _ ≫ h) y _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _) y hy _
    rw [Category.id_comp] at e4
    have e5 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) (scal x a (fun _ => j)) = cst (𝟙 _ ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y a :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
    rw [gs_mul (𝟙 _) y _ hy, e4, e3, e5, ← e1, e2, ha i, gs_mul h y _ hi, gs_constFn t'.G.hom _ h y hi a,
      hS, Category.id_comp]
    ring
  · apply fn_ext
    intro y' hy'
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y' ∈ Xo.univ.t.PP.L.U j := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have hkm : k y' ∈ (PPx x).U (fun _ => j) := hle j hj
    have hmem : y' ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) := Set.mem_iInter.mpr fun _ => hj
    have f1 := hσ'' _ (𝟙 _) y' j i hj hy'
    have f2 := gs_appLE k _ _ (hle j) (𝟙 _) y' hj (s''.f (fun _ => j))
    have f3 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (scal x b (fun _ => j)) = cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _ ≫ k) y' hkm b
    have f4 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs ((𝟙 _ ≫ k) ≫ h) y' _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _ ≫ k) y' hkm _
    rw [Category.assoc, hkh, Category.comp_id] at f4
    have f5 := hs0 _ (𝟙 _) y' (fun _ => j) i hmem hy'
    have f2b : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (s''.f (fun _ => j)) =
        cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b *
          gs (𝟙 _) y' ((Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j)) (s0.f (fun _ => j)) := by
      rw [hb (fun _ => j), gs_mul (𝟙 _ ≫ k) y' _ hkm, f3, f4]
    rw [f5] at f2b
    have f6 := (f1.symm.trans f2).trans f2b
    rw [Category.id_comp, hk1, mul_left_comm] at f6
    rw [gs_mul (𝟙 _) y' _ hy', gs_constFn t'.G.hom _ (𝟙 _) y' hy' b, Category.id_comp]
    exact (Units.mul_right_inj _).mp f6

end Formalism.L2.Pj
end
end

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

private theorem free_range_idem_lemma {V : Type} [CommRing V] [IsLocalRing V] {n : ℕ}
    (g : Module.End V (Fin n → V)) (hg : IsIdempotentElem g) : Module.Free V (LinearMap.range g) := by
  haveI : Module.Projective V (LinearMap.range g) :=
    Module.Projective.of_split (LinearMap.range g).subtype g.rangeRestrict
      (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
        obtain ⟨y, rfl⟩ := hx
        exact LinearMap.congr_fun hg y))
  exact Module.free_of_flat_of_isLocalRing

theorem finrank_range_idem {V k : Type} [CommRing V] [IsLocalRing V] [Field k] [CharZero k] (f : V →+* k) {n : ℕ}
    (e : Module.End V (Fin n → V)) (e' : Module.End k (Fin n → k)) (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : ∀ c, e' (f ∘ c) = f ∘ e c) : Module.finrank V (LinearMap.range e) = Module.finrank k (LinearMap.range e') := by
  classical

  have hker : LinearMap.ker e = LinearMap.range (1 - e) := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      rw [LinearMap.mem_ker] at hx
      simp [hx]
    · rintro ⟨y, rfl⟩
      have h2 := LinearMap.congr_fun he y
      simp only [Module.End.mul_apply] at h2
      simp [h2]
  haveI := free_range_idem_lemma e he
  haveI : Module.Free V (LinearMap.ker e) := by
    rw [hker]; exact free_range_idem_lemma (1 - e) he.one_sub
  haveI : Module.Finite V (LinearMap.ker e) := by
    rw [hker]; infer_instance
  have hP : LinearMap.IsProj (LinearMap.range e) e :=
    ⟨fun x => LinearMap.mem_range_self e x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun he y⟩
  have hP' : LinearMap.IsProj (LinearMap.range e') e' :=
    ⟨fun x => LinearMap.mem_range_self e' x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun he' y⟩

  have hs : ∀ i : Fin n, (f ∘ Pi.single i (1 : V)) = Pi.single i (1 : k) := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have htr : f (LinearMap.trace V _ e) = LinearMap.trace k _ e' := by
    rw [LinearMap.trace_eq_matrix_trace V (Pi.basisFun V (Fin n)),
      LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n))]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (h (Pi.single i 1)) i
    rw [hs i] at this
    exact this.symm
  have h1 := hP.trace
  have h2 := hP'.trace
  apply Nat.cast_injective (R := k)
  rw [← h2, ← htr, h1, map_natCast]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gsvVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gsvVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gsvVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  unfold gsvVec
  rw [ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Over.comp_left, Category.assoc, Category.assoc]
  congr 1
  all_goals first
    | rfl
    | (simp; done)
    | (simp [Over.pullback]; done)
    | (simp [Over.pullback, pullback.map]; done)
    | (erw [pullback.lift_fst]; done)
    | (erw [pullback.lift_fst]; rfl)

theorem gsv_bc [IsLocalRing L] {L' : Type} [CommRing L'] [Algebra L L'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L') (JetR L' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap L L') ≫ x)).obj Xo.univ.t.G) (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, gsvVec (spMap (algebraMap L L') ≫ x) xc' (algebraMap L L' ∘ cc) =
        spMap (dualMap (algebraMap L L')) ≫ gsvVec x xc cc) ∧
      ∀ (a : 𝓞 E) (cc : Fin n → L),
        tmap hx' ((Over.pullback (spMap (algebraMap L L') ≫ x)).map (Xo.univ.t.act.act a)) (algebraMap L L' ∘ cc) =
          algebraMap L L' ∘ tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := L) (R' := L') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB L L'))
    (isGrpPullback_pullback Xo.univ.t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback Xo.univ.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB L L' ≫ x))
  have hv : ∀ cc : Fin n → L, gsvVec (spMap (algebraMap L L') ≫ x) (fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc) =
      spMap (dualMap (algebraMap L L')) ≫ gsvVec x xc cc := by
    intro cc
    have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left =
        (tvec (x := x₁) (algebraMap L L' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  have hx' := gfp_chart_iso e hx₁
  refine ⟨fun m => x₁ m ≫ e.hom, hx', hv, fun a cc => gsv_inj hx' ?_⟩
  rw [gsvVec_tmap hx', hv, hv, gsvVec_tmap hx, Category.assoc]

def rhoT (hx : IsUnivChart _ n xc) : 𝓞 E →+* Module.End L (Fin n → L) :=
  have add : ∀ a b, tmap hx ((Over.pullback x).map (Xo.univ.t.act.act (a + b))) =
      tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) + tmap hx ((Over.pullback x).map (Xo.univ.t.act.act b)) :=
    fun a b => LinearMap.ext fun cc => ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx,
        ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Xo.univ.t.act.add, Functor.map_mul,
        MonObj.comp_mul])
  { toFun := fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a))
    map_one' := LinearMap.ext fun cc => gsv_inj hx (by rw [gsvVec_tmap, Xo.univ.t.act.one]; exact Category.comp_id _)
    map_mul' := fun a b => LinearMap.ext fun cc => gsv_inj hx (by
      rw [Module.End.mul_apply, gsvVec_tmap, gsvVec_tmap, gsvVec_tmap, mul_comm a b, Xo.univ.t.act.mul, Category.assoc]; rfl)
    map_zero' := by
      have := add 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    map_add' := add }

theorem exists_eig_basis [IsLocalRing L] [Algebra c.F L] (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Nonempty (Module.Basis (Fin (Dw.mult τ)) L
      (eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F L (embK c τ a))) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ Xo.X}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (JetR R (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
      (hx : IsUnivChart _ n xc), IsIdempotentElem (proj (rhoT hx) (embK c) α τ) ∧ LinearMap.range (proj (rhoT hx) (embK c) α τ) =
        eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F R (embK c τ a) :=
    fun {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rhoT hx) (embK c τ) (proj (rhoT hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rhoT hx) (embK c τ) m → proj (rhoT hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rhoT hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨LinearMap.ext fun m => e₂ _ (e₁ m), Submodule.ext fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun ⟨m', h⟩ => h ▸ e₁ m', fun h => ⟨m, e₂ m h⟩⟩
  let k := IsLocalRing.ResidueField L
  letI : Algebra c.F k := ((algebraMap L k).comp (algebraMap c.F L)).toAlgebra
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  obtain ⟨xc', hx', -, htm⟩ := gsv_bc (L' := k) hx
  have hx0' : (spMap (algebraMap L k) ≫ x) ≫ Xo.s = sOf c k := by
    rw [Category.assoc, hx0]
    exact (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp _ _).symm
  have pw : ∀ (j : ℕ) cc, (rhoT hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rhoT hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rhoT hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rhoT hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  have r := finrank_range_idem (algebraMap L k) _ _ (key hx).1 (key hx').1 (pr _)
  have := Formalism.L2.Pj.LocFrM.range_free _ (key hx).1
  rw [(key hx').2] at r
  rw [← (key hx).2]
  exact ⟨Module.finBasisOfFinrankEq L _ (r.trans (gfp_finrank hx0' hx' τ))⟩

theorem exists_frPt_local (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) [IsLocalRing L] [Algebra c.F L] (x : Sp L ⟶ Xo.X)
    (hx0 : x ≫ Xo.s = sOf c L) : ∃ y : FrPt Xo c L, y.x = x := by
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  have B := fun τ => (exists_eig_basis (c := c) hx0 hx τ).some
  obtain ⟨t', ⟨m⟩⟩ := exists_sab x Xo.univ.t
  obtain ⟨β, hβ⟩ := globalSections_rank_one_obj hT Xo.univ m
  obtain ⟨s, hs⟩ := locFrGen_of x m β hβ
  refine ⟨⟨x, hx0, fun τ i => gsvVec x xc (B τ i), fun τ i => gsv_tan hx _, fun τ i => (gsv_eig_iff hx τ _).2 (B τ i).2,
    fun τ w hw he => ?_, s, hs⟩, rfl⟩
  obtain ⟨cc, rfl⟩ := gsv_exists hx w hw
  let v : eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F L (embK c τ a) :=
    ⟨cc, (gsv_eig_iff hx τ _).1 he⟩
  have k : ∀ a, IsCombAt x (fun i => gsvVec x xc (B τ i)) a (gsvVec x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [gsv_comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

end Formalism.L2.Pj
end
end
