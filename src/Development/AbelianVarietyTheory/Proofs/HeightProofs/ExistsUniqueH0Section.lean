import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

namespace GlobalTheory.LieIdImg

open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

theorem genRelR_iff_genThrough {A : Type} [CommRing A] [IsLocalRing A] {B B₀ Y : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Y ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (h : Sp A ⟶ Y) :
    GenRelR w t (LB.pullGen _ _ _ t₀ h) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough w ε t t₀ h := by
  constructor
  · intro H
    refine ⟨H.1, fun Z r z p q hp hq => ?_⟩
    have e := ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ ht₀ h) H
      Z r z p q hp hq
    rwa [gm_pullGen', Category.comp_id] at e
  · rintro ⟨h₁, h₂⟩
    refine (genRelR_iff w t _).2 ⟨h₁, fun j j₀ hj₀ hj => ?_⟩
    have e := h₂ _ (𝟙 _) (cpt A) j₀ j hj₀ hj
    simp only [Category.id_comp] at e
    rw [gm_pullGen', Category.id_comp, e]

theorem dualMap_inl {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (r : R) :
    dualMap f (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (f r) := by
  ext <;> simp [dualMap]

theorem dualMap_eps {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    dualMap f DualNumber.eps = DualNumber.eps := by
  ext <;> simp [dualMap]

theorem eq_dualMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (f r)) (h' : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMap f :=
  (ConstTan.eq_dualMapR f ρ h h').trans (ConstTan.eq_dualMapR f _ (dualMap_inl f) (dualMap_eps f)).symm

theorem lieId_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.LieId W ν v ↔ (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsTanGt ν ∧ LieImg W ν v) := by
  intro E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a χ W ν v
  refine and_congr_right fun _ => ?_
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hloc : ∀ n, IsLocalRing (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) := fun n =>
    have : IsLocalRing (PowerSeries A ⧸ I ^ (n + 1)) :=
      isLocalRing_quotient_pow (ConstLie.span_X_ne_top (A := A)) n
    ConstTan.isLocalRing_dual _
  have hs : ∀ n, spMap (algebraMap (PowerSeries A ⧸ I ^ (n + 1)) (DualNumber (PowerSeries A ⧸ I ^ (n + 1)))) ≫
      Out.thick (PowerSeries A) I n =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ (epsR (PowerSeries A)).hom := fun n =>
    (ConstLie.spMap_comp' _ _).trans ((congrArg spMap
      (RingHom.ext fun r => (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm)).trans
        (ConstLie.spMap_comp' _ _).symm)
  constructor
  · intro h n ρ κ vn h₁ h₂ h₃ h₄ _ h₆ x
    have := hloc n
    obtain ⟨vn', k₁, -, k₃⟩ := h n
    obtain rfl := eq_dualMap _ ρ h₁ h₂
    obtain rfl := eq_dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A))) κ h₃ h₄
    have := thick_mono (PowerSeries A) I n
    have hm : Mono (pullback.fst W.t.G.hom (Out.thick (PowerSeries A) I n)) := inferInstance
    obtain rfl : vn = vn' := hm.right_cancellation _ _ (h₆.trans k₁.symm)
    exact (genRelR_iff_genThrough W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn) (ν.isGen x) _).2 (k₃ x)
  · intro h n
    have := hloc n
    let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
      pullback.lift (spMap (dualMap (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ v.left) (spMap (algebraMap _ _))
        (by rw [Category.assoc, Over.w v, hs])
    have h' := h n _ _ vn (dualMap_inl _) (dualMap_eps _)
      (dualMap_inl ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))) (dualMap_eps _)
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    refine ⟨vn, pullback.lift_fst _ _ _, (Category.assoc _ _ _).symm.trans ((h' 0).1 2), fun x => ?_⟩
    exact (genRelR_iff_genThrough W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt n).t_gen _) vn) (ν.isGen x) _).1 (h' x)

end GlobalTheory.LieIdImg
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_identity_arc_witness_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.LieId W ν v ↔ (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsTanGt ν ∧ LieImg W ν v) := by
  atlas_forward_decl GlobalTheory.LieIdImg.lieId_iff
end

section
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.ThetaAlongCmp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def Comparison₂ {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B}
    (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (w1 : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso G.PP.L (t.PP.L.pull m2.φ)) (σ : LB.Sec G.PP.L),
    RigIso m1 w1 ∧ RigIso m2 w2 ∧ SecRel m1 w1 s σ ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j k, m2.φ (r z) ∈ t.PP.L.U j → r z ∈ G.PP.L.U k →
      gs (r ≫ m2.φ) z _ (θ.f j) = (gw w2 r z j k).val * gs r z _ (σ.f k)

section Comparison₂

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B}
  (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x))

theorem tie_iff : (∃ (w1 : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso G.PP.L (t.PP.L.pull m2.φ))
      (σ' : LB.Sec G.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (t.PP.L.pull m2.φ)),
      RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : G.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = G.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ Comparison₂ m1 m2 θ s := by
  constructor
  · rintro ⟨w1, w2, σ, s1, θ2, r1, r2, i1, i2, p, c⟩
    refine ⟨w1, w2, σ, r1, r2, fun Z r z j k hj hk => ?_, fun Z r z j k hj hk => ?_⟩
    · have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j) ≤ toGx m1 ⁻¹ᵁ (PPx x).U (fun _ => j) :=
        fun q hq => le_toGx m1 j (mem_pull.1 hq)
      refine Eq.trans ?_ ((isoMaps_iff w1 σ s1).1 i1 Z r z j k hj hk)
      rw [c (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => j) le]
      exact (gs_appLE (toGx m1) _ _ le r z (mem_pull.2 hj) _).symm
    · have le : (t.PP.L.pull m2.φ).U (fun _ => j) ≤ m2.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      refine Eq.trans ?_ ((isoMaps_iff w2 σ θ2).1 i2 Z r z j k hj hk)
      rw [p (fun _ => j) le]
      exact (gs_appLE m2.φ _ _ le r z (mem_pull.2 hj) _).symm
  · rintro ⟨w1, w2, σ, r1, r2, a, b⟩
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w1).1 r1.1) Xo.univ.t.PP.isLB G.PP.isLB σ
    refine ⟨w1, w2, σ, s1, thfPull t.PP.L m2.φ θ, r1, r2,
      (isoMaps_iff w1 σ s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk,
      (isoMaps_iff w2 σ _).2 fun Z r z j k hj hk =>
        (gs_appLE m2.φ _ _ _ r z (mem_pull.2 hj) _).trans (b Z r z j k hj hk), fun _ _ => rfl, ?_⟩
    intro g e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    have eg : g = toGx m1 := by
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [e₁, toGx_snd]
      · rw [e₂, toGx_fst]
    subst eg
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart G.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem rigIso_unique (hG : Out.GlobalFnsSt) {w w' : LB.Iso G.PP.L (t.PP.L.pull m2.φ)} (m1 : SABMap G Xo.univ.t x)
    (h : RigIso m2 w) (h' : RigIso m2 w') : w = w' := by
  have hp : IsProper G.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hp, G.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp V) (exists_chart G.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m2.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    G.G.hom (eSec G.G) (Over.w η[G.G]) (hG _ _ hab).2 h.1 h'.1 h.2 h'.2

end Comparison₂

section FirstPower

variable {X : Scheme.{0}} {L : LB X}

theorem gs_h0Sec {σ : Out.H0 L 1} {θ : L.Sec} (h : SectionOfLineBundleOne σ θ) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hp : r z ∈ L.U k) :
    gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (σ.f (fun _ => k)) = gs r z (L.U k) (θ.f k) := by
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) ≤ L.U k := fun y hy => Set.mem_iInter.1 hy 0
  rw [h (fun _ => k) le]
  exact gs_res r z le (Set.mem_iInter.2 fun _ => hp) _

theorem exists_section_of_h0 (σ : Out.H0 L 1) : ∃ θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ k, L.U k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) := fun k y hy =>
    Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun k => resG X (le k) (σ.f (fun _ => k)), fun i j => fn_ext fun y hy => ?_⟩, fun J hJ => ?_⟩
  · have m₁ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := le i hy.1
    have m₂ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := le j hy.2
    have gg := gm_linComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 X) y _ _ m₁ m₂
    rw [Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp] at gg
    refine (gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans ((gs_compat σ (𝟙 X) y m₁ m₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val gg.symm))
        ((gs_res _ y _ hy _).trans (gs_res _ y _ hy.2 _)))))))
  · obtain ⟨k, rfl⟩ : ∃ k, J = fun _ => k := ⟨J 0, funext fun i => congrArg J (Subsingleton.elim i 0)⟩
    refine fn_ext fun y hy => ?_
    have hy' : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) := hy
    exact ((gs_res (𝟙 X) y hJ hy' _).trans (gs_res (𝟙 X) y (le k) (hJ hy') _)).symm

end FirstPower

section Core

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B B₁ B₂ : Scheme.{0}} {t : SAB H B}
  {t₁ : SAB H B₁} {T : SAB H B₂} {f : Sp V ⟶ B} {p : B₁ ⟶ Xo.X} {q : B₁ ⟶ B₂} {χ : B ⟶ B₂} {u : Sp V ⟶ B₁}
  (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (n0 : SABMap t₁ Xo.univ.t p) (n1 : SABMap t₁ T q)
  (n2 : SABMap t T χ) (m : SABMap G t₁ u)

def Thru (w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)) (w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ))
    (w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) (j : T.PP.L.ι) (k : t.PP.L.ι) (k₁ : t₁.PP.L.ι)
    (j₀ : Xo.univ.t.PP.L.ι), n1.φ (m.φ (r z)) ∈ T.PP.L.U j → m2.φ (r z) ∈ t.PP.L.U k →
    m.φ (r z) ∈ t₁.PP.L.U k₁ → m1.φ (r z) ∈ Xo.univ.t.PP.L.U j₀ →
    (gw w₁ (r ≫ m.φ) z j k₁).val * gs (r ≫ toGx m1) z _ (s.f (fun _ => j₀)) =
      (gw w₀ (r ≫ m.φ) z j₀ k₁).val * (gw w₂ (r ≫ m2.φ) z j k).val * gs (r ≫ m2.φ) z _ (θ.f k)

theorem tie_iff_thru (hG : Out.GlobalFnsSt) (hx : x = u ≫ p) (hu : u ≫ q = f ≫ χ) (e₁ : m1.φ = m.φ ≫ n0.φ)
    (e₂ : m.φ ≫ n1.φ = m2.φ ≫ n2.φ)
    {w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)} {w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)}
    {w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)} (r₀ : RigIso n0 w₀) (r₁ : RigIso n1 w₁) (r₂ : RigIso n2 w₂)
    (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Comparison₂ m1 m2 θ s ↔ Thru m1 m2 n0 n1 n2 m w₀ w₁ w₂ θ s := by
  obtain ⟨wm, rm⟩ := exists_rigIso m
  obtain ⟨W2, R2⟩ := exists_rigIso m2
  obtain ⟨W1, R1, T1⟩ := cube_rig_comp n0.cm m.cm m1.cm e₁ (by rw [m1.base, m.base, n0.base, hx]) _ _ _ w₀ wm r₀ rm
  obtain ⟨N, eN, WN, RN, TN⟩ := exists_comp_rig n1 m _ rfl r₁ rm
  obtain ⟨WN', RN', TN'⟩ := cube_rig_comp n2.cm m2.cm N.cm (eN.trans e₂)
    (by rw [N.base, m2.base, n2.base, hu]) _ _ _ w₂ W2 r₂ R2
  obtain rfl : WN = WN' := rigIso_unique N hG m1 RN RN'
  have sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) (j : T.PP.L.ι) (k : t.PP.L.ι) (k₁ : t₁.PP.L.ι)
      (i : G.PP.L.ι), n1.φ (m.φ (r z)) ∈ T.PP.L.U j → m2.φ (r z) ∈ t.PP.L.U k → m.φ (r z) ∈ t₁.PP.L.U k₁ →
      r z ∈ G.PP.L.U i → (gw w₁ (r ≫ m.φ) z j k₁).val * (gw wm r z k₁ i).val =
        (gw w₂ (r ≫ m2.φ) z j k).val * (gw W2 r z k i).val := fun Z r z j k k₁ i hj hk hk₁ hi => by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val ((TN Z r z j k₁ i hj hk₁ hi).symm.trans
      (TN' Z r z j k i ((congrArg (fun g => g (r z) ∈ T.PP.L.U j) eN).mpr hj) hk hi))
  constructor
  · rintro ⟨W1', W2', σ, R1', R2', a, b⟩ Z r z j k k₁ j₀ hj hk hk₁ hj₀
    obtain rfl : W1 = W1' := rigIso_unique m1 hG m1 R1 R1'
    obtain rfl : W2 = W2' := rigIso_unique m2 hG m1 R2 R2'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (r z)
    rw [a Z r z j₀ i hj₀ hi, b Z r z k i hk hi, T1 Z r z j₀ k₁ i hj₀ hk₁ hi, Units.val_mul]
    linear_combination (gw w₀ (r ≫ m.φ) z j₀ k₁).val * gs r z _ (σ.f i) * sq Z r z j k k₁ i hj hk hk₁ hi
  · intro h
    obtain ⟨σ, hσ⟩ := sec_pull_down ((isGen_iff W2).1 R2.1) t.PP.isLB G.PP.isLB θ
    refine ⟨W1, W2, σ, R1, R2, fun Z r z j₀ i hj₀ hi => ?_, hσ⟩
    obtain ⟨j, hj⟩ := exists_chart T.PP.isLB (n1.φ (m.φ (r z)))
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (m2.φ (r z))
    obtain ⟨k₁, hk₁⟩ := exists_chart t₁.PP.isLB (m.φ (r z))
    have e := h Z r z j k k₁ j₀ hj hk hk₁ hj₀
    rw [hσ Z r z k i hk hi] at e
    refine (Units.mul_right_inj (gw w₁ (r ≫ m.φ) z j k₁)).1 (e.trans ?_)
    rw [T1 Z r z j₀ k₁ i hj₀ hk₁ hi, Units.val_mul]
    linear_combination -(gw w₀ (r ≫ m.φ) z j₀ k₁).val * gs r z _ (σ.f i) * sq Z r z j k k₁ i hj hk hk₁ hi

def OnOpens (L : RigLB t.G) (g₁ : Gx x ⟶ t₁.G.left) (g₂ : Gx x ⟶ t.G.left)
    (w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)) (w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ))
    (w₂ : LB.Iso L.L (T.PP.L.pull n2.φ)) (σ : Out.H0 L.L 1) (s : LB.Sec (PPx x)) : Prop :=
  ∀ (j : T.PP.L.ι) (k : L.L.ι) (k₁ : t₁.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι) (U : (Gx x).Opens)
    (h₀ : U ≤ g₁ ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁))
    (h₁ : U ≤ g₁ ⁻¹ᵁ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁))
    (h₂ : U ≤ g₂ ⁻¹ᵁ (LB.div (T.PP.L.pull n2.φ) L.L).U (fun _ => j, k))
    (h₃ : U ≤ g₂ ⁻¹ᵁ LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k))
    (h₄ : U ≤ (PPx x).U (fun _ => j₀)),
    (g₁.appLE _ _ h₁).hom (w₁.s (fun _ => j, k₁)).val * resG _ h₄ (s.f (fun _ => j₀)) =
      (g₁.appLE _ _ h₀).hom (w₀.s (fun _ => j₀, k₁)).val * (g₂.appLE _ _ h₂).hom (w₂.s (fun _ => j, k)).val *
        (g₂.appLE _ _ h₃).hom (σ.f (fun _ => k))

theorem gs_onOpens {g₁ : Gx x ⟶ t₁.G.left} {g₂ : Gx x ⟶ t.G.left}
    {w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)} {w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)}
    {w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)} {σ : Out.H0 t.PP.L 1} {θ : LB.Sec t.PP.L} (hσ : SectionOfLineBundleOne σ θ)
    (s : LB.Sec (PPx x)) (j : T.PP.L.ι) (k : t.PP.L.ι) (k₁ : t₁.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι) (U : (Gx x).Opens)
    (h₀ : U ≤ g₁ ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁))
    (h₁ : U ≤ g₁ ⁻¹ᵁ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁))
    (h₂ : U ≤ g₂ ⁻¹ᵁ (LB.div (T.PP.L.pull n2.φ) t.PP.L).U (fun _ => j, k))
    (h₃ : U ≤ g₂ ⁻¹ᵁ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k))
    (h₄ : U ≤ (PPx x).U (fun _ => j₀)) {Z : Scheme.{0}} (r : Z ⟶ Gx x) (z : Z) (hz : r z ∈ U) :
    gs r z U ((g₁.appLE _ _ h₁).hom (w₁.s (fun _ => j, k₁)).val * resG _ h₄ (s.f (fun _ => j₀))) =
        (gw w₁ (r ≫ g₁) z j k₁).val * gs r z _ (s.f (fun _ => j₀)) ∧
      gs r z U ((g₁.appLE _ _ h₀).hom (w₀.s (fun _ => j₀, k₁)).val *
          (g₂.appLE _ _ h₂).hom (w₂.s (fun _ => j, k)).val * (g₂.appLE _ _ h₃).hom (σ.f (fun _ => k))) =
        (gw w₀ (r ≫ g₁) z j₀ k₁).val * (gw w₂ (r ≫ g₂) z j k).val * gs (r ≫ g₂) z _ (θ.f k) :=
  ⟨(gs_mul r z U hz _ _).trans (congrArg₂ (· * ·)
      ((gs_appLE g₁ _ _ h₁ r z hz _).trans (gs_unit (r ≫ g₁) z _ (h₁ hz) _)) (gs_res r z h₄ hz _)),
    (gs_mul r z U hz _ _).trans (congrArg₂ (· * ·) ((gs_mul r z U hz _ _).trans (congrArg₂ (· * ·)
      ((gs_appLE g₁ _ _ h₀ r z hz _).trans (gs_unit (r ≫ g₁) z _ (h₀ hz) _))
      ((gs_appLE g₂ _ _ h₂ r z hz _).trans (gs_unit (r ≫ g₂) z _ (h₂ hz) _))))
      ((gs_appLE g₂ _ _ h₃ r z hz _).trans (gs_h0Sec hσ (r ≫ g₂) z k (h₂ hz).2)))⟩

theorem onOpens_iff_thru (e₁ : m1.φ = m.φ ≫ n0.φ) (e₂ : m.φ ≫ n1.φ = m2.φ ≫ n2.φ) {h : Gx x ⟶ G.G.left}
    (hφ : h ≫ m1.φ = (snd (Over.mk x) Xo.univ.t.G).left) (hg : toGx m1 ≫ h = 𝟙 _) (hg' : h ≫ toGx m1 = 𝟙 _)
    {w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)} {w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)}
    {w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)} {σ : Out.H0 t.PP.L 1} {θ : LB.Sec t.PP.L} (hσ : SectionOfLineBundleOne σ θ)
    (s : LB.Sec (PPx x)) :
    OnOpens n0 n1 n2 t.PP (h ≫ m.φ) (h ≫ m2.φ) w₀ w₁ w₂ σ s ↔ Thru m1 m2 n0 n1 n2 m w₀ w₁ w₂ θ s := by
  constructor
  · intro a Z r z j k k₁ j₀ hj hk hk₁ hj₀
    have c₁ : (r ≫ toGx m1) ≫ h ≫ m.φ = r ≫ m.φ := by rw [Category.assoc, reassoc_of% hg]
    have c₂ : (r ≫ toGx m1) ≫ h ≫ m2.φ = r ≫ m2.φ := by rw [Category.assoc, reassoc_of% hg]
    have d₁ : (h ≫ m.φ) ((r ≫ toGx m1) z) = m.φ (r z) := congrArg (fun g => g z) c₁
    have d₂ : (h ≫ m2.φ) ((r ≫ toGx m1) z) = m2.φ (r z) := congrArg (fun g => g z) c₂
    let U : (Gx x).Opens :=
      ((h ≫ m.φ) ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁) ⊓
        (h ≫ m.φ) ⁻¹ᵁ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁)) ⊓
      (((h ≫ m2.φ) ⁻¹ᵁ (LB.div (T.PP.L.pull n2.φ) t.PP.L).U (fun _ => j, k) ⊓
        (h ≫ m2.φ) ⁻¹ᵁ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) ⊓ (PPx x).U (fun _ => j₀))
    have p₀ : m.φ (r z) ∈ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁) :=
      ⟨mem_pull.2 ((congrArg (fun g => g (r z) ∈ Xo.univ.t.PP.L.U j₀) e₁).mp hj₀), hk₁⟩
    have p₁ : m.φ (r z) ∈ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁) := ⟨mem_pull.2 hj, hk₁⟩
    have p₂ : m2.φ (r z) ∈ (LB.div (T.PP.L.pull n2.φ) t.PP.L).U (fun _ => j, k) :=
      ⟨mem_pull.2 ((congrArg (fun g => g (r z) ∈ T.PP.L.U j) e₂).mp hj), hk⟩
    have p₃ : m2.φ (r z) ∈ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k) :=
      Set.mem_iInter.2 fun _ => hk
    rw [← d₁] at p₀ p₁
    rw [← d₂] at p₂ p₃
    have hz : (r ≫ toGx m1) z ∈ U := ⟨⟨p₀, p₁⟩, ⟨p₂, p₃⟩, le_toGx m1 j₀ hj₀⟩
    have h₀ : U ≤ _ := inf_le_left.trans inf_le_left
    have h₁ : U ≤ _ := inf_le_left.trans inf_le_right
    have h₂ : U ≤ _ := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have h₃ : U ≤ _ := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have h₄ : U ≤ _ := inf_le_right.trans inf_le_right
    obtain ⟨b₁, b₂⟩ := gs_onOpens n0 n1 n2 (w₀ := w₀) (w₁ := w₁) (w₂ := w₂) hσ s j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄ _ z hz
    rw [c₁] at b₁
    rw [c₁, c₂] at b₂
    exact b₁.symm.trans ((congrArg (gs _ z U) (a j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄)).trans b₂)
  · intro a j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄
    refine fn_ext fun y hy => ?_
    obtain ⟨b₁, b₂⟩ := gs_onOpens n0 n1 n2 (w₀ := w₀) (w₁ := w₁) (w₂ := w₂) hσ s j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄
      (𝟙 _) y hy
    have e := a _ h y j k k₁ j₀ (mem_pull.1 (h₁ hy).1) (h₂ hy).2 (h₁ hy).2
      ((congrArg (fun g => g y ∈ Xo.univ.t.PP.L.U j₀) hφ).mpr (Set.mem_iInter.1 (h₄ hy) 0))
    rw [hg'] at e
    rw [Category.id_comp] at b₁
    rw [Category.id_comp, Category.id_comp] at b₂
    exact b₁.trans (e.trans b₂.symm)

theorem tie_iff_onOpens (hG : Out.GlobalFnsSt) (hx : x = u ≫ p) (hu : u ≫ q = f ≫ χ) (e₁ : m1.φ = m.φ ≫ n0.φ)
    (e₂ : m.φ ≫ n1.φ = m2.φ ≫ n2.φ) (L : RigLB t.G) (hL : L = t.PP) (Q : Out.H0 L.L 1 → Prop)
    (s : LB.Sec (PPx x)) :
    (∃ θ : LB.Sec t.PP.L, (∃ (σ : Out.H0 L.L 1) (θ' : LB.Sec L.L), Q σ ∧ SectionOfLineBundleOne σ θ' ∧ HEq θ θ') ∧ Comparison₂ m1 m2 θ s) ↔
      ∃ (σ : Out.H0 L.L 1) (g₁ : Gx x ⟶ t₁.G.left) (g₂ : Gx x ⟶ t.G.left) (w₂ : LB.Iso L.L (T.PP.L.pull n2.φ))
        (w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)) (w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)),
        Q σ ∧ g₁ ≫ n0.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
        g₁ ≫ t₁.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ u ∧
        g₂ ≫ n2.φ = g₁ ≫ n1.φ ∧ g₂ ≫ t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ f ∧
        IsRigIso n2.cm L T.PP w₂ ∧ IsRigIso n1.cm t₁.PP T.PP w₁ ∧ IsRigIso n0.cm t₁.PP Xo.univ.t.PP w₀ ∧
        OnOpens n0 n1 n2 L g₁ g₂ w₀ w₁ w₂ σ s := by
  subst hL
  obtain ⟨h, hφ, hh, hg, hg'⟩ := exists_inv m1
  have a₁ : (h ≫ m.φ) ≫ n0.φ = (snd (Over.mk x) Xo.univ.t.G).left := by rw [Category.assoc, ← e₁, hφ]
  have a₂ : (h ≫ m.φ) ≫ t₁.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ u := by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, hh]
  have a₃ : (h ≫ m2.φ) ≫ n2.φ = (h ≫ m.φ) ≫ n1.φ := by rw [Category.assoc, Category.assoc, e₂]
  have a₄ : (h ≫ m2.φ) ≫ t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ f := by
    rw [Category.assoc, m2.cart.1.w, ← Category.assoc, hh]
  constructor
  · rintro ⟨θ, ⟨σ, θ', hQ, hσ, he⟩, hT⟩
    cases he
    obtain ⟨w₀, r₀⟩ := exists_rigIso n0
    obtain ⟨w₁, r₁⟩ := exists_rigIso n1
    obtain ⟨w₂, r₂⟩ := exists_rigIso n2
    exact ⟨σ, h ≫ m.φ, h ≫ m2.φ, w₂, w₁, w₀, hQ, a₁, a₂, a₃, a₄, r₂, r₁, r₀,
      (onOpens_iff_thru m1 m2 n0 n1 n2 m e₁ e₂ hφ hg hg' hσ s).2
        ((tie_iff_thru m1 m2 n0 n1 n2 m hG hx hu e₁ e₂ r₀ r₁ r₂ θ s).1 hT)⟩
  · rintro ⟨σ, g₁, g₂, w₂, w₁, w₀, hQ, b₁, b₂, b₃, b₄, r₂, r₁, r₀, hO⟩
    obtain rfl : g₁ = h ≫ m.φ := n0.cart.1.hom_ext (b₁.trans a₁.symm) (b₂.trans a₂.symm)
    obtain rfl : g₂ = h ≫ m2.φ := n2.cart.1.hom_ext (b₃.trans a₃.symm) (b₄.trans a₄.symm)
    obtain ⟨θ, hσ⟩ := exists_section_of_h0 σ
    exact ⟨θ, ⟨σ, θ, hQ, hσ, HEq.rfl⟩, (tie_iff_thru m1 m2 n0 n1 n2 m hG hx hu e₁ e₂ r₀ r₁ r₂ θ s).2
      ((onOpens_iff_thru m1 m2 n0 n1 n2 m e₁ e₂ hφ hg hg' hσ s).1 hO)⟩

end Core

end GlobalTheory.ArcQ.ThetaAlongCmp

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

theorem thetaClause_iff_thetaAlong : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (S : Type) [CommRing S] (ι : PowerSeries A →+* S) (x : Sp S ⟶ Xo.X) (z : Sp S ⟶ Xo.XF c) (t' : SAB H (Sp S)) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' W.t (spMap ι)) (φ : t'.G.left ⟶ Y.oF.t.G.left) (s : LB.Sec (PPx x)), z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ = x → φ ≫ Y.oF.t.G.hom = t'.G.hom ≫ z → φ ≫ Y.m0.toSABMap.φ = m1.φ → φ ≫ Y.m.φ = m2.φ ≫ W.m.φ → ((∃ (θ : LB.Sec W.t.PP.L) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)), ThetaOf W th θ ∧ RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.ThetaAlong W ι z th s) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ b a χ W th S _ ι x z t' m1 m2 φ s hj hx φb φ1 φ2
  subst hx
  obtain ⟨m, e₁⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ z Y.m0.toSABMap m1
  obtain rfl : φ = m.φ := Y.m0.toSABMap.cart.1.hom_ext (φ1.trans e₁) (φb.trans m.cart.1.w.symm)
  refine Iff.trans ?_ (ThetaAlongCmp.tie_iff_onOpens m1 m2 Y.m0.toSABMap Y.m W.m m hG rfl hj e₁ φ2 W.P.U.LG
    W.P.bundle (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.ThetaId W th) s)
  refine exists_congr fun θ => ?_
  rw [← ThetaAlongCmp.tie_iff]
  constructor
  · rintro ⟨w1, w2, σ', s1, θ2, ⟨σ, fam, θ', h1, h2, h3, h4⟩, hT⟩
    exact ⟨⟨σ, θ', ⟨fam, h1, h2⟩, h3, h4⟩, w1, w2, σ', s1, θ2, hT⟩
  · rintro ⟨⟨σ, θ', ⟨fam, h1, h2⟩, h3, h4⟩, w1, w2, σ', s1, θ2, hT⟩
    exact ⟨w1, w2, σ', s1, θ2, ⟨σ, fam, θ', h1, h2, h3, h4⟩, hT⟩

end GlobalTheory.ArcQ
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_theta_pullback : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (S : Type) [CommRing S] (ι : PowerSeries A →+* S) (x : Sp S ⟶ Xo.X) (z : Sp S ⟶ Xo.XF c) (t' : SAB H (Sp S)) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' W.t (spMap ι)) (φ : t'.G.left ⟶ Y.oF.t.G.left) (s : LB.Sec (PPx x)), z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ = x → φ ≫ Y.oF.t.G.hom = t'.G.hom ≫ z → φ ≫ Y.m0.toSABMap.φ = m1.φ → φ ≫ Y.m.φ = m2.φ ≫ W.m.φ → ((∃ (θ : LB.Sec W.t.PP.L) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)), ThetaOf W th θ ∧ RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.ThetaAlong W ι z th s) := by
  atlas_forward_decl GlobalTheory.ArcQ.thetaClause_iff_thetaAlong
end

section
section
noncomputable section

namespace GlobalTheory.QkPullDirect

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
open scoped CategoryTheory.Obj

section Charts

variable {X X' Y Y' Y'' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_of_corr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen)
    (ht' : t'.IsGen) (H : LB.Gen.Corr L φ' ε (fun k => h ≫ φ k) ε t' (LB.pullGen L φ ε t h)) {Z : Scheme.{0}}
    (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (hp : ∀ k, φ' k (r z) ∈ L.U (p k)) :
    gm r z (LB.wchart L φ' p) (t'.s p) = gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  have e := (val_corr hJ H r).trans (val_pull hJ t h r)
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])] at e
  have m₀ := hJ.mem (fun k => h ≫ φ k) r
  have m₁ : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 hp
  have a := gen_trans ht' r z m₁ m₀
  have b := gen_trans ht (r ≫ h) z (j := p) (j' := fun k => J (r ≫ h ≫ φ k)) (Set.mem_iInter.2 hp)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 m₀ k)
  refine a.trans (Eq.trans (congrArg₂ (· * ·) ?_ e) b.symm)
  simp only [trF, Category.assoc]

theorem genThrough_iff (hL : L.IsLB) (w : LB.Iso L' (L.pull F)) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ψ : K → (Y' ⟶ X')} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen)
    (ht' : t'.IsGen) (H : LB.Gen.Corr L φ' ε (fun k => h ≫ φ k) ε t' (LB.pullGen L φ ε t h))
    (a : LB.Gen (LB.LinComb L' ψ ε)) : GenThrough w ε a t' (𝟙 Y') ↔ GenThrough w ε a t h := by
  unfold GenThrough
  refine (and_congr_left' (forall_congr' fun k => by rw [Category.id_comp, hφ])).trans (and_congr_right fun hc => ?_)
  refine forall₅_congr fun Z r z p q => forall_congr' fun hp => forall_congr' fun _ => ?_
  rw [Category.comp_id, gm_of_corr hL hφ ht ht' H r z p fun k => ?_]
  have e : φ' k (r z) = F (ψ k (r z)) := congrArg (fun g => g (r z)) ((hφ k).trans (hc k).symm)
  rw [e]
  exact hp k

end Charts

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem isPullGtF_iff_genThrough (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (g : GtPtF D F) (g' : GtPtF D' F) :
    IsPullGtF φ hD F g g' ↔ g'.b.left ≫ prOf hD = g.b.left ∧
      ∀ x, GenThrough hD.w DegPre.gtε (g'.s x) (g.s (hD.xe x)) (𝟙 _) :=
  and_congr Iff.rfl (forall_congr' fun x =>
    ⟨fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff hD.w _ _ _ (g'.s x) (g.s (hD.xe x)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩,
      fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff hD.w _ _ _ (g'.s x) (g.s (hD.xe x)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩⟩)

theorem gtφ_of_qkExt {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F']
    {f : F →+* F'} (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p : QkPt D F k} {q : QkPt D F' k} (h : QkExt f p q) (χ : D.X) (i : Fin 4) :
    D.gtφ F' q.g.b χ i = spMap f ≫ D.gtφ F p.g.b χ i := by
  have b : q.g.b = extMap f hf ≫ p.g.b := Over.OverMorphism.ext h.2.1
  have a₁ : (cP D _ χ * q.g.b).left = spMap f ≫ (cP D _ χ * p.g.b).left := by
    rw [b, ← comp_cP D (extMap f hf), ← MonObj.comp_mul]; rfl
  have a₂ : (cP D (TF (R := R) F') χ).left = spMap f ≫ (cP D (TF (R := R) F) χ).left := by
    rw [← comp_cP D (extMap f hf)]; rfl
  have a₃ : (1 : TF (R := R) F' ⟶ D.P.A).left = spMap f ≫ (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← MonObj.comp_one (extMap f hf)]; rfl
  fin_cases i
  exacts [a₁, a₂, h.2.1, a₃]

theorem direct_iff (hD : IsPullDeg φ D D') [Algebra (FractionRing R) (FractionRing R')] {k : ℕ}
    {p : QkPt D (FractionRing R) k} {q₀ : QkPt D (FractionRing R') k}
    (h : QkExt (algebraMap (FractionRing R) (FractionRing R')) p q₀) (q : QkPt D' (FractionRing R') k) :
    (q.y = hD.xe.symm q₀.y ∧ IsPullGtF φ hD (FractionRing R') q₀.g q.g) ↔ (hD.xe q.y = p.y ∧
      q.g.b.left ≫ prOf hD = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ p.g.b.left ∧
      ∀ x, GenThrough hD.w DegPre.gtε (q.g.s x) (p.g.s (hD.xe x))
        (spMap (algebraMap (FractionRing R) (FractionRing R')))) := by
  rw [isPullGtF_iff_genThrough, hD.xe.eq_symm_apply, h.1, h.2.1]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun x =>
    genThrough_iff D.P.isLB hD.w (gtφ_of_qkExt (RingHom.comp_id _) h _) (p.g.isGen _) (q₀.g.isGen _) (h.2.2 _) _))

theorem isPullQk_iff (A A' : Type) [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] (g : A →+* A')
    (D₀ : Out.DegPre A) (D₁ : Out.DegPre A') (pd : Out.IsPullDeg g D₀ D₁) (hB : D₀.TauBimult) (k : ℕ)
    (p : Out.QkPt D₀ (FractionRing A) k) (q : Out.QkPt D₁ (FractionRing A') k) :
    GlobalTheory.ArcPull.IsPullQk pd p q ↔ ∃ hg : Function.Injective g, pd.xe q.y = p.y ∧
      q.g.b.left ≫ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.prOf pd = spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg) ≫ p.g.b.left ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x))
        (spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg)) := by
  constructor
  · rintro ⟨_, hK, q₀, e₀, h⟩
    have hg : Function.Injective g := fun a b e => IsFractionRing.injective A (FractionRing A)
      ((algebraMap (FractionRing A) (FractionRing A')).injective (by rw [hK, hK, e]))
    have hf : GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg = algebraMap (FractionRing A) (FractionRing A') :=
      IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun r =>
        (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap hg r).trans (hK r).symm)
    refine ⟨hg, ?_⟩
    rw [hf]
    exact (direct_iff pd e₀ q).1 h
  · rintro ⟨hg, h⟩
    letI : Algebra (FractionRing A) (FractionRing A') := (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg).toAlgebra
    obtain ⟨q₀, e₀, -⟩ := existsUnique_qkExt (F' := FractionRing A') hB
      (algebraMap (FractionRing A) (FractionRing A')) (RingHom.comp_id _) p
    exact ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap_algebraMap hg, q₀, e₀, (direct_iff pd e₀ q).2 h⟩

end GlobalTheory.QkPullDirect
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullQk_iff_fraction_map : ∀ (A A' : Type) [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] (g : A →+* A') (D₀ : Out.DegPre A) (D₁ : Out.DegPre A') (pd : Out.IsPullDeg g D₀ D₁), D₀.TauBimult → ∀ (k : ℕ) (p : Out.QkPt D₀ (FractionRing A) k) (q : Out.QkPt D₁ (FractionRing A') k), GlobalTheory.ArcPull.IsPullQk pd p q ↔ ∃ hg : Function.Injective g, pd.xe q.y = p.y ∧ q.g.b.left ≫ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.prOf pd = spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg) ≫ p.g.b.left ∧ ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x)) (spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg)) := by
  atlas_forward_decl GlobalTheory.QkPullDirect.isPullQk_iff
end

section
section
noncomputable section

namespace GlobalTheory.ConstEig

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

section Transport

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLie

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : DegPre R} {D₀ : DegPre R₀}
  {φ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {e : D₀.X → D.X}

theorem tr_comp {T : Over (Sp R)} {T₀ T₁ : Over (Sp R₀)} {h : T.left ⟶ T₁.left} {g : GtPt D T} {g₀ : GtPt D₀ T₀}
    {g₁ : GtPt D₀ T₁} (H : Tr w e h g g₁) (ρ : T₁ ⟶ T₀) (P : GtPt.IsPull ρ.left g₀ g₁) :
    Tr w e (h ≫ ρ.left) g g₀ := fun x => by
  have hb : ρ ≫ g₀.b = g₁.b := (Over.OverMorphism.ext P.1).symm
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [(H x).1, Category.assoc, ConstTanRed.comp_gtφT D₀ ρ g₀.b g₁.b hb]
  · refine Eq.trans ?_ ((H x).2 Z r z J J' hJ hJ')
    rw [← Category.assoc]
    exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (P.2 x) (r ≫ h)).symm

end Transport

section ThetaShiftProofs

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLie GlobalTheory.FormalPoint
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A]
  [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)

abbrev scaleE {R : Type} [CommRing R] (r : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR r)) (LieCombBaseChange.epsScale_over _)

theorem scaleE_cstE {A : Type} [CommRing A] (r : A) :
    (scaleE (PowerSeries.C (R := A) r)).left ≫ cstE A = cstE A ≫ (scaleE r).left := by
  refine (spMap_comp' _ _).trans (Eq.trans (congrArg spMap ?_) (spMap_comp' _ _).symm)
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable (hG : GlobalFnsSt)
include hG

theorem lieImg_scale {ν ν' : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (r : A)
    (P : GtPt.IsPull (scaleE r).left ν ν') : LieImg W ν' (scaleE (PowerSeries.C (R := A) r) ≫ v) := by
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have Q := Tr.cancel W.spec.1 W.e.surjective hg (tr_comp hg' (scaleE r) P) (scaleE (PowerSeries.C (R := A) r))
    (scaleE_cstE r)
  exact lieImg_of_tr W hg' (hp.pull _ Q)

theorem lieImg_act {ν ν' : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (x : 𝓞 E)
    (hν' : letI := H.starRing; IsSmulPt a.oa x ν ν') : LieImg W ν' (v ≫ W.t.act.act x) := by
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have s := Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' hν'
  exact lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)

end ThetaShiftProofs

theorem isEigGt_iff : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), LieImg W ν v → ((letI := H.starRing; GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsEigGt a.oa t ν) ↔ ∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ v.left) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W t ν v hv
  letI := H.starRing
  refine forall_congr' fun x => ⟨fun ⟨ν', h₁, h₂⟩ => ?_, fun h => ?_⟩
  · have e := (ConstLie.main hG E H Dw l Xo c O β Y A b a χ W ν').1.unique (lieImg_act W hG hv x h₂)
      (lieImg_scale W hG hv (t x) h₁)
    exact congrArg (fun q => q.left) e
  · obtain ⟨ν', h₂⟩ := TorusModel.exists_isSmulPt hG a.oa x ν
    obtain ⟨ν'', h₁⟩ := ConstLie.exists_isPull (scaleE (t x)) ν
    obtain rfl : ν' = ν'' := ConstLie.eq_of_red W hG (lieImg_act W hG hv x h₂) (lieImg_scale W hG hv (t x) h₁)
      (congrArg (ConstLie.redE A ≫ ·) h)
    exact ⟨ν', h₁, h₂⟩

end GlobalTheory.ConstEig
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_tangent_point : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), LieImg W ν v → ((letI := H.starRing; GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsEigGt a.oa t ν) ↔ ∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ v.left) := by
  atlas_forward_decl GlobalTheory.ConstEig.isEigGt_iff
end

section
section
noncomputable section

namespace GlobalTheory.ConstEig

open Matrix

theorem eig_toPowerSeries {A : Type} [CommRing A] {I : Type} {g m : ℕ}
    (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (h : ∀ z : Fin g → A, (∀ i, z ᵥ* M i = ρ i • z) → ∃! cf : Fin m → A, z = ∑ k, cf k • U k)
    (w : Fin g → PowerSeries A)
    (hw : ∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) :
    ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j) := by
  have key : ∀ cf : Fin m → PowerSeries A, (w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j)) ↔
      ∀ n, (fun j => PowerSeries.coeff n (w j)) = ∑ k, PowerSeries.coeff n (cf k) • U k := fun cf => by
    simp only [funext_iff, PowerSeries.ext_iff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
      PowerSeries.coeff_mul_C]
    exact forall_comm
  choose c hc hu using fun n => h (fun j => PowerSeries.coeff n (w j)) fun i => by
    funext j
    have := congrArg (PowerSeries.coeff n) (congrFun (hw i) j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine ⟨fun k => PowerSeries.mk fun n => c n k, (key _).2 fun n => ?_, fun cf hcf => ?_⟩
  · simpa only [PowerSeries.coeff_mk] using hc n
  · funext k
    ext n
    rw [PowerSeries.coeff_mk, ← hu n _ ((key _).1 hcf n)]

end GlobalTheory.ConstEig

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

open Matrix GlobalTheory.BasisUniv GlobalTheory.ConstLie in

theorem GlobalTheory.ConstEig.basis_iff_const : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (m : ℕ) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (eig : (epsR (PowerSeries A) ⟶ W.t.G) → Prop), (∀ w, eig w ↔ ∀ x : 𝓞 E, (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ w.left) → (∀ k, LieImg W (e k) (v k)) → (∀ k, IsTangent (v k) ∧ eig (v k)) → ((∀ w, IsTangent w → eig w → ∃! cf : Fin m → PowerSeries A, IsLieComb cf v w) ↔ ∀ ν w, LieImg W ν w → IsTangent w → eig w → ∃! cf : Fin m → A, GtComb cf e ν) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W t m e v eig heig hev hv
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W
  have lin := GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W

  have back : ∀ {n : ℕ} {e₀ : Fin n → Out.GtPt a.D₀ (epsR A)} {v₀ : Fin n → (epsR (PowerSeries A) ⟶ W.t.G)},
      (∀ k, LieImg W (e₀ k) (v₀ k)) → ∀ {ν w} {cf : Fin n → PowerSeries A}, LieImg W ν w → IsLieComb cf v₀ w →
      GtComb (fun i => PowerSeries.constantCoeff (cf i)) e₀ ν := fun {n e₀ v₀} h₀ ν w cf hw hc => by
    obtain ⟨ν', hν'⟩ := exists_gtComb (fun i => PowerSeries.constantCoeff (cf i)) e₀
    obtain ⟨t', ht', -⟩ := (ex ν').1
    obtain rfl : ν = ν' := eq_of_red W hG hw ht'
      (red_eq_of_comb _ hc ((lin n _ e₀ ν' v₀ t' h₀ hν').1 ht') (fun i => by simp) fun _ => rfl)
    exact hν'
  constructor
  · intro h ν w hw ht he
    obtain ⟨cf, hc, hu⟩ := h w ht he
    refine ⟨_, back hev hw hc, fun cf' h' => funext fun i => ?_⟩
    rw [← hu _ ((lin m _ e ν v w hev h').1 hw)]
    simp
  · intro h w ht he
    obtain ⟨g, e₁, v₁, M, hev₁, hv₁, hcomb, hM⟩ := exists_const_basis hG E H Dw l Xo c O β Y A b a χ W
    have hsm : Smooth W.t.G.hom := W.t.semi.smooth
    have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
    obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
    have hU : ∀ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v₁ (v k) := fun k => by
      obtain ⟨U, hU, -⟩ := hcomb _ (((ex (e k)).2 _ (hev k)).2 (hv k).1)
      exact ⟨U, (lin g U e₁ (e k) v₁ _ (fun i => (hev₁ i).2) hU).1 (hev k)⟩
    choose U hU using hU
    have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v₁ (v₁ i ≫ W.t.act.act x) := hM
    obtain ⟨z, hz, -⟩ := hv₁.2 w ht
    simp only [comb_iff hy hv₁ hU hz]
    refine GlobalTheory.ConstEig.eig_toPowerSeries M (fun x => t x) U (fun s hs => ?_) z
      (fun x => (eig_iff hy hv₁ _ (hMR x) hz _).1 ((heig w).1 he x))
    obtain ⟨ν, hν⟩ := exists_gtComb s e₁
    obtain ⟨w', hw', -⟩ := (ex ν).1
    have hc := (lin g s e₁ ν v₁ w' (fun i => (hev₁ i).2) hν).1 hw'
    have key : ∀ cf : Fin m → A, GtComb cf e ν ↔ s = ∑ k, cf k • U k := fun cf => by
      have e₂ : IsLieComb (fun k => PowerSeries.C (R := A) (cf k)) v w' ↔ s = ∑ k, cf k • U k := by
        rw [comb_iff hy hv₁ hU hc]
        constructor
        · intro q
          funext j
          have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun q j)
          simpa [Finset.sum_apply] using this
        · intro q
          funext j
          have := congrArg (PowerSeries.C (R := A)) (congrFun q j)
          simpa [Finset.sum_apply] using this
      rw [← e₂]
      exact ⟨fun q => (lin m cf e ν v w' hev q).1 hw', fun q => by simpa using back hev hw' q⟩
    have := h ν w' hw' (isTangent_of_comb hy hv₁.1 hc) ((heig w').2 fun x =>
      (eig_iff hy hv₁ _ (hMR x) hc _).2 (by
        funext j
        have := congrArg (PowerSeries.C (R := A)) (congrFun (hs x) j)
        simpa [Matrix.vecMul, dotProduct] using this))
    simpa only [key] using this
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_tangent_family : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (m : ℕ) (e : Fin m → Out.GtPt a.D₀ (epsR A)) (v : Fin m → (epsR (PowerSeries A) ⟶ W.t.G)) (eig : (epsR (PowerSeries A) ⟶ W.t.G) → Prop), (∀ w, eig w ↔ ∀ x : 𝓞 E, (w ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ w.left) → (∀ k, LieImg W (e k) (v k)) → (∀ k, IsTangent (v k) ∧ eig (v k)) → ((∀ w, IsTangent w → eig w → ∃! cf : Fin m → PowerSeries A, IsLieComb cf v w) ↔ ∀ ν w, LieImg W ν w → IsTangent w → eig w → ∃! cf : Fin m → A, GtComb cf e ν) := by
  atlas_forward_decl GlobalTheory.ConstEig.basis_iff_const
end

section
noncomputable section

namespace GlobalTheory.ArcCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints hiding Wit WitBC
open GlobalTheory.ConstTan GlobalTheory.FormalPoint ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj MonObj

section Gt

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem tan_iff (ν : Out.GtPt D₀ (epsR A)) : GtTanR ν ↔ IsTanGt ν := by
  have sec : spMap (TrivSqZeroExt.fstHom A A A).toRingHom ≫ (epsR A).hom = 𝟙 (Sp A) :=
    (ConstLie.spMap_comp' _ _).trans (Spec.map_id _)
  let p₀ : Over.mk (𝟙 (Sp A)) ⟶ epsR A := Over.homMk _ sec
  obtain ⟨g₀, h₀⟩ := ConstLie.exists_isPullGt p₀ ν
  have e₁ : GtTanR ν ↔ ConstLie.ZeroAlong ν p₀ :=
    ⟨fun ⟨_, hz, hp⟩ => (ConstLie.isZero_iff_zeroAlong (ρ := p₀) hp).1 hz,
      fun hz => ⟨g₀, (ConstLie.isZero_iff_zeroAlong h₀).2 hz, h₀⟩⟩
  have o : (1 : Over.mk (𝟙 (Sp A)) ⟶ D₀.P.A).left = η[D₀.P.A].left := Category.id_comp _
  refine e₁.trans (and_congr ⟨fun h => (congrArg (fun q : Over.mk (𝟙 (Sp A)) ⟶ D₀.P.A => q.left) h).trans o,
    fun h => Over.OverMorphism.ext (h.trans o.symm)⟩ (forall_congr' fun x => ⟨fun H => ?_, fun H Z r z J hJ => ?_⟩))
  · exact corr_of_val D₀.P.isLB fun y J hJ => (val_pull hJ _ _ _).trans ((H _ _ y J hJ).trans (val_one _).symm)
  · exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ H r).trans (val_one _))

theorem comb_iff {m : ℕ} (cf : Fin m → A) (e : Fin m → Out.GtPt D₀ (epsR A)) (ν : Out.GtPt D₀ (epsR A)) :
    GtComb cf e ν ↔ IsCombGt e cf ν := Iff.rfl

variable {A' : Type} [CommRing A'] [IsDomain A'] {D₁ : Out.DegPre A'} {f : A →+* A'}

end Gt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Inputs

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A} {b' : O →+* A'}

def SameLevel (a : ArcIn Dw l β A b) (s : Dw.La → Out.QkPt a.D₀ (FractionRing A) l.M)
    (sA : Dw.La → Out.QkPt a.D₀ (FractionRing A) l.A) : Prop :=
  (∀ v, Out.QkPt.Equiv a.D₀ _ (sA v) (a.etaA v)) ∧
    ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), Out.QkPt.Equiv a.D₀ _ (s v) (a.eta v)

variable (f : A →+* A') (a : ArcIn Dw l β A b) (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀)

variable {Y : Model Xo c β} {a a'} {χ : Sp (PowerSeries A) ⟶ Y.X}

end Inputs

section ThetaShiftProofs

variable {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)

theorem lieId_iff [IsLocalRing A] (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) :
    LieId W ν v ↔ GtTanR ν ∧ LieImg W ν v := by
  rw [tan_iff]; exact GlobalTheory.T.lie_identity_arc_witness_iff E H Dw l Xo c O β Y A b a χ W ν v

theorem arcBasis_iff [IsLocalRing A] [IsNoetherianRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A))
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) :
    ArcBasis W ρ e ↔ ∀ τ, (letI := H.starRing; IsEigBasisGt a.oa (ρ τ) (e τ)) := by
  have hG := GlobalTheory.globalFns_holds
  have ex := ConstLie.main hG E H Dw l Xo c O β Y A b a χ W
  have eg := GlobalTheory.T.arc_witness_tangent_point hG E H Dw l Xo c O β Y A b a χ W
  have ba := fun t m e v => GlobalTheory.T.arc_witness_tangent_family hG E H Dw l Xo c O β Y A b a χ W t m e v _ fun _ => Iff.rfl
  constructor
  · rintro ⟨v, hv, h⟩ τ
    refine ⟨fun i => (tan_iff _).1 (((ex _).2 _ (hv τ i)).2 ((h τ).1 i).1),
      fun i => (eg _ _ _ (hv τ i)).2 ((h τ).1 i).2, fun ω ht he => ?_⟩
    obtain ⟨w, hw, -⟩ := (ex ω).1
    exact (ba (ρ τ) _ (e τ) (v τ) (hv τ) (h τ).1).1 (h τ).2 ω w hw (((ex _).2 _ hw).1 ((tan_iff _).2 ht))
      ((eg _ _ _ hw).1 he)
  · intro h
    choose v hv _ using fun τ k => (ex (e τ k)).1
    have h₁ := fun τ k => And.intro (((ex _).2 _ (hv τ k)).1 ((tan_iff _).2 ((h τ).1 k)))
      ((eg _ _ _ (hv τ k)).1 ((h τ).2.1 k))
    exact ⟨v, hv, fun τ => ⟨h₁ τ, (ba (ρ τ) _ (e τ) (v τ) (hv τ) (h₁ τ)).2 fun ν w hw ht he =>
      (h τ).2.2 ν ((tan_iff _).1 (((ex _).2 _ hw).2 ht)) ((eg _ _ _ hw).2 he)⟩⟩

theorem isLetters_iff [IsLocalRing A] [IsNoetherianRing A] (io : c.F →+* FractionRing A)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) :
    IsLetters a io e ↔ io.comp β = (algebraMap A (FractionRing A)).comp b ∧ ∃ ρ : (E →+* ℂ) → (𝓞 E →+* A),
      (∀ τ, (algebraMap A (FractionRing A)).comp (ρ τ) = io.comp (embK c τ)) ∧ ArcBasis W ρ e :=
  and_congr Iff.rfl ⟨fun h => by
    choose ρ h₁ h₂ using h
    exact ⟨ρ, h₁, (arcBasis_iff W ρ e).2 h₂⟩, fun ⟨ρ, h₁, h₂⟩ τ => ⟨ρ τ, h₁ τ, (arcBasis_iff W ρ e).1 h₂ τ⟩⟩

variable [IsLocalRing A] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec)
  {S : Type} [CommRing S] [Algebra c.F S] (io : PowerSeries A →+* S) (y : FrPt Xo c S)

theorem dual_over {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [ConstLie.spMap_comp', ConstLie.spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isArcFr_of_isArcFrPt (h : IsArcFrPt W e th io y) : (∀ τ k, GtTanR (e τ k)) ∧ IsArcFr W e th io y := by
  obtain ⟨z, ⟨zx, -, zj⟩, hu, hθ⟩ := h
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  have comp : ∀ (x : Sp S ⟶ Xo.X) (_ : z ≫ pullback.fst _ _ = x),
      ∃ m1 : SABMap t' Xo.univ.t x, m1.φ = m.φ ≫ Y.m0.toSABMap.φ := by
    intro x hx; subst hx; exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m
  obtain ⟨m1, hm1⟩ := comp _ zx
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : p = spMap io ≫ χ) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' W.t (spMap io), n.φ = m'.φ ≫ W.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m n
  obtain ⟨m2, hm2⟩ := cancel _ zj n
  have φ2 : m.φ ≫ Y.m.φ = m2.φ ≫ W.m.φ := hn.symm.trans hm2
  refine ⟨fun τ k => ?_, z, t', m1, m2, m.φ, zj, zx, m.cart.1.w, hm1.symm, φ2, fun τ k => ?_,
    (GlobalTheory.T.arc_witness_theta_pullback GlobalTheory.globalFns_holds E H Dw l Xo c O β Y A b a χ W th S io y.x z t' m1 m2 m.φ y.s zj zx m.cart.1.w
      hm1.symm φ2).2 hθ⟩
  · obtain ⟨v, -, hv, -⟩ := hu τ k
    exact ((lieId_iff W _ _).1 hv).1
  · obtain ⟨v, uF, hv, h₁, h₂, h₃⟩ := hu τ k
    have a₁ := m.cart.1.lift_fst _ _ h₁
    have a₂ := m.cart.1.lift_snd _ _ h₁
    have vb : v.left ≫ W.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A))) := Over.w v
    refine ⟨v, m.cart.1.lift _ _ h₁, ((lieId_iff W _ _).1 hv).2, ?_, W.m.cart.1.hom_ext ?_ ?_, a₂⟩
    · rw [hm1, ← Category.assoc]
      exact (congrArg (· ≫ _) a₁).trans h₂
    · rw [Category.assoc, Category.assoc]
      exact (congrArg _ φ2.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) a₁).trans h₃))
    · rw [Category.assoc, Category.assoc, vb, dual_over, m2.cart.1.w, ← Category.assoc, a₂]

theorem isArcFrPt_of_isArcFr
    (hz : ∀ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = spMap io ≫ χ → z ≫ pullback.fst _ _ = y.x →
      z ≫ pullback.snd _ _ = spMap (algebraMap c.F S))
    (he : ∀ τ k, GtTanR (e τ k)) (h : IsArcFr W e th io y) : IsArcFrPt W e th io y := by
  obtain ⟨z, t', m1, m2, φ, zj, zx, φb, φ1, φ2, hu, hθ⟩ := h
  refine ⟨z, ⟨zx, hz z zj zx, zj⟩, fun τ k => ?_,
    (GlobalTheory.T.arc_witness_theta_pullback GlobalTheory.globalFns_holds E H Dw l Xo c O β Y A b a χ W th S io y.x z t' m1 m2 φ y.s zj zx φb φ1 φ2).1 hθ⟩
  obtain ⟨v, u, hv, h₁, h₂, h₃⟩ := hu τ k
  refine ⟨v, u ≫ φ, (lieId_iff W _ _).2 ⟨he τ k, hv⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, φb, ← Category.assoc, h₃]
  · rw [Category.assoc, φ1, h₁]
  · rw [Category.assoc, φ2, ← Category.assoc, h₂, Category.assoc]

theorem over_of_overBase [Mono (spMap β)] (hb : spMap io ≫ χ ≫ Y.s = spMap (algebraMap c.F S) ≫ spMap β)
    (z : Sp S ⟶ Xo.XF c) (zj : z ≫ Y.j = spMap io ≫ χ) : z ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  rw [← cancel_mono (spMap β), ← hb, ← Category.assoc (spMap io), ← zj, Model.j, Category.assoc, Category.assoc,
    Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]

theorem isArcFrPt_iff [Mono (spMap β)] :
    IsArcFrPt W e th io y ↔ (∀ τ k, GtTanR (e τ k)) ∧
      spMap io ≫ χ ≫ Y.s = spMap (algebraMap c.F S) ≫ spMap β ∧ IsArcFr W e th io y := by
  constructor
  · intro h
    refine ⟨(isArcFr_of_isArcFrPt W e th io y h).1, ?_, (isArcFr_of_isArcFrPt W e th io y h).2⟩
    obtain ⟨z, ⟨-, zs, zj⟩, -⟩ := h
    rw [← Category.assoc, ← zj, ← zs, Model.j, Category.assoc, Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc Y.jQ, Y.jQ_over]
  · rintro ⟨he, hb, h⟩
    exact isArcFrPt_of_isArcFr W e th io y (fun z zj _ => over_of_overBase io hb z zj) he h

end ThetaShiftProofs

end GlobalTheory.ArcCompare
end
end
