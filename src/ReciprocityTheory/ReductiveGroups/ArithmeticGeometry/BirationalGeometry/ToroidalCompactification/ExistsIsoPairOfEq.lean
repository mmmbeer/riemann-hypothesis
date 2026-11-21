import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

set_option maxHeartbeats 1600000 in

theorem ArcWit.witMove (h5 : Out.Laws5) (hQ : QkPullExistsSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) {G'' : Over (Sp R)}
    [GrpObj G''] [IsCommMonObj G''] {D'' : Out.DegData R I} [Module (𝓞 E) D''.toPre.X]
    {A'' : Out.PolAV (Sp (FractionRing R))} (U'' : Out.Unif I D'' A'' G'')
    (oD'' : letI := H.starRing; D''.toPre.OAct (𝓞 E))
    (bc : G'' ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W.t.G) [IsMonHom bc.hom]
    (hD : Out.IsPullDeg (RingHom.id R) W.P.D.toPre D''.toPre) (hPU : Out.IsPullUnif (RingHom.id R) hD bc W.P.U U'')
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, oD''.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)) :
    letI := H.starRing
    ∃ (he'' : eSec D''.toPre.P.A ≫ (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫
        W.φ = spMap f ≫ eSec a.D₀.P.A)
      (w'' : LB.Iso D''.toPre.P.L (a.D₀.P.L.pull
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ)))
      (e'' : a.D₀.X ≃ₗ[𝓞 E] D''.toPre.X),
      (∀ y, hD.xe (e'' y) = W.e y) ∧ Tri W.w hD.w w'' ∧
      IsGrpPullback D''.toPre.P.A a.D₀.P.A (spMap f)
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ) ∧ w''.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec D''.toPre.P.A) (fun _ => 1)) D''.toPre.rig
        (rigPullOf ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ)
          (spMap f) he'' a.D₀.P.L a.D₀.rig) ∧
      (∀ x, (oD''.onB.act x).left ≫
          (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ =
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ) ≫
          (a.oa.onB.act x).left) ∧
      (∀ y, (D''.toPre.c (e'' y)).left ≫
          (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ =
        spMap f ≫ (a.D₀.c y).left) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F),
        (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
          algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
        uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
        (∀ y, GenRel w'' (LB.pullGen _ _ _ (D''.toPre.psi (e'' y)) (Out.jFK (R := R) F))
          (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F)) (uF ^ (a.be y y / 2))) ∧
        ∀ (yF : Sp F ⟶ Xo.XF c), yF ≫ Y.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χ →
          ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
            ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
              (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
                HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
            ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt D''.toPre F k) (x : Out.TFK (R := R) F ⟶ A''.A),
              QkExt (algebraMap _ F) p₀ q₀ → q.y = e'' q₀.y →
              (∀ z, GenRel w'' (q.g.s (e'' z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k))) →
              x.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
                pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) ≫ W.m.φ = yF ≫ σ.left ≫ Y.m.φ →
              Out.QkToAkU U''.toUnifPre F k q x := by
  letI := H.starRing
  have hs := specOf_id R
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  set Φ := hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R)) with hΦ
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff W.w).1 s2
  obtain ⟨w', T⟩ := exists_comp W.P.D.toPre.P.isLB W.w hD.w g0 gD a.D₀.P.isLB D''.toPre.P.isLB
  let xe' : D''.toPre.X ≃ₗ[𝓞 E] W.P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := hD.e_hom
  have gpB : IsGrpPullback D''.toPre.P.A W.P.D.toPre.P.A (spMap (RingHom.id R)) Φ :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback W.P.D.toPre.P.A (Out.specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hxe : ∀ y, hD.xe (xe'.symm (W.e y)) = W.e y := fun y => xe'.apply_symm_apply _
  have hsf : spMap (RingHom.id R) ≫ spMap f = spMap f := by
    simp [spMap]
  have he' : eSec D''.toPre.P.A ≫ Φ ≫ W.φ = spMap f ≫ eSec a.D₀.P.A := by
    rw [← Category.assoc, hD.he, Category.assoc, W.he, ← Category.assoc, hsf]
  refine ⟨he', w', W.e.trans xe'.symm, hxe, T, (gpB.comp s1).congr hsf rfl,
    (isGen_iff w').2 (T.pgen_comp W.P.D.toPre.P.isLB g0 gD), ?_, fun x => ?_, fun y => ?_,
    fun F _ _ _ _ uF ha hu => ?_⟩
  · have r₀ := (maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le W.φ (spMap f) W.he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec W.P.D.toPre.P.A) _ D''.toPre.rig W.P.D.toPre.rig
      (Out.specOf (RingHom.id R)) _ (rigPull_le Φ (Out.specOf (RingHom.id R)) hD.he W.P.D.toPre.P.L) (fun _ => rfl)).1
      hD.w_rig
    have r₂ := T.pmaps_comp W.P.D.toPre.P.isLB (fun _ => hD.he) r₀ r₁
    rw [hsf] at r₂
    exact (maps_iff w' _ (fun _ => eSec a.D₀.P.A) _ D''.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le (Φ ≫ W.φ) (spMap f) he' a.D₀.P.L) (fun _ => rfl)).2 r₂
  · have e₁ : (oD''.onB.act x).left ≫ Φ = Φ ≫ (W.P.oD.onB.act x).left := by
      have e₀ := congrArg (fun z => z.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) (el x)
      have e₂ : ((Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)).left ≫
          pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R)) = pullback.fst _ _ ≫ (W.P.oD.onB.act x).left :=
        pullback.lift_fst _ _ _
      simp only [Over.comp_left, Category.assoc, e₂] at e₀
      simpa only [hΦ, Category.assoc] using e₀
    show (oD''.onB.act x).left ≫ Φ ≫ W.φ = (Φ ≫ W.φ) ≫ (a.oa.onB.act x).left
    rw [← Category.assoc, e₁, Category.assoc, s4 x, Category.assoc]; rfl
  · show (D''.toPre.c (xe'.symm (W.e y))).left ≫ Φ ≫ W.φ = spMap f ≫ (a.D₀.c y).left
    rw [← Category.assoc, hD.c_pr, hxe, Category.assoc, s5 y, ← Category.assoc, hsf]
  · have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing R) F (algebraMap R (FractionRing R) ((RingHom.id R) r)) := fun _ => rfl
    have hj : Out.jFK (R := R) F ≫ Out.jK R ≫ spMap (RingHom.id R) = Out.jFK (R := R) F ≫ Out.jK R := by
      simp [spMap]
    obtain ⟨k₁, k₂⟩ := s6 F uF ha hu
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀ q' x' e1 e2 e3 e4 => ?_⟩
    · have pm := pmaps_psi hD F hj (xe'.symm (W.e y))
      have k := k₁ y
      rw [← hxe y] at k
      refine (genRel_transfer T W.P.D.toPre.P.isLB D''.toPre.P.isLB (fun _ => ?_) pm _ _).1 k
      have hx : D''.toPre.xK (xe'.symm (W.e y)) ≫ Φ =
          Out.jK R ≫ Out.specOf (RingHom.id R) ≫ (W.P.D.toPre.c (hD.xe (xe'.symm (W.e y)))).left := by
        rw [← hD.c_pr, ← Category.assoc]; rfl
      rw [Category.id_comp, Category.assoc, hx, ← Category.assoc (Out.jK R), ← Category.assoc]
      exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
    · obtain ⟨q, hq₁, hq₂⟩ := hQ R R (RingHom.id R) W.P.D.toPre D''.toPre hD F hF k q'
      have a1 : bc.hom.left ≫ pullback.snd W.t.G.hom (Out.specOf (RingHom.id R)) = G''.hom := Over.w bc.hom
      have a2 : U''.gen.inv.left ≫ pullback.snd G''.hom (Out.jK R) = A''.A.hom := Over.w U''.gen.inv
      have a3 : x'.left ≫ A''.A.hom = Out.jFK (R := R) F := Over.w x'
      have hcomm : (x'.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
          pullback.fst W.t.G.hom (Out.specOf (RingHom.id R))) ≫ W.t.G.hom = Out.jFK (R := R) F ≫ Out.jK R := by
        simp only [Category.assoc, pullback.condition, pullback.condition_assoc, reassoc_of% a1, reassoc_of% a2,
          reassoc_of% a3]
        simp [Out.specOf]
      let z : Out.TFK (R := R) F ⟶ (Over.pullback (Out.jK R)).obj W.t.G :=
        Over.homMk (pullback.lift _ (Out.jFK (R := R) F) hcomm) (pullback.lift_snd _ _ _)
      let x : Out.TFK (R := R) F ⟶ W.P.A.A := z ≫ W.P.U.gen.hom
      have hx : x'.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
          pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) =
          x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK R) := by
        have hgi : W.P.U.gen.hom.left ≫ W.P.U.gen.inv.left = 𝟙 _ := by
          rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
        show _ = (z.left ≫ W.P.U.gen.hom.left) ≫ _
        rw [Category.assoc, ← Category.assoc W.P.U.gen.hom.left, hgi, Category.id_comp]
        exact (pullback.lift_fst _ _ _).symm
      have hk : 1 ≤ k := by
        rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      refine h5.qkBaseChange R R I I hR hR (RingHom.id R) W.P.D W.P.A W.t.G W.P.U G'' bc inferInstance A'' D'' hD U''
        hPU F hF k hk q x q' x' hq₁ hq₂ hx (k₂ yF hyF k p₀ σ hσ q₀ q x e1 ?_ (fun z => ?_) ?_)
      · have : hD.xe q'.y = q.y := by rw [hq₁, AddEquiv.apply_symm_apply]
        rw [← this, e2]; exact hxe _
      · obtain ⟨hψ', hm⟩ := hq₂.2 (xe'.symm (W.e z))
        have pm := (maps_iff hD.w _ _ _ (q'.g.s (xe'.symm (W.e z))) (q.g.s (hD.xe (xe'.symm (W.e z)))) (𝟙 _) _
          (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
        have k' := (genRel_transfer T W.P.D.toPre.P.isLB D''.toPre.P.isLB hψ' pm _ _).2 (e3 z)
        rw [hxe z] at k'
        exact k'
      · rw [← e4]
        simpa only [Category.assoc] using congrArg (· ≫ W.m.φ) hx.symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U)
    (x : Γ(X, U)ˣ) : res h (res h' x) = res (h.trans h') x := by
  have e : X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (h.trans h')).op := by
    rw [← Functor.map_comp]
    rfl
  apply Units.ext
  exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

private theorem res_g_mul_res_g_eq_res_g_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k := le_inf h₁ (h₂.trans inf_le_right)
  have key := congrArg (⇑(res hW)) (hL.cocycle i j k)
  simp only [map_mul, res_res_lemma] at key
  exact key

private theorem gm_res_toroidal_compactification {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U)
    (hy : f y ∈ V) (x : Γ(X, U)ˣ) : gm f y V (res h x) = gm f y U x := by
  have hU : f y ∈ U := h hy
  have e : X.presheaf.map (homOfLE h).op ≫ f.app V ≫ Y.presheaf.germ (f ⁻¹ᵁ V) y hy =
      f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hU := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm
  rw [dif_pos hy, dif_pos hU]
  apply Units.ext
  exact congrArg (fun φ => φ.hom (x : Γ(X, U))) e

private theorem isGen_g_iso_self_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    (⟨fun p : L.ι × L.ι => L.g p.1 p.2⟩ : LB.Iso L L).IsGen := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  have h₀ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U p₂ := inf_le_left
  have h₁ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₁ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₂ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U q₁ ⊓ L.U q₂ := inf_le_right
  have h₃ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₁ ⊓ L.U q₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  have h₄ : L.U p₁ ⊓ L.U p₂ ⊓ (L.U q₁ ⊓ L.U q₂) ≤ L.U p₂ ⊓ L.U q₂ :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have c₁ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ q₁ q₂ h₁ h₂ h₃
  have c₂ := res_g_mul_res_g_eq_res_g_of_isLB hL p₁ p₂ q₂ h₀ h₄ h₃
  have key : res h₀ (L.g p₁ p₂) =
      res h₁ (L.g p₁ q₁) * (res h₄ (L.g p₂ q₂))⁻¹ * res h₂ (L.g q₁ q₂) := by
    rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]
  exact key

private theorem gm_g_mul_gm_g_swap_eq_one_of_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y)
    {i j : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j) :
    gm f y (L.U j ⊓ L.U i) (L.g j i) * gm f y (L.U i ⊓ L.U j) (L.g i j) = 1 := by
  have hW : f y ∈ L.U j ⊓ L.U i := ⟨hj, hi⟩
  have h₂ : L.U j ⊓ L.U i ≤ L.U i ⊓ L.U j := le_of_eq (inf_comm _ _)
  have h₃ : L.U j ⊓ L.U i ≤ L.U j ⊓ L.U j := le_inf inf_le_left inf_le_left
  rw [← gm_res_toroidal_compactification f y h₂ hW (L.g i j), ← gm_res_toroidal_compactification f y (le_refl (L.U j ⊓ L.U i)) hW (L.g j i),
    ← map_mul (gm f y (L.U j ⊓ L.U i)), res_g_mul_res_g_eq_res_g_of_isLB hL j i j (le_refl _) h₂ h₃,
    ← res_res_lemma (inf_le_left : L.U j ⊓ L.U i ≤ L.U j) (le_inf le_rfl le_rfl : L.U j ≤ L.U j ⊓ L.U j),
    hL.g_self]
  simp only [map_one]

theorem exists_iso_pair_of_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G}
    (h : L₁ = L₂) :
    ∃ (w : LB.Iso L₁.L L₂.L) (w' : LB.Iso L₂.L L₁.L), w.IsGen ∧ w'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig ∧
      LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₂.rig L₁.rig ∧
      ∀ {Y : Scheme.{0}} (f : Y ⟶ G.left) (y : Y) (i : L₁.L.ι) (j : L₂.L.ι), f y ∈ L₁.L.U i → f y ∈ L₂.L.U j →
        gv w f y j i * gv w' f y i j = 1 := by
  cases h
  refine ⟨⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩, ⟨fun p : L₁.L.ι × L₁.L.ι => L₁.L.g p.1 p.2⟩,
    isGen_g_iso_self_of_isLB L₁.isLB, isGen_g_iso_self_of_isLB L₁.isLB, ?_, ?_, ?_⟩
  · intro p
    exact L₁.rigGen p.1 p.2
  · intro p
    exact L₁.rigGen p.1 p.2
  · intro Y f y i j hi hj
    exact gm_g_mul_gm_g_swap_eq_one_of_isLB L₁.isLB f y hi hj

section Lev

open ReciprocityTheory.ChartRestriction.G.Out

end Lev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
