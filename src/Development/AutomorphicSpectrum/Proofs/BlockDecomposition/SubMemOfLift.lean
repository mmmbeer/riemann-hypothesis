import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ChartP

open GlobalTheory.CompanionTheory.ChartAlg

section Lift

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} {T : Fin d → Γ(X, V)}
  (𝓛 : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ)

def barI : R ⧸ I →+* 𝓛.D ⧸ I.map 𝓛.i := Ideal.quotientMap (I.map 𝓛.i) 𝓛.i Ideal.le_comap_map

theorem barI_mk (r : R) : barI 𝓛 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (𝓛.i r) := rfl

theorem j_strV : 𝓛.j.comp (strV q V) = (barI 𝓛).comp κ := by
  refine RingHom.ext fun o => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
  rw [RingHom.comp_apply, RingHom.comp_apply, 𝓛.hj o x hx, ← hx, barI_mk]

def ptL (hV : IsAffineOpen V) : PtOver X q κ (𝓛.D ⧸ I.map 𝓛.i) :=
  ⟨(barI 𝓛, Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec), by
    change (Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec) ≫ q = Spec.map (CommRingCat.ofHom ((barI 𝓛).comp κ))
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← j_strV]
    rfl⟩

theorem rep_lift (hV : IsAffineOpen V) (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : 𝓛.D ⧸ I.map 𝓛.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) (ptL 𝓛 hV) = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hbase : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := 𝓛.univ B (ψ'.comp (Ideal.Quotient.mk I)) e'
    (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]) hbase
  have hk : ∀ a ∈ I.map 𝓛.i, f a = 0 := by
    have hle : I.map 𝓛.i ≤ RingHom.ker f := Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact fun a ha => hle ha
  let φ : 𝓛.D ⧸ I.map 𝓛.i →+* B := Ideal.Quotient.lift _ f hk
  have hφ : ∀ z, φ (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have hφj : φ.comp 𝓛.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
    rw [RingHom.comp_apply, ← hz, hφ]
    exact hf2 r z hz
  have hφψ : φ.comp (barI 𝓛) = ψ' := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun r => ?_
    change φ (barI 𝓛 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
    rw [barI_mk, hφ]
    exact RingHom.congr_fun hf1 r
  refine ⟨φ, ?_, ?_⟩
  · refine Subtype.ext (Prod.ext hφψ ?_)
    change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
    exact eq_specMap hV y'.1.2 hy'
  · intro φ' h'
    have h1 : φ'.comp (barI 𝓛) = ψ' := congrArg (fun z => z.1.1) h'
    have h2 : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2 :=
      congrArg (fun z => z.1.2) h'
    have h3 : e' = φ'.comp 𝓛.j := by
      refine evalAt_specMap hV (φ'.comp 𝓛.j) y'.1.2 ?_ hy'
      rw [← h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h4 : φ'.comp (Ideal.Quotient.mk _) = f := by
      refine hfu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        exact RingHom.congr_fun h1 (Ideal.Quotient.mk I r)
      · rw [h3]
        exact congrArg φ' hz
    apply Ideal.Quotient.ringHom_ext
    exact h4

variable (γ : DividedPowers I) (p : ℕ) (δ : DividedPowers (I.map 𝓛.i)) (hδ : IsDPMorphism γ δ 𝓛.i)
  (hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i))) (hV : IsAffineOpen V)

def thL : Thick (nlFun γ p X q κ) := mkT 𝓛.D 𝓛.i (I.map 𝓛.i) δ hadm hδ (ptL 𝓛 hV) (fun _ => rfl)

theorem thL_inU : InU V (thL 𝓛 γ p δ hδ hadm hV) := top_le_specMap hV 𝓛.j

theorem ev_thL : ev (thL 𝓛 γ p δ hδ hadm hV) (thL_inU 𝓛 γ p δ hδ hadm hV) = 𝓛.j :=
  evalAt_specMap hV 𝓛.j _ rfl _

def chartL (het : (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t : MvPolynomial (Fin d) R →+* 𝓛.D).Etale) : Chart γ p q κ V d where
  D := thL 𝓛 γ p δ hδ hadm hV
  t := 𝓛.t
  etale := het
  J_eq := rfl
  inV := thL_inU 𝓛 γ p δ hδ hadm hV
  rep := rep_lift 𝓛 hV

end Lift

theorem exists_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  intro O R _ _ I γ p hp hn X q κ V d c
  obtain ⟨𝓛⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale
  have hflat : 𝓛.i.Flat := (GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).1
  obtain ⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map 𝓛.i), IsDPMorphism γ δ 𝓛.i := by
    letI := 𝓛.i.toAlgebra
    haveI : Module.Flat R 𝓛.D := hflat
    exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat R 𝓛.D I γ
  have hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i)) :=
    ⟨fun _ => by simpa using hn.map 𝓛.i, fun h => absurd h hp⟩
  exact ⟨chartL 𝓛 γ p δ hδ hadm c.affine 𝓛.et, hflat, fun i =>
    (RingHom.congr_fun (ev_thL 𝓛 γ p δ hδ hadm c.affine) (c.t i)).trans (𝓛.hT i)⟩

end GlobalTheory.CompanionTheory.ChartP
end
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr

structure Pts {b : Base} (L : b.Fun) {Y : Scheme.{0}} (qY : Y ⟶ Spec (CommRingCat.of b.R)) where
  pt : ∀ T : Thick L, Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ Y
  nat : ∀ {T T' : Thick L} (φ : T ⟶ T'),
    pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T
  str : ∀ T : Thick L, pt T ≫ qY = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp T.i))

section Fib

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥)

def bar : R ⧸ I ≃+* R := (Ideal.quotEquivOfEq hI).trans (RingEquiv.quotientBot R)

def gk (κ : O →+* R ⧸ I) : O →+* R := (bar hI).toRingHom.comp κ

theorem mk_bar (x : R ⧸ I) : Ideal.Quotient.mk I (bar hI x) = x := by
  subst hI
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem mk_gk (κ : O →+* R ⧸ I) (a : O) : Ideal.Quotient.mk I (gk hI κ a) = κ a := mk_bar hI (κ a)

variable {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)

abbrev XF : Scheme.{0} := pullback q (Spec.map (CommRingCat.ofHom (gk hI κ)))

abbrev jF : XF hI q κ ⟶ X := pullback.fst _ _

abbrev qF : XF hI q κ ⟶ Spec (CommRingCat.of R) := pullback.snd _ _

variable {q κ} {γ : DividedPowers I} {p : ℕ}

theorem pt_comp (T : Thick (nlFun γ p X q κ)) :
    pt T ≫ q = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp T.i)) ≫
      Spec.map (CommRingCat.ofHom (gk hI κ)) := by
  have h := (show PtOver X q κ (T.B ⧸ T.J) from T.y).2
  refine h.trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun a => ?_)
  have hw := T.w (gk hI κ a)
  rw [mk_gk] at hw
  exact hw

theorem pt_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') :
    pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

variable (γ p q κ) in

def fib : Pts (nlFun γ p X q κ) (qF hI q κ) where
  pt T := pullback.lift (pt T) (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp T.i))) (pt_comp hI T)
  nat {T T'} φ := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact pt_nat φ
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun a => ?_)
      exact congrArg (Ideal.Quotient.mk T'.J) (φ.comm a).symm
  str T := pullback.lift_snd _ _ _

theorem fib_fst (T : Thick (nlFun γ p X q κ)) : (fib hI q κ γ p).pt T ≫ jF hI q κ = pt T := pullback.lift_fst _ _ _

end Fib

end GlobalTheory.CompanionTheory.FibGr
end

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr
open GlobalTheory.CompanionTheory.GrForm (wz wz_mem rep_add rep_neg sum_wz_sub rep_congr a_eq form_eq form_sub_mem)
open GlobalTheory.CompanionTheory.GrCech (mulMor mulT_congr mulMor_add mulMor_mul mulMor_smul res_res pull_mk)

variable {b : Base} {L : b.Fun} {Y : Scheme.{0}} {qY : Y ⟶ Spec (CommRingCat.of b.R)} (𝔭 : Pts L qY)

def InY (W : Y.Opens) (T : Thick L) : Prop := ⊤ ≤ 𝔭.pt T ⁻¹ᵁ W

def ev {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) : Γ(Y, W) →+* T.B ⧸ T.J := GlobalTheory.Cris.evalAt (𝔭.pt T) W h

theorem ev_nat {W : Y.Opens} {T T' : Thick L} (φ : T ⟶ T') (h : InY 𝔭 W T) (h' : InY 𝔭 W T') (f : Γ(Y, W)) :
    ev 𝔭 T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev 𝔭 T h f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ Y) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ 𝔭.pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev 𝔭 T h f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (𝔭.pt T) h hh f
  exact key _ (𝔭.nat φ) h'

theorem ev_res {W W' : Y.Opens} (hW : W' ≤ W) (T : Thick L) (h : InY 𝔭 W T) (h' : InY 𝔭 W' T) (f : Γ(Y, W)) :
    ev 𝔭 T h' (rs hW f) = ev 𝔭 T h f := evalAt_res (𝔭.pt T) hW h h' f

theorem ev_str {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (a : b.R) :
    ev 𝔭 T h (strV qY W a) = Ideal.Quotient.mk T.J (T.i a) :=
  evalAt_base qY (RingHom.id b.R) ((Ideal.Quotient.mk T.J).comp T.i) (𝔭.pt T) (by rw [RingHom.comp_id]; exact 𝔭.str T) h a

open Classical in

def lft (W : Y.Opens) (T : Thick L) (f : Γ(Y, W)) : T.B :=
  if h : InY 𝔭 W T then Function.surjInv Ideal.Quotient.mk_surjective (ev 𝔭 T h f) else 0

theorem lft_spec {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f : Γ(Y, W)) :
    Ideal.Quotient.mk T.J (lft 𝔭 W T f) = ev 𝔭 T h f := by
  rw [lft, dif_pos h]
  exact Function.surjInv_eq _ _

def IsLift (W : Y.Opens) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) : Prop :=
  ∀ i (T : Thick L) (h : InY 𝔭 W T), Ideal.Quotient.mk T.J (u i T) = ev 𝔭 T h (t i)

variable (L) in

abbrev GF (r : ℕ) : Thick L ⥤ ModuleCat.{0} b.R := sq (thFil L r) (thFil L ((r : ℤ) + 1))

def Rp {W : Y.Opens} (P : ObjectProperty (Thick L)) {d r : ℕ} (u : Fin d → ∀ T : Thick L, T.B)
    (x : Idx r d → Γ(Y, W)) (c : HU (GF L r) P r) : Prop :=
  CrystallineSemistableComparison.Pb.Rep (sFil P r) (sFil P ((r : ℤ) + 1)) (fun s => ∑ I : Idx r d,
    wz (Φ := sP P) (fun i T => u i T.obj) I.1 s *
      (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I))) c

theorem lift_sub_mem {W : Y.Opens} {P : ObjectProperty (Thick L)} (hP : ∀ T, P T → InY 𝔭 W T) (f : Γ(Y, W))
    (v : ∀ T : Thick L, T.B) (hv : ∀ (T : Thick L) (h : InY 𝔭 W T), Ideal.Quotient.mk T.J (v T) = ev 𝔭 T h f)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from v T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from v T.obj) ∈ (sP P).J.S T' := by
  have h := hP _ T.property
  have h' := hP _ T'.property
  change v T'.obj - φ.hom.φ (v T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq, hv _ h', ev_nat 𝔭 φ.hom h h' f, ← hv _ h]
  rfl

theorem exists_rp (W : Y.Opens) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) (hu : IsLift 𝔭 W t u)
    (P : ObjectProperty (Thick L)) (hP : ∀ T, P T → InY 𝔭 W T) (r : ℕ) (x : Idx r d → Γ(Y, W)) :
    ∃ c, Rp 𝔭 (W := W) P u x c := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hu' : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' :=
    fun i _ _ φ => lift_sub_mem 𝔭 hP (t i) (u i) (hu i) φ
  have hy : ∀ (I : Idx r d) {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from lft 𝔭 W T'.obj (x I)) -
        ((sP P).A.map φ).hom (show (sP P).A.obj T from lft 𝔭 W T.obj (x I)) ∈ (sP P).J.S T' :=
    fun I _ _ φ => lift_sub_mem 𝔭 hP (x I) (fun T => lft 𝔭 W T (x I)) (fun T h => lft_spec 𝔭 T h (x I)) φ
  choose f hf hz using fun I : Idx r d =>
    GlobalTheory.CompanionTheory.GrForm.stCocycle hF (fun i (T : P.FullSubcategory) => (show (sP P).A.obj T from u i T.obj)) hu'
      (fun T : P.FullSubcategory => (show (sP P).A.obj T from lft 𝔭 W T.obj (x I))) (hy I) I.1
  have hd : CH.d (sq (sFil P r) (sFil P ((r : ℤ) + 1))) r (∑ I, f I) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun I _ => hf I
  refine ⟨(CH.cx (sq (sFil P r) (sFil P ((r : ℤ) + 1)))).cls (∑ I, f I) hd, ∑ I, f I, hd, rfl, ?_⟩
  intro s
  have e : (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from (∑ I, f I) s) =
      ∑ I, (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f I s) := Finset.sum_apply _ _ _
  rw [e, AddSubmonoidClass.coe_finset_sum, map_sum]
  exact Finset.sum_congr rfl fun I _ => hz I s

theorem lft_add_sub {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f g : Γ(Y, W)) :
    lft 𝔭 W T (f + g) - (lft 𝔭 W T f + lft 𝔭 W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, lft_spec 𝔭 T h, lft_spec 𝔭 T h, lft_spec 𝔭 T h, map_add, sub_self]

theorem lft_neg_sub {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f : Γ(Y, W)) :
    lft 𝔭 W T (-f) - (-lft 𝔭 W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec 𝔭 T h, lft_spec 𝔭 T h, map_neg, sub_self]

theorem lift_cocycle {W : Y.Opens} {d : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 W t u) (P : ObjectProperty (Thick L)) (hP : ∀ T, P T → InY 𝔭 W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat 𝔭 φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

theorem rp_add (W : Y.Opens) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) (hu : IsLift 𝔭 W t u)
    (P : ObjectProperty (Thick L)) (hP : ∀ T, P T → InY 𝔭 W T) (r : ℕ) (x x' : Idx r d → Γ(Y, W))
    (c c' : HU (GF L r) P r) (hc : Rp 𝔭 (W := W) P u x c) (hc' : Rp 𝔭 (W := W) P u x' c') :
    Rp 𝔭 (W := W) P u (x + x') (c + c') ∧ Rp 𝔭 (W := W) P u (-x) (-c) := by
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle 𝔭 hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub 𝔭 _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub 𝔭 _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

theorem lift_cocycle_mem {W : Y.Opens} {d : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 W t u) {Q : ObjectProperty (Thick L)} (hQ : ∀ T, Q T → InY 𝔭 W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat 𝔭 φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : Y.Opens} (hW : W' ≤ W) (T : Thick L) (h : InY 𝔭 W T) (h' : InY 𝔭 W' T) (f : Γ(Y, W)) :
    lft 𝔭 W T f - lft 𝔭 W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec 𝔭 T h f, lft_spec 𝔭 T h' (rs hW f), ev_res 𝔭 hW T h h' f]

theorem rp_res (W W' : Y.Opens) (hW : W' ≤ W) {d : ℕ} (t : Fin d → Γ(Y, W)) (u : Fin d → ∀ T : Thick L, T.B) (hu : IsLift 𝔭 W t u)
    (P P' : ObjectProperty (Thick L)) (hPP : P' ≤ P) (hP : ∀ T, P T → InY 𝔭 W T) (hP' : ∀ T, P' T → InY 𝔭 W' T)
    (r : ℕ) (x : Idx r d → Γ(Y, W)) (c : HU (GF L r) P r) (hc : Rp 𝔭 (W := W) P u x c) :
    Rp 𝔭 (W := W') P' u (fun I => rs hW (x I)) ((resU (GF L r) hPP).pull r c) := by
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InY 𝔭 W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF L r) hPP).pullC r f, ?_, rfl, ?_⟩
  · have := (resU (GF L r) hPP).d_pullC r f
    refine this.trans ?_
    have hf' : CH.d (P.ι ⋙ GF L r) r f = 0 := hf
    rw [hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem 𝔭 hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft 𝔭 W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem 𝔭 hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    exact hsum

end GlobalTheory.CompanionTheory.FibGr
end
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr
open GlobalTheory.CompanionTheory.GrForm (wz wz_mem rep_add rep_neg sum_wz_sub rep_congr a_eq form_eq form_sub_mem)
open GlobalTheory.CompanionTheory.GrCech (mulMor mulT_congr mulMor_add mulMor_mul mulMor_smul res_res pull_mk)

variable {b : Base} {L : b.Fun} {Y : Scheme.{0}} {qY : Y ⟶ Spec (CommRingCat.of b.R)} (𝔭 : Pts L qY)

theorem sub_mem_of_lift {W : Y.Opens} {T T' : Thick L} (φ : T ⟶ T') (h : InY 𝔭 W T) (h' : InY 𝔭 W T') (f : Γ(Y, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev 𝔭 T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev 𝔭 T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat 𝔭 φ h h', ← hv]
  rfl

theorem J_mul_sFil (P : ObjectProperty (Thick L)) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T :=
  GlobalTheory.CompanionTheory.GrCech.J_mul_mem (GlobalTheory.CompanionTheory.DPFil.isFil_sFil P) r hv hw

def evLift {Q : ObjectProperty (Thick L)} {W : Y.Opens} (_hQ : ∀ T, Q T → InY 𝔭 W T) (f : Γ(Y, W))
    (T : Q.FullSubcategory) : (sP Q).A.obj T := lft 𝔭 W T.obj f

theorem mk_evLift {Q : ObjectProperty (Thick L)} {W : Y.Opens} (hQ : ∀ T, Q T → InY 𝔭 W T) (f : Γ(Y, W))
    (T : Q.FullSubcategory) : Ideal.Quotient.mk T.obj.J (evLift 𝔭 hQ f T) = ev 𝔭 T.obj (hQ _ T.property) f :=
  lft_spec 𝔭 _ _ _

theorem sub_mem_of_mk {T : Thick L} {x y : T.B} (h : Ideal.Quotient.mk T.J x = Ideal.Quotient.mk T.J y) :
    x - y ∈ T.J := Ideal.Quotient.eq.1 h

theorem evLift_nat {Q : ObjectProperty (Thick L)} {W : Y.Opens} (hQ : ∀ T, Q T → InY 𝔭 W T) (f : Γ(Y, W))
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    evLift 𝔭 hQ f T' - ((sP Q).A.map φ).hom (evLift 𝔭 hQ f T) ∈ (sP Q).J.S T' := by
  refine sub_mem_of_mk (T := T'.obj) ?_
  rw [mk_evLift 𝔭, ev_nat 𝔭 φ.hom (hQ _ T.property) (hQ _ T'.property), ← mk_evLift 𝔭 hQ f T]
  rfl

def fAct {Q : ObjectProperty (Thick L)} (hF : IsFil (sP Q) (sFil Q)) {W : Y.Opens}
    (hQ : ∀ T, Q T → InY 𝔭 W T) (r : ℕ) (f : Γ(Y, W)) :
    HU (GF L r) Q r →ₗ[b.R] HU (GF L r) Q r :=
  (mulMor hF r (evLift 𝔭 hQ f) (evLift_nat 𝔭 hQ f)).pull r

section ThAct
variable {Q : ObjectProperty (Thick L)} (hF : IsFil (sP Q) (sFil Q)) {W : Y.Opens}
  (hQ : ∀ T, Q T → InY 𝔭 W T) (r : ℕ)

theorem fAct_add (f g : Γ(Y, W)) (c : HU (GF L r) Q r) :
    fAct 𝔭 hF hQ r (f + g) c = fAct 𝔭 hF hQ r f c + fAct 𝔭 hF hQ r g c := by
  refine mulMor_add hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift 𝔭, map_add (Ideal.Quotient.mk T.obj.J), mk_evLift 𝔭, mk_evLift 𝔭, map_add]

theorem fAct_mul (f g : Γ(Y, W)) (c : HU (GF L r) Q r) :
    fAct 𝔭 hF hQ r (f * g) c = fAct 𝔭 hF hQ r f (fAct 𝔭 hF hQ r g c) := by
  refine mulMor_mul hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift 𝔭, map_mul (Ideal.Quotient.mk T.obj.J), mk_evLift 𝔭, mk_evLift 𝔭, map_mul]

theorem fAct_one (c : HU (GF L r) Q r) : fAct 𝔭 hF hQ r 1 c = c := by
  refine (mulMor_smul hF r _ (1 : b.R) (fun T => sub_mem_of_mk (T := T.obj) ?_) r c).trans (one_smul _ _)
  rw [mk_evLift 𝔭, map_one, map_one (algebraMap b.R _)]
  exact (map_one _).symm

def fHom : Γ(Y, W) →+* AddMonoid.End (HU (GF L r) Q r) :=
  RingHom.mk' { toFun := fun f => (fAct 𝔭 hF hQ r f).toAddMonoidHom
                map_one' := AddMonoidHom.ext fun c => fAct_one 𝔭 hF hQ r c
                map_mul' := fun f g => AddMonoidHom.ext fun c => fAct_mul 𝔭 hF hQ r f g c }
    fun f g => AddMonoidHom.ext fun c => fAct_add 𝔭 hF hQ r f g c


theorem res_fAct {Q' : ObjectProperty (Thick L)} (hF' : IsFil (sP Q') (sFil Q')) {W' : Y.Opens}
    (hQ' : ∀ T, Q' T → InY 𝔭 W' T) (hW : W' ≤ W) (hle : Q' ≤ Q) (f : Γ(Y, W)) (c : HU (GF L r) Q r) :
    (resU (GF L r) hle).pull r (fAct 𝔭 hF hQ r f c) =
      fAct 𝔭 hF' hQ' r (rs hW f) ((resU (GF L r) hle).pull r c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change Submodule.Quotient.mk ((resU (GF L r) hle).hom.mapZ r ((mulMor hF r (evLift 𝔭 hQ f) (evLift_nat 𝔭 hQ f)).hom.mapZ r z)) =
    Submodule.Quotient.mk ((mulMor hF' r (evLift 𝔭 hQ' (rs hW f)) (evLift_nat 𝔭 hQ' (rs hW f))).hom.mapZ r ((resU (GF L r) hle).hom.mapZ r z))
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine Eq.symm (((mulT_congr hF' r (T := s.obj (Fin.last r)) (u := evLift 𝔭 hQ' (rs hW f) _) (v := evLift 𝔭 hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))) ?_ _)).trans ?_)
  · refine sub_mem_of_mk (T := (s.obj (Fin.last r)).obj) ?_
    rw [mk_evLift]
    exact (ev_res 𝔭 hW _ (hQ _ (hle _ (s.obj (Fin.last r)).property)) _ _).trans (mk_evLift 𝔭 hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))).symm
  · rfl

theorem fAct_str (a : b.R) (c : HU (GF L r) Q r) : fAct 𝔭 hF hQ r (strV qY W a) c = a • c := by
  refine mulMor_smul hF r _ a (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift 𝔭]
  exact ev_str 𝔭 _ _ a

end ThAct

theorem rp_class {W : Y.Opens} {P : ObjectProperty (Thick L)} {d r : ℕ} {u : Fin d → ∀ T : Thick L, T.B}
    {x : Idx r d → Γ(Y, W)} {c c' : HU (GF L r) P r} (h : Rp 𝔭 (W := W) P u x c) (h' : Rp 𝔭 (W := W) P u x c') : c = c' := by
  obtain ⟨f, hf, rfl, hs⟩ := h
  obtain ⟨f', hf', rfl, hs'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hs s).trans (hs' s).symm)
  subst e
  rfl

theorem inY_mono {W W' : Y.Opens} (h : W' ≤ W) {T : Thick L} (hT : InY 𝔭 W' T) : InY 𝔭 W T :=
  hT.trans (fun _ hx => h hx)

theorem isLift_res {V W : Y.Opens} (h : W ≤ V) {d : ℕ} {t : Fin d → Γ(Y, V)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 V t u) {t' : Fin d → Γ(Y, W)} (ht : ∀ i, t' i = rs h (t i)) : IsLift 𝔭 W t' u := by
  intro i T hT
  rw [ht, hu i T (inY_mono 𝔭 h hT), ev_res 𝔭 h T (inY_mono 𝔭 h hT) hT]

def Free (W : Y.Opens) (P : ObjectProperty (Thick L)) (r : ℕ) {d : ℕ} (u : Fin d → ∀ T : Thick L, T.B) : Prop :=
  (∀ cl : HU (GF L r) P r, ∃ x, Rp 𝔭 (W := W) P u x cl) ∧ ∀ x : Idx r d → Γ(Y, W), Rp 𝔭 (W := W) P u x 0 → x = 0

section Forms
variable {W : Y.Opens} {d : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
  {P : ObjectProperty (Thick L)} {r : ℕ}

theorem rp_zero (hu : IsLift 𝔭 W t u) (hP : ∀ T, P T → InY 𝔭 W T) :
    Rp 𝔭 (W := W) P u (0 : Idx r d → Γ(Y, W)) (0 : HU (GF L r) P r) := by
  obtain ⟨c, hc⟩ := exists_rp 𝔭 W t u hu P hP r 0
  have h2 := (rp_add 𝔭 W t u hu P hP r _ _ _ _ hc (rp_add 𝔭 W t u hu P hP r _ _ _ _ hc hc).2).1
  rw [add_neg_cancel, add_neg_cancel] at h2
  exact h2

theorem rp_sum (hu : IsLift 𝔭 W t u) (hP : ∀ T, P T → InY 𝔭 W T) {κ' : Type} (S : Finset κ')
    (x : κ' → Idx r d → Γ(Y, W)) (c : κ' → HU (GF L r) P r) (h : ∀ k ∈ S, Rp 𝔭 (W := W) P u (x k) (c k)) :
    Rp 𝔭 (W := W) P u (∑ k ∈ S, x k) (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rp_zero 𝔭 hu hP
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rp_add 𝔭 W t u hu P hP r _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1

theorem rp_coef (hu : IsLift 𝔭 W t u) (hP : ∀ T, P T → InY 𝔭 W T) (hF : Free 𝔭 W P r u)
    {x x' : Idx r d → Γ(Y, W)} {c : HU (GF L r) P r} (h : Rp 𝔭 (W := W) P u x c) (h' : Rp 𝔭 (W := W) P u x' c) : x = x' := by
  have h2 := (rp_add 𝔭 W t u hu P hP r _ _ _ _ h (rp_add 𝔭 W t u hu P hP r _ _ _ _ h' h').2).1
  rw [add_neg_cancel c] at h2
  exact add_neg_eq_zero.1 (hF.2 _ h2)

end Forms

theorem evLift_mul_sub {W : Y.Opens} {P : ObjectProperty (Thick L)} (hP : ∀ T, P T → InY 𝔭 W T) (z x : Γ(Y, W))
    (T : P.FullSubcategory) :
    (show T.obj.B from evLift 𝔭 hP z T) * lft 𝔭 W T.obj x - lft 𝔭 W T.obj (z * x) ∈ T.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, mk_evLift 𝔭, lft_spec 𝔭 _ (hP _ T.property), lft_spec 𝔭 _ (hP _ T.property), map_mul]

theorem rp_fAct {W : Y.Opens} {P : ObjectProperty (Thick L)} (hF : IsFil (sP P) (sFil P))
    (hP : ∀ T, P T → InY 𝔭 W T) {d r : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 W t u) (z : Γ(Y, W)) (x : Idx r d → Γ(Y, W)) (c : HU (GF L r) P r)
    (hc : Rp 𝔭 (W := W) P u x c) : Rp 𝔭 (W := W) P u (fun I => z * x I) (fAct 𝔭 hF hP r z c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulMor hF r (evLift 𝔭 hP z) (evLift_nat 𝔭 hP z)).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift 𝔭 φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from evLift 𝔭 hP z (s.obj (Fin.last r))) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have := J_mul_sFil P r _ (evLift_mul_sub 𝔭 hP z (x I) (s.obj (Fin.last r))) hw
    have e := GlobalTheory.CompanionTheory.GrForm.units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (evLift 𝔭 hP z (s.obj (Fin.last r))) (wz uu I.1 s) (lft 𝔭 W (s.obj (Fin.last r)).obj (x I))
      (lft 𝔭 W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

theorem free_of_frame (hLoc : KH.LocGr) {W : Y.Opens} {Q : ObjectProperty (Thick L)} (hin : ∀ T : Q.FullSubcategory, InY 𝔭 W T.obj)
    {d : ℕ} (u : Fin d → ∀ T : Thick L, T.B) (t : Fin d → Γ(Y, W)) (E : Frame (sP Q) d) (σ : ∀ T, E.D ⟶ T)
    (θ : Γ(Y, W) ≃+* (sP Q).A.obj E.D) (hGr : E.GrConst (sFil Q)) (hbot : (sFil Q 1).S E.D = ⊥)
    (hco : E.Coords fun i => θ (t i)) (hσ : ∀ i T, ((sP Q).A.map (σ T)).hom (θ (t i)) = u i T.obj)
    (hpt : ∀ (T : Q.FullSubcategory) (h : InY 𝔭 W T.obj) (f : Γ(Y, W)),
      Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP Q).A.map (σ T)).hom (θ f)) = ev 𝔭 T.obj h f)
    (Qp : Poly (sP Q)) (r : ℕ) (hC : ∀ r' : ℤ, r' ≤ (r : ℤ) + 1 → Qp.Crit (sFil Q) r') : Free 𝔭 W Q r u := by
  have hF : IsFil (sP Q) (sFil Q) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  obtain ⟨-, hL⟩ := hLoc Qp hF E σ hGr (r : ℤ) hC r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have key : ∀ (y : Idx r d → Γ(Y, W)) (z : ComposableArrows Q.FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP Q) (fun i T => u i T.obj) I.1 z *
          (show (sP Q).A.obj (z.obj (Fin.last r)) from lft 𝔭 W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil Q ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec 𝔭 _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil Q (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

theorem off_zero (hLoc : KH.LocGr) {Q : ObjectProperty (Thick L)} {d : ℕ} (E : Frame (sP Q) d) (σ : ∀ T, E.D ⟶ T)
    (hGr : E.GrConst (sFil Q)) (hbot : (sFil Q 1).S E.D = ⊥) (Qp : Poly (sP Q)) (r j : ℕ)
    (hC : ∀ r' : ℤ, r' ≤ (r : ℤ) + 1 → Qp.Crit (sFil Q) r') (hj : j ≠ r) : Subsingleton (HU (GF L r) Q j) := by
  have hF : IsFil (sP Q) (sFil Q) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  obtain ⟨h1, hL⟩ := hLoc Qp hF E σ hGr (r : ℤ) hC j
  rcases lt_or_gt_of_ne hj with h | h
  · obtain ⟨q, rfl⟩ : ∃ q, r = j + (q + 1) := ⟨r - j - 1, by omega⟩
    obtain ⟨h2, -⟩ := hL (q + 1) (by push_cast; ring)
    refine ⟨fun a c => ?_⟩
    have z : ∀ c : CH.H (gr (sFil Q) (((j + (q + 1) : ℕ) : ℤ))) j, c = 0 := by
      intro c
      obtain ⟨x, hx, f, hf, rfl, hs⟩ := h2 c
      have hx0 : ∀ I, x I = 0 := fun I => by
        have h3 : (sFil Q ((q + 1 : ℕ) : ℤ)).S E.D ≤ (sFil Q 1).S E.D := hF.anti (by push_cast; omega) _
        exact Ideal.mem_bot.1 (hbot ▸ h3 (hx I))
      have f0 : f = 0 := funext fun s => Subtype.ext (by
        refine (hs s).trans ?_
        have e0 : ∀ I : Idx j d, E.form σ I.1 (x I) s = 0 := fun I => by
          rw [hx0 I]
          unfold Frame.form
          rw [map_zero, mul_zero]
        have e1 : (∑ I : Idx j d, E.form σ I.1 (x I) s) = 0 := Finset.sum_eq_zero fun I _ => e0 I
        exact (congrArg (Ideal.Quotient.mk _) e1).trans (map_zero _))
      subst f0
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.zero_mem _)
    exact (z a).trans (z c).symm
  · exact h1 (by exact_mod_cast h)

theorem basis_gen {W₀ : Y.Opens} {d : ℕ} (t₀ : Fin d → Γ(Y, W₀)) (P₀ : ObjectProperty (Thick L))
    (hP₀ : ∀ T, P₀ T → InY 𝔭 W₀ T) (r : ℕ) :
    ∃ ω : Idx r d → HU (GF L r) P₀ r, ∀ (W : Y.Opens) (hle : W ≤ W₀) (Q : ObjectProperty (Thick L)) (hQ₀ : Q ≤ P₀)
      (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InY 𝔭 W T)
      (_ : Free 𝔭 W Q r (fun k T => lft 𝔭 W₀ T (t₀ k))) (h : HU (GF L r) Q r),
      ∃! f : Idx r d → Γ(Y, W), h = ∑ k, fAct 𝔭 hF hQW r (f k) ((resU (GF L r) hQ₀).pull r (ω k)) := by
  classical
  let u : Fin d → ∀ T : Thick L, T.B := fun k T => lft 𝔭 W₀ T (t₀ k)
  have hu : IsLift 𝔭 W₀ t₀ u := fun k T h => lft_spec 𝔭 T h _
  choose ω hω using fun k : Idx r d => exists_rp 𝔭 W₀ t₀ u hu P₀ hP₀ r (Pi.single k 1)
  refine ⟨ω, ?_⟩
  intro W hle Q hQ₀ hF hQW hFree h
  have hu' : IsLift 𝔭 W (fun i => rs hle (t₀ i)) u := isLift_res 𝔭 hle hu fun _ => rfl
  have hrep : ∀ f : Idx r d → Γ(Y, W), Rp 𝔭 (W := W) Q u f
      (∑ k, fAct 𝔭 hF hQW r (f k) ((resU (GF L r) hQ₀).pull r (ω k))) := by
    intro f
    have s1 := rp_sum 𝔭 hu' hQW Finset.univ
      (fun k I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(Y, W₀)) I)) _
      (fun k _ => rp_fAct 𝔭 hF hQW hu' (f k) _ _
        (rp_res 𝔭 W₀ W hle t₀ u hu P₀ Q hQ₀ hP₀ hQW r _ _ (hω k)))
    have e : (∑ k, fun I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(Y, W₀)) I)) = f := by
      funext I
      rw [Finset.sum_apply, Finset.sum_eq_single I]
      · simp
      · intro b _ hb'
        simp [Pi.single_eq_of_ne (Ne.symm hb')]
      · simp
    rwa [e] at s1
  obtain ⟨x, hx⟩ := hFree.1 h
  refine ⟨x, rp_class 𝔭 hx (hrep x), fun y hy => ?_⟩
  have hy' : Rp 𝔭 (W := W) Q u y h := by
    rw [hy]
    exact hrep y
  exact rp_coef 𝔭 hu' hQW hFree hy' hx

end GlobalTheory.CompanionTheory.FibGr
end
end
