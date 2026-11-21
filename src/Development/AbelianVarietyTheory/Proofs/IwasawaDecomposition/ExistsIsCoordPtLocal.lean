import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Ex.NumD

variable {O : Type} [CommRing O] (N : NumD O)

end GlobalTheory.Ex.NumD

namespace GlobalTheory.LocM.MultiPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Terms

variable {R : Type} [CommRing R] [IsDomain R] {C : Type} [Field C] [Algebra (FractionRing R) C] (A : ArcF D R C)

end Terms

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.LocM.MultiPt

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LocM.MultiPt
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.CoordReduce

open ReciprocityTheory.ChartRestriction.G.Out in

theorem exists_isCoordPt_local (h₁ : Laws) (h₂ : Laws2) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : PolAV B)
    {R : Type} [CommRing R] [IsLocalRing R] (s : Sp R ⟶ B) {k : ℕ} (hk : Odd k) (hu : IsUnit (k : R)) {J : Type}
    (x : J → (Over.mk s ⟶ P.A)) (hx : ∀ i, x i ^ k ^ 2 = 1) (z : Over.mk s ⟶ P.A) :
    ∃ w : J → R, IsCoordPt P k x z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i) := by
  have hG := h₁.globalFns
  have hL := P.isLB
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V, hV, b, hb⟩ := h₂.secBaseChangeAny B P 1 le_rfl (s (IsLocalRing.closedPoint R))
  obtain ⟨t, rfl⟩ : ∃ t : Sp R ⟶ (overRes (T := baseOver B) V).left, t ≫ (overRes (T := baseOver B) V).hom = s :=
    ⟨IsOpenImmersion.lift V.ι s (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open (s ⁻¹ᵁ V).isOpen hV),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th₀, hth₀⟩ := ThetaLocal.exists_generator _ hsp
  let T : Over B := baseAt t
  obtain ⟨th, hth⟩ := ThetaPtExist.exists_isGenSec_of_retract hL (𝟙 T) (𝟙 T) (Category.comp_id _) th₀ hth₀
  obtain ⟨α₀, hα₀⟩ := h₁.mulPull B P k
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) α₀ hα₀
    (snd T P.A).left (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _)
    ((k : ℤ) ^ 2) 1 α hα th
  have hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ := fun i => by
    obtain ⟨U, hU, θ, hθ⟩ := (sym B P (k ^ 2) hk.pow T (x i) (hx i)).1 (IsLocalRing.closedPoint R)
    obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
    let h : T ⟶ overRes (T := T) ⊤ := Over.homMk (Sp R).topIso.inv (by
      show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ _ = _
      rw [Scheme.toIso_inv_ι_assoc])
    have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB h hθ
    rw [← Category.assoc, hh, Category.id_comp] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩
  choose U hU using hU
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt)
    (lift_snd _ _) ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  obtain ⟨c, hc⟩ := Geo.Tor.exists_chart hL (z.left (IsLocalRing.closedPoint R))
  obtain ⟨τ, hτ⟩ := AbSquare.exists_gen_of_mem_chart hL (Y := T.left) (K := Fin 1) (fun _ => z.left)
    (fun _ => (k : ℤ) ^ 2) (fun _ => c) fun _ y =>
      ((IsLocalRing.specializes_closedPoint (R := R) y).map z.left.continuous).mem_open (P.L.U c).isOpen hc
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) z τ hτ
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (w i), hk, ?_, th, s₁, α, τ, U, s₂, hth, hα, hτ, hs₁,
    hU, hs₂, fun i => ?_⟩
  · have := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  · convert hw i using 1
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (w i)

open ReciprocityTheory.ChartRestriction.G.Out in

theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))


end GlobalTheory.CoordReduce
end
end
