import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDualCrystal.Test

section Dual

variable {S : Scheme.{0}} {A B A₁ B₁ : Over S} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
  {P : LB (A ⊗ B).left} {P₁ : LB (A₁ ⊗ B₁).left}

theorem point_ext (h : IsDual A B P) {T : Over S} {x y : T ⟶ B}
    (e : evc h.isLB (fst A T) (snd A T ≫ x) = evc h.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB h.isLB _
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.additive _ _ _ _

theorem dual_unique {B' : Over S} [GrpObj B'] {P' : LB (A ⊗ B').left} (h : IsDual A B P) (h' : IsDual A B' P') :
    Nonempty (B ≅ B') := by
  have key : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (A ⊗ C).left} {Q' : LB (A ⊗ D).left}
      (q : IsDual A C Q) (q' : IsDual A D Q'), ∃ x : C ⟶ D, ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ C),
        evc q'.isLB a (b ≫ x) = evc q.isLB a b := by
    intro C D _ _ Q Q' q q'
    obtain ⟨x, hx, -⟩ := q'.univ C Q q.isLB q.additive
    refine ⟨x, fun Y a b ↦ ?_⟩
    have := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff q.isLB (pull_isLB q'.isLB _)).2 hx)
    rw [cls_ev q'.isLB, pull_evc] at this
    simpa [evc] using this.symm
  obtain ⟨x, hx⟩ := key h h'
  obtain ⟨y, hy⟩ := key h' h
  exact ⟨⟨x, y, point_ext h (by rw [← Category.assoc, hy, hx, Category.comp_id]),
    point_ext h' (by rw [← Category.assoc, hx, hy, Category.comp_id])⟩⟩





end Dual

section Crystal

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}

def baseThick (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Thick κ (spMap π) where
  B := R
  J := I
  δ := κ
  nil := hκ
  dp := (DPMorphism.id κ).isDPMorphism
  B₀ := R₀
  π := π
  surj := hπ
  ker b := by rw [← hI]; rfl
  x := 𝟙 _
  w := Category.id_comp _

end Crystal

end GlobalTheory.Published.AbelianDualCrystal.Test
