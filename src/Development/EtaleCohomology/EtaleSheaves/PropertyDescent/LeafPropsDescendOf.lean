import Development.EtaleCohomology.EtaleSheaves.PropertyDescent

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafPropsDescendPf.BaseChange

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem toR_incl {R R' : Subalgebra k Ω} (hR : R ≤ R') : toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem cond {R R' : Subalgebra k Ω} (hR : R ≤ R') {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D}
    {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) : v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, toR_incl]; exact h.w

theorem sq {R R' : Subalgebra k Ω} (hR : R ≤ R') {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D}
    {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, toR_incl]; exact h



end LateralTheory.E.LeafPropsDescendPf.BaseChange

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafPropsDescendPf.Split

def LeafSpreadSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

end LateralTheory.E.LeafPropsDescendPf.Split

end
end
