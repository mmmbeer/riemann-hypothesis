import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ComplexMetric

theorem ProjPointContinuous.proof : ProjPointContinuous.Statement.{u} := by
  intro A _ N ρ
  rw [continuous_iff_isClosed]
  intro Z hZ
  let Z' : Set (ProjectiveSpectrum (ProjSpace.grading A N)) := Z
  have hZ' : IsClosed Z' := hZ
  have e : Z' = ProjectiveSpectrum.zeroLocus _
      (ProjectiveSpectrum.vanishingIdeal Z' : Set (MvPolynomial (Fin (N + 1)) A)) := by
    rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ'.closure_eq]
  have hpre : (projPoint ρ : CP N → projectiveSpace A N) ⁻¹' Z =
      ⋂ d, ⋂ f ∈ {f | f ∈ ProjSpace.grading A N d ∧ f ∈ ProjectiveSpectrum.vanishingIdeal Z'},
        {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, and_imp]
    change projPoint ρ v ∈ Z' ↔ _
    conv_lhs => rw [e]
    change (ProjectiveSpectrum.vanishingIdeal Z' : Set (MvPolynomial (Fin (N + 1)) A)) ⊆
      (projPoint ρ v).asHomogeneousIdeal ↔ _
    constructor
    · intro h d f _ hf
      exact h hf
    · intro h
      exact ProjScheme.le_of_homogeneous _ _ h
  rw [hpre]
  exact isClosed_iInter fun d => isClosed_biInter fun f hf => isClosed_setOf_mem_projPoint ρ hf.1

end ComplexMetric

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ComplexMetric

theorem FractionContinuous.proof : FractionContinuous.Statement.{u} := by
  intro A _ N ρ d a b ha hb

  have hrep : ∀ (w : Fin (N + 1) → ℂ) (hw : w ≠ 0),
      ∃ c : ℂ, c ≠ 0 ∧ (Projectivization.mk ℂ w hw).rep = c • w := by
    intro w hw
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hw).1
      (Projectivization.mk_rep (Projectivization.mk ℂ w hw))
    exact ⟨c, c.ne_zero, hc.symm⟩

  have hSo : IsOpen {v : CP N | evalAt ρ v.rep b ≠ 0} := by
    have e : {v : CP N | evalAt ρ v.rep b ≠ 0} =
        {v : CP N | b ∈ (projPoint ρ v).asHomogeneousIdeal}ᶜ := by
      ext v
      exact (not_congr (mem_projPointOf ρ v.rep_nonzero hb)).symm
    rw [e]
    exact (isClosed_setOf_mem_projPoint ρ hb).isOpen_compl
  have hq : Topology.IsQuotientMap
      (Projectivization.mk' ℂ : {w : Fin (N + 1) → ℂ // w ≠ 0} → CP N) := by
    refine ⟨⟨rfl⟩, fun v => ?_⟩
    exact ⟨⟨v.rep, v.rep_nonzero⟩, Projectivization.mk_rep v⟩
  rw [hq.continuousOn_isOpen_iff hSo]

  have hval : ∀ w : {w : Fin (N + 1) → ℂ // w ≠ 0},
      evalAt ρ (Projectivization.mk' ℂ w).rep a / evalAt ρ (Projectivization.mk' ℂ w).rep b =
        evalAt ρ w.1 a / evalAt ρ w.1 b := by
    intro w
    obtain ⟨c, hc, e⟩ := hrep w.1 w.2
    change evalAt ρ (Projectivization.mk ℂ w.1 w.2).rep a /
      evalAt ρ (Projectivization.mk ℂ w.1 w.2).rep b = _
    rw [e, evalAt_smul ρ ha, evalAt_smul ρ hb]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hc)
  have hne : ∀ w : {w : Fin (N + 1) → ℂ // w ≠ 0},
      w ∈ (Projectivization.mk' ℂ) ⁻¹' {v : CP N | evalAt ρ v.rep b ≠ 0} →
        evalAt ρ w.1 b ≠ 0 := by
    intro w hw h0
    obtain ⟨c, _, e⟩ := hrep w.1 w.2
    apply hw
    change evalAt ρ (Projectivization.mk ℂ w.1 w.2).rep b = 0
    rw [e, evalAt_smul ρ hb, h0, mul_zero]
  have hfun : ((fun v : CP N => evalAt ρ v.rep a / evalAt ρ v.rep b) ∘
      Projectivization.mk' ℂ) = fun w => evalAt ρ w.1 a / evalAt ρ w.1 b := by
    funext w
    exact hval w
  rw [hfun]
  exact ContinuousOn.div ((continuous_evalAt ρ a).comp continuous_subtype_val).continuousOn
    ((continuous_evalAt ρ b).comp continuous_subtype_val).continuousOn hne

end ComplexMetric

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ComplexMetric.GermFraction.proof : ComplexMetric.GermFraction.Statement.{u} := by
  intro A _ N V g q hq
  obtain ⟨W, hqW, i, d, r, s, hs, hw⟩ := g.2 ⟨q, hq⟩
  refine ⟨W, hqW, i.le, d, r.1, s.1, r.2, s.2, fun y hy => hs ⟨y, hy⟩, ?_⟩
  intro ρ w y hy h
  have e1 : (Proj.stalkIso (ProjSpace.grading A N) y).hom.hom
      ((projectiveSpace A N).presheaf.germ V y (i.le hy) g) = g.1 ⟨y, i.le hy⟩ :=
    Proj.stalkIso'_germ _ V y (i.le hy) g
  rw [evalStalkProj, RingHom.comp_apply, e1]
  have e2 : g.1 ⟨y, i.le hy⟩ = _ := hw ⟨y, hy⟩
  rw [e2, evalAtPrime_mk]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

theorem ComplexMetric.LocalLift.proof : ComplexMetric.LocalLift.Statement.{u} := by
  intro A _ N X U f p hp
  obtain ⟨t, ht⟩ := X.ι.stalkMap_surjective p (germR hp f)
  obtain ⟨V, hpV, g, hg⟩ := (projectiveSpace A N).presheaf.exists_germ_eq t
  have h1 : X.X.presheaf.germ U p hp f =
      X.X.presheaf.germ (X.ι ⁻¹ᵁ V) p hpV (X.ι.app V g) := by
    rw [← Scheme.Hom.germ_stalkMap_apply, hg]
    exact ht.symm
  obtain ⟨W, hpW, iU, iV, he⟩ := X.X.presheaf.germ_eq p hp hpV _ _ h1
  refine ⟨V, g, W, hpW, iU.le, iV.le, fun p' hp' => ?_⟩
  have e1 := X.X.presheaf.germ_res_apply iU p' hp' f
  have e2 := X.X.presheaf.germ_res_apply iV p' hp' (X.ι.app V g)
  have e3 := Scheme.Hom.germ_stalkMap_apply X.ι V p' (iV.le hp') g
  exact e1.symm.trans ((congrArg (X.X.presheaf.germ W p' hp') he).trans (e2.trans e3.symm))

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ComplexMetric

lemma continuous_point_of (h₁ : ProjPointContinuous.Statement.{u}) {A : Type u} [CommRing A]
    {N : ℕ} (X : ProjScheme A N) (ρ : A →+* ℂ) : Continuous (X.point (ρ := ρ)) := by
  rw [X.ι.isClosedEmbedding.isInducing.continuous_iff]
  have e : (X.ι.base ∘ X.point (ρ := ρ)) = projPoint ρ ∘ Subtype.val := funext X.ι_point
  rw [e]
  exact (h₁ A N ρ).comp continuous_subtype_val

theorem RegularContinuous.proof (h₁ : ProjPointContinuous.Statement.{u})
    (h₂ : FractionContinuous.Statement.{u}) (h₃ : GermFraction.Statement.{u})
    (h₄ : LocalLift.Statement.{u}) : RegularContinuous.Statement.{u} := by
  intro A _ N X ρ U f
  have hpt := continuous_point_of h₁ X ρ
  rw [continuous_iff_continuousAt]
  rintro ⟨y₀, hy₀⟩
  obtain ⟨V, g, W, hpW, hWU, hWV, hlift⟩ := h₄ A N X U f (X.point y₀) hy₀
  obtain ⟨W', hqW', hW'V, d, a, b, ha, hb, hbW', hval⟩ :=
    h₃ A N V g (X.ι.base (X.point y₀)) (hWV hpW)
  let O : Set {x : X.complexPoints ρ // X.point x ∈ U} :=
    {y | X.point y.1 ∈ W ∧ X.ι.base (X.point y.1) ∈ W'}
  have hc1 : Continuous fun y : {x : X.complexPoints ρ // X.point x ∈ U} => X.point y.1 :=
    hpt.comp continuous_subtype_val
  have hO : IsOpen O :=
    (W.isOpen.preimage hc1).inter (W'.isOpen.preimage (X.ι.continuous.comp hc1))
  have hy₀O : (⟨y₀, hy₀⟩ : {x : X.complexPoints ρ // X.point x ∈ U}) ∈ O := ⟨hpW, hqW'⟩
  have key : ∀ y ∈ O, X.evalAtPoint y.1 (germR y.2 f) =
      evalAt ρ y.1.1.rep a / evalAt ρ y.1.1.rep b := by
    rintro ⟨y, hy⟩ ⟨h1, h2⟩
    have e := hlift (X.point y) h1
    rw [ProjScheme.evalAtPoint, e]
    exact (X.evalStalk_stalkMap (X.isOver_point y) _).trans (hval ρ y.1.rep _ h2 (X.isOver_point y))
  have hne : ∀ y ∈ O, evalAt ρ y.1.1.rep b ≠ 0 := fun y hy h0 =>
    hbW' _ hy.2 ((X.isOver_point y.1 d b hb).2 h0)
  have hg : Continuous fun y : {x : X.complexPoints ρ // X.point x ∈ U} => y.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc : ContinuousAt (fun y : {x : X.complexPoints ρ // X.point x ∈ U} =>
      evalAt ρ y.1.1.rep a / evalAt ρ y.1.1.rep b) ⟨y₀, hy₀⟩ := by
    refine ContinuousWithinAt.continuousAt (s := O) ?_ (hO.mem_nhds hy₀O)
    have hF := (h₂ A N ρ d a b ha hb).continuousWithinAt (hne _ hy₀O)
    exact ContinuousWithinAt.comp (f := fun y : {x : X.complexPoints ρ // X.point x ∈ U} => y.1.1)
      hF hg.continuousWithinAt fun y hy => hne y hy
  exact hc.congr (Filter.eventuallyEq_of_mem (hO.mem_nhds hy₀O) fun y hy => (key y hy).symm)

end ComplexMetric

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace ComplexMetric

theorem ProjPointContinuous.full : ProjPointContinuous.Statement.{u} :=
  ProjPointContinuous.proof

theorem FractionContinuous.full : FractionContinuous.Statement.{u} :=
  FractionContinuous.proof

theorem GermFraction.full : GermFraction.Statement.{u} :=
  GermFraction.proof

theorem LocalLift.full : LocalLift.Statement.{u} :=
  LocalLift.proof

theorem RegularContinuous.full : RegularContinuous.Statement.{u} :=
  RegularContinuous.proof ProjPointContinuous.full FractionContinuous.full GermFraction.full
    LocalLift.full

end ComplexMetric

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

def standardMetricOf (X : ProjScheme A N) : X.ContinuousMetric (𝟙_ X.X.Modules) :=
  X.standardMetric ComplexMetric.RegularContinuous.full

def standardMetricSelf (A : Type u) [CommRing A] (N : ℕ) :
    (ProjScheme.self A N).ContinuousMetric (𝟙_ (ProjScheme.self A N).X.Modules) :=
  (ProjScheme.self A N).standardMetricOf

example (x : (ProjScheme.self ℤ 1).complexPoints (Int.castRingHom ℂ))
    (s : (ProjScheme.self ℤ 1).Fibre (𝟙_ (ProjScheme.self ℤ 1).X.Modules) x) :
    (standardMetricSelf ℤ 1).norm _ x s = ‖(ProjScheme.self ℤ 1).unitFibreEquiv x s‖ := rfl

end ProjScheme

end

end GroundTheory.Heights₂.Heights
end
