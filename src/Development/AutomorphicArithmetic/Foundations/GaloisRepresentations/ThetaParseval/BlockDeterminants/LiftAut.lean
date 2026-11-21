import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.AutomorphicArithmetic.AdelicQuotients.WeilRepresentationSmoothVectors
import Development.AutomorphicArithmetic.AdelicQuotients.PolynomialDataStableFinitePlace
import Development.AutomorphicArithmetic.AdelicQuotients.PolynomialDataStableInfinitePlace
import Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftContinuous
import Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftLinear
import Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftEquivariant
import Development.AutomorphicArithmetic.AdelicQuotients.PolynomialDataFiniteKType

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

namespace UpperTheory.TP

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

open PositivityTheory.ThKEnd.Grp in

private theorem stab_of {m : ℕ} {Y : Spc F E m} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : UA σ Y.J →* Module.End ℂ V) (P : Submodule ℂ V)
    (hlev : ∀ Φ ∈ P, ∀ᶠ u in 𝓝 (1 : UA σ Y.J), (∀ w, (mat u).map (piInf (τ w)) = 1) → A u Φ = Φ)
    (hr : ∀ g ∈ UAt σ Y (evI F), ∀ Φ ∈ P, A g Φ ∈ P)
    (hl : ∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ P, A g Φ ∈ P) (g : UA σ Y.J) : ∀ Φ ∈ P, A g Φ ∈ P := by
  intro Φ hΦ
  have h1 : Tendsto (fun S : Finset (Pl F) => (piece (eps S) (eps_sq S) g)⁻¹ * g) atTop (𝓝 1) := by
    rw [← inv_mul_cancel g]
    exact (tendsto_piece g).inv.mul_const g
  obtain ⟨S, h2⟩ := (h1.eventually (hlev Φ hΦ)).exists
  have h4 : ∀ w, (mat ((piece (eps S) (eps_sq S) g)⁻¹ * g)).map (piInf (τ w)) = 1 := fun w => by
    rw [mat_mul, Matrix.map_mul, ← piInf_piece S g, ← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨l, l1, l2⟩ := piece_prod g S
  have e : g = piece (eps ∅) (eps_sq ∅) g * l.prod * ((piece (eps S) (eps_sq S) g)⁻¹ * g) := by
    rw [← l2, mul_inv_cancel_left]
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h2 h4]
  refine hr _ (piece_inf g) _ ?_
  clear e h2 h4 l2
  induction l with
  | nil => simpa using hΦ
  | cons x l ih =>
    obtain ⟨v, hv⟩ := l1 x List.mem_cons_self
    rw [List.prod_cons, map_mul, Module.End.mul_apply]
    exact hl v x hv _ (ih fun h hh => l1 h (List.mem_cons_of_mem _ hh))

variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}

private theorem levelX_sch {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (u, 1) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := UpperTheory.weil_representation_smooth_vectors F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add, h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]

private theorem polStab (T : Tools) (hp : IsPair B M χX χW om n 0 d 0) (x : UA σ X.J) (y : UA σ W.J) :
    ∀ Φ ∈ PolData B M, om (x, y) Φ ∈ PolData B M := by
  have hsch : ∀ Φ ∈ PolData B M, Φ ∈ schA F (Fin n × Fin d) := fun Φ h => PositivityTheory.ThKG.polData_le hp.good h
  have o1 : ∀ {m : ℕ} {v : Pl F} (Y : Spc F E m), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun Y => PositivityTheory.ThKH.Locrep.one_mem_UAt (σ := σ) Y _
  have o2 : ∀ {m : ℕ} (Y : Spc F E m), (1 : UA σ Y.J) ∈ UAt σ Y (evI F) := fun Y u _ => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]
  have e : ((x, y) : UA σ X.J × UA σ W.J) = (x, 1) * (1, y) := by simp
  intro Φ hΦ
  rw [e, map_mul, Module.End.mul_apply]
  refine stab_of B.emb (om.comp (MonoidHom.inl _ _)) _ (fun Φ h => levelX_sch hp (hsch Φ h))
    (fun g hg Φ h => UpperTheory.polynomial_data_stable_infinite_place F E σ B n d X W M χX χW om hp g hg 1 (o2 W) Φ h)
    (fun v g hg Φ h => UpperTheory.polynomial_data_stable_finite_place T F E σ B n d X W M χX χW om _ _ _ _ hp v g hg 1 (o1 W) Φ h) x _ ?_
  exact stab_of B.emb (om.comp (MonoidHom.inr _ _)) _
    (fun Φ h => PositivityTheory.ThKEnd.Grp.level_sch PositivityTheory.ThKEst.level hp (hsch Φ h))
    (fun g hg Φ h => UpperTheory.polynomial_data_stable_infinite_place F E σ B n d X W M χX χW om hp 1 (o2 X) g hg Φ h)
    (fun v g hg Φ h => UpperTheory.polynomial_data_stable_finite_place T F E σ B n d X W M χX χW om _ _ _ _ hp v 1 (o1 X) g hg Φ h) y _ hΦ

private theorem real_of_off {τ : ∀ w : InfinitePlace F, EmbOver E w} {g : UA σ W.J} (hg : g ∈ gOff σ W ∅) (w : InfinitePlace F) :
    (mat g).map (piInf (τ w)) = 1 := by
  have h : ∀ w, (mat g).map (compInf F E w) = 1 := by
    refine Subgroup.closure_induction (p := fun g _ => ∀ w, (mat g).map (compInf F E w) = 1) (fun x hx => hx.1) ?_ ?_ ?_ hg
    · intro w; exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro x y _ _ hx hy w
      rw [show mat (x * y) = mat x * mat y from rfl, Matrix.map_mul, hx, hy, one_mul]
    · intro x _ hx w
      have e : mat x⁻¹ * mat x = 1 := PositivityTheory.ThKEnd.Grp.mat_inv_mul x
      have := congrArg (fun A => A.map (compInf F E w)) e
      simp only [Matrix.map_mul, hx w, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
  have e : (mat g).map (piInf (τ w)) = ((mat g).map (compInf F E w)).map (infEmb (τ w)) := by ext i j; rfl
  rw [e, h, Matrix.map_one _ (map_zero _) (map_one _)]

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n}
  {W : Spc (maximalRealSubfield E) E d} {B : Base (maximalRealSubfield E) E} {M : Model (cj E) X W}
  {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}

end CM

end UpperTheory.TP

end
