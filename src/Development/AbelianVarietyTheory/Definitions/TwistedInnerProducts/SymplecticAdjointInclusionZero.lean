import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer.Check

variable {D : D7}

theorem sympl_left (S T : HSp D) (g : GA D T) (x y : WO S T) :
    symplOH S T (mt T g ⬝ x) (mt T g ⬝ y) = symplOH S T x y := by
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul, Matrix.mul_assoc, cancel₃ (mt_unitary T g)]

section Target

variable {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (n : GA D T) (β : Mx D ρ T₀.rank)
  (y : Mx D S.rank ρ)

def xiT : Mx D ρ S.rank := d.pX ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)

theorem splitT (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    mt T n⁻¹ ⬝ d.incAdj S y = d.incX S (xiT d n y) + d.inc0 S (ptT d S y n) + d.incAdj S y := by
  have h : d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y) = incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S) := by
    rw [cancel₂ h3, d.incAdj_apply, d.incY_apply, cancel₂ d.pY_jY, Matrix.one_mul]
  have h' : d.incAdj S y = d.jY ⬝ (d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)) := by rw [h]; rfl
  conv_rhs => rw [d.incX_apply, d.wittDecomp_inclAnisotropicHom_apply, xiT, ptT]; arg 2; rw [h']
  rw [← Matrix.mul_assoc d.jX, ← Matrix.mul_assoc d.j0, ← Matrix.mul_assoc d.jY, ← Matrix.add_mul, ← Matrix.add_mul,
    d.sum_eq_one, Matrix.one_mul]

theorem symplectic_adjoint_inclusion_zero (v : WO S T₀) : symplOH S T (d.incAdj S y) (d.inc0 S v) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ v

theorem cenT_eq (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    cenT d S y n = -symplOH S T (d.incX S (xiT d n y)) (d.incAdj S y) := by
  rw [cenT, splitT d n y h3, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, symplectic_adjoint_inclusion_zero,
    GlobalTheory.OrientedHeis.symplOH_self, add_zero, add_zero, symplOH_skew]

theorem moveT (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (w₀ : WO S T₀) :
    mt T n⁻¹ ⬝ d.inc0 S w₀ = d.inc0 S w₀ + d.incX S (β ⬝ w₀) := by
  rw [d.wittDecomp_inclAnisotropicHom_apply, d.incX_apply, cancel₂ h2, Matrix.add_mul, Matrix.mul_assoc]

theorem crossT (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) (w₀ : WO S T₀) :
    symplOH S T₀ w₀ (ptT d S y n) = -symplOH S T (d.incX S (β ⬝ w₀)) (d.incAdj S y) := by
  have h := sympl_left S T n⁻¹ (d.inc0 S w₀) (d.incAdj S y)
  have z : symplOH S T (d.inc0 S w₀) (d.incAdj S y) = 0 := by rw [symplOH_skew, symplectic_adjoint_inclusion_zero, neg_zero]
  have z' : symplOH S T (d.inc0 S w₀) (d.incX S (xiT d n y)) = 0 := by
    rw [symplOH_skew, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero]
  rw [splitT d n y h3, moveT d n β h2, z, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, z, z',
    d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, d.symplOH_incX_incX, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero, add_zero, zero_add] at h
  exact eq_neg_of_add_eq_zero_left h


end Target


section Source

variable {ψ : AddChar (AF D.host.F) ℂ} {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (n : GA D S) (β : Mx D S₀.rank ρ)
  (x : Mx D T.rank ρ)

def etaS : Mx D T.rank ρ := d.extX T x ⬝ mt S n ⬝ d.jY

theorem splitS (h1 : mt S n ⬝ d.jX = d.jX) :
    d.extX T x ⬝ mt S n = d.extY T (etaS d n x) + d.extX T x + d.ext0 T (ptS d T x n) := by
  refine d.mat_ext ?_ ?_ ?_
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, h1, d.pX_jX, d.pY_jX, d.p0_jX,
      Matrix.mul_zero, zero_add, add_zero]
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0,
      Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, ptS]
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY,
      Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, etaS]

theorem cenS_eq (h1 : mt S n ⬝ d.jX = d.jX) :
    cenS d T x n = -symplOH S T (d.extY T (etaS d n x)) (d.extX T x) := by
  rw [cenS, splitS d n x h1, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, d.wittDecomp_sympl_extIsotropic_extAnisotropic,
    GlobalTheory.OrientedHeis.symplOH_self, add_zero, add_zero, symplOH_skew]

theorem moveS (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (w₀ : WO S₀ T) :
    d.ext0 T w₀ ⬝ mt S n = d.ext0 T w₀ + d.extY T (w₀ ⬝ β) := by
  rw [d.matrixExtendByZero_apply, d.extY_apply, Matrix.mul_assoc, h2, Matrix.mul_add, Matrix.mul_assoc]



end Source

theorem om_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {g : GA D S} (hg : g ∈ GQ S) {h : GA D T} (hh : h ∈ GQ T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hpres : ∀ w, IsThetaFunO ψ S T (heisO ψ S T w f)) (w : WO S T) :
    om (g, h) f (actO S T g h w) = f w := by
  have h1 := congrFun (hom.om_heis g h w f hf) 0
  rw [hom.om_aut g hg h hh _ (hpres w)] at h1
  simpa only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add] using h1.symm





theorem UX_one (u : UX D 1) : u = 1 := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact ((mem_UX.1 u.2) 0 0).2


end GlobalTheory.MixPer.Check

end
