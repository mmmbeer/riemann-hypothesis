import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterSymmR
import Formalism.FlagUnipotentLattices.KappaAssemblyOf
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SobLeafP
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem psi_real (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) :
    ∃ Λ : Ainf D.host.F →+ ℂ, Continuous Λ ∧ ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1) := by
  obtain ⟨⟨θ, hθ⟩, hall⟩ := hψ.2
  have hf := hall θ hθ
  let Λ : Ainf D.host.F →+ ℂ :=
    { toFun := fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := fun y y' => by simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]; ring }
  refine ⟨Λ, ?_, fun z hz => ?_⟩
  · show Continuous fun y => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E))
    exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
  · have hz' : z = pairA D.host.F z.1 0 := Prod.ext rfl hz
    rw [hz']
    exact hf z.1


end Formalism.IndefR.Eqv

end
end

section
namespace Formalism.IndefR.Eqv

open scoped ContDiff
open MeasureTheory

section Pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ev {k : ℕ} (j : Fin k) : Fin k → ℝ := Pi.single j 1

theorem norm_ev {k : ℕ} (j : Fin k) : ‖ev j‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : i = j
    · subst h; simp [ev]
    · simp [ev, h]
  · have := norm_le_pi_norm (ev j) j
    simpa [ev] using this

theorem natCast_lt_inf (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top m

end Pt

end Formalism.IndefR.Eqv
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}


def Gf (ψ : AddChar (AF D.host.F) ℂ) (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) :
    (Fin k → ℝ) → ℂ := fun t => heisO ψ S T (L t) f x

def Ff (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) : (Fin k → ℝ) → ℂ := fun t => f (x + L t)

def ellAdd (Λ : Ainf D.host.F →+ ℂ) (L : (Fin k → ℝ) →+ WO S T) (x : WO S T) : (Fin k → ℝ) →+ ℂ :=
  AddMonoidHom.mk' (fun t => Λ (symplOH S T x (L t)).1) (fun t t' => by
    simp only [map_add, symplOH_add_right]
    exact Λ.map_add _ _)

theorem continuous_ellAdd (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T)
    (hL : Continuous L) (x : WO S T) : Continuous (ellAdd Λ L x) := by
  have hs : Continuous fun t => symplOH S T x (L t) := (continuous_symplOH_right x).comp hL
  have h1 : Continuous fun t => Λ (symplOH S T x (L t)).1 := hΛ.comp (continuous_fst.comp hs)
  exact h1

def ellx (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) : (Fin k → ℝ) →L[ℝ] ℂ :=
  AddMonoidHom.toRealLinearMap (ellAdd Λ L x) (continuous_ellAdd Λ hΛ L hL x)

theorem ellx_apply (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) (t : Fin k → ℝ) : ellx Λ hΛ L hL x t = Λ (symplOH S T x (L t)).1 := rfl

section Bound

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in
theorem Gf_eq (f : WO S T → ℂ) (x : WO S T) :
    Gf ψ L f x = fun t => Complex.exp (ellx Λ hΛ L hL.1 x t) * Ff L f x t := by
  funext t
  have hr : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
  simp only [Gf, Ff, heisO, ellx_apply]
  rw [hψΛ _ (symplOH_snd x (L t) hr)]

include hΛ hψΛ hL in
theorem Gf_smooth {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) : ContDiff ℝ ∞ (Gf ψ L f x) := by
  rw [Gf_eq hΛ hψΛ hL]
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (ellx Λ hΛ L hL.1 x).contDiff).mul
    (hf.smooth k L hL.1 hL.2.1 x)

end Bound

end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_neg_mul (a : AF D.host.F) : ψ (-a) * ψ a = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]




end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem clm_sum {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (ℓ : (Fin k → ℝ) →L[ℝ] M) (s : Fin k → ℝ) :
    ℓ s = ∑ i, s i • ℓ (ev i) := by
  have : s = ∑ i, s i • ev i := by
    funext j; simp [ev, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  rw [map_sum]
  simp [map_smul]

section Real

variable (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)

include hΛ hL in

theorem beta_poly (s t : Fin k → ℝ) :
    Λ (symplOH S T (L s) (L t)).1 = ∑ i, ∑ j, s i * t j * Λ (symplOH S T (L (ev i)) (L (ev j))).1 := by

  have hs : ∀ t, Λ (symplOH S T (L s) (L t)).1 = ∑ i, s i * Λ (symplOH S T (L (ev i)) (L t)).1 := by
    intro t
    let g : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun s => Λ (symplOH S T (L s) (L t)).1) (fun a b => by
      simp only [map_add, symplOH_add_left]; exact Λ.map_add _ _)
    have hg : Continuous g := by
      have h1 : Continuous fun s => symplOH S T (L s) (L t) := (continuous_symplOH_left (L t)).comp hL
      exact hΛ.comp (continuous_fst.comp h1)
    have := clm_sum (AddMonoidHom.toRealLinearMap g hg) s
    simpa [g, smul_eq_mul] using this
  rw [hs t]
  refine Finset.sum_congr rfl fun i _ => ?_
  let g : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => Λ (symplOH S T (L (ev i)) (L t)).1) (fun a b => by
    simp only [map_add, symplOH_add_right]; exact Λ.map_add _ _)
  have hg : Continuous g := by
    have h1 : Continuous fun t => symplOH S T (L (ev i)) (L t) := (continuous_symplOH_right _).comp hL
    exact hΛ.comp (continuous_fst.comp h1)
  have := clm_sum (AddMonoidHom.toRealLinearMap g hg) t
  simp only [AddMonoidHom.coe_toRealLinearMap, g, AddMonoidHom.mk'_apply, smul_eq_mul] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.real_smul]
  ring

end Real

section RealCont

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in

theorem cont_real {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x0 : WO S T) {n : ℕ} (l : Fin n → Fin k) :
    Continuous fun s => dH ψ L l f (x0 + L s) := by
  set b : Fin k → Fin k → ℂ := fun i j => Λ (symplOH S T (L (ev i)) (L (ev j))).1
  set g0 : (Fin k → ℝ) → ℂ := fun r => f (x0 + L r)
  have hg0 : ContDiff ℝ ∞ g0 := hf.smooth k L hL.1 hL.2.1 x0
  set ℓ := ellx Λ hΛ L hL.1 x0
  set Φ : (Fin k → ℝ) × (Fin k → ℝ) → ℂ := fun p =>
    Complex.exp (ℓ p.2 + ∑ i, ∑ j, (p.1 i : ℂ) * (p.2 j : ℂ) * b i j) * g0 (p.1 + p.2)
  have hΦ : ContDiff ℝ ∞ Φ := by
    have h1 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin k → ℝ) => ℓ p.2 := ℓ.contDiff.comp contDiff_snd
    have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∑ i, ∑ j, (p.1 i : ℂ) * (p.2 j : ℂ) * b i j := by
      refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
      refine ContDiff.mul (ContDiff.mul ?_ ?_) contDiff_const
      · exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_fst)
      · exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (h1.add h2)).mul (hg0.comp (contDiff_fst.add contDiff_snd))
  have hGf : ∀ s, Gf ψ L f (x0 + L s) = fun t => Φ (s, t) := by
    intro s; funext t
    have hrs : eInf D • L s = L s := (wo_real_iff (L s)).mp (hL.2.1 s)
    have hrt : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
    simp only [Gf, heisO, Φ, g0]
    rw [symplOH_add_left]
    have h2 : (symplOH S T x0 (L t) + symplOH S T (L s) (L t)).2 = 0 := by
      show (symplOH S T x0 (L t)).2 + (symplOH S T (L s) (L t)).2 = 0
      rw [symplOH_snd _ _ hrt, symplOH_snd _ _ hrt, add_zero]
    rw [hψΛ _ h2, show (symplOH S T x0 (L t) + symplOH S T (L s) (L t)).1 =
      (symplOH S T x0 (L t)).1 + (symplOH S T (L s) (L t)).1 from rfl, map_add, beta_poly Λ hΛ L hL.1 s t,
      map_add, add_assoc]
    rfl
  have hval : ∀ s, dH ψ L l f (x0 + L s) = iteratedFDeriv ℝ n Φ (s, 0) (fun i => (0, ev (l i))) := by
    intro s
    have e : dH ψ L l f (x0 + L s) = iteratedFDeriv ℝ n (Gf ψ L f (x0 + L s)) 0 (fun i => ev (l i)) := rfl
    rw [e, hGf s]
    have hcomp : (fun t => Φ (s, t)) = (fun q => Φ (q + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ)) := by
      funext t; simp
    have hΦs : ContDiff ℝ ∞ (fun q => Φ (q + (s, 0))) := hΦ.comp (contDiff_id.add contDiff_const)
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ))
      hΦs 0 (natCast_lt_inf n).le, iteratedFDeriv_comp_add_right]
    simp
  simp_rw [hval]
  exact (ContinuousMultilinearMap.apply ℝ _ ℂ _).continuous.comp
    ((hΦ.continuous_iteratedFDeriv (natCast_lt_inf n).le).comp (continuous_id.prodMk continuous_const))

end RealCont

end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

instance instTAGWO : IsTopologicalAddGroup (WO S T) := PHeisFC.tagWA T S

theorem eFin_idem : eFin D * eFin D = eFin D :=
  Prod.ext (show (0 : Ainf D.host.F) * 0 = 0 from mul_zero _) (show (1 : Af D.host.F) * 1 = 1 from mul_one _)

theorem symplOH_zero_right (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := symplOH_add_right x (0 : WO S T) 0
  rw [add_zero] at h
  linear_combination -h



end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}


end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infMat_eq (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) (i j : Fin V.rank) :
    infMat D.sp.cm.sig V.gram (θ τ) g i j = θ τ (infPart D (mt V g i j)) := rfl

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_smul (c : AF D.host.F) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x := by
  unfold actO
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  simp [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (L2.Theta.mt T h)]
  unfold L2.Theta.mt
  simp


end Formalism.IndefR.Eqv

end
end
