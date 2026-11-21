import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareEqDiagOfQuadraticEven

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

theorem Hf_add_left (T : Tor D) (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem Hf_herm (T : Tor D) (x y : VC D N N') :
    Hf D T y x = starRingEnd ℂ (Hf D T x y) := by
  unfold Hf
  rw [map_div₀]
  congr 1
  · simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp


def cf (T : Tor D) (x y : VC D N N') : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)))

private theorem Hf_add_right_lemma (T : Tor D) (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  rw [Hf_herm T (y + y') x, Hf_add_left T y y' x, map_add, ← Hf_herm T y x, ← Hf_herm T y' x]

theorem U_U (T : Tor D) (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z = cf T x y * U D T (x + y) G z := by
  have hc : starRingEnd ℂ (Hf D T x y) = Hf D T x y - 2 * ((Hf D T x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  simp only [U, cf]
  rw [add_assoc z x y, Hf_add_left T z x y, Hf_add_right_lemma T z x y, Hf_add_left T x y (x + y),
    Hf_add_right_lemma T x x y, Hf_add_right_lemma T y x y, Hf_herm T x y, hc]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem U_smul (T : Tor D) (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => c * G w) z = c * U D T x G z := by
  simp only [U]
  ring

def SemiChar (T : Tor D) (La' : AddSubgroup (VC D N N')) : Prop :=
  ∀ x ∈ La', ∀ y ∈ La', al D T (x + y) = al D T x * al D T y * cf T x y

theorem fix_eq (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') {y : VC D N N'} (hy : y ∈ La') :
    (fun w => al D T y * U D T y G w) = G := by
  have hG' : Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, al D T x * U D T x G z = G z := hG
  funext w
  exact hG'.2 y hy w

theorem two_step (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') {y : VC D N N'} (hy : y ∈ La') (x z : VC D N N') :
    al D T x * U D T x G z = al D T x * al D T y * cf T x y * U D T (x + y) G z := by
  conv_lhs => rw [← fix_eq T hG hy]
  rw [U_smul T x (al D T y) (U D T y G) z, U_U T x y G z]
  ring

theorem rep_shift (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) {x y : VC D N N'} (hx : x ∈ La₂)
    (hy₁ : y ∈ La₁) (hy₂ : y ∈ La₂) (z : VC D N N') :
    al D T (x + y) * U D T (x + y) G z = al D T x * U D T x G z := by
  rw [hS x hx y hy₂]
  exact (two_step T hG hy₁ x z).symm

theorem term_indep (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) (a b : La₂)
    (hab : (a : La₂ ⧸ La₁.addSubgroupOf La₂) = (b : La₂ ⧸ La₁.addSubgroupOf La₂))
    (z : VC D N N') :
    al D T (b : VC D N N') * U D T (b : VC D N N') G z =
      al D T (a : VC D N N') * U D T (a : VC D N N') G z := by
  have h := (QuotientAddGroup.eq).mp hab
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have hb : (b : VC D N N') = (a : VC D N N') + ((-a + b : La₂) : VC D N N') := by
    push_cast
    abel
  rw [hb]
  exact rep_shift T hS hG a.2 h (-a + b).2 z

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

theorem Hf_diff (T : Tor D) (x : VC D N N') :
    Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  first
  | fun_prop
  | exact (Differentiable.sum fun τ _ => Differentiable.sum fun i _ => Differentiable.sum fun j _ =>
      ((differentiable_apply j).comp ((differentiable_apply i).comp
        (differentiable_apply τ))).mul_const _).div_const _

theorem U_diff (T : Tor D) (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U D T x G) := by
  have hU : U D T x G = fun z => G (z + x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) := by
    funext z
    rfl
  rw [hU]
  have hH := Hf_diff T x
  first
  | exact (hG.comp (differentiable_id.add_const x)).mul
      ((((differentiable_const _).mul hH).sub (differentiable_const _)).cexp)
  | fun_prop

theorem U_sum (T : Tor D) {Q : Type*} [Fintype Q] (x : VC D N N') (F : Q → VC D N N' → ℂ)
    (z : VC D N N') : U D T x (fun w => ∑ q, F q w) z = ∑ q, U D T x (F q) z := by
  simp only [U, Finset.sum_mul]

theorem Iop_mem_ThSp (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) : Iop D T La₁ La₂ G ∈ ThSp D T La₂ := by
  classical
  have hG' : Differentiable ℂ G ∧ ∀ x ∈ La₁, ∀ z, al D T x * U D T x G z = G z := hG
  show Differentiable ℂ (Iop D T La₁ La₂ G) ∧
    ∀ x ∈ La₂, ∀ z, al D T x * U D T x (Iop D T La₁ La₂ G) z = Iop D T La₁ La₂ G z
  by_cases hfin : Finite (La₂ ⧸ La₁.addSubgroupOf La₂)
  · haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
    have hfun : Iop D T La₁ La₂ G = fun w =>
        ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
          ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
            al D T ((Quotient.out q : La₂) : VC D N N') *
              U D T ((Quotient.out q : La₂) : VC D N N') G w := by
      funext w
      simp only [Iop, finsum_eq_sum_of_fintype]
    refine ⟨?_, ?_⟩
    · rw [hfun]
      have hd : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, Differentiable ℂ (fun w =>
          al D T ((Quotient.out q : La₂) : VC D N N') *
            U D T ((Quotient.out q : La₂) : VC D N N') G w) :=
        fun q => (U_diff T _ hG'.1).const_mul _
      first
      | exact (Differentiable.fun_sum fun q _ => hd q).const_mul _
      | fun_prop
      | exact (by simpa using (Differentiable.sum (u := Finset.univ) fun q _ => hd q)).const_mul _
    · intro x hx z
      have key : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
          al D T x * U D T x (fun w => al D T ((Quotient.out q : La₂) : VC D N N') *
            U D T ((Quotient.out q : La₂) : VC D N N') G w) z =
          al D T ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
              VC D N N') *
            U D T ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
              VC D N N') G z := by
        intro q
        rw [U_smul T x _ (U D T ((Quotient.out q : La₂) : VC D N N') G) z, U_U T x _ G z,
          ← mul_assoc, ← mul_assoc, ← hS x hx _ (Quotient.out q).2]
        have h1 : ((Quotient.out q : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) = q := Quotient.out_eq q
        have h2 : ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
            La₂ ⧸ La₁.addSubgroupOf La₂) = ((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q :=
          Quotient.out_eq _
        have hab : (((⟨x, hx⟩ : La₂) + Quotient.out q : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) =
            ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
              La₂ ⧸ La₁.addSubgroupOf La₂) := by
          rw [h2, QuotientAddGroup.mk_add, h1]
        exact (term_indep T hS hG _ _ hab z).symm
      simp only [hfun]
      rw [U_smul T x _ _ z, U_sum T x _ z, mul_left_comm (al D T x)]
      congr 1
      rw [Finset.mul_sum, Finset.sum_congr rfl fun q _ => key q]
      exact Fintype.sum_equiv
        (Equiv.addLeft (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂))) _ _
        (fun q => by first | rfl | simp only [Equiv.coe_addLeft])
  · haveI : Infinite (La₂ ⧸ La₁.addSubgroupOf La₂) := not_finite_iff_infinite.mp hfin
    have hidx : (La₁.addSubgroupOf La₂).index = 0 := by
      first
      | exact AddSubgroup.index_eq_zero_of_infinite
      | exact AddSubgroup.index_eq_zero_iff_infinite.mpr inferInstance
    have h0 : Iop D T La₁ La₂ G = fun _ => 0 := by
      funext z
      simp [Iop, hidx]
    rw [h0]
    refine ⟨differentiable_const _, fun x _ z => ?_⟩
    simp [U]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

theorem Iop_of_le (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hle : La₂ ≤ La₁)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) : Iop D T La₁ La₂ G = G := by
  classical
  have hG' : Differentiable ℂ G ∧ ∀ x ∈ La₁, ∀ z, al D T x * U D T x G z = G z := hG
  funext z
  have htop : La₁.addSubgroupOf La₂ = ⊤ := AddSubgroup.addSubgroupOf_eq_top.mpr hle
  have hidx : (La₁.addSubgroupOf La₂).index = 1 := by
    rw [htop, AddSubgroup.index_top]
  haveI hsub : Subsingleton (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
    rw [QuotientAddGroup.eq, htop]
    exact AddSubgroup.mem_top _
  haveI : Unique (La₂ ⧸ La₁.addSubgroupOf La₂) := uniqueOfSubsingleton 0
  have hterm : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G z =
        G z :=
    fun q => hG'.2 _ (hle (Quotient.out q).2) z
  simp only [Iop, hterm, finsum_unique]
  simp [hidx]

theorem IopIso_diag (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (G : VC D N N' → ℂ)
    (hG : G ∈ Th D T L L') :
    normSq D T (La D T L L') (Iop D T (La D T L L') (La D T L L') G) =
      normSq D T (La D T L L') G := by
  rw [Iop_of_le T le_rfl hG]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

def HfInt (T : Tor D) (La' : AddSubgroup (VC D N N')) : Prop :=
  ∀ x ∈ La', ∀ y ∈ La', ∃ a b : ℤ, Even (a - b) ∧
    Hf D T x y = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I

theorem sqrt_d_pos (D : Car) : 0 < Real.sqrt D.host.d := by
  first
  | exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.zero_lt_of_lt D.host.qd_big.2))
  | (apply Real.sqrt_pos.mpr; have h := D.host.qd_big.2; exact_mod_cast (by omega : 0 < D.host.d))

theorem Hf_add_right (T : Tor D) (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  rw [Hf_herm T (y + y') x, Hf_add_left T y y' x, map_add, ← Hf_herm T y x, ← Hf_herm T y' x]

theorem Hf_self_im (T : Tor D) (x : VC D N N') : (Hf D T x x).im = 0 := by
  have h := congrArg Complex.im (Hf_herm T x x)
  simp only [Complex.conj_im] at h
  linarith

theorem Hf_re_swap (T : Tor D) (x y : VC D N N') : (Hf D T y x).re = (Hf D T x y).re := by
  simpa using congrArg Complex.re (Hf_herm T x y)

theorem self_int (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : HfInt T La')
    {x : VC D N N'} (hx : x ∈ La') :
    ∃ m : ℤ, (Hf D T x x).re = 2 * m / Real.sqrt D.host.d ∧
      round (Real.sqrt D.host.d / 2 * (Hf D T x x).re) = m := by
  obtain ⟨a, b, hab, hH⟩ := hI x hx x hx
  have hb0 : b = 0 := by
    have h := congrArg Complex.im hH
    rw [Hf_self_im] at h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im] at h
    have h' : (b : ℝ) = 0 := by linarith
    exact_mod_cast h'
  obtain ⟨m, hm⟩ := hab
  have ha : a = 2 * m := by omega
  have haR : (a : ℝ) = 2 * (m : ℝ) := by exact_mod_cast ha
  have hre : (Hf D T x x).re = (a : ℝ) / Real.sqrt D.host.d := by
    rw [hH]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have hs : Real.sqrt D.host.d ≠ 0 := (sqrt_d_pos D).ne'
  refine ⟨m, ?_, ?_⟩
  · rw [hre, haR]
  · rw [hre, haR]
    have hm' : Real.sqrt D.host.d / 2 * (2 * (m : ℝ) / Real.sqrt D.host.d) =
        (m : ℝ) * (Real.sqrt D.host.d / Real.sqrt D.host.d) * (2 / 2) := by
      ring
    rw [hm', div_self hs, div_self (two_ne_zero : (2 : ℝ) ≠ 0), mul_one, mul_one, round_intCast]

theorem neg_one_zpow_congr {n m : ℤ} (h : Even (n - m)) : (-1 : ℂ) ^ n = (-1 : ℂ) ^ m := by
  have h0 : (-1 : ℂ) ≠ 0 := by norm_num
  calc (-1 : ℂ) ^ n = (-1 : ℂ) ^ ((n - m) + m) := by rw [sub_add_cancel]
    _ = (-1 : ℂ) ^ (n - m) * (-1 : ℂ) ^ m := zpow_add₀ h0 _ _
    _ = (-1 : ℂ) ^ m := by rw [Even.neg_one_zpow h, one_mul]

theorem cf_int (T : Tor D) (x y : VC D N N') (b : ℤ) (hb : (Hf D T x y).im = b) :
    cf T x y = (-1 : ℂ) ^ (-b) := by
  unfold cf
  rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem semiChar_of_HfInt (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : HfInt T La') :
    SemiChar T La' := by
  unfold SemiChar
  intro x hx y hy
  obtain ⟨mx, hmx, hrx⟩ := self_int T hI hx
  obtain ⟨my, hmy, hry⟩ := self_int T hI hy
  obtain ⟨a, b, hab, hxy⟩ := hI x hx y hy
  have hs : Real.sqrt D.host.d ≠ 0 := (sqrt_d_pos D).ne'
  have hre : (Hf D T x y).re = (a : ℝ) / Real.sqrt D.host.d := by
    rw [hxy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have him : (Hf D T x y).im = b := by
    rw [hxy]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have hsum : (Hf D T (x + y) (x + y)).re =
      (Hf D T x x).re + (Hf D T y y).re + 2 * (Hf D T x y).re := by
    rw [Hf_add_left T x y (x + y), Hf_add_right T x x y, Hf_add_right T y x y, Complex.add_re,
      Complex.add_re, Complex.add_re, Hf_re_swap T x y]
    ring
  have hr : round (Real.sqrt D.host.d / 2 * (Hf D T (x + y) (x + y)).re) = mx + my + a := by
    rw [hsum, hmx, hmy, hre]
    have h4 : Real.sqrt D.host.d / 2 * (2 * (mx : ℝ) / Real.sqrt D.host.d +
        2 * (my : ℝ) / Real.sqrt D.host.d + 2 * ((a : ℝ) / Real.sqrt D.host.d)) =
        ((mx : ℝ) + my + a) * (Real.sqrt D.host.d / Real.sqrt D.host.d) * (2 / 2) := by
      ring
    rw [h4, div_self hs, div_self (two_ne_zero : (2 : ℝ) ≠ 0), mul_one, mul_one]
    exact_mod_cast round_intCast (mx + my + a)
  unfold al
  rw [hr, hrx, hry, cf_int T x y b him,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  obtain ⟨k, hk⟩ := hab
  exact ⟨k + b, by omega⟩

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem finite_quot_of_smul {V : Type*} [AddCommGroup V] (La₁ La₂ R : AddSubgroup V)
    [Module.Finite ℤ R] (hle : La₂ ≤ R) (k : ℤ) (hk : k ≠ 0) (hkR : ∀ z ∈ R, k • z ∈ La₁) :
    Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
  classical
  haveI : IsNoetherian ℤ R := by
    first
    | exact isNoetherian_of_isNoetherianRing_of_finite ℤ R
    | infer_instance
  have hinj : Function.Injective (AddSubgroup.inclusion hle).toIntLinearMap := by
    intro a b h
    exact AddSubgroup.inclusion_injective hle h
  haveI : Module.Finite ℤ La₂ := Module.Finite.of_injective _ hinj
  haveI : Module.Finite ℤ (La₂ ⧸ La₁.addSubgroupOf La₂) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨k, mem_nonZeroDivisors_of_ne_zero hk⟩, ?_⟩
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  show k • (QuotientAddGroup.mk z : La₂ ⧸ La₁.addSubgroupOf La₂) = 0
  rw [show k • (QuotientAddGroup.mk z : La₂ ⧸ La₁.addSubgroupOf La₂) =
      QuotientAddGroup.mk (k • z) from
      (map_zsmul (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)) k z).symm]
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using hkR z (hle z.2)

variable {D : Car}

theorem Phi_smul_eq {N N' : ℕ} (δ : ℂ) (M : ℤ) (hM : M ≠ 0) (n : ℕ)
    (A : Fin N' → Fin N → 𝓞 D.host.E) :
    ((n : ℤ) * M) • FL.Phi D (N := N) (N' := N') (δ / M) A =
      ∑ i0 : Fin N', ∑ j0 : Fin N,
        FL.ins D i0 j0 (fun τ => δ * n * embT D τ ((A i0 j0 : 𝓞 D.host.E) : D.host.E)) := by
  funext τ i j
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  simp only [Finset.sum_apply]
  have h1 : ∀ i0 : Fin N', i0 ≠ i → (∑ j0 : Fin N, FL.ins D i0 j0
      (fun τ => δ * n * embT D τ ((A i0 j0 : 𝓞 D.host.E) : D.host.E)) τ i j) = 0 := by
    intro i0 hi0
    apply Finset.sum_eq_zero
    intro j0 _
    simp [FL.ins, Ne.symm hi0]
  have h2 : ∀ j0 : Fin N, j0 ≠ j → FL.ins D i j0
      (fun τ => δ * n * embT D τ ((A i j0 : 𝓞 D.host.E) : D.host.E)) τ i j = 0 := by
    intro j0 hj0
    simp [FL.ins, Ne.symm hj0]
  have h3 : FL.ins D i j (fun τ => δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) τ i j =
      δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E) := if_pos ⟨rfl, rfl⟩
  rw [Fintype.sum_eq_single i h1, Fintype.sum_eq_single j h2, h3]
  show ((n : ℤ) * M) • (δ / M * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) = _
  rw [zsmul_eq_mul]
  push_cast
  first
  | (rw [show ((n : ℂ) * (M : ℂ)) * (δ / (M : ℂ) * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) =
        δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E) * ((M : ℂ) / (M : ℂ)) by ring,
      div_self hM', mul_one])
  | (field_simp; ring)
  | field_simp

theorem La_index_finite (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) {N N' : ℕ}
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₁ : admitted D N N' L₁ L₁') (h₂ : admitted D N N' L₂ L₂') :
    Finite (La D (tor0 D cc δ) L₂ L₂' ⧸
      (La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')) := by
  obtain ⟨M, hM, hup⟩ := FL.La_upper D L₂ L₂' h₂ cc δ
  obtain ⟨n, hn, hlow⟩ := FL.La_lower D L₁ L₁' h₁ cc hcc δ
  haveI : Module.Finite ℤ (FL.Phi D (N := N) (N' := N') (δ / M)).range :=
    Module.Finite.of_surjective (FL.Phi D (N := N) (N' := N') (δ / M)).rangeRestrict.toIntLinearMap
      (AddMonoidHom.rangeRestrict_surjective _)
  refine finite_quot_of_smul _ _ _ hup ((n : ℤ) * M)
    (mul_ne_zero (by exact_mod_cast hn) hM) ?_
  rintro z ⟨A, rfl⟩
  rw [Phi_smul_eq δ M hM n A]
  exact AddSubgroup.sum_mem _ fun i0 _ => AddSubgroup.sum_mem _ fun j0 _ => hlow i0 j0 (A i0 j0)

theorem La_index_ne_zero (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) {N N' : ℕ}
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₁ : admitted D N N' L₁ L₁') (h₂ : admitted D N N' L₂ L₂') :
    ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')).index ≠ 0 := by
  haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂
  exact AddSubgroup.index_ne_zero_of_finite

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

def vol {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det}

theorem mulVec_col {N : ℕ} (A U : Matrix (Fin N) (Fin N) D.host.E) (j : Fin N) :
    A *ᵥ (fun i => U i j) = fun i => (A * U) i j := by
  funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem detId_mul_vol_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    detId D L L' * vol D L ≤ vol D L' := by
  unfold detId vol
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨A, hA, rfl⟩, _, ⟨U, hU, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨A * U, fun j => ?_, (det_mul A U).symm⟩
  rw [← mulVec_col]; exact hA _ (hU j)

theorem cS_span_le (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) ≤ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  intro x hx
  rw [CU.mem_cS] at hx
  have key : ∀ y ∈ Submodule.span (𝓞 D.host.E) S,
      D.host.conj y ∈ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a _ ha => rw [CU.conj_smul]; exact Submodule.smul_mem _ _ ha
  have := key _ hx
  rwa [CU.conj_conj] at this

theorem cS_cS (𝔞 : IdE D) : CU.cS D (CU.cS D 𝔞) = 𝔞 := by
  ext x; rw [CU.mem_cS, CU.mem_cS, CU.conj_conj]

theorem vol_mul_cS_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L' * CU.cS D (vol D L) ≤ detId D L L' := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol detId
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨V * Wᴴ, fun x hx => ?_, ?_⟩
  · have hc : ∀ i, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ *ᵥ x) i := by
      intro i
      obtain ⟨r, hr⟩ := hL x hx _ (hW i)
      refine ⟨r, hr.trans ?_⟩
      simp [stdH, Matrix.mulVec, dotProduct, conjTranspose_apply]
    choose r hr using hc
    have e : (V * Wᴴ) *ᵥ x = ∑ i, r i • (fun k => V k i) := by
      rw [← mulVec_mulVec]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i, mul_comm]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)
  · rw [det_mul, det_conjTranspose, CU.star_conj]

theorem vol_mul_cS_le_one {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L * CU.cS D (vol D L) ≤ 1 := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  have hc : ∀ i j, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ * V) i j := by
    intro i j
    obtain ⟨r, hr⟩ := hL _ (hV j) _ (hW i)
    refine ⟨r, hr.trans ?_⟩
    simp [stdH, Matrix.mul_apply, conjTranspose_apply]
  choose r hr using hc
  have e : Wᴴ * V = (Matrix.of r).map (algebraMap (𝓞 D.host.E) D.host.E) := by
    ext i j; simp [hr]
  show _ ∈ (1 : IdE D)
  rw [Submodule.mem_one, ← CU.star_conj, ← det_conjTranspose]
  refine ⟨(Matrix.of r).det, ?_⟩
  have h2 : algebraMap (𝓞 D.host.E) D.host.E (Matrix.of r).det = (Wᴴ * V).det := by
    rw [e, RingHom.map_det]; rfl
  rw [h2, det_mul]
  exact mul_comm _ _

theorem sd_int {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  fun x hx w hw => (hL.2.2 x).1 hx w hw

def UnitDisc (D : Car) : Prop :=
  let _ := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsSDLat D.host.E N L →
    1 ≤ vol D L * CU.cS D (vol D L)

theorem determinant_norm_one_of_unit_disc (hU : UnitDisc D) : DetIdealsKernelNormOne D := by
  let _ := D.host.cmStar
  intro N L L' _ hL hL'
  have e1 : vol D L * CU.cS D (vol D L) = 1 :=
    le_antisymm (vol_mul_cS_le_one D L (sd_int D hL)) (hU N L hL)
  have e2 : vol D L' * CU.cS D (vol D L') = 1 :=
    le_antisymm (vol_mul_cS_le_one D L' (sd_int D hL')) (hU N L' hL')
  have hA : detId D L L' = vol D L' * CU.cS D (vol D L) := by
    refine le_antisymm ?_ (vol_mul_cS_le D L L' (sd_int D hL))
    calc detId D L L' = detId D L L' * (vol D L * CU.cS D (vol D L)) := by rw [e1, mul_one]
      _ = detId D L L' * vol D L * CU.cS D (vol D L) := by rw [mul_assoc]
      _ ≤ vol D L' * CU.cS D (vol D L) :=
          mul_le_mul' (detId_mul_vol_le D L L') (le_refl _)
  rw [CU.normOne_ideal_iff_mul_conj, hA, CU.cS_mul, cS_cS]
  calc vol D L' * CU.cS D (vol D L) * (CU.cS D (vol D L') * vol D L)
      = (vol D L' * CU.cS D (vol D L')) * (vol D L * CU.cS D (vol D L)) := by ring
    _ = 1 := by rw [e1, e2, mul_one]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem adj_step {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (U : Matrix (Fin N) (Fin N) D.host.E) (hU : ∀ j, (fun i => U i j) ∈ L) (t : Fin N → D.host.E)
    (ht : ∀ i, ∀ b ∈ CU.cS D (vol D L), t i * b ∈ (1 : IdE D)) :
    D.host.conj U.det ^ (N - 1) * ∏ i, t i ∈ vol D L := by
  let _ := D.host.cmStar
  refine Submodule.subset_span ⟨(adjugate U)ᴴ * diagonal t, fun i => ?_, ?_⟩
  · refine (hL.2.2 _).2 fun x hx => ?_
    have hdet : (U.updateCol i x).det ∈ vol D L := by
      refine Submodule.subset_span ⟨U.updateCol i x, fun j => ?_, rfl⟩
      by_cases hj : j = i
      · subst hj; convert hx using 1; funext k; simp
      · convert hU j using 1; funext k; simp [hj]
    have hb : star (U.updateCol i x).det ∈ CU.cS D (vol D L) := by
      rw [CU.mem_cS, ← CU.star_conj, star_star]; exact hdet
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (ht i _ hb)
    refine ⟨r, hr.trans ?_⟩
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp only [stdH, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_diagonal,
      conjTranspose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [det_mul, det_diagonal, det_conjTranspose, det_adjugate, Fintype.card_fin, star_pow,
      CU.star_conj]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix nonZeroDivisors
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

open FractionalIdeal in

theorem spanPow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (S : Set K)
    (hIS : (I : Submodule R K) = Submodule.span R S) (k : ℕ) :
    (I : Submodule R K) ^ k ≤ Submodule.span R ((fun s => s ^ k) '' S) := by
  classical
  set Q := Submodule.span R ((fun s => s ^ k) '' S)
  have hQle : Q ≤ ((I ^ k : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [coe_pow, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact Submodule.pow_mem_pow _ (hIS ▸ Submodule.subset_span hs) k
  let Qf : FractionalIdeal R⁰ K := ⟨Q, isFractional_of_le hQle⟩
  have hQf : Qf ≤ I ^ k := hQle
  have hIk : I ^ k ≠ 0 := pow_ne_zero _ hI
  suffices h : I ^ k ≤ Qf by
    rw [← coe_pow]; exact h
  by_contra hne
  have hb : Qf * (I ^ k)⁻¹ ≤ 1 := by
    calc Qf * (I ^ k)⁻¹ ≤ I ^ k * (I ^ k)⁻¹ := mul_le_mul' hQf le_rfl
      _ = 1 := mul_inv_cancel₀ hIk
  obtain ⟨B, hB⟩ := le_one_iff_exists_coeIdeal.mp hb
  have hBtop : B ≠ ⊤ := by
    rintro rfl
    apply hne
    have h1 : Qf * (I ^ k)⁻¹ = 1 := by rw [← hB, coeIdeal_top]
    calc I ^ k = Qf * (I ^ k)⁻¹ * I ^ k := by rw [h1, one_mul]
      _ = Qf := by rw [mul_assoc, inv_mul_cancel₀ hIk, mul_one]
      _ ≤ Qf := le_rfl
  obtain ⟨P, hPmax, hBP⟩ := Ideal.exists_le_maximal B hBtop
  have := hPmax.isPrime
  have hstep : ∀ s ∈ S, s ∈ ((P : FractionalIdeal R⁰ K) * I) := by
    intro s hs
    have hsI : spanSingleton R⁰ s ≤ I := by
      rw [spanSingleton_le_iff_mem, ← mem_coe, hIS]; exact Submodule.subset_span hs
    have hc : spanSingleton R⁰ s * I⁻¹ ≤ 1 := by
      calc spanSingleton R⁰ s * I⁻¹ ≤ I * I⁻¹ := mul_le_mul' hsI le_rfl
        _ = 1 := mul_inv_cancel₀ hI
    obtain ⟨C, hC⟩ := le_one_iff_exists_coeIdeal.mp hc
    have hCk : C ^ k ≤ P := by
      rw [← coeIdeal_le_coeIdeal K, coeIdeal_pow, hC, mul_pow, spanSingleton_pow, inv_pow]
      calc spanSingleton R⁰ (s ^ k) * (I ^ k)⁻¹ ≤ Qf * (I ^ k)⁻¹ := by
            refine mul_le_mul' ?_ le_rfl
            rw [spanSingleton_le_iff_mem]
            exact Submodule.subset_span ⟨s, hs, rfl⟩
        _ = B := hB.symm
        _ ≤ P := (coeIdeal_le_coeIdeal K).mpr hBP
    have hCP : C ≤ P := Ideal.IsPrime.le_of_pow_le hCk
    have h2 : spanSingleton R⁰ s * I⁻¹ ≤ P := hC ▸ (coeIdeal_le_coeIdeal K).mpr hCP
    have h3 : spanSingleton R⁰ s ≤ (P : FractionalIdeal R⁰ K) * I := by
      calc spanSingleton R⁰ s = spanSingleton R⁰ s * I⁻¹ * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ P * I := mul_le_mul' h2 le_rfl
    exact spanSingleton_le_iff_mem.mp h3
  have hIP : I ≤ (P : FractionalIdeal R⁰ K) * I := by
    rw [← coe_le_coe, hIS, Submodule.span_le]
    intro s hs
    exact mem_coe.mpr (hstep s hs)
  have h1P : (1 : FractionalIdeal R⁰ K) ≤ P := by
    calc (1 : FractionalIdeal R⁰ K) = I * I⁻¹ := (mul_inv_cancel₀ hI).symm
      _ ≤ P * I * I⁻¹ := mul_le_mul' hIP le_rfl
      _ = P := by rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
  rw [← coeIdeal_top, coeIdeal_le_coeIdeal] at h1P
  exact hPmax.ne_top (top_le_iff.mp h1P)

variable (D : Car)

theorem cS_span (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) = Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  refine le_antisymm (cS_span_le D S) ?_
  rw [Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  rw [SetLike.mem_coe, CU.mem_cS, CU.conj_conj]
  exact Submodule.subset_span hs

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix nonZeroDivisors FractionalIdeal
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem unitDisc : UnitDisc D := by
  let _ := D.host.cmStar
  intro N L hL
  obtain ⟨m, hm0, hup, hlow⟩ := FL.sd_bounds D L hL
  set G : Set D.host.E := {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E,
    (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det} with hG
  have hvol : vol D L = Submodule.span (𝓞 D.host.E) G := rfl
  have hmE : (m : D.host.E) ≠ 0 := Int.cast_ne_zero.mpr hm0
  set c : D.host.E := ((m : D.host.E) ^ N)⁻¹ with hc
  have hcc : D.host.conj c = c := by simp [hc, map_inv₀, map_pow, map_intCast]
  have hmN : (m : D.host.E) ^ N ∈ G := by
    refine ⟨Matrix.diagonal (fun _ => (m : D.host.E)), fun j => ?_, by simp [det_diagonal]⟩
    have h1 := hlow (Pi.single j 1) (fun i => by
      by_cases h : i = j
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero)
    convert h1 using 1
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hGle : vol D L ≤ Submodule.span (𝓞 D.host.E) {c} := by
    rw [hvol, Submodule.span_le]
    rintro _ ⟨U, hU, rfl⟩
    have hint : ∀ i j, IsIntegral ℤ ((m : D.host.E) * U i j) := fun i j => hup _ (hU j) i
    let M' : Matrix (Fin N) (Fin N) (𝓞 D.host.E) := Matrix.of fun i j => ⟨_, hint i j⟩
    have e : M'.map (algebraMap (𝓞 D.host.E) D.host.E) = (m : D.host.E) • U := by
      ext i j; rfl
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨M'.det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det]
    change (M'.map (algebraMap _ _)).det * c = U.det
    rw [e, det_smul, Fintype.card_fin, hc, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hmE), one_mul]
  have hMle : CU.cS D (vol D L) ≤ Submodule.span (𝓞 D.host.E) {c} := by
    intro x hx
    rw [CU.mem_cS] at hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hGle hx)
    refine Submodule.mem_span_singleton.mpr ⟨CU.conjO D a, ?_⟩
    have h2 := congrArg D.host.conj ha
    rwa [CU.conj_smul, hcc, CU.conj_conj] at h2
  let Lf : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
    ⟨vol D L, isFractional_of_le (J := spanSingleton _ c) (by rw [coe_spanSingleton]; exact hGle)⟩
  let Mf : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
    ⟨CU.cS D (vol D L), isFractional_of_le (J := spanSingleton _ c)
      (by rw [coe_spanSingleton]; exact hMle)⟩
  have hmL : (m : D.host.E) ^ N ∈ vol D L := Submodule.subset_span hmN
  have hmM : (m : D.host.E) ^ N ∈ CU.cS D (vol D L) := by
    rw [CU.mem_cS, map_pow, map_intCast]; exact hmL
  have hMf0 : Mf ≠ 0 := by
    intro h
    have h1 : (m : D.host.E) ^ N ∈ (Mf : Submodule (𝓞 D.host.E) D.host.E) := hmM
    rw [h, coe_zero, Submodule.mem_bot] at h1
    exact pow_ne_zero _ hmE h1
  have hMS : (Mf : Submodule (𝓞 D.host.E) D.host.E) = Submodule.span _ (D.host.conj '' G) :=
    cS_span D G
  have key : (Mf : Submodule (𝓞 D.host.E) D.host.E) ^ (N - 1) *
      ((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ N ≤
        vol D L := by
    refine (mul_le_mul' (spanPow Mf hMf0 _ hMS (N - 1)) le_rfl).trans ?_
    have hp : ((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ N =
        ∏ _i : Fin N, Submodule.span (𝓞 D.host.E)
          (((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) :
            Set D.host.E) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Submodule.span_eq]
    rw [hp, Submodule.prod_span, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨_, ⟨_, ⟨U, hU, rfl⟩, rfl⟩, rfl⟩, b, hb, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).mp hb
    refine adj_step D L hL U hU g fun i y hy => ?_
    have h1 := (mem_inv_iff hMf0).mp (hg i) y hy
    rwa [← mem_coe, coe_one] at h1
  have key' : Mf ^ (N - 1) * Mf⁻¹ ^ N ≤ Lf := by
    rw [← coe_le_coe, coe_mul, coe_pow, coe_pow]; exact key
  have hfin : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Lf * Mf := by
    rcases N with _ | n
    · have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Lf := by
        simpa using key'
      have h2 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Mf := by
        rw [FractionalIdeal.one_le, ← mem_coe]
        have h5 : (1 : D.host.E) ∈ CU.cS D (vol D L) := by simpa using hmM
        exact h5
      calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 1 * 1 := (one_mul 1).symm
        _ ≤ Lf * Mf := mul_le_mul' h1 h2
    · have h3 : Mf ^ (n + 1 - 1) * Mf⁻¹ ^ (n + 1) = Mf⁻¹ := by
        rw [Nat.add_sub_cancel, inv_pow, pow_succ, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hMf0), one_mul]
      rw [h3] at key'
      calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = Mf⁻¹ * Mf := (inv_mul_cancel₀ hMf0).symm
        _ ≤ Lf * Mf := mul_le_mul' key' le_rfl
  have h4 := coe_le_coe.mpr hfin
  rw [coe_one, coe_mul] at h4
  exact h4

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem relative_determinant_norm_one (D : Car) : DetIdealsKernelNormOne D :=
  DN.determinant_norm_one_of_unit_disc D (DN.unitDisc D)

theorem character_unit_on_determinant (D : Car) (χ : IdE D → ℂ) (hχ : IsChi D χ) : ChiUnitDet D χ :=
  chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ


end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise ENNReal Function

variable {D : Car} {N N' : ℕ}

def unionFd (M La : AddSubgroup (VC D N N')) (s : Set (VC D N N')) : Set (VC D N N') :=
  ⋃ q : La ⧸ M.addSubgroupOf La, (Quotient.out q : La) +ᵥ s

theorem out_mem (M La : AddSubgroup (VC D N N')) (g : La) :
    (((g + Quotient.out (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La) : La)) : VC D N N') ∈ M := by
  have h : (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La) =
      QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La)) :=
    (Quotient.out_eq _).symm
  rw [QuotientAddGroup.eq, neg_neg] at h
  exact AddSubgroup.mem_addSubgroupOf.mp h

theorem out_inj (M La : AddSubgroup (VC D N N')) {q q' : La ⧸ M.addSubgroupOf La}
    (h : (Quotient.out q : La) = Quotient.out q') : q = q' := by
  exact Quotient.out_injective h

theorem mem_vadd_iff {La : AddSubgroup (VC D N N')} (g : La) (s : Set (VC D N N')) (x : VC D N N') :
    x ∈ g +ᵥ s ↔ x - (g : VC D N N') ∈ s := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]
  rfl

theorem unionFd_fd {M La : AddSubgroup (VC D N N')} (hle : M ≤ La)
    [Finite (La ⧸ M.addSubgroupOf La)] {s : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) :
    IsAddFundamentalDomain M (unionFd M La s) volume where
  nullMeasurableSet := NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_vadd _
  ae_covers := by
    filter_upwards [hs.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    refine ⟨⟨_, out_mem M La g⟩, Set.mem_iUnion.2 ⟨QuotientAddGroup.mk (-g), ?_⟩⟩
    rw [mem_vadd_iff]
    convert hg using 1
    simp only [AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
    abel
  aedisjoint := by
    intro a b hab
    change volume ((a +ᵥ unionFd M La s) ∩ (b +ᵥ unionFd M La s)) = 0
    let a' : La := ⟨a, hle a.2⟩
    let b' : La := ⟨b, hle b.2⟩
    have hsub : (a +ᵥ unionFd M La s) ∩ (b +ᵥ unionFd M La s) ⊆
        ⋃ q : La ⧸ M.addSubgroupOf La, ⋃ q' : La ⧸ M.addSubgroupOf La,
          ((a' + Quotient.out q) +ᵥ s) ∩ ((b' + Quotient.out q') +ᵥ s) := by
      rintro x ⟨hxa, hxb⟩
      obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.1 hxa
      obtain ⟨u', hu', hu'e⟩ := Set.mem_vadd_set.1 hxb
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hu
      obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 hu'
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨q', ⟨?_, ?_⟩⟩⟩
      · rw [mem_vadd_iff] at hq ⊢
        convert hq using 1
        simp only [a', AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
        abel
      · rw [mem_vadd_iff] at hq' ⊢
        convert hq' using 1
        rw [← hu'e]
        simp only [b', AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
        abel
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun q' => ?_)
    by_cases he : a' + Quotient.out q = b' + Quotient.out q'
    · exfalso
      have h2 := congrArg (fun z : La => (z : VC D N N')) he
      simp only [a', b', AddSubgroup.coe_add] at h2
      have hqq : q = q' := by
        rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf]
        have : ((-Quotient.out q + Quotient.out q' : La) : VC D N N') = (a : VC D N N') - b := by
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
          rw [eq_sub_iff_add_eq]
          rw [← sub_eq_zero] at h2 ⊢
          rw [← neg_eq_zero, ← h2]
          abel
        rw [this]
        exact M.sub_mem a.2 b.2
      subst hqq
      apply hab
      simp only [add_left_inj] at h2
      exact Subtype.ext h2
    · exact hs.aedisjoint he

theorem pieces_disj {M La : AddSubgroup (VC D N N')} {s : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) :
    Pairwise (AEDisjoint volume on fun q : La ⧸ M.addSubgroupOf La => (Quotient.out q : La) +ᵥ s) := by
  intro q q' hqq'
  exact hs.aedisjoint (fun h => hqq' (out_inj M La h))

theorem lint_unionFd {M La : AddSubgroup (VC D N N')} [Countable La]
    [Fintype (La ⧸ M.addSubgroupOf La)]
    {s : Set (VC D N N')} (hs : IsAddFundamentalDomain La s volume) (f : VC D N N' → ℝ≥0∞)
    (hf : ∀ g : La, ∀ x, f (g +ᵥ x) = f x) :
    ∫⁻ x in unionFd M La s, f x =
      (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * ∫⁻ x in s, f x := by
  unfold unionFd
  rw [MeasureTheory.lintegral_iUnion₀ (fun q => hs.nullMeasurableSet.vadd _) (pieces_disj hs)]
  have h1 : ∀ q : La ⧸ M.addSubgroupOf La,
      ∫⁻ x in (Quotient.out q : La) +ᵥ s, f x = ∫⁻ x in s, f x :=
    fun q => (hs.vadd _).setLIntegral_eq hs f hf
  simp only [h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem vol_unionFd {M La : AddSubgroup (VC D N N')} [Countable La]
    [Fintype (La ⧸ M.addSubgroupOf La)]
    {s : Set (VC D N N')} (hs : IsAddFundamentalDomain La s volume) :
    volume (unionFd M La s) = (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * volume s := by
  unfold unionFd
  rw [MeasureTheory.measure_iUnion₀ (pieces_disj hs) (fun q => hs.nullMeasurableSet.vadd _)]
  simp only [MeasureTheory.measure_vadd, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem avg_sub {M La : AddSubgroup (VC D N N')} [Countable La] [Countable M] (hle : M ≤ La)
    [Finite (La ⧸ M.addSubgroupOf La)] {s t : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) (ht : IsAddFundamentalDomain M t volume)
    (f : VC D N N' → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hper : ∀ g ∈ La, ∀ x, f (x + g) = f x) :
    ⨍ x in t, f x = ⨍ x in s, f x := by
  haveI := Fintype.ofFinite (La ⧸ M.addSubgroupOf La)
  have hu := unionFd_fd hle hs
  have hperM : ∀ (g : M) (x : VC D N N'), f (g +ᵥ x) = f x := fun g x => by
    show f ((g : VC D N N') + x) = f x
    rw [add_comm]
    exact hper _ (hle g.2) x
  have hperL : ∀ (g : La) (x : VC D N N'), ENNReal.ofReal (f (g +ᵥ x)) = ENNReal.ofReal (f x) :=
    fun g x => by
      show ENNReal.ofReal (f ((g : VC D N N') + x)) = ENNReal.ofReal (f x)
      rw [add_comm, hper _ g.2 x]
  have hvol : volume t = volume (unionFd M La s) := ht.measure_eq hu
  have hint : ∫ x in t, f x = ∫ x in unionFd M La s, f x := ht.setIntegral_eq hu hperM
  have hlin : ∫⁻ x in unionFd M La s, ENNReal.ofReal (f x) =
      (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * ∫⁻ x in s, ENNReal.ofReal (f x) :=
    lint_unionFd hs _ hperL
  have hI : ∀ u : Set (VC D N N'), ∫ x in u, f x = (∫⁻ x in u, ENNReal.ofReal (f x)).toReal :=
    fun u => MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hfc.aestronglyMeasurable
  have hn : (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def, hvol, vol_unionFd hs, hint, hI, hlin, hI,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, smul_eq_mul, smul_eq_mul, mul_inv,
    show ∀ a b c : ℝ, a⁻¹ * b * (a * c) = (a⁻¹ * a) * b * c from fun a b c => by ring,
    inv_mul_cancel₀ hn, one_mul]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise ENNReal Function

variable {D : Car} {N N' : ℕ}

def crD (T : Tor D) (A B : VC D N N' → ℂ) (z : VC D N N') : ℂ :=
  A z * starRingEnd ℂ (B z) * (Real.exp (-Real.pi * (Hf D T z z).re) : ℂ)

private theorem Hf_swap_eq_conj (T : Tor D) (x y : VC D N N') :
    Hf D T y x = starRingEnd ℂ (Hf D T x y) := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  rw [map_div₀, Complex.conj_ofReal]
  congr 1
  simp only [map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem re_Hf_add' (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re =
      (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  have hadd : Hf D T (z + x) (z + x) = Hf D T z z + Hf D T z x + Hf D T x z + Hf D T x x := by
    unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
    simp only [Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  rw [hadd, Hf_swap_eq_conj T z x]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem exp_mul_conj (w : ℂ) :
    Complex.exp w * starRingEnd ℂ (Complex.exp w) = ((Real.exp (2 * w.re) : ℝ) : ℂ) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.add_conj, Complex.ofReal_exp]

theorem crD_U (T : Tor D) (A B : VC D N N' → ℂ) (y z : VC D N N') :
    crD T (U D T y A) (U D T y B) z = crD T A B (z + y) := by
  simp only [crD, Formalism.L2.Ker.Cd.TaylorLogMetric.U]
  rw [re_Hf_add' T z y]
  set e : ℂ := -(Real.pi : ℂ) * Hf D T z y - (Real.pi : ℂ) * Hf D T y y / 2 with he
  have h := exp_mul_conj e
  have hre : 2 * e.re = -Real.pi * (2 * (Hf D T z y).re + (Hf D T y y).re) := by
    rw [he]
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.neg_im]
    ring
  calc A (z + y) * Complex.exp e * starRingEnd ℂ (B (z + y) * Complex.exp e) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ)
      = A (z + y) * starRingEnd ℂ (B (z + y)) * (Complex.exp e * starRingEnd ℂ (Complex.exp e)) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ) := by rw [map_mul]; ring
    _ = _ := by
      rw [h, hre, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring

theorem crD_smul (T : Tor D) (c c' : ℂ) (A B : VC D N N' → ℂ) (z : VC D N N') :
    crD T (fun w => c * A w) (fun w => c' * B w) z = c * starRingEnd ℂ c' * crD T A B z := by
  unfold crD
  simp only [map_mul]
  ring

def ep (T : Tor D) (x y : VC D N N') : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))

private theorem Hf_add_leftColumnData (T : Tor D) (z y x : VC D N N') :
    Hf D T (z + y) x = Hf D T z x + Hf D T y x := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem mul_exp_mul_exp_eq_of_add_eq (g a b c d e : ℂ) (h : a + b = c + (d + e)) :
    g * Complex.exp a * Complex.exp b = Complex.exp c * (g * Complex.exp d * Complex.exp e) := by
  rw [mul_assoc g, ← Complex.exp_add, h, Complex.exp_add, Complex.exp_add]
  ring

theorem aU_eig (T : Tor D) {La₁ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) {y : VC D N N'} (hy : y ∈ La₁) (x z : VC D N N') :
    al D T y * U D T y (U D T x G) z = ep T x y * U D T x G z := by
  have key : ∀ w, al D T y * U D T y G w = G w := fun w => hG.2 y hy w
  have hc : starRingEnd ℂ (Hf D T x y) = Hf D T x y - 2 * (((Hf D T x y).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have hcomm : U D T y (U D T x G) z = ep T x y * U D T x (U D T y G) z := by
    simp only [Formalism.L2.Ker.Cd.TaylorLogMetric.U, ep]
    rw [Hf_add_leftColumnData, Hf_add_leftColumnData, Hf_swap_eq_conj T x y, hc, show z + y + x = z + x + y by abel]
    apply mul_exp_mul_exp_eq_of_add_eq
    ring
  calc al D T y * U D T y (U D T x G) z
      = ep T x y * ((al D T y * U D T y G (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2)) := by
        rw [hcomm]
        simp only [Formalism.L2.Ker.Cd.TaylorLogMetric.U]
        ring
    _ = ep T x y * U D T x G z := by rw [key]; rfl

def trm (T : Tor D) (G : VC D N N' → ℂ) (x : VC D N N') : VC D N N' → ℂ :=
  fun z => al D T x * U D T x G z

theorem al_mul_conj (T : Tor D) (y : VC D N N') : al D T y * starRingEnd ℂ (al D T y) = 1 := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.al
  rw [map_zpow₀, map_neg, map_one, ← mul_zpow]
  norm_num

theorem crD_shift (T : Tor D) {La₁ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) {y : VC D N N'} (hy : y ∈ La₁) (x x' z : VC D N N') :
    crD T (trm T G x) (trm T G x') (z + y) =
      ep T x y * starRingEnd ℂ (ep T x' y) * crD T (trm T G x) (trm T G x') z := by
  have hUt : ∀ x₀, U D T y (trm T G x₀) =
      fun w => (starRingEnd ℂ (al D T y) * ep T x₀ y) * trm T G x₀ w := by
    intro x₀
    funext w
    have h1 := aU_eig T hG hy x₀ w
    have h2 := al_mul_conj T y
    have hlin : U D T y (trm T G x₀) w = al D T x₀ * U D T y (U D T x₀ G) w := by
      simp only [Formalism.L2.Ker.Cd.TaylorLogMetric.U, trm]
      ring
    rw [hlin]
    simp only [trm]
    linear_combination (al D T x₀ * starRingEnd ℂ (al D T y)) * h1 -
      (al D T x₀ * U D T y (U D T x₀ G) w) * h2
  rw [← crD_U T (trm T G x) (trm T G x') y z, hUt x, hUt x',
    crD_smul T (starRingEnd ℂ (al D T y) * ep T x y) (starRingEnd ℂ (al D T y) * ep T x' y)
      (trm T G x) (trm T G x') z, map_mul, Complex.conj_conj]
  have h2 := al_mul_conj T y
  linear_combination (ep T x y * starRingEnd ℂ (ep T x' y) * crD T (trm T G x) (trm T G x') z) * h2

private theorem Hf_sub_left' (T : Tor D) (x x' y : VC D N N') :
    Hf D T (x - x') y = Hf D T x y - Hf D T x' y := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  rw [← sub_div]
  congr 1
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ep_mul_conj (T : Tor D) (x x' y : VC D N N') :
    ep T x y * starRingEnd ℂ (ep T x' y) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Hf D T (x - x') y).im : ℂ)) := by
  unfold ep
  rw [← Complex.exp_conj, ← Complex.exp_add, Hf_sub_left' T x x' y, Complex.sub_im]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem ep_eq_one_iff (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : (t : ℂ) = n := by
      apply mul_left_cancel₀ h2
      rw [hn]
      ring
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem int_shift {M : AddSubgroup (VC D N N')} [Countable M] {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) (x : VC D N N') :
    ∫ z in t, f (z + x) = ∫ z in t, f z := by
  have hmp := MeasureTheory.measurePreserving_add_right
    (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')) x
  have ht' : IsAddFundamentalDomain M ((fun z => z + x) ⁻¹' t) volume :=
    ht.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id
      (fun g z => add_assoc (g : VC D N N') z x)
  calc ∫ z in t, f (z + x) = ∫ z in (fun z => z + x) ⁻¹' t, f (z + x) := by
        refine ht.setIntegral_eq ht' (fun g z => ?_)
        show f ((g : VC D N N') + z + x) = f (z + x)
        rw [show (g : VC D N N') + z + x = z + x + g by abel, hper _ g.2]
    _ = ∫ z in t, f z := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight x) f t

theorem int_zero_of_char {M : AddSubgroup (VC D N N')} [Countable M] {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) (y : VC D N N') (lam : ℂ) (hlam : lam ≠ 1)
    (hy : ∀ z, f (z + y) = lam * f z) :
    ∫ z in t, f z = 0 := by
  have h := int_shift ht f hper y
  simp_rw [hy] at h
  rw [MeasureTheory.integral_const_mul] at h
  have h2 : (lam - 1) * ∫ z in t, f z = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hlam)

theorem intOn_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ) (hf : Continuous f)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) : IntegrableOn f t volume := by
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  haveI : DiscreteTopology L := hM.1
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hM.2⟩
  haveI : Countable M := by
    haveI := hM.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hb : Submodule.span ℤ (Set.range b) = L := Module.Basis.ofZLatticeBasis_span ℝ L _
  have hs0 : IsAddFundamentalDomain M (ZSpan.fundamentalDomain b) volume := by
    have h := ZSpan.isAddFundamentalDomain b (MeasureTheory.volume : MeasureTheory.Measure (VC D N N'))
    rw [hb] at h
    exact h
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hf.continuousOn
  have hbd : ∀ z, ‖f z‖ ≤ C := by
    intro z
    obtain ⟨m, hm, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b z
    have hmM : (m : VC D N N') ∈ M := hb.le m.2
    have h3 := hC _ (subset_closure hm)
    rwa [show m +ᵥ z = z + (m : VC D N N') from add_comm _ _, hper _ hmM] at h3
  have hfin : volume t ≠ ⊤ := by
    rw [ht.measure_eq hs0]
    exact ((ZSpan.fundamentalDomain_isBounded b).measure_lt_top).ne
  exact MeasureTheory.Measure.integrableOn_of_bounded (M := C) hfin hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbd)

theorem countable_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) : Countable M := by
  haveI := hM.1
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem fd_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) :
    ∃ t : Set (VC D N N'), IsAddFundamentalDomain M t volume := by
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  haveI : DiscreteTopology L := hM.1
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hM.2⟩
  let b := Module.Free.chooseBasis ℤ L
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L), ?_⟩
  have h := ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis ℝ L)
    (MeasureTheory.volume : MeasureTheory.Measure (VC D N N'))
  rw [Module.Basis.ofZLatticeBasis_span] at h
  exact h

theorem full_inf {La₁ La₂ : AddSubgroup (VC D N N')} (h₁ : FullLat La₁) (h₂ : FullLat La₂)
    [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)] : FullLat (La₁ ⊓ La₂) := by
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (La₁ : Set (VC D N N')) := h₁.1
    exact DiscreteTopology.of_subset this (fun v hv => (AddSubgroup.mem_inf.mp hv).1)
  · rw [eq_top_iff, ← h₂.2, Submodule.span_le]
    intro v hv
    have hn : (La₁.addSubgroupOf La₂).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    have hmem : (La₁.addSubgroupOf La₂).index • (⟨v, hv⟩ : La₂) ∈ La₁.addSubgroupOf La₂ :=
      AddSubgroup.nsmul_index_mem _ _
    have h1 : (La₁.addSubgroupOf La₂).index • v ∈ La₁ := by
      rw [AddSubgroup.mem_addSubgroupOf] at hmem
      simpa using hmem
    have h2 : (La₁.addSubgroupOf La₂).index • v ∈ La₂ := La₂.nsmul_mem hv _
    have h3 : (La₁.addSubgroupOf La₂).index • v ∈
        Submodule.span ℝ ((La₁ ⊓ La₂ : AddSubgroup (VC D N N')) : Set (VC D N N')) :=
      Submodule.subset_span (AddSubgroup.mem_inf.mpr ⟨h1, h2⟩)
    have h4 := Submodule.smul_mem _ (((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ h3
    rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn),
      one_smul] at h4

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB
open scoped Pointwise ENNReal Function

variable {D : Car} {N N' : ℕ}

theorem Hf_cont_left (T : Tor D) (w : VC D N N') : Continuous fun z : VC D N N' => Hf D T z w := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  fun_prop

theorem Hf_cont_diag (T : Tor D) : Continuous fun z : VC D N N' => Hf D T z z := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Hf
  refine Continuous.div_const ?_ _
  refine continuous_finset_sum _ fun τ _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have hc : Continuous fun z : VC D N N' => z τ i j :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))
  exact hc.mul (Complex.continuous_conj.comp hc)

theorem U_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) (x : VC D N N') :
    Continuous (U D T x G) := by
  unfold Formalism.L2.Ker.Cd.TaylorLogMetric.U
  exact (hG.comp (continuous_id.add continuous_const)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul (Hf_cont_left T x)).sub continuous_const))

theorem dens_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) :
    Continuous (Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T G) := by
  unfold Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens
  exact ((continuous_norm.comp hG).pow 2).mul
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (Hf_cont_diag T))))

theorem crD_cont (T : Tor D) {A B : VC D N N' → ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous (crD T A B) := by
  unfold crD
  exact (hA.mul (Complex.continuous_conj.comp hB)).mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (Hf_cont_diag T)))))

theorem crD_self (T : Tor D) (A : VC D N N' → ℂ) (z : VC D N N') :
    crD T A A z = ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T A z : ℝ) : ℂ) := by
  unfold crD Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem normSq_eq (T : Tor D) (La' : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ) :
    normSq D T La' G = ⨍ z in Classical.epsilon
      (fun Fd => IsAddFundamentalDomain La' Fd volume), Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T G z := rfl

theorem crD_Mper (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) (hZ : ∀ x ∈ La₂, ∀ y ∈ La₂, ∃ b : ℤ, (Hf D T x y).im = b)
    {x x' : VC D N N'} (hx : x ∈ La₂) (hx' : x' ∈ La₂) :
    ∀ m ∈ La₁ ⊓ La₂, ∀ z, crD T (trm T G x) (trm T G x') (z + m) =
      crD T (trm T G x) (trm T G x') z := by
  intro m hm z
  have hm' := AddSubgroup.mem_inf.mp hm
  rw [crD_shift T hG hm'.1 x x' z, ep_mul_conj]
  obtain ⟨b, hb⟩ := hZ (x - x') (La₂.sub_mem hx hx') m hm'.2
  rw [(ep_eq_one_iff _).2 ⟨b, hb⟩, one_mul]

theorem trm_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) (x : VC D N N') :
    Continuous (trm T G x) := by
  unfold trm
  exact continuous_const.mul (U_cont T hG x)

private theorem crD_const_mul_sum (T : Tor D) (c : ℂ) {ι : Type*} (s : Finset ι) (A : ι → VC D N N' → ℂ)
    (z : VC D N N') :
    crD T (fun w => c * ∑ i ∈ s, A i w) (fun w => c * ∑ i ∈ s, A i w) z =
      c * starRingEnd ℂ c * ∑ i ∈ s, ∑ j ∈ s, crD T (A i) (A j) z := by
  simp only [crD]
  rw [map_mul, map_sum]
  calc c * (∑ i ∈ s, A i z) * (starRingEnd ℂ c * ∑ j ∈ s, starRingEnd ℂ (A j z)) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ)
      = c * starRingEnd ℂ c * ((∑ i ∈ s, A i z) * (∑ j ∈ s, starRingEnd ℂ (A j z)) *
        ((Real.exp (-Real.pi * (Hf D T z z).re) : ℝ) : ℂ)) := by ring
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]

theorem iso_core (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')}
    (h₁ : FullLat La₁) (h₂ : FullLat La₂)
    [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)] [Finite (La₁ ⧸ La₂.addSubgroupOf La₁)]
    (hZ : ∀ x ∈ La₂, ∀ y ∈ La₂, ∃ b : ℤ, (Hf D T x y).im = b)
    (hS : SemiChar T La₂)
    (hSD : ∀ v ∈ La₂, (∀ y ∈ La₁, ∃ b : ℤ, (Hf D T v y).im = b) → v ∈ La₁)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) :
    normSq D T La₂ (Iop D T La₁ La₂ G) = normSq D T La₁ G := by
  have hGc : Continuous G := hG.1.continuous
  have hI := Iop_mem_ThSp T hS hG
  have hM : FullLat (La₁ ⊓ La₂) := full_inf h₁ h₂
  haveI : Countable (La₁ ⊓ La₂ : AddSubgroup (VC D N N')) := countable_of_full hM
  haveI : Countable La₁ := countable_of_full h₁
  haveI : Countable La₂ := countable_of_full h₂
  obtain ⟨t, ht⟩ := fd_of_full hM
  haveI : Finite (La₂ ⧸ (La₁ ⊓ La₂).addSubgroupOf La₂) := by
    rw [AddSubgroup.inf_addSubgroupOf_right]
    infer_instance
  haveI : Finite (La₁ ⧸ (La₁ ⊓ La₂).addSubgroupOf La₁) := by
    rw [AddSubgroup.inf_addSubgroupOf_left]
    infer_instance
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  have hs₁ := Classical.epsilon_spec (fd_of_full h₁)
  have hs₂ := Classical.epsilon_spec (fd_of_full h₂)
  have hd0 : ∀ (F : VC D N N' → ℂ) z, 0 ≤ Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T F z := fun F z => by
    unfold Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens
    positivity

  have e1 : normSq D T La₂ (Iop D T La₁ La₂ G) = ⨍ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z := by
    rw [normSq_eq]
    exact (avg_sub inf_le_right hs₂ ht _ (hd0 _) (dens_cont T hI.1.continuous)
      (fun g hg z => dens_periodic T La₂ _ hI g hg z)).symm
  have hdU : ∀ x w, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T x G) w = Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T G (w + x) := fun x w => by
    have h := crD_U T G G x w
    rw [crD_self, crD_self] at h
    exact_mod_cast h

  have hUx : ∀ x : VC D N N', ⨍ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T x G) z = normSq D T La₁ G := by
    intro x
    rw [← normSq_U_of_full T La₁ h₁ G hG x, normSq_eq]
    refine avg_sub inf_le_left hs₁ ht _ (hd0 _) (dens_cont T (U_cont T hGc x)) ?_
    intro g hg z
    rw [hdU, hdU, show z + g + x = z + x + g by abel, dens_periodic T La₁ G hG g hg]
  have hn0 : (((La₁.addSubgroupOf La₂).index : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr AddSubgroup.index_ne_zero_of_finite
  have hcard : Fintype.card (La₂ ⧸ La₁.addSubgroupOf La₂) = (La₁.addSubgroupOf La₂).index := by
    rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hxq : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, ((Quotient.out q : La₂) : VC D N N') ∈ La₂ := fun q => (Quotient.out q).2
  have hint : ∀ q q' : La₂ ⧸ La₁.addSubgroupOf La₂,
      MeasureTheory.IntegrableOn (crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q' : La₂) : VC D N N'))) t volume :=
    fun q q' => intOn_of_full hM ht _ (crD_cont T (trm_cont T hGc _) (trm_cont T hGc _))
      (crD_Mper T hG hZ (hxq q) (hxq q'))

  have hoff : ∀ q q' : La₂ ⧸ La₁.addSubgroupOf La₂, q ≠ q' →
      ∫ z in t, crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q' : La₂) : VC D N N')) z = 0 := by
    intro q q' hqq'
    have hnot : ((Quotient.out q : La₂) : VC D N N') - ((Quotient.out q' : La₂) : VC D N N') ∉ La₁ := by
      intro hmem
      apply hqq'
      have e1 : (QuotientAddGroup.mk (Quotient.out q) : La₂ ⧸ La₁.addSubgroupOf La₂) = q := Quotient.out_eq q
      have e2 : (QuotientAddGroup.mk (Quotient.out q') : La₂ ⧸ La₁.addSubgroupOf La₂) = q' :=
        Quotient.out_eq q'
      rw [← e1, ← e2, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
        AddSubgroup.coe_neg]
      have h3 : -((Quotient.out q : La₂) : VC D N N') + ((Quotient.out q' : La₂) : VC D N N') = -(((Quotient.out q : La₂) : VC D N N') - ((Quotient.out q' : La₂) : VC D N N')) := by abel
      rw [h3]
      exact La₁.neg_mem hmem
    have hex : ∃ y ∈ La₁, ¬ ∃ b : ℤ, (Hf D T (((Quotient.out q : La₂) : VC D N N') - ((Quotient.out q' : La₂) : VC D N N')) y).im = b := by
      by_contra hcon
      push_neg at hcon
      exact hnot (hSD _ (La₂.sub_mem (hxq q) (hxq q')) hcon)
    obtain ⟨y, hy, hyb⟩ := hex
    refine int_zero_of_char ht _ (crD_Mper T hG hZ (hxq q) (hxq q')) y
      (ep T ((Quotient.out q : La₂) : VC D N N') y * starRingEnd ℂ (ep T ((Quotient.out q' : La₂) : VC D N N') y)) ?_ (fun z => crD_shift T hG hy _ _ z)
    rw [ep_mul_conj]
    exact fun h1 => hyb ((ep_eq_one_iff _).1 h1)

  have hdiag : ∀ (q : La₂ ⧸ La₁.addSubgroupOf La₂) z, crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q : La₂) : VC D N N')) z =
      ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z : ℝ) : ℂ) := by
    intro q z
    show crD T (fun w => al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w)
      (fun w => al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w) z = _
    rw [crD_smul, al_mul_conj, one_mul, crD_self]

  have hexp : ∀ z, ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z : ℝ) : ℂ) =
      ((((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, ∑ q' : La₂ ⧸ La₁.addSubgroupOf La₂,
        crD T (trm T G ((Quotient.out q : La₂) : VC D N N')) (trm T G ((Quotient.out q' : La₂) : VC D N N')) z := by
    intro z
    rw [← crD_self]
    have hI' : Iop D T La₁ La₂ G = fun w => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
        ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, trm T G ((Quotient.out q : La₂) : VC D N N') w := by
      funext w
      unfold Formalism.L2.Ker.Cd.TaylorLogMetric.Iop
      rw [finsum_eq_sum_of_fintype]
      rfl
    have hcc : ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * starRingEnd ℂ ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) =
        ((((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) := by
      rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (Nat.cast_nonneg _)]
    rw [hI', crD_const_mul_sum, hcc]
  have hint_sum : ∫ z in t, ((Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z : ℝ) : ℂ) =
      ((((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
        ((∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z : ℝ) : ℂ) := by
    simp_rw [hexp]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _
      (fun q _ => MeasureTheory.integrable_finset_sum _ (fun q' _ => hint q q'))]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MeasureTheory.integral_finset_sum _ (fun q' _ => hint q q'),
      Finset.sum_eq_single q (fun q' _ hq' => hoff q q' (Ne.symm hq'))
        (fun h => absurd (Finset.mem_univ q) h)]
    simp_rw [hdiag]
    exact integral_ofReal
  have hreal : ∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z =
      (((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, ∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z := by
    have h := hint_sum
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  have hU' : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      (volume t).toReal⁻¹ * ∫ z in t, Formalism.L2.Ker.Cd.IntegralLatticeDensity.dens D T (U D T ((Quotient.out q : La₂) : VC D N N') G) z = normSq D T La₁ G := by
    intro q
    rw [← hUx ((Quotient.out q : La₂) : VC D N N'), MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def,
      smul_eq_mul]
  rw [e1, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, smul_eq_mul, hreal, mul_left_comm, Finset.mul_sum]
  simp_rw [hU']
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions MeasureTheory Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def HfIntRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L')

def SelfDualRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ v : VC D N N', (∀ y ∈ La D (tor0 D cc δ) L L', ∃ b : ℤ, (Hf D (tor0 D cc δ) v y).im = b) →
        v ∈ La D (tor0 D cc δ) L L'

theorem IopIso_of_parts (hA : HfIntRec) (hB : SelfDualRec) :
    ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ) := by
  intro D cc hcc δ hδ N N' L₁ L₁' L₂ L₂' h₁ h₂ G hG
  by_cases h0 : δ = 0
  · subst h0
    have hLam : (tor0 D cc 0).abelian₂ = ⊥ := by
      show lamOf D cc 0 = ⊥
      unfold Formalism.L2.Ker.Cd.TaylorLogMetric.lamOf
      rw [AddSubgroup.closure_eq_bot_iff]
      rintro w ⟨c, _, rfl⟩
      simp
    have hLa : ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), La D (tor0 D cc 0) L L' = ⊥ := by
      intro L L'
      unfold Formalism.L2.Ker.Cd.TaylorLogMetric.La
      rw [AddSubgroup.closure_eq_bot_iff]
      rintro z ⟨w, hw, A, _, rfl⟩
      rw [hLam, AddSubgroup.mem_bot] at hw
      simp [hw]
    rw [hLa L₂ L₂', ← hLa L₁ L₁']
    exact IopIso_diag D (tor0 D cc 0) L₁ L₁' G hG
  · have hF₁ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.fullLat D L₁ L₁' h₁ cc hcc δ h0
    have hF₂ := Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.fullLat D L₂ L₂' h₂ cc hcc δ h0
    haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂
    haveI := La_index_finite cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁
    have hI₂ := hA D cc hcc δ hδ h0 N N' L₂ L₂' h₂
    refine IL.iso_core (tor0 D cc δ) hF₁ hF₂ ?_ (semiChar_of_HfInt _ hI₂) ?_ hG
    · intro x hx y hy
      obtain ⟨a, b, _, hab⟩ := hI₂ x hx y hy
      exact ⟨b, by rw [hab]; simp⟩
    · intro v _ hv
      exact hB D cc hcc δ hδ h0 N N' L₁ L₁' h₁ v hv


end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end
