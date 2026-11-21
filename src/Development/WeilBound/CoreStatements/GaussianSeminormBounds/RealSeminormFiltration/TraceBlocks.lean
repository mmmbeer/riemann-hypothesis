import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieG
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieE

section
noncomputable section

open scoped TensorProduct Matrix Classical Real
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex MvPolynomial

namespace PositivityTheory.RL.Up

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def atL (w : ι) : Module.End ℂ V →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, V) :=
  (PiTensorProduct.mapMultilinear ℂ (fun _ : ι => V) fun _ => V).toLinearMap (fun _ => LinearMap.id) w

omit [Fintype ι] in
theorem atL_eq (w : ι) (L : Module.End ℂ V) : atPl (V := fun _ : ι => V) w L = atL w L := rfl

omit [Fintype ι] in
theorem atL_tprod (w : ι) (L : Module.End ℂ V) (x : ι → V) :
    atL w L (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (Function.update x w (L (x w))) := by
  rw [← atL_eq, atPl, PiTensorProduct.map_tprod]
  congr 1
  funext v
  by_cases h : v = w
  · subst h; simp
  · simp [h]

omit [Fintype ι] in
theorem atL_mul (w : ι) (L L' : Module.End ℂ V) : atL w (L * L') = atL w L * atL w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp [atL_tprod]

omit [Fintype ι] in
theorem atL_one (w : ι) : atL w (1 : Module.End ℂ V) = 1 := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp [atL_tprod]

theorem map_sumPl (e : V →ₗ[ℂ] W) (L : ι → Module.End ℂ V) (L' : ι → Module.End ℂ W) (h : ∀ w x, e (L w x) = L' w (e x))
    (T : ⨂[ℂ] _ : ι, V) : PiTensorProduct.map (fun _ => e) (sumPl (V := fun _ => V) L T) =
      sumPl (V := fun _ => W) L' (PiTensorProduct.map (fun _ => e) T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, sumPl, LinearMap.sum_apply, map_sum, atL_eq, atL_tprod, PiTensorProduct.map_tprod]
    congr 1
    refine Finset.sum_congr rfl fun w _ => congrArg _ (funext fun v => ?_)
    by_cases hv : v = w
    · subst hv; simp [h]
    · simp [hv]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tensor

variable {P Q R S : ℕ}

theorem pd_X {σ : Type} [DecidableEq σ] (a b : σ) :
    ((pderiv a).toLinearMap * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * (pderiv a).toLinearMap + if a = b then 1 else 0 := by
  refine LinearMap.ext fun p => ?_
  by_cases h : a = b
  · subst h
    simp [add_comm]
  · simp [h, pderiv_X_of_ne (Ne.symm h)]

theorem pd_pd {σ : Type} [DecidableEq σ] (a b : σ) :
    ((pderiv a).toLinearMap * (pderiv b).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) =
      (pderiv b).toLinearMap * (pderiv a).toLinearMap := by
  refine LinearMap.ext fun P => ?_
  change pderiv a (pderiv b P) = pderiv b (pderiv a P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem low_rai (l l' : Ln P Q R S) : lowB l' * raiB l = raiB l * lowB l' + if l = l' then 1 else 0 := by
  unfold lowB raiB
  by_cases h : l = l'
  · subst h
    cases linePos l <;> simp [pd_X]
  · have h' : l' ≠ l := Ne.symm h
    cases linePos l <;> cases linePos l' <;> simp [pd_X, h, h', pd_pd l l']
    exact LinearMap.ext fun p => mul_left_comm _ _ _

theorem anti_omE (l l' : Ln P Q R S) : raiB l * lowB l' + lowB l' * raiB l = (2 : ℂ) • omE l l' := by
  rw [low_rai, omE]
  split_ifs <;> module

def eps : Ix R S → ℝ := Sum.elim (fun _ => 1) fun _ => -1

theorem lineSign_eq (a : Ix P Q) (b : Ix R S) :
    lineSign (p := P) (q := Q) (r := R) (s := S) a b = ((eps a * eps b : ℝ) : ℂ) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, eps]

theorem eps_sq (a : Ix R S) : eps a * eps a = 1 := by rcases a with a | a <;> simp [eps]

theorem upq_entry {Y : Mat R S} (hY : Y ∈ upq R S) (b b' : Ix R S) :
    ((eps b * eps b' : ℝ) : ℂ) * star (Y b' b) = -Y b b' := by
  have := congrFun (congrFun (show Yᴴ * Jm R S + Jm R S * Y = 0 from hY) b) b'
  rw [PositivityTheory.RL.Jm_eq, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at this
  rcases b with b | b <;> rcases b' with b' | b' <;> simp [eps] at this ⊢ <;>
    first | linear_combination this | linear_combination -this

theorem im_twisted_inner_sum (c c' : Matrix (Ix P Q) (Ix R S) ℂ) : (∑ l, Fock.tw1 c l * star (Fock.tw1 c' l)).im =
    ∑ l : Ln P Q R S, eps l.1 * eps l.2 * (c l.1 l.2 * star (c' l.1 l.2)).im := by
  rw [im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases l with ⟨a | a, b | b⟩ <;> simp [Fock.tw1, linePos, eps] <;> ring

def cu (Y : Mat R S) (j : Ln P Q R S × Bool) : Matrix (Ix P Q) (Ix R S) ℂ :=
  (if j.2 then 1 else I) • (Matrix.single j.1.1 j.1.2 (1 : ℂ) * Yᵀ)

def cv (j : Ln P Q R S × Bool) : Matrix (Ix P Q) (Ix R S) ℂ :=
  (((eps j.1.1 * eps j.1.2 / 2 : ℝ) : ℂ) * if j.2 then I else -1) • Matrix.single j.1.1 j.1.2 1

theorem expand (Y : Mat R S) (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    c * Yᵀ = ∑ j, (2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 c l)).im) • cu Y j := by
  have h : ∀ j : Ln P Q R S × Bool, 2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 c l)).im =
      if j.2 then (c j.1.1 j.1.2).re else (c j.1.1 j.1.2).im := fun j => by
    obtain ⟨⟨a, b⟩, t⟩ := j
    rw [im_twisted_inner_sum, Finset.sum_eq_single (a, b) (fun l _ hl => by
      have : ¬(a = l.1 ∧ b = l.2) := fun h => hl (Prod.ext h.1.symm h.2.symm)
      simp [cv, this]) (by simp)]
    rcases a with a | a <;> rcases b with b | b <;> cases t <;> simp [cv, eps] <;> ring
  simp only [h]
  conv_lhs => rw [Matrix.matrix_eq_sum_single c]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (c a b) = c a b • Matrix.single a b 1 by simp, Matrix.smul_mul]
  simp only [Fintype.sum_bool, cu, if_true, Bool.false_eq_true, if_false, one_smul]
  generalize Matrix.single a b (1 : ℂ) * Yᵀ = N
  ext i k
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
  linear_combination (-N i k) * re_add_im (c a b)

theorem heis_smul (z : ℂ) (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp (z • c) = ((Real.sqrt (2 * π) : ℝ) : ℂ) •
    (z • (∑ l : Ln P Q R S, c l.1 l.2 • raiB l) - star z • ∑ l : Ln P Q R S,
      (((eps l.1 * eps l.2 : ℝ) : ℂ) * star (c l.1 l.2)) • lowB l) := by
  rw [heisOp, Finset.smul_sum (r := z), Finset.smul_sum (r := star z), ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [lineSign_eq, Matrix.smul_apply, smul_eq_mul, star_mul', smul_smul]
  congr 2
  ring

theorem fock_eq {Y : Mat R S} (hY : Y ∈ upq R S) :
    (8 * π * I : ℂ)⁻¹ • ∑ j : Ln P Q R S × Bool, (heisOp (cu Y j) * heisOp (cv j) + heisOp (cv j) * heisOp (cu Y j)) =
      fockAct2 P Q R S Y := by
  set k : ℂ := ((Real.sqrt (2 * π) : ℝ) : ℂ) with hk
  have hk2 : k * k = 2 * π := by
    rw [hk, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have one : ∀ (a : Ix P Q) (b : Ix R S), (8 * π * I : ℂ)⁻¹ • ∑ t : Bool,
      (heisOp (cu Y ((a, b), t)) * heisOp (cv ((a, b), t)) + heisOp (cv ((a, b), t)) * heisOp (cu Y ((a, b), t))) =
      (1 / 2 : ℂ) • (∑ b', Y b' b • omE (a, b') (a, b) + ∑ b', Y b b' • omE (a, b) (a, b')) := fun a b => by
    have r1 : (∑ l : Ln P Q R S, (Matrix.single a b (1 : ℂ) * Yᵀ) l.1 l.2 • raiB l) = ∑ b', Y b' b • raiB (a, b') := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun a' _ h => by simp [Matrix.mul_apply, h.symm]) (by simp)]
      simp
    have r2 : (∑ l : Ln P Q R S, (((eps l.1 * eps l.2 : ℝ) : ℂ) * star ((Matrix.single a b (1 : ℂ) * Yᵀ) l.1 l.2)) • lowB l) =
        -(((eps a * eps b : ℝ) : ℂ) • ∑ b', Y b b' • lowB (a, b')) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun a' _ h => by simp [Matrix.mul_apply, h.symm]) (by simp),
        Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [smul_smul, ← neg_smul, Matrix.single_mul_apply_same, one_mul, Matrix.transpose_apply]
      congr 1
      have h1 := upq_entry hY b b'
      have h2 : ((eps b : ℝ) : ℂ) * (eps b : ℝ) = 1 := by rw [← ofReal_mul, eps_sq, ofReal_one]
      push_cast at h1 ⊢
      linear_combination ((eps a : ℂ) * eps b) * h1 - ((eps a : ℂ) * eps b' * star (Y b' b)) * h2
    have r3 : (∑ l : Ln P Q R S, (Matrix.single a b (1 : ℂ)) l.1 l.2 • raiB l) = raiB (a, b) := by
      rw [Finset.sum_eq_single (a, b) (fun l _ hl => by
        have : ¬(a = l.1 ∧ b = l.2) := fun h => hl (Prod.ext h.1.symm h.2.symm)
        simp [this]) (by simp)]
      simp
    have r4 : (∑ l : Ln P Q R S, (((eps l.1 * eps l.2 : ℝ) : ℂ) * star ((Matrix.single a b (1 : ℂ)) l.1 l.2)) • lowB l) =
        ((eps a * eps b : ℝ) : ℂ) • lowB (a, b) := by
      rw [Finset.sum_eq_single (a, b) (fun l _ hl => by
        have : ¬(a = l.1 ∧ b = l.2) := fun h => hl (Prod.ext h.1.symm h.2.symm)
        simp [this]) (by simp)]
      simp
    have a1 : (2 : ℂ) • ∑ b', Y b' b • omE (a, b') (a, b) =
        (∑ b', Y b' b • raiB (a, b')) * lowB (a, b) + lowB (a, b) * ∑ b', Y b' b • raiB (a, b') := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, anti_omE, smul_comm]
    have a2 : (2 : ℂ) • ∑ b', Y b b' • omE (a, b) (a, b') =
        raiB (a, b) * (∑ b', Y b b' • lowB (a, b')) + (∑ b', Y b b' • lowB (a, b')) * raiB (a, b) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, ← smul_add, anti_omE, smul_comm]
    have hs : ((eps a * eps b : ℝ) : ℂ) * ((eps a * eps b : ℝ) : ℂ) = 1 := by
      rw [← ofReal_mul, mul_mul_mul_comm, eps_sq, eps_sq, mul_one, ofReal_one]
    rw [show (1 / 2 : ℂ) = (1 / 4) * 2 by norm_num, mul_smul, smul_add (2 : ℂ), a1, a2, inv_smul_eq_iff₀ (by simp [hπ])]
    simp only [Fintype.sum_bool, cu, cv, heis_smul, r1, r2, r3, r4, if_true, Bool.false_eq_true, if_false, ← hk]
    simp only [ofReal_div, ofReal_ofNat, star_mul', star_div₀, star_ofNat, star_one, star_neg, star_def, conj_I, conj_ofReal, map_neg, map_one]
    generalize ((eps a * eps b : ℝ) : ℂ) = s at hs
    generalize (∑ b', Y b' b • raiB (a, b') : Module.End ℂ (Pol P Q R S)) = Rp
    generalize (∑ b', Y b b' • lowB (a, b') : Module.End ℂ (Pol P Q R S)) = Lp
    simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_neg, neg_mul]
    match_scalars <;> first | ring1 | linear_combination (I * s ^ 2) * hk2 + (2 * π * I) * hs
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [Finset.smul_sum (r := (8 * π * I : ℂ)⁻¹) (s := (Finset.univ : Finset (Ix R S))), one]
  simp only [fockAct2, LinearMap.comp_apply, omAct_apply, Matrix.kroneckerMapBilinear_apply_apply,
    Matrix.kroneckerMap_apply, LinearMap.mul_apply', Fintype.sum_prod_type, Matrix.one_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_comm (f := fun b b' => Y b' b • omE (a, b') (a, b)),
    ← two_smul ℂ, smul_smul]
  simp [ite_smul]

def sw (P Q R S : ℕ) : Pol R S P Q ≃ₐ[ℂ] Pol P Q R S := renameEquiv ℂ (Equiv.prodComm _ _)

theorem linePos_swap (a : Ix P Q) (b : Ix R S) :
    linePos (p := R) (q := S) (r := P) (s := Q) (b, a) = linePos (p := P) (q := Q) (r := R) (s := S) (a, b) := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem sw_pd (a : Ix P Q) (b : Ix R S) (p : Pol R S P Q) : sw P Q R S (pderiv (b, a) p) = pderiv (a, b) (sw P Q R S p) :=
  (pderiv_rename (Equiv.prodComm _ _).injective (b, a) p).symm

theorem sw_low (a : Ix P Q) (b : Ix R S) (p : Pol R S P Q) : sw P Q R S (lowB (b, a) p) = lowB (a, b) (sw P Q R S p) := by
  unfold lowB
  rw [linePos_swap]
  split_ifs
  · exact sw_pd a b p
  · simp [sw]

theorem sw_rai (a : Ix P Q) (b : Ix R S) (p : Pol R S P Q) : sw P Q R S (raiB (b, a) p) = raiB (a, b) (sw P Q R S p) := by
  unfold raiB
  rw [linePos_swap]
  split_ifs
  · simp [sw]
  · simp only [LinearMap.neg_apply, map_neg]
    exact congrArg _ (sw_pd a b p)

theorem sw_heis (c : Matrix (Ix R S) (Ix P Q) ℂ) (p : Pol R S P Q) :
    sw P Q R S (heisOp c p) = heisOp cᵀ (sw P Q R S p) := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, map_smul, map_sum, map_sub,
    Fintype.sum_prod_type, sw_low, sw_rai, lineSign_eq, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  rw [mul_comm (eps a)]

theorem sw_fock (Y : Mat P Q) (p : Pol R S P Q) :
    sw P Q R S (fockAct2 R S P Q Y p) = fockAct1 P Q R S Y (sw P Q R S p) := by
  have h : ∀ (a a' : Ix P Q) (b b' : Ix R S), sw P Q R S (omE (b, a) (b', a') p) = omE (a, b) (a', b') (sw P Q R S p) :=
    fun a a' b b' => by
      simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, sw_rai, sw_low, Prod.mk.injEq, and_comm]
      split_ifs <;> simp
  simp only [fockAct1, fockAct2, LinearMap.comp_apply, LinearMap.flip_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply', Fintype.sum_prod_type,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

end PositivityTheory.RL.Up

namespace PositivityTheory.RL

open Up

theorem lieFirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := by
  intro h2 F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om χ m hcm hψ hfr hΦ hd hW hm γ hγ Y hY T
  let Ψ : Tens F R S P Q ≃ₗ[ℂ] Tens F P Q R S := PiTensorProduct.congr fun _ => (sw P Q R S).toLinearEquiv
  have hΨ : ∀ T, Ψ T = PiTensorProduct.map (fun _ => (sw P Q R S).toLinearMap) T := fun _ => rfl
  have h1 : IsFockMap ψ τ d' C A (Φ ∘ₗ Ψ.toLinearMap) := by
    refine ⟨hΦ.1.comp Ψ.injective, fun u hu c hc T => ?_⟩
    have := hΦ.2 uᵀ (fun s hs => by rw [← Matrix.transpose_smul, hu s hs, Matrix.transpose_zero]) (fun w => (c w)ᵀ)
      (fun w => by rw [Matrix.transpose_map, hc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]) (Ψ T)
    have e : ∀ t, d.rho ψ (realAd F t • uᵀ) = d'.rho ψ (realAd F t • u) := fun t => by
      rw [Darboux.rho, Darboux.rho, ← hd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [e] at this
    rw [hΨ, ← map_sumPl _ (fun w => heisOp (c w)) _ fun w x => sw_heis (c w) x] at this
    exact this
  have := h2 F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om χ m hcm hψ ⟨(mul_comm _ _).trans hfr.1, hfr.2.2, hfr.2.1⟩ h1 hW hm
    γ hγ Y hY (Ψ.symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
  rw [hΨ, map_sumPl _ _ (fun w => fockAct1 P Q R S (Y w) + ((m w : ℂ) / 2 * (Y w).trace) • 1) fun w x => by
    simp only [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, Module.End.one_apply]
    exact congrArg (· + _) (sw_fock (Y w) x), ← hΨ, LinearEquiv.apply_symm_apply] at this
  exact this

end PositivityTheory.RL

end
end

section
noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex MeasureTheory

namespace PositivityTheory.RL.Up

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem box_SB {g g' : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (hg' : g' ∈ SB (κ → Af F)) :
    boxFun g g' ∈ SB (κ ⊕ κ → Af F) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  refine ⟨(hg.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (by fun_prop)).mul
    (hg'.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((hg.2.prod hg'.2).image
    (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := Af F)).symm.continuous) fun x hx => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩

variable (F κ) in
theorem exists_box : ∃ (f : SInf F κ) (B : SInf F (κ ⊕ κ)) (r : (κ → mixedEmbedding.mixedSpace F) → ℝ),
    (∀ x, B x = f (x ∘ Sum.inl) * f (x ∘ Sum.inr)) ∧ (∀ x, f x = r x) ∧ Continuous r ∧ HasCompactSupport r ∧ r 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, by norm_num, by norm_num⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := ofRealCLM.contDiff.comp b.contDiff
  have h3 : HasCompactSupport fun x : κ ⊕ κ → mixedEmbedding.mixedSpace F =>
      ((b (x ∘ Sum.inl) : ℝ) : ℂ) * ((b (x ∘ Sum.inr) : ℝ) : ℂ) := by
    refine HasCompactSupport.intro ((h1.prod h1).image
      (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := mixedEmbedding.mixedSpace F)).symm.continuous)
      fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩
  exact ⟨h1.toSchwartzMap h2, h3.toSchwartzMap ((h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inl i))).mul
    (h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inr i)))), b, fun _ => rfl, fun _ => rfl, b.continuous,
    b.hasCompactSupport, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)⟩

variable (F κ) in
theorem exists_form (ψ : AddChar (AF F) ℂ) : ∃ l ∈ (adeleClass F).adm (κ ⊕ κ),
    (∀ x y : κ → AF F, ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧
      ∃ (B : SInf F (κ ⊕ κ)), ∃ G ∈ SB (κ ⊕ κ → Af F), l (pureA F B G) ≠ 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  borelize (κ → Af F)
  let X := κ → mixedEmbedding.mixedSpace F
  borelize X
  let μ : Measure X := Measure.addHaar
  let ν : Measure (κ → Af F) := Measure.addHaar
  haveI : MeasurableAdd X := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → Af F) := ContinuousAdd.measurableAdd
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  let k : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] (X × (κ → Af F) → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun p => Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {φ | Integrable (k φ) (μ.prod ν)}
      zero_mem' := integrable_zero _ _ _
      add_mem' := fun ha hb => ha.add hb
      smul_mem' := fun c _ h => h.smul c }
  let l0 : N →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ p, k φ p ∂(μ.prod ν)
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c _ }
  obtain ⟨l, hl⟩ := l0.exists_extend
  have hl' : ∀ φ ∈ N, l φ = ∫ p, k φ p ∂(μ.prod ν) := fun φ h => LinearMap.congr_fun hl ⟨φ, h⟩
  let dg : X →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.elim id id i)
  have hdg : AntilipschitzWith 1 dg := AddMonoidHomClass.antilipschitz_of_bound dg fun x => by
    rw [NNReal.coe_one, one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (dg x) (Sum.inl i)
  let Rs : SInf F (κ ⊕ κ) →L[ℂ] 𝓢(X, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ dg.hasTemperateGrowth hdg
  have hk : ∀ (B : SInf F (κ ⊕ κ)) (G : (κ ⊕ κ → Af F) → ℂ),
      k (pureA F B G) = fun p => Rs B p.1 * G (Sum.elim p.2 p.2) := fun B G => by
    funext p
    refine congrArg₂ (· * ·) (congrArg B (funext fun i => ?_)) (congrArg G (funext fun i => ?_))
    · rcases i with i | i <;> exact RingEquiv.apply_symm_apply _ _
    · rcases i with i | i <;> rfl
  have hc : Continuous fun b : κ → Af F => (Sum.elim b b : κ ⊕ κ → Af F) :=
    continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i
  have hG : ∀ G ∈ SB (κ ⊕ κ → Af F), Integrable (fun b : κ → Af F => G (Sum.elim b b)) ν := fun G hG =>
    (hG.1.continuous.comp hc).integrable_of_hasCompactSupport (hG.2.comp_isClosedEmbedding
      (Function.LeftInverse.isClosedEmbedding (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (fun _ => rfl) (by fun_prop) hc))
  have hp : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F), pureA F B G ∈ N := fun B G h => by
    show Integrable (k _) _
    rw [hk]
    exact (Rs B).integrable.mul_prod (hG G h)
  have hv : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F),
      l (pureA F B G) = (∫ a, Rs B a ∂μ) * ∫ b, G (Sum.elim b b) ∂ν := fun B G h => by
    rw [hl' _ (hp B G h), hk]
    exact integral_prod_mul (Rs B) fun b => G (Sum.elim b b)
  refine ⟨l, fun G h => ⟨(∫ b, G (Sum.elim b b) ∂ν) • (SchwartzMap.integralCLM ℂ μ ∘L Rs), fun B => ?_⟩,
    fun x y φ hφ => ?_, ?_⟩
  · rw [hv B G h, mul_comm]
    rfl
  · have hN : φ ∈ N := (Submodule.span_le.2 (by rintro _ ⟨B, G, h, rfl⟩; exact hp B G h) : schA F (κ ⊕ κ) ≤ N) hφ
    let c : X × (κ → Af F) := (fun i => evI F (x i), fun i => (x i).2)
    have e : k (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = fun p => k φ (c + p) := by
      funext p
      have e1 : SeminormBoundRestriction.pt (c + p).1 (c + p).2 = SeminormBoundRestriction.pt p.1 p.2 + x := funext fun i =>
        Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _).trans ((add_comm _ _).trans
          (congrArg (_ + ·) (RingEquiv.symm_apply_apply _ _)))) (add_comm _ _)
      show schr _ _ _ (Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)) =
        φ (Sum.elim (SeminormBoundRestriction.pt (c + p).1 (c + p).2) (SeminormBoundRestriction.pt (c + p).1 (c + p).2))
      rw [e1, schr, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
      simp only [dotProduct_neg, add_neg_cancel, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      funext i
      rcases i with i | i <;> rfl
    rw [hl' _ hN, hl' _ (by
      show Integrable (k _) _
      rw [e]
      exact (show Integrable (k φ) (μ.prod ν) from hN).comp_add_left c), e]
    exact integral_add_left_eq_self (k φ) c
  · obtain ⟨f, B, r, hB, hf, hr, hr', hr0⟩ := exists_box F κ
    obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
    have hg' : (fun x => ((‖g x‖ : ℝ) : ℂ)) ∈ SB (κ → Af F) :=
      ⟨hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ), hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩
    refine ⟨B, _, box_SB hg' hg', ?_⟩
    rw [hv _ _ (box_SB hg' hg')]
    refine mul_ne_zero ?_ ?_
    · have : ∀ a, Rs B a = ((r a * r a : ℝ) : ℂ) := fun a => by
        rw [ofReal_mul, ← hf]
        exact hB _
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hr.mul hr).integral_pos_of_hasCompactSupport_nonneg_nonzero hr'.mul_left (fun _ => mul_self_nonneg _)
        (x := 0) (by simp [hr0])).ne'
    · have : ∀ b, boxFun (fun x => ((‖g x‖ : ℝ) : ℂ)) (fun x => ((‖g x‖ : ℝ) : ℂ)) (Sum.elim b b) =
          ((‖g b‖ * ‖g b‖ : ℝ) : ℂ) := fun b => (ofReal_mul _ _).symm
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hg.1.continuous.norm.mul hg.1.continuous.norm).integral_pos_of_hasCompactSupport_nonneg_nonzero
        hg.2.norm.mul_left (fun _ => mul_self_nonneg _) (x := y) (by simp [hy])).ne'

end PositivityTheory.RL.Up

end
end

section
noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex

namespace PositivityTheory.RL.Up

section Mat

variable {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_conj' (C : Matrix β ι ℂ) (C' : Matrix ι β ℂ) (h1 : C * C' = 1) (h2 : C' * C = 1) (Y : Matrix ι ι ℂ) :
    NormedSpace.exp (C * Y * C') = C * NormedSpace.exp Y * C' := by
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℝ _
  let φ : Matrix ι ι ℂ →+* Matrix β β ℂ :=
    { toFun := fun X => C * X * C'
      map_one' := by rw [Matrix.mul_one, h1]
      map_mul' := fun X X' => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C', h2, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun X X' => by rw [Matrix.mul_add, Matrix.add_mul] }
  exact (NormedSpace.map_exp φ ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) Y).symm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_blocks (Z Z' : Matrix β β ℂ) :
    NormedSpace.exp (Matrix.fromBlocks Z 0 0 Z') = Matrix.fromBlocks (NormedSpace.exp Z) 0 0 (NormedSpace.exp Z') := by
  have : CompleteSpace (Matrix β β ℂ) := FiniteDimensional.complete ℝ _
  have : @CompleteSpace (Matrix β β ℂ × Matrix β β ℂ) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete ℝ _
  let φ : Matrix β β ℂ × Matrix β β ℂ →+* Matrix (β ⊕ β) (β ⊕ β) ℂ :=
    { toFun := fun X => Matrix.fromBlocks X.1 0 0 X.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun X X' => by simp [Matrix.fromBlocks_multiply]
      map_zero' := Matrix.fromBlocks_zero
      map_add' := fun X X' => by simp [Matrix.fromBlocks_add] }
  have := NormedSpace.map_exp φ (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd) (Z, Z')
  refine this.symm.trans ?_
  show Matrix.fromBlocks _ 0 0 _ = _
  rw [Prod.fst_exp, Prod.snd_exp]
  rfl

theorem trace_blocks (Z Z' : Matrix β β ℂ) : (Matrix.fromBlocks Z 0 0 Z').trace = Z.trace + Z'.trace := by
  simp [Matrix.trace]

theorem iff_K {b : ℂ} {M : Matrix β β ℂ} (hu : IsUnit ((b • M).map star).det) (g : Matrix β β ℂ) :
    gᴴ * (b • M).map star * g = (b • M).map star ↔ gᵀ * M * g.map star = M := by
  rcases isEmpty_or_nonempty β with h | h
  · exact iff_of_true (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hb : b ≠ 0 := fun e => by
    rw [e, zero_smul, Matrix.map_zero _ (star_zero _), Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have e : gᴴ * (b • M).map star * g = (b • (gᵀ * M * g.map star)).map star := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, map_star_mul, map_star_mul]
    congr 1
    ext i j
    simp
  rw [e, (Matrix.map_injective star_injective).eq_iff, (smul_right_injective _ hb).eq_iff]

theorem frame_K {R S : ℕ} {H : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ} (h : IsFrame H C) :
    (H.map star)ᴴ = H.map star ∧ IsUnit (H.map star).det := by
  obtain ⟨C', h1, h2⟩ := frame_inv h
  have e : H.map star = C'ᴴ * Jm R S * C' := by
    rw [← Jm_map_star, ← h.1, map_star_mul, map_star_mul, show Cᵀ.map star = Cᴴ from rfl,
      show (C.map star).map star = C by ext; simp]
    calc _ = (C * C')ᴴ * H.map star * (C * C') := by rw [h1]; simp
      _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  refine ⟨by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.mul_assoc],
    Matrix.isUnit_det_of_left_inverse (B := C * Jm R S * Cᴴ) ?_⟩
  calc _ = C * (Jm R S * (C' * C)ᴴ * Jm R S) * C' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.conjTranspose_one, Matrix.mul_one, Jm_mul_self, Matrix.mul_one, h1]

end Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
  {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
  {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
  {C : InfinitePlace F → Matrix β (Ix R S) ℂ}

theorem sB_frame (h : IsCMExt F E σ) (hfr : Framed τ JA JB a b A C) {u u' : Matrix α β (AE F E)}
    {c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ} (hc : ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ)
    (hc' : ∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) :
    sB σ JA JB u u' = ∑ w, 2 * (∑ l, Fock.tw1 (c w) l * star (Fock.tw1 (c' w) l)).im := by
  rw [sB, symp, Fock.trace_trace h τ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 := Fock.herm_frame (MA := JA.map (piInf (τ w))) (MB := JB.map (piInf (τ w))) hfr.1 (hfr.2.1 w) (hfr.2.2 w)
    (c w) (c' w)
  simp only [← hc, ← hc', Matrix.map_apply] at e2
  rw [← e2, hTens, neg_one_mul, map_neg, neg_re]
  simp only [map_sum, map_mul, piInf_cA h]
  ring

theorem fock_data (h : IsCMExt F E σ) (hfr : Framed τ JA JB a b A C) {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ}
    (hΦ : IsFockMap ψ τ d A C Φ) {D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)}
    (hD : ∀ u, At (evI F) u → ∀ f, SD (fun t => d.rho ψ (realAd F t • u)) f (D u f))
    {γ : Multiplicative ℝ →* UG (cA σ) JB} {Y : InfinitePlace F → Mat R S} (hY : IsGen τ C γ Y) :
    ∃ Z : InfinitePlace F → Matrix β β ℂ, (∀ w, (Z w).trace = (Y w).trace) ∧
      (∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = NormedSpace.exp (t • Z w)) ∧
      (∀ (t : ℝ) w, piInf (τ w) ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).det = cexp (t * (Y w).trace)) ∧
      (∀ w, (Y w).trace.re = 0) ∧
      ∃ u v : InfinitePlace F × (Ln P Q R S × Bool) → Matrix α β (AE F E), (∀ j, At (evI F) (u j)) ∧ (∀ j, At (evI F) (v j)) ∧
        (∀ x, At (evI F) x → ∀ w, x.map (piInf (τ w)) * (Z w)ᵀ = ∑ j, sB σ JA JB (v j) x • (u j).map (piInf (τ w))) ∧
        ∀ T, (8 * π * I : ℂ)⁻¹ • ∑ j, (D (u j) (D (v j) (Φ T)) + D (v j) (D (u j) (Φ T))) =
          Φ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  choose C' h1 h2 using fun w => frame_inv (hfr.2.2 w)
  choose A' a1 a2 using fun w => frame_inv (hfr.2.1 w)
  have hg : ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      C w * NormedSpace.exp (t • Y w) * C' w := fun t w => by rw [← hY, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hu : ∀ w, Y w ∈ upq R S := fun w => lie_of_exp _ _ fun t => (frame_iff_smul (hfr.2.2 w) (hY t w)).1 (by
    have := congrArg (fun X : Matrix β β (AE F E) => X.map (piInf (τ w))) (γ (Multiplicative.ofAdd t)).2
    simp only [map_form h] at this
    exact this)
  obtain ⟨L, -, hL, hL'⟩ := exists_lf h τ α β
  let U : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ → Matrix α β (AE F E) := fun w c =>
    L fun w' => A w' * (Pi.single w c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w' * (C w')ᵀ
  have hU : ∀ w c T, D (U w c) (Φ T) = Φ (atL w (heisOp c) T) := fun w c T => by
    rw [(actsLaws F κ _ _ (Φ _)).2.2.2.2 _ (hD _ (hL _) (Φ T)) (hΦ.2 _ (hL _) _ (hL' _) T)]
    congr 2
    rw [sumPl, Finset.sum_eq_single w (fun w' _ hw => by simp [atL_eq, hw, heisOp]) (by simp), atL_eq, Pi.single_eq_same]
  refine ⟨fun w => C w * Y w * C' w, fun w => by rw [Matrix.trace_mul_cycle, h2, Matrix.one_mul], fun t w => ?_,
    fun t w => ?_, fun w => ?_, fun j => U j.1 (cu (Y j.1) j.2), fun j => U j.1 (cv j.2), fun j => hL _, fun j => hL _,
    fun x hx w => ?_, fun T => ?_⟩
  · rw [hg, ← exp_conj' _ _ (h1 w) (h2 w), Matrix.mul_smul, Matrix.smul_mul]
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hg, Matrix.det_conj_of_mul_eq_one (h1 w) (h2 w),
      GlobalTheory.DetSqrtCover.det_exp, Matrix.trace_smul, real_smul]
  · rw [Matrix.trace, re_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrArg Complex.re (upq_entry (hu w) i i)
    rw [eps_sq] at this
    simp at this
    simp
    linarith
  · let c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ := fun w => A' w * x.map (piInf (τ w)) * (C' w)ᵀ
    have hc : ∀ w, x.map (piInf (τ w)) = A w * c w * (C w)ᵀ := fun w => by
      simp only [c, ← Matrix.mul_assoc, a1, Matrix.one_mul]
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.mul_one]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single w (fun w' _ hw => by simp [U, hL', hw.symm]) (by simp)]
    have e : ∀ j, sB σ JA JB (U w (cv j)) x = 2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im := fun j => by
      rw [sB_frame h hfr (hL' _) hc, Finset.sum_eq_single w (fun w' _ hw => by simp [hw, Fock.tw1]) (by simp),
        Pi.single_eq_same]
    simp only [e, U, hL', Pi.single_eq_same]
    rw [Finset.sum_congr rfl fun j _ => (by rw [Matrix.mul_smul, Matrix.smul_mul] :
      (2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im) • (A w * cu (Y w) j * (C w)ᵀ) =
        A w * ((2 * (∑ l, Fock.tw1 (cv j) l * star (Fock.tw1 (c w) l)).im) • cu (Y w) j) * (C w)ᵀ),
      ← Matrix.sum_mul, ← Matrix.mul_sum, ← expand, hc]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (C w)ᵀ, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.one_mul]
  · simp only [hU, ← map_add, ← map_sum, ← map_smul]
    congr 1
    rw [Fintype.sum_prod_type, sumPl, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [atL_eq, ← fock_eq (hu w)]
    simp only [map_smul, map_sum, map_add, atL_mul, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
      Module.End.mul_apply]

theorem sumPl_add (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (L : InfinitePlace F → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (s : InfinitePlace F → ℂ) (T : Tens F P Q R S) :
    Φ (sumPl (fun w => L w + s w • 1) T) = Φ (sumPl L T) + (∑ w, s w) • Φ T := by
  simp only [sumPl, atL_eq, map_add, map_smul, atL_one, Finset.sum_add_distrib, ← Finset.sum_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]

theorem exists_dbl {γ γ' : Multiplicative ℝ →* UG (cA σ) JB} (h : γ ∈ RLines σ JB) (h' : γ' ∈ RLines σ JB) :
    ∃ δ ∈ RLines σ (dbl JB), ∀ t, ((δ t).1 : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) =
      Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)) := by
  let φ : Matrix β β (AE F E) × Matrix β β (AE F E) →* Matrix (β ⊕ β) (β ⊕ β) (AE F E) :=
    { toFun := fun X => Matrix.fromBlocks X.1 0 0 X.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun X X' => by simp [Matrix.fromBlocks_multiply] }
  let δ0 : Multiplicative ℝ →* GL (β ⊕ β) (AE F E) := (Units.map φ).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp
    (((UG (cA σ) JB).subtype.comp γ).prod ((UG (cA σ) JB).subtype.comp γ')))
  have c1 : Continuous fun t => (γ t).1 := continuous_subtype_val.comp h.1
  have c2 : Continuous fun t => (γ' t).1 := continuous_subtype_val.comp h'.1
  have hc : Continuous δ0 := Units.continuous_iff.2
    ⟨(Units.continuous_val.comp c1).matrix_fromBlocks continuous_const continuous_const (Units.continuous_val.comp c2),
     (Units.continuous_coe_inv.comp c1).matrix_fromBlocks continuous_const continuous_const
      (Units.continuous_coe_inv.comp c2)⟩
  refine ⟨δ0.codRestrict _ fun t => ?_, ⟨hc.subtype_mk _, fun t u hu => ?_⟩, fun t => rfl⟩
  · have e1 : ((γ t).1 : Matrix β β (AE F E))ᵀ * JB * ((γ t).1 : Matrix β β (AE F E)).map (cA σ) = JB := (γ t).2
    have e2 : ((γ' t).1 : Matrix β β (AE F E))ᵀ * JB * ((γ' t).1 : Matrix β β (AE F E)).map (cA σ) = JB := (γ' t).2
    show (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)))ᵀ * dbl JB *
      (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E))).map (cA σ) = dbl JB
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  · show u • (Matrix.fromBlocks ((γ t).1 : Matrix β β (AE F E)) 0 0 ((γ' t).1 : Matrix β β (AE F E)) - 1) = 0
    have e1 := h.2 t u hu
    have e2 := h'.2 t u hu
    rw [smul_sub, sub_eq_zero] at e1 e2 ⊢
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, e1, e2]

theorem at_det {g : Matrix β β (AE F E)} (hg : At (evI F) (g - 1)) : At (evI F) (g.det - 1) := fun u hu => by
  let J : Ideal (AE F E) := LinearMap.ker (LinearMap.mul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) u))
  have hJ : ∀ x, x ∈ J ↔ u • x = 0 := fun x => by rw [Algebra.smul_def]; rfl
  rw [← hJ, ← Ideal.Quotient.eq, RingHom.map_det, map_one, ← Matrix.det_one (n := β),
    ← map_one (Ideal.Quotient.mk J).mapMatrix]
  congr 1
  ext i j
  exact Ideal.Quotient.eq.2 ((hJ _).2 (congrFun (congrFun (hg u hu) i) j))

theorem norm_eq_one (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {z : AE F E} (hz : At (evI F) (z - 1))
    (h1 : ∀ w, ‖piInf (τ w) z‖ = 1) : Algebra.norm (AF F) z = 1 := by
  obtain ⟨x, hx⟩ := exists_moved h
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact ρ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have hy : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ, neg_sub]
  have hy0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  obtain ⟨B, b0, b1⟩ := exists_basis h (β := x - σ x) (by
    rw [hy]
    exact fun e => hy0 (by linear_combination (-1 / 2 : E) * e))
  have hq : IsQuad (cA σ) ((1 : AF F) ⊗ₜ[F] (x - σ x)) :=
    ⟨(IsUnit.mk0 _ hy0).map (Algebra.TensorProduct.includeRight (R := F) (A := AF F)),
      by rw [← TensorProduct.tmul_neg, ← hy]; rfl,
      Algebra.TensorProduct.basis (AF F) B, by rw [Algebra.TensorProduct.basis_apply, b0]; rfl,
      by rw [Algebra.TensorProduct.basis_apply, b1]⟩
  refine hq.algebraMap_injective ?_
  rw [hq.algebraMap_norm, map_one, ← sub_eq_zero]
  refine eq_zero_of_piInf h τ _ (fun u hu => ?_) fun w => ?_
  · have e : z * cA σ z - 1 = (z - 1) * cA σ z + cA σ (z - 1) := by rw [map_sub, map_one]; ring
    rw [e, smul_add, ← smul_mul_assoc, ← map_smul, hz u hu, zero_mul, map_zero, add_zero]
  · rw [map_sub, map_mul, piInf_cA h, map_one, star_def, mul_conj, normSq_eq_norm_sq, h1]
    simp

theorem sB_anti (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (u v : Matrix α β (AE F E)) :
    sB σ JA JB u v = -sB σ JA JB v u := by
  rw [sB, sB, d.form, d.form, ← Fock.evIh_apply, ← Fock.evIh_apply, ← map_neg, ← map_neg, ← map_neg, ← map_neg, neg_neg,
    neg_sub]

theorem sB_neg (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (u v : Matrix α β (AE F E)) :
    sB σ JA JB (-u) v = -sB σ JA JB u v := by
  rw [sB, sB, d.form, d.form, ← Fock.evIh_apply, ← Fock.evIh_apply]
  simp only [map_neg, Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg, map_sub]
  ring

theorem sB_zero (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (v : Matrix α β (AE F E)) :
    sB σ JA JB 0 v = 0 := by
  have := sB_neg d 0 v
  rw [neg_zero] at this
  linarith

variable {dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)}

theorem sB_dbl (hdd : IsDblCoord (cA σ) (-1) JA JB d dd) (u u' v v' : Matrix α β (AE F E)) :
    sB σ JA (dbl JB) (Matrix.fromCols u u') (Matrix.fromCols v v') = sB σ JA JB u v - sB σ JA JB u' v' := by
  rw [sB, sB, sB, dd.form, d.form, d.form, hdd, hdd, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim,
    ← Fock.evIh_apply, ← Fock.evIh_apply, ← Fock.evIh_apply]
  simp only [dotProduct_neg, map_sub, map_add, map_neg]
  ring

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem at_cols {u u' : Matrix α β (AE F E)} (h : At (evI F) u) (h' : At (evI F) u') : At (evI F) (Matrix.fromCols u u') :=
  fun s hs => by
    ext i j
    rcases j with j | j
    · exact congrFun (congrFun (h s hs) i) j
    · exact congrFun (congrFun (h' s hs) i) j

theorem box_D (hdd : IsDblCoord (cA σ) (-1) JA JB d dd) {D Dd} (hD : IsD d D) (hDd : IsD dd Dd) {u : Matrix α β (AE F E)}
    (hu : At (evI F) u) {B : SInf F (κ ⊕ κ)} {f f' : SInf F κ} (hB : ∀ x, B x = f (x ∘ Sum.inl) * f' (x ∘ Sum.inr)) (x) :
    Dd (Matrix.fromCols u 0) B x = D u f (x ∘ Sum.inl) * f' (x ∘ Sum.inr) := by
  let L1 : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)
  let L2 : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inr i)
  have h1 := ((f.hasFDerivAt (L1 x)).comp x L1.hasFDerivAt).mul ((f'.hasFDerivAt (L2 x)).comp x L2.hasFDerivAt)
  have h2 : fderiv ℝ B x = _ := (congrArg (fderiv ℝ · x) (funext hB)).trans h1.fderiv
  have e1 : L1 (fun i => evI F ((Sum.elim (d.e u).1 0 : κ ⊕ κ → AF F) i)) = fun i => evI F ((d.e u).1 i) := rfl
  have e2 : L2 (fun i => evI F ((Sum.elim (d.e u).1 0 : κ ⊕ κ → AF F) i)) = 0 := funext fun _ => Der.evI_zero
  rw [hDd _ (at_cols hu fun _ _ => smul_zero _), hD u hu, hdd, h2, hB, map_zero]
  simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, e1, e2, map_zero, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    Der.evI_zero, mul_zero, Finset.sum_const_zero, add_zero, smul_eq_mul, Function.comp_apply]
  show _ + f' (x ∘ Sum.inr) * fderiv ℝ f (x ∘ Sum.inl) _ - _ = _
  ring

end PositivityTheory.RL.Up

namespace PositivityTheory.RL

open Up

example : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := lieFirst

end PositivityTheory.RL

end
end
