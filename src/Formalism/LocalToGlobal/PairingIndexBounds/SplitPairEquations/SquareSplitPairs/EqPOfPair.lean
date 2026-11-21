import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

def SplitPair (D : D7) : Prop :=
  ∀ (N' : ℕ) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N' → SD D L' → SD D L'' →
    ∀ n : 𝓞 D.host.E, n ≠ 0 → ∃ e : Matrix (Fin N') (Fin N') D.host.E,
      (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
      ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
          (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
        ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ M *ᵥ y = (n : D.host.E) • m

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

variable {D : D7}

theorem osmul {N : ℕ} (b : 𝓞 D.host.E) (v : Fin N → D.host.E) : b • v = (b : D.host.E) • v := rfl

theorem coe_ne {n : 𝓞 D.host.E} (hn : n ≠ 0) : (n : D.host.E) ≠ 0 := by
  intro h
  apply hn
  exact_mod_cast h

theorem mem_homL {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ TaylorLogMetric.homL D L L' ↔ ∀ x ∈ L, A *ᵥ x ∈ L' := by
  constructor
  · intro h
    unfold TaylorLogMetric.homL at h
    induction h using Submodule.span_induction with
    | mem B hB => exact hB
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [Matrix.add_mulVec]
      exact L'.add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [Matrix.smul_mulVec]
      exact L'.smul_mem c (hB x hx)
  · intro h
    exact Submodule.subset_span h

theorem homL_mul_pres {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {e : Matrix (Fin N') (Fin N') D.host.E}
    (he : ∀ y ∈ L', e *ᵥ y ∈ L') {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D L L') :
    e * A ∈ TaylorLogMetric.homL D L L' :=
  mem_homL.2 fun x hx => by
    rw [← Matrix.mulVec_mulVec]
    exact he _ (mem_homL.1 hA x hx)

theorem homL_mul_min {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    {n : 𝓞 D.host.E} (hn0 : n ≠ 0) (hn : ∀ u ∈ Lc, (n : D.host.E) • u ∈ La)
    (hM : ∀ y ∈ Lb, ∃ m ∈ Ld, M *ᵥ y = (n : D.host.E) • m)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D La Lb) : M * A ∈ TaylorLogMetric.homL D Lc Ld :=
  mem_homL.2 fun u hu => by
    obtain ⟨m, hm, hMm⟩ := hM _ (mem_homL.1 hA _ (hn u hu))
    have h1 : (n : D.host.E) • ((M * A) *ᵥ u) = (n : D.host.E) • m := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hMm]
    rw [smul_right_injective _ (coe_ne hn0) h1]
    exact hm

theorem yy_mul {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    (h : ∀ A ∈ TaylorLogMetric.homL D La Lb, M * A ∈ TaylorLogMetric.homL D Lc Ld) :
    ∀ B ∈ TaylorLogMetric.YYl D La Lb, M * B ∈ TaylorLogMetric.YYl D Lc Ld := by
  intro B hB
  unfold TaylorLogMetric.YYl at hB ⊢
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M * A, h A hA, by rw [Matrix.mul_smul]⟩
  | zero => simp
  | add B C _ _ hB hC =>
    rw [Matrix.mul_add]
    exact Submodule.add_mem _ hB hC
  | smul c B _ hB =>
    rw [Matrix.mul_smul]
    exact Submodule.smul_mem _ c hB

def phi {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => ∑ k, TaylorLogMetric.embT D τ (M i k) * z τ k j
  map_zero' := by funext τ i j; simp
  map_add' := by intro z w; funext τ i j; simp [mul_add, Finset.sum_add_distrib]

theorem phi_apply {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') (τ i j) :
    phi M z τ i j = ∑ k, TaylorLogMetric.embT D τ (M i k) * z τ k j := rfl

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem phi_embV {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) (w : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    phi M (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) = w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (M * A) := by
  funext τ i j
  simp only [phi_apply, Pi.smul_apply, smul_eq_mul, TaylorLogMetric.embV, TaylorLogMetric.tor0, Matrix.mul_apply, map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem phi_La {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    (h : ∀ B ∈ TaylorLogMetric.YYl D La Lb, M * B ∈ TaylorLogMetric.YYl D Lc Ld) :
    ∀ z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) La Lb, phi M z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Lc Ld := by
  intro z hz
  unfold TaylorLogMetric.La at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    rw [phi_embV]
    exact AddSubgroup.subset_closure ⟨w, hw, M * A, h A hA, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem phi_one {N N' : ℕ} (z : TaylorLogMetric.VC D N N') : phi (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ i j
  simp [phi_apply, Matrix.one_apply]

theorem phi_sub {N N' : ℕ} (M M' : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') :
    phi (M - M') z = phi M z - phi M' z := by
  funext τ i j
  simp [phi_apply, sub_mul, Finset.sum_sub_distrib]

theorem phi_mul {N N' : ℕ} (M M' : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') :
    phi (M * M') z = phi M (phi M' z) := by
  funext τ i j
  simp only [phi_apply, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : D7}

theorem sum_three_comm {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem formV_phi {N N' : ℕ} (A : ℝ) (M : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (phi M x) y =
      Ker.formV A D.what₂.Tau N N' x (phi (letI := D.host.cmStar; Mᴴ) y) := by
  let _ := D.host.cmStar
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, phi_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, conjTranspose_apply, embT_star']
  rw [sum_three_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_star]
  ring

variable (D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ)

def HH : Sesq (TaylorLogMetric.VC D N N') := Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'

def qq (x : TaylorLogMetric.VC D N N') : ℝ := Real.sqrt D.host.d / 2 * (HH D cc δ N N' x x).re

def cp (x y : TaylorLogMetric.VC D N N') : ℝ :=
  Real.sqrt D.host.d / 2 * ((HH D cc δ N N' x y).re + (HH D cc δ N N' y x).re)

def bet (x y : TaylorLogMetric.VC D N N') : ℝ := cp D cc δ N N' x y - (HH D cc δ N N' x y).im

def Good (x y : TaylorLogMetric.VC D N N') : Prop := ∃ k : ℤ, bet D cc δ N N' x y = 2 * k

variable {D cc δ N N'}

theorem qq_add (x y : TaylorLogMetric.VC D N N') :
    qq D cc δ N N' (x + y) = qq D cc δ N N' x + qq D cc δ N N' y + cp D cc δ N N' x y := by
  simp only [qq, cp, map_add, LinearMap.add_apply, Complex.add_re]
  ring

theorem bet_add_left (x x' y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (x + x') y = bet D cc δ N N' x y + bet D cc δ N N' x' y := by
  simp only [bet, cp, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem bet_add_right (x y y' : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' x (y + y') = bet D cc δ N N' x y + bet D cc δ N N' x y' := by
  simp only [bet, cp, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem bet_phi (e : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (phi e x) (phi e y) = bet D cc δ N N' x (phi (letI := D.host.cmStar; eᴴ * e) y) := by
  letI := D.host.cmStar
  have h1 : HH D cc δ N N' (phi e x) (phi e y) = HH D cc δ N N' x (phi (eᴴ * e) y) := by
    unfold HH
    rw [formV_phi, phi_mul]
  have h2 : HH D cc δ N N' (phi e y) (phi e x) = HH D cc δ N N' (phi (eᴴ * e) y) x := by
    unfold HH
    rw [formV_phi, formV_phi, ← phi_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  unfold bet cp
  rw [h1, h2]

theorem negpow (b : ℤ) : ((-1 : ℂ) ^ b) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [show (Real.pi : ℂ) * Complex.I * (b : ℂ) = (b : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem al_of_q {z : TaylorLogMetric.VC D N N'} {m : ℤ} (h : qq D cc δ N N' z = m) : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) z = (-1 : ℂ) ^ m := by
  show (-1 : ℂ) ^ (round (qq D cc δ N N' z)) = _
  rw [h, round_intCast]

theorem good_of_law {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy)
    (hlaw : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ))) :
    Good D cc δ N N' x y := by
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add,
    ← Complex.exp_add] at hlaw
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hlaw
  have hq := qq_add (D := D) (cc := cc) (δ := δ) x y
  rw [hx, hy, hxy] at hq
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h2 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h3 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * n := by
    exact_mod_cast h2
  simp only [bet, altE] at h3 ⊢
  linarith

theorem law_of_good {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy) (hg : Good D cc δ N N' x y) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ)) := by
  obtain ⟨k, hk⟩ := hg
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add,
    ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k, ?_⟩
  have hq := qq_add (D := D) (cc := cc) (δ := δ) x y
  rw [hx, hy, hxy] at hq
  simp only [bet] at hk
  have h4 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * k := by
    simp only [altE]
    linarith
  have h5 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * k := by
    exact_mod_cast h4
  rw [h5]
  ring

theorem good_of_lat {Y : AddSubgroup (TaylorLogMetric.VC D N N')} (hsc : IsSemiChar (HH D cc δ N N') Y (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)))
    (hq : ∀ z ∈ Y, ∃ m : ℤ, qq D cc δ N N' z = m) {x y : TaylorLogMetric.VC D N N'} (hx : x ∈ Y) (hy : y ∈ Y) :
    Good D cc δ N N' x y := by
  obtain ⟨mx, hmx⟩ := hq x hx
  obtain ⟨my, hmy⟩ := hq y hy
  obtain ⟨mxy, hmxy⟩ := hq (x + y) (Y.add_mem hx hy)
  exact good_of_law hmx hmy hmxy (hsc.2 x hx y hy)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

variable {D : D7}

theorem mul_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {m k : 𝓞 D.host.E}
    {v : Fin N → D.host.E} (h : (k : D.host.E) • v ∈ L₁) : ((m * k : 𝓞 D.host.E) : D.host.E) • v ∈ L₁ := by
  have e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v) := by
    rw [osmul, smul_smul]
    norm_cast
  rw [e]
  exact L₁.smul_mem m h

theorem exists_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) (x : Fin N → D.host.E) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (n : D.host.E) • x ∈ L₁ :=
  _root_.UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem hsp x

theorem exists_n_one {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : L.FG)
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ ∀ u ∈ L, (n : D.host.E) • u ∈ L₁ := by
  obtain ⟨s, hs⟩ := hL
  choose f hf0 hf using exists_smul_mem hsp
  refine ⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩
  intro u hu
  rw [← hs] at hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul s f hg]
    exact mul_smul_mem (hf g)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L₁.add_mem hx hy
  | smul c x _ hx =>
    rw [osmul c x, smul_comm, ← osmul]
    exact L₁.smul_mem c hx

theorem exists_n {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) (hL1 : SD D L₁) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (∀ u ∈ L, (n : D.host.E) • u ∈ L₁) ∧ ∀ u ∈ L₁, (n : D.host.E) • u ∈ L := by
  obtain ⟨hfg, hsp, -⟩ := hL
  obtain ⟨hfg1, hsp1, -⟩ := hL1
  obtain ⟨a, ha, h1⟩ := exists_n_one hfg hsp1
  obtain ⟨b, hb, h2⟩ := exists_n_one hfg1 hsp
  refine ⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩
  rw [mul_comm]
  exact mul_smul_mem (h2 u hu)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem good3 {a b c t : ℝ} (h : t = a + b + c) (ha : ∃ k : ℤ, a = 2 * k) (hb : ∃ k : ℤ, b = 2 * k)
    (hc : ∃ k : ℤ, c = 2 * k) : ∃ k : ℤ, t = 2 * k := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  obtain ⟨z, rfl⟩ := hc
  exact ⟨x + y + z, by rw [h]; push_cast; ring⟩

theorem sqSplit_of (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hP : SplitPair D) : Sq.SqSplit B := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  obtain ⟨n, hn0, hnL, hnL1⟩ := exists_n h1 h2
  obtain ⟨e, heL', heL'', hM⟩ := hP N' L' L'' hN' h3 h4 n hn0
  have hAdm : ∀ i : Bool × Bool, TaylorLogMetric.admitted D N N' (if i.1 then L₁ else L) (if i.2 then L'' else L') := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    · exact admissible_of_integral_conj_le hN hN' h1 h3
    · exact admissible_of_integral_conj_le hN hN' h1 h4
    · exact admissible_of_integral_conj_le hN hN' h2 h3
    · exact admissible_of_integral_conj_le hN hN' h2 h4
  have hq : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, ∃ m : ℤ, qq D cc δ N N' z = m := fun i z hz =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' _ _ (hAdm i) z hz
  have hsc : ∀ i, IsSemiChar (HH D cc δ N N') (Sq.sqFam B.tor L L₁ L' L'' i) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) :=
    fun i => ((B.latAll hcc hδ hδ0).1 N N' _ _ (hAdm i)).2
  have hn : ∀ a c : Bool, ∀ u ∈ (if c then L₁ else L), (n : D.host.E) • u ∈ (if a then L₁ else L) := by
    intro a c u hu
    cases a <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢
    · rw [← osmul]; exact L.smul_mem n hu
    · exact hnL1 u hu
    · exact hnL u hu
    · rw [← osmul]; exact L₁.smul_mem n hu
  have hor : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), y ∈ L' ∨ y ∈ L'' := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · exact Or.inl hy
    · exact Or.inr hy
  have hin : ∀ d : Bool, ∀ m, m ∈ L' → m ∈ L'' → m ∈ (if d then L'' else L') := by
    intro d m hm1 hm2
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hm1
    · exact hm2
  have he : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), e *ᵥ y ∈ (if b then L'' else L') := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
    · exact heL' y hy
    · exact heL'' y hy
  have hpres : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi e z ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro i z hz
    exact phi_La (yy_mul fun A hA => homL_mul_pres (he i.2) hA) z hz
  have hMin : ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
      ∀ i j, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi M z ∈ Sq.sqFam B.tor L L₁ L' L'' j := by
    intro M hMs i j z hz
    refine phi_La (yy_mul fun A hA => homL_mul_min hn0 (hn i.1 j.1) ?_ hA) z hz
    intro y hy
    obtain ⟨m, hm1, hm2, hm⟩ := hM M hMs y (hor i.2 y hy)
    exact ⟨m, hin j.2 m hm1 hm2, hm⟩
  have hM1 : e * e - e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert _ _
  have hM2 : (letI := D.host.cmStar; eᴴ) * e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hM3 : (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e) ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

  have hidem : ∀ x : TaylorLogMetric.VC D N N', phi e x - phi e (phi e x) = -(phi (e * e - e) x) := by
    intro x
    rw [phi_sub, phi_mul]
    abel
  have hone : ∀ x : TaylorLogMetric.VC D N N', x - phi e x = phi (1 - e) x := by
    intro x
    rw [phi_sub, phi_one]
  refine ⟨AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i),
    AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i), ?_⟩
  have hA : ∀ x, x ∈ AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, x - phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  have hA' : ∀ x, x ∈ AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx' i
    have := (Sq.sqFam B.tor L L₁ L' L'' i).add_mem ((hA x).1 hx i) ((hA' x).1 hx' i)
    rwa [sub_add_cancel] at this
  · intro i x hx
    refine ⟨phi e x, (hA _).2 fun j => ?_, x - phi e x, (hA' _).2 fun j => ?_, hpres i x hx,
      (Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hx (hpres i x hx), (add_sub_cancel _ _).symm⟩
    · rw [hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
    · rw [map_sub, hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (phi e x) (phi e y) +
        bet D cc δ N N' (phi e x) (y - phi e y) + bet D cc δ N N' (x - phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (phi e x) (x - phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (phi e x) (phi e y) (y - phi e y)
      rw [add_sub_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM2 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) (hpres i x hxi) ((hA y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA x).1 hx j) hyj
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (x - phi e x) (y - phi e y) +
        bet D cc δ N N' (x - phi e x) (phi e y) + bet D cc δ N N' (phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (x - phi e x) (phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (x - phi e x) (y - phi e y) (phi e y)
      rw [sub_add_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [hone x, hone y, bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM3 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) ((Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hxi ((hA' x).1 hx i)) ((hA' y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA' x).1 hx j) hyj

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of_pair (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hP : SplitPair D) : B.EqP χ :=
  eqP_top B hcc hδ hδ0 hS χ hχ (sqSplit_of B hcc hδ hδ0 hP)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end
