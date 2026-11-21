import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
import ReciprocityTheory.SemistableReduction.AlgAll
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerAeval
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain TensorProduct

theorem isDer_tensor {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing M] [Algebra R M]
    (d : A →ₗ[R] A) (hd : IsDer d) : IsDer (TensorProduct.map d (LinearMap.id : M →ₗ[R] M)) := by
  refine ⟨fun x y => map_add _ x y, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b n =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      rw [hd.mul, TensorProduct.add_tmul, mul_comm n m]
    | add y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, mul_add]
      ring
  | add x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, add_mul]
    ring

theorem der_div_eq_zero {L : Type*} [Field L] {δ : L → L} (h : IsDer δ) {x y : L} (hx : δ x = 0) (hy : δ y = 0) :
    δ (x / y) = 0 := by
  by_cases hy0 : y = 0
  · rw [hy0, div_zero, h.der_zero]
  · have e := h.mul (x / y) y
    rw [div_mul_cancel₀ x hy0, hx, hy, mul_zero, zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hy0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

theorem exists_derKp (p : Idx D j N) : ∃ δ : Kp X la N → Kp X la N, IsDer δ ∧
    (∀ f : Pol X la N, δ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f))) ∧
    ∀ c : X.Kl la, δ (algebraMap (X.Kl la) (Kp X la N) c) = 0 := by
  obtain ⟨δ, hδ, hf⟩ := IsDer.ofLoc (gI X la N).primeCompl
    (fun f => algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f))
    (fun x y => by simp only [map_add])
    (fun x y => by simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul])
  obtain ⟨δ', hδ', h'⟩ := IsDer.ofLoc (nonZeroDivisors (Op X la N))
    (fun z => algebraMap (Op X la N) (Kp X la N) (δ z))
    (fun x y => by simp only [hδ.add, map_add]) (fun x y => by simp only [hδ.mul, map_add, map_mul])
  have hval : ∀ f : Pol X la N, δ' (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f)) := by
    intro f
    rw [h', hf]
  have hOl : ∀ a : X.Ol la, δ' (algebraMap (X.Ol la) (Kp X la N) a) = 0 := by
    intro a
    have e : algebraMap (X.Ol la) (Kp X la N) a =
        algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C a)) := by
      rw [IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N),
        IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N), MvPolynomial.algebraMap_eq]
    rw [e, hval, MvPolynomial.pderiv_C, map_zero, map_zero]
  refine ⟨δ', hδ', hval, fun c => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.Ol la) c
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact der_div_eq_zero hδ' (hOl a) (hOl b)

def dK (p : Idx D j N) : Kp X la N → Kp X la N := Classical.choose (exists_derKp X la N p)

theorem dK_isDer (p : Idx D j N) : IsDer (dK X la N p) := (Classical.choose_spec (exists_derKp X la N p)).1

theorem dK_pol (p : Idx D j N) (f : Pol X la N) :
    dK X la N p (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) f)) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f)) :=
  (Classical.choose_spec (exists_derKp X la N p)).2.1 f

theorem dK_Kl (p : Idx D j N) (c : X.Kl la) : dK X la N p (algebraMap (X.Kl la) (Kp X la N) c) = 0 :=
  (Classical.choose_spec (exists_derKp X la N p)).2.2 c

theorem dK_Tv (p q : Idx D j N) :
    dK X la N p (algebraMap (Op X la N) (Kp X la N) (Tv X la N q)) = if q = p then 1 else 0 := by
  classical
  have := dK_pol X la N p (MvPolynomial.X q)
  rw [MvPolynomial.pderiv_X, Pi.single_apply] at this
  rw [show Tv X la N q = algebraMap (Pol X la N) (Op X la N) (MvPolynomial.X q) from rfl, this]
  split_ifs <;> simp

def dKl (p : Idx D j N) : Kp X la N →ₗ[X.Kl la] Kp X la N where
  toFun := dK X la N p
  map_add' := (dK_isDer X la N p).add
  map_smul' c x := by
    rw [Algebra.smul_def, (dK_isDer X la N p).mul, dK_Kl, mul_zero, add_zero, RingHom.id_apply, Algebra.smul_def]

def dR (p : Idx D j N) : Rp X la N → Rp X la N := fun r =>
  TensorProduct.map (dKl X la N p) (LinearMap.id : X.Vl la →ₗ[X.Kl la] X.Vl la) r

theorem dR_isDer (p : Idx D j N) : IsDer (dR X la N p) :=
  isDer_tensor (dKl X la N p) (dK_isDer X la N p)

theorem dR_algebraMap (p : Idx D j N) (c : Kp X la N) :
    dR X la N p (algebraMap (Kp X la N) (Rp X la N) c) = algebraMap (Kp X la N) (Rp X la N) (dK X la N p c) := by
  show TensorProduct.map (dKl X la N p) LinearMap.id (c ⊗ₜ[X.Kl la] (1 : X.Vl la)) = dK X la N p c ⊗ₜ[X.Kl la] (1 : X.Vl la)
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem dR_emb (p : Idx D j N) (F : X.Forms) : dR X la N p (emb X la N F) = 0 := by
  show TensorProduct.map (dKl X la N p) LinearMap.id ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = 0
  rw [TensorProduct.map_tmul]
  show dK X la N p 1 ⊗ₜ[X.Kl la] _ = 0
  rw [(dK_isDer X la N p).der_one, TensorProduct.zero_tmul]

theorem dR_smul (p : Idx D j N) (c : Kp X la N) (r : Rp X la N) :
    dR X la N p (c • r) = dK X la N p c • r + c • dR X la N p r := by
  rw [Algebra.smul_def, (dR_isDer X la N p).mul, dR_algebraMap, Algebra.smul_def, Algebra.smul_def]
  ring

theorem dR_Vw (p : Idx D j N) (u : WeightFamilies.Wt D j) {r : Rp X la N} (hr : r ∈ Vw X la N u) :
    dR X la N p r ∈ Vw X la N u := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, rfl⟩ := hx
    rw [dR_emb]
    exact Submodule.zero_mem _
  | zero => rw [(dR_isDer X la N p).der_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [(dR_isDer X la N p).add]; exact Submodule.add_mem _ hx hy
  | smul c x hx0 hx =>
    rw [dR_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx0) (Submodule.smul_mem _ _ hx)

section Sec

variable {X la N} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem dR_sec (l : Fin N) (i : Fin (WeightFamilies.dimY D j + 1)) :
    dR X la N (0, l) (sec X la w i) = if i = 0 then emb X la N (X.inc wL (w l)) else 0 := by
  classical
  unfold sec
  rw [(dR_isDer X la N (0, l)).der_sum]
  simp only [dR_smul, dR_emb, smul_zero, add_zero, dK_Tv, Prod.mk.injEq]
  split_ifs with hi
  · subst hi
    simp
  · simp [hi]

end Sec

section Lw

variable {N} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (l : Fin N)

theorem exists_derLw : ∃ δ : Lw X la w → Lw X la w, IsDer δ ∧
    ∀ r, δ (algebraMap (Rp X la N) (Lw X la w) r) = algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r) :=
  IsDer.ofLoc (Submonoid.powers (sec X la w 0)) (fun r => algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r))
    (fun x y => by simp only [(dR_isDer X la N (0, l)).add, map_add])
    (fun x y => by simp only [(dR_isDer X la N (0, l)).mul, map_add, map_mul])

def dL : Lw X la w → Lw X la w := Classical.choose (exists_derLw X la w l)

theorem dL_isDer : IsDer (dL X la w l) := (Classical.choose_spec (exists_derLw X la w l)).1

theorem dL_alg (r : Rp X la N) :
    dL X la w l (algebraMap (Rp X la N) (Lw X la w) r) = algebraMap (Rp X la N) (Lw X la w) (dR X la N (0, l) r) :=
  (Classical.choose_spec (exists_derLw X la w l)).2 r

theorem dL_w0inv : dL X la w l (w0inv X la w) =
    -(w0inv X la w ^ 2 * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w l)))) := by
  have h := section_mul_inverse_eq_one X la w
  have e1 := (dL_isDer X la w l).mul (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0)) (w0inv X la w)
  rw [h, (dL_isDer X la w l).der_one, dL_alg, dR_sec, if_pos rfl] at e1
  linear_combination (-(w0inv X la w)) * e1 - dL X la w l (w0inv X la w) * h

theorem dL_w0inv_pow (k : ℕ) : dL X la w l (w0inv X la w ^ k) =
    -((k : Lw X la w) * w0inv X la w ^ (k + 1) * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w l)))) := by
  cases k with
  | zero => simp [(dL_isDer X la w l).der_one]
  | succ k =>
    rw [(dL_isDer X la w l).der_pow_succ, dL_w0inv]
    push_cast
    ring

theorem dL_frac (k : ℕ) (g : Rp X la N) : dL X la w l (frac X la w k g) =
    frac X la w k (dR X la N (0, l) g) - (k : Lw X la w) * frac X la w (k + 1) (emb X la N (X.inc wL (w l)) * g) := by
  rw [frac_apply, frac_apply, frac_apply, (dL_isDer X la w l).mul, dL_w0inv_pow, dL_alg, map_mul]
  ring

theorem mem_Frac0_emb (k : Fin N) :
    frac X la w 1 (emb X la N (X.inc wL (w k))) ∈ Frac0 X la w :=
  Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)))

theorem dL_mem {x : Lw X la w} (hx : x ∈ Frac0 X la w) : dL X la w l x ∈ Frac0 X la w := by
  rw [mem_Frac0] at hx ⊢
  obtain ⟨k, g, hg, rfl⟩ := (mem_Hfr X la w).1 hx
  rw [dL_frac]
  refine Submodule.sub_mem _ (frac_mem_Hfr X la w (dR_Vw X la N (0, l) _ hg)) ?_
  rw [← nsmul_eq_mul]
  refine nsmul_mem (frac_mem_Hfr X la w ?_) k
  have := mul_mem_Vw X la N (emb_mem_Vw X la N wL (w l)) hg
  rwa [wadd_addL] at this

def dF : Frac0 X la w → Frac0 X la w := fun x => ⟨dL X la w l x, dL_mem X la w l x.2⟩

theorem dF_isDer : IsDer (dF X la w l) :=
  ⟨fun x y => Subtype.ext ((dL_isDer X la w l).add x y), fun x y => Subtype.ext ((dL_isDer X la w l).mul x y)⟩

def xr (k : Fin N) : Frac0 X la w := ⟨frac X la w 1 (emb X la N (X.inc wL (w k))), mem_Frac0_emb X la w k⟩

theorem dF_xr (k : Fin N) : dF X la w l (xr X la w k) = -(xr X la w k * xr X la w l) := by
  apply Subtype.ext
  show dL X la w l (frac X la w 1 (emb X la N (X.inc wL (w k)))) =
    -(frac X la w 1 (emb X la N (X.inc wL (w k))) * frac X la w 1 (emb X la N (X.inc wL (w l))))
  rw [dL_frac, dR_emb, map_zero, zero_sub, frac_mul, Nat.cast_one, one_mul, mul_comm (emb X la N _)]

theorem dF_algebraMap (c : Kp X la N) :
    dF X la w l (algebraMap (Kp X la N) (Frac0 X la w) c) = algebraMap (Kp X la N) (Frac0 X la w) (dK X la N (0, l) c) := by
  apply Subtype.ext
  show dL X la w l (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) (dK X la N (0, l) c)
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), dL_alg, dR_algebraMap,
    ← IsScalarTower.algebraMap_apply]

theorem dF_Jid {x : Frac0 X la w} (hx : x ∈ Jid X la w) : dF X la w l x ∈ Jid X la w := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have e : dF X la w l (sfr X la w i.succ) = -(sfr X la w i.succ * ⟨frac X la w 1 (emb X la N (X.inc wL (w l))),
        mem_Frac0_emb X la w l⟩) := by
      apply Subtype.ext
      show dL X la w l (frac X la w 1 (sec X la w i.succ)) = -(frac X la w 1 (sec X la w i.succ) *
        frac X la w 1 (emb X la N (X.inc wL (w l))))
      rw [dL_frac, dR_sec, if_neg (Fin.succ_ne_zero i), map_zero, zero_sub, frac_mul, Nat.cast_one, one_mul,
        mul_comm (emb X la N _)]
    rw [e]
    exact neg_mem (Ideal.mul_mem_right _ _ (sfr_succ_mem_Jid X la w i))
  | zero => rw [(dF_isDer X la w l).der_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [(dF_isDer X la w l).add]; exact Ideal.add_mem _ hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, (dF_isDer X la w l).mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

theorem exists_derOsK : ∃ δ : OsK X la w → OsK X la w, IsDer δ ∧
    ∀ x, δ (toOsK X la w x) = toOsK X la w (dF X la w l x) := by
  obtain ⟨δ, hδ, h⟩ := (dF_isDer X la w l).quot (Jid X la w) (fun x hx => dF_Jid X la w l hx)
  exact ⟨δ, hδ, fun x => h x⟩

theorem sum_T0_mul_ratio_eq_one : ∑ k, algebraMap (Kp X la N) (Frac0 X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
    xr X la w k = 1 := by
  have e : ∀ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
      frac X la w 1 (emb X la N (X.inc wL (w k))) = frac X la w 1
        ((algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) • emb X la N (X.inc wL (w k))) := by
    intro k
    rw [LinearMap.map_smul, Algebra.smul_def]
  have hL : ∑ k, algebraMap (Kp X la N) (Lw X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k))) *
      frac X la w 1 (emb X la N (X.inc wL (w k))) = 1 := by
    simp_rw [e]
    rw [← map_sum]
    show frac X la w 1 (sec X la w 0) = 1
    rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  apply Subtype.ext
  show (Frac0 X la w).val (∑ k, _) = (Frac0 X la w).val 1
  rw [map_sum, map_one]
  simp only [map_mul, AlgHom.commutes]
  exact hL

end Lw

end Formalism.L2.Pj.GenericSectionMinimum
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

open IsLocalRing Cardinal

section Fld

variable {F : Type} [Field F]

def constField (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) : IntermediateField K F where
  carrier := {x | δ x = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [h.mul, ha, hb, mul_zero, mul_zero, add_zero]
  one_mem' := h.der_one
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [h.add, ha, hb, add_zero]
  zero_mem' := h.der_zero
  algebraMap_mem' c := hK c
  inv_mem' x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]; exact h.der_zero
    · have e := h.mul x x⁻¹
      rw [mul_inv_cancel₀ hx0, h.der_one, hx, mul_zero, add_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_left hx0

theorem kill_adjoin (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) (s : Set F) (hs : ∀ x ∈ s, δ x = 0) :
    ∀ x ∈ IntermediateField.adjoin K s, δ x = 0 := by
  intro x hx
  have hle : IntermediateField.adjoin K s ≤ constField K h hK :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => hs y hy)
  exact hle hx

theorem der_aeval {δ : F → F} (h : IsDer δ) {E : Type} [CommRing E] [Algebra E F]
    (hE : ∀ e, δ (algebraMap E F e) = 0) {σ : Type} [Fintype σ] [DecidableEq σ] (t : σ → F)
    (P : MvPolynomial σ E) :
    δ (MvPolynomial.aeval t P) = ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * δ (t i) := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp [hE]
  next p q hp hq =>
    simp only [map_add, h.add, hp, hq, add_mul, Finset.sum_add_distrib]
  next p n hp =>
    have hsingle : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial σ E)) =
        if i = n then 1 else 0 := by
      intro i
      by_cases hi : i = n
      · subst hi
        simp
      · simp [MvPolynomial.pderiv_X, Pi.single_apply, hi, Ne.symm hi]
    simp only [map_mul, MvPolynomial.aeval_X, h.mul, hp, MvPolynomial.pderiv_mul, map_add, hsingle,
      add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem totalDegree_pderiv_lt {E : Type} [CommRing E] {σ : Type} (p : MvPolynomial σ E) (i : σ)
    (h : MvPolynomial.pderiv i p ≠ 0) : (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp h)
  have key : ∀ m ∈ (MvPolynomial.pderiv i p).support, (m.sum fun _ e => e) + 1 ≤ p.totalDegree := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hs : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have hle := MvPolynomial.le_totalDegree hs
    rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at hle
  have h1 := key m hm
  have h2 : (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    apply Finset.sup_le
    intro s hs
    have := key s hs
    omega
  omega

theorem algIndep_of_der {E : Type} [Field E] [CharZero E] [Algebra E F] {N : ℕ} (t : Fin N → F)
    (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l)) (hE : ∀ l e, δ l (algebraMap E F e) = 0)
    (ht : ∀ l k, δ l (t k) = if k = l then 1 else 0) : AlgebraicIndependent E t := by
  classical
  have main : ∀ n : ℕ, ∀ P : MvPolynomial (Fin N) E, P.totalDegree ≤ n →
      MvPolynomial.aeval t P = 0 → P = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih P hd hP
    have hder : ∀ l, MvPolynomial.pderiv l P = 0 := by
      intro l
      by_contra hne
      have hlt := totalDegree_pderiv_lt P l hne
      apply hne
      refine ih _ (lt_of_lt_of_le hlt hd) (MvPolynomial.pderiv l P) le_rfl ?_
      have hz := der_aeval (hδ l) (hE l) t P
      rw [hP, (hδ l).der_zero] at hz
      simpa [ht] using hz.symm
    have hdeg0 : P.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro s hs
      by_contra hpos
      obtain ⟨l, hl⟩ : ∃ l, s l ≠ 0 := by
        by_contra hall
        push_neg at hall
        have h0 : s = 0 := Finsupp.ext fun a => by simp [hall a]
        simp [h0] at hpos
      have hs' : s - Finsupp.single l 1 + Finsupp.single l 1 = s := by
        ext j
        by_cases hj : j = l
        · subst hj
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same]
          omega
        · simp [Finsupp.single_apply, Ne.symm hj]
      have hc := MvPolynomial.coeff_pderiv (i := l) P (s - Finsupp.single l 1)
      rw [hder l, MvPolynomial.coeff_zero, hs'] at hc
      rw [MvPolynomial.mem_support_iff] at hs
      have h2 : (((s - Finsupp.single l 1 : Fin N →₀ ℕ) l : ℕ) : E) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
      exact hs ((mul_eq_zero.mp hc.symm).resolve_right h2)
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdeg0
    rw [hdeg0, MvPolynomial.aeval_C] at hP
    have hc0 : MvPolynomial.coeff 0 P = 0 := (map_eq_zero (algebraMap E F)).mp hP
    rw [hdeg0, hc0, MvPolynomial.C_0]
  exact (injective_iff_map_eq_zero (MvPolynomial.aeval (R := E) t)).mpr fun P hP => main _ P le_rfl hP

end Fld

theorem gauss_indep {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] [Algebra K U]
    [IsScalarTower K Ω U] (V : ValuationSubring U) (T : τ → U) (hT : ∀ q, T q ∈ V)
    (hG : ∀ Q : MvPolynomial τ K, (∀ α, V.valuation (algebraMap K U (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K U (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
      ((algebraMap _ (ResidueField V)).comp (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue V ⟨T j, hT j⟩) := by
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI _ia : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
    ((algebraMap _ (ResidueField V)).comp
      (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  classical
  have f0def : ∀ x : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω),
      (((ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
        (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) x : V) : U) =
        algebraMap K U (x : K) := by
    intro x
    show algebraMap Ω U (algebraMap K Ω (x : K)) = _
    exact (IsScalarTower.algebraMap_apply K Ω U _).symm
  have hcomp : ∀ x : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω),
      algebraMap (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V)
        (residue _ x) =
      residue V ((ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
        (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) x) := by
    intro x
    simp only [_ia, _iW, _io, ReciprocityTheory.MultiplicativeHeights.residueAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] <;> rfl
  set f0 := (ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
    (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) with hf0
  refine (injective_iff_map_eq_zero (MvPolynomial.aeval
    (R := ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
    (fun j => residue V ⟨T j, hT j⟩))).mpr ?_
  intro R hR
  by_contra hR0
  obtain ⟨Q', rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective R
  have hqU : ((MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q' : V) : U) =
      MvPolynomial.aeval T
        (MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q') := by
    have e1 := MvPolynomial.eval₂_comp_left V.subtype f0 (fun j => (⟨T j, hT j⟩ : V)) Q'
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e2 : V.subtype.comp f0 =
        (algebraMap K U).comp ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype :=
      RingHom.ext fun x => f0def x
    rw [← e2]
    exact e1
  have hres : residue V (MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q') =
      MvPolynomial.aeval (fun j => residue V ⟨T j, hT j⟩) (MvPolynomial.map (residue _) Q') := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e1 := MvPolynomial.eval₂_comp_left (residue V) f0 (fun j => (⟨T j, hT j⟩ : V)) Q'
    have e2 : (residue V).comp f0 =
        (algebraMap (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (ResidueField V)).comp (residue _) :=
      RingHom.ext fun x => (hcomp x).symm
    rw [← e2]
    exact e1
  have hlt : V.valuation ((MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q' : V) : U) < 1 := by
    rw [← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, hres]
    exact hR
  have hc : ∀ α, (MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α =
      ((Q'.coeff α : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω)) : K) := fun α =>
    MvPolynomial.coeff_map _ _ _
  have hle : ∀ α, V.valuation (algebraMap K U
      ((MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α)) ≤ 1 := by
    intro α
    rw [hc, ← f0def]
    exact V.valuation_le_one _
  have hex : ∃ α, V.valuation (algebraMap K U
      ((MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α)) = 1 := by
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hR0
    refine ⟨α, ?_⟩
    rw [MvPolynomial.coeff_map] at hα
    have hu : IsUnit (Q'.coeff α) := by
      by_contra hnu
      apply hα
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
    rw [hc, ← f0def]
    exact (V.valuation_eq_one_iff _).mp (hu.map f0)
  have h1 := hG _ hle hex
  rw [← hqU] at h1
  rw [h1] at hlt
  exact lt_irrefl _ hlt

theorem gauss_direct {F K : Type} [Field F] [Field K] [CharZero K] [Algebra K F] (D N : ℕ)
    (T : Fin (D + 1) × Fin N → F) (y : Fin N → F) (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l))
    (hδK : ∀ l c, δ l (algebraMap K F c) = 0) (hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0)
    (hδs : ∀ l (i : Fin D) k, δ l (T (i.succ, k)) = 0) (hδy : ∀ l k, δ l (y k) = -(y k * y l))
    (h1 : ∑ k, T (0, k) * y k = 1)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range T)) F)
    (V : ValuationSubring F)
    (hG : ∀ Q : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, V.valuation (algebraMap K F (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K F (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    ∀ k, y k ∈ V := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  have hT1 : ∀ q, V.valuation (T q) = 1 := by
    intro q
    have := hG (MvPolynomial.X q) (fun α => ?_) ⟨Finsupp.single q 1, ?_⟩
    · simpa using this
    · rw [MvPolynomial.coeff_X']
      split_ifs <;> simp
    · rw [MvPolynomial.coeff_X', if_pos rfl]
      simp
  have hTV : ∀ q, T q ∈ V := fun q => (V.valuation_le_one_iff _).1 (hT1 q).le

  have hTind : AlgebraicIndependent K T := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    by_contra hQ0
    have hne : Q.support.Nonempty := by
      obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hQ0
      exact ⟨β, MvPolynomial.mem_support_iff.mpr hβ⟩
    obtain ⟨α, hα, hmax⟩ := Q.support.exists_max_image (fun β => V.valuation (algebraMap K F (Q.coeff β))) hne
    have hc : Q.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    have hvc : V.valuation (algebraMap K F (Q.coeff α)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]
      exact (map_ne_zero _).2 hc
    have key := hG (MvPolynomial.C (Q.coeff α)⁻¹ * Q) (fun β => ?_) ⟨α, ?_⟩
    · rw [map_mul, hQ, mul_zero, Valuation.map_zero] at key
      exact zero_ne_one key
    · rw [MvPolynomial.coeff_C_mul, map_mul, Valuation.map_mul, map_inv₀, Valuation.map_inv]
      by_cases hβ : β ∈ Q.support
      · calc (V.valuation (algebraMap K F (Q.coeff α)))⁻¹ * V.valuation (algebraMap K F (Q.coeff β))
            ≤ (V.valuation (algebraMap K F (Q.coeff α)))⁻¹ * V.valuation (algebraMap K F (Q.coeff α)) :=
              by gcongr; exact hmax β hβ
          _ = 1 := inv_mul_cancel₀ hvc
      · rw [MvPolynomial.notMem_support_iff.mp hβ, map_zero, Valuation.map_zero, mul_zero]
        exact zero_le'
    · rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, map_one, Valuation.map_one]

  have hN : ∃ k, y k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at h1
  obtain ⟨j0, -, hj0⟩ := Finset.univ.exists_max_image (fun k => V.valuation (y k))
    (by obtain ⟨k, -⟩ := hN; exact ⟨k, Finset.mem_univ _⟩)
  have hy0 : y j0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hN
    intro h0
    have := hj0 k (Finset.mem_univ _)
    rw [h0, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hk this
  let a : Fin N → F := fun k => y k / y j0
  have haV : ∀ k, V.valuation (a k) ≤ 1 := by
    intro k
    show V.valuation (y k / y j0) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ (hj0 k (Finset.mem_univ _)) zero_le'
  have ha0 : a j0 = 1 := div_self hy0
  have hay : ∀ k, a k * y j0 = y k := fun k => div_mul_cancel₀ _ hy0
  have hδa : ∀ l k, δ l (a k) = 0 := by
    intro l k
    have e := (hδ l).mul (a k) (y j0)
    rw [hay, hδy, hδy] at e
    have e2 : y j0 * δ l (a k) = 0 := by linear_combination (-1 : F) * e + y l * hay k
    exact (mul_eq_zero.mp e2).resolve_left hy0

  let sE : Set F := Set.range (fun q : Fin D × Fin N => T (q.1.succ, q.2)) ∪ Set.range a
  let E : IntermediateField K F := IntermediateField.adjoin K sE
  have hδE : ∀ l (e : E), δ l (algebraMap E F e) = 0 := by
    intro l e
    show δ l (e : F) = 0
    refine kill_adjoin K (hδ l) (hδK l) sE ?_ e e.2
    rintro x (⟨q, rfl⟩ | ⟨k, rfl⟩)
    · exact hδs l q.1 q.2
    · exact hδa l k
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hT0ind : AlgebraicIndependent E (fun k => T (0, k)) :=
    algIndep_of_der _ δ hδ hδE (fun l k => hδ0 l k)

  have hmemT : ∀ (i : Fin D) k, T (i.succ, k) ∈ E := fun i k =>
    IntermediateField.subset_adjoin K sE (Set.mem_union_left _ ⟨(i, k), rfl⟩)
  have hmema : ∀ k, a k ∈ E := fun k =>
    IntermediateField.subset_adjoin K sE (Set.mem_union_right _ ⟨k, rfl⟩)
  haveI : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).mpr (algebraMap K E).injective
  haveI : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr (algebraMap E F).injective
  have hadd : Algebra.trdeg K E + Algebra.trdeg E F ≤ Algebra.trdeg K F := trdeg_add_le
  have htF : Algebra.trdeg K F ≤ (((D + 1) * N : ℕ) : Cardinal) := by
    haveI := halg
    calc Algebra.trdeg K F ≤ #(Set.range T) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range T)
      _ ≤ #(Fin (D + 1) × Fin N) := Cardinal.mk_range_le
      _ = (((D + 1) * N : ℕ) : Cardinal) := by simp [Cardinal.mk_fintype]
  have hEF : ((N : ℕ) : Cardinal) ≤ Algebra.trdeg E F := by
    simpa using hT0ind.cardinalMk_le_trdeg
  let t' : Fin D × Fin N → E := fun q => ⟨T (q.1.succ, q.2), hmemT q.1 q.2⟩
  have ht' : AlgebraicIndependent K t' := by
    have hinj : Function.Injective (fun q : Fin D × Fin N => ((q.1.succ, q.2) : Fin (D + 1) × Fin N)) := by
      intro u v huv
      have h' : ((u.1.succ, u.2) : Fin (D + 1) × Fin N) = (v.1.succ, v.2) := huv
      obtain ⟨h1', h2'⟩ := Prod.mk.inj h'
      exact Prod.ext_iff.2 ⟨Fin.succ_injective _ h1', h2'⟩
    exact AlgebraicIndependent.of_comp E.val (hTind.comp _ hinj)
  have hlow : (((D * N : ℕ)) : Cardinal) ≤ Algebra.trdeg K E := by
    simpa using ht'.cardinalMk_le_trdeg
  have hfin : Algebra.trdeg K E < ℵ₀ :=
    lt_of_le_of_lt (le_self_add.trans ((add_le_add le_rfl hEF).trans (hadd.trans htF)))
      Cardinal.natCast_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hfin
  have hle : n + N ≤ (D + 1) * N := by
    have := (add_le_add le_rfl hEF).trans (hadd.trans htF)
    rw [hn] at this
    exact_mod_cast this
  have hge : D * N ≤ n := by
    rw [hn] at hlow
    exact_mod_cast hlow
  have htr : Algebra.trdeg K E = ((D * N : ℕ) : Cardinal) := by
    rw [hn]
    congr 1
    have e : (D + 1) * N = D * N + N := by ring
    rw [e] at hle
    exact le_antisymm (Nat.le_of_add_le_add_right hle) hge

  let u : Fin (D + 1) × Fin N → V := fun q => ⟨T q, hTV q⟩
  let p : Fin (D + 1) × Fin N → MvPolynomial (Fin N) E := fun q =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin N) E) (MvPolynomial.X q.2)
      (fun i => MvPolynomial.C (⟨T (i.succ, q.2), hmemT i q.2⟩ : E)) q.1
  have hp : ∀ q α, (p q).coeff α ∈ V.comap (algebraMap E F) := by
    rintro ⟨i, k⟩ α
    induction i using Fin.cases with
    | zero =>
      show (MvPolynomial.X k : MvPolynomial (Fin N) E).coeff α ∈ V.comap (algebraMap E F)
      rw [MvPolynomial.coeff_X']
      split_ifs
      · exact (V.comap (algebraMap E F)).one_mem
      · exact (V.comap (algebraMap E F)).zero_mem
    | succ i =>
      show (MvPolynomial.C (⟨T (i.succ, k), hmemT i k⟩ : E)).coeff α ∈ V.comap (algebraMap E F)
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact hTV _
      · exact (V.comap (algebraMap E F)).zero_mem
  have hpu : ∀ q, MvPolynomial.aeval (fun s => T (0, s)) (p q) = (u q : F) := by
    rintro ⟨i, k⟩
    induction i using Fin.cases with
    | zero =>
      show MvPolynomial.aeval (fun s => T (0, s)) (MvPolynomial.X k : MvPolynomial (Fin N) E) = T (0, k)
      rw [MvPolynomial.aeval_X]
    | succ i =>
      show MvPolynomial.aeval (fun s => T (0, s)) (MvPolynomial.C (⟨T (i.succ, k), hmemT i k⟩ : E)) = T (i.succ, k)
      rw [MvPolynomial.aeval_C]
      rfl
  have hcard : Fintype.card (Fin (D + 1) × Fin N) = Fintype.card (Fin N) + D * N := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have hind := gauss_indep (Ω := E) V T hTV hG
  have RT := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K E F (D * N) htr (Fin N) (fun s => T (0, s)) V
    (fun s => hTV _) (Fin (D + 1) × Fin N) u p hp hcard hpu hind
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap E F)
  have RT3 := RT.2.2

  have haW : ∀ k, (⟨a k, hmema k⟩ : E) ∈ V.comap (algebraMap E F) := fun k =>
    (V.valuation_le_one_iff _).1 (haV k)
  let abar : Fin N → ResidueField (V.comap (algebraMap E F)) := fun k => residue (V.comap (algebraMap E F)) ⟨⟨a k, hmema k⟩, haW k⟩
  let aV : Fin N → V := fun k => ⟨a k, (V.valuation_le_one_iff _).1 (haV k)⟩
  let tV : Fin N → V := fun k => ⟨T (0, k), hTV _⟩
  let Lp : MvPolynomial (Fin N) (ResidueField (V.comap (algebraMap E F))) :=
    ∑ k, MvPolynomial.C (abar k) * MvPolynomial.X k
  have hLp : Lp ≠ 0 := by
    intro h0
    have := congrArg (fun P => MvPolynomial.coeff (Finsupp.single j0 1) P) h0
    simp only [Lp, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      MvPolynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j0] at this
    · rw [if_pos rfl, mul_one] at this
      have h1' : abar j0 = 1 := by
        show residue (V.comap (algebraMap E F)) ⟨⟨a j0, hmema j0⟩, haW j0⟩ = 1
        have : (⟨⟨a j0, hmema j0⟩, haW j0⟩ : ↥(V.comap (algebraMap E F))) = 1 := Subtype.ext (Subtype.ext ha0)
        rw [this, map_one]
      rw [h1'] at this
      exact one_ne_zero this
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hs
      exact hb ((Finsupp.single_left_inj one_ne_zero).mp hs)
    · simp
  have hev : MvPolynomial.aeval (fun s => residue V ⟨T (0, s), hTV _⟩) Lp = residue V (∑ k, aV k * tV k) := by
    simp only [Lp, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
  have hres : residue V (∑ k, aV k * tV k) ≠ 0 := by
    rw [← hev]
    intro h0
    exact hLp (RT3.eq_zero_of_aeval_eq_zero _ h0)
  have hunit : IsUnit (∑ k, aV k * tV k) := by
    by_contra hnu
    apply hres
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hL1 : V.valuation (∑ k, a k * T (0, k)) = 1 := by
    have := (V.valuation_eq_one_iff _).1 hunit
    simpa [aV, tV] using this

  have hprod : y j0 * ∑ k, a k * T (0, k) = 1 := by
    rw [Finset.mul_sum, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hay k]
    ring
  have hyv : V.valuation (y j0) = 1 := by
    have := congrArg V.valuation hprod
    rw [Valuation.map_mul, hL1, mul_one, Valuation.map_one] at this
    exact this
  intro k
  rw [← V.valuation_le_one_iff]
  exact (hj0 k (Finset.mem_univ _)).trans hyv.le

end Formalism.L2.Pj.GenericSectionMinimum
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain IsLocalRing

theorem isIntegral_of_quot {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] (x : A)
    (h : ∀ m : Ideal A, m.IsMaximal → IsIntegral R (Ideal.Quotient.mk m x)) : IsIntegral R x := by
  classical
  let S := (IsArtinianRing.setOfPred_isMaximal_finite A).toFinset
  let q : Ideal A → Polynomial R := fun m => if hm : m.IsMaximal then Classical.choose (h m hm) else 1
  have hq : ∀ m, (q m).Monic := fun m => by
    by_cases hm : m.IsMaximal
    · simp only [q, dif_pos hm]; exact (Classical.choose_spec (h m hm)).1
    · simp only [q, dif_neg hm]; exact Polynomial.monic_one
  have hqm : ∀ m, m.IsMaximal → Polynomial.aeval x (q m) ∈ m := fun m hm => by
    have hqe : q m = Classical.choose (h m hm) := dif_pos hm
    set p := Classical.choose (h m hm) with hp
    have e : Polynomial.eval₂ (algebraMap R (A ⧸ m)) (Ideal.Quotient.mk m x) p = 0 :=
      (Classical.choose_spec (h m hm)).2
    rw [hqe, ← Ideal.Quotient.eq_zero_iff_mem]
    have e2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R m) x p
    rw [Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def] at e2
    rw [← e2]
    exact e
  let Pp := ∏ m ∈ S, q m
  have hP : Pp.Monic := Polynomial.monic_prod_of_monic _ _ fun m _ => hq m
  have hmem : ∀ J : Ideal A, J.IsPrime → Polynomial.aeval x Pp ∈ J := by
    intro J hJ
    haveI := hJ
    have hJm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
    have hJS : J ∈ S := (Set.Finite.mem_toFinset _).2 hJm
    exact Ideal.mem_of_dvd _ (map_dvd _ (Finset.dvd_prod_of_mem q hJS)) (hqm J hJm)
  obtain ⟨n, hn⟩ := (nilpotent_iff_mem_prime).2 hmem
  refine ⟨Pp ^ n, hP.pow n, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, hn]

section Inst

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem isIntegral_xr (hfd : FiniteDimensional (Kp X la N) (OsK X la w)) (k : Fin N) :
    IsIntegral (Op X la N) (toOsK X la w (xr X la w k)) := by
  classical
  haveI := hfd
  haveI : CharZero (X.Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective
  haveI : CharZero (Kp X la N) := charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective
  haveI : IsArtinianRing (OsK X la w) := IsArtinianRing.of_finite (Kp X la N) (OsK X la w)
  have hirr : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have hirrO : Irreducible (unifO X la N) := Op.irreducible_map X la N hirr
  haveI : Algebra.IsIntegral (Kp X la N) (OsK X la w) := Algebra.IsIntegral.of_finite _ _
  have hunif : IsUnif (OsK X la w) (unifO X la N) := isUnif_of_field (Kp X la N) hirrO
  have hu : ∀ n : ℕ, 0 < n → IsUnit (n : OsK X la w) := fun n hn => by
    rw [← map_natCast (algebraMap (Kp X la N) (OsK X la w)) n]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map _

  have hδO : ∀ l : Fin N, ∃ δ : OsK X la w → OsK X la w, IsDer δ ∧
      ∀ x, δ (toOsK X la w x) = toOsK X la w (dF X la w l x) := fun l => exists_derOsK X la w l
  choose δO hδOd hδOv using hδO
  refine isIntegral_of_quot _ fun m hm => ?_
  haveI : m.IsMaximal := hm
  letI : Field (OsK X la w ⧸ m) := Ideal.Quotient.field m
  let π : OsK X la w →+* OsK X la w ⧸ m := Ideal.Quotient.mk m

  have hδm : ∀ l : Fin N, ∃ δ : OsK X la w ⧸ m → OsK X la w ⧸ m, IsDer δ ∧ ∀ x, δ (π x) = π (δO l x) :=
    fun l => (hδOd l).quot m (fun x hx => (hδOd l).mem_max hu m hx)
  choose δ hδ hδv using hδm
  by_contra hni

  obtain ⟨V, hRV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure (Op X la N) (OsK X la w ⧸ m)).toSubring) (x := π (toOsK X la w (xr X la w k))) (fun h => hni h)
  have hIV : ∀ z : OsK X la w ⧸ m, IsIntegral (Op X la N) z → z ∈ V := fun z hz => hRV hz
  have hOV : ∀ o : Op X la N, algebraMap (Op X la N) (OsK X la w ⧸ m) o ∈ V := fun o => hIV _ isIntegral_algebraMap
  have hOle : ∀ o : Op X la N, V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) o) ≤ 1 := fun o =>
    (V.valuation_le_one_iff _).2 (hOV o)

  have hϖ : V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N)) < 1 := by
    refine lt_of_le_of_ne (hOle _) fun h1 => hxV ?_
    obtain ⟨n, hn⟩ := hunif.denom (toOsK X la w (xr X la w k))
    have hint : IsIntegral (Op X la N) (π (unifO X la N ^ n • toOsK X la w (xr X la w k))) :=
      (show IsIntegral (Op X la N) (unifO X la N ^ n • toOsK X la w (xr X la w k)) from hn).map
        (Ideal.Quotient.mkₐ (Op X la N) m)
    have hmem := hIV _ hint
    rw [Algebra.smul_def, map_mul] at hmem
    rw [← V.valuation_le_one_iff] at hmem ⊢
    have e : π (algebraMap (Op X la N) (OsK X la w) (unifO X la N ^ n)) =
        algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N) ^ n := by
      rw [map_pow, map_pow]; rfl
    rwa [e, Valuation.map_mul, Valuation.map_pow, h1, one_pow, one_mul] at hmem
  have hmax : ∀ a ∈ maximalIdeal (Op X la N), V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) a) < 1 := by
    intro a ha
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrO, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, Valuation.map_mul]
    calc V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) b) *
          V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N))
        ≤ 1 * V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N)) := by gcongr; exact hOle b
      _ < 1 := by rw [one_mul]; exact hϖ
  have hunitV : ∀ u : Op X la N, IsUnit u → V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) = 1 := by
    intro u hu'
    obtain ⟨u', hu''⟩ := hu'.exists_right_inv
    have e := congrArg (fun z => V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) z)) hu''
    simp only [map_mul, Valuation.map_mul, map_one, Valuation.map_one] at e
    refine le_antisymm (hOle u) ?_
    calc (1 : _) = V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) *
          V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u') := e.symm
      _ ≤ V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) * 1 := by gcongr; exact hOle u'
      _ = _ := mul_one _

  letI : Algebra (X.Kl la) (OsK X la w ⧸ m) :=
    ((algebraMap (Kp X la N) (OsK X la w ⧸ m)).comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  let T : Fin (WeightFamilies.dimY D j + 1) × Fin N → OsK X la w ⧸ m := fun q =>
    algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))
  let y : Fin N → OsK X la w ⧸ m := fun k => π (toOsK X la w (xr X la w k))
  have hKF : ∀ z : Kp X la N, algebraMap (Kp X la N) (OsK X la w ⧸ m) z =
      π (toOsK X la w (algebraMap (Kp X la N) (Frac0 X la w) z)) := fun z => rfl
  have hδK : ∀ l (z : Kp X la N), δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) z) =
      algebraMap (Kp X la N) (OsK X la w ⧸ m) (dK X la N (0, l) z) := by
    intro l z
    rw [hKF, hδv, hδOv, dF_algebraMap, ← hKF]
  have hev : ∀ Pp : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Ol la),
      MvPolynomial.aeval T (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la)) Pp) =
        algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (Pol X la N) (Op X la N) Pp) := by
    intro Pp
    induction Pp using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
      show algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a)) =
        algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N)
          (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C a)))
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N), ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N),
        ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X]
      rfl
  have htow : ∀ a : X.Ol la, algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) a) =
      algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (Op X la N) a) := by
    intro a
    show algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a)) =
      algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) a))
    rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N),
      ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]
  have hmaxOl : ∀ a : X.Ol la, a ∈ maximalIdeal (X.Ol la) →
      V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) a)) < 1 := by
    intro a ha
    rw [htow]
    refine hmax _ ((mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))
  have hKlO : ∀ c : X.Kl la, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) ≤ 1 →
      c ∈ Set.range (algebraMap (X.Ol la) (X.Kl la)) := by
    intro c hc
    by_cases hc0 : c = 0
    · exact ⟨0, by rw [hc0, map_zero]⟩
    rcases (X.Ol la).mem_or_inv_mem c with hcO | hcO
    · exact ⟨⟨c, hcO⟩, rfl⟩
    · by_cases hu : IsUnit (⟨c⁻¹, hcO⟩ : X.Ol la)
      · obtain ⟨v', hv'⟩ := hu.exists_right_inv
        have e : (c⁻¹ : X.Kl la) * (v' : X.Kl la) = 1 := by
          have := congrArg (fun z : X.Ol la => (z : X.Kl la)) hv'
          simpa using this
        refine ⟨v', ?_⟩
        show (v' : X.Kl la) = c
        calc (v' : X.Kl la) = c * (c⁻¹ * v') := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
          _ = c := by rw [e, mul_one]
      · exfalso
        have hlt := hmaxOl ⟨c⁻¹, hcO⟩ ((mem_maximalIdeal _).2 hu)
        have e : V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) *
            V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) = 1 := by
          rw [← Valuation.map_mul, ← map_mul]
          show V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (c * c⁻¹)) = 1
          rw [mul_inv_cancel₀ hc0, map_one, Valuation.map_one]
        have hlt2 : V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) *
            V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) < 1 := by
          calc V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) *
              V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩))
              ≤ 1 * V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) := by
                gcongr
            _ < 1 := by rw [one_mul]; exact hlt
        exact absurd e (ne_of_lt hlt2)
  have hG : ∀ Q : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Kl la),
      (∀ α, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (Q.coeff α)) = 1) →
      V.valuation (MvPolynomial.aeval T Q) = 1 := by
    rintro Q hle ⟨α, hα⟩
    obtain ⟨Pp, rfl⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la))) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      exact hKlO _ (hle β)
    rw [hev]
    apply hunitV
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N)]
    show Pp ∉ gI X la N
    intro hg
    rw [gI, Formalism.DV.gaussIdeal, MvPolynomial.mem_map_C_iff] at hg
    rw [MvPolynomial.coeff_map] at hα
    exact (hmaxOl _ (hg α)).ne hα
  have hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0 := by
    intro l k
    show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k)))) = _
    rw [hδK, dK_Tv]
    by_cases hk : k = l
    · subst hk; simp
    · rw [if_neg (fun h => hk (Prod.mk.inj h).2), if_neg hk, map_zero]
  have hδs : ∀ l (i : Fin (WeightFamilies.dimY D j)) k, δ l (T (i.succ, k)) = 0 := by
    intro l i k
    show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i.succ, k)))) = 0
    rw [hδK, dK_Tv, if_neg (fun h => Fin.succ_ne_zero i (Prod.mk.inj h).1), map_zero]
  have hδKl : ∀ l (c : X.Kl la), δ l (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) = 0 := by
    intro l c
    show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) c)) = 0
    rw [hδK, dK_Kl, map_zero]
  have hδy : ∀ l k, δ l (y k) = -(y k * y l) := by
    intro l k
    show δ l (π (toOsK X la w (xr X la w k))) = _
    rw [hδv, hδOv, dF_xr, map_neg, map_mul, map_neg, map_mul]
  have h1 : ∑ k, T (0, k) * y k = 1 := by
    have := congrArg (fun z => π (toOsK X la w z)) (sum_T0_mul_ratio_eq_one X la w)
    simp only [map_sum, map_mul, map_one] at this
    exact this
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (X.Kl la) (Set.range T)) (OsK X la w ⧸ m) := by
    set Sa := Algebra.adjoin (X.Kl la) (Set.range T) with hSa
    have hmemS : ∀ Q : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Kl la), MvPolynomial.aeval T Q ∈ Sa := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.aeval_C]; exact Sa.algebraMap_mem c
      | add p q hp hq => rw [map_add]; exact Sa.add_mem hp hq
      | mul_X p q hp => rw [map_mul, MvPolynomial.aeval_X]; exact Sa.mul_mem hp (Algebra.subset_adjoin ⟨q, rfl⟩)
    letI : Algebra (Pol X la N) (OsK X la w ⧸ m) :=
      ((algebraMap (Op X la N) (OsK X la w ⧸ m)).comp (algebraMap (Pol X la N) (Op X la N))).toAlgebra
    haveI : IsScalarTower (Pol X la N) (Op X la N) (OsK X la w ⧸ m) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hPS : ∀ Pp : Pol X la N, algebraMap (Pol X la N) (OsK X la w ⧸ m) Pp ∈ Sa := fun Pp => by
      show algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (Pol X la N) (Op X la N) Pp) ∈ Sa
      rw [← hev]
      exact hmemS _
    have hinj : Function.Injective (algebraMap (Pol X la N) (OsK X la w ⧸ m)) := by
      show Function.Injective ((algebraMap (Kp X la N) (OsK X la w ⧸ m)).comp
        ((algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (Pol X la N) (Op X la N))))
      exact (algebraMap (Kp X la N) _).injective.comp ((IsFractionRing.injective _ _).comp
        (IsLocalization.injective (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors))
    let ψ : Pol X la N →+* Sa := (algebraMap (Pol X la N) (OsK X la w ⧸ m)).codRestrict Sa hPS
    haveI : Algebra.IsIntegral (Kp X la N) (OsK X la w ⧸ m) := Algebra.IsIntegral.of_finite _ _
    refine ⟨fun f => ?_⟩
    have hfK : IsAlgebraic (Kp X la N) f := (Algebra.IsIntegral.isIntegral f).isAlgebraic
    have hfO : IsAlgebraic (Op X la N) f :=
      (IsFractionRing.isAlgebraic_iff (A := Op X la N) (K := Kp X la N) (C := OsK X la w ⧸ m)).2 hfK
    obtain ⟨p, hp0, hp⟩ := hfO
    obtain ⟨⟨b, hb⟩, hbp⟩ := IsLocalization.integerNormalization_map_to_map (gI X la N).primeCompl p
    have hp'0 : IsLocalization.integerNormalization (gI X la N).primeCompl p ≠ 0 := by
      intro h0
      rw [h0, Polynomial.map_zero] at hbp
      have hb' : algebraMap (Pol X la N) (Op X la N) b ≠ 0 :=
        (IsLocalization.map_units (Op X la N) (⟨b, hb⟩ : (gI X la N).primeCompl)).ne_zero
      rw [← algebraMap_smul (Op X la N) b p] at hbp
      exact hp0 ((smul_eq_zero.mp hbp.symm).resolve_left hb')
    refine ⟨(IsLocalization.integerNormalization (gI X la N).primeCompl p).map ψ,
      (Polynomial.map_ne_zero_iff (fun a b' hab => hinj (congrArg Subtype.val hab))).2 hp'0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap Sa (OsK X la w ⧸ m)).comp ψ = algebraMap (Pol X la N) (OsK X la w ⧸ m) :=
      RingHom.ext fun _ => rfl
    rw [e, ← Polynomial.aeval_def]
    exact IsLocalization.integerNormalization_aeval_eq_zero (M := (gI X la N).primeCompl) p hp
  exact hxV (gauss_direct (WeightFamilies.dimY D j) N T y δ hδ hδKl hδ0 hδs hδy h1 halg V hG k)

end Inst

theorem generic_section_minimum_integral {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (xplus X E hM) ka wL wF)
    (la : HeightOneSpectrum (𝓞 B.KO)) : GenericSectionMinimumIntegral G la := by
  classical
  intro hfd hred ζ
  haveI := hfd
  haveI := hred
  haveI : CharZero ((xplus X E hM).Kl la) :=
    charZero_of_injective_algebraMap (algebraMap B.KO ((xplus X E hM).Kl la)).injective
  haveI : CharZero (Kp (xplus X E hM) la G.N) :=
    charZero_of_injective_algebraMap (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).injective
  haveI : IsDVRAt ζ := (integralClosure_dvr' (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N)
    (OsK (xplus X E hM) la G.w)).2 ζ
  have hirr : Irreducible (unif (xplus X E hM) la) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))
  haveI : Algebra.IsIntegral (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := Algebra.IsIntegral.of_finite _ _
  have hunif : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N) :=
    isUnif_of_field (Kp (xplus X E hM) la G.N) (Op.irreducible_map _ la G.N hirr)
  have hint : ∀ k, toOsK (xplus X E hM) la G.w (wRat G la k) ∈
      As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) :=
    fun k => isIntegral_xr (xplus X E hM) la G.w hfd k
  refine ⟨fun k => ord_nonneg ζ hunif (hint k), ?_⟩
  by_contra hall
  push Not at hall
  have hmemζ : ∀ k, (⟨_, hint k⟩ : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) ∈ ζ.asIdeal := by
    intro k
    by_contra hk
    apply hall k
    rw [ord_of_mem ζ hunif (hint k)]
    have hu : IsUnit (algebraMap _ (Loc ζ) (⟨_, hint k⟩ : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)))) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal _).2 hk
    have h0 : vL ζ ⟨_, hint k⟩ = 0 := by
      show Ring.ord (Loc ζ) _ = 0
      have := Ring.ord_mul_of_isUnit_left hu (1 : Loc ζ)
      rw [mul_one, Ring.ord_one] at this
      exact this
    rw [h0]
    rfl
  have hT : ∀ k, algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)
      (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (Tv (xplus X E hM) la G.N (0, k))) ∈
        As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := fun k =>
    isIntegral_algebraMap (x := Tv (xplus X E hM) la G.N (0, k))
  let s : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) := ∑ k, ⟨_, hT k⟩ * ⟨_, hint k⟩
  have hs1 : s = 1 := by
    apply Subtype.ext
    have := congrArg (toOsK (xplus X E hM) la G.w) (sum_T0_mul_ratio_eq_one (xplus X E hM) la G.w)
    simp only [map_sum, map_mul, map_one] at this
    show (As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).val s =
      (As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).val 1
    rw [map_sum, map_one]
    simp only [map_mul]
    exact this
  have hsζ : s ∈ ζ.asIdeal := Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hmemζ k)
  rw [hs1] at hsζ
  exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hsζ)

end Formalism.L2.Pj.GenericSectionMinimum
end
end
