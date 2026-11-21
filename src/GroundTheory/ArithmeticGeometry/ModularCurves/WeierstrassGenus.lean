import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassChartIso
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCharts
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RiemannRoch
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite

section
universe u

namespace GroundTheory.Arith.Modular

open Polynomial Polynomial.Bivariate

namespace Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

noncomputable def xPolynomial : R[X][Y] :=
  Y ^ 3 + C (C W.a₂) * Y ^ 2 + C (C W.a₄ - C W.a₁ * X) * Y + C (C W.a₆ - X ^ 2 - C W.a₃ * X)

theorem degree_xPolynomial_lt : (C (C W.a₂) * Y ^ 2 + C (C W.a₄ - C W.a₁ * X) * Y +
    C (C W.a₆ - X ^ 2 - C W.a₃ * X) : R[X][Y]).degree < 3 := by
  compute_degree!

theorem monic_xPolynomial : (xPolynomial W).Monic := by
  unfold xPolynomial
  rw [add_assoc, add_assoc]
  exact monic_X_pow_add (by simpa [add_assoc] using degree_xPolynomial_lt W)

theorem natDegree_xPolynomial [Nontrivial R] : (xPolynomial W).natDegree = 3 := by
  unfold xPolynomial
  compute_degree!

abbrev XRing : Type u := AdjoinRoot (xPolynomial W)

theorem eval₂_polynomial_XRing :
    (W.toAffine.polynomial).eval₂ (Polynomial.eval₂RingHom (algebraMap R (XRing W))
      (AdjoinRoot.root (xPolynomial W))) (AdjoinRoot.of (xPolynomial W) X) = 0 := by
  have h : AdjoinRoot.mk (xPolynomial W) (Y ^ 3 + C (C W.a₂) * Y ^ 2 + C (C W.a₄ - C W.a₁ * X) * Y +
      C (C W.a₆ - X ^ 2 - C W.a₃ * X)) = 0 := AdjoinRoot.mk_self
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, coe_eval₂RingHom]
  have ha : ∀ a : R, algebraMap R (XRing W) a = AdjoinRoot.of (xPolynomial W) (C a) := fun a => rfl
  simp only [ha]
  linear_combination -h

theorem eval₂_xPolynomial_coord :
    (xPolynomial W).eval₂ (Polynomial.eval₂RingHom (algebraMap R W.toAffine.CoordinateRing) (yC W))
      (xC W) = 0 := by
  have E := equation_xC_yC W
  simp only [xPolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom]
  linear_combination -E

noncomputable def toXRing : W.toAffine.CoordinateRing →+* XRing W :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R (XRing W)) (AdjoinRoot.root (xPolynomial W)))
    (AdjoinRoot.of (xPolynomial W) X) (eval₂_polynomial_XRing W)

noncomputable def ofXRing : XRing W →+* W.toAffine.CoordinateRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R W.toAffine.CoordinateRing) (yC W))
    (xC W) (eval₂_xPolynomial_coord W)

theorem infNatDegree [Nontrivial R] : (infPolynomial W).natDegree = 3 := by
  unfold infPolynomial
  compute_degree!

theorem ofXRing_toXRing (a : W.toAffine.CoordinateRing) : ofXRing W (toXRing W a) = a := by
  change ((ofXRing W).comp (toXRing W)) a = RingHom.id _ a
  congr 1
  apply AdjoinRoot.ringHom_ext
  · ext p
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_C, RingHom.id_apply]
      change AdjoinRoot.lift _ _ (eval₂_xPolynomial_coord W) (AdjoinRoot.of _ (C p)) = _
      rw [AdjoinRoot.lift_of]
      simp
      rfl
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_X, RingHom.id_apply, AdjoinRoot.lift_root]
      rfl
  · simp [toXRing, ofXRing, yC]

theorem toXRing_ofXRing (a : XRing W) : toXRing W (ofXRing W a) = a := by
  change ((toXRing W).comp (ofXRing W)) a = RingHom.id _ a
  congr 1
  apply AdjoinRoot.ringHom_ext
  · ext p
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_C, RingHom.id_apply]
      change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.of _ (C p)) = _
      rw [AdjoinRoot.lift_of]
      simp
      rfl
    · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_of, coe_eval₂RingHom,
        eval₂_X, RingHom.id_apply, yC, AdjoinRoot.lift_root]
  · simp only [toXRing, ofXRing, RingHom.comp_apply, AdjoinRoot.lift_root, RingHom.id_apply, xC,
      AdjoinRoot.mk_C, AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

noncomputable def xRingEquiv : W.toAffine.CoordinateRing ≃+* XRing W :=
  RingEquiv.ofRingHom (toXRing W) (ofXRing W) (RingHom.ext (toXRing_ofXRing W))
    (RingHom.ext (ofXRing_toXRing W))

noncomputable def xAlgEquiv : W.toAffine.CoordinateRing ≃ₐ[R] XRing W :=
  AlgEquiv.ofRingEquiv (f := xRingEquiv W) (fun r => by
    change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.of _ (C r)) = _
    rw [AdjoinRoot.lift_of]
    simp)

theorem xAlgEquiv_xC : xAlgEquiv W (xC W) = AdjoinRoot.root (xPolynomial W) := by
  change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.mk _ (C X)) = _
  rw [AdjoinRoot.mk_C, AdjoinRoot.lift_of]
  simp

theorem xAlgEquiv_yC : xAlgEquiv W (yC W) = AdjoinRoot.of (xPolynomial W) X := by
  change AdjoinRoot.lift _ _ (eval₂_polynomial_XRing W) (AdjoinRoot.root _) = _
  rw [AdjoinRoot.lift_root]

section Bases

variable [Nontrivial R]

noncomputable def basisX : Module.Basis (Fin 3) R[X] (XRing W) :=
  (AdjoinRoot.powerBasis' (monic_xPolynomial W)).basis.reindex (finCongr (natDegree_xPolynomial W))

theorem basisX_apply (i : Fin 3) : basisX W i = AdjoinRoot.root (xPolynomial W) ^ (i : ℕ) := by
  rw [basisX, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

noncomputable def basisI : Module.Basis (Fin 3) R[X] (InfChart W) :=
  (AdjoinRoot.powerBasis' (monic_infPolynomial W)).basis.reindex (finCongr (infNatDegree W))

theorem basisI_apply (i : Fin 3) : basisI W i = xI W ^ (i : ℕ) := by
  rw [basisI, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

end Bases

end Weierstrass

end GroundTheory.Arith.Modular
end

section
universe u

namespace GroundTheory.Arith.Modular

open Polynomial Polynomial.Bivariate

namespace Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem ringHom_eq_eval₂ {S : Type*} [CommRing S] (φ : R[X] →+* S) (q : R[X]) :
    φ q = q.eval₂ (φ.comp C) (φ X) := by
  conv_lhs => rw [← Polynomial.eval₂_C_X (p := q)]
  rw [Polynomial.hom_eval₂]

noncomputable def coordA [Nontrivial R] (a : W.toAffine.CoordinateRing) : Fin 3 →₀ R[X] :=
  (basisX W).repr (xAlgEquiv W a)

noncomputable def coordI [Nontrivial R] (b : InfChart W) : Fin 3 →₀ R[X] := (basisI W).repr b

theorem eq_sum_coordA [Nontrivial R] (a : W.toAffine.CoordinateRing) :
    a = ∑ i : Fin 3, (coordA W a i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ) := by
  apply (xAlgEquiv W).injective
  conv_lhs => rw [← (basisX W).sum_repr (xAlgEquiv W a)]
  simp only [map_sum, map_mul, map_pow, xAlgEquiv_xC, basisX_apply, coordA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]
  congr 1
  have e : ∀ q : R[X], xAlgEquiv W (q.eval₂ (algebraMap R _) (yC W)) =
      q.eval₂ ((xAlgEquiv W).toRingHom.comp (algebraMap R _)) (xAlgEquiv W (yC W)) :=
    fun q => Polynomial.hom_eval₂ q (algebraMap R _) (xAlgEquiv W).toRingEquiv.toRingHom (yC W)
  rw [ringHom_eq_eval₂ (algebraMap R[X] (XRing W)), e, xAlgEquiv_yC]
  congr 1
  ext r
  simp
  rfl

theorem eq_sum_coordI [Nontrivial R] (b : InfChart W) :
    b = ∑ i : Fin 3, (coordI W b i).eval₂ (algebraMap R _) (zI W) * xI W ^ (i : ℕ) := by
  conv_lhs => rw [← (basisI W).sum_repr b]
  simp only [basisI_apply, coordI]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]
  congr 1
  rw [ringHom_eq_eval₂ (algebraMap R[X] (InfChart W))]
  rfl

section Coordinates

variable [Nontrivial R]

theorem coordA_sum (P : Fin 3 → R[X]) :
    coordA W (∑ i : Fin 3, (P i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) =
      Finsupp.equivFunOnFinite.symm P := by
  have e : ∀ q : R[X], xAlgEquiv W (q.eval₂ (algebraMap R _) (yC W)) = algebraMap R[X] _ q := by
    intro q
    rw [ringHom_eq_eval₂ (algebraMap R[X] (XRing W))]
    rw [show xAlgEquiv W (q.eval₂ (algebraMap R _) (yC W)) =
      q.eval₂ ((xAlgEquiv W).toRingEquiv.toRingHom.comp (algebraMap R _)) (xAlgEquiv W (yC W)) from
      Polynomial.hom_eval₂ q (algebraMap R _) (xAlgEquiv W).toRingEquiv.toRingHom (yC W)]
    rw [xAlgEquiv_yC]
    congr 1
    ext r
    simp
    rfl
  have h : xAlgEquiv W (∑ i : Fin 3, (P i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) =
      (basisX W).equivFun.symm P := by
    simp only [map_sum, map_mul, map_pow, e, xAlgEquiv_xC, Module.Basis.equivFun_symm_apply,
      basisX_apply, Algebra.smul_def]
  rw [coordA, h]
  ext i : 1
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem coordA_injective : Function.Injective (coordA W) := by
  intro a b h
  exact (xAlgEquiv W).injective ((basisX W).repr.injective h)

theorem coordA_yC_pow_mul (n : ℕ) (a : W.toAffine.CoordinateRing) :
    coordA W (yC W ^ n * a) = (X ^ n : R[X]) • coordA W a := by
  conv_lhs => rw [eq_sum_coordA W a, Finset.mul_sum]
  have : ∀ i : Fin 3, yC W ^ n * ((coordA W a i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) =
      (X ^ n * coordA W a i).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ) := by
    intro i
    rw [eval₂_mul, eval₂_X_pow]
    ring
  simp only [this, coordA_sum]
  ext i
  simp

theorem yC_mul_eq_zero {a : W.toAffine.CoordinateRing} (h : yC W * a = 0) : a = 0 := by
  apply coordA_injective W
  have h2 := coordA_yC_pow_mul W 1 a
  rw [pow_one, h] at h2
  ext i k
  have h3 := congrArg (fun f : Fin 3 →₀ R[X] => (f i).coeff (k + 1)) h2
  simp only [Finsupp.smul_apply, smul_eq_mul, pow_one, coeff_X_mul] at h3
  rw [← h3]
  simp [coordA]

end Coordinates

section Overlap

noncomputable instance invertibleY :
    Invertible (algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)) :=
  ⟨yInv W, by rw [mul_comm]; exact yC_mul_yInv W, yC_mul_yInv W⟩

theorem invOf_yC : ⅟(algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)) = yInv W := rfl

theorem algebraMap_overlap_injective :
    Function.Injective (algebraMap W.toAffine.CoordinateRing (Overlap W)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton W.toAffine.CoordinateRing := Module.subsingleton R _
    exact fun a b _ => Subsingleton.elim a b
  have hy : Submonoid.powers (yC W) ≤ nonZeroDivisors _ := by
    rw [Submonoid.powers_le]
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun z hz => yC_mul_eq_zero W hz, fun z hz => yC_mul_eq_zero W (by rwa [mul_comm])⟩
  exact IsLocalization.injective (Overlap W) hy

theorem infToOverlap_eval₂ (q : R[X]) :
    infToOverlap W (q.eval₂ (algebraMap R _) (zI W)) =
      q.eval₂ (algebraMap R (Overlap W)) (yInv W) := by
  rw [show infToOverlap W (q.eval₂ (algebraMap R _) (zI W)) =
    q.eval₂ ((infToOverlap W).toRingHom.comp (algebraMap R _)) (infToOverlap W (zI W))
    from Polynomial.hom_eval₂ _ _ (infToOverlap W).toRingHom _, infToOverlap_zI]
  have hc : (infToOverlap W).toRingHom.comp (algebraMap R (InfChart W)) =
      algebraMap R (Overlap W) := (infToOverlap W).comp_algebraMap
  rw [hc]

variable [Nontrivial R]

theorem infToOverlap_eq (b : InfChart W) :
    infToOverlap W b = ∑ i : Fin 3, (coordI W b i).eval₂ (algebraMap R (Overlap W)) (yInv W) *
      (algebraMap _ (Overlap W) (xC W) * yInv W) ^ (i : ℕ) := by
  have h := congrArg (infToOverlap W) (eq_sum_coordI W b)
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, infToOverlap_xI, infToOverlap_eval₂]

theorem yC_pow_mul_infToOverlap (b : InfChart W) (N : ℕ)
    (hN : ∀ i : Fin 3, (coordI W b i).natDegree + i ≤ N) :
    algebraMap _ (Overlap W) (yC W) ^ N * infToOverlap W b =
      algebraMap _ (Overlap W) (∑ i : Fin 3, (reflect (N - i) (coordI W b i)).eval₂
        (algebraMap R _) (yC W) * xC W ^ (i : ℕ)) := by
  rw [infToOverlap_eq, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hq : (coordI W b i).natDegree ≤ N - i := by have := hN i; omega
  have hNi : N = (N - i) + i := by have := hN i; omega
  set y := algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)
  set x := algebraMap W.toAffine.CoordinateRing (Overlap W) (xC W)
  set q := coordI W b i
  have key : q.eval₂ (algebraMap R (Overlap W)) (yInv W) * y ^ (N - i) =
      (reflect (N - i) q).eval₂ (algebraMap R (Overlap W)) y := by
    have := eval₂_reflect_mul_pow (algebraMap R (Overlap W)) y (N - i) (reflect (N - i) q)
      (natDegree_reflect_le.trans (by simp [hq]))
    rwa [reflect_reflect, invOf_yC] at this
  rw [map_mul, map_pow, show algebraMap W.toAffine.CoordinateRing (Overlap W)
    ((reflect (N - i) q).eval₂ (algebraMap R _) (yC W)) =
      (reflect (N - i) q).eval₂ (algebraMap R (Overlap W)) y by
    rw [Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq], ← key]
  have hyu : y * yInv W = 1 := yC_mul_yInv W
  conv_lhs => rw [hNi, pow_add]
  calc y ^ (N - i) * y ^ (i : ℕ) * (q.eval₂ (algebraMap R (Overlap W)) (yInv W) * (x * yInv W) ^ (i : ℕ))
      = q.eval₂ (algebraMap R (Overlap W)) (yInv W) * y ^ (N - i) * x ^ (i : ℕ) *
          (y * yInv W) ^ (i : ℕ) := by ring
    _ = _ := by rw [hyu, one_pow, mul_one]

end Overlap

section Main

variable [Nontrivial R]

noncomputable def degBound (b : InfChart W) : ℕ := (∑ i : Fin 3, (coordI W b i).natDegree) + 3

theorem le_degBound (b : InfChart W) (i : Fin 3) :
    (coordI W b i).natDegree + i ≤ degBound W b := by
  have h1 : (coordI W b i).natDegree ≤ ∑ j : Fin 3, (coordI W b j).natDegree :=
    Finset.single_le_sum (f := fun j => (coordI W b j).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : (i : ℕ) < 3 := i.isLt
  unfold degBound
  omega

theorem coordA_eq_of_sub_eq (a : W.toAffine.CoordinateRing) (b : InfChart W) (r : R)
    (h : algebraMap _ (Overlap W) a - infToOverlap W b =
      r • (algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W)) :
    (X ^ degBound W b : R[X]) • coordA W a = Finsupp.equivFunOnFinite.symm (fun i : Fin 3 =>
      reflect (degBound W b - i) (coordI W b i) +
        if i = 2 then C r * X ^ (degBound W b - 1) else 0) := by
  set N := degBound W b
  have hN3 : 3 ≤ N := by unfold N degBound; omega
  have hy := yC_pow_mul_infToOverlap W b N (le_degBound W b)
  have hA : yC W ^ N * a = ∑ i : Fin 3, (reflect (N - i) (coordI W b i) +
      if i = 2 then C r * X ^ (N - 1) else 0).eval₂ (algebraMap R _) (yC W) * xC W ^ (i : ℕ) := by
    apply algebraMap_overlap_injective W
    have h' : algebraMap _ (Overlap W) a = infToOverlap W b +
        r • (algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W) := by rw [← h]; ring
    have hsplit : ∑ i : Fin 3, (reflect (N - i) (coordI W b i) +
        if i = 2 then C r * X ^ (N - 1) else 0).eval₂ (algebraMap R W.toAffine.CoordinateRing)
          (yC W) * xC W ^ (i : ℕ) =
        (∑ i : Fin 3, (reflect (N - i) (coordI W b i)).eval₂ (algebraMap R _) (yC W) *
          xC W ^ (i : ℕ)) + r • (xC W ^ 2 * yC W ^ (N - 1)) := by
      simp only [Fin.sum_univ_three, eval₂_add]
      simp [Algebra.smul_def]
      ring
    rw [hsplit, map_add, ← hy, map_mul, map_pow, h', mul_add]
    congr 1
    simp only [Algebra.smul_def, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    have hyu := yC_mul_yInv W
    have hN : N = (N - 1) + 1 := by omega
    conv_lhs => rw [hN, pow_succ]
    linear_combination (algebraMap R (Overlap W) r *
      algebraMap W.toAffine.CoordinateRing (Overlap W) (xC W) ^ 2 *
      algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W) ^ (N - 1)) * hyu
  rw [← coordA_yC_pow_mul, hA, coordA_sum]

end Main

section Main2

variable [Nontrivial R]

theorem eq_zero_of_sub_eq_smul (a : W.toAffine.CoordinateRing) (b : InfChart W) (r : R)
    (h : algebraMap _ (Overlap W) a - infToOverlap W b =
      r • (algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W)) : r = 0 := by
  have hc := congrArg (fun f : Fin 3 →₀ R[X] => (f 2).coeff (degBound W b - 1))
    (coordA_eq_of_sub_eq W a b r h)
  have hN3 : 3 ≤ degBound W b := by unfold degBound; omega
  have hq := le_degBound W b 2
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_equivFunOnFinite_symm] at hc
  simp only [coeff_add, coeff_X_pow_mul', coeff_reflect] at hc
  have hrev : revAt (degBound W b - ((2 : Fin 3) : ℕ)) (degBound W b - 1) = degBound W b - 1 :=
    revAt_eq_self_of_lt (by simp; omega)
  rw [if_neg (by omega), hrev, coeff_eq_zero_of_natDegree_lt (by simp at hq; omega), if_pos trivial,
    coeff_C_mul_X_pow, if_pos rfl, zero_add] at hc
  exact hc.symm

end Main2

section Kernel

variable [Nontrivial R]

end Kernel

section Span

noncomputable def cechMap : (W.toAffine.CoordinateRing × InfChart W) →ₗ[R] Overlap W :=
  (IsScalarTower.toAlgHom R W.toAffine.CoordinateRing (Overlap W)).toLinearMap.comp
      (LinearMap.fst R _ _) -
    (infToOverlap W).toLinearMap.comp (LinearMap.snd R _ _)

@[simp]
theorem cechMap_apply (p : W.toAffine.CoordinateRing × InfChart W) :
    cechMap W p = algebraMap _ (Overlap W) p.1 - infToOverlap W p.2 := rfl

noncomputable def cechGen : Overlap W := algebraMap _ (Overlap W) (xC W) ^ 2 * yInv W

noncomputable def cechSpan : Submodule R (Overlap W) :=
  LinearMap.range (cechMap W) ⊔ Submodule.span R {cechGen W}

theorem monomial_mem_cechSpan (k n : ℕ) (i : Fin 3) :
    algebraMap _ (Overlap W) (yC W ^ k * xC W ^ (i : ℕ)) * yInv W ^ n ∈ cechSpan W := by
  set y := algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)
  set x := algebraMap W.toAffine.CoordinateRing (Overlap W) (xC W)
  have hyu : y * yInv W = 1 := yC_mul_yInv W
  rw [map_mul, map_pow, map_pow]
  by_cases hnk : n ≤ k
  · apply Submodule.mem_sup_left
    refine ⟨(yC W ^ (k - n) * xC W ^ (i : ℕ), 0), ?_⟩
    simp only [cechMap_apply, map_zero, sub_zero, map_mul, map_pow]
    have hk : k = (k - n) + n := by omega
    conv_rhs => rw [hk, pow_add]
    calc y ^ (k - n) * x ^ (i : ℕ) = y ^ (k - n) * x ^ (i : ℕ) * (y * yInv W) ^ n := by
          rw [hyu, one_pow, mul_one]
      _ = _ := by ring
  · have hm : n = k + (n - k) := by omega
    have hval : y ^ k * x ^ (i : ℕ) * yInv W ^ n = x ^ (i : ℕ) * yInv W ^ (n - k) := by
      conv_lhs => rw [hm, pow_add]
      calc y ^ k * x ^ (i : ℕ) * (yInv W ^ k * yInv W ^ (n - k))
          = x ^ (i : ℕ) * yInv W ^ (n - k) * (y * yInv W) ^ k := by ring
        _ = _ := by rw [hyu, one_pow, mul_one]
    rw [hval]
    by_cases hi : (i : ℕ) ≤ n - k
    · apply Submodule.mem_sup_left
      refine ⟨(0, -(zI W ^ (n - k - i) * xI W ^ (i : ℕ))), ?_⟩
      simp only [cechMap_apply, map_zero, zero_sub, map_neg, neg_neg, map_mul, map_pow,
        infToOverlap_xI, infToOverlap_zI]
      have : n - k = (n - k - i) + i := by omega
      conv_rhs => rw [this, pow_add]
      ring
    · apply Submodule.mem_sup_right
      have hi2 : (i : ℕ) = 2 := by have := i.isLt; omega
      have hnk1 : n - k = 1 := by omega
      rw [hi2, hnk1, pow_one]
      exact Submodule.subset_span rfl

variable [Nontrivial R]

noncomputable def basisXR : Module.Basis (ℕ × Fin 3) R (XRing W) :=
  (Polynomial.basisMonomials R).smulTower (basisX W)

theorem xAlgEquiv_symm_basisXR (k : ℕ) (i : Fin 3) :
    (xAlgEquiv W).symm (basisXR W (k, i)) = yC W ^ k * xC W ^ (i : ℕ) := by
  rw [AlgEquiv.symm_apply_eq, map_mul, map_pow, map_pow, xAlgEquiv_xC, xAlgEquiv_yC, basisXR,
    Module.Basis.smulTower_apply, basisX_apply, Polynomial.coe_basisMonomials, Algebra.smul_def]
  congr 1
  rw [← map_pow]
  simp [Polynomial.monomial_one_right_eq_X_pow]

theorem cechSpan_eq_top : cechSpan W = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hv⟩ := IsLocalization.surj (Submonoid.powers (yC W)) v
  simp only at hv
  have hv' : v = algebraMap _ (Overlap W) a * yInv W ^ n := by
    rw [← hv, mul_assoc, map_pow, ← mul_pow, yC_mul_yInv W, one_pow, mul_one]
  rw [hv']
  let Ψ : XRing W →ₗ[R] Overlap W :=
    (LinearMap.mulRight R (yInv W ^ n)).comp
      ((IsScalarTower.toAlgHom R W.toAffine.CoordinateRing (Overlap W)).toLinearMap.comp
        (xAlgEquiv W).symm.toLinearMap)
  have hrange : LinearMap.range Ψ ≤ cechSpan W := by
    rw [LinearMap.range_eq_map, ← (basisXR W).span_eq, Submodule.map_span_le]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      xAlgEquiv_symm_basisXR, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      LinearMap.mulRight_apply]
    exact monomial_mem_cechSpan W k n i
  have := hrange ⟨xAlgEquiv W a, rfl⟩
  simpa [Ψ] using this

end Span

section Cohomology

theorem subsingleton_of_subsingleton [Subsingleton R] : Subsingleton (Overlap W) := by
  have : Subsingleton W.toAffine.CoordinateRing := Module.subsingleton R _
  exact Module.subsingleton W.toAffine.CoordinateRing _

theorem eq_zero_of_smul_cechGen_mem {r : R} (h : r • cechGen W ∈ LinearMap.range (cechMap W)) :
    r = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨⟨a, b⟩, hab⟩ := h
  exact eq_zero_of_sub_eq_smul W a b r hab

end Cohomology

end Weierstrass

end GroundTheory.Arith.Modular
end

section
open CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

section TwoOpens

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

abbrev i01 : Fin 2 → Fin 2 := ![0, 1]

noncomputable def twoDiff : Cochain P U 0 →+ P.obj (op (inter U i01)) :=
  (Pi.evalAddMonoidHom (fun i => P.obj (op (inter U i))) i01).comp (d P U 0)

abbrev TwoQuot : Type u := P.obj (op (inter U i01)) ⧸ (twoDiff P U).range

noncomputable def cocycleToQuot : cocycles P U 1 →+ TwoQuot P U :=
  (QuotientAddGroup.mk' _).comp
    ((Pi.evalAddMonoidHom (fun i => P.obj (op (inter U i))) i01).comp (cocycles P U 1).subtype)

lemma cocycleToQuot_apply (σ : cocycles P U 1) :
    cocycleToQuot P U σ = QuotientAddGroup.mk ((σ : Cochain P U 1) i01) := rfl

noncomputable def cechOneToQuot : cechH P U 1 →+ TwoQuot P U :=
  QuotientAddGroup.lift _ (cocycleToQuot P U) (by
    rintro ⟨σ, hσ⟩ hb
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ] at hb
    obtain ⟨τ, rfl⟩ := hb
    rw [AddMonoidHom.mem_ker, cocycleToQuot_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨τ, rfl⟩)

lemma cechOneToQuot_cls (σ : Cochain P U 1) (hσ : d P U 1 σ = 0) :
    cechOneToQuot P U (cls σ hσ) = QuotientAddGroup.mk (σ i01) := rfl

end TwoOpens

section TwoOpens2

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

lemma res_injective_of_le {V W : Opens X} (h : V ≤ W) (h' : W ≤ V) :
    Function.Injective (res P h) := by
  intro x y hxy
  have := congrArg (res P h') hxy
  rwa [res_res, res_res, res_refl, res_refl] at this

lemma res_cochain_congr {n : ℕ} (σ : Cochain P U n) {V : Opens X} {i i' : Fin (n + 1) → Fin 2}
    (e : i = i') (h : V ≤ inter U i) (h' : V ≤ inter U i') : res P h (σ i) = res P h' (σ i') := by
  subst e
  rfl

lemma vec2_eq (i : Fin 2 → Fin 2) : i = ![i 0, i 1] := by
  funext x
  fin_cases x <;> rfl

lemma vec3_eq (j : Fin 3 → Fin 2) : j = ![j 0, j 1, j 2] := by
  funext x
  fin_cases x <;> rfl

lemma comp_succAbove_zero (a b c : Fin 2) : ![a, b, c] ∘ Fin.succAbove 0 = ![b, c] := by
  funext x
  fin_cases x <;> rfl

lemma comp_succAbove_one (a b c : Fin 2) : ![a, b, c] ∘ Fin.succAbove 1 = ![a, c] := by
  funext x
  fin_cases x <;> rfl

lemma comp_succAbove_two (a b c : Fin 2) : ![a, b, c] ∘ Fin.succAbove 2 = ![a, b] := by
  funext x
  fin_cases x <;> rfl

lemma d_one_apply (σ : Cochain P U 1) (a b c : Fin 2) :
    d P U 1 σ ![a, b, c] =
      res P (by rw [← comp_succAbove_zero a b c]; exact inter_le_comp U _ _) (σ ![b, c]) -
        res P (by rw [← comp_succAbove_one a b c]; exact inter_le_comp U _ _) (σ ![a, c]) +
        res P (by rw [← comp_succAbove_two a b c]; exact inter_le_comp U _ _) (σ ![a, b]) := by
  rw [d_apply, Fin.sum_univ_three]
  rw [res_cochain_congr P U σ (comp_succAbove_zero a b c) _
      (by rw [← comp_succAbove_zero a b c]; exact inter_le_comp U _ _),
    res_cochain_congr P U σ (comp_succAbove_one a b c) _
      (by rw [← comp_succAbove_one a b c]; exact inter_le_comp U _ _),
    res_cochain_congr P U σ (comp_succAbove_two a b c) _
      (by rw [← comp_succAbove_two a b c]; exact inter_le_comp U _ _)]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two]
  abel

lemma inter_le_inter_of_forall {m n : ℕ} (i : Fin m → Fin 2) (i' : Fin n → Fin 2)
    (h : ∀ a, ∃ b, i b = i' a) : inter U i ≤ inter U i' := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  intro a
  obtain ⟨b, hb⟩ := h a
  rw [← hb]
  exact hx b

variable {P U}

lemma cocycle_diag {σ : Cochain P U 1} (hσ : d P U 1 σ = 0) (c : Fin 2) : σ ![c, c] = 0 := by
  have h := congrFun hσ ![c, c, c]
  rw [d_one_apply, sub_self, zero_add] at h
  exact res_injective_of_le P _ (inter_le_inter_of_forall U _ _ (fun a => ⟨0, by fin_cases a <;> rfl⟩))
    (h.trans (map_zero _).symm)

lemma cocycle_swap {σ : Cochain P U 1} (hσ : d P U 1 σ = 0) (h01 : σ i01 = 0) : σ ![1, 0] = 0 := by
  have h := congrFun hσ ![0, 1, 0]
  rw [d_one_apply, cocycle_diag hσ 0, map_zero, sub_zero] at h
  change _ + res P _ (σ i01) = 0 at h
  rw [h01, map_zero, add_zero] at h
  exact res_injective_of_le P _ (inter_le_inter_of_forall U _ _ (fun a => by
    fin_cases a
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩)) (h.trans (map_zero _).symm)

variable (P U)

theorem cechOneToQuot_injective : Function.Injective (cechOneToQuot P U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H σ =>
  obtain ⟨σ, hσ⟩ := σ
  obtain ⟨τ, hτ⟩ := (QuotientAddGroup.eq_zero_iff _).1 hx
  apply (QuotientAddGroup.eq_zero_iff _).2
  rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ]
  refine ⟨τ, ?_⟩
  have hσ' : d P U 1 (σ - d P U 0 τ) = 0 := by
    rw [map_sub, (mem_cocycles _).1 hσ, d_d, sub_zero]
  have h01 : (σ - d P U 0 τ) i01 = 0 := by
    change σ i01 - twoDiff P U τ = 0
    rw [hτ]
    exact sub_self _
  suffices h : σ - d P U 0 τ = 0 from (sub_eq_zero.1 h).symm
  funext i
  obtain ⟨a, b, rfl⟩ : ∃ a b, i = ![a, b] := ⟨_, _, vec2_eq i⟩
  fin_cases a <;> fin_cases b
  · exact cocycle_diag hσ' 0
  · exact h01
  · exact cocycle_swap hσ' h01
  · exact cocycle_diag hσ' 1

end TwoOpens2

section TwoOpens3

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

lemma inter_le_inter_zero_one {i : Fin 2 → Fin 2} (h : i 0 ≠ i 1) : inter U i ≤ inter U i01 := by
  have hi : ∀ a : Fin 2, a = i 0 ∨ a = i 1 := by
    intro a
    revert h
    generalize i 0 = p
    generalize i 1 = q
    fin_cases a <;> fin_cases p <;> fin_cases q <;> simp
  exact inter_le_inter_of_forall U _ _ (fun a =>
    (hi (i01 a)).elim (fun e => ⟨0, e.symm⟩) (fun e => ⟨1, e.symm⟩))

open Classical in

noncomputable def twoCochain (s : P.obj (op (inter U i01))) : Cochain P U 1 := fun i =>
  if h : i 0 = i 1 then 0 else
    if i 0 = 0 then res P (inter_le_inter_zero_one U h) s else -res P (inter_le_inter_zero_one U h) s

theorem d_twoCochain (s : P.obj (op (inter U i01))) : d P U 1 (twoCochain P U s) = 0 := by
  funext j
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, j = ![a, b, c] := ⟨_, _, _, vec3_eq j⟩
  rw [d_one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [twoCochain, res_res]

theorem twoCochain_zero_one (s : P.obj (op (inter U i01))) : twoCochain P U s i01 = s := by
  simp [twoCochain]

theorem cechOneToQuot_surjective : Function.Surjective (cechOneToQuot P U) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H s =>
  exact ⟨cls (twoCochain P U s) (d_twoCochain P U s), by
    rw [cechOneToQuot_cls, twoCochain_zero_one]⟩

variable {P} in

noncomputable def twoQuotMap {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') :
    TwoQuot P U →+ TwoQuot P' U :=
  QuotientAddGroup.map _ _ (φ.app (op (inter U i01))).hom (by
    rintro _ ⟨τ, rfl⟩
    refine ⟨push U φ 0 τ, ?_⟩
    change (d P' U 0 (push U φ 0 τ)) i01 = φ.app _ ((d P U 0 τ) i01)
    rw [← push_d]
    rfl)

end TwoOpens3

end GroundTheory.Arith.Modular
end

section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Overlap

noncomputable abbrev varZY : HomRing W := var W 2 * var W 1

theorem varZY_mem : varZY W ∈ homGrading W 2 := SetLike.mul_mem_graded (var_mem W 2) (var_mem W 1)

noncomputable abbrev mapZ : Away (homGrading W) (var W 2) →+* Away (homGrading W) (varZY W) :=
  awayMap (homGrading W) (var_mem W 1) rfl

noncomputable abbrev mapY : Away (homGrading W) (var W 1) →+* Away (homGrading W) (varZY W) :=
  awayMap (homGrading W) (var_mem W 2) (mul_comm _ _)

theorem chartZEquiv_frac (k : Fin 3) : chartZEquiv W (frac W 2 k) = dehomZ W (X k) := by
  rw [chartZEquiv, awayEquiv_apply]
  exact awayTo_mk W (dehomZ W) (dehomZ_X_two W) (dehomZ_cubic W) 1 (X k) _

theorem chartYEquiv_frac (k : Fin 3) : chartYEquiv W (frac W 1 k) = dehomY W (X k) := by
  rw [chartYEquiv, awayEquiv_apply]
  exact awayTo_mk W (dehomY W) (dehomY_X_one W) (dehomY_cubic W) 1 (X k) _

theorem isLocalizationElem_eq :
    Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1) = frac W 2 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_frac, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, vinv,
    IsLocalization.Away.invSelf]
  simp

theorem chartZEquiv_isLocalizationElem :
    chartZEquiv W (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1)) =
      yC W := by
  rw [isLocalizationElem_eq, chartZEquiv_frac]
  simp [dehomZ]

@[instance_reducible]
noncomputable def overlapAlgebra : Algebra (Away (homGrading W) (var W 2)) (Away (homGrading W) (varZY W)) :=
  (mapZ W).toAlgebra

attribute [local instance] overlapAlgebra

instance : IsLocalization.Away
    (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2) (var_mem W 1))
    (Away (homGrading W) (varZY W)) :=
  Away.isLocalization_mul (var_mem W 2) (var_mem W 1) rfl one_ne_zero

theorem map_powers_isLocalizationElem :
    (Submonoid.powers (Away.isLocalizationElem (𝒜 := homGrading W) (var_mem W 2)
      (var_mem W 1))).map (chartZEquiv W).toMonoidHom = Submonoid.powers (yC W) := by
  rw [Submonoid.map_powers]
  congr 1
  exact chartZEquiv_isLocalizationElem W

noncomputable def overlapEquiv : Away (homGrading W) (varZY W) ≃+* Overlap W :=
  IsLocalization.ringEquivOfRingEquiv _ _ (chartZEquiv W) (map_powers_isLocalizationElem W)

theorem overlapEquiv_mapZ (a : Away (homGrading W) (var W 2)) :
    overlapEquiv W (mapZ W a) = algebraMap _ (Overlap W) (chartZEquiv W a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (map_powers_isLocalizationElem W) a

theorem mapY_frac_mul (k : Fin 3) :
    mapY W (frac W 1 k) * mapZ W (frac W 2 1) = mapZ W (frac W 2 k) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, frac, awayMap_mk, Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, pow_one]
  ring

theorem mapY_scalarAway (r : R) : mapY W (scalarAway W 1 r) = mapZ W (scalarAway W 2 r) := by
  simp only [scalarAway, RingHom.comp_apply, awayMap_fromZeroRingHom]

theorem chartYEquiv_symm_xI : (chartYEquiv W).symm (xI W) = frac W 1 0 := by
  rw [RingEquiv.symm_apply_eq, chartYEquiv_frac]
  simp [dehomY]

theorem chartYEquiv_symm_zI : (chartYEquiv W).symm (zI W) = frac W 1 2 := by
  rw [RingEquiv.symm_apply_eq, chartYEquiv_frac]
  simp [dehomY]

theorem chartYEquiv_symm_algebraMap (r : R) :
    (chartYEquiv W).symm (algebraMap R _ r) = scalarAway W 1 r := by
  rw [RingEquiv.symm_apply_eq, chartYEquiv_scalarAway]

theorem overlapEquiv_mapY_frac (k : Fin 3) :
    overlapEquiv W (mapY W (frac W 1 k)) =
      algebraMap _ (Overlap W) (dehomZ W (X k)) * yInv W := by
  have h := congrArg (overlapEquiv W) (mapY_frac_mul W k)
  rw [map_mul, overlapEquiv_mapZ, overlapEquiv_mapZ, chartZEquiv_frac, chartZEquiv_frac] at h
  have hy : dehomZ W (X 1) = yC W := by simp [dehomZ]
  rw [hy] at h
  rw [← h, mul_assoc, yC_mul_yInv, mul_one]

theorem overlapEquiv_mapY (b : Away (homGrading W) (var W 1)) :
    overlapEquiv W (mapY W b) = infToOverlap W (chartYEquiv W b) := by
  obtain ⟨t, rfl⟩ := (chartYEquiv W).symm.surjective b
  rw [RingEquiv.apply_symm_apply]
  change ((overlapEquiv W).toRingHom.comp ((mapY W).comp (chartYEquiv W).symm.toRingHom)) t =
    (infToOverlap W).toRingHom t
  congr 1
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show AdjoinRoot.of (infPolynomial W) (Polynomial.C r) = algebraMap R (InfChart W) r from rfl,
        chartYEquiv_symm_algebraMap, mapY_scalarAway, overlapEquiv_mapZ, chartZEquiv_scalarAway,
        AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show AdjoinRoot.of (infPolynomial W) Polynomial.X = zI W from rfl, chartYEquiv_symm_zI,
        overlapEquiv_mapY_frac, infToOverlap_zI]
      simp [dehomZ]
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show AdjoinRoot.root (infPolynomial W) = xI W from rfl, chartYEquiv_symm_xI,
      overlapEquiv_mapY_frac, infToOverlap_xI]
    simp [dehomZ, xC]

end Overlap

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Cover

noncomputable abbrev cover : Fin 2 → (Curve W).Opens :=
  ![Proj.basicOpen (homGrading W) (var W 2), Proj.basicOpen (homGrading W) (var W 1)]

noncomputable abbrev strPresheaf : (Opens (Curve W).toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (modulesAb (structureSheafModule (Curve W))).obj

theorem inter_cover_zero : inter (cover W) ![(0 : Fin 2)] = Proj.basicOpen (homGrading W) (var W 2) := by
  simp [inter]

theorem inter_cover_one : inter (cover W) ![(1 : Fin 2)] = Proj.basicOpen (homGrading W) (var W 1) := by
  simp [inter]

theorem inter_cover_zero_one : inter (cover W) i01 = Proj.basicOpen (homGrading W) (varZY W) := by
  rw [Proj.basicOpen_mul]
  apply le_antisymm
  · exact le_inf (inter_le _ _ 0) (inter_le _ _ 1)
  · intro x hx
    rw [mem_inter_iff]
    intro a
    fin_cases a
    · exact hx.1
    · exact hx.2

noncomputable def secMap {f : HomRing W} {V : (Curve W).Opens}
    (h : V = Proj.basicOpen (homGrading W) f) : Away (homGrading W) f →+* Γ(Curve W, V) :=
  ((Curve W).presheaf.map (homOfLE h.le).op).hom.comp (Proj.awayToSection (homGrading W) f).hom

theorem secMap_bijective {f : HomRing W} {m : ℕ} (hf : f ∈ homGrading W m) (hm : 0 < m)
    {V : (Curve W).Opens} (h : V = Proj.basicOpen (homGrading W) f) :
    Function.Bijective (secMap W h) := by
  subst h
  have : IsIso (Proj.awayToSection (homGrading W) f) :=
    (Proj.basicOpenIsoAway (homGrading W) f hf hm).isIso_hom
  have e : secMap W (rfl : Proj.basicOpen (homGrading W) f = _) =
      (Proj.awayToSection (homGrading W) f).hom := by
    ext a
    simp only [secMap, RingHom.comp_apply]
    rw [show homOfLE (le_refl (Proj.basicOpen (homGrading W) f)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

end Cover

end Weierstrass

section TwoDiffGeneral

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

lemma comp_succAbove_zero' : i01 ∘ Fin.succAbove 0 = ![(1 : Fin 2)] := by
  funext x
  fin_cases x
  rfl

lemma comp_succAbove_one' : i01 ∘ Fin.succAbove 1 = ![(0 : Fin 2)] := by
  funext x
  fin_cases x
  rfl

end TwoDiffGeneral

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Restriction

noncomputable def overlapSecEquiv : Γ(Curve W, inter (cover W) i01) ≃+* Overlap W :=
  (RingEquiv.ofBijective (secMap W (inter_cover_zero_one W))
    (secMap_bijective W (varZY_mem W) two_pos (inter_cover_zero_one W))).symm.trans (overlapEquiv W)

end Restriction

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Quotient

noncomputable def overlapAddEquiv :
    (strPresheaf W).obj (op (inter (cover W) i01)) ≃+ Overlap W where
  toFun s := overlapSecEquiv W s
  invFun t := (overlapSecEquiv W).symm t
  left_inv s := (overlapSecEquiv W).symm_apply_apply s
  right_inv t := (overlapSecEquiv W).apply_symm_apply t
  map_add' s t := map_add (overlapSecEquiv W) s t

open Classical in

noncomputable def cochainOfPair (s₀ : (strPresheaf W).obj (op (inter (cover W) ![(0 : Fin 2)])))
    (s₁ : (strPresheaf W).obj (op (inter (cover W) ![(1 : Fin 2)]))) :
    Cochain (strPresheaf W) (cover W) 0 := fun i =>
  if h : i 0 = 0 then
    res (strPresheaf W) (by
      intro x hx
      rw [mem_inter_iff] at hx ⊢
      intro a
      have := hx 0
      rw [h] at this
      fin_cases a
      exact this) s₀
  else
    res (strPresheaf W) (by
      intro x hx
      rw [mem_inter_iff] at hx ⊢
      intro a
      have := hx 0
      have h1 : i 0 = 1 := by omega
      rw [h1] at this
      fin_cases a
      exact this) s₁

end Quotient

end Weierstrass

end GroundTheory.Arith.Modular
end

section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

section Restrict

lemma presheaf_map_map_apply {Y : Scheme.{u}} {A B C : Y.Opens} (f : op C ⟶ op B) (g : op B ⟶ op A)
    (s : Γ(Y, C)) : Y.presheaf.map g (Y.presheaf.map f s) = Y.presheaf.map (f ≫ g) s := by
  rw [Functor.map_comp, CommRingCat.comp_apply]

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma awayToSection_one_fromZero (z : 𝒜 0) :
    Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun s => (Proj.basicOpen 𝒜 1).topIso.hom s) (ι_appTop_toSpecZero 𝒜 z)
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h
  rw [← h, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact presheaf_map_map_apply _ _ _

lemma awayToSection_fromZero {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (z : 𝒜 0) :
    Proj.awayToSection 𝒜 f (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z))
    (Proj.awayMap_awayToSection 𝒜 hf (one_mul f).symm)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  rw [h, awayToSection_one_fromZero, presheaf_map_map_apply]
  rfl

end Restrict

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Scalars

end Scalars

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section CoverFacts

noncomputable instance curveOver : (Curve W).Over (Spec (.of R)) := ⟨toSpec W⟩

end CoverFacts

section Genus

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

end Genus

end Weierstrass

end GroundTheory.Arith.Modular
end
