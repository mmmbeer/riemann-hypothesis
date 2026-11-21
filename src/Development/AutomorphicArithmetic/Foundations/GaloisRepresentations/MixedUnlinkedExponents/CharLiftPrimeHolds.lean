import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsFacts
import Mathlib.NumberTheory.RamificationInertia.Galois
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamSumOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClTwistEqSelfOfEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalExpBoundHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentsOfSmoothCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem lp_zero' : UpperTheory.Gal.GamX.lp (0 : Multiset ℂˣ) = 1 := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_cons' (a : ℂˣ) (A : Multiset ℂˣ) :
    UpperTheory.Gal.GamX.lp (a ::ₘ A) = (1 - Polynomial.C (a : ℂ) * Polynomial.X) * UpperTheory.Gal.GamX.lp A := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_eval_zero (A : Multiset ℂˣ) : (UpperTheory.Gal.GamX.lp A).eval 0 = 1 := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih => rw [lp_cons', Polynomial.eval_mul, ih]; simp

private theorem lp_ne_zero (A : Multiset ℂˣ) : UpperTheory.Gal.GamX.lp A ≠ 0 := by
  intro h
  have h1 := lp_eval_zero A
  rw [h] at h1
  simp at h1

private theorem lin_eq (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]) =
      Polynomial.C (-(a : ℂ)) * (Polynomial.X - Polynomial.C ((a⁻¹ : ℂˣ) : ℂ)) := by
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  rw [Units.val_inv_eq_inv_val, mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha,
    Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]
  ring

private theorem lin_roots (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]).roots = {((a⁻¹ : ℂˣ) : ℂ)} := by
  rw [lin_eq, Polynomial.roots_C_mul _ (by simp), Polynomial.roots_X_sub_C]

private theorem lp_roots (A : Multiset ℂˣ) :
    (UpperTheory.Gal.GamX.lp A).roots = A.map (fun a => ((a⁻¹ : ℂˣ) : ℂ)) := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih =>
    rw [lp_cons', Polynomial.roots_mul (by rw [← lp_cons']; exact lp_ne_zero _), lin_roots, ih,
      Multiset.map_cons, Multiset.singleton_add]

theorem UpperTheory.Gal.GamX.lpInj :
    UpperTheory.Gal.GamX.LpInj := by
  intro A B h
  have h1 := congrArg Polynomial.roots h
  rw [lp_roots, lp_roots] at h1
  exact Multiset.map_injective (fun a b hab => inv_injective (Units.ext hab)) h1
end

section
noncomputable section

open Polynomial

namespace UpperTheory.Gal.GamX

private lemma lp_zero : lp 0 = 1 := by simp [lp]

private lemma lp_cons (a : ℂˣ) (A : Multiset ℂˣ) :
    lp (a ::ₘ A) = (1 - C ((a : ℂˣ) : ℂ) * X) * lp A := by
  simp [lp]

private lemma lp_nsmul (f : ℕ) (B : Multiset ℂˣ) : lp (f • B) = lp B ^ f := by
  simp [lp, Multiset.map_nsmul, Multiset.prod_nsmul]

private lemma prod_factor {f : ℕ} (hf : 0 < f) (a : ℂ) :
    ∏ u ∈ nthRootsFinset f (1 : ℂ), (1 - C a * (C u * X)) = 1 - C (a ^ f) * X ^ f := by
  classical
  set S := nthRootsFinset f (1 : ℂ) with hS
  have hζ := Complex.isPrimitiveRoot_exp f hf.ne'
  have mem : ∀ u, u ∈ S ↔ u ^ f = 1 := fun u => mem_nthRootsFinset hf 1
  have ne0 : ∀ u ∈ S, u ≠ 0 := by
    intro u hu h0
    rw [mem, h0, zero_pow hf.ne'] at hu
    exact zero_ne_one hu
  have h1 : ∀ w : ℂ[X], ∏ u ∈ S, (w - C u) = w ^ f - 1 := by
    intro w
    have e := congrArg (aeval w) (X_pow_sub_one_eq_prod hf hζ)
    simp only [map_sub, map_one, aeval_X_pow, map_prod, aeval_X, aeval_C,
      Polynomial.algebraMap_eq] at e
    exact e.symm
  have h3 : ∀ w : ℂ[X], ∏ u ∈ S, (w - C u⁻¹) = ∏ u ∈ S, (w - C u) := by
    intro w
    refine Finset.prod_nbij' (fun u => u⁻¹) (fun u => u⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      rw [mem] at hu ⊢
      rw [inv_pow, hu, inv_one]
    · intro u hu
      rw [mem] at hu ⊢
      rw [inv_pow, hu, inv_one]
    · intro u _
      exact inv_inv u
    · intro u _
      exact inv_inv u
    · intro u _
      rfl
  have h2 : ∀ w : ℂ[X], ∏ u ∈ S, (1 - C u * w) = (∏ u ∈ S, (-C u)) * (w ^ f - 1) := by
    intro w
    rw [← h1, ← h3, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro u hu
    have hc : C u * C u⁻¹ = (1 : ℂ[X]) := by
      rw [← C_mul, mul_inv_cancel₀ (ne0 u hu), C_1]
    linear_combination -hc
  have hc : (∏ u ∈ S, (-C u : ℂ[X])) = -1 := by
    have e := h2 0
    simp only [mul_zero, sub_zero, Finset.prod_const_one, zero_pow hf.ne', zero_sub] at e
    linear_combination e
  have key := h2 (C a * X)
  rw [hc] at key
  calc ∏ u ∈ S, (1 - C a * (C u * X)) = ∏ u ∈ S, (1 - C u * (C a * X)) := by
        refine Finset.prod_congr rfl ?_
        intro u _
        ring
    _ = 1 - C (a ^ f) * X ^ f := by
        rw [key, mul_pow, C_pow]
        ring

private lemma prod_lp {f : ℕ} (hf : 0 < f) (A : Multiset ℂˣ) :
    ∏ u ∈ nthRootsFinset f (1 : ℂ), (lp A).comp (C u * X) =
      (lp (A.map (· ^ f))).comp (X ^ f) := by
  induction A using Multiset.induction_on with
  | empty =>
    simp [lp_zero]
  | cons b A ih =>
    rw [Multiset.map_cons, lp_cons, lp_cons, mul_comp, ← ih]
    simp only [mul_comp, sub_comp, one_comp, C_comp, X_comp]
    rw [Finset.prod_mul_distrib, prod_factor hf, Units.val_pow_eq_pow_val]

theorem lpPowOf : LpPowOf := by
  intro hinj f hf A B h
  apply hinj
  classical
  have hζ := Complex.isPrimitiveRoot_exp f hf.ne'
  apply expand_injective hf
  rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow, ← prod_lp hf, lp_nsmul, pow_comp]
  have e : ∀ u ∈ nthRootsFinset f (1 : ℂ), (lp A).comp (C u * X) = (lp B).comp (X ^ f) := by
    intro u hu
    rw [h, comp_assoc, pow_comp, X_comp, mul_pow, ← C_pow, (mem_nthRootsFinset hf 1).1 hu,
      C_1, one_mul]
  rw [Finset.prod_congr rfl e, Finset.prod_const, hζ.card_nthRootsFinset]

end UpperTheory.Gal.GamX
end
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem map_eq_of_injOn {α β : Type*} (S : Set α) (g : α → β) (hg : Set.InjOn g S)
    (A B : Multiset α) (hA : ∀ x ∈ A, x ∈ S) (hB : ∀ x ∈ B, x ∈ S)
    (h : A.map g = B.map g) : A = B := by
  have key : ∀ C : Multiset α, (∀ x ∈ C, x ∈ S) → ∀ ξ ∈ S, C.count ξ = (C.map g).count (g ξ) := by
    intro C hC ξ hξ
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro x hx
    exact ⟨fun e => congrArg g e, fun e => hg hξ (hC x hx) e⟩
  ext ξ
  by_cases hξ : ξ ∈ S
  · rw [key A hA ξ hξ, key B hB ξ hξ, h]
  · rw [Multiset.count_eq_zero_of_notMem (fun m => hξ (hA _ m)),
      Multiset.count_eq_zero_of_notMem (fun m => hξ (hB _ m))]

theorem UpperTheory.Gal.GamX.valsExtOf :
    UpperTheory.Gal.GamX.ValsExtOf := by
  unfold ValsExtOf ValsExt
  intro hP k _ _ _ _ c c' θ h
  have hinj : Set.InjOn (fun ξ : kˣ →* ℂˣ => (ξ * θ) (unif k)) {ξ | IsUnram (ξ * θ)} := by
    intro ξ hξ ξ' hξ' e
    have hu : IsUnram ((ξ * θ) * (ξ' * θ)⁻¹) := isUnram_mul hξ (isUnram_inv hξ')
    exact mul_right_cancel ((hP k).2.1 _ _ hu e)
  exact map_eq_of_injOn _ _ hinj _ _ (fun x hx => (Multiset.mem_filter.1 hx).2)
    (fun x hx => (Multiset.mem_filter.1 hx).2) h
end

section
noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

namespace UpperTheory.Gal.GamX

theorem fdegEq : FdegEq := by
  intro K L _ _ _ _ _ _ v
  refine ⟨GroundTheory.Global.nonempty_placesOver L v, fun w w' => ?_⟩
  have hw := w.2
  have hw' := w'.2
  unfold fdeg
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w'.1.asIdeal]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal Gal(L/K)

end UpperTheory.Gal.GamX
end
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.GamX.twValsOf :
    UpperTheory.Gal.GamX.TwValsOf := by
  intro hNV K L _ _ _ _ _ v d f e hf hne he hA hB c hc θ hθ
  unfold UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal at hNV
  have hv1 : ∀ {k : Type} [Field k] [ValuativeRel k] (a t : kˣ →* ℂˣ),
      vals {a} t = if IsUnram (a * t) then {(a * t) (unif k)} else 0 := by
    intro k _ _ a t
    unfold vals
    rw [Multiset.filter_singleton]
    split_ifs <;> simp
  have hadd : ∀ {k : Type} [Field k] [ValuativeRel k] (c1 c2 : Multiset (kˣ →* ℂˣ)) (t : kˣ →* ℂˣ),
      vals (c1 + c2) t = vals c1 t + vals c2 t := by
    intro k _ _ c1 c2 t
    simp only [vals, Multiset.filter_add, Multiset.map_add]
  induction c using Multiset.induction_on with
  | empty => simp [vals]
  | cons a c ih =>
    have hca : IsSmoothChar a := hc a (Multiset.mem_cons_self a c)
    have ih' := ih (fun ξ h => hc ξ (Multiset.mem_cons_of_mem h))
    have hone : Multiset.map (fun x => x ^ f) (∑ j ∈ Finset.range d, vals {a} (θ * e j)) =
        f • ∑ w : PlacesOver L v, vals (Multiset.map (fun ξ => ξ.comp (nm w)) {a}) (θ.comp (nm w)) := by
      simp only [Multiset.map_singleton, hv1, ← mul_assoc, ← MonoidHom.mul_comp]
      set μ := a * θ with hμ
      have hμs : IsSmoothChar μ := by
        unfold IsSmoothChar at hca hθ ⊢
        have hle : a.ker ⊓ θ.ker ≤ μ.ker := by
          intro x hx
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, hμ, MonoidHom.mul_apply, hx.1, hx.2, mul_one]
        exact Subgroup.isOpen_mono hle (by rw [Subgroup.coe_inf]; exact hca.inter hθ)
      have hcomp : ∀ j (w : PlacesOver L v), (μ * e j).comp (nm w) = μ.comp (nm w) := by
        intro j w
        rw [MonoidHom.mul_comp, he j w, mul_one]
      by_cases hex : ∃ w : PlacesOver L v, IsUnram (μ.comp (nm w))
      · obtain ⟨w1, hw1⟩ := hex
        have hall : ∀ w : PlacesOver L v, IsUnram (μ.comp (nm w)) := fun w => hA w1 w μ hw1
        have hcard := hB w1 μ hμs hw1
        have hsumf : ∑ w' : PlacesOver L v, fdeg w' = Fintype.card (PlacesOver L v) * f := by
          simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have hfpos : 0 < f := by
          have := (hNV K L v w1 μ).2.2.1
          rwa [hf w1] at this
        have hval : ∀ j, IsUnram (μ * e j) → ∀ w : PlacesOver L v,
            μ ((nm w) (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) =
              (μ * e j) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f := by
          intro j hj w
          have h1 := ((hNV K L v w (μ * e j)).1 hj).2
          have h2 : (e j) ((nm w) (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) = 1 := by
            have := congrArg (fun φ => φ (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) (he j w)
            simpa using this
          rw [MonoidHom.mul_apply, h2, mul_one, hf w] at h1
          exact h1
        have hpos : 0 < (Finset.filter (fun j => IsUnram (μ * e j)) (Finset.range d)).card := by
          rw [hcard, hsumf]
          exact Nat.mul_pos (Fintype.card_pos_iff.mpr hne) hfpos
        obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter] at hj0
        refine Eq.trans ((Multiset.eq_replicate (n := Fintype.card (PlacesOver L v) * f)
          (a := (μ * e j0) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f)).mpr ⟨?_, ?_⟩)
          ((Multiset.eq_replicate).mpr ⟨?_, ?_⟩).symm
        · rw [Multiset.card_map, Multiset.card_sum, ← hsumf, ← hcard, Finset.card_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        · intro b hb
          rw [Multiset.mem_map] at hb
          obtain ⟨x, hx, rfl⟩ := hb
          rw [Multiset.mem_sum] at hx
          obtain ⟨j, -, hxj⟩ := hx
          split_ifs at hxj with hj
          · rw [Multiset.mem_singleton] at hxj
            subst hxj
            rw [← hval j hj w1, hval j0 hj0.2 w1]
          · simp at hxj
        · simp only [hall, ↓reduceIte]
          rw [Multiset.card_nsmul, Multiset.card_sum]
          simp [mul_comm]
        · intro b hb
          simp only [hall, ↓reduceIte] at hb
          have hb' := Multiset.mem_of_mem_nsmul hb
          rw [Multiset.mem_sum] at hb'
          obtain ⟨w, -, hbw⟩ := hb'
          rw [Multiset.mem_singleton] at hbw
          rw [hbw, MonoidHom.comp_apply]
          exact hval j0 hj0.2 w
      · push_neg at hex
        have hno : ∀ j, ¬ IsUnram (μ * e j) := by
          intro j hj
          obtain ⟨w0⟩ := hne
          have := ((hNV K L v w0 (μ * e j)).1 hj).1
          rw [hcomp] at this
          exact hex w0 this
        simp [hno, hex]
    rw [← Multiset.singleton_add]
    simp only [hadd, Multiset.map_add, Finset.sum_add_distrib, smul_add]
    rw [hone, ih']
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

theorem gamOneOf : GamOneOf := by
  unfold GamOneOf GamOne
  intro hC hV hS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw s s' hs hs'
  have hsub : Subsingleton (PlacesOver L v) := ⟨fun a b => (hw a).trans (hw b).symm⟩
  have key : ∀ (u : PlacesOver L v) (h : w = u), SuppAt P u.1 (h ▸ s') := by
    rintro u rfl
    exact hs'
  have hval : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      vals (chs s') (θ.comp (nm w)) = vals (up w s) (θ.comp (nm w)) := by
    intro θ hθ
    have h := hS K L hp n hn π P hW v s (fun u => (hw u).symm ▸ s') hs
      (fun u => key u (hw u).symm) θ hθ
    rw [Fintype.sum_subsingleton _ w, Fintype.sum_subsingleton _ w] at h
    exact h
  refine Multiset.ext.2 fun ζ => ?_
  by_cases hT : Thru w ζ
  · obtain ⟨χ, hχ, hu⟩ := id hT
    have hf := hV (w.1.adicCompletion L) (chs s') (up w s) (χ.comp (nm w)) (hval χ hχ)
    have hc := congrArg (Multiset.count ζ) hf
    rw [Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu,
      Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu] at hc
    rw [Multiset.count_filter_of_pos hT]
    exact hc
  · rw [Multiset.count_filter_of_neg hT, eq_comm, Multiset.count_eq_zero]
    intro hm
    obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hm
    exact hT ⟨ξ⁻¹, ((hC _ s).2.1 ξ hξ).inv, fun x _ => by simp⟩

end UpperTheory.Gal.GamX
end
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.nmEq :
    UpperTheory.Gal.GamX.NmEq := by
  intro K L _ _ _ _ _ v w
  rfl
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem chs_cons_some (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL k)) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s := by
  have h : ∃ η : kˣ →* ℂˣ, ∃ hη : IsSmoothChar η, IrrGL.ofChar ξ hξ = IrrGL.ofChar η hη := ⟨ξ, hξ, rfl⟩
  have hc : h.choose = ξ := by
    obtain ⟨hη, he⟩ := h.choose_spec
    exact (IrrGL.ofChar_inj.mp he).symm
  unfold chs
  rw [Multiset.filterMap_cons_some _ _ _ (by rw [dif_pos h])]
  rw [hc]

private theorem chs_cons_not {y : IrrGL k} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL k)) : chs (y ::ₘ s) = chs s := by
  unfold chs
  rw [Multiset.filterMap_cons_none _ _ (by rw [dif_neg hy])]

end Loc

theorem UpperTheory.Gal.GamX.chsTr :
    UpperTheory.Gal.GamX.ChsTr := by
  intro k k' _ _ _ _ _ _ _ _ i hi' s
  induction s using Multiset.induction_on with
  | empty => simp [chs_zero]
  | cons y s ih =>
    rw [Multiset.map_cons]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      have hξ' : IsSmoothChar (ξ.comp (Units.map (i.symm : k' →* k))) :=
        hξ.comp _ (Units.continuous_map hi')
      rw [GlobalTheory.CharLiftStep.trGL_ofChar i hi' ξ hξ _ hξ' (fun _ => rfl), chs_cons_some, chs_cons_some,
        Multiset.map_cons, ih]
    · have hy' : ¬ ∃ ξ : k'ˣ →* ℂˣ, ∃ hξ, GlobalTheory.SuppIne.trGL i hi' y = IrrGL.ofChar ξ hξ := by
        rintro ⟨ξ, hξ, he⟩
        have h1 : y.fst = 1 := congrArg Sigma.fst he
        exact hy (GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y h1)
      rw [chs_cons_not hy', chs_cons_not hy, ih]
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.splitSuppOf :
    UpperTheory.Gal.GamX.SplitSuppOf := by
  unfold UpperTheory.Gal.GamX.SplitSuppOf
  intro hNm hSF hWS hSS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw
  haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2
  rcases GlobalTheory.CharLiftStep.cycAt_or_split hp v w.1 with hc | ⟨he, hf⟩
  · exfalso
    refine hw fun u => ?_
    haveI : u.1.asIdeal.LiesOver v.asIdeal := u.2
    have hu : u.1.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.1.asIdeal) (p := v.asIdeal)).symm
    obtain ⟨-, -, -, h⟩ := hc
    exact Subtype.ext (h u.1 hu)
  · obtain ⟨hi', hN⟩ := GlobalTheory.CharLiftStep.normU_of_split v w.1 he hf
    set i := RingEquiv.ofBijective _ (GlobalTheory.CharLiftStep.bijective_of_split v w.1 he hf) with hidef
    have hi : Continuous i := GroundTheory.Global.continuous_adicCompletionMap v w.1
    have hcomp : ∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) :=
      GroundTheory.Global.adicCompletionMap_algebraMap v w.1
    refine ⟨i, hi', hi, hcomp, ?_, ?_⟩
    · rw [hNm K L v w]
      exact MonoidHom.ext fun y => Units.ext (hN y)
    · rintro s s' ⟨τ, hτ, h⟩ ⟨τ', hτ', h'⟩
      haveI : Fact (Module.finrank K L).Prime := ⟨hp⟩
      haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
      obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hW' : WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat := hW
      obtain ⟨e, he'⟩ := hSS K L σ hσ hp n hn π P (hWS K L hp n hn π P hW').1 hW' v w.1 i hi hcomp τ τ' hτ hτ'
      have hg : ∀ g : GL (Fin n) (w.1.adicCompletion L),
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv (τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) τ'.ρ :=
        Representation.Equiv.mk e fun g => LinearMap.ext fun x => by
          simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp]
          exact (he' _ x).trans (congrArg (fun g' => τ'.ρ g' (e x)) (hg g))
      have h2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' h).of_equiv φ
      exact (hSF L n hn P w.1).2.1 s' _ ⟨τ', hτ', h'⟩ ⟨τ', hτ', h2⟩
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem chs_single {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) : chs ({IrrGL.ofChar ξ hξ} : Multiset (IrrGL k)) = {ξ} := by
  have hex : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ hξ = IrrGL.ofChar ζ hζ := ⟨ξ, hξ, rfl⟩
  have hc : hex.choose = ξ := by
    obtain ⟨hζ, e⟩ := hex.choose_spec
    exact (IrrGL.ofChar_inj.1 e).symm
  unfold chs
  rw [← Multiset.cons_zero (IrrGL.ofChar ξ hξ), Multiset.filterMap_cons_some _ _ _ (b := ξ) (by rw [dif_pos hex, hc])]
  simp

theorem UpperTheory.Gal.GamX.rkSupp :
    UpperTheory.Gal.GamX.RkSupp := by
  unfold RkSupp
  intro K _ _ _ π ψ hπ v s hs
  obtain ⟨σ, hσ, h⟩ := id hs
  have h1 := GlobalTheory.rankOne_algNorm_locComp K π ψ hπ v σ hσ
  have h2 : IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar (ψ.loc v) (ParLaws.isSmoothChar_loc ψ v) := by
    rw [← h1]
    simp [GlobalTheory.GalOfCusp.algNorm]
  have hc : (IrrGL.of σ.ρ σ.smooth σ.irred).IsCusp := h2 ▸ IrrGL.isCusp_ofChar _ _
  have h3 : SuppAt π v {IrrGL.of σ.ρ σ.smooth σ.irred} :=
    ⟨σ, hσ, (hasSupport_self hc).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm⟩
  have h4 := (UpperTheory.V.Z.Gam.suppFacts K 1 le_rfl π v).2.1 _ _ hs h3
  rw [h4, h2, chs_single]
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem loc_one_of' {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

private theorem eq_of_ae {L : Type} [Field L] [NumberField L] (a b : HChar L)
    (h : ∀ᶠ u : HeightOneSpectrum (𝓞 L) in Filter.cofinite, a.UnrAt u ∧ b.UnrAt u ∧ a.val u = b.val u) : a = b := by
  let ρ : HChar L := a * b⁻¹
  have hl : ∀ u x, ρ.loc u x = a.loc u x * (b.loc u x)⁻¹ := fun _ _ => rfl
  have hev : ∀ᶠ u : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ρ.UnrAt u ∧ ρ.val u = 1 := by
    filter_upwards [h] with u hu
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hl, hu.1 x hx, hu.2.1 x hx]; simp
    · have e : ρ.val u = a.val u * (b.val u)⁻¹ := rfl
      rw [e, hu.2.2, mul_inv_cancel]
  have h1 : ρ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ρ.1 ρ.2.1 ρ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of' ρ w this.1 this.2 y
  have h2 : ρ = 1 := Subtype.ext h1
  exact mul_inv_eq_one.1 h2

theorem UpperTheory.Gal.GamX.rkLiftOf :
    UpperTheory.Gal.GamX.RkLiftOf := by
  unfold RkLiftOf RkLift
  intro hN K L _ _ _ _ _ _ _ ψ ψ' hW v w
  obtain ⟨ξ, hξ⟩ := hN K L ψ
  suffices e : ψ' = ξ by rw [e]; exact (hξ v w).1
  refine eq_of_ae _ _ ?_
  filter_upwards [hW, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ')] with u h1 h2 h3
  have h2' : ψ.UnrAt (u.under (𝓞 K)) := h2
  have h3' : ψ'.UnrAt u := h3
  have hl : u.asIdeal.LiesOver (u.under (𝓞 K)).asIdeal := ⟨rfl⟩
  obtain ⟨-, hu, d⟩ := hξ (u.under (𝓞 K)) ⟨u, hl⟩
  obtain ⟨b, c⟩ := hu h2'
  have hnv : ∀ {F : Type} [Field F] [NumberField F] (x : HeightOneSpectrum (𝓞 F)), normV x = Ideal.absNorm x.asIdeal :=
    fun x => by rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hf : normV u = normV (u.under (𝓞 K)) ^ fdeg (⟨u, hl⟩ : PlacesOver L (u.under (𝓞 K))) := by
    rw [hnv, hnv]; exact d
  obtain ⟨B, hB, hB'⟩ := h1 _ hf
  obtain rfl := CG.HasSat.unique hB (CG.hasSat_ofChar h2')
  have e := CG.HasSat.unique hB' (CG.hasSat_ofChar h3')
  rw [Multiset.map_singleton, Multiset.singleton_inj] at e
  exact ⟨h3', b, e.symm.trans c.symm⟩
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.upThruOf :
    UpperTheory.Gal.GamX.UpThruOf := by
  unfold UpThruOf UpThru
  intro hC K L _ _ _ _ _ v w s
  rw [Multiset.filter_eq_self]
  intro ζ hζ
  obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hζ
  have hs : IsSmoothChar ξ := (hC _ s).2.1 ξ hξ
  refine ⟨ξ⁻¹, IsSmoothChar.inv hs, fun x _ => by simp⟩
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def CharSupp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
      (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : SmIrr (GL (Fin n) (u.adicCompletion L))), π.IsLocComp v τ → P.IsLocComp u T →
      ∀ (ξ : Fin n → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (GlobalTheory.RoadU.chars ξ hξ) →
        HasSupport T.ρ (GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
          fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

def CharLiftPrime : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub K a) (P : CuspSub L a),
    GlobalTheory.GalCut.IsLift π P → GlobalTheory.RoadU.CharLift π P

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chs_cons (ξ : kˣ →* ℂˣ) (h : IsSmoothChar ξ) (s : Multiset (IrrGL k)) : chs (IrrGL.ofChar ξ h ::ₘ s) = ξ ::ₘ chs s := by
  have e : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ h = IrrGL.ofChar ζ hζ := ⟨ξ, h, rfl⟩
  refine Multiset.filterMap_cons_some _ _ _ ?_
  rw [dif_pos e]
  obtain ⟨_, h2⟩ := e.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

theorem chs_cons_of_not {y : IrrGL k} (h : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (s : Multiset (IrrGL k)) :
    chs (y ::ₘ s) = chs s := Multiset.filterMap_cons_none _ _ (dif_neg h)

theorem chs_map {ι : Type} (t : Multiset ι) (ξ : ι → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) :
    chs (t.map fun j => IrrGL.ofChar (ξ j) (hξ j)) = t.map ξ := by
  induction t using Multiset.induction with
  | empty => rfl
  | cons a t ih => rw [Multiset.map_cons, chs_cons, ih, Multiset.map_cons]

theorem card_chs_le (s : Multiset (IrrGL k)) (h : ∀ y ∈ s, 0 < y.1) :
    Multiset.card (chs s) ≤ (s.map Sigma.fst).sum ∧
      (Multiset.card (chs s) = (s.map Sigma.fst).sum → ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) := by
  induction s using Multiset.induction with
  | empty => exact ⟨le_rfl, fun _ y hy => absurd hy (Multiset.notMem_zero _)⟩
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    have ha := h a (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases c : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, a = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := c
      have e : (IrrGL.ofChar ξ hξ).1 = 1 := rfl
      rw [chs_cons, Multiset.card_cons, e]
      refine ⟨by omega, fun H y hy => ?_⟩
      rcases Multiset.mem_cons.1 hy with rfl | hy
      · exact ⟨ξ, hξ, rfl⟩
      · exact h2 (by omega) y hy
    · rw [chs_cons_of_not c]
      exact ⟨by omega, fun H => by omega⟩

theorem eq_of_chs {s t : Multiset (IrrGL k)} (hs : ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (ht : ∀ y ∈ t, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (h : chs s = chs t) : s = t := by
  have key : ∀ s : Multiset (IrrGL k), (∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) →
      s = (chs s).map fun ξ => if h : IsSmoothChar ξ then IrrGL.ofChar ξ h else IrrGL.ofChar 1 isSmoothChar_one := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; rfl
    | cons a s ih =>
      intro H
      obtain ⟨ξ, hξ, rfl⟩ := H a (Multiset.mem_cons_self _ _)
      rw [chs_cons, Multiset.map_cons, dif_pos hξ, ← ih fun y hy => H y (Multiset.mem_cons_of_mem hy)]
  rw [key s hs, key t ht, h]

end

theorem charSupp_of (h1 : GamMixed) (h2 : NmEq) (h3 : SuppFacts) : CharSupp := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hW v u hu τ T hτ hT ξ hξ hs
  obtain ⟨⟨s', hs'⟩, huniq, hdeg, -⟩ := h3 L n hn P u
  have H := h1 K L hp n hn π P hW v ⟨u, hu⟩ _ s' ⟨τ, hτ, hs⟩ hs'
  obtain ⟨-, hsum, hpos⟩ := hdeg s' hs'
  obtain ⟨c1, c2⟩ := card_chs_le s' hpos
  rw [up, GlobalTheory.RoadU.chars, chs_map, h2 K L v ⟨u, hu⟩, Multiset.map_map] at H
  have hc : Multiset.card ((chs s').filter (Thru (v := v) ⟨u, hu⟩)) = n := by rw [H]; simp
  have hle := Multiset.filter_le (Thru (v := v) ⟨u, hu⟩) (chs s')
  have hc' := Multiset.card_le_card hle
  have e := Multiset.eq_of_le_of_card_le hle (by omega)
  have es : s' = GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    refine eq_of_chs (c2 (by omega)) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
      exact ⟨_, _, rfl⟩
    · rw [← e, H, GlobalTheory.RoadU.chars, chs_map]; rfl
  obtain ⟨T', hT', hs''⟩ := hs'
  have h1 : (CG.mk P).IsLoc u (Quotient.mk _ T) := hT
  have h2 : (CG.mk P).IsLoc u (Quotient.mk _ T') := hT'
  obtain ⟨φ⟩ := Quotient.exact (CG.IsLoc.unique L n _ u _ _ h2 h1)
  exact es ▸ hs''.of_equiv φ

theorem charLiftPrime_of (h : CharSupp) : CharLiftPrime := by
  intro K L _ _ _ _ _ _ _ _ hp a ha π P hL
  refine ⟨hL, fun v u _ => h K L hp a ha π P ?_ v u⟩
  unfold WeakBC
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
    (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL K a π)] with w hw
  obtain ⟨B, hB⟩ := hw
  exact fun f hf => ⟨B, hB, hL.sat w f B hf hB⟩

end UpperTheory.Gal.GamX
end
end

section
namespace UpperTheory.Gal.GamX

open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

theorem gamSum_holds : GamSum :=
  gamSumOf matchBCX normCnt normVal (lpPowOf lpInj) chsFacts fdegEq (twValsOf normVal)

theorem gamOne_holds : GamOne := gamOneOf chsFacts (valsExtOf polFacts) gamSum_holds

theorem splitSupp_holds : SplitSupp :=
  splitSuppOf nmEq suppFacts Sph.weakStable
    (splitStrong (descStep (coreDesc ci Sph.gm) (liftAll (liftStep (coreLift ci Sph.gm)))))

theorem gamMixed_holds : GamMixed :=
  gamMixed_of gamOne_holds splitSupp_holds chsTr rkSupp (rkLiftOf UpperTheory.V.Z.Gam.normLoc) (upThruOf chsFacts)

theorem charSupp_holds : CharSupp := charSupp_of gamMixed_holds nmEq suppFacts

theorem charLiftPrime_holds : CharLiftPrime := charLiftPrime_of charSupp_holds

end UpperTheory.Gal.GamX
end
