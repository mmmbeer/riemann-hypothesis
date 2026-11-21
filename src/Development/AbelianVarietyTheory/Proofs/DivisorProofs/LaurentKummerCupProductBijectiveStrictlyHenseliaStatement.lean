import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPrimitiveVectorCompactRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StrictlyHenselianIsColimit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_zero_of_geometric_points : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ) (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  first | (exact @GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (exact GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (intros; apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MultiplicativeGroupGlobalSections

open LaurentPolynomial in

theorem laurent_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S}
    (hC : f.comp C = g.comp C) (hT : f (T 1) = g (T 1)) : f = g := by
  have h1 : f (T 1) * f (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have h2 : g (T 1) * g (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have hTm : f (T (-1)) = g (T (-1)) :=
    calc f (T (-1)) = f (T (-1)) * (g (T 1) * g (T (-1))) := by rw [h2, mul_one]
      _ = (f (T 1) * f (T (-1))) * g (T (-1)) := by rw [← hT]; ring
      _ = g (T (-1)) := by rw [h1, one_mul]
  have hTn : ∀ n : ℤ, f (T n) = g (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [T_zero]
    | succ n ih => rw [T_add, map_mul, map_mul, ih, hT]
    | pred n ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hTm]
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [single_eq_C]
    exact congrArg (fun φ : R →+* S => φ b) hC
  · intro n
    exact hTn n

theorem pull_spMap_id (q : ℕ) (A : Type) [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ n x = x := by
  have h : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap]
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]
  rw [h, pull_id]

open LaurentPolynomial GmPhiNat in

theorem exists_ht_zero_pull_laurent_eq (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial R)) 0 i) :
    ∃ z : Ht q (sp R) 0 i, pull _ (spMap (LaurentPolynomial.C : R →+* LaurentPolynomial R)) _ 0 z = y := by
  let ev₁ : LaurentPolynomial R →+* R := eval₂ (RingHom.id R) 1
  have hev : ev₁.comp C = RingHom.id R := RingHom.ext fun a => eval₂_C _ _ a
  refine ⟨pull _ (spMap ev₁) _ 0 y, ?_⟩
  symm
  rw [← sub_eq_zero]
  have hqL : IsUnit (q : LaurentPolynomial R) := by simpa using hq.map (C : R →+* LaurentPolynomial R)
  apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom q (LaurentPolynomial R) hqL i
  intro K _ _ f
  set y' := y - pull _ (spMap (C : R →+* LaurentPolynomial R)) _ 0 (pull _ (spMap ev₁) _ 0 y) with hy'

  have h0 : pull _ (spMap ev₁) _ 0 y' = 0 := by
    rw [hy', map_sub, ← pull_spMap_comp, hev, pull_spMap_id, sub_self]
  let f₀ : R →+* K := f.comp C
  have hT1 : IsUnit (f (T 1)) := by
    refine isUnit_iff_exists_inv.2 ⟨f (T (-1)), ?_⟩
    rw [← map_mul, ← T_add]; simp
  let u : Kˣ := hT1.unit
  let evu : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) u
  have hf : f = evu.comp (laurentMap f₀) := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc]
      ext a
      simp [evu, f₀, eval₂_C]
    · simp [evu, laurentMap_T, eval₂_T, u]
  let ev₁K : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) 1
  have hevK : ev₁K.comp C = RingHom.id K := RingHom.ext fun a => eval₂_C _ _ a
  have hcomm : ev₁K.comp (laurentMap f₀) = f₀.comp ev₁ := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc, hevK, RingHom.comp_assoc, hev]
      rfl
    · simp [ev₁K, ev₁, laurentMap_T, eval₂_T]
  have hqK : IsUnit (q : K) := by simpa using hq.map f₀
  have hζ : ∃ ζ : K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  have hbij := GlobalTheory.EtC.h_zero_pull_bijective q K (LaurentPolynomial K) (C : K →+* LaurentPolynomial K) hqK hζ
    inferInstance (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i
  have hw : pull _ (spMap (laurentMap f₀)) _ 0 y' = 0 := by
    obtain ⟨v, hv⟩ := hbij.2 (pull _ (spMap (laurentMap f₀)) _ 0 y')
    have hv0 : v = 0 := by
      have e1 : pull _ (spMap ev₁K) _ 0 (pull _ (spMap (C : K →+* LaurentPolynomial K)) _ 0 v) = v := by
        rw [← pull_spMap_comp, hevK, pull_spMap_id]
      rw [← e1, hv, ← pull_spMap_comp, hcomm, pull_spMap_comp, h0, map_zero]
    rw [← hv, hv0, map_zero]
  rw [hf, pull_spMap_comp, hw, map_zero]

end GlobalTheory.EtC.MultiplicativeGroupGlobalSections

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T], IsUnit (q : T) → ∀ (i : ℤ) (y : Ht q (sp (LaurentPolynomial T)) 0 i), ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y := by
  first | (exact @GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (exact GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (intros; apply GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Simplicial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.KerLaurent

theorem laurent_ext {R S : Type} [CommRing R] [CommRing S] {φ ψ : LaurentPolynomial R →+* S}
    (hC : ∀ a, φ (LaurentPolynomial.C a) = ψ (LaurentPolynomial.C a))
    (hT : φ (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)) : φ = ψ := by
  have h1 : LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1) = (1 : LaurentPolynomial R) := by
    rw [← LaurentPolynomial.T_add]; simp
  have hTm : φ (LaurentPolynomial.T (-1)) = ψ (LaurentPolynomial.T (-1)) := by
    have a := congrArg φ h1
    have b := congrArg ψ h1
    rw [map_mul, map_one] at a b
    rw [hT] at a
    calc φ (LaurentPolynomial.T (-1)) = φ (LaurentPolynomial.T (-1)) * (ψ (LaurentPolynomial.T 1) * ψ (LaurentPolynomial.T (-1))) := by
          rw [b, mul_one]
      _ = (ψ (LaurentPolynomial.T 1) * φ (LaurentPolynomial.T (-1))) * ψ (LaurentPolynomial.T (-1)) := by ring
      _ = ψ (LaurentPolynomial.T (-1)) := by rw [a, one_mul]
  have hTn : ∀ n : ℤ, φ (LaurentPolynomial.T n) = ψ (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => rw [LaurentPolynomial.T_zero, map_one, map_one]
    | succ k ih => rw [LaurentPolynomial.T_add, map_mul, map_mul, ih, hT]
    | pred k ih => rw [sub_eq_add_neg, LaurentPolynomial.T_add, map_mul, map_mul, ih, hTm]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, hp, hr]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hTn]

def ev1 (R : Type) [CommRing R] : LaurentPolynomial R →+* R := LaurentPolynomial.eval₂ (RingHom.id R) 1

def flat (R : Type) [CommRing R] : LaurentPolynomial R →+* LaurentPolynomial R :=
  (LaurentPolynomial.C : R →+* LaurentPolynomial R).comp (ev1 R)

theorem laurentPolynomialEvalAtOne_C (R : Type) [CommRing R] (a : R) : ev1 R (LaurentPolynomial.C a) = a := by
  simp [ev1, LaurentPolynomial.eval₂_C]

theorem eval_one_T (R : Type) [CommRing R] (n : ℤ) : ev1 R (LaurentPolynomial.T n) = 1 := by
  simp [ev1, LaurentPolynomial.eval₂_T]

theorem flat_comp_C (R : Type) [CommRing R] :
    (flat R).comp (LaurentPolynomial.C : R →+* LaurentPolynomial R) = LaurentPolynomial.C :=
  RingHom.ext fun a => by simp [flat, laurentPolynomialEvalAtOne_C]

theorem laurentPolynomialEvalAtOne_comp_mapRingHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    (ev1 S).comp (laurentMap f) = f.comp (ev1 R) := by
  refine laurent_ext (fun a => ?_) ?_
  · have h := RingHom.congr_fun (GmPhiNat.laurentMap_C f) a
    simp only [RingHom.comp_apply] at h ⊢
    rw [h, laurentPolynomialEvalAtOne_C, laurentPolynomialEvalAtOne_C]
  · simp only [RingHom.comp_apply]
    rw [GmPhiNat.laurentMap_T, eval_one_T, eval_one_T, map_one]

theorem flat_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    (laurentMap f).comp (flat R) = (flat S).comp (laurentMap f) := by
  change ((laurentMap f).comp LaurentPolynomial.C).comp (ev1 R) = LaurentPolynomial.C.comp ((ev1 S).comp (laurentMap f))
  rw [GmPhiNat.laurentMap_C, laurentPolynomialEvalAtOne_comp_mapRingHom]
  rfl

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev fB : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev fT : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constArr : Arrow.mk (yoneda.map (fT A A')) ⟶ Arrow.mk (yoneda.map (fB A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [GmPhiNat.laurentMap_C])

def oneArr : Arrow.mk (yoneda.map (fB A A')) ⟶ Arrow.mk (yoneda.map (fT A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (ev1 A')))) (yoneda.map (Spec.map (CommRingCat.ofHom (ev1 A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentPolynomialEvalAtOne_comp_mapRingHom])

def cP : cech (fT A A') ⟶ cech (fB A A') := Arrow.mapCechNerve (constArr A A')

def cS : cech (fB A A') ⟶ cech (fT A A') := Arrow.mapCechNerve (oneArr A A')

abbrev inc : Fin (1 + 1) → (A' →+* A' ⊗[A] A') :=
  ![Algebra.TensorProduct.includeLeftRingHom, (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom]

theorem inc_comp (j : Fin (1 + 1)) : (inc A A' j).comp (algebraMap A A') = (inc A A' 0).comp (algebraMap A A') := by
  refine RingHom.ext fun a => ?_
  fin_cases j
  · rfl
  · change (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a) =
      (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a)
    rw [AlgHom.commutes, AlgHom.commutes]

theorem laurent_univ (R : Type) [CommRing R] (g : Fin (1 + 1) → (LaurentPolynomial A' →+* R))
    (hg : ∀ j, (g j).comp (laurentMap (algebraMap A A')) = (g 0).comp (laurentMap (algebraMap A A'))) :
    ∃! φ : LaurentPolynomial (A' ⊗[A] A') →+* R, ∀ j, φ.comp (laurentMap (inc A A' j)) = g j := by
  have hLC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (a : S),
      laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) :=
    fun f a => RingHom.congr_fun (GmPhiNat.laurentMap_C f) a
  have hgC : ∀ (j : Fin (1 + 1)) (a : A), g j (LaurentPolynomial.C (algebraMap A A' a)) =
      g 0 (LaurentPolynomial.C (algebraMap A A' a)) := by
    intro j a
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.C a)
    simp only [RingHom.comp_apply, hLC] at this
    exact this
  have hgT : ∀ j : Fin (1 + 1), g j (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := by
    intro j
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.T 1)
    simp only [RingHom.comp_apply, GmPhiNat.laurentMap_T] at this
    exact this
  letI : Algebra A R := ((g 0).comp ((LaurentPolynomial.C : A' →+* LaurentPolynomial A').comp (algebraMap A A'))).toAlgebra
  let g0 : A' →ₐ[A] R := ⟨(g 0).comp LaurentPolynomial.C, fun r => rfl⟩
  let g1 : A' →ₐ[A] R := ⟨(g 1).comp LaurentPolynomial.C, fun r => by
    change g 1 (LaurentPolynomial.C (algebraMap A A' r)) = g 0 (LaurentPolynomial.C (algebraMap A A' r))
    exact hgC 1 r⟩
  let ψ0 : A' ⊗[A] A' →ₐ[A] R := Algebra.TensorProduct.lift g0 g1 (fun _ _ => Commute.all _ _)
  let u : Rˣ := Units.map (g 0 : LaurentPolynomial A' →* R) (laurentVarUnit A')
  have hu : (u : R) = g 0 (LaurentPolynomial.T 1) := rfl
  let ψ : LaurentPolynomial (A' ⊗[A] A') →+* R := LaurentPolynomial.eval₂ ψ0.toRingHom u
  have hψC : ∀ x, ψ (LaurentPolynomial.C x) = ψ0 x := fun x => LaurentPolynomial.eval₂_C _ _ _
  have hψT : ψ (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := by
    simp [ψ, LaurentPolynomial.eval₂_T, hu]
  refine ⟨ψ, fun j => ?_, fun φ hφ => ?_⟩
  · refine laurent_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, hLC, hψC]
      fin_cases j
      · change ψ0 (a ⊗ₜ 1) = g 0 (LaurentPolynomial.C a)
        simp [ψ0, g0]
      · change ψ0 (1 ⊗ₜ a) = g 1 (LaurentPolynomial.C a)
        simp [ψ0, g1]
    · simp only [RingHom.comp_apply, GmPhiNat.laurentMap_T, hψT, hgT j]
  · have hC : ∀ x, φ (LaurentPolynomial.C x) = ψ (LaurentPolynomial.C x) := by
      intro x
      rw [hψC]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        have e : a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : A')) * ((1 : A') ⊗ₜ[A] b) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have h0 := RingHom.congr_fun (hφ 0) (LaurentPolynomial.C a)
        have h1 := RingHom.congr_fun (hφ 1) (LaurentPolynomial.C b)
        simp only [RingHom.comp_apply, hLC] at h0 h1
        rw [e, map_mul, map_mul, map_mul]
        change φ (LaurentPolynomial.C (a ⊗ₜ[A] 1)) * φ (LaurentPolynomial.C (1 ⊗ₜ[A] b)) = _
        rw [show (a ⊗ₜ[A] (1 : A')) = inc A A' 0 a from rfl, show ((1 : A') ⊗ₜ[A] b) = inc A A' 1 b from rfl, h0, h1]
        simp [ψ0, g0, g1]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    refine laurent_ext hC ?_
    have h0 := RingHom.congr_fun (hφ 0) (LaurentPolynomial.T 1)
    simp only [RingHom.comp_apply, GmPhiNat.laurentMap_T] at h0
    rw [h0, hψT]

theorem level_one : ∃ e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (A' ⊗[A] A')))) ≅ (cech (fT A A')).obj (op ⦋1⦌),
    e.hom ≫ (cP A A' ≫ cS A A').app (op ⦋1⦌) = yoneda.map (Spec.map (CommRingCat.ofHom (flat (A' ⊗[A] A')))) ≫ e.hom := by
  obtain ⟨e, he⟩ := GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda (LaurentPolynomial A) (LaurentPolynomial A') (LaurentPolynomial (A' ⊗[A] A'))
    (laurentMap (algebraMap A A')) 1 (fun j => laurentMap (inc A A' j))
    (fun j => by rw [← GmPhiNat.laurentMap_comp, ← GmPhiNat.laurentMap_comp, inc_comp]) (laurent_univ A A')
  refine ⟨e, ?_⟩
  have he' : ∀ j : Fin (1 + 1), e.hom ≫ WidePullback.π (fun _ => (Arrow.mk (yoneda.map (fT A A'))).hom) j =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (inc A A' j)))) := he
  have hπ : ∀ j : Fin (1 + 1), (e.hom ≫ (cP A A' ≫ cS A A').app (op ⦋1⦌)) ≫ WidePullback.π _ j =
      (yoneda.map (Spec.map (CommRingCat.ofHom (flat (A' ⊗[A] A')))) ≫ e.hom) ≫ WidePullback.π _ j := by
    intro j
    change (e.hom ≫ (WidePullback.lift _ _ _ ≫ WidePullback.lift _ _ _)) ≫ WidePullback.π _ j = _
    simp only [Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc]
    rw [← Category.assoc e.hom, he' j, he j]
    simp only [constArr, oneArr, Arrow.homMk_left, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact flat_laurentMap (inc A A' j)
  apply WidePullback.hom_ext
  · exact hπ
  · have h0 : ∀ k : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (A' ⊗[A] A')))) ⟶ (cech (fT A A')).obj (op ⦋1⦌),
        k ≫ WidePullback.base (fun _ : Fin (1 + 1) => (Arrow.mk (yoneda.map (fT A A'))).hom) =
          (k ≫ WidePullback.π _ 0) ≫ (Arrow.mk (yoneda.map (fT A A'))).hom := fun k => by
      rw [← WidePullback.π_arrow _ 0]; exact (Category.assoc _ _ _).symm
    erw [h0, h0, hπ 0]
    rfl

theorem cobd_pull {R : Type} [CommRing R] {E E' : Spc} {F : Shv R} {n : ℕ} (φ : E' ⟶ E)
    (σ : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    cobd ((free R).map (φ.app (op ⦋n⦌)) ≫ σ) = (free R).map (φ.app (op ⦋n + 1⦌)) ≫ cobd σ := by
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Category.assoc, ← Functor.map_comp, SimplicialObject.δ_naturality, Functor.map_comp, Category.assoc]

theorem cobd_of_h1_zero {R : Type} [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (hE : Eqv R (cechAug f) F)
    (hX : ∀ x : H R (sch.obj X) F 1, x = 0) (σ : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F) (hσ : cobd σ = 0) :
    ∃ τ, σ = cobd τ := by
  obtain ⟨y, hy⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech f) 1).1 σ hσ
  obtain ⟨x, rfl⟩ := (hE 1).2 y
  rw [hX x, map_zero] at hy
  exact GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ σ hy

theorem cobd_of_retract {R : Type} [CommRing R] {F : Shv R} {E E' : Spc} (P : E' ⟶ E) (S : E ⟶ E')
    (hinv : ∀ σ : (free R).obj (E'.obj (op ⦋1⦌)) ⟶ F, (free R).map ((P ≫ S).app (op ⦋1⦌)) ≫ σ = σ)
    (hE : ∀ σ : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F, cobd σ = 0 → ∃ τ, σ = cobd τ)
    (σ : (free R).obj (E'.obj (op ⦋1⦌)) ⟶ F) (hσ : cobd σ = 0) : ∃ τ, σ = cobd τ := by
  obtain ⟨τ, hτ⟩ := hE ((free R).map (S.app _) ≫ σ) (by rw [cobd_pull, hσ, Limits.comp_zero])
  refine ⟨(free R).map (P.app _) ≫ τ, ?_⟩
  rw [cobd_pull, ← hτ, ← Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app, hinv]

theorem fixed_of_iso {R : Type} [CommRing R] {F : Shv R} {P : PSh} {X : Scheme.{0}} (e : yoneda.obj X ≅ P) (u : P ⟶ P)
    (g : X ⟶ X) (he : e.hom ≫ u = yoneda.map g ≫ e.hom) (hs : ∀ s : Sec F X, Sec.res g s = s)
    (σ : (free R).obj P ⟶ F) : (free R).map u ≫ σ = σ := by
  have key : (free R).map (yoneda.map g) ≫ ((free R).map e.hom ≫ σ) = (free R).map e.hom ≫ σ := by
    apply CupSpec.free_ext
    intro U x
    have h1 : ∀ y : U ⟶ X, freeGen R (yoneda.obj X) U y = Sec.res y (freeGen R (yoneda.obj X) X (𝟙 X)) := by
      intro y
      rw [CupSpec.freeGen_res]
      congr 1
    change Sec.map ((free R).map e.hom ≫ σ) (Sec.map ((free R).map (yoneda.map g)) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    change Sec.map ((free R).map e.hom ≫ σ) (freeGen R _ U (x ≫ g)) = _
    rw [h1, h1 x, ← CupSpec.map_res, ← CupSpec.map_res]
    have h2 : ∀ s : Sec F X, Sec.res (x ≫ g) s = Sec.res x (Sec.res g s) := by
      intro s; simp only [Sec.res, op_comp, Functor.map_comp]; rfl
    rw [h2, hs]
  have : (free R).map e.hom ≫ ((free R).map u ≫ σ) = (free R).map e.hom ≫ σ := by
    rw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc, key]
  exact (cancel_epi _).1 this

theorem tateTwistCohomology_zero_laurent_from_base (q : ℕ) [NeZero q] (T : Type) [CommRing T] (hq : IsUnit (q : T)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial T)) 0 i) :
    ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y :=
  GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective q T hq i y

theorem sec_flat (q : ℕ) [NeZero q] (T : Type) [CommRing T] (hq : IsUnit (q : T)) (i : ℤ)
    (s : Sec (tw q i) (Spec (CommRingCat.of (LaurentPolynomial T)))) :
    Sec.res (Spec.map (CommRingCat.ofHom (flat T))) s = s := by
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  apply (e _).injective
  rw [← he]
  obtain ⟨y, hy⟩ := tateTwistCohomology_zero_laurent_from_base q T hq i (e _ s)
  rw [← hy]
  change pull _ (spMap (flat T)) _ 0 (pull _ (spMap LaurentPolynomial.C) _ 0 y) = _
  rw [← GmPhiNat.pull_spMap_comp, flat_comp_C]

end GlobalTheory.EtC.KerLaurent

namespace GlobalTheory.EtC.KerLaurent
variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

theorem cobd_laurent (q : ℕ) [NeZero q] (hint : Algebra.IsIntegral A A')
    (hker : RingHom.ker (algebraMap A A') ≤ nilradical A) (hq : IsUnit (q : A))
    (hA : ∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) (i : ℤ)
    (σ : (free (ZMod q)).obj ((cech (fT A A')).obj (op ⦋1⦌)) ⟶ tw q i) (hσ : cobd σ = 0) : ∃ τ, σ = cobd τ := by
  have hi : (algebraMap A A').IsIntegral := fun a => hint.isIntegral a
  obtain ⟨hf1, hf2⟩ := GmStep.spec_integral_surj (algebraMap A A') hi hker
  have hqA : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    simpa using this
  have hE := GlobalTheory.EtC.b4 q (fB A A') hqA i
  haveI := hA i
  have hqT : IsUnit (q : A' ⊗[A] A') := by simpa using hq.map (algebraMap A (A' ⊗[A] A'))
  refine cobd_of_retract (cP A A') (cS A A') (fun σ' => ?_)
    (cobd_of_h1_zero _ (fB A A') hE (fun x => Subsingleton.elim _ _)) σ hσ
  obtain ⟨e, he⟩ := level_one A A'
  exact fixed_of_iso e _ _ he (sec_flat q _ hqT i) σ'

end GlobalTheory.EtC.KerLaurent

open GlobalTheory.EtC.KerLaurent in

theorem GlobalTheory.EtC.kerLaurent : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'],
    Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) →
    (∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i),
    pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = 0 → x = 0 := by
  intro q _ A A' _ _ _ hint hker hq hA i x hx
  have hi : (algebraMap A A').IsIntegral := fun a => hint.isIntegral a
  have hlm : GmStep.laurentMap (algebraMap A A') = laurentMap (algebraMap A A') :=
    laurent_ext (fun a => by
      rw [GmStep.laurentMap_C]
      exact (RingHom.congr_fun (GmPhiNat.laurentMap_C _) a).symm)
      (by rw [GmStep.laurentMap_T, GmPhiNat.laurentMap_T])
  obtain ⟨hf1, hf2⟩ := GmStep.spec_integral_surj (laurentMap (algebraMap A A'))
    (hlm ▸ GmStep.laurentMap_isIntegral _ hi) (hlm ▸ GmStep.laurentMap_ker _ hker)
  have hE := GlobalTheory.EtC.b4 q (fT A A') (GmPhiNat.isUnit_gamma q A hq) i
  obtain ⟨σ, hσ, hcls⟩ := GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero (ZMod q) (tw q i) _ _ (fT A A') x hx
  obtain ⟨τ, rfl⟩ := cobd_laurent A A' q hint hker hq hA i σ hσ
  have h0 := (GlobalTheory.T.simplicialCochain_classes_basic_properties (ZMod q) (tw q i) (cech (fT A A')) 0).2.2.2.1 τ _ hcls
  exact (hE 1).1 (by rw [map_zero]; exact h0)
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_cohomology_injective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → (∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = 0 → x = 0 := by
  first | (exact @GlobalTheory.EtC.kerLaurent) | (exact GlobalTheory.EtC.kerLaurent) | (intros; apply GlobalTheory.EtC.kerLaurent  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Simplicial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.DescZero

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

theorem spec_integral_surj (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral)
    (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩
  exact this

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

def cπ {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (k : Fin (n + 1)) : (cech f).obj (op ⦋n⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) :=
  WidePullback.π (fun _ : Fin (n + 1) => yoneda.map f) k

theorem cech_δ0_π {Y X : Scheme.{0}} (f : Y ⟶ X) :
    SimplicialObject.δ (cech f) (0 : Fin 2) ≫ cπ f 0 0 = cπ f (0 + 1) 1 :=
  WidePullback.lift_π _ _ _ _ 0

theorem cech_δ1_π {Y X : Scheme.{0}} (f : Y ⟶ X) :
    SimplicialObject.δ (cech f) (1 : Fin 2) ≫ cπ f 0 0 = cπ f (0 + 1) 0 :=
  WidePullback.lift_π _ _ _ _ 0

theorem cechDiag_π {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌) ≫ cπ f 0 0 = 𝟙 _ :=
  WidePullback.lift_π _ _ _ _ 0

end GlobalTheory.EtC.DescZero

namespace GlobalTheory.EtC.DescZero

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma spec_map_surjective_of_integral_ker_le_nilradical (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.IsIntegral A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  constructor
  intro x
  let p : PrimeSpectrum A := x
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal A')
    (by rw [← RingHom.ker_eq_comap_bot]; exact hker.trans (nilradical_le_prime _))
  exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum A'), PrimeSpectrum.ext hQx⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma sec_res_comp_divisor {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme}
    (h : W ⟶ V) (g : V ⟶ U) (s : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (h ≫ g) s =
      _root_.GlobalTheory.EtC.Sec.res h (_root_.GlobalTheory.EtC.Sec.res g s) := by
  simp [_root_.GlobalTheory.EtC.Sec.res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma disc_face_eq_id (P : _root_.GlobalTheory.EtC.PSh) (n : ℕ) (i : Fin (n + 2)) :
    SimplicialObject.δ (_root_.GlobalTheory.EtC.disc.obj P) i = 𝟙 _ := by
  first | rfl | simp [SimplicialObject.δ, _root_.GlobalTheory.EtC.disc]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cobd_eq_zero_of_scheme {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R} (X : Scheme)
    (t : (_root_.GlobalTheory.EtC.free R).obj ((_root_.GlobalTheory.EtC.sch.obj X) _⦋0⦌) ⟶ F) :
    _root_.GlobalTheory.EtC.cobd t = 0 := by
  have h : ∀ i : Fin 2, SimplicialObject.δ (_root_.GlobalTheory.EtC.sch.obj X) i = 𝟙 _ :=
    fun i => disc_face_eq_id (yoneda.obj X) 0 i
  unfold _root_.GlobalTheory.EtC.cobd
  simp [Fin.sum_univ_two, h]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma isCls_secClass_of_val_eq_res {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R)
    (X : Scheme) (s : _root_.GlobalTheory.EtC.Sec F X)
    (t : (_root_.GlobalTheory.EtC.free R).obj ((_root_.GlobalTheory.EtC.sch.obj X) _⦋0⦌) ⟶ F)
    (ht : ∀ (U : Scheme) (x : U ⟶ X), _root_.GlobalTheory.EtC.val t U x = _root_.GlobalTheory.EtC.Sec.res x s) :
    _root_.GlobalTheory.EtC.IsCls t (_root_.GlobalTheory.EtC.secClass F s) := by
  obtain ⟨hex, -, -, -, -⟩ :=
    _root_.GlobalTheory.EtC.isCls_basic R F (_root_.GlobalTheory.EtC.sch.obj X) 0
  obtain ⟨x, hx⟩ := hex t (cobd_eq_zero_of_scheme X t)
  suffices hxs : x = _root_.GlobalTheory.EtC.secClass F s by rw [← hxs]; exact hx
  obtain ⟨z, hz, hzv⟩ := hx
  rw [← hz]
  refine ((_root_.GlobalTheory.EtC.secClass_props R F X).1 s z).1 ?_
  have key : ∀ h, (z : Cochain _ _ ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 h =
      (_root_.GlobalTheory.EtC.chainsXIso R (_root_.GlobalTheory.EtC.sch.obj X) 0).hom ≫ t ≫
        _root_.GlobalTheory.EtC.resι R F := by
    intro h
    rw [hzv]
    exact Cochain.single_v _ _ _
  erw [_root_.GlobalTheory.EtC.CupSpec.ev_def, key, Iso.inv_hom_id_assoc]
  have hval := ht X (𝟙 X)
  calc _ = _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R F)
        (_root_.GlobalTheory.EtC.val t X (𝟙 X)) := rfl
    _ = _ := by rw [hval]; simp [_root_.GlobalTheory.EtC.Sec.res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cobd_eq_zero_of_face_comp_eq {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R}
    {E : _root_.GlobalTheory.EtC.Spc} (T : (_root_.GlobalTheory.EtC.free R).obj (E _⦋0⦌) ⟶ F)
    (h : (_root_.GlobalTheory.EtC.free R).map (SimplicialObject.δ E 0) ≫ T =
      (_root_.GlobalTheory.EtC.free R).map (SimplicialObject.δ E 1) ≫ T) :
    _root_.GlobalTheory.EtC.cobd T = 0 := by
  unfold _root_.GlobalTheory.EtC.cobd
  simp [Fin.sum_univ_two, h]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cech_face_comp_cπ_eq_cπ_rev {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 2) :
    SimplicialObject.δ (_root_.GlobalTheory.EtC.cech f) i ≫ _root_.GlobalTheory.EtC.DescZero.cπ f 0 0 =
      _root_.GlobalTheory.EtC.DescZero.cπ f 1 i.rev := by
  fin_cases i <;>
  · simp only [_root_.GlobalTheory.EtC.DescZero.cπ, _root_.GlobalTheory.EtC.cech, SimplicialObject.δ, Arrow.cechNerve]
    erw [WidePullback.lift_π]
    rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma res_eq_of_tensorSquare_res_eq_lemma_6 {R : Type} [CommRing R] {F : _root_.GlobalTheory.EtC.Shv R}
    (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    (s : _root_.GlobalTheory.EtC.Sec F (Spec (CommRingCat.of A')))
    (hs : _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s =
      _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s)
    {U : Scheme} (y₀ y₁ : U ⟶ Spec (CommRingCat.of A'))
    (hy : y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) =
      y₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    _root_.GlobalTheory.EtC.Sec.res y₀ s = _root_.GlobalTheory.EtC.Sec.res y₁ s := by
  let u := pullback.lift y₀ y₁ hy ≫ (pullbackSpecIso A A' A').hom
  have hu₀ : u ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) = y₀ := by
    simp only [u, Category.assoc]
    erw [pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  have hu₁ : u ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) = y₁ := by
    simp only [u, Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    exact pullback.lift_snd _ _ _
  clear_value u
  rw [← hu₀, ← hu₁, sec_res_comp_divisor, sec_res_comp_divisor, hs]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cπ_comp_eq_cπ_comp {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (k l : Fin (n + 1))
    (U : Scheme.{0}) (e : ((_root_.GlobalTheory.EtC.cech f).obj (op ⦋n⦌)).obj (op U)) :
    (show U ⟶ Y from (_root_.GlobalTheory.EtC.DescZero.cπ f n k).app (op U) e) ≫ f =
      (show U ⟶ Y from (_root_.GlobalTheory.EtC.DescZero.cπ f n l).app (op U) e) ≫ f := by
  have h := (WidePullback.π_arrow (fun _ : Fin (n + 1) => yoneda.map f) k).trans
    (WidePullback.π_arrow (fun _ : Fin (n + 1) => yoneda.map f) l).symm
  exact congr_arg (fun φ => φ.app (op U) e) h

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in
private lemma cechDiag_comp_cπ_eq_id {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (_root_.GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌) ≫ _root_.GlobalTheory.EtC.DescZero.cπ f 0 0 = 𝟙 _ := by
  simp only [_root_.GlobalTheory.CechOne.cechDiag, _root_.GlobalTheory.EtC.DescZero.cπ]
  erw [WidePullback.lift_π]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.EtC.DescZero.desc_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'],
    Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) →
    ∀ (j : ℤ) (b : _root_.GlobalTheory.EtC.Ht q (_root_.GlobalTheory.EtC.sp A') 0 j),
      _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b =
        _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b →
      ∃ a : _root_.GlobalTheory.EtC.Ht q (_root_.GlobalTheory.EtC.sp A) 0 j, _root_.GlobalTheory.EtC.pull _ (_root_.GlobalTheory.EtC.spMap (algebraMap A A')) _ 0 a = b := by
  intro q _ A A' _ _ _ hint hker hq j b hb
  let f : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A A'))
  haveI : IsIntegralHom f := by rw [IsIntegralHom.SpecMap_iff]; exact hint.isIntegral
  haveI : Surjective f := spec_map_surjective_of_integral_ker_le_nilradical A A' hker
  have hbij : Function.Bijective
      (_root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.cechAug f) (_root_.GlobalTheory.EtC.tw q j) 0) :=
    _root_.GlobalTheory.EtC.b4 q f
      (by simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) j 0
  set F := _root_.GlobalTheory.EtC.tw q j with hF
  obtain ⟨-, hbijc, -, hres, -⟩ := _root_.GlobalTheory.EtC.secClass_props (ZMod q) F (Spec (CommRingCat.of A'))
  obtain ⟨s, rfl⟩ := hbijc.2 b
  have hs : _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s =
      _root_.GlobalTheory.EtC.Sec.res
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom)) s := by
    apply (_root_.GlobalTheory.EtC.secClass_props (ZMod q) F _).2.1.1
    rw [← hres, ← hres]
    exact hb
  have hfreeY := _root_.GlobalTheory.EtC.FreeHom.main (ZMod q)
    ((_root_.GlobalTheory.EtC.sch.obj (Spec (CommRingCat.of A'))) _⦋0⦌) F
  obtain ⟨t, ht⟩ := hfreeY.2.1
    (fun U x => _root_.GlobalTheory.EtC.Sec.res (show U ⟶ Spec (CommRingCat.of A') from x) s)
    (fun V U g x => sec_res_comp_divisor g (show U ⟶ Spec (CommRingCat.of A') from x) s)
  have hrep := isCls_secClass_of_val_eq_res F _ s t ht
  obtain ⟨hex, -, -, -, hpull⟩ :=
    _root_.GlobalTheory.EtC.isCls_basic (ZMod q) F (_root_.GlobalTheory.EtC.cech f) 0
  obtain ⟨T, hTdef⟩ : ∃ T, T =
      (_root_.GlobalTheory.EtC.free (ZMod q)).map (_root_.GlobalTheory.EtC.DescZero.cπ f 0 0) ≫ t :=
    ⟨_, rfl⟩
  have hT : _root_.GlobalTheory.EtC.cobd T = 0 := by
    refine cobd_eq_zero_of_face_comp_eq T ?_
    have hfree := _root_.GlobalTheory.EtC.FreeHom.main (ZMod q)
      ((_root_.GlobalTheory.EtC.cech f) _⦋1⦌) F
    apply hfree.1
    intro U e
    simp only [hTdef, ← Functor.map_comp_assoc, cech_face_comp_cπ_eq_cπ_rev]
    rw [hfreeY.2.2.2.1, hfreeY.2.2.2.1, ht, ht]
    exact res_eq_of_tensorSquare_res_eq_lemma_6 A A' s hs _ _
      (cπ_comp_eq_cπ_comp f 1 (Fin.rev 0) (Fin.rev 1) U e)
  obtain ⟨x, hx⟩ := hex T hT
  have hcx : _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.CechOne.cechDiag f) F 0 x =
      _root_.GlobalTheory.EtC.secClass F s := by
    refine (_root_.GlobalTheory.EtC.isCls_basic (ZMod q) F
      (_root_.GlobalTheory.EtC.sch.obj (Spec (CommRingCat.of A'))) 0).2.2.1 t _ _ ?_ hrep
    have h := hpull _ (_root_.GlobalTheory.CechOne.cechDiag f) T x hx
    have hcomp : (_root_.GlobalTheory.EtC.free (ZMod q)).map
        ((_root_.GlobalTheory.CechOne.cechDiag f).app (op ⦋0⦌)) ≫ T = t := by
      rw [hTdef, ← Functor.map_comp_assoc]
      erw [cechDiag_comp_cπ_eq_id]
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [hcomp] at h
    exact h
  obtain ⟨a, ha⟩ := hbij.2 x
  refine ⟨a, ?_⟩
  change _root_.GlobalTheory.EtC.pull (ZMod q) (_root_.GlobalTheory.EtC.sch.map f) F 0 a = _
  rw [← _root_.GlobalTheory.CechOne.cechDiag_aug, _root_.GlobalTheory.EtC.pull_comp, ha, hcx]

end GlobalTheory.EtC.DescZero

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_equalizer_degree_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → ∀ (j : ℤ) (b : Ht q (sp A') 0 j), pull _ (spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b = pull _ (spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b → ∃ a : Ht q (sp A) 0 j, pull _ (spMap (algebraMap A A')) _ 0 a = b := by
  first | (exact @GlobalTheory.EtC.DescZero.desc_zero) | (exact GlobalTheory.EtC.DescZero.desc_zero) | (intros; apply GlobalTheory.EtC.DescZero.desc_zero  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.LiftWitness

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem spMap_id (L : Type) [CommRing L] : spMap (RingHom.id L) = 𝟙 _ := by
  simp [spMap]

theorem laurentProd_bijective (B C : Type) [CommRing B] [CommRing C] : Function.Bijective
    ((laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.coeff_injective
    ext n
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h1
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h2
  · rintro ⟨f, g⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk rfl f.coeff g.coeff), ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor <;> (apply AddMonoidAlgebra.coeff_injective; ext n; simp [laurentMap_coeff])

open GlobalTheory.EtC.GmPhiNat in

theorem eq_zero_of_pull_laurent_fst_snd (q : ℕ) (B C : Type) [CommRing B] [CommRing C] (n i : ℤ)
    (z : Ht q (sp (LaurentPolynomial (B × C))) n i)
    (h1 : pull _ (spMap (laurentMap (RingHom.fst B C))) _ n z = 0)
    (h2 : pull _ (spMap (laurentMap (RingHom.snd B C))) _ n z = 0) : z = 0 := by
  let e := (laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))
  let E := RingEquiv.ofBijective e (laurentProd_bijective B C)
  have hinv : E.symm.toRingHom.comp e = RingHom.id _ :=
    RingHom.ext fun x => E.symm_apply_apply x
  have hw : pull _ (spMap e) _ n z = 0 := by
    apply (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q (LaurentPolynomial B) (LaurentPolynomial C) n i).1
    simp only [← pull_spMap_comp, map_zero, e, RingHom.fst_comp_prod, RingHom.snd_comp_prod]
    exact Prod.ext h1 h2
  have := pull_spMap_comp q e E.symm.toRingHom n i z
  rw [hinv, spMap_id, pull_id, hw, map_zero] at this
  exact this

theorem surj_prod (q : ℕ) [NeZero q] (B C : Type) [CommRing B] [CommRing C] (hq : IsUnit (q : B × C)) (i : ℤ)
    (hB : Function.Surjective (gmPhi q B i)) (hC : Function.Surjective (gmPhi q C i)) :
    Function.Surjective (gmPhi q (B × C) i) := by
  intro y
  obtain ⟨b, hb⟩ := hB (pull _ (spMap (laurentMap (RingHom.fst B C))) _ 1 y)
  obtain ⟨c, hc⟩ := hC (pull _ (spMap (laurentMap (RingHom.snd B C))) _ 1 y)
  obtain ⟨a, ha⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q B C 0 (i - 1)).2 (b, c)
  simp only [Prod.mk.injEq] at ha
  refine ⟨a, (sub_eq_zero.mp ?_).symm⟩
  apply eq_zero_of_pull_laurent_fst_snd q B C 1 i
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.1, hb, sub_self]
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.2, hc, sub_self]

theorem exists_factor (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (p : Ideal A) [p.IsPrime] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  let D := A ⧸ p
  let Ω := AlgebraicClosure (FractionRing D)
  let T := integralClosure D Ω
  letI : Algebra A T := ((algebraMap D T).comp (Ideal.Quotient.mk p)).toAlgebra
  have hint : Algebra.IsIntegral A T := by
    have h1 : (Ideal.Quotient.mk p).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : (algebraMap D T).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := D) x
    exact ⟨fun x => RingHom.IsIntegral.trans _ _ h1 h2 x⟩
  have hloc : IsLocalRing T := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A T
  have hqT : IsUnit (q : T) := by simpa using hq.map (algebraMap A T)
  refine ⟨T, inferInstance, inferInstance, hint, fun a ha => ?_,
    (GlobalTheory.T.units_cohomology_bijective q T (GlobalTheory.aic_integralClosure_algebraicClosure D) hqT i).2⟩
  have hinjΩ : Function.Injective (algebraMap D Ω) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) Ω]
    exact (algebraMap (FractionRing D) Ω).injective.comp (IsFractionRing.injective D (FractionRing D))
  have hinj : Function.Injective (algebraMap D T) := by
    intro x y h
    exact hinjΩ (congrArg Subtype.val h)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact ha

theorem exists_witness (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (S : Finset (Ideal A)) (hS : ∀ p ∈ S, p.IsPrime) (hne : S.Nonempty) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → ∀ p ∈ S, a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton p =>
    have := hS p (Finset.mem_singleton_self p)
    obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_factor q A hq i p
    exact ⟨B, inferInstance, inferInstance, hint, fun a ha r hr => by
      rw [Finset.mem_singleton] at hr; subst hr; exact hker a ha, hsurj⟩
  | cons p S hp hSne ih =>
    have := hS p (Finset.mem_cons_self p S)
    obtain ⟨B, _, _, hintB, hkerB, hsurjB⟩ := ih fun r hr => hS r (Finset.mem_cons_of_mem hr)
    obtain ⟨C, _, _, hintC, hkerC, hsurjC⟩ := exists_factor q A hq i p
    have hqBC : IsUnit (q : B × C) := by simpa using hq.map (algebraMap A (B × C))
    refine ⟨B × C, inferInstance, inferInstance, inferInstance, fun a ha r hr => ?_,
      surj_prod q B C hqBC i hsurjB hsurjC⟩
    rw [Prod.algebraMap_apply, Prod.mk_eq_zero] at ha
    rcases Finset.mem_cons.1 hr with rfl | hr
    · exact hkerC a ha.2
    · exact hkerB a ha.1 r hr

theorem lift_witness : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
      ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  intro q _ A _ _ hSH hq i x
  obtain ⟨hH, -⟩ := hSH
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
    exact ⟨p, hfin.mem_toFinset.2 hp⟩
  obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_witness q A hq i hfin.toFinset
    (fun p hp => (hfin.mem_toFinset.1 hp).1.1) hne
  obtain ⟨a', ha'⟩ := hsurj (pull _ (spMap (laurentMap (algebraMap A B))) _ 1 x)
  refine ⟨B, inferInstance, inferInstance, hint, fun a ha => ?_, a', ha'.symm⟩
  rw [RingHom.mem_ker] at ha
  have : a ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 fun p hp => hker a ha p (hfin.mem_toFinset.2 hp)
  exact this
end GlobalTheory.EtC.LiftWitness
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_from_integral : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧ ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  first | (exact @GlobalTheory.EtC.LiftWitness.lift_witness) | (exact GlobalTheory.EtC.LiftWitness.lift_witness) | (intros; apply GlobalTheory.EtC.LiftWitness.lift_witness  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.GmPhiNoeth

theorem coeff_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem laurentMap_id (R : Type) [CommRing R] : laurentMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun p => AddMonoidAlgebra.ext (Finsupp.ext fun n => by rw [coeff_laurentMap]; rfl)

def laurentFunctor : CommRingCat.{0} ⥤ CommRingCat.{0} where
  obj R := CommRingCat.of (LaurentPolynomial R)
  map f := CommRingCat.ofHom (laurentMap f.hom)
  map_id R := by
    change CommRingCat.ofHom (laurentMap (RingHom.id R)) = _
    rw [laurentMap_id]; rfl
  map_comp f g := by
    change CommRingCat.ofHom (laurentMap (g.hom.comp f.hom)) = _
    rw [GmPhiNat.laurentMap_comp]; rfl

def isColimit_laurent {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) : IsColimit (laurentFunctor.mapCocone c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc' : IsColimit ((forget CommRingCat.{0}).mapCocone c) := isColimitOfPreserves _ hc

  have hsurj : ∀ a : c.pt, ∃ j, ∃ b : D.obj j, (c.ι.app j).hom b = a := fun a =>
    Types.jointly_surjective_of_isColimit hc' a

  have hker : ∀ j (b : D.obj j), (c.ι.app j).hom b = 0 → ∃ k, ∃ f : j ⟶ k, (D.map f).hom b = 0 := by
    intro j b hb
    have h := (Types.FilteredColimit.isColimit_eq_iff' hc' b 0).1 (by
      change (c.ι.app j).hom b = (c.ι.app j).hom 0
      rw [hb, map_zero])
    obtain ⟨k, f, hf⟩ := h
    refine ⟨k, f, ?_⟩
    change (D.map f).hom b = (D.map f).hom 0 at hf
    rw [hf, map_zero]
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : LaurentPolynomial (D.obj j)),
      laurentMap (c.ι.app k).hom (laurentMap (D.map f).hom y) = laurentMap (c.ι.app j).hom y := by
    intro j k f y
    rw [← RingHom.comp_apply, ← GmPhiNat.laurentMap_comp, ← CommRingCat.hom_comp, c.w f]
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (laurentFunctor.mapCocone c)) ?_ ?_)
  · intro (x : LaurentPolynomial c.pt)
    suffices h : ∃ j, ∃ y : LaurentPolynomial (D.obj j), laurentMap (c.ι.app j).hom y = x by
      obtain ⟨j, y, hy⟩ := h
      exact ⟨j, y, hy.symm⟩
    induction x using LaurentPolynomial.induction_on' with
    | add p p' hp hp' =>
      obtain ⟨j, y, rfl⟩ := hp
      obtain ⟨j', y', rfl⟩ := hp'
      refine ⟨IsFiltered.max j j', laurentMap (D.map (IsFiltered.leftToMax j j')).hom y +
        laurentMap (D.map (IsFiltered.rightToMax j j')).hom y', ?_⟩
      rw [map_add, hw, hw]
    | C_mul_T n a =>
      obtain ⟨j, b, rfl⟩ := hsurj a
      refine ⟨j, LaurentPolynomial.C b * LaurentPolynomial.T n, ?_⟩
      rw [map_mul, GmPhiNat.laurentMap_T, ← RingHom.comp_apply, GmPhiNat.laurentMap_C, RingHom.comp_apply]
  · intro i j (xi : LaurentPolynomial (D.obj i)) (xj : LaurentPolynomial (D.obj j)) h
    change laurentMap (c.ι.app i).hom xi = laurentMap (c.ι.app j).hom xj at h
    let m := IsFiltered.max i j
    let fi := IsFiltered.leftToMax i j
    let fj := IsFiltered.rightToMax i j
    let z : LaurentPolynomial (D.obj m) := laurentMap (D.map fi).hom xi - laurentMap (D.map fj).hom xj
    have hz : laurentMap (c.ι.app m).hom z = 0 := by
      simp only [z, map_sub, hw, h, sub_self]

    have hfin : ∀ s : Finset ℤ, ∃ k, ∃ h : m ⟶ k, ∀ n ∈ s, (D.map h).hom (z.coeff n) = 0 := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => exact ⟨m, 𝟙 m, fun n hn => absurd hn (Finset.notMem_empty n)⟩
      | insert n s _ ih =>
        obtain ⟨k₁, h₁, hk₁⟩ := ih
        have hn : (c.ι.app m).hom (z.coeff n) = 0 := by
          rw [← coeff_laurentMap, hz]; rfl
        obtain ⟨k₂, h₂, hk₂⟩ := hker m _ hn
        obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span h₁ h₂
        refine ⟨k, h₁ ≫ g₁, fun n' hn' => ?_⟩
        rcases Finset.mem_insert.1 hn' with rfl | hn'
        · rw [hg, D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₂, map_zero]
        · rw [D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₁ n' hn', map_zero]
    obtain ⟨k, hmk, hk⟩ := hfin z.coeff.support
    have hz0 : laurentMap (D.map hmk).hom z = 0 := by
      refine AddMonoidAlgebra.ext (Finsupp.ext fun n => ?_)
      rw [coeff_laurentMap]
      by_cases hn : n ∈ z.coeff.support
      · exact hk n hn
      · rw [Finsupp.notMem_support_iff.1 hn, map_zero]; rfl
    refine ⟨k, fi ≫ hmk, fj ≫ hmk, ?_⟩
    change laurentMap (D.map (fi ≫ hmk)).hom xi = laurentMap (D.map (fj ≫ hmk)).hom xj
    rw [D.map_comp, D.map_comp, CommRingCat.hom_comp, CommRingCat.hom_comp, GmPhiNat.laurentMap_comp,
      GmPhiNat.laurentMap_comp, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub]
    exact hz0

end GlobalTheory.EtC.GmPhiNoeth

open GlobalTheory.EtC.GmPhiNoeth in

theorem GlobalTheory.EtC.gmPhi_surjective_of_noetherian : ∀ (q : ℕ) [NeZero q],
    (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
      Function.Surjective (gmPhi q A i)) →
    ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  intro q _ hN A _ hSH hq i x
  obtain ⟨hH, hsep⟩ := hSH
  obtain ⟨J, _, _, D, ι, hc, hl, hst, hqj, -, -⟩ :=
    GlobalTheory.SHColim.strictlyHenselian_isColimit q A ⟨hH, hsep⟩ hq
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ laurentFunctor) _ (isColimit_laurent hc) 1 i).1 x hqL
  obtain ⟨B, _, _, s, hs⟩ := hst j
  haveI := hl j
  haveI : IsNoetherianRing (D.obj j) := GlobalTheory.StalkNoeth.isNoetherianRing_of_isStalk B (D.obj j) s hs
  obtain ⟨b, hb⟩ := hN (D.obj j) hs.1 (hqj j) i y
  have hn := gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (A := D.obj j) (B := A) (ι.app j).hom (hqj j) i b
  rw [hb] at hn
  exact ⟨_, hn.symm.trans hy⟩
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_noetherian_case : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (exact GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (intros; apply GlobalTheory.EtC.gmPhi_surjective_of_noetherian  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmPhiBij

theorem inj (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ) : Function.Injective (gmPhi q R i) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine GlobalTheory.T.class_zero_of_geometric_points q R hq (i - 1) a fun K _ _ f => ?_
  have hqK : IsUnit (q : K) := by simpa using hq.map f
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (Polynomial.natDegree_pos_iff_degree_pos.mp hd).ne'
  apply (GlobalTheory.T.units_cohomology_bijective q K hK hqK i).1
  rw [map_zero, ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q f hq, ha, map_zero]

theorem surj_noeth (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A] (hA : SH A) (hq : IsUnit (q : A)) (i : ℤ) :
    Function.Surjective (gmPhi q A i) := by
  intro x
  obtain ⟨A', _, _, hint, hker, a', ha'⟩ := GlobalTheory.T.laurent_class_from_integral q A hA hq i x
  have hq' : IsUnit (q : A') := by simpa using hq.map (algebraMap A A')
  set L := (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom with hLdef
  set R := (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom with hRdef
  have hLR : L.comp (algebraMap A A') = R.comp (algebraMap A A') := by
    refine RingHom.ext fun a => ?_
    change (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a) =
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a)
    rw [AlgHom.commutes, AlgHom.commutes]
  have hq2 : IsUnit (q : A' ⊗[A] A') := by simpa using hq'.map L
  have heq : pull _ (spMap L) _ 0 a' = pull _ (spMap R) _ 0 a' := by
    apply inj q _ hq2 i
    rw [← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q L hq', ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q R hq', ← ha', ← GmPhiNat.pull_spMap_comp,
      ← GmPhiNat.pull_spMap_comp, ← GmPhiNat.laurentMap_comp, ← GmPhiNat.laurentMap_comp, hLR]
  obtain ⟨a, ha⟩ := GlobalTheory.T.descent_equalizer_degree_zero q A A' hint hker hq (i - 1) a' heq
  refine ⟨a, ?_⟩
  have hsub : gmPhi q A i a - x = 0 := by
    apply GlobalTheory.T.laurent_cohomology_injective q A A' hint hker hq (fun j => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) 1 one_pos) i
    rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (algebraMap A A') hq, ha, ha', sub_self]
  exact sub_eq_zero.mp hsub

end GmPhiBij

theorem gmPhi_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Function.Bijective (gmPhi q A i) := by
  intro q _ A _ hA hq i
  exact ⟨GmPhiBij.inj q A hq i, GlobalTheory.T.surjective_of_noetherian_case q (fun B _ _ hB hqB j => GmPhiBij.surj_noeth q B hB hqB j) A hA hq i⟩

end GlobalTheory.EtC

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Bijective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective) | (exact GlobalTheory.EtC.gmPhi_bijective) | (intros; apply GlobalTheory.EtC.gmPhi_bijective  <;> assumption)
end
