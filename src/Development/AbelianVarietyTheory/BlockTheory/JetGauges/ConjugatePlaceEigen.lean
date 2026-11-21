import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.DualLattices.CotangentSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out

structure HidaSetting (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] : Prop where
  prime : p.Prime
  algClosed : IsAlgClosed C
  charZero : CharZero C
  integers : v.Integers O
  p_lt : v (p : C) < 1
  complete : IsAdicComplete (Ideal.span {(p : O)}) O

section Inhabitant

open Ideal

variable (p : ℕ) [hp : Fact p.Prime]

theorem valuation_coe_eq_norm (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

theorem norm_p : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← valuation_coe_eq_norm, PadicComplex.valuation_p]; simp

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem mem_iff_norm (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [← valuation_coe_eq_norm]
  change Valued.v x ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

theorem smodEq_iff (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton, (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    ← norm_p, ← norm_pow, ← valuation_coe_eq_norm, ← valuation_coe_eq_norm, NNReal.coe_le_coe]
  rfl

theorem tendsto_inv_p_pow :
    Filter.Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_p_lt_one p)

theorem isHausdorff : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun x hx => ?_⟩
  have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := fun n => by
    simpa using (smodEq_iff p n x 0).1 (hx n)
  have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_p_pow p) (Filter.Eventually.of_forall h)
  exact Subtype.ext (norm_le_zero_iff.1 h0)

theorem isPrecomplete : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ {m n : ℕ}, m ≤ n → ‖(f m : ℂ_[p]) - (f n : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m :=
    fun hmn => (smodEq_iff p _ _ _).1 (hf hmn)
  have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
    refine cauchySeq_of_le_geometric (p : ℝ)⁻¹ 1 (inv_p_lt_one p) fun n => ?_
    rw [dist_eq_norm, _root_.one_mul]
    exact h (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hm : ∀ m : ℕ, ‖(f m : ℂ_[p]) - L‖ ≤ (p : ℝ)⁻¹ ^ m := fun m =>
    le_of_tendsto ((tendsto_const_nhds.sub hL).norm)
      ((Filter.eventually_ge_atTop m).mono fun n hn => h hn)
  have hLO : L ∈ 𝓞_ℂ_[p] := by
    rw [mem_iff_norm]
    exact le_of_tendsto hL.norm
      (Filter.Eventually.of_forall fun n => (mem_iff_norm p _).1 (f n).2)
  exact ⟨⟨L, hLO⟩, fun n => (smodEq_iff p n _ _).2 (hm n)⟩

theorem isAdicComplete : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  { isHausdorff p, isPrecomplete p with }


end Inhabitant

section Places

variable {E : Type} [Field E] [NumberField E]

def IsOver (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Prop := (p : 𝓞 E) ∈ w.asIdeal

abbrev Ow (w : HeightOneSpectrum (𝓞 E)) : Type := w.adicCompletionIntegers E

abbrev PadicOrder (p : ℕ) [Fact p.Prime] (E : Type) [Field E] : Type := ℤ_[p] ⊗[ℤ] 𝓞 E

def toPadic (p : ℕ) [Fact p.Prime] (E : Type) [Field E] : 𝓞 E →+* PadicOrder p E :=
  (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] PadicOrder p E).toRingHom

def IsPlaceIdem (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) (e : PadicOrder p E) : Prop :=
  IsIdempotentElem e ∧ e - 1 ∈ w.asIdeal.map (toPadic p E) ∧
    ∀ w' : HeightOneSpectrum (𝓞 E), IsOver p w' → w' ≠ w → e ∈ w'.asIdeal.map (toPadic p E)

variable [IsCMField E]

def conjInt (E : Type) [Field E] [NumberField E] [IsCMField E] : 𝓞 E ≃+* 𝓞 E :=
  (IsCMField.ringOfIntegersComplexConj E).toRingEquiv

def conjEmb {O : Type} [CommRing O] (τ : 𝓞 E →+* O) : 𝓞 E →+* O :=
  τ.comp (conjInt E).toRingHom

def conjPlace (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := w.asIdeal.comap (conjInt E).toRingHom
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := fun h => w.ne_bot (by
    rw [eq_bot_iff] at h ⊢
    intro a ha
    have : (conjInt E).symm a ∈ w.asIdeal.comap (conjInt E).toRingHom := by
      rw [Ideal.mem_comap]
      show conjInt E ((conjInt E).symm a) ∈ w.asIdeal
      rwa [RingEquiv.apply_symm_apply]
    simpa using h this)

end Places

section Eigen

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {R : Type} [CommRing R] (α : RingAct G R)

def dAct (a : R) (x : LieG G) : LieG G :=
  ⟨x.1 ≫ α.act a, by
    haveI := α.hom a
    rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

def LieEig (τ : R →+* O) : Type :=
  {x : LieG G // ∀ a : R, x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1}

def omegaEig (τ : R →+* O) : Submodule O (LieEig α τ → O) where
  carrier := {f | (∀ x y z : LieEig α τ, z.1.1 = x.1.1 * y.1.1 → f z = f x + f y) ∧
    ∀ (c : O) (x z : LieEig α τ), z.1.1 = ptMap (dualScale c) ≫ x.1.1 → f z = c * f x}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun x y z h => by
        simp only [Pi.add_apply]; rw [hf1 x y z h, hg1 x y z h]; ring,
      fun c x z h => by
        simp only [Pi.add_apply]; rw [hf2 c x z h, hg2 c x z h]; ring⟩
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨fun x y z h => by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [hf1 x y z h]; ring,
      fun a x z h => by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [hf2 a x z h]; ring⟩

def restrictEig (τ : R →+* O) : (LieG G → O) →ₗ[O] (LieEig α τ → O) :=
  LinearMap.funLeft O O Subtype.val

def HasEigRank (τ : R →+* O) (r : ℕ) : Prop :=
  ∃ b : (Fin r → O) ≃ LieEig α τ,
    (∀ s t, (b (s + t)).1.1 = (b s).1.1 * (b t).1.1) ∧
    ∀ (c : O) s, (b (c • s)).1.1 = ptMap (dualScale c) ≫ (b s).1.1

def eigRank (τ : R →+* O) : ℕ := Module.finrank O (omegaEig α τ)

def htEig (p : ℕ) (τ : R →+* O) : Submodule O (omegaEig α τ) :=
  ((htSpan G p).map (restrictEig α τ)).comap (omegaEig α τ).subtype

example (τ : R →+* O) (f : LieG G → O) (hf : f ∈ omega G) :
    restrictEig α τ f ∈ omegaEig α τ := by
  refine ⟨fun x y z h => ?_, fun c x z h => ?_⟩
  · have := hf.1 x.1 y.1 (h ▸ z.1.2)
    show f z.1 = f x.1 + f y.1
    rw [← this]; congr 1; exact Subtype.ext h
  · have := hf.2 c x.1 (h ▸ z.1.2)
    show f z.1 = c * f x.1
    rw [← this]; congr 1; exact Subtype.ext h

end Eigen

section Arith

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {E : Type} [Field E] [NumberField E] (α : RingAct G (𝓞 E))

variable [IsCMField E]

def HasSignatureOn (Ψ : Set (𝓞 E →+* O)) (rp rm : ℕ) : Prop :=
  ∀ τ ∈ Ψ, HasEigRank α τ rp ∧ HasEigRank α (conjEmb τ) rm

end Arith

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
