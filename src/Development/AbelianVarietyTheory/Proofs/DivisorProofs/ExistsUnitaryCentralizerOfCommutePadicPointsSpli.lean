import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.Classify

section
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  first | exact @GlobalTheory.HTGroupOver.liesOver_or_conj | exact GlobalTheory.HTGroupOver.liesOver_or_conj | (intros; apply GlobalTheory.HTGroupOver.liesOver_or_conj <;> assumption)
end

section
open GlobalTheory.LKTrip

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.MaxIdealTensorPadic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem conjT_conjT (y : ℚ_[p] ⊗[ℚ] G.F) : conjT G.F ℚ_[p] (conjT G.F ℚ_[p] y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [conjT_tmul, NumberField.IsCMField.complexConj_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eq_sigma_liftW (f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p)
    (hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a)
    (i : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x)) (y : ℚ_[p] ⊗[ℚ] G.F) :
    f y = σ ((G.liftW i y : G.Fw i) : PadicAlgCl p) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : (a ⊗ₜ[ℚ] x : ℚ_[p] ⊗[ℚ] G.F) = (a ⊗ₜ 1) * (1 ⊗ₜ x) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, map_mul, hf, h, map_mul, MulMemClass.coe_mul, map_mul]
    congr 1
    · simp [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, HTGroup.embW]
    · congr 1
      simp only [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, AddMemClass.coe_add, map_add]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (M : Ideal (TensorProduct ℚ ℚ_[p] G.F)), M.IsMaximal →
    ∃ i : Fin G.m, M = RingHom.ker (G.liftW i) ∨
      M = RingHom.ker ((G.liftW i).toRingHom.comp (conjT G.F ℚ_[p])) := by
  intro p _ G M hM
  letI : Field ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Algebra.IsAlgebraic.of_finite _ _
  let ι : ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  let f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).toRingHom
  have hker : ∀ y, y ∈ M ↔ f y = 0 := by
    intro y
    show y ∈ M ↔ ι (Ideal.Quotient.mk M y) = 0
    rw [map_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a =>
    (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).commutes a
  let τ : G.F →+* PadicAlgCl p := f.comp (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] _).toRingHom
  rcases GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver p G τ with hτ | hτ
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ hτ
    refine ⟨i, Or.inl ?_⟩
    have h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    rw [hker, RingHom.mem_ker, eq_sigma_liftW G f hf i σ h y, map_eq_zero_iff _ σ.injective]
    exact ZeroMemClass.coe_eq_zero
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
    refine ⟨i, Or.inr ?_⟩
    let g : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := f.comp (conjT G.F ℚ_[p])
    have hg : ∀ a : ℚ_[p], g (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a => by
      simp only [g, RingHom.comp_apply, conjT_tmul, map_one, hf]
    have h : ∀ x : G.F, g (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    have e : f y = g (conjT G.F ℚ_[p] y) := by simp only [g, RingHom.comp_apply, conjT_conjT]
    rw [hker, e, eq_sigma_liftW G g hg i σ h, map_eq_zero_iff _ σ.injective, RingHom.mem_ker]
    exact ZeroMemClass.coe_eq_zero

end GlobalTheory.MaxIdealTensorPadic
end
end

section
open GlobalTheory.LKTrip

namespace GlobalTheory

theorem padic_tensor_numberField_isReduced :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F],
      IsReduced (TensorProduct ℚ ℚ_[p] F) := by
  intro p _ F _ _
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℚ_[p] (TensorProduct ℚ ℚ_[p] F) :=
    Algebra.FormallyUnramified.base_change ℚ_[p]
  exact Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] (TensorProduct ℚ ℚ_[p] F)

end GlobalTheory
end

section
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.HTGroupLocInj
variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

noncomputable def iotaZ : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem locW_iotaZ (i : Fin G.m) (z : ℚ_[p] ⊗[ℚ] G.F) :
    G.locW i (iotaZ G z) = algebraMap (G.Fw i) (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (G.liftW i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    change (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) a) * (G.rho i (algebraMap G.F G.C y)) =
      algebraMap (G.Fw i) _ (algebraMap ℚ_[p] (G.Fw i) a * G.embW i y)
    rw [G.rho_F, Algebra.ofId_apply, map_mul, ← IsScalarTower.algebraMap_apply]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

theorem starT_iotaZ (z : ℚ_[p] ⊗[ℚ] G.F) :
    (starT G.star ℚ_[p] (iotaZ G z)).unop = iotaZ G (conjT G.F ℚ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp [iotaZ, starT_tmul, G.star_F]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem inj_Z (z : ℚ_[p] ⊗[ℚ] G.F) (h1 : ∀ i, G.liftW i z = 0) (h2 : ∀ i, G.liftW i (conjT G.F ℚ_[p] z) = 0) :
    z = 0 := by
  have hJ : z ∈ (⊥ : Ideal (ℚ_[p] ⊗[ℚ] G.F)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    obtain ⟨i, hi | hi⟩ := GlobalTheory.MaxIdealTensorPadic.main p G M hM <;> rw [hi, RingHom.mem_ker]
    · exact h1 i
    · exact h2 i
  haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] G.F) := IsArtinianRing.of_finite ℚ_[p] _
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ℚ_[p] ⊗[ℚ] G.F)
  have hk0 : z ^ k = 0 := by
    have := Ideal.pow_mem_pow hJ k
    rw [hk] at this
    simpa using this
  haveI := GlobalTheory.padic_tensor_numberField_isReduced p G.F
  exact IsReduced.eq_zero _ ⟨k, hk0⟩

theorem iotaZ_comm (d : ℚ_[p] ⊗[ℚ] G.C) (z : ℚ_[p] ⊗[ℚ] G.F) : Commute d (iotaZ G z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact hx.add_right hy
  | tmul a y =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => exact hx.add_left hy
    | tmul b c =>
      simp only [iotaZ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (b ⊗ₜ c) * (a ⊗ₜ algebraMap G.F G.C y) = (a ⊗ₜ algebraMap G.F G.C y) * (b ⊗ₜ c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b a,
        Algebra.commutes]

theorem locW_inj (x : ℚ_[p] ⊗[ℚ] G.C) (h1 : ∀ i, G.locW i x = 0)
    (h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = 0) : x = 0 := by
  classical
  letI algD : Algebra G.F (ℚ_[p] ⊗[ℚ] G.C) :=
    RingHom.toAlgebra' ((iotaZ G).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)) (by
      intro c d
      show iotaZ G ((1 : ℚ_[p]) ⊗ₜ c) * d = d * iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
      exact (iotaZ_comm G d _).symm.eq)
  letI algZ : Algebra G.F (ℚ_[p] ⊗[ℚ] G.F) := Algebra.TensorProduct.rightAlgebra
  let f : G.C →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).toRingHom with
      commutes' := fun c => by
        show (1 : ℚ_[p]) ⊗ₜ algebraMap G.F G.C c = iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
        simp [iotaZ] }
  let g : (ℚ_[p] ⊗[ℚ] G.F) →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (iotaZ G).toRingHom with
      commutes' := fun c => rfl }
  let Φ := Algebra.TensorProduct.lift f g (fun c z => iotaZ_comm G _ _)
  have hΦ1 : ∀ z, Φ ((1 : G.C) ⊗ₜ z) = iotaZ G z := fun z => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hΦs : Function.Surjective Φ := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
      refine ⟨c ⊗ₜ (a ⊗ₜ (1 : G.F)), ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show ((1 : ℚ_[p]) ⊗ₜ c) * iotaZ G (a ⊗ₜ 1) = a ⊗ₜ c
      simp [iotaZ, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  let ψ : ℚ_[p] ⊗[ℚ] G.C →+* ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) ×
      ((i : Fin G.m) → (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ᵐᵒᵖ) :=
    RingHom.prod (RingHom.pi fun i => (G.locW i).toRingHom)
      (RingHom.pi fun i => (RingHom.op (G.locW i).toRingHom).comp (starT G.star ℚ_[p]))
  have hψ : ∀ d, ψ d = 0 ↔ (∀ i, G.locW i d = 0) ∧ ∀ i, G.locW i (starT G.star ℚ_[p] d).unop = 0 := by
    intro d
    simp only [ψ, Prod.ext_iff, funext_iff, RingHom.prod_apply, Pi.ringHom_apply, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, RingHom.comp_apply]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [← MulOpposite.unop_inj]
    rfl
  let J : TwoSidedIdeal (G.C ⊗[G.F] (ℚ_[p] ⊗[ℚ] G.F)) := TwoSidedIdeal.ker (ψ.comp Φ.toRingHom)
  have hJ : J = ⊥ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot J hne
    apply hz0
    rw [TwoSidedIdeal.mem_ker, RingHom.comp_apply] at hz
    change ψ (Φ ((1 : G.C) ⊗ₜ z)) = 0 at hz
    rw [hΦ1, hψ] at hz
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    apply inj_Z G z
    · intro i
      have := hz.1 i
      rw [locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
    · intro i
      have := hz.2 i
      rw [starT_iotaZ, locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
  obtain ⟨y, rfl⟩ := hΦs x
  have hy : y ∈ J := by
    rw [TwoSidedIdeal.mem_ker]
    exact (hψ _).2 ⟨h1, h2⟩
  rw [hJ, TwoSidedIdeal.mem_bot] at hy
  rw [hy, map_zero]

end GlobalTheory.HTGroupLocInj
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.Frame

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {k : Type} [Field k] [CharP k p]
  [PerfectRing k p] {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {H : PDivGroup p k}
  {act : D.O → (H ⟶ H)} {rat : ℤ → (H ⟶ H) → Prop} {d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)}

def part (fr : Frame L T red r H act rat d) (w : Fin G.m) : Submodule (WittVector p k) (T.M H) :=
  Submodule.span (WittVector p k) (Set.range (fr.B w))

end GlobalTheory.LKGeo.Frame
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKTrip

theorem exists_algEquiv_extending_padicAlgCl {p : ℕ} [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (φ : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x : E, σ x = φ x := by
  refine ⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p))
    (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩
  exact φ.liftNormal_commutes (PadicAlgCl p) x

theorem HTGroup.sum_finrank_Fw_eq_finrank_Kq {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank G.Kq G.F := by
  letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra
  haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F
  let f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p) := fun a =>
    { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with
      commutes' := fun x => by
        have h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x) :=
          Subtype.ext (G.emb_over a.1 x)
        change a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)
        rw [h, AlgHom.commutes] }
  have hf : ∀ a x, f a x = a.2 (G.embW a.1 x) := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨w, φ⟩ ⟨w', ψ⟩ h
      have h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x) := fun x => by
        rw [← hf ⟨w, φ⟩, h, hf]
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending_padicAlgCl _ φ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_padicAlgCl _ ψ
      obtain rfl : w = w' := by
        refine G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)
        change τ.symm (σ (G.emb w x)) = G.emb w' x
        rw [AlgEquiv.symm_apply_eq]
        exact (hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)
      obtain rfl : φ = ψ := by
        refine IntermediateField.adjoin_algHom_ext ℚ_[p] ?_
        rintro _ ⟨x, rfl⟩
        exact h' x
      rfl
    · intro τ
      obtain ⟨w, σ, h⟩ := G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)
      refine ⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
      exact (DFunLike.congr_fun h x).symm
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_sigma, AlgHom.card] at hc
  simpa only [AlgHom.card] using hc

theorem HTGroup.two_mul_sum_finrank_Fw (p : ℕ) [Fact p.Prime] (G : HTGroup p) :
    2 * ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank ℚ G.F := by
  rw [G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]
  exact Module.finrank_mul_finrank ℚ G.Kq G.F

end GlobalTheory.LKTrip
end

section
open GlobalTheory.LKTrip
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKTrip.HTGroup.LocPBij

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem starT_starT (x : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (starT G.star ℚ_[p] x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem starT_algebraMap (a : ℚ_[p]) :
    (starT G.star ℚ_[p] (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a)).unop = algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
    MulOpposite.unop_one]

theorem starT_mul (x y : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (x * y)).unop = (starT G.star ℚ_[p] y).unop * (starT G.star ℚ_[p] x).unop := by
  rw [map_mul, MulOpposite.unop_mul]

def starL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C where
  toFun x := (starT G.star ℚ_[p] x).unop
  map_add' x y := by rw [map_add, MulOpposite.unop_add]
  map_smul' a x := by
    rw [Algebra.smul_def, starT_mul, starT_algebraMap, RingHom.id_apply, Algebra.smul_def]
    exact (Algebra.commutes _ _).symm

def psiL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]]
    ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :=
  LinearMap.prod (LinearMap.pi fun i => (G.locW i).toLinearMap)
    ((LinearMap.pi fun i => (G.locW i).toLinearMap).comp (starL G))

theorem psiL_injective : Function.Injective (psiL G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact GlobalTheory.HTGroupLocInj.locW_inj G x (fun i => congrFun (congrArg Prod.fst hx) i)
    (fun i => congrFun (congrArg Prod.snd hx) i)

theorem finrank_eq : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) = Module.finrank ℚ_[p]
    (((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i))) := by
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_prod,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Fintype.card_fin]
  rw [← HTGroup.two_mul_sum_finrank_Fw p G, ← Finset.mul_sum]
  ring

theorem psiL_bijective : Function.Bijective (psiL G) := by
  haveI : ∀ i, FiniteDimensional ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => inferInstance
  exact ⟨psiL_injective G,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq G)).1 (psiL_injective G)⟩

end GlobalTheory.LKTrip.HTGroup.LocPBij

theorem GlobalTheory.LKTrip.HTGroup.bijective_locP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  intro p _ G
  have key : ∀ d : ℚ_[p] ⊗[ℚ] G.C, (starT G.star ℚ_[p] d).unop = d → (∀ i, G.locW i d = 0) → d = 0 :=
    fun d hd h0 => GlobalTheory.HTGroupLocInj.locW_inj G d h0 (fun i => by rw [hd]; exact h0 i)
  constructor
  · rintro ⟨⟨x, c⟩, hx⟩ ⟨⟨y, d⟩, hy⟩ h
    have hx' : (x : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := hx
    have hy' : (y : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] y).unop = algebraMap ℚ_[p] _ (d : ℚ_[p]) := hy
    have hc : c = d := congrArg Prod.fst h
    subst hc
    have hu := fun i => congrFun (congrArg Prod.snd h) i
    have sx : (starT G.star ℚ_[p] x).unop = ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hx', ← mul_assoc, Units.inv_mul, one_mul]
    have sy : (starT G.star ℚ_[p] y).unop = ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hy', ← mul_assoc, Units.inv_mul, one_mul]
    have hw : ∀ i, G.locW i x = G.locW i y := fun i => congrArg Units.val (hu i)
    have hwi : ∀ i, G.locW i ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) = G.locW i ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) := by
      intro i
      have := congrArg (fun u => ((u⁻¹ : (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ˣ) : Matrix (Fin G.n) (Fin G.n) (G.Fw i))) (hu i)
      exact this
    have hxy : x = y := by
      apply Units.ext
      apply GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_injective G
      refine Prod.ext (funext hw) (funext fun i => ?_)
      show G.locW i (starT G.star ℚ_[p] x).unop = G.locW i (starT G.star ℚ_[p] y).unop
      rw [sx, sy, map_mul, map_mul, hwi]
    subst hxy
    rfl
  · rintro ⟨c, a⟩
    obtain ⟨x, hx⟩ := (GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_bijective G).2
      (fun i => ((a i : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)),
       fun i => algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)))
    have h1 : ∀ i, G.locW i x = a i := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => congrFun (congrArg Prod.snd hx) i
    have hyy := GlobalTheory.LKTrip.HTGroup.LocPBij.starT_starT G x
    have hxy : x * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, Algebra.left_comm, Units.mul_inv, mul_one, sub_self]
    have hyx : (starT G.star ℚ_[p] x).unop * x = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, mul_assoc, Units.inv_mul, mul_one, sub_self]
    let u : (ℚ_[p] ⊗[ℚ] G.C)ˣ := ⟨x, algebraMap ℚ_[p] _ ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (starT G.star ℚ_[p] x).unop,
      by rw [Algebra.left_comm, hxy, ← map_mul, Units.inv_mul, map_one],
      by rw [mul_assoc, hyx, ← map_mul, Units.inv_mul, map_one]⟩
    refine ⟨⟨(u, c), hxy⟩, Prod.ext rfl (funext fun i => Units.ext (h1 i))⟩
end
end

section
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.bijective_locP) | (exact GlobalTheory.LKTrip.HTGroup.bijective_locP) | (intros; apply GlobalTheory.LKTrip.HTGroup.bijective_locP  <;> assumption)
end

section
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem GlobalTheory.TorCls.centraliser_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c :=
  fun p _ G β hβ y₀ c hc => GlobalTheory.TorCls.AtP.atp_of_bijective G (GlobalTheory.T.padicPoints_similitude_GL_product_bijective p G) β hβ y₀ c hc
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c := by
  atlas_forward_decl GlobalTheory.TorCls.centraliser_at_p
end
