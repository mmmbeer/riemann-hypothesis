import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensCntRes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL

section
noncomputable section

namespace PI.VolStabSW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

structure AntiB (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) where
  δ : E
  D0 : F
  c : Module.Basis (Fin 2) F E
  hc0 : c 0 = 1
  hc1 : c 1 = δ
  hδ : δ * δ = algebraMap F E D0
  hσδ : σ δ = -δ
  hD0 : D0 ≠ 0

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem repr_change {ι ι' : Type} [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E) (z : Fv F v ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr z k =
      ∑ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j *
        algebraMap F (Fv F v) (b.repr (c j) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) c).sum_repr z]
  simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.smul_apply, Finsupp.mapRange_apply]

theorem int_iff {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (z : Fv F v ⊗[F] E) :
    (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F) ↔
      (∀ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j ∈ v.adicCompletionIntegers F) := by
  constructor
  · intro h j
    rw [repr_change v c b z j]
    exact sum_mem fun k _ => mul_mem (h k) (hcb k j)
  · intro h k
    rw [repr_change v b c z k]
    exact sum_mem fun j _ => mul_mem (h j) (hbc j k)

variable {σ : E →ₐ[F] E} (A : AntiB F E σ)

abbrev Pt (x y : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ (1 : E) + y ⊗ₜ A.δ

abbrev Xc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 0

abbrev Yc (z : Fv F v ⊗[F] E) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) A.c).repr z 1

theorem repr_Pt (x y : Fv F v) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (Pt v A x y) = Finsupp.single 0 x + Finsupp.single 1 y := by
  have h0 : (Algebra.TensorProduct.basis (Fv F v) A.c).repr (x ⊗ₜ (1 : E)) = Finsupp.single 0 x := by
    rw [← A.hc0, Algebra.TensorProduct.basis_repr_tmul, A.c.repr_self]
    simp [Finsupp.mapRange_single]
  have h1 : (Algebra.TensorProduct.basis (Fv F v) A.c).repr (y ⊗ₜ A.δ) = Finsupp.single 1 y := by
    rw [← A.hc1, Algebra.TensorProduct.basis_repr_tmul, A.c.repr_self]
    simp [Finsupp.mapRange_single]
  rw [map_add, h0, h1]

theorem Xc_Pt (x y : Fv F v) : Xc v A (Pt v A x y) = x := by
  rw [Xc, repr_Pt]; simp

theorem Yc_Pt (x y : Fv F v) : Yc v A (Pt v A x y) = y := by
  rw [Yc, repr_Pt]; simp

theorem decomp (z : Fv F v ⊗[F] E) : z = Pt v A (Xc v A z) (Yc v A z) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) A.c).sum_repr z]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, A.hc0,
    A.hc1, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,
    mul_one]

theorem Pt_mul (x y x' y' : Fv F v) :
    Pt v A x y * Pt v A x' y' =
      Pt v A (x * x' + y * y' * algebraMap F (Fv F v) A.D0) (x * y' + y * x') := by
  have e : (y * y') ⊗ₜ[F] (algebraMap F E A.D0) =
      (y * y' * algebraMap F (Fv F v) A.D0) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.algebraMap_eq_smul_one A.D0, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def]; ring
  simp only [Pt, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, A.hδ, e,
    TensorProduct.add_tmul]
  rw [mul_comm y x']
  abel

theorem one_eq_Pt : (1 : Fv F v ⊗[F] E) = Pt v A 1 0 := by
  rw [Pt, TensorProduct.zero_tmul, add_zero, Algebra.TensorProduct.one_def]

theorem sig_Pt (x y : Fv F v) : sigR (Fv F v) σ (Pt v A x y) = Pt v A x (-y) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (Pt v A x y) = _
  simp [Pt, Algebra.TensorProduct.map_tmul, A.hσδ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem Xc_mul (z w : Fv F v ⊗[F] E) :
    Xc v A (z * w) = Xc v A z * Xc v A w + Yc v A z * Yc v A w * algebraMap F (Fv F v) A.D0 := by
  conv_lhs => rw [decomp v A z, decomp v A w, Pt_mul, Xc_Pt]

theorem Yc_mul (z w : Fv F v ⊗[F] E) :
    Yc v A (z * w) = Xc v A z * Yc v A w + Yc v A z * Xc v A w := by
  conv_lhs => rw [decomp v A z, decomp v A w, Pt_mul, Yc_Pt]

theorem Xc_sig (z : Fv F v ⊗[F] E) : Xc v A (sigR (Fv F v) σ z) = Xc v A z := by
  conv_lhs => rw [decomp v A z, sig_Pt, Xc_Pt]

theorem Yc_sig (z : Fv F v ⊗[F] E) : Yc v A (sigR (Fv F v) σ z) = -Yc v A z := by
  conv_lhs => rw [decomp v A z, sig_Pt, Yc_Pt]

theorem Xc_one : Xc v A 1 = 1 := by rw [one_eq_Pt v A, Xc_Pt]

theorem Yc_one : Yc v A 1 = 0 := by rw [one_eq_Pt v A, Yc_Pt]

theorem repr_incl (e : E) (j : Fin 2) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (inclR (Fv F v) e) j =
      algebraMap F (Fv F v) (A.c.repr e j) := by
  show (Algebra.TensorProduct.basis (Fv F v) A.c).repr ((1 : Fv F v) ⊗ₜ e) j = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem Xc_add (z w : Fv F v ⊗[F] E) : Xc v A (z + w) = Xc v A z + Xc v A w := by
  rw [Xc, Xc, Xc, map_add, Finsupp.add_apply]

theorem Yc_add (z w : Fv F v ⊗[F] E) : Yc v A (z + w) = Yc v A z + Yc v A w := by
  rw [Yc, Yc, Yc, map_add, Finsupp.add_apply]

theorem Xc_neg (z : Fv F v ⊗[F] E) : Xc v A (-z) = -Xc v A z := by
  rw [Xc, Xc, map_neg, Finsupp.neg_apply]

theorem Yc_neg (z : Fv F v ⊗[F] E) : Yc v A (-z) = -Yc v A z := by
  rw [Yc, Yc, map_neg, Finsupp.neg_apply]

theorem Xc_zero : Xc v A 0 = 0 := by simp [Xc]

theorem Yc_zero : Yc v A 0 = 0 := by simp [Yc]

def InC (z : Fv F v ⊗[F] E) : Prop :=
  Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F

variable (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)

def lamC : Subring (Fv F v ⊗[F] E) where
  carrier := {z | InC v A z}
  mul_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z * w)
    refine ⟨?_, ?_⟩
    · rw [Xc_mul]
      exact add_mem (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD)
    · rw [Yc_mul]
      exact add_mem (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1)
  one_mem' := by
    change InC v A 1
    refine ⟨?_, ?_⟩
    · rw [Xc_one]; exact one_mem _
    · rw [Yc_one]; exact zero_mem _
  add_mem' {z w} hz hw := by
    change InC v A z at hz
    change InC v A w at hw
    change InC v A (z + w)
    exact ⟨by rw [Xc_add]; exact add_mem hz.1 hw.1, by rw [Yc_add]; exact add_mem hz.2 hw.2⟩
  zero_mem' := by
    change InC v A 0
    exact ⟨by rw [Xc_zero]; exact zero_mem _, by rw [Yc_zero]; exact zero_mem _⟩
  neg_mem' {z} hz := by
    change InC v A z at hz
    change InC v A (-z)
    exact ⟨by rw [Xc_neg]; exact neg_mem hz.1, by rw [Yc_neg]; exact neg_mem hz.2⟩

theorem mem_lamC (z : Fv F v ⊗[F] E) : z ∈ lamC v A hD ↔
    Xc v A z ∈ v.adicCompletionIntegers F ∧ Yc v A z ∈ v.adicCompletionIntegers F := Iff.rfl

theorem incl_mem (e : E) (he : ∀ j, algebraMap F (Fv F v) (A.c.repr e j) ∈ v.adicCompletionIntegers F) :
    inclR (Fv F v) e ∈ lamC v A hD := by
  rw [mem_lamC, Xc, Yc, repr_incl, repr_incl]
  exact ⟨he 0, he 1⟩

theorem sig_mem {z : Fv F v ⊗[F] E} (hz : z ∈ lamC v A hD) : sigR (Fv F v) σ z ∈ lamC v A hD := by
  rw [mem_lamC, Xc_sig, Yc_sig]
  exact ⟨hz.1, neg_mem hz.2⟩

def sigC : lamC v A hD →+* lamC v A hD where
  toFun z := ⟨sigR (Fv F v) σ z, sig_mem v A hD z.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coe_sigC (z : lamC v A hD) : (sigC v A hD z : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))

include hr in

def rho : lamC v A hD →+* K where
  toFun z := algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r
  map_one' := by
    simp only [Subring.coe_one, Xc_one, Yc_one, red_one, red_zero, map_one, map_zero, zero_mul,
      add_zero]
  map_mul' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [Subring.coe_mul, Xc_mul, Yc_mul]
    rw [red_add v (mul_mem hz.1 hw.1) (mul_mem (mul_mem hz.2 hw.2) hD),
      red_add v (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1), red_mul v hz.1 hw.1,
      red_mul v (mul_mem hz.2 hw.2) hD, red_mul v hz.2 hw.2, red_mul v hz.1 hw.2,
      red_mul v hz.2 hw.1]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap _ K (red v (Yc v A z)) * algebraMap _ K (red v (Yc v A w)))) * hr
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, Xc_zero, Yc_zero, red_zero, map_zero, zero_mul, add_zero]
  map_add' z w := by
    have hz := z.2
    have hw := w.2
    rw [mem_lamC] at hz hw
    simp only [AddMemClass.coe_add, Xc_add, Yc_add]
    rw [red_add v hz.1 hw.1, red_add v hz.2 hw.2]
    simp only [map_add]
    ring

theorem rho_apply (z : lamC v A hD) : rho v A hD r hr z =
    algebraMap _ K (red v (Xc v A z)) + algebraMap _ K (red v (Yc v A z)) * r := rfl

theorem rho_sig (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
    (z : lamC v A hD) : rho v A hD r hr (sigC v A hD z) = σ' (rho v A hD r hr z) := by
  have hz := z.2
  rw [mem_lamC] at hz
  rw [rho_apply, rho_apply, coe_sigC, Xc_sig, Yc_sig, red_neg v hz.2, map_add, map_mul,
    AlgEquiv.commutes, AlgEquiv.commutes, hσr, map_neg]
  ring

variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))

include hbij in
theorem rho_eq_zero (z : lamC v A hD) : rho v A hD r hr z = 0 ↔
    Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1 := by
  have hz := z.2
  rw [mem_lamC] at hz
  rw [← red_eq_zero_iff v hz.1, ← red_eq_zero_iff v hz.2, rho_apply]
  constructor
  · intro h
    have := hbij.1 (a₁ := (red v (Xc v A z), red v (Yc v A z))) (a₂ := (0, 0)) (by simpa using h)
    simp only [Prod.mk.injEq] at this
    exact this
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; simp

include hbij in
theorem rho_surj (w : K) : ∃ z : lamC v A hD, rho v A hD r hr z = w := by
  obtain ⟨⟨s, t⟩, hst⟩ := hbij.2 w
  obtain ⟨x, hx, rfl⟩ := red_surj v s
  obtain ⟨y, hy, rfl⟩ := red_surj v t
  refine ⟨⟨Pt v A x y, ?_⟩, ?_⟩
  · rw [mem_lamC, Xc_Pt, Yc_Pt]; exact ⟨hx, hy⟩
  · rw [rho_apply]
    simp only [Xc_Pt, Yc_Pt]
    exact hst

theorem smul_char (z : Fv F v ⊗[F] E) :
    (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔
      (z ∈ lamC v A hD ∧ Valued.v (Xc v A z) < 1 ∧ Valued.v (Yc v A z) < 1) := by
  have hπ := unifV_spec v
  have hπv : Valued.v (unifV v) < 1 := by rw [unifV_val]; decide
  constructor
  · rintro ⟨z', hz', rfl⟩
    rw [mem_lamC] at hz'
    have ex : Xc v A (unifV v • z') = unifV v * Xc v A z' := by
      rw [Xc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have ey : Yc v A (unifV v • z') = unifV v * Yc v A z' := by
      rw [Yc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have h1 : ∀ x ∈ v.adicCompletionIntegers F, Valued.v (unifV v * x) < 1 := by
      intro x hx
      rw [map_mul]
      calc Valued.v (unifV v) * Valued.v x ≤ Valued.v (unifV v) * 1 :=
            mul_le_mul' le_rfl ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx)
        _ < 1 := by rw [mul_one]; exact hπv
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_lamC, ex, ey]; exact ⟨mul_mem hπ.2.2 hz'.1, mul_mem hπ.2.2 hz'.2⟩
    · rw [ex]; exact h1 _ hz'.1
    · rw [ey]; exact h1 _ hz'.2
  · rintro ⟨_, h1, h2⟩
    refine ⟨(unifV v)⁻¹ • z, ?_, ?_⟩
    · rw [mem_lamC, Xc, Yc, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
        smul_eq_mul]
      exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2
          ((lt_one_iff_unif v _).1 h1),
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2
          ((lt_one_iff_unif v _).1 h2)⟩
    · rw [smul_smul, mul_inv_cancel₀ hπ.1, one_smul]

end Lat

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hinv := sigma_invol σ hCM.2.2.2
  have hne : ∃ e, σ e ≠ e := by
    by_contra h
    push Not at h
    let w : InfinitePlace E := Classical.arbitrary _
    have hc : w.IsComplex := hCM.2.1.isComplex w
    apply (InfinitePlace.not_isReal_iff_isComplex.2 hc)
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := hCM.2.2.2 w.embedding x
    rw [h x] at this
    rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact this.symm
  obtain ⟨e, he⟩ := hne
  refine ⟨e - σ e, sub_ne_zero.2 (Ne.symm he), ?_⟩
  rw [map_sub, hinv]; ring

theorem anti_coeff (σ : E →ₐ[F] E) {δ : E} (hδ0 : δ ≠ 0) (hσδ : σ δ = -δ) (s t : F)
    (h : σ (s • (1 : E) + t • δ) = s • 1 + t • δ) : t = 0 := by
  simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hσδ, mul_one] at h
  have h2 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (algebraMap F E).injective (by rw [h4, map_zero])
    · exact absurd h4 hδ0

theorem exists_basis_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have hinv := sigma_invol σ hCM.2.2.2
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := anti_coeff σ hδ0 hσδ s t (by rw [hst, map_zero])
    subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [hCM.2.2.1]; rfl
  let c := basisOfLinearIndependentOfCardEqFinrank li hcard
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = δ := by simp [c]
  have hsum := c.sum_repr (δ * δ)
  rw [Fin.sum_univ_two, hc0, hc1] at hsum
  have hβ : c.repr (δ * δ) 1 = 0 := by
    refine anti_coeff σ hδ0 hσδ (c.repr (δ * δ) 0) _ ?_
    rw [hsum, map_mul, hσδ]; ring
  rw [hβ, zero_smul, add_zero, Algebra.smul_def, mul_one] at hsum
  refine ⟨δ, c.repr (δ * δ) 0, c, hδ0, hσδ, hsum.symm, ?_, hc0, hc1⟩
  intro h0
  rw [h0, map_zero] at hsum
  exact hδ0 (mul_self_eq_zero.1 hsum.symm)

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open Polynomial

theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  classical
  by_cases hsq : ∃ c : k, c * c = D
  · obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by rintro rfl; exact hD (by rw [← hc, mul_zero])
    let σ' : (k × k) ≃ₐ[k] (k × k) :=
      { RingEquiv.prodComm with commutes' := fun r => rfl }
    have hσ : ∀ x : k × k, σ' x = x.swap := fun x => rfl
    refine ⟨k × k, inferInstance, inferInstance, σ', (c, -c), ⟨fun x => by simp [hσ], Or.inr
      ⟨AlgEquiv.refl, fun x => by simp [hσ]⟩⟩, ?_, ?_, ?_⟩
    · ext <;> simp [hc]
    · ext <;> simp [hσ]
    · have h2c : (2 : k) * c ≠ 0 := mul_ne_zero h2 hc0
      constructor
      · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
        obtain ⟨h1, h2'⟩ := h
        have hy : y1 = y2 := by
          have : (2 * c) * (y1 - y2) = 0 := by linear_combination h1 - h2'
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2c)
        subst hy
        have hx : x1 = x2 := by linear_combination h1
        rw [hx]
      · rintro ⟨u, w⟩
        refine ⟨((u + w) / 2, (u - w) / (2 * c)), ?_⟩
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        constructor
        · field_simp
          ring
        · field_simp
          ring
  · push Not at hsq
    let f : k[X] := X ^ 2 - C D
    have hfdeg : f.natDegree = 2 := natDegree_X_pow_sub_C
    have hnr : ∀ x, ¬ IsRoot f x := by
      intro x hx
      apply hsq x
      have : x ^ 2 - D = 0 := by simpa [f] using hx
      linear_combination this
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide) hnr
    have : Fact (Irreducible f) := ⟨hirr⟩
    have hf0 : f ≠ 0 := hirr.ne_zero
    let K := AdjoinRoot f
    let r : K := AdjoinRoot.root f
    have hr2 : r * r = algebraMap k K D := by
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      rw [← sq, show algebraMap k K D = AdjoinRoot.of f D from rfl]
      linear_combination h
    have hneg : f.eval₂ (Algebra.ofId k K) (-r) = 0 := by
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq]
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      exact h
    let τ : K →ₐ[k] K := AdjoinRoot.liftAlgHom f (Algebra.ofId k K) (-r) hneg
    have hτr : τ r = -r := AdjoinRoot.liftAlgHom_root _ _ _ _
    have hττ : τ.comp τ = AlgHom.id k K := by
      apply AdjoinRoot.algHom_ext
      show τ (τ r) = r
      rw [hτr, map_neg, hτr, neg_neg]
    let σ' : K ≃ₐ[k] K := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσr : σ' r = -r := hτr
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr2
      exact hD ((algebraMap k K).injective (by rw [← hr2, map_zero]))
    have h2K : (2 : K) ≠ 0 := by
      intro h
      apply h2
      apply (algebraMap k K).injective
      rw [map_ofNat, h, map_zero]
    have hfin : Module.finrank k K = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
    refine ⟨K, inferInstance, inferInstance, σ', r, ⟨fun x => ?_, Or.inl ⟨Field.toIsField K, hfin,
      fun h => ?_⟩⟩, hr2, hσr, ?_⟩
    · show τ (τ x) = x
      exact congrArg (fun g : K →ₐ[k] K => g x) hττ
    · have h1 : σ' r = r := by rw [h]; rfl
      rw [hσr] at h1
      have : (2 : K) * r = 0 := by linear_combination -h1
      exact hr0 ((mul_eq_zero.1 this).resolve_left h2K)
    · have hinj : Function.Injective
          (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
        rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only at h
        by_cases hy : y1 = y2
        · subst hy
          have : algebraMap k K x1 = algebraMap k K x2 := by linear_combination h
          rw [(algebraMap k K).injective this]
        · exfalso
          have hy' : y1 - y2 ≠ 0 := sub_ne_zero.2 hy
          have hyK : algebraMap k K (y1 - y2) ≠ 0 := by
            rw [Ne, map_eq_zero_iff _ (algebraMap k K).injective]; exact hy'
          have hm : algebraMap k K (y1 - y2) * r = algebraMap k K (x2 - x1) := by
            rw [map_sub, map_sub]; linear_combination h
          have hrr : r = algebraMap k K ((x2 - x1) / (y1 - y2)) := by
            rw [map_div₀, eq_div_iff hyK, mul_comm]
            exact hm
          apply hsq ((x2 - x1) / (y1 - y2))
          apply (algebraMap k K).injective
          rw [map_mul, ← hrr, hr2]
      have hKm : Module.Finite k K := (AdjoinRoot.powerBasis hf0).finite
      have hKf : Finite K := Module.finite_of_finite k
      refine hinj.bijective_of_nat_card_le ?_
      letI := Fintype.ofFinite k
      letI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
        hfin, Fintype.card_prod, sq]

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem sigR_incl (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ e) =
    (1 : Fv F v) ⊗ₜ σ e
  simp [Algebra.TensorProduct.map_tmul]

theorem two_ne_zero_k (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1) :
    (2 : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
  intro h
  have h' : Ideal.Quotient.mk v.asIdeal (2 : 𝓞 F) = 0 := by rw [map_ofNat]; exact h
  rw [Ideal.Quotient.eq_zero_iff_mem, ← v_iO_lt_iff] at h'
  simp only [iO, map_ofNat] at h' h2
  rw [h2] at h'
  exact lt_irrefl _ h'

end Place

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)
  (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)

def entL {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F) :
    Matrix (Fin n) (Fin n) (lamC v A hD) :=
  Matrix.of fun p q => ⟨inclR (Fv F v) (G p q), incl_mem v A hD _ (hG p q)⟩

variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
  (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)

include hσr in
theorem cnt_herm {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (hGs : ∀ i j, σ (G j i) = G i j)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (i j : Fin n) :
    σ' (((entL v A hD G hG).map (rho v A hD r hr)) j i) = ((entL v A hD G hG).map (rho v A hD r hr)) i j := by
  simp only [Matrix.map_apply]
  rw [← rho_sig v A hD r hr σ' hσr]
  congr 1
  apply Subtype.ext
  rw [coe_sigC]
  show sigR (Fv F v) σ (inclR (Fv F v) (G j i)) = inclR (Fv F v) (G i j)
  rw [sigR_incl, hGs]

theorem cnt_unit {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (u : E) (hu : G.det * u = 1)
    (hui : ∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) :
    IsUnit ((entL v A hD G hG).map (rho v A hD r hr)).det := by
  have hdet : ((entL v A hD G hG).det : Fv F v ⊗[F] E) = inclR (Fv F v) G.det := by
    have e1 := RingHom.map_det (lamC v A hD).subtype (entL v A hD G hG)
    rw [RingHom.mapMatrix_apply] at e1
    have e2 := RingHom.map_det (inclR (Fv F v) (F := F) (E := E)) G
    rw [RingHom.mapMatrix_apply] at e2
    rw [show ((entL v A hD G hG).det : Fv F v ⊗[F] E) = (lamC v A hD).subtype (entL v A hD G hG).det
      from rfl, e1, e2]
    rfl
  have hu' : (entL v A hD G hG).det * ⟨inclR (Fv F v) u, incl_mem v A hD u hui⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdet, Subring.coe_one]
    show inclR (Fv F v) G.det * inclR (Fv F v) u = 1
    rw [← map_mul, hu, map_one]
  have e3 := RingHom.map_det (rho v A hD r hr) (entL v A hD G hG)
  rw [RingHom.mapMatrix_apply] at e3
  rw [← e3]
  exact (isUnit_iff_exists_inv.2 ⟨_, hu'⟩).map _

variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))

include hσr hbij in
set_option maxHeartbeats 400000 in
theorem cnt_meas [Finite K] (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K)
          ((entL v A hD J hJi).map (rho v A hD r hr)) X = (entL v A hD T hTi).map (rho v A hD r hr)} : ENNReal) *
          μ (lamF b v a M 0) := by
  classical
  have rs := rho_sig v A hD r hr σ' hσr
  have rz := rho_eq_zero v A hD r hr hbij
  have rsu := rho_surj v A hD r hr hbij
  generalize rho v A hD r hr = ρ at rs rz rsu ⊢
  obtain ⟨rT, rT_eq⟩ : ∃ f : Fv F v ⊗[F] E → K, ∀ z (h : z ∈ lamC v A hD), f z = ρ ⟨z, h⟩ :=
    ⟨fun z => if h : z ∈ lamC v A hD then ρ ⟨z, h⟩ else 0, fun z h => dif_pos h⟩
  have memL : ∀ Y, Y ∈ latSub b v a M ↔ ∀ i p, Y i p ∈ lamC v A hD := by
    intro Y
    show (∀ i p k, _ ∈ _) ↔ _
    refine forall_congr' fun i => forall_congr' fun p => ?_
    rw [int_iff v b A.c hbc hcb, Fin.forall_fin_two]
    exact Iff.rfl
  have memN : ∀ Y, Y ∈ lamF b v a M 0 ↔
      ∀ i p, ∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = Y i p := by
    intro Y
    rw [lamF, mem_smulSub, zero_add, pow_one]
    constructor
    · rintro ⟨Y', hY', rfl⟩ i p
      exact ⟨Y' i p, (memL Y').1 hY' i p, rfl⟩
    · intro h
      choose f hf1 hf2 using h
      exact ⟨f, (memL f).2 hf1, funext fun i => funext fun p => hf2 i p⟩
  have hsm : ∀ w : lamC v A hD,
      (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = (w : Fv F v ⊗[F] E)) ↔ ρ w = 0 := by
    intro w
    rw [smul_char v A hD, rz]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  have hNL : lamF b v a M 0 ≤ latSub b v a M := by
    intro Y hY
    rw [memN] at hY
    rw [memL]
    intro i p
    obtain ⟨z', hz', e⟩ := hY i p
    rw [← e]
    exact ((smul_char v A hD _).1 ⟨z', hz', rfl⟩).1
  have hker : ∀ Y ∈ latSub b v a M, (fun i p => rT (Y i p)) = 0 ↔ Y ∈ lamF b v a M 0 := by
    intro Y hY
    rw [memN, funext_iff]
    refine forall_congr' fun i => ?_
    rw [funext_iff]
    refine forall_congr' fun p => ?_
    have h1 := (memL Y).1 hY i p
    rw [hsm ⟨Y i p, h1⟩]
    show rT (Y i p) = 0 ↔ _
    rw [rT_eq _ h1]
  have hadd : ∀ Y ∈ latSub b v a M, ∀ Y' ∈ latSub b v a M,
      (fun i p => rT ((Y + Y') i p)) = (fun i p => rT (Y i p)) + (fun i p => rT (Y' i p)) := by
    intro Y hY Y' hY'
    funext i p
    have h1 := (memL Y).1 hY i p
    have h2 := (memL Y').1 hY' i p
    show rT (Y i p + Y' i p) = rT (Y i p) + rT (Y' i p)
    rw [rT_eq _ (add_mem h1 h2), rT_eq _ h1, rT_eq _ h2, ← map_add]
    rfl
  have hsurj : ∀ W : Fin a → Fin M → K, ∃ Y ∈ latSub b v a M, (fun i p => rT (Y i p)) = W := by
    intro W
    choose g hg using fun i p => rsu (W i p)
    refine ⟨fun i p => (g i p : Fv F v ⊗[F] E), (memL _).2 fun i p => (g i p).2, ?_⟩
    funext i p
    show rT (g i p : Fv F v ⊗[F] E) = W i p
    rw [rT_eq _ (g i p).2]
    exact hg i p
  have rT_mul : ∀ z w, z ∈ lamC v A hD → w ∈ lamC v A hD → rT (z * w) = rT z * rT w := by
    intro z w hz hw
    rw [rT_eq _ (mul_mem hz hw), rT_eq _ hz, rT_eq _ hw, ← map_mul]
    rfl
  have rT_sub : ∀ z w, z ∈ lamC v A hD → w ∈ lamC v A hD → rT (z - w) = rT z - rT w := by
    intro z w hz hw
    rw [rT_eq _ (sub_mem hz hw), rT_eq _ hz, rT_eq _ hw, ← map_sub]
    rfl
  have rT_sig : ∀ z, z ∈ lamC v A hD → rT (sigR (Fv F v) σ z) = σ' (rT z) := by
    intro z hz
    rw [rT_eq _ (sig_mem v A hD hz), rT_eq _ hz, ← rs ⟨z, hz⟩]
    rfl
  have rT_sum : ∀ (s : Finset (Fin M)) (f : Fin M → Fv F v ⊗[F] E),
      (∀ p, f p ∈ lamC v A hD) → rT (∑ p ∈ s, f p) = ∑ p ∈ s, rT (f p) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, rT_eq _ (zero_mem _), ← map_zero ρ]
      rfl
    | insert p s hp ih =>
      have hs : ∑ q ∈ s, f q ∈ lamC v A hD := sum_mem fun q _ => hf q
      rw [Finset.sum_insert hp, Finset.sum_insert hp, ← ih, rT_eq _ (add_mem (hf p) hs),
        rT_eq _ (hf p), rT_eq _ hs, ← map_add]
      rfl
  have hsm' : ∀ z, z ∈ lamC v A hD →
      ((∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔ rT z = 0) := by
    intro z hz
    rw [rT_eq _ hz]
    exact hsm ⟨z, hz⟩
  have hentry : ∀ Y, (∀ i p, Y i p ∈ lamC v A hD) → ∀ i j,
      ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) ∈ lamC v A hD ∧
      rT ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) =
        ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) (fun i p => rT (Y i p)) i j := by
    intro Y hY i j
    have e1 : ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) =
        ∑ p, ∑ q, sigR (Fv F v) σ (Y i p) * inclR (Fv F v) (J p q) * Y j q := rfl
    have hmem : ∀ p q, sigR (Fv F v) σ (Y i p) * inclR (Fv F v) (J p q) * Y j q ∈ lamC v A hD :=
      fun p q => mul_mem (mul_mem (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q))) (hY j q)
    rw [e1]
    refine ⟨sum_mem fun p _ => sum_mem fun q _ => hmem p q, ?_⟩
    rw [rT_sum _ _ fun p => sum_mem fun q _ => hmem p q]
    show _ = ∑ p, ∑ q, (σ' : K →+* K) (rT (Y i p)) * ρ (entL v A hD J hJi p q) * rT (Y j q)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rT_sum _ _ fun q => hmem p q]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [rT_mul _ _ (mul_mem (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q))) (hY j q),
      rT_mul _ _ (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q)), rT_sig _ (hY i p),
      rT_eq _ (incl_mem v A hD _ (hJi p q))]
    rfl
  have hFm : ∀ S : HermR (Fv F v) σ a, S ∈ hF b v σ a 0 ↔
      ∀ i j, ∃ z', z' ∈ lamC v A hD ∧
        unifV v • z' = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
    intro S
    rw [hF, mem_smulSub, zero_add, pow_one]
    constructor
    · rintro ⟨S', hS', rfl⟩ i j
      have hS'' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F := hS'
      have hc := (int_iff v b A.c hbc hcb _).1 (hS'' i j)
      exact ⟨(S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, ⟨hc 0, hc 1⟩, rfl⟩
    · intro h
      choose f hf1 hf2 using h
      refine ⟨(unifV v)⁻¹ • S, ?_, ?_⟩
      · intro i j
        show ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((((unifV v)⁻¹ • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ _
        rw [coe_hermSMul, Matrix.smul_apply, ← hf2 i j, smul_smul,
          inv_mul_cancel₀ (unifV_spec v).1, one_smul]
        exact (int_iff v b A.c hbc hcb _).2 (Fin.forall_fin_two.2 (hf1 i j))
      · apply Subtype.ext
        rw [coe_hermSMul, coe_hermSMul, smul_smul, mul_inv_cancel₀ (unifV_spec v).1, one_smul]
  have hset : latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
        {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0} =
      {Y | Y ∈ latSub b v a M ∧ (fun i p => rT (Y i p)) ∈
        {X | ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) X = (entL v A hD T hTi).map ρ}} := by
    ext Y
    show (Y ∈ latSub b v a M ∧ _) ↔ (Y ∈ latSub b v a M ∧ _)
    refine and_congr_right fun hY => ?_
    have hY' := (memL Y).1 hY
    show _ ∈ hF b v σ a 0 ↔ ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) (fun i p => rT (Y i p)) =
      (entL v A hD T hTi).map ρ
    rw [hFm, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    obtain ⟨hg1, hg2⟩ := hentry Y hY' i j
    have hTm := incl_mem v A hD _ (hTi i j)
    have e : ((gramH (Fv F v) σ hσ J hJ Y - hermOf (Fv F v) σ T hT : HermR (Fv F v) σ a) :
        Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
        (gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j -
          inclR (Fv F v) (T i j) := rfl
    rw [e, hsm' _ (sub_mem hg1 hTm), rT_sub _ _ hg1 hTm, sub_eq_zero, hg2, rT_eq _ hTm]
    exact Iff.rfl
  rw [hset, measure_count μ (latSub b v a M) (lamF b v a M 0) hNL hNm (fun Y i p => rT (Y i p))
    hadd hker hsurj]
  rfl

end Meas

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem cnt_at (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
    (hDu : Valued.v (algebraMap F (Fv F v) A.D0) = 1)
    (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
      (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
      IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧
      (∀ u : E, J.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit J'.det) ∧
      (∀ i j, σ' (T' j i) = T' i j) ∧
      (∀ u : E, T.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit T'.det) ∧
      Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
      μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
          μ (lamF b v a M 0) := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let fk : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have h2k := two_ne_zero_k v h2
  have hDk : red v (algebraMap F (Fv F v) A.D0) ≠ 0 := by
    rw [Ne, red_eq_zero_iff v hD, hDu]; exact lt_irrefl 1
  obtain ⟨K, iK, iA, σ', r, hQ, hr, hσr, hbij⟩ := exists_quadAlg (𝓞 F ⧸ v.asIdeal) h2k _ hDk
  have : Finite K := Finite.of_surjective _ hbij.2
  exact ⟨𝓞 F ⧸ v.asIdeal, K, fk, hfin, iK, iA, σ', (entL v A hD J hJi).map (rho v A hD r hr),
    (entL v A hD T hTi).map (rho v A hD r hr), hQ, h2k,
    cnt_herm v A hD r hr σ' hσr J hJ hJi, fun u hu hui => cnt_unit v A hD r hr J hJi u hu hui,
    cnt_herm v A hD r hr σ' hσr T hT hTi, fun u hu hui => cnt_unit v A hD r hr T hTi u hu hui, rfl,
    cnt_meas v A hD r hr σ' hσr hbij hσ J hJ T hT b hbc hcb hJi hTi hNm μ⟩

end Place

theorem cntAA_holds : CntAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨δ, D0, c, hδ0, hσδ, hδ, hD0, hc0, hc1⟩ := exists_basis_anti σ hCM
  let A : AntiB F E σ := ⟨δ, D0, c, hc0, hc1, hδ, hσδ, hD0⟩
  have hJdet : J.det ≠ 0 := hJ.2
  filter_upwards [ev_int (F := F) D0, ev_unit hD0, ev_unit (two_ne_zero : (2 : F) ≠ 0),
    eventually_all.2 fun j => eventually_all.2 fun k => ev_int (F := F) (b.repr (c j) k),
    eventually_all.2 fun k => eventually_all.2 fun j => ev_int (F := F) (c.repr (b k) j),
    eventually_all.2 fun p => eventually_all.2 fun q => eventually_all.2 fun j =>
      ev_int (F := F) (c.repr (J p q) j),
    eventually_all.2 fun p => eventually_all.2 fun q => eventually_all.2 fun j =>
      ev_int (F := F) (c.repr (gramE σ J X0 p q) j),
    eventually_all.2 fun j => ev_int (F := F) (c.repr (J.det)⁻¹ j),
    eventually_all.2 fun j => ev_int (F := F) (c.repr ((gramE σ J X0).det)⁻¹ j)]
    with v hD hDu h2 hbc hcb hJi hTi hJu hTu
  intro μ hμ
  haveI := hμ
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    ((latFacts_holds F E σ d b a M v).1 0).measurableSet
  obtain ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2k, hJ', hJu', hT', hTu', hcard, hmeas⟩ :=
    cnt_at v A (sigma_invol σ hCM.2.2.2) J hJ.1 (gramE σ J X0) hT b hbc hcb hD hDu h2 hJi hTi
      hNm μ
  exact ⟨k, K, i1, i2, i3, i4, σ', J', T', hQ, h2k, hJ', hJu' _ (mul_inv_cancel₀ hJdet) hJu, hT',
    hTu' _ (mul_inv_cancel₀ hdet) hTu, hcard, hmeas⟩

end PI.VolStabSW
end
end
