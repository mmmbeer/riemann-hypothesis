import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHI
import ReciprocityTheory.Automorphisms.InstMainA
import ReciprocityTheory.ResidueCardinality.ArtinOntoB

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

def crdS (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) : Fv F v :=
  (Algebra.TensorProduct.basis (Fv F v) b).repr ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k

theorem mem_hermO_iff (S : HermR (Fv F v) σ a) :
    S ∈ hermO b v σ a ↔ ∀ i j k, crdS b v σ a S i j k ∈ v.adicCompletionIntegers F := Iff.rfl

theorem crdS_add (S T : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) :
    crdS b v σ a (S + T) i j k = crdS b v σ a S i j k + crdS b v σ a T i j k := by
  simp [crdS, Matrix.add_apply, map_add]

theorem crdS_smul (t : Fv F v) (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) :
    crdS b v σ a (t • S) i j k = t * crdS b v σ a S i j k := by
  simp only [crdS, coe_hermSMul, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]

def redH : (hermO b v σ a) →+
    (Fin a → Fin a → Fin d → ResidueField (v.adicCompletionIntegers F)) where
  toFun S i j k := residue _ ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩
  map_zero' := by
    funext i j k
    have : crdS b v σ a (0 : HermR (Fv F v) σ a) i j k = 0 := by simp [crdS]
    simp only [ZeroMemClass.coe_zero, this, Pi.zero_apply]
    rw [show (⟨0, _⟩ : v.adicCompletionIntegers F) = 0 from rfl, map_zero]
  map_add' S T := by
    funext i j k
    simp only [Pi.add_apply, ← map_add]
    congr 1
    ext
    simp [crdS_add]

theorem unifV_ne_zero : unifV v ≠ 0 := by
  intro h
  have := unifV_val v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem val_of_res (x : v.adicCompletionIntegers F) (h : residue _ x = 0) :
    Valued.v (x : Fv F v) ≤ WithZero.exp (-1 : ℤ) :=
  ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v
    ((ReciprocityTheory.Aut.mem_maxIdeal_iff v x).1 ((residue_eq_zero_iff x).1 h))

theorem res_of_val (x : v.adicCompletionIntegers F) (h : Valued.v (x : Fv F v) < 1) :
    residue _ x = 0 :=
  (residue_eq_zero_iff x).2 ((ReciprocityTheory.Aut.mem_maxIdeal_iff v x).2 h)

theorem ker_redH :
    (redH b v σ a).ker = (hF b v σ a 0).addSubgroupOf (hermO b v σ a) := by
  ext S
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  have hπ := unifV_val v
  have hπ0 := unifV_ne_zero v
  constructor
  · intro h
    have hc : ∀ i j k, Valued.v (crdS b v σ a S i j k) ≤ WithZero.exp (-1 : ℤ) := by
      intro i j k
      have h1 : residue _ (⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ :
          v.adicCompletionIntegers F) = 0 := congrFun (congrFun (congrFun h i) j) k
      have h2 := val_of_res v _ h1
      exact h2
    refine (mem_smulSub _ _ _).2 ⟨(unifV v)⁻¹ • (S : HermR (Fv F v) σ a), ?_, ?_⟩
    · refine (mem_hermO_iff b v σ a _).2 fun i j k => ?_
      rw [crdS_smul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hπ]
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v (crdS b v σ a S i j k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := mul_le_mul_right (hc i j k) _
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [zero_add, pow_one, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
  · intro h
    obtain ⟨p, hp, hpS⟩ := (mem_smulSub _ _ _).1 h
    funext i j k
    have hlt : Valued.v (crdS b v σ a S i j k) < 1 := by
      rw [← hpS, zero_add, pow_one, crdS_smul, map_mul, hπ]
      have hp1 : Valued.v (crdS b v σ a p i j k) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_hermO_iff b v σ a p).1 hp i j k)
      calc WithZero.exp (-1 : ℤ) * Valued.v (crdS b v σ a p i j k) ≤ WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul_right hp1 _
        _ < 1 := by
          rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
          norm_num
    have h3 := res_of_val v ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ hlt
    exact h3

end IdxHW

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace IdxHW

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

theorem crd_sigR (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (sigR (Fv F v) σ y) k =
      ∑ l, algebraMap F (Fv F v) (b.repr (σ (b l)) k) *
        (Algebra.TensorProduct.basis (Fv F v) b).repr y l := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [sigR, Algebra.TensorProduct.map_tmul]
    rw [hs]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    have he : σ e = ∑ l, b.repr e l • σ (b l) := by
      have h := congrArg σ (b.sum_repr e)
      rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    rw [he, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add]
    simp only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem eventually_int (x : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).eventually

end IdxHW

theorem fix2 {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, (C - 1) r 0 ≠ 0 ∨ (C - 1) r 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hC
    have : C - 1 = 0 := by
      ext i j
      fin_cases j
      · exact (h i).1
      · exact (h i).2
    exact sub_eq_zero.1 this
  have hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
        algebraMap F K ((C - 1) r 0) * x 0 + algebraMap F K ((C - 1) r 1) * x 1 = 0 := by
    intro K _ _ x hx
    have h := congrFun hx r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at h
    simp only [Matrix.sub_apply, Matrix.one_apply, map_sub]
    fin_cases r <;> simp at h ⊢ <;> linear_combination h
  have hrowu := hrow F u (by simpa using hCu)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hrowu
  by_cases hβ : (C - 1) r 1 ≠ 0
  · refine ⟨0, 1, by decide, ?_, -((C - 1) r 0) / (C - 1) r 1, fun K _ _ x hx => ?_⟩
    · intro h0
      apply hu
      have h1 : u 1 = 0 := by
        rw [h0, mul_zero, zero_add] at hrowu
        exact (mul_eq_zero.1 hrowu).resolve_left hβ
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · have h := hrow K x hx
      have hβK : algebraMap F K ((C - 1) r 1) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hβ
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  · push Not at hβ
    have hα : (C - 1) r 0 ≠ 0 := hr.resolve_right (by rw [hβ]; exact fun h => h rfl)
    have hu0 : u 0 = 0 := by
      rw [hβ, zero_mul, add_zero] at hrowu
      exact (mul_eq_zero.1 hrowu).resolve_left hα
    refine ⟨1, 0, by decide, ?_, 0, fun K _ _ x hx => ?_⟩
    · intro h1
      apply hu
      ext i
      fin_cases i
      · exact hu0
      · exact h1
    · have h := hrow K x hx
      rw [hβ, map_zero, zero_mul, add_zero] at h
      have hαK : algebraMap F K ((C - 1) r 0) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hα
      rw [map_zero, zero_mul]
      exact (mul_eq_zero.1 h).resolve_left hαK

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

theorem sigma_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra h
  push Not at h
  have hc := hCM.2.1
  let w : InfinitePlace E := Classical.arbitrary _
  have hcw : w.IsComplex := hc.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hcw
  rw [InfinitePlace.isReal_iff]
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have h1 := hCM.2.2.2 w.embedding x
  rw [h x] at h1
  exact h1.symm

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

def Cmat : Matrix (Fin 2) (Fin 2) F := fun k l => b.repr (σ (b l)) k

def cr (y : Fv F v ⊗[F] E) (k : Fin 2) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) b).repr y k

theorem cr_sig (y : Fv F v ⊗[F] E) (k : Fin 2) :
    cr b v (sigR (Fv F v) σ y) k = ∑ l, algebraMap F (Fv F v) (Cmat b σ k l) * cr b v y l :=
  crd_sigR b v σ y k

theorem cr_smul_one (t : Fv F v) (k : Fin 2) :
    cr b v (t • (1 : Fv F v ⊗[F] E)) k = t * algebraMap F (Fv F v) (b.repr 1 k) := by
  simp [cr, Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul, map_smul]

theorem cr_symm (f : Fin 2 → Fv F v) (k : Fin 2) :
    cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k = f k := by
  have : cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k =
      (Algebra.TensorProduct.basis (Fv F v) b).equivFun
        ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k := by
    simp [cr, Module.Basis.equivFun_apply]
  rw [this, LinearEquiv.apply_symm_apply]

theorem crdS_eq (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin 2) :
    crdS b v σ a S i j k = cr b v ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k := rfl

def psi (k0 : Fin 2) : hermO b v σ a →+ (Fin a × Fin a → v.adicCompletionIntegers F) where
  toFun S q := if q.1 < q.2 then ⟨crdS b v σ a S q.1 q.2 0, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
    else if q.2 < q.1 then ⟨crdS b v σ a S q.2 q.1 1, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
    else ⟨crdS b v σ a S q.1 q.1 k0, (mem_hermO_iff b v σ a S).1 S.2 _ _ _⟩
  map_zero' := by
    funext q
    split_ifs <;> ext <;> simp [crdS]
  map_add' S T := by
    funext q
    simp only [Pi.add_apply]
    by_cases h1 : q.1 < q.2
    · simp only [if_pos h1]
      ext
      simp [crdS_add]
    · by_cases h2 : q.2 < q.1
      · simp only [if_neg h1, if_pos h2]
        ext
        simp [crdS_add]
      · simp only [if_neg h1, if_neg h2]
        ext
        simp [crdS_add]

end Main

end IdxHW

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem psi_surj (k0 : Fin 2) (hσ : ∀ x, σ (σ x) = x)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hu : ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F)
    (hk0 : b.repr 1 k0 ≠ 0) : Function.Surjective (psi b v σ a k0) := by
  classical
  intro z
  let T : Fv F v → Fv F v → Fv F v ⊗[F] E := fun p q =>
    (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm ![p, q]
  have cT : ∀ p q k, cr b v (T p q) k = ![p, q] k := fun p q k => cr_symm b v _ k
  have hu0 : algebraMap F (Fv F v) (b.repr 1 k0) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]; exact hk0
  let t : Fin a → Fv F v := fun i => (z (i, i) : Fv F v) * (algebraMap F (Fv F v) (b.repr 1 k0))⁻¹
  let Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then T (z (i, j)) (z (j, i))
    else if j < i then sigR (Fv F v) σ (T (z (j, i)) (z (i, j))) else t i • 1
  have hY : Y ∈ HermR (Fv F v) σ a := by
    intro i j
    show sigR (Fv F v) σ (Y j i) = Y i j
    rcases lt_trichotomy i j with h | h | h
    · simp only [Y, if_pos h, if_neg (not_lt.2 h.le)]
      exact sigR_invol (Fv F v) σ hσ _
    · subst h
      simp only [Y, lt_irrefl, if_false]
      rw [Algebra.smul_def, mul_one, sigR_algebraMap]
    · simp only [Y, if_pos h, if_neg (not_lt.2 h.le)]
  let S : HermR (Fv F v) σ a := ⟨Y, hY⟩
  have hSY : ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Y i j := fun _ _ => rfl
  have hSO : S ∈ hermO b v σ a := by
    refine (mem_hermO_iff b v σ a S).2 fun i j k => ?_
    rw [crdS_eq, hSY]
    rcases lt_trichotomy i j with h | h | h
    · simp only [Y, if_pos h, cT]
      fin_cases k
      · exact (z (i, j)).2
      · exact (z (j, i)).2
    · subst h
      simp only [Y, lt_irrefl, if_false, cr_smul_one]
      have e : t i * algebraMap F (Fv F v) (b.repr 1 k) =
          (z (i, i) : Fv F v) * algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) := by
        simp only [t, map_div₀]
        field_simp
      rw [e]
      exact mul_mem (z (i, i)).2 (hu k)
    · simp only [Y, if_neg (not_lt.2 h.le), if_pos h, cr_sig, Fin.sum_univ_two, cT]
      refine add_mem (mul_mem (hC _ _) ?_) (mul_mem (hC _ _) ?_)
      · exact (z (j, i)).2
      · exact (z (i, j)).2
  refine ⟨⟨S, hSO⟩, ?_⟩
  funext q
  obtain ⟨i, j⟩ := q
  apply Subtype.ext
  rcases lt_trichotomy i j with h | h | h
  · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos h, crdS_eq, hSY]
    simp only [Y, if_pos h, cT]
    rfl
  · subst h
    simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false, crdS_eq, hSY]
    simp only [Y, lt_irrefl, if_false, cr_smul_one, t]
    rw [inv_mul_cancel_right₀ hu0]
  · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 h.le), if_pos h,
      crdS_eq, hSY]
    simp only [Y, if_pos h, cT]
    rfl

end Surj

end IdxHW

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Comap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem val_mul_lt {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (hy : Valued.v y < 1) :
    Valued.v (x * y) < 1 := by
  rw [map_mul]
  have hx' : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hx') hy

theorem comap_eq (k0 k1 : Fin 2) (hk : k0 ≠ k1) (ρ : F)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hρ : algebraMap F (Fv F v) ρ ∈ v.adicCompletionIntegers F)
    (hfix : ∀ x : Fin 2 → Fv F v,
      Matrix.mulVec ((Cmat b σ).map (algebraMap F (Fv F v))) x = x →
        x k1 = algebraMap F (Fv F v) ρ * x k0) :
    (hF b v σ a 0).addSubgroupOf (hermO b v σ a) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin a =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (psi b v σ a k0) := by
  rw [← ker_redH]
  ext S
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  have key : redH b v σ a S = 0 ↔ ∀ i j k, Valued.v (crdS b v σ a S i j k) < 1 := by
    constructor
    · intro h i j k
      have h1 : residue _ (⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ :
          v.adicCompletionIntegers F) = 0 := congrFun (congrFun (congrFun h i) j) k
      have h2 := (ReciprocityTheory.Aut.mem_maxIdeal_iff v _).1 ((residue_eq_zero_iff _).1 h1)
      exact h2
    · intro h
      funext i j k
      have h3 := res_of_val v ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ (h i j k)
      exact h3
  rw [key]
  set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
    ((S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) with hSm
  have hps : ∀ q, psi b v σ a k0 S q ∈ (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup ↔
      Valued.v ((psi b v σ a k0 S q : v.adicCompletionIntegers F) : Fv F v) < 1 :=
    fun q => ReciprocityTheory.Aut.mem_maxIdeal_iff v _
  constructor
  · intro h q _
    rw [hps]
    obtain ⟨i, j⟩ := q
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hij]
      exact h i j 0
    · subst hij
      simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false]
      exact h i i k0
    · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 hij.le), if_pos hij]
      exact h j i 1
  · intro h
    have h' : ∀ q, Valued.v ((psi b v σ a k0 S q : v.adicCompletionIntegers F) : Fv F v) < 1 :=
      fun q => (hps q).1 (h q (Set.mem_univ q))
    have hup : ∀ i j, i < j → ∀ k, Valued.v (crdS b v σ a S i j k) < 1 := by
      intro i j hij k
      fin_cases k
      · have := h' (i, j)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hij] at this
        exact this
      · have := h' (j, i)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 hij.le),
          if_pos hij] at this
        exact this
    intro i j k
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hup i j hij k
    · subst hij
      have hd : Valued.v (crdS b v σ a S i i k0) < 1 := by
        have := h' (i, i)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false] at this
        exact this
      have hfx := hfix (fun l => crdS b v σ a S i i l) (by
        funext m
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        have hs : sigR (Fv F v) σ (Sm i i) = Sm i i := S.1.2 i i
        have := cr_sig b v σ (Sm i i) m
        rw [hs] at this
        simp only [crdS_eq]
        exact this.symm)
      have hkk : k = k0 ∨ k = k1 := by
        fin_cases k <;> fin_cases k0 <;> fin_cases k1 <;> simp_all
      rcases hkk with rfl | rfl
      · exact hd
      · have e : crdS b v σ a S i i k = algebraMap F (Fv F v) ρ * crdS b v σ a S i i k0 := hfx
        rw [e]
        exact val_mul_lt v hρ hd
    · have hs : Sm i j = sigR (Fv F v) σ (Sm j i) := (S.1.2 i j).symm
      rw [crdS_eq, show ((S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Sm i j
        from rfl, hs, cr_sig, Fin.sum_univ_two]
      refine Valuation.map_add_lt _ (val_mul_lt v (hC _ _) ?_) (val_mul_lt v (hC _ _) ?_)
      · exact hup j i hij 0
      · exact hup j i hij 1

end Comap

theorem index_max {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

end IdxHW

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing IdxHW

theorem idxH_holds : IdxH := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  subst hd
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let u : Fin 2 → F := fun k => b.repr 1 k
  have hC1 : Cmat b σ ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := sigma_ne_id σ hCM
    apply hx
    have hb : ∀ l, σ (b l) = b l := fun l => by
      apply b.repr.injective
      ext k
      have := congrFun (congrFun h k) l
      simp only [Cmat] at this
      rw [this, b.repr_self, Matrix.one_apply, Finsupp.single_apply]
      by_cases hkl : k = l
      · subst hkl; simp
      · simp [hkl, Ne.symm hkl]
    have : σ.toLinearMap = LinearMap.id := b.ext fun l => by simp [hb l]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hu : u ≠ 0 := by
    intro h
    apply one_ne_zero (α := E)
    apply b.repr.injective
    ext k
    simpa [u] using congrFun h k
  have hCu : Matrix.mulVec (Cmat b σ) u = u := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Cmat, u]
    have h1 : σ 1 = 1 := map_one σ
    have h2 : (1 : E) = ∑ l, b.repr 1 l • b l := (b.sum_repr 1).symm
    have h3 : σ 1 = ∑ l, b.repr 1 l • σ (b l) := by
      rw [show σ 1 = σ (∑ l, b.repr 1 l • b l) from by rw [b.sum_repr], map_sum]
      exact Finset.sum_congr rfl fun l _ => σ.toLinearMap.map_smul _ _
    have := congrArg (fun y => b.repr y k) h3
    simp only [h1, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  obtain ⟨k0, k1, hk, hk0, ρ, hfix⟩ := fix2 (Cmat b σ) hC1 u hu hCu
  filter_upwards [eventually_all.2 fun k => eventually_all.2 fun l => eventually_int (Cmat b σ k l),
    eventually_all.2 fun k => eventually_int (u k / u k0), eventually_int ρ] with v hC hu' hρ
  unfold AddSubgroup.relIndex
  rw [comap_eq b v σ a k0 k1 hk ρ hC hρ (fun x hx => hfix (Fv F v) x hx),
    AddSubgroup.index_comap_of_surjective _ (psi_surj b v σ a k0 hσ hC hu' hk0),
    AddSubgroup.index_pi]
  simp only [index_max, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  ring

end PI.VolStabW
end
end
