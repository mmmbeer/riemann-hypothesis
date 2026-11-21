import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHI
import ReciprocityTheory.Automorphisms.InstMainA
import ReciprocityTheory.ResidueCardinality.ArtinOntoB

section
noncomputable section

namespace PI.VolStabS

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

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

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
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  filter_upwards [(IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x).compl_mem_cofinite] with v hv
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hv' : v.valuation F x ≤ 1 := by
    simpa [IsDedekindDomain.HeightOneSpectrum.Support] using hv
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).le.trans hv'

end IdxHW

theorem fix2 {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by
  obtain ⟨i, hi⟩ : ∃ i, (C - 1) i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hC
    ext a c
    have := congrFun (h a) c
    simpa [sub_eq_zero] using this
  have hab : (C - 1) i 0 ≠ 0 ∨ (C - 1) i 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hi
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  have hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
      algebraMap F K ((C - 1) i 0) * x 0 + algebraMap F K ((C - 1) i 1) * x 1 = 0 := by
    intro K _ _ x hx
    have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at this
    fin_cases i <;> simp [Matrix.sub_apply, Matrix.one_apply] at this ⊢ <;> linear_combination this
  have key : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
      x 0 * algebraMap F K (u 1) = x 1 * algebraMap F K (u 0) := by
    intro K _ _ x hx
    have E1 := hrow K x hx
    have E2 : algebraMap F K ((C - 1) i 0) * algebraMap F K (u 0) +
        algebraMap F K ((C - 1) i 1) * algebraMap F K (u 1) = 0 := by
      have := hrow F u (by simpa using hCu)
      have := congrArg (algebraMap F K) this
      simpa [map_add, map_mul] using this
    rcases hab with ha | hb
    · have hA : algebraMap F K ((C - 1) i 0) ≠ 0 := (map_ne_zero _).2 ha
      apply mul_left_cancel₀ hA
      linear_combination algebraMap F K (u 1) * E1 - x 1 * E2
    · have hB : algebraMap F K ((C - 1) i 1) ≠ 0 := (map_ne_zero _).2 hb
      apply mul_left_cancel₀ hB
      linear_combination x 0 * E2 - algebraMap F K (u 0) * E1
  by_cases hu0 : u 0 ≠ 0
  · refine ⟨0, 1, by decide, hu0, u 1 / u 0, fun K _ _ x hx => ?_⟩
    have h1 := key K x hx
    have hu0' : algebraMap F K (u 0) ≠ 0 := (map_ne_zero _).2 hu0
    rw [map_div₀]
    field_simp
    linear_combination -h1
  · push_neg at hu0
    have hu1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      funext j
      fin_cases j
      · exact hu0
      · exact h1
    refine ⟨1, 0, by decide, hu1, u 0 / u 1, fun K _ _ x hx => ?_⟩
    have h1 := key K x hx
    have hu1' : algebraMap F K (u 1) ≠ 0 := (map_ne_zero _).2 hu1
    rw [map_div₀]
    field_simp
    linear_combination h1

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

theorem sigma_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  obtain ⟨-, hC, -, hst⟩ := hCM
  by_contra h
  push_neg at h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have hw : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := hst w.embedding x
    rw [h x] at this
    simp only [ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex w)) hw

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
  simp [cr, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', Algebra.TensorProduct.basis_repr_tmul]

theorem cr_symm (f : Fin 2 → Fv F v) (k : Fin 2) :
    cr b v ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm f) k = f k := by
  unfold cr
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

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

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

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
  intro g
  have hinv : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  set u : Fv F v := algebraMap F (Fv F v) (b.repr 1 k0) with hu_def
  have hu0 : u ≠ 0 := (map_ne_zero (algebraMap F (Fv F v))).mpr hk0
  let Y : Fin a → Fin a → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm ![(g (i, j) : Fv F v), (g (j, i) : Fv F v)]
  let D : Fin a → Fv F v ⊗[F] E := fun i => ((g (i, i) : Fv F v) / u) • (1 : Fv F v ⊗[F] E)
  let M : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then Y i j else if j < i then sigR (Fv F v) σ (Y j i) else D i
  have hD : ∀ i, sigR (Fv F v) σ (D i) = D i := by
    intro i
    simp [D, sigR, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have hY : ∀ i j k, cr b v (Y i j) k = ![(g (i, j) : Fv F v), (g (j, i) : Fv F v)] k :=
    fun i j k => cr_symm b v _ k
  have hDk : ∀ i k, cr b v (D i) k = (g (i, i) : Fv F v) / u * algebraMap F (Fv F v) (b.repr 1 k) :=
    fun i k => cr_smul_one b v _ k
  have hM : M ∈ HermR (Fv F v) σ a := by
    show ∀ i j, sigR (Fv F v) σ (M j i) = M i j
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [M, h, lt_asymm h, hinv]
    · simp [M, hD]
    · simp [M, h, lt_asymm h]
  have hO : (⟨M, hM⟩ : HermR (Fv F v) σ a) ∈ hermO b v σ a := by
    rw [mem_hermO_iff]
    intro i j k
    rw [crdS_eq]
    show cr b v (M i j) k ∈ _
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [M, if_pos h]
      rw [hY]
      fin_cases k <;> simp
    · simp only [M, lt_irrefl, if_false]
      rw [hDk]
      have e : (g (i, i) : Fv F v) / u * algebraMap F (Fv F v) (b.repr 1 k)
          = (g (i, i) : Fv F v) * algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) := by
        rw [map_div₀, ← hu_def]
        ring
      rw [e]
      exact mul_mem (g _).2 (hu k)
    · simp only [M, if_neg (lt_asymm h), if_pos h]
      rw [cr_sig]
      refine sum_mem fun l _ => mul_mem (hC k l) ?_
      rw [hY]
      fin_cases l <;> simp
  refine ⟨⟨⟨M, hM⟩, hO⟩, ?_⟩
  funext q
  obtain ⟨i, j⟩ := q
  simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h1 h2
  · apply Subtype.ext
    show cr b v (M i j) 0 = _
    simp only [M, if_pos h1]
    rw [hY]
    simp
  · apply Subtype.ext
    show cr b v (M j i) 1 = _
    simp only [M, if_pos h2]
    rw [hY]
    simp
  · have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    subst hij
    apply Subtype.ext
    show cr b v (M i i) k0 = _
    simp only [M, lt_irrefl, if_false]
    rw [hDk, ← hu_def]
    exact div_mul_cancel₀ _ hu0

end Surj

end IdxHW

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Comap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem val_mul_lt {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (hy : Valued.v y < 1) :
    Valued.v (x * y) < 1 := by
  have hx' : Valued.v x ≤ 1 := hx
  calc Valued.v (x * y) = Valued.v x * Valued.v y := map_mul _ _ _
    _ ≤ 1 * Valued.v y := by gcongr
    _ = Valued.v y := one_mul _
    _ < 1 := hy

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

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing IdxHW

theorem idxH_holds : IdxH := by
  unfold IdxH
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ _ d b
  obtain ⟨-, -, hrank, hstar⟩ := id hCM
  have hd : d = 2 := by rw [← hrank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd

  have hσ : ∀ x, σ (σ x) = x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro x
    apply τ.injective
    rw [hstar, hstar, star_star]

  obtain ⟨x0, hx0⟩ := IdxHW.sigma_ne_id σ hCM
  have hC1 : IdxHW.Cmat b σ ≠ 1 := by
    intro hC
    apply hx0
    have hb : ∀ l, σ (b l) = b l := by
      intro l
      apply b.repr.injective
      ext k
      have hkl := congrFun (congrFun hC k) l
      simp only [IdxHW.Cmat] at hkl
      rw [hkl, b.repr_self, Matrix.one_apply, Finsupp.single_apply]
      by_cases h : k = l
      · subst h
        simp
      · simp [h, Ne.symm h]
    conv_lhs => rw [← b.sum_repr x0]
    rw [map_sum]
    conv_rhs => rw [← b.sum_repr x0]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.map_smul_of_tower, hb]

  have hu0 : (fun k => b.repr 1 k) ≠ 0 := by
    intro h
    have h1 : b.repr (1 : E) = 0 := by
      ext k
      exact congrFun h k
    exact one_ne_zero (b.repr.injective (h1.trans (map_zero b.repr).symm))
  have hCu : (IdxHW.Cmat b σ).mulVec (fun k => b.repr 1 k) = fun k => b.repr 1 k := by
    funext k
    simp only [Matrix.mulVec, dotProduct, IdxHW.Cmat]
    have e : σ 1 = ∑ l, b.repr 1 l • σ (b l) := by
      conv_lhs => rw [← b.sum_repr 1]
      rw [map_sum]
      simp only [AlgHom.map_smul_of_tower]
    rw [map_one] at e
    conv_rhs => rw [e]
    simp [mul_comm]
  obtain ⟨k0, k1, hk, hk0, ρ, hρfix⟩ := fix2 (IdxHW.Cmat b σ) hC1 _ hu0 hCu

  have hev : ∀ᶠ v in cofinite,
      (∀ k l, algebraMap F (Fv F v) (IdxHW.Cmat b σ k l) ∈ v.adicCompletionIntegers F) ∧
      algebraMap F (Fv F v) ρ ∈ v.adicCompletionIntegers F ∧
      ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => IdxHW.eventually_int _).and
      ((IdxHW.eventually_int ρ).and (Filter.eventually_all.2 fun k => IdxHW.eventually_int _))
  filter_upwards [hev] with v hv
  obtain ⟨hC, hρ, hu⟩ := hv
  have hfix : ∀ x : Fin 2 → Fv F v,
      Matrix.mulVec ((IdxHW.Cmat b σ).map (algebraMap F (Fv F v))) x = x →
        x k1 = algebraMap F (Fv F v) ρ * x k0 := hρfix (Fv F v)
  rw [AddSubgroup.relIndex, IdxHW.comap_eq b v σ a k0 k1 hk ρ hC hρ hfix,
    AddSubgroup.index_comap_of_surjective _ (IdxHW.psi_surj b v σ a k0 hσ hC hu hk0),
    AddSubgroup.index_pi, Finset.prod_const, IdxHW.index_max v]
  simp [sq]

end PI.VolStabS
end
end
