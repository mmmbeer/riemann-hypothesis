import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coord {ι : Type} (b : Module.Basis ι F E) (i : ι) : AE F E →ₗ[F] AF F :=
  (TensorProduct.lid F (AF F)).toLinearMap ∘ₗ LinearMap.rTensor (AF F) (b.coord i)

theorem coord_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (e : E) (a : AF F) :
    coord b i (e ⊗ₜ[F] a) = b.repr e i • a := by
  simp [coord, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply]

theorem sum_coord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (x : AE F E) :
    ∑ i, b i ⊗ₜ[F] coord b i x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp only [coord_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul,
      Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem coord_mul_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (x : AE F E) (a : AF F) :
    coord b i (x * ((1 : E) ⊗ₜ[F] a)) = coord b i x * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coord_tmul, coord_tmul, smul_mul_assoc]
  | add x y hx hy =>
    rw [add_mul, map_add, map_add, hx, hy, add_mul]

theorem continuous_coord {ι : Type} (b : Module.Basis ι F E) (i : ι) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (coord b i) := by
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  letI : Algebra (AF F) (AE F E) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let f : AE F E →ₗ[AF F] AF F :=
    { toFun := coord b i
      map_add' := map_add _
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [Algebra.smul_def, mul_comm,
          show algebraMap (AF F) (AE F E) r = (1 : E) ⊗ₜ[F] r from rfl, coord_mul_tmul, mul_comm] }
  exact IsModuleTopology.continuous_of_linearMap f

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incl_mem_SS {e : E} (he : e ∈ intOE E) : inclE (F := F) (AF F) e ∈ SS F E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem one_tmul_mem_SS {a : AF F} (ha : a ∈ intAd F) : (1 : E) ⊗ₜ[F] a ∈ SS F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem tmul_mem_SS {e : E} (he : e ∈ intOE E) {a : AF F} (ha : a ∈ intAd F) :
    e ⊗ₜ[F] a ∈ SS F E := by
  have h : e ⊗ₜ[F] a = (e ⊗ₜ[F] (1 : AF F)) * ((1 : E) ⊗ₜ[F] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact mul_mem (incl_mem_SS (F := F) he) (one_tmul_mem_SS ha)

theorem mem_SS_of_coord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (hb : ∀ i, b i ∈ intOE E)
    (x : AE F E) (hx : ∀ i, coord b i x ∈ intAd F) : x ∈ SS F E := by
  rw [← sum_coord b x]
  exact sum_mem fun i _ => tmul_mem_SS (hb i) (hx i)

theorem mul_mem_closure_tmul {y z : AE F E}
    (hy : y ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a})
    (hz : z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a}) :
    y * z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, a, ha, rfl⟩ := hy
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨e', he', a', ha', rfl⟩ := hz
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, mul_mem he he', _, mul_mem ha ha', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

theorem mem_closure_of_mem_SS {x : AE F E} (hx : x ∈ SS F E) :
    x ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨e, rfl⟩ | ⟨a, rfl⟩
    · exact AddSubgroup.subset_closure ⟨e, e.2, 1, one_mem _, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, a.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, rfl⟩
  | add y z _ _ hy hz => exact add_mem hy hz
  | neg y _ hy => exact neg_mem hy
  | mul y z _ _ hy hz => exact mul_mem_closure_tmul hy hz

theorem coord_mem_of_mem_SS {ι : Type} (b : Module.Basis ι F E) (D : 𝓞 F)
    (hD : ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range)
    {x : AE F E} (hx : x ∈ SS F E) (i : ι) : (D : F) • coord b i x ∈ intAd F := by
  have hx' := mem_closure_of_mem_SS hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, a, ha, rfl⟩ := hy
    obtain ⟨m, hm⟩ := hD e he i
    rw [coord_tmul, smul_smul, ← hm]
    exact smul_mem_intAd m ha
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [map_add, smul_add]; exact add_mem hu hv
  | neg u _ hu => rw [map_neg, smul_neg]; exact neg_mem hu

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E) (D : 𝓞 F), D ≠ 0 ∧ (∀ i, b i ∈ intOE E) ∧
      ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let β : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun j =>
    algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E j)
  have hspanQ : Submodule.span ℚ (Set.range β) = ⊤ := by
    have h := (NumberField.integralBasis E).span_eq
    have hr : Set.range (NumberField.integralBasis E) = Set.range β := by
      ext x
      simp [β, NumberField.integralBasis_apply]
    rw [hr] at h
    exact h
  have hspan : Submodule.span F (Set.range β) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range β) := by rw [hspanQ]; exact Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ F _ hx
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent F (Set.range β)
  have hBfin : B.Finite := (Set.finite_range β).subset hBsub
  haveI := hBfin.fintype
  let e := Fintype.equivFin B
  let b0 : Module.Basis B F E := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hspan])
  let b : Module.Basis (Fin (Fintype.card B)) F E := b0.reindex e
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    ((Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Fintype.card B))).image
      fun p => b.repr (β p.1) p.2)
  refine ⟨Fintype.card B, b, (D : 𝓞 F), nonZeroDivisors.ne_zero D.2, ?_, ?_⟩
  · intro i
    have hbi : b i = ((e.symm i : B) : E) := by simp [b, b0]
    obtain ⟨j, hj⟩ := hBsub (e.symm i).2
    rw [hbi, ← hj]
    exact RingHom.mem_range.mpr ⟨_, rfl⟩
  · intro x hx i
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
    have key : ∀ j, ((D : 𝓞 F) : F) * b.repr (β j) i ∈ (algebraMap (𝓞 F) F).range := by
      intro j
      obtain ⟨z, hz⟩ := hD (b.repr (β j) i) (Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩)
      refine RingHom.mem_range.mpr ⟨z, ?_⟩
      rw [hz, Algebra.smul_def]
    have hxe : algebraMap (𝓞 E) E y = ∑ j, ((NumberField.RingOfIntegers.basis E).repr y j) • β j := by
      conv_lhs => rw [← (NumberField.RingOfIntegers.basis E).sum_repr y]
      rw [map_sum]
      simp [β, map_zsmul]
    rw [hxe]
    simp only [map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
    exact Subring.sum_mem _ fun j _ => Subring.zsmul_mem _ (key j) _

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_basis_mem_intOE :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) F E, ∀ i, b i ∈ intOE E := by
  classical
  let c := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  have hyF : IsUnit ((y : ℤ) : F) := (Int.cast_ne_zero.mpr hy0).isUnit
  refine ⟨_, c.isUnitSMul (w := fun _ => ((y : ℤ) : F)) (fun _ => hyF), fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul F]
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr (hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i)))⟩, rfl⟩

private theorem exists_int_ne_zero_mul_repr_mem_range {n : ℕ} (b : Module.Basis (Fin n) F E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ e ∈ intOE E, ∀ i, (y : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let g := NumberField.RingOfIntegers.basis E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin n =>
      b.repr (algebraMap (𝓞 E) E (g p.1)) p.2))
  refine ⟨y, hy0, ?_⟩
  rintro _ ⟨z, rfl⟩ i
  have hz : algebraMap (𝓞 E) E z = ∑ j, g.repr z j • algebraMap (𝓞 E) E (g j) := by
    conv_lhs => rw [← g.sum_repr z]
    simp only [map_sum, map_zsmul]
  have key : (y : F) * b.repr (algebraMap (𝓞 E) E z) i
      = ∑ j, g.repr z j • ((y : F) * b.repr (algebraMap (𝓞 E) E (g j)) i) := by
    rw [hz, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, mul_smul_comm]
  rw [key]
  refine sum_mem fun j _ => zsmul_mem ?_ _
  have h2 : IsIntegral ℤ ((y : F) * b.repr (algebraMap (𝓞 E) E (g j)) i) := by
    have h := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))
    rw [zsmul_eq_mul] at h
    exact h
  exact ⟨⟨_, (mem_integralClosure_iff ℤ F).mpr h2⟩, rfl⟩

theorem exists_den_of_incl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ e : E, inclE (F := F) (AF F) e ∈ SS F E → (D : F) • e ∈ intOE E := by
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  obtain ⟨y, hy0, hy⟩ := exists_int_ne_zero_mul_repr_mem_range b
  have hyF : ((y : 𝓞 F) : F) = (y : F) := by
    rw [show ((y : 𝓞 F) : F) = algebraMap (𝓞 F) F (y : 𝓞 F) from rfl, map_intCast]
  refine ⟨(y : 𝓞 F), fun h => hy0 ?_, fun e he => ?_⟩
  · have h' := congrArg (algebraMap (𝓞 F) F) h
    rw [map_intCast, map_zero] at h'
    exact_mod_cast h'
  have hc : ∀ i, (y : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
    intro i
    have h := coord_mem_of_mem_SS b (y : 𝓞 F) (by rw [hyF]; exact hy) he i
    rw [hyF, show inclE (F := F) (AF F) e = e ⊗ₜ[F] (1 : AF F) from rfl, coord_tmul,
      smul_smul, ← Algebra.algebraMap_eq_smul_one] at h
    exact mem_range_of_mem_intAd _ h
  rw [hyF, ← b.sum_repr e, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [smul_smul]
  obtain ⟨r, hr⟩ := hc i
  rw [← hr, Algebra.smul_def]
  refine mul_mem ?_ (hb i)
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr ((r.isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F E))⟩, rfl⟩

theorem exists_den_of_isCompact :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (AE F E), IsCompact C → ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ C, (d : F) • x ∈ SS F E := by
  classical
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  have hsm : ∀ (r : 𝓞 F) (a : AF F), a ∈ intAd F → algebraMap (𝓞 F) F r • a ∈ intAd F := by
    intro r a ha
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem_intAd r) ha
  have pt : ∀ a : AF F, ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) F d • a ∈ intAd F := by
    intro a
    obtain ⟨u, hu⟩ := exists_sub_mem_intAd (F := F) a
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({u} : Finset F)
    have hyu : IsIntegral ℤ ((y : F) * u) := by
      have h := hy u (Finset.mem_singleton_self u)
      rw [zsmul_eq_mul] at h
      exact h
    let m : 𝓞 F := ⟨(y : F) * u, (mem_integralClosure_iff ℤ F).mpr hyu⟩
    have hm : algebraMap (𝓞 F) F m = (y : F) * u := rfl
    refine ⟨(y : 𝓞 F), fun h => hy0 ?_, ?_⟩
    · have h' := congrArg (algebraMap (𝓞 F) F) h
      rw [map_intCast, map_zero] at h'
      exact_mod_cast h'
    · have e : algebraMap (𝓞 F) F (y : 𝓞 F) • a
          = algebraMap F (AF F) (algebraMap (𝓞 F) F (y : 𝓞 F)) * (a - algebraMap F (AF F) u)
            + algebraMap F (AF F) (algebraMap (𝓞 F) F m) := by
        rw [hm, map_intCast, Algebra.smul_def, map_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (algebraMap_mem_intAd _) hu) (algebraMap_mem_intAd m)
  have den : ∀ K : Set (AF F), IsCompact K →
      ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K, algebraMap (𝓞 F) F d • a ∈ intAd F := by
    intro K hK
    choose dp hdp0 hdp using pt
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun a : AF F => (fun z => z - a) ⁻¹' (intAd F : Set (AF F)))
      (fun a => (isOpen_intAd (F := F)).preimage (continuous_id.sub continuous_const))
      (fun z _ => Set.mem_iUnion.mpr ⟨z, by
        show z - z ∈ intAd F
        rw [sub_self]
        exact zero_mem _⟩)
    refine ⟨∏ c ∈ t, dp c, Finset.prod_ne_zero_iff.mpr fun c _ => hdp0 c, fun z hz => ?_⟩
    have hz' := ht hz
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    rw [← Finset.mul_prod_erase t dp hct]
    have e : algebraMap (𝓞 F) F (dp c * ∏ c' ∈ t.erase c, dp c') • z
        = algebraMap (𝓞 F) F (dp c * ∏ c' ∈ t.erase c, dp c') • (z - c)
          + algebraMap (𝓞 F) F (∏ c' ∈ t.erase c, dp c') • (algebraMap (𝓞 F) F (dp c) • c) := by
      rw [map_mul, mul_comm]
      simp only [smul_sub, mul_smul]
      abel
    rw [e]
    exact add_mem (hsm _ _ hzc) (hsm _ _ (hdp c))
  have hK : ∀ i, IsCompact (coord b i '' C) := fun i => hC.image (continuous_coord b i)
  choose d hd0 hd using fun i => den _ (hK i)
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i, fun x hx => ?_⟩
  refine mem_SS_of_coord b hb _ fun i => ?_
  rw [map_smul, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
  show algebraMap (𝓞 F) F (d i * ∏ j ∈ Finset.univ.erase i, d j) • coord b i x ∈ intAd F
  rw [map_mul, mul_comm, mul_smul]
  exact hsm _ _ (hd i _ ⟨x, hx, rfl⟩)

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end
