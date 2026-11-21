import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SpansOverField
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesInhabited

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField Matrix
open scoped MatrixOrder

section Evaluations

variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def evalOn (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

def tensorCoord : Y →ₗ[ℤ] Y →ₗ[ℤ] (ι × ι → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y p => b.repr x p.1 * b.repr y p.2)
    (fun _ _ _ => by funext p; simp [add_mul]) (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add]) (fun _ _ _ => by funext p; simp [mul_left_comm])

theorem evalOn_tensorCoord (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change ∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Evaluations

theorem exists_eq_sum_eval : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)), (∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ a b c d : Y, (∀ β ∈ S, β a b = β c d) → γ a b = γ c d) → γ ∈ S) → ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) → ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i) := by
  intro Y _ _ _ S hS l hl
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let A : Submodule ℤ (_ × _ → ℤ) := ⨅ β : S, LinearMap.ker (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
  have hA : ∀ n, n ∈ A ↔ ∀ β : S, evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0 := fun n => by
    simp [A, Submodule.mem_iInf]
  have : NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A) := by
    refine ⟨fun {k q} h => ?_⟩
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hA] at h
    rw [Submodule.Quotient.mk_eq_zero, hA]
    intro β
    have h1 := h β
    rw [map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hk)
  have : Module.Free ℤ ((_ × _ → ℤ) ⧸ A) := Module.free_of_finite_type_torsion_free'
  let eb := Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)
  let γ : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := fun k =>
    (tensorCoord b).compr₂ ((Int.castAddHom ℝ).toIntLinearMap ∘ₗ eb.coord k ∘ₗ A.mkQ)
  have hγ : ∀ k x y, γ k x y = (eb.repr (Submodule.Quotient.mk (tensorCoord b x y)) k : ℤ) :=
    fun _ _ _ => rfl
  have hγS : ∀ k, γ k ∈ S := fun k => hS _ fun x y x' y' h => by
    have e : Submodule.Quotient.mk (p := A) (tensorCoord b x y) =
        Submodule.Quotient.mk (tensorCoord b x' y') := (Submodule.Quotient.eq A).2 ((hA _).2 fun β => by
      rw [map_sub, evalOn_tensorCoord, evalOn_tensorCoord, h β β.2, sub_self])
    rw [hγ, hγ, e]
  choose z hz using fun k => hl ⟨γ k, hγS k⟩ fun x y => ⟨_, hγ k x y⟩
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm
  refine ⟨_, fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩
  have hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) =
      evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
    rw [e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2))]
    simp [evalOn, zsmul_eq_mul]
  rw [hR]
  let ψ := A.liftQ (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) (iInf_le _ β)
  have hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m := fun m =>
    Submodule.liftQ_apply _ _ _
  have hβ : β = ∑ k, ψ (eb k) • (⟨γ k, hγS k⟩ : S) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro x y
    rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, hγ, smul_eq_mul]
    rw [← evalOn_tensorCoord b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]
    conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (tensorCoord b x y))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  rw [congrArg l hβ, map_sum, ← hψ, hn, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hz, smul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]

theorem posSemidef_of_int {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 := hp y
    rw [hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
  have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact hq q

theorem posDef_of_int {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hd : M.det ≠ 0 := fun h => by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [h0] using hp v hv
  have h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_
    have : (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) =
        ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by simp [dotProduct, mulVec]
    rw [this]
    by_cases hx : x = 0
    · simp [hx]
    · exact_mod_cast (hp x hx).le
  refine ⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩
  rw [← Int.cast_det]
  exact_mod_cast hd

theorem sum_pos_of_tensor_pos : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by
  intro Y _ _ _ ι _ a c hs hp γ hγ h0 hne
  classical
  let b := Module.finBasis ℤ Y
  let M : Matrix _ _ ℤ := Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)
  have hM := (posDef_of_int M (fun p q => hs _ _) fun x hx => by
    have := hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by
      simpa [Finsupp.single_apply] using LinearMap.congr_fun h (b q))
    convert this using 1
    simp only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    ring).2
  let G : Matrix _ _ ℝ := Matrix.of fun p q => γ (b p) (b q)
  have hG : G.PosSemidef := posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by
    convert h0 (∑ p, x p • b p) using 1
    simp only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]; ring
  have htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace := by
    simp only [← evalOn_tensorCoord b γ]
    change ∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply,
      Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hCd : IsUnit C.det := by
    refine Ne.isUnit fun h => hM.det_pos.ne' ?_
    rw [hC, det_mul, h, mul_zero]
  have h1 := hG.mul_mul_conjTranspose_same C
  have h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i) := by
    rw [htr, hC, trace_mul_cycle, star_eq_conjTranspose]
  rw [← h2]
  refine lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_
  have h3 := h1.trace_eq_zero_iff.1 h.symm
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 hCd
  have h4 : G = 0 := by
    rwa [← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero] at h3
  exact b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q

theorem eq_zero_of_trace_mul (E : Type) [Field E] [NumberField E] {u : 𝓞 E}
    (h : ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * u) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) u).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hu)
  have h1 := h α
  rw [mul_comm, ← hα, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  exact mul_ne_zero (by exact_mod_cast hd.ne') hr h1

theorem exists_traceDual : ∀ (E : Type) [Field E] [NumberField E], ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (ω θ : ι → 𝓞 E), 0 < N ∧ ∑ s, θ s * ω s = (N : 𝓞 E) ∧ ∀ g : 𝓞 E →ₗ[ℤ] ℤ, ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = N * g α := by
  intro E _ _
  classical
  let ω := RingOfIntegers.basis E
  let d := (integralBasis E).traceDual
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨k, hk, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image d)
  let θ : _ → 𝓞 E := fun s => k • (⟨k • d s, hint _ (by simp)⟩ : 𝓞 E)
  have hN : (((k * k).toNat : ℕ) : ℤ) = k * k := Int.toNat_of_nonneg (mul_self_nonneg k)
  have hθ : ∀ s t, Algebra.trace ℤ (𝓞 E) (ω t * θ s) = if t = s then k * k else 0 := by
    intro s t
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_trace_int]
    have : ((ω t * θ s : 𝓞 E) : E) = k • k • (d s * integralBasis E t) := by
      change (ω t : E) * (k • k • d s) = _
      rw [integralBasis_apply, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [this, map_zsmul, map_zsmul, Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have h3 : ∀ (g : 𝓞 E →ₗ[ℤ] ℤ) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = k * k * g α := by
    intro g α
    have : (Algebra.trace ℤ (𝓞 E)) ∘ₗ LinearMap.mulRight ℤ (∑ s, g (ω s) • θ s) = (k * k) • g :=
      ω.ext fun t => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm,
          map_sum, map_smul, hθ, LinearMap.smul_apply, smul_eq_mul]
        simp [mul_comm]
    exact LinearMap.congr_fun this α
  refine ⟨(k * k).toNat, _, inferInstance, ω, θ, ?_, ?_, fun g α => by rw [hN, h3]⟩
  · have := mul_self_pos.2 hk
    omega
  · rw [← sub_eq_zero]
    refine eq_zero_of_trace_mul E fun α => ?_
    have h4 : ∀ s, Algebra.trace ℤ (𝓞 E) (α * (θ s * ω s)) = k * k * ω.repr (α * ω s) s := by
      intro s
      have := h3 (ω.coord s) (α * ω s)
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      rw [← this, mul_comm (θ s), mul_assoc]
    rw [mul_sub, map_sub, Finset.mul_sum, map_sum, mul_comm α (_ : 𝓞 E), ← nsmul_eq_mul, map_nsmul,
      nsmul_eq_mul, hN, Algebra.trace_eq_matrix_trace ω α]
    simp only [h4, Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Finset.mul_sum, sub_self]

end GlobalTheory.PointStepCompare
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (Bil leastExponent IsIntegralFn IsPositiveFn IsBalancedSpace evalSum)

section Lattice

variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

variable (X) in

def intTorsion : Submodule (𝓞 E) X where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ n • x = 0}
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add, mul_smul n m y, hy, mul_comm, mul_smul, hx, smul_zero, smul_zero, add_zero]
  zero_mem' := ⟨1, one_pos, smul_zero _⟩
  smul_mem' := by
    rintro c x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [smul_comm, hx, smul_zero]⟩

end Lattice

section Phi

variable (E : Type) [Field E] [NumberField E]

theorem trace_pos {u : 𝓞 E} (h : ∀ τ : E →+* ℂ, 0 < (τ (u : E)).re) :
    0 < Algebra.trace ℤ (𝓞 E) u := by
  have h1 := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := (u : E)))
  rw [← Algebra.coe_trace_int, Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (u : E)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact Finset.sum_pos (fun σ _ => h σ.toRingHom) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
  rw [← h1] at h2
  simpa using h2

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem smul_ne_zero_of_free [Module.Free ℤ X] {c : 𝓞 E} {x : X} (hc : c ≠ 0) (hx : x ≠ 0) :
    c • x ≠ 0 := by
  intro h
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hc)
  have : r • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul, h, smul_zero]
  exact hx ((smul_eq_zero.1 this).resolve_left hr)

theorem projective_of_free [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Projective (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Flat (𝓞 E) X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    exact smul_ne_zero_of_free E (nonZeroDivisors.coe_ne_zero c) hx hc
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable [IsCMField E]

theorem bar_bar (a : 𝓞 E) : bar E (bar E a) = a := by
  ext; simp [IsCMField.coe_ringOfIntegersComplexConj]

theorem emb_bar (τ : E →+* ℂ) (a : 𝓞 E) : τ (bar E a : E) = starRingEnd ℂ (τ (a : E)) :=
  IsCMField.complexEmbedding_complexConj E τ _

theorem trace_bar (a : 𝓞 E) : Algebra.trace ℤ (𝓞 E) (bar E a) = Algebra.trace ℤ (𝓞 E) a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.ringOfIntegersComplexConj E).restrictScalars ℤ) a

theorem sum_pos_of_isPosHerm [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} {x x' : Fin n → X}
    (hl : IsPosHerm E (outer E x x')) (γ : Bil X) (hγ : GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalanced E γ)
    (hp : ∀ a, 0 ≤ γ a a) (h0 : γ ≠ 0) : 0 < ∑ i, γ (x i) (x' i) := by
  obtain ⟨N, ι, _, ω, θ, hN, hsum, htr⟩ := exists_traceDual E
  have htr' : ∀ (f : X →ₗ[ℤ] ℤ) (a : X) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, f (ω s • a) • θ s) = N * f (α • a) := fun f a α =>
    htr (f ∘ₗ (LinearMap.toSpanSingleton (𝓞 E) X a).restrictScalars ℤ) α
  let up : (X →ₗ[ℤ] ℤ) → Module.Dual (𝓞 E) X := fun f =>
    { toFun := fun a => ∑ s, f (ω s • a) • θ s
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        rw [← sub_eq_zero]
        refine eq_zero_of_trace_mul E fun α => ?_
        rw [mul_sub, map_sub, htr', RingHom.id_apply, smul_eq_mul, ← mul_assoc, htr', mul_smul,
          sub_self] }
  have hup : ∀ f a, up f a = ∑ s, f (ω s • a) • θ s := fun _ _ => rfl
  have key : ∀ f g : X →ₗ[ℤ] ℤ, Algebra.trace ℤ (𝓞 E) (outer E x x' (up f) (up g)) =
      N * ∑ p : Fin n × ι, f (ω p.2 • x p.1) * g (bar E (θ p.2) • x' p.1) := by
    intro f g
    rw [outer, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hup f, Finset.sum_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e : θ s * bar E (up g (x' i)) = bar E (bar E (θ s) * up g (x' i)) := by
      conv_lhs => rw [← bar_bar E (θ s)]
      exact (map_mul (IsCMField.ringOfIntegersComplexConj E) _ _).symm
    rw [smul_mul_assoc, map_smul, e, trace_bar, hup g, htr', smul_eq_mul]
    ring
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h1 := sum_pos_of_tensor_pos X (Fin n × ι) (fun p => ω p.2 • x p.1) (fun p => bar E (θ p.2) • x' p.1)
    (fun f g => by
      apply mul_left_cancel₀ hN'.ne'
      rw [← key, ← key, hl.1 (up g) (up f), trace_bar])
    (fun f hf => by
      have hne : up f ≠ 0 := by
        intro h
        apply hf
        ext a
        have := htr' f a 1
        rw [← hup, h] at this
        simpa [hN.ne'] using this
      have := trace_pos E (hl.2 _ hne)
      rw [key] at this
      exact pos_of_mul_pos_right this hN'.le) γ hγ.1 hp h0
  have h2 : ∑ p : Fin n × ι, γ (ω p.2 • x p.1) (bar E (θ p.2) • x' p.1) =
      N * ∑ i, γ (x i) (x' i) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ s, γ (ω s • x i) (bar E (θ s) • x' i) = γ ((θ s * ω s) • x i) (x' i) := fun s => by
      rw [← hγ.2, mul_smul]
    simp only [this]
    rw [← LinearMap.sum_apply, ← map_sum, ← Finset.sum_smul, hsum, Nat.cast_smul_eq_nsmul, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul]
  rw [h2] at h1
  exact pos_of_mul_pos_right h1 (Nat.cast_nonneg N)

def rankOne (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) : Bil X :=
  LinearMap.mk₂ ℤ (fun a c => (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re)
    (fun a a' c => by simp [add_mul])
    (fun k a c => by simp [mul_assoc, mul_add])
    (fun a c c' => by simp [mul_add])
    (fun k a c => by simp [mul_add, mul_left_comm])

omit [IsCMField E] in
theorem rankOne_apply (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) (a c : X) :
    rankOne E η τ a c = (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re := rfl

theorem rankOne_balanced (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalanced E (rankOne E η τ) := by
  refine ⟨fun a c => by simp [rankOne_apply, mul_comm], fun e a c => ?_⟩
  rw [rankOne_apply, rankOne_apply, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  rw [map_mul, map_mul, emb_bar E τ e, map_mul, Complex.conj_conj]
  congr 1; ring

theorem outer_append {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) :
    outer E (Fin.append x x') (Fin.append x' x) η η' = outer E x x' η η' + outer E x' x η η' := by
  simp only [outer, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

omit [NumberField E] [IsCMField E] [Module (𝓞 E) X] in
theorem pairing_append (γ : Bil X) (hγ : ∀ a c, γ a c = γ c a) {n : ℕ} (x x' : Fin n → X) :
    pairing (fun a c => γ a c) (Fin.append x x') (Fin.append x' x) = ∑ i, γ (x i) (x' i) := by
  simp only [pairing, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rw [Finset.sum_congr rfl fun i _ => hγ (x' i) (x i)]
  ring

theorem bar_outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) :
    bar E (outer E x x' η η') = outer E x' x η' η := by
  have := bar_bar E
  simp only [outer, bar, map_sum, map_mul] at this ⊢
  simp only [this, mul_comm]

theorem re_outer {n : ℕ} (x x' : Fin n → X) (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) :
    (τ (outer E x x' η η : E)).re = ∑ i, rankOne E η τ (x i) (x' i) := by
  simp only [outer, rankOne_apply]
  push_cast
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← emb_bar]

variable {S : Submodule ℝ (Bil X)}

theorem isPosHerm_of_positive (hS : IsBalancedSpace E S) {n : ℕ} {x x' : Fin n → X}
    (h : ∀ γ : S, (∀ a, 0 ≤ (γ : Bil X) a a) → γ ≠ 0 → 0 < ∑ i, (γ : Bil X) (x i) (x' i)) :
    IsPosHerm E (outer E (Fin.append x x') (Fin.append x' x)) := by
  refine ⟨fun η η' => ?_, fun η hη τ => ?_⟩
  · rw [outer_append, outer_append, ← bar_outer E x' x η η', ← bar_outer E x x' η η', add_comm]
    exact (map_add (IsCMField.ringOfIntegersComplexConj E) _ _).symm
  · have h1 := pairing_append _ (rankOne_balanced E η τ).1 x x'
    have h2 := h ⟨_, (hS _).2 (rankOne_balanced E η τ)⟩
      (fun a => by
        show 0 ≤ rankOne E η τ a a
        rw [rankOne_apply, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _)
      (fun h0 => hη (LinearMap.ext fun a => by
        have : rankOne E η τ a a = 0 := congrArg (fun β : S => (β : Bil X) a a) h0
        rw [rankOne_apply, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_zero] at this
        simpa using this))
    rw [re_outer]
    simp only [pairing] at h1
    simp only at h2
    linarith

variable [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_exponent (hS : IsBalancedSpace E S) (l : S →ₗ[ℝ] ℝ) (hi : IsIntegralFn S l)
    (hp : IsPositiveFn S l) : ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧
      ∀ β : S, l β = pairing (fun a c => (β : Bil X) a c) x x' := by
  obtain ⟨m, x, x', hx⟩ := exists_eq_sum_eval X S (fun γ hγ => (hS γ).2
    ⟨fun a c => hγ _ _ _ _ fun β hβ => ((hS β).1 hβ).1 a c,
      fun e a c => hγ _ _ _ _ fun β hβ => ((hS β).1 hβ).2 e a c⟩) l hi
  exact ⟨_, _, _, isPosHerm_of_positive E hS fun γ h1 h2 => hx γ ▸ hp γ h1 h2,
    fun β => by rw [pairing_append _ ((hS _).1 β.2).1, hx]⟩

theorem exists_functional (hS : IsBalancedSpace E S) {w : 𝓞 E} (hw : w + bar E w = 1) {n : ℕ}
    {x x' : Fin n → X} (hl : IsPosHerm E (outer E x x')) :
    ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧
      ∀ β : S, l β = pairing (fun a c => (β : Bil X) a c) x x' := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have := projective_of_free E (X := X)
  have ho : outer E (Fin.append (fun i => w • x i) x') (Fin.append x' fun i => w • x i) =
      outer E x x' := by
    funext η η'
    have e1 : outer E (fun i => w • x i) x' η η' = w * outer E x x' η η' := by
      simp [outer, Finset.mul_sum, mul_assoc]
    have e2 : outer E (fun i => w • x i) x' η' η = w * outer E x x' η' η := by
      simp [outer, Finset.mul_sum, mul_assoc]
    rw [outer_append, ← bar_outer E (fun i => w • x i) x' η' η, e1, e2, hl.1 η η']
    have e3 : bar E (w * bar E (outer E x x' η η')) = bar E w * outer E x x' η η' := by
      conv_rhs => rw [← bar_bar E (outer E x x' η η')]
      exact map_mul (IsCMField.ringOfIntegersComplexConj E) _ _
    rw [e3, ← add_mul, hw, one_mul]
  have hv : ∀ β : S, evalSum S (fun i => w • x i) x' β =
      pairing (fun a c => (β : Bil X) a c) x x' := fun β => by
    rw [← pairing_eq_of_outer_eq E (β : Bil X) ((hS _).1 β.2).2 _ _ _ _ ho,
      pairing_append _ ((hS _).1 β.2).1]
    rfl
  refine ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum S _ _, fun γ h1 h2 => ?_, hv⟩
  rw [hv, pairing]
  exact half_pos (sum_pos_of_isPosHerm E hl _ ((hS _).1 γ.2) h1 fun h => h2 (Subtype.ext h))

theorem exists_admissible (hS : IsBalancedSpace E S) :
    ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l := by
  let b := Module.finBasis ℤ X
  refine ⟨evalSum S b b, GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum S _ _, fun γ h1 h2 => ?_⟩
  refine sum_pos_of_isPosHerm E ⟨fun η η' => (bar_outer E _ _ _ _).symm, fun η hη τ => ?_⟩ _
    ((hS _).1 γ.2) h1 fun h => h2 (Subtype.ext h)
  rw [re_outer]
  simp only [rankOne_apply, Complex.mul_conj, Complex.ofReal_re]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => hη ?_
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm
  have : η.restrictScalars ℤ = 0 := b.ext fun i => by simpa using hz i (Finset.mem_univ _)
  exact LinearMap.ext fun a => LinearMap.congr_fun this a

end Phi

abbrev FormSpaces : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)

abbrev FormValues (S : FormSpaces) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

def AreBalancedSpaces (S : FormSpaces) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), β ∈ S E cj Y ↔ (∀ a b, β a b = β b a) ∧
      ∀ c c' : 𝓞 E, (c' : E) = cj c → ∀ a b, β (c • a) b = β a (c' • b)

section Clauses

variable {S : FormSpaces} {φ : FormValues S}

theorem isBalancedSpace (hS : AreBalancedSpaces S) (E : Type) [Field E] [NumberField E] [IsCMField E]
    {cj : E → E} (hcj : ∀ c : 𝓞 E, (bar E c : E) = cj c) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    IsBalancedSpace E (S E cj Y) := by
  intro β
  rw [hS]
  refine and_congr Iff.rfl ⟨fun h c => h c _ (hcj c), fun h c c' hc => ?_⟩
  obtain rfl : c' = bar E c := RingOfIntegers.ext (hc.trans (hcj c).symm)
  exact h c

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)

end Clauses

end GlobalTheory.PointStepCompare
end
end
