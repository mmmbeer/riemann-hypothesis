import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.AdjointLiftFromEisensteinSeedOfHyps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.EGCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.OrdExT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVROrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistRealSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.NeZeroRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharPolOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.SeedInW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TUpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpSol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWToCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemLevelOfLocalDepth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.toIsDomain
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix
namespace UpperTheory.V.Sd
section CongLemmas
variable {l : ℕ} [Fact l.Prime]
private theorem cong_refl (a : (Qbar l)ˣ) : Cong a a := by simp [Cong]
private theorem cong_symm {a b : (Qbar l)ˣ} (h : Cong a b) : Cong b a := by
  unfold Cong at *; rwa [norm_sub_rev]
private theorem cong_trans {a b c : (Qbar l)ˣ} (h : Cong a b) (h' : Cong b c) : Cong a c := by
  unfold Cong at *
  have := IsUltrametricDist.norm_add_le_max ((a : Qbar l) - b) ((b : Qbar l) - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')
private theorem cong_norm {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  unfold Cong at h
  have := IsUltrametricDist.norm_eq_of_add_norm_lt_max (x := (a : Qbar l)) (y := -(b : Qbar l))
    (by rw [← sub_eq_add_neg, norm_neg, hb]; exact h.trans_le (le_max_right _ _))
  rw [this, norm_neg, hb]
private theorem cong_mul_right {a b : (Qbar l)ˣ} (h : Cong a b) (c : (Qbar l)ˣ) (hc : ‖(c : Qbar l)‖ = 1) :
    Cong (a * c) (b * c) := by
  unfold Cong at *
  rw [Units.val_mul, Units.val_mul, ← sub_mul, norm_mul, hc, mul_one]
  exact h
private theorem cong_mul {a b c d : (Qbar l)ˣ} (h : Cong a b) (h' : Cong c d) (hb : ‖(b : Qbar l)‖ = 1)
    (hd : ‖(d : Qbar l)‖ = 1) : Cong (a * c) (b * d) := by
  refine cong_trans (cong_mul_right h c (cong_norm h' hd)) ?_
  rw [mul_comm b c, mul_comm b d]
  exact cong_mul_right h' b hb
private theorem norm_inv_one {b : (Qbar l)ˣ} (hb : ‖(b : Qbar l)‖ = 1) : ‖((b⁻¹ : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_inv_eq_inv_val, norm_inv, hb, inv_one]
private theorem norm_mul_one {a b : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hb : ‖(b : Qbar l)‖ = 1) :
    ‖((a * b : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_mul, norm_mul, ha, hb, mul_one]
private theorem norm_pow_one {a : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (n : ℕ) :
    ‖((a ^ n : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [Units.val_pow_eq_pow_val, norm_pow, ha, one_pow]
private theorem cong_inv {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : Cong a⁻¹ b⁻¹ := by
  have := cong_mul_right (cong_symm h) (a⁻¹ * b⁻¹) (norm_mul_one (norm_inv_one (cong_norm h hb)) (norm_inv_one hb))
  rwa [mul_inv_cancel_left, mul_comm a⁻¹ b⁻¹, mul_inv_cancel_left] at this
private theorem cong_pow {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) (n : ℕ) : Cong (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using cong_refl 1
  | succ n ih => rw [pow_succ, pow_succ]; exact cong_mul ih h (norm_pow_one hb n) hb
private theorem norm_of_finOrder {Γ : Type} [Group Γ] {φ : Γ →* (Qbar l)ˣ} (h : IsOfFinOrder φ) (s : Γ) :
    ‖(φ s : Qbar l)‖ = 1 := by
  obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 : φ s ^ n = 1 := by rw [← MonoidHom.pow_apply, h1]; rfl
  have h3 : ‖(φ s : Qbar l)‖ ^ n = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
private theorem cyc_val (s : G F Ω) :
    ((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl
private theorem norm_cyc (s : G F Ω) : ‖((cycBar F Ω l s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
  rw [cyc_val, norm_algebraMap']
  exact PadicInt.norm_units _
private theorem cong_cyc (s : G F Ω) : Cong (cycBar F Ω l s ^ (l - 1)) 1 := by
  unfold Cong
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val, cyc_val]; simp
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero
private theorem cong_cyc_pow (s : G F Ω) (j t : ℕ) : Cong (cycBar F Ω l s ^ (j + (l - 1) * t)) (cycBar F Ω l s ^ j) := by
  rw [pow_add, pow_mul]
  have := cong_mul (cong_refl (cycBar F Ω l s ^ j)) (cong_pow (cong_cyc (l := l) s) (by simp) t)
    (norm_pow_one (norm_cyc s) j) (by simp)
  simpa using this
end CongLemmas
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem finOrder_of_kills {C : Type} [CommGroup C] {N : ℕ} (hN : 0 < N) {φ : G ℚ Ω →* C} (h : KillsMu N φ) :
    IsOfFinOrder φ := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, MonoidHom.ext fun s => ?_⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  refine h _ fun ζ hζ => ?_
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h1 := hz.autToPow_spec ℚ (s ^ Fintype.card (ZMod N)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hz.pow_eq_one, pow_one] at h1
  rw [map_pow, ← h1]
omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (h : IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj]; simp
omit [IsAlgClosure ℚ Ω] in
private theorem cc_not_mem (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K Ω] {c : G ℚ Ω} (h : IsCC c) :
    c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := h
  intro hc
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hj, hc x]
private theorem sq_mem_galOf (K : Type) [Field K] [NumberField K] [Algebra K Ω] (h : Module.finrank ℚ K = 2) (s : G ℚ Ω) :
    s * s ∈ galOf ℚ K Ω := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  haveI : IsGalois ℚ K := inferInstance
  have h1 : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h]
  have h2 : AlgEquiv.restrictNormalHom K (s * s) = 1 := by
    rw [map_mul, ← sq, ← h1, pow_card_eq_one']
  intro x
  have := AlgEquiv.restrictNormal_commutes (s * s) K x
  rw [← this]
  change algebraMap K Ω (AlgEquiv.restrictNormalHom K (s * s) x) = _
  rw [h2]; rfl
private theorem algClosure (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
end Gal
section Shape
variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
private theorem ordAt_change {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ ψ' : Fin n → G F Ω →* (Qbar l)ˣ}
    {A : ValuationSubring Ω} (h : OrdAt r m ψ A) (h' : ∀ i s, Cong (ψ' i s) (ψ i s)) : OrdAt r m ψ' A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  exact ⟨κ, h1, h2, fun i s => cong_trans (h3 i s) (cong_symm (h' i s))⟩
private theorem order_at_adjoint_zero {ρ : G F Ω →* GL (Fin 2) (Qbar l)} {m : ℤ} {Φ : G F Ω →* (Qbar l)ˣ} (hΦ : ∀ s, ‖(Φ s : Qbar l)‖ = 1)
    {A : ValuationSubring Ω} (h : OrdAt ρ ![m, 0] ![Φ, 1] A) : OrdAt (ad0 ρ) ![m, 0, -m] ![Φ, 1, Φ⁻¹] A := by
  obtain ⟨κ, h1, h2, h3⟩ := h
  have h4 : ∀ s : ↥(Dec (F := F) A), Cong ((κ 0 / κ 1) s) (Φ s) := fun s => by
    have := cong_mul (h3 0 s) (cong_inv (h3 1 s) (by simp)) (hΦ s) (by simp)
    simpa [div_eq_mul_inv] using this
  refine ⟨_, (ad0Facts l _ ρ).2.2.2.1 _ κ h1, fun i s hs => ?_, fun i s => ?_⟩
  · have a0 := h2 0 s hs
    have a1 := h2 1 s hs
    fin_cases i <;> simp [a0, a1]
  · fin_cases i
    · exact h4 s
    · exact cong_refl _
    · have := cong_inv (h4 s) (hΦ s)
      simpa using this
private theorem exists_symmetric_pairing_adjoint_zero {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) {c : Γ} (hc : c * c = 1) :
    ∃ P : GL (Fin 3) (Qbar l), (P.val)ᵀ = P ∧ ∀ s,
      (ad0 ρ s).valᵀ * (P.val) *
        (ad0 ρ (c * s * c⁻¹)).val = P := by
  obtain ⟨P, h1, h2⟩ := (ad0Facts l _ ρ).2.1
  have e : (ad0 ρ c).val * (ad0 ρ c).val = 1 := by
    rw [← Units.val_mul, ← map_mul, hc, map_one, Units.val_one]
  have e' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  refine ⟨P * ad0 ρ c, ?_, fun s => ?_⟩
  · rw [Units.val_mul, Matrix.transpose_mul, h1]
    conv_rhs => rw [← h2 c]
    rw [Matrix.mul_assoc _ _ (ad0 ρ c).val, e, Matrix.mul_one]
  · rw [e', map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul]
    conv_rhs => rw [← h2 s]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ad0 ρ c).val (ad0 ρ c).val, e,
      Matrix.one_mul]
private theorem adjoint_zero_twist {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (κ : Γ →* kˣ) : ad0 (tw ρ κ) = ad0 ρ := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hk : (κ s : k) ≠ 0 := (κ s).ne_zero
  have hd : (ρ s : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (Matrix.isUnits_det_units _).ne_zero
  have e1 : ∀ (r : Γ →* GL (Fin 2) k), (ad0 r s : Matrix (Fin 3) (Fin 3) k) =
      ((r s : Matrix (Fin 2) (Fin 2) k).det)⁻¹ • symSquareMatrixHom k (r s : Matrix (Fin 2) (Fin 2) k) := fun r => by
    rw [ad0, tw_val]; simp
  have e2 : ∀ (a : k) (g : Matrix (Fin 2) (Fin 2) k), symSquareMatrixHom k (a • g) = (a ^ 2) • symSquareMatrixHom k g := fun a g => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> ring
  rw [e1, e1, tw_val, e2, Matrix.det_smul, smul_smul]
  congr 1
  simp only [Fintype.card_fin]
  field_simp
end Shape
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Sym.W.adjoint_lift_from_eisenstein_of_propagation :
    UpperTheory.V.Z.Sym.W.PropEGW → UpperTheory.V.Z.Sym.W.SeedInW → UpperTheory.V.Z.Sym.W.AdAutW → _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := by
  intro heg hIn hadj K L Ω _ _ _ _ _ _ _ _ _ _ l _ ι c N w χ' η θ j D hne M hM0 hM hU hχu B
  haveI := D.imag
  haveI := D.ab
  haveI := algClosure (Ω := Ω) L
  have hcc := cc_sq D.cc
  have hη2 : ∀ s, η s * η s = 1 := fun s => by
    rw [← map_mul, ← MonoidHom.mem_ker, D.η_ker]; exact sq_mem_galOf K D.quad s
  have hηc : η c = -1 := by
    have h1 : η c ≠ 1 := fun h => cc_not_mem K D.cc (D.η_ker ▸ MonoidHom.mem_ker.2 h)
    have h2 : (η c : Qbar l) * η c = 1 := by rw [← Units.val_mul, hη2, Units.val_one]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · exact absurd (Units.ext h) h1
    · exact Units.ext h
  have hηL : ∀ s ∈ galOf ℚ L Ω, η s = 1 := fun s hs => by
    rw [← MonoidHom.mem_ker, D.η_ker]; exact D.KL hs
  have hθL : ∀ s ∈ galOf ℚ L Ω, θ s = 1 := fun s hs => D.θL hs
  have hsp : SplitAt N w (χ' * η) :=
    ⟨fun s hs => by rw [MonoidHom.mul_apply, D.χ_split.1 s hs, D.η_split.1 s hs, one_mul],
      fun s hs => by rw [MonoidHom.mul_apply, D.χ_split.2 s hs, D.η_split.2 s hs, one_mul]⟩
  have hφ1 : χ' * η ≠ 1 := fun h => hne (MonoidHom.ext fun s => by
    have h1 : χ' s * η s = 1 := by rw [← MonoidHom.mul_apply, h]; rfl
    exact mul_right_cancel (h1.trans (hη2 s).symm))
  have hfin := finOrder_of_kills D.aux.pos hsp.1
  have hχn := norm_of_finOrder (finOrder_of_kills D.aux.pos D.χ_split.1)
  obtain ⟨k₀, hk₀⟩ := heg l Ω ι c D.cc N w (χ' * η) θ D.aux hsp hφ1
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlev : Even (l - 1) := (Fact.out : l.Prime).even_sub_one D.aux.odd
  obtain ⟨t, ht⟩ : ∃ t, t = B + k₀ + 2 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = j + (l - 1) * t := ⟨_, rfl⟩
  have hmt : t ≤ m := by
    have := Nat.le_mul_of_pos_left t (show 0 < l - 1 by omega)
    omega
  have hpar : (χ' * η) c = (-1) ^ (m + 1) := by
    rw [MonoidHom.mul_apply, D.par, hηc, hm, pow_succ, pow_add, pow_mul, hlev.neg_one_pow, one_pow, mul_one]
  obtain ⟨ρ, hρ, hrw, hun⟩ := hk₀ (m + 1) (by omega) hpar
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = cycBar ℚ Ω l ^ (m + 1 - 1) * (χ' * η) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = cycBar ℚ Ω l ^ j * χ' := ⟨_, rfl⟩
  have hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1 := fun s => by
    rw [hΦ]; exact norm_mul_one (norm_pow_one (norm_cyc s) _) (norm_of_finOrder hfin s)
  have hΨn : ∀ s, ‖(Ψ s : Qbar l)‖ = 1 := fun s => by
    rw [hΨ]; exact norm_mul_one (norm_pow_one (norm_cyc s) _) (hχn s)
  have hΦΨ : ∀ s ∈ galOf ℚ L Ω, Cong (Φ s) (Ψ s) := fun s hs => by
    have := cong_mul_right (cong_cyc_pow (l := l) s j t) _ (hχn s)
    rw [hΦ, hΨ]
    simpa [hηL s hs, hm] using this
  have hio : IrrOpen ρ := by
    refine (sI l D.aux.odd Ω ι _ θ (m + 1) (by omega) hfin ρ hρ).2 ?_
    obtain ⟨s, hs, h⟩ := D.sq
    refine ⟨s, fun h' => h ?_⟩
    rw [← hΦ] at h'
    rw [← hΨ]
    exact cong_trans (cong_pow (cong_symm (hΦΨ s hs)) (hΦn s) 2) h'
  have hio' := ad0Irr l _ ρ hρ.cont hio
  have AF := ad0Facts l _ ρ
  have RL := resFacts ℚ L Ω l 3 (ad0 ρ)
  have hiL : IsIrr ((ad0 ρ).comp (galEmb ℚ L Ω)) := RL.2.2.2.1.1 (hio' _ RL.2.1)
  obtain ⟨P, hP1, hP2⟩ := exists_symmetric_pairing_adjoint_zero ρ hcc
  have hψ : ∀ (i : Fin 3) (s : G L Ω), Cong ((![Ψ, 1, Ψ⁻¹] i).comp (galEmb ℚ L Ω) s) ((![Φ, 1, Φ⁻¹] i).comp (galEmb ℚ L Ω) s) := by
    intro i s
    have h := cong_symm (hΦΨ _ (galEmb_mem ℚ L Ω s))
    fin_cases i
    · exact h
    · exact cong_refl _
    · exact cong_inv h (hΦn _)
  refine ⟨m, by omega, ?_, (ad0 ρ).comp (galEmb ℚ L Ω), RL.2.2.2.2.1 hio', ?_⟩
  · rw [hm]; simp [Nat.ModEq]
  rw [← hΨ]
  refine ⟨(AF.1 hρ.cont).comp RL.1, hiL, ⟨P, hP1, fun s s' h => ?_⟩, ?_, fun A hA => ?_, fun A hA => ?_, ?_⟩
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h, hP2]; simp
  · have h1 := hρ.res
    rw [← hΦ] at h1
    have h2 := AF.2.2.2.2.2 1 Φ (fun s => ⟨by simp, hΦn s⟩) h1
    rw [div_one, one_div] at h2
    refine (shapeFacts l _ 3 _ 1).2.2.2.2.1 (fun i => (![Φ, 1, Φ⁻¹] i).comp (galEmb ℚ L Ω)) _ 1 (fun i s => ?_)
      (fun s i => h2 _ i) hψ
    fin_cases i
    · exact hΦn _
    · simp
    · exact norm_inv_one (hΦn _)
  · have h1 : TypeAway (ad0 ρ) _ := fun A hA => AF.2.2.1 _ _ _ (hρ.away A hA)
    refine (shapeFacts l _ 3 _ 1).2.1 _ _ _ 1 (RL.2.2.2.2.2.1 _ h1 A hA) fun i s _ => ?_
    have a1 := hηL _ (galEmb_mem ℚ L Ω s)
    have a2 := hθL _ (galEmb_mem ℚ L Ω s)
    fin_cases i <;> simp [a1, a2]
  · have h1 := hρ.above A hA
    rw [← hΦ, show ((m + 1 : ℕ) : ℤ) - 1 = m by push_cast; ring] at h1
    exact ordAt_change (RL.2.2.2.2.2.2 _ _ A (order_at_adjoint_zero hΦn h1)) hψ
  · obtain ⟨κ, hκ⟩ := hIn K L Ω l ι c N w χ' η θ j D M hM0 ((dvd_mul_left l 2).trans hM) hU hχu m ρ (by omega) hρ hio hrw hun hpar
    have h1 := hadj L Ω l ι D.aux.odd M m hM0 hM hU _ hκ
    rw [adjoint_zero_twist, show ad0 (ρ.comp (galEmb ℚ L Ω)) = (ad0 ρ).comp (galEmb ℚ L Ω) from rfl] at h1
    refine _root_.UpperTheory.V.Z.Win.Birth.mkCsdW' h1.1 fun _ => h1.2.witA
      (UpperTheory.V.Z.Win.Birth.potOrd L Ω l 3 _ ![(m : ℤ), 0, -(m : ℤ)] (fun i => (![Φ, 1, Φ⁻¹] i).comp (galEmb ℚ L Ω)) _ (fun a b => ?_) fun A hA => ?_)
    · fin_cases a <;> fin_cases b <;> simp <;> omega
    · have h2 := hρ.above A hA
      rw [← hΦ, show ((m + 1 : ℕ) : ℤ) - 1 = m by push_cast; ring] at h2
      exact RL.2.2.2.2.2.2 _ _ A (order_at_adjoint_zero hΦn h2)
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
namespace UpperTheory.V.Sd.EG
section Norm
variable {l : ℕ} [hl : Fact l.Prime]
end Norm
private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]
section Gal
variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega
theorem ordExT_sv_alt (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {ψ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = ψ) :
    ∃ c π r, OrdForm ι ψ⁻¹ (1 - (k : ℤ)) c (fun _ => ![0, 1 - (k : ℤ)]) (fun _ => 1) π r ∧
      (∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + (cycBar ℚ Ω l ^ (k - 1) * ψ) s)‖ < 1) ∧
      (∀ w : Pl ℚ, HasU w (π.locRep w) (N.factorization (normV w)) (g.a (normV w))) ∧
      ∀ w : Pl ℚ, ¬ normV w ∣ N → ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => X - C b).prod =
        X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1)) := by
  classical
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N (by omega) χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, hinf, hU, hsat⟩ := _root_.UpperTheory.V.Sd.holRep_alt P ℚ k (by omega) _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems ℚ Ω l ι 2 one_le_two π χ' hreg hpol
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  set c : Pl ℚ → ℕ := fun w => N.factorization (normV w) with hc
  have hc0 : ∀ w, c w = 0 ↔ ¬ normV w ∣ N := fun w => by
    simp [hc, Nat.factorization_eq_zero_iff, normV_prime w, NeZero.ne N]
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * ψ with hD
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have c1 : Continuous fun s : G ℚ Ω => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hG.cont.comp continuous_inv)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    ((Filter.eventually_cofinite.1 hatt.2).union (fin_dvd hlN))
  have hall : ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 ∧
      (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    refine ((isClosed_small (c1.matrix_trace.sub (continuous_const.add hDc))).inter
      (isClosed_eq c1.matrix_det hDc)).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨⟨B₁, hB₁, hF⟩, hq⟩ := hw
    have hqN : ¬ normV w ∣ N := fun h => hq (h.mul_left _)
    obtain ⟨B₂, hB₂, e⟩ := hsat w ((hc0 w).2 hqN)
    obtain rfl := hB₁.unique hB₂
    obtain ⟨h2, h3⟩ := tr_det ι _ (((hF A hA).2 σ hσ).trans e)
    have hAq := (over_iff hA _).2 dvd_rfl
    have h1 : (D σ : Qbar l) = ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1)) := by
      rw [hDv, cyc_frob (normV_prime w) hAq (fun h => hq (h.mul_right _)) hσ, dirG_frob _ (normV_prime w) hAq hqN hσ]
      simp [mul_comm]
    have h4 := hg _ (normV_prime w)
    rw [map_sub, map_add, map_one, ← h1, ← h2] at h4
    exact ⟨h4, by rw [Set.mem_setOf_eq, h3, h1, (hval w hqN).2]⟩
  have hlev : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hker : ψ⁻¹.ker = ψ.ker := by ext s; simp
  refine ⟨levL l c, π, r, ⟨hreg, ⟨χ', hpol⟩, hG.cont, hatt, MonoidHom.ext fun s => ?_, ?_, ?_, fun w A hA => ?_, fun w hw => ?_,
    fun w hw hwl => ?_, fun w hw => ?_⟩, fun s => (hall s).1, hU, fun w hw => (hval w hw).2 ▸ hsat w ((hc0 w).2 hw)⟩
  · have h1 := (hall s⁻¹).2
    rw [inv_inv] at h1
    refine (Units.ext h1 : Matrix.GeneralLinearGroup.det (r s) = D s⁻¹).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv, map_inv]
    rfl
  · rw [hker, ← hm]
    exact dirG_open _
  · refine (fin_dvd hlN).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · exact ((mem_iff w l).1 h).mul_right _
    · rw [Set.mem_setOf_eq, hlev w h, Ne, hc0, not_not] at hw
      exact hw.mul_left _
  · rw [hker, ← hm]
    by_cases h : normV w ∣ N
    · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => hN ((mem_iff_eq w hl.out).1 h' ▸ h)
      rw [hlev w h1, hc0]
      exact iff_of_false (ram hχ _ (normV_prime w) h ((over_iff hA _).2 dvd_rfl)) (by simp [h, h1])
    · refine iff_of_true (fun s hs => dirG_unr _ (fun h' => h ((over_iff hA _).1 h')) hs) ?_
      by_cases h1 : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      · exact Or.inr h1
      · exact Or.inl ((hlev w h1).trans ((hc0 w).2 h))
  · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => by rw [hlev1 w h'] at hw; exact one_ne_zero hw
    obtain ⟨v, h2, h3, -⟩ := hU w
    rw [show N.factorization (normV w) = 0 from (hlev w h1).symm.trans hw] at h3
    exact ⟨v, h2, h3⟩
  · rw [hlev w hwl] at hw ⊢
    refine ⟨_, hU w, norm_eq_one_of ?_⟩
    have h4 := hg _ (normV_prime w)
    rw [Ne, hc0, not_not] at hw
    rwa [χ.map_nonunit (fun h' => (Nat.Prime.coprime_iff_not_dvd (normV_prime w)).1 ((ZMod.isUnit_iff_coprime _ _).1 h') hw),
      zero_mul, add_zero, map_sub, map_one] at h4
  · have hq := (mem_iff_eq w hl.out).1 hw
    have hqN : ¬ normV w ∣ N := hq ▸ hN
    obtain ⟨B, hB, e⟩ := hsat w ((hc0 w).2 hqN)
    rw [(hval w hqN).2] at e
    have h2 : ‖ι.symm (χ (normV w : ZMod N))‖ = 1 := by
      refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
      rw [← ZMod.coe_unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd (normV_prime w)).2 hqN), ← map_pow, ← map_pow,
        ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, map_one]
    have h3 : ‖(normV w : Qbar l)‖ < 1 := by rw [hq]; exact norm_l
    have hs : ‖ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))‖ < ‖(normV w : Qbar l)‖ := by
      rw [map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]
      exact pow_lt_self_of_lt_one₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)) h3 (by omega)
    have ha : ‖ι.symm (g.a (normV w)) - 1‖ < 1 := by
      have := small_add (hg _ (normV_prime w)) (hs.trans h3)
      rw [← map_add] at this
      rw [← map_one ι.symm, ← map_sub]
      convert this using 3
      ring
    obtain ⟨lam, h5, h6⟩ := stab w ι π hB e ha hs
    refine ⟨hlev1 w hw, ?_, ?_, norm_one, ⟨lam, h5, ?_⟩, fun τ _ => hinf _⟩
    · simp; omega
    · simp
    · simpa using h6
end Gal
end UpperTheory.V.Sd.EG
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.V.Z.Sym.W.RetractionModules
section Rep
private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := by
  have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
    rcases f.injective_or_eq_zero with hi | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · simp)
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
    by_contra hn
    push Not at hn
    refine hx ((Submodule.mem_bot R).1 ?_)
    rw [← IsSemisimpleModule.jacobson_eq_bot R M]
    exact Submodule.mem_sInf.2 hn
  obtain ⟨W, hc⟩ := exists_isCompl m
  haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
  obtain ⟨e⟩ := hiso W
  refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
  simpa using h0
variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩
private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])
private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ
end Rep
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]
section Gal
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}
end Gal
end UpperTheory.V.Z.Sym.W.RetractionModules
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Z.Sym.W.RetractionModules
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem plainAll {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r} (H : OrdForm ι ξ s c m a π r) {wt HT} (hG : UpperTheory.Gal.SV.IsGalRS π ι r wt HT) (w) :
    UpperTheory.V.Z.Win.PlainAtR π w := fun σ hσ =>
  (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
theorem UpperTheory.V.Z.Sym.W.tieS_a_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.Unl.TieS := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl B hB
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := _root_.UpperTheory.Gal.SV.exRS_alt PH.toClassicalTheorems F Ω l ι 2 one_le_two π χ H.reg hχ
  exact (hall r H.cont H.att).frob w hl B hB
theorem UpperTheory.V.Z.Sym.W.ordWin_a_alt (PH : _root_.UpperTheory.V.Af.HypothesesH') (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s c m a π r)
    (H : OrdForm ι ξ s c m a π r) : UpperTheory.GalN.V.RW ι r := by
  refine UpperTheory.GalN.V.L.rwwd F Ω l ι 2 r H.cont fun w hl A h => ?_
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := _root_.UpperTheory.Gal.SV.exRS_alt PH.toClassicalTheorems F Ω l ι 2 one_le_two π χ H.reg hχ
  exact (hall r H.cont H.att).ratio w hl A h (plainAll H (hall r H.cont H.att) w)
theorem UpperTheory.V.Z.Sym.W.tieU_a_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.Unl.TieU := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl n lam hn hl0 hU A h t ht
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := _root_.UpperTheory.Gal.SV.exRS_alt PH.toClassicalTheorems F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F 2 π w
  obtain ⟨v, hv, hf, hUv⟩ := hU
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt P F w σ n (Units.mk0 lam hl0) hn
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hUv, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨b, hb⟩ := GlobalTheory.localArtinExists_holds F Ω A w h
  let g : Weil h := (⟨t, mem_Weil_of_isFrob h ht⟩ : Weil h)⁻¹
  have hdeg : deg g = -1 := by
    rw [deg_inv, deg_eq_one_iff.2 ht]
  have hp := plainAll H hG w σ hσ
  have e1 := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P F Ω l ι 2 r w hl A h b hb σ (hG.loc w σ hσ hp).1 hp ψ hψ hs g
  have h2 : ((r (g : G F Ω)).val.charpoly.map ι.toRingHom).IsRoot
      ((((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ)) := by
    have hA := GlobalTheory.SatChar.absPow_art hb ((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ) g
    have hc : -((((2 : ℕ) : ℂ) - 1) / 2) = ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [e1, UpperTheory.V.Z.Sym.W.psPol, Fin.prod_univ_two, hc, ← hA]
    refine Polynomial.IsRoot.def.2 ?_
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Units.val_mul, mul_comm ((ψ 0 (b g) : ℂˣ) : ℂ), sub_self, zero_mul]
  have key : (((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ) = lam := by
    have hy : ord (w.adicCompletion F) (b g) = 1 := by rw [hb.ord_eq, hdeg, neg_neg]
    have hv0 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    have hv1 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      rw [SphCompletion.ord_completion] at hy
      rw [← WithZero.exp_log hv0]
      congr 1
      omega
    have hu : IsUnitAt w (b g * (atFin w (unif w))⁻¹) := by
      have h2 := unif_spec w
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, h2]
      exact mul_inv_cancel₀ (by simp)
    have hμy : μ₁ (b g) = μ₁ (atFin w (unif w)) := by
      exact mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact hμ _ hu)
    have hA := GlobalTheory.SatChar.absPow_art hb (1 / 2 : ℝ) g
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (zero_lt_one.trans this).ne'
    have hQ2 : ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((normV w : ℕ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hq]
      norm_num
    have hs' : ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      norm_num
    have hc : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hdeg] at hA
    rw [hψ0, Units.val_mul, Units.val_inv_eq_inv_val, hc, hA, hμy, hs', hdeg, Complex.cpow_neg]
    have hl' := hlam
    rw [Units.val_mk0] at hl'
    generalize ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = Q at hQ2 ⊢
    rw [← hl', ← hQ2]
    simp only [zpow_neg, zpow_one, inv_inv]
    ring
  rw [key] at h2
  refine ⟨ι.symm lam, ?_, by simp⟩
  have h3 : ι.toRingHom (ι.symm lam) = lam := ι.apply_symm_apply lam
  rw [← h3] at h2
  exact (Polynomial.isRoot_map_iff ι.injective).1 h2
end
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.EG
namespace UpperTheory.V.Z.Sym.Unl
private theorem quad_pair {K : Type} [Field K] {a d u v : K} (hu : u ^ 2 - a * u + d = 0) (hv : v ^ 2 - a * v + d = 0)
    (hne : u ≠ v) : v + u = a ∧ v * u = d := by
  have h1 : u + v - a = 0 :=
    (mul_eq_zero.1 (by linear_combination hu - hv : (u - v) * (u + v - a) = 0)).resolve_left (sub_ne_zero.2 hne)
  exact ⟨by linear_combination h1, by linear_combination u * h1 - hu⟩
private theorem charpoly_quad {K : Type} [Field K] (B : Matrix (Fin 2) (Fin 2) K) {u : K} (h : B.charpoly.IsRoot u) :
    u ^ 2 - B.trace * u + B.det = 0 := by
  rw [Matrix.charpoly_fin_two] at h
  simpa [Polynomial.IsRoot] using h
private theorem inv_charpoly_root {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) {x : K}
    (h : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x) :
    x ≠ 0 ∧ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x⁻¹ := by
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  exact ⟨hx0, Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi⟩
private theorem norm_xi {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (ξ : G ℚ Ω →* (Qbar l)ˣ) (h : IsOpen (ξ.ker : Set (G ℚ Ω))) (s : G ℚ Ω) : ‖ι (ξ s : Qbar l)‖ = 1 := by
  haveI : Finite (G ℚ Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ s ^ ξ.ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ s)
  have h2 : (ι (ξ s : Qbar l)) ^ ξ.ker.index = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 h0
private theorem det_inv {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 3 ≤ k)
    (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (ξ : G ℚ Ω →* (Qbar l)ˣ)
    (h : Matrix.GeneralLinearGroup.det.comp r = cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) (s : G ℚ Ω) :
    (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * ((ξ s)⁻¹ : (Qbar l)ˣ) := by
  have h1 : Matrix.GeneralLinearGroup.det (r s⁻¹) = (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ := DFunLike.congr_fun h s⁻¹
  have h2 : (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ = cycBar ℚ Ω l s ^ (k - 1) * (ξ s)⁻¹ := by
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, MonoidHom.mul_apply, map_inv, map_inv,
      MonoidHom.inv_apply, MonoidHom.pow_apply, inv_inv]
  have h3 := congrArg Units.val (h1.trans h2)
  simpa using h3
theorem half_of_printed_hida : _root_.UpperTheory.V.Af.HypothesesH' → HalfOf := by
  intro P Ω _ _ _ l _ ι k N _ hk χ hχ g hg ξ c m a π r hO hU hS w hwl A hA s hs x y hx hy heq
  have hp := normV_prime w
  obtain ⟨hx0, hxr⟩ := inv_charpoly_root (r s) hx
  obtain ⟨hy0, hyr⟩ := inv_charpoly_root (r s) hy
  rw [← map_inv] at hxr hyr
  have hp1 : (1 : ℝ) < (normV w : ℝ) := by exact_mod_cast hp.one_lt
  have hnx : 0 < ‖ι x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hny : 0 < ‖ι y‖ := norm_pos_iff.2 (by simpa using hy0)
  by_cases hpN : normV w ∣ N
  · have hb := badAbs k N hk χ hχ g (normV w) hp hpN
    have hR : 0 < ‖g.a (normV w)‖ := by
      have : 0 < ‖g.a (normV w)‖ ^ 2 := by rw [hb]; positivity
      rcases (norm_nonneg (g.a (normV w))).lt_or_eq with h | h
      · exact h
      · rw [← h] at this
        simp at this
    have hn : N.factorization (normV w) ≠ 0 := (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne'
    obtain ⟨u₀, hu₀, hun⟩ := _root_.UpperTheory.V.Z.Sym.W.tieU_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl _ _ hn (norm_pos_iff.1 hR) (hU w) A hA s hs
    have hAq := (over_iff hA _).2 (dvd_refl (normV w))
    have hpl : ¬ normV w ∣ l := fun h => hwl ((mem_iff w l).2 h)
    have hd : ‖ι (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det‖ = (normV w : ℝ) ^ (k - 1) := by
      rw [det_inv hk r ξ hO.det s, cyc_frob hp hAq hpl hs, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast,
        Units.val_inv_eq_inv_val, map_inv₀, norm_inv, norm_xi ι ξ hO.ξ_open s, inv_one, mul_one]
    have hall : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u → ‖ι u‖ = ‖g.a (normV w)‖ := fun u hu => by
      by_cases e : u = u₀
      · rw [e, hun]
      · have h1 := (quad_pair (charpoly_quad _ hu) (charpoly_quad _ hu₀) e).2
        have h2 : ‖ι u₀‖ * ‖ι u‖ = (normV w : ℝ) ^ (k - 1) := by rw [← norm_mul, ← map_mul, h1, hd]
        rw [hun, ← hb] at h2
        exact mul_left_cancel₀ hR.ne' (h2.trans (sq _))
    have e1 := hall _ hxr
    have e2 := hall _ hyr
    rw [map_inv₀, norm_inv] at e1 e2
    have e3 : ‖ι x‖ = ‖ι y‖ := inv_injective (e1.trans e2.symm)
    rw [e3] at heq
    have : (1 : ℝ) * ‖ι y‖ ^ 2 = (normV w : ℝ) * ‖ι y‖ ^ 2 := by rw [one_mul]; exact heq
    have := mul_right_cancel₀ (pow_pos hny 2).ne' this
    exact hp1.ne this
  · obtain ⟨B, hB, e⟩ := hS w hpN
    have hF := _root_.UpperTheory.V.Z.Sym.W.tieS_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl B hB
    have hP := ((hF A hA).2 s hs).trans e
    have hq : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u →
        (ι u) ^ 2 - g.a (normV w) * ι u + χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) = 0 := fun u hu => by
      have h1 := congrArg (Polynomial.eval (ι u)) hP
      have h2 : (Polynomial.eval (ι u) (((r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly).map ι.toRingHom)) = 0 := by
        have := Polynomial.eval₂_at_apply (p := (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly) ι.toRingHom u
        rw [Polynomial.eval_map]
        refine this.trans ?_
        rw [hu.eq_zero, map_zero]
      rw [h2] at h1
      simpa using h1.symm
    have hU' := hq _ hxr
    have hV' := hq _ hyr
    have hfin : ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι x⁻¹‖ ^ 2 := by
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_pow, inv_pow, heq]
      field_simp
    by_cases e : ι x⁻¹ = ι y⁻¹
    · rw [e] at hfin
      have h3 : ‖ι y⁻¹‖ ≠ 0 := by rw [map_inv₀, norm_inv]; exact (inv_pos.2 hny).ne'
      have : (1 : ℝ) * ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι y⁻¹‖ ^ 2 := by rw [one_mul]; exact hfin
      have := mul_right_cancel₀ (pow_ne_zero 2 h3) this
      exact hp1.ne this
    · obtain ⟨h1, h2⟩ := quad_pair hU' hV' e
      exact goodHalf k N hk χ hχ g hg (normV w) hp hpN _ _ h1 h2 hfin
end UpperTheory.V.Z.Sym.Unl
end
end
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
namespace UpperTheory.V.Sd.EG
section Norm
variable {l : ℕ} [hl : Fact l.Prime]
private theorem root_small {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have hx := norm_root hl.out.ne_zero h
  have hy : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp [hx])
  have e := add_pow_prime_eq hl.out (x - 1) 1
  rw [sub_add_cancel, h, one_pow] at e
  set S := ∑ k ∈ Finset.Ioo 0 l, (x - 1) ^ (k - 1) * 1 ^ (l - k - 1) * ((l.choose k / l : ℕ) : Qbar l) with hS
  have hs : ‖S‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : (x - 1) ^ l = -((l : Qbar l) * ((x - 1) * S)) := by linear_combination -e
  have h3 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, e2, norm_neg, norm_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_l (mul_le_one₀ hy (norm_nonneg _) hs)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h3
variable (l) in
private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu
private theorem cong_mul {a u : (Qbar l)ˣ} (ha : ‖(a : Qbar l)‖ = 1) (hu : u ∈ U l) : Cong (a * u) a := by
  have e : ((a * u : (Qbar l)ˣ) : Qbar l) - a = a * (u - 1) := by push_cast; ring
  unfold Cong
  rw [e, norm_mul, ha, one_mul]
  exact hu
private theorem resSum_of {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ)
    (ht : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s)‖ < 1)
    (hd : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s‖ < 1) : ResSum ρ ![1, Φ] := by
  intro s i
  have e : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (X - C ((![1, Φ] j s : (Qbar l)ˣ) : Qbar l)) =
      C (-((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + Φ s))) * X +
        C ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det - Φ s) := by
    rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_one, map_neg, map_sub, map_add]
    ring
  rw [← coeff_sub, e, coeff_add, coeff_C_mul_X, coeff_C]
  refine small_add ?_ ?_
  · split_ifs
    · rw [norm_neg]; exact ht s
    · simp
  · split_ifs
    · exact hd s
    · simp
private theorem trace_inv {K : Type} [Field K] (g : GL (Fin 2) K) (d : Kˣ) (h : Matrix.GeneralLinearGroup.det g = d⁻¹) :
    ((d : K) • (g : Matrix (Fin 2) (Fin 2) K)).trace = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  have h1 := congrArg Units.val h
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
  rw [Matrix.coe_units_inv, Matrix.inv_def, h1, Ring.inverse_unit, inv_inv, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [add_comm]
end Norm
section Gal
variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem dec_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {γ : G ℚ Ω}
    (hγ : IsFrob A (normV v) γ) (K : Subgroup (G ℚ Ω)) (hI : Ine (F := ℚ) A ≤ K) (hK : γ ∈ K) :
    Dec (F := ℚ) A ≤ K.topologicalClosure := by
  haveI : IsGalois ℚ Ω := {}
  have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K.topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  refine le_trans (le_sInf ?_) key.ge
  rintro N ⟨hNo, hN⟩
  have h := (Subgroup.le_topologicalClosure _).trans hN
  exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (hI.trans h) (h hK)
private theorem above_of {ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hρ : Continuous ρ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ}
    (hκ : IsFlagOn ρ (Dec (F := ℚ) A) κ) (hI : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1)
    (hF : ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A (normV v) (σ : G ℚ Ω) → κ 0 σ ∈ U l) (s : ↥(Dec (F := ℚ) A)) :
    κ 0 s * κ 1 s = Matrix.GeneralLinearGroup.det (ρ s) ∧ κ 0 s ∈ U l := by
  obtain ⟨g, hg⟩ := hκ
  constructor
  · have e : Matrix.GeneralLinearGroup.det (g * ρ s * g⁻¹) = Matrix.GeneralLinearGroup.det (ρ s) := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [← e]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, (hg s).1 1 0 (by decide), (hg s).2, (hg s).2]
    simp
  · obtain ⟨γ, hγ⟩ := exists_isFrob hv
    have h1 := dec_le hv hγ (((U l).comap (κ 0)).map (Dec (F := ℚ) A).subtype)
      (fun t ht => ⟨⟨t, ht.1⟩, by
        show κ 0 _ ∈ U l
        rw [hI _ ht]; exact one_mem _, rfl⟩)
      ⟨⟨γ, hγ.1⟩, hF _ hγ, rfl⟩ s.2
    have hc : Continuous fun t : G ℚ Ω => (g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1 :=
      ((continuous_apply 0).comp ((continuous_apply 0).comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp ((continuous_const.mul hρ).mul continuous_const)))).sub continuous_const
    have h2 := closure_minimal (t := {t : G ℚ Ω | ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1}) (by
      rintro _ ⟨t, ht, rfl⟩
      show ‖(g * ρ t * g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 - 1‖ < 1
      rw [(hg t).2]
      exact ht) (isClosed_small hc) h1
    show ‖_‖ < 1
    rw [← (hg s).2]
    exact h2
private theorem core (P : _root_.UpperTheory.V.Af.HypothesesH') (hl2 : l ≠ 2) (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {φ θ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = φ * θ) (hθ : θ ^ l = 1)
    (hcj : Z.Sym.Unl.Cj k N χ g.f) :
    ∃ ρ, EisRep ι φ θ k ρ ∧ Z.Win.Birth.PR ι ρ ∧ UpperTheory.GalN.V.RW ι ρ ∧ Z.Sym.Unl.NoHalf ι ρ := by
  obtain ⟨c, π, r, H, htr, hU, hS⟩ := _root_.UpperTheory.V.Sd.EG.ordExT_sv_alt P ι hk hN hχ g hg hm
  have hθU : ∀ s, θ s ∈ U l := fun s => root_small (by
    have := DFunLike.congr_fun hθ s
    rw [MonoidHom.pow_apply] at this
    rw [← Units.val_pow_eq_pow_val, this]; rfl)
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * (φ * θ) with hD
  set Φ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * φ with hΦ
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDΦ : ∀ s, D s = Φ s * θ s := fun s => by simp [hD, hΦ, mul_assoc]
  have hΦn : ∀ s, ‖(Φ s : Qbar l)‖ = 1 := fun s => by
    have := congrArg norm (hDv s)
    rwa [norm_mul, norm_pow, cyc_norm, dirG_norm, one_pow, mul_one, hDΦ, Units.val_mul, norm_mul, norm_eq_one_of (hθU s), mul_one] at this
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have hcong : ∀ s, ‖(D s : Qbar l) - Φ s‖ < 1 := fun s => by
    rw [hDΦ]; exact cong_mul (hΦn s) (hθU s)
  have hdr : ∀ s, Matrix.GeneralLinearGroup.det (r s) = (D s)⁻¹ := fun s => by
    refine (DFunLike.congr_fun H.det s).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv]
    rfl
  have hdet : ∀ s, (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    rw [tw_val, Matrix.det_smul, ← Matrix.GeneralLinearGroup.val_det_apply, hdr, Fintype.card_fin, sq, mul_assoc, Units.mul_inv, mul_one]
  have SF := shapeFacts l (G ℚ Ω) 2 r D
  have hc0 : Continuous fun s => (tw r D s : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    simp only [tw_val]
    exact hDc.smul (Units.continuous_val.comp H.cont)
  have halg := (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results P.toClassicalTheorems ℚ Ω l ι).1 ((k - 1 : ℕ) : ℤ) (φ * θ) (hm ▸ dirG_open _)
  rw [zpow_natCast] at halg
  refine ⟨tw r D, ⟨Units.continuous_iff.2 ⟨hc0, ?_⟩, SF.2.2.2.2.2 (_root_.UpperTheory.V.Sd.ordinary_irreducible_of_printed_hida P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H),
    _root_.UpperTheory.V.Sd.twist_real_selfDual P.toClassicalTheorems ℚ Ω l ι 2 r D halg ⟨π, H.reg, H.att⟩, MonoidHom.ext fun s => Units.ext (hdet s),
    resSum_of _ Φ (fun s => ?_) fun s => ?_, fun A hA => ?_, fun A hA => ?_⟩,
    Z.Win.Birth.prTw ℚ Ω l ι r D halg (Z.Win.Birth.prOrd ℚ Ω l ι _ _ _ _ _ _ _ H),
    (Z.Sym.Unl.twOk ℚ Ω l 2 ι r D).2 (_root_.UpperTheory.V.Z.Sym.W.ordWin_a_alt P ℚ Ω l ι _ _ _ _ _ _ _ H),
    (Z.Sym.Unl.twOk ℚ Ω l 2 ι r D).1 (_root_.UpperTheory.V.Z.Sym.Unl.half_of_printed_hida P Ω l ι k N hk χ hχ g hcj _ _ _ _ _ _ H hU hS)⟩
  · simp only [← map_inv]
    exact hc0.comp continuous_inv
  · have := small_add (htr s) (hcong s)
    rw [tw_val, trace_inv _ _ (hdr s), ← map_inv]
    convert this using 2
    ring
  · rw [hdet]; exact hcong s
  · refine (shapeFacts l (G ℚ Ω) 2 _ 1).2.1 _ _ _ (Equiv.swap 0 1) (SF.1 _ _ (_root_.UpperTheory.V.Z.Win.RR.ordAway_a_alt P ℚ Ω l ι _ _ _ _ _ _ _ H A hA))
      fun i s hs => ?_
    have h1 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l A).2.2.2 hA hs
    have h2 : D s = (φ * θ) s := by
      rw [hD, MonoidHom.mul_apply, MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow, one_mul]
    fin_cases i
    · show 1 = ((φ * θ) s)⁻¹ * D s
      rw [h2, inv_mul_cancel]
    · show (φ * θ) s = 1 * D s
      rw [h2, one_mul]
  · obtain ⟨w, hw, hwl, hmem⟩ := (ML.placeBasic Ω).2.2.2.2.2.2.2.2.1 A l hl.out hA
    obtain ⟨κ, hκ, hI, hFr⟩ := _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_printsH P ℚ Ω l hl2 (splitL hl.out) ι _ _ _ _ _ _ _ H w hmem A hw
    have hI0 : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ 0 s = 1 := fun s hs => (hI 0 s hs).trans (zpow_zero _)
    have key := above_of H.cont hw hκ hI0 fun σ hσ => by
      have h1 : κ 0 σ⁻¹ * cycBar ℚ Ω l (σ : G ℚ Ω) ^ (0 : ℤ) ∈ U l := hFr σ hσ
      rwa [zpow_zero, mul_one, map_inv, inv_mem_iff] at h1
    have h1 : ∀ s : ↥(Dec (F := ℚ) A), κ 1 s * D s = (κ 0 s)⁻¹ := fun s => by
      rw [eq_inv_iff_mul_eq_one, mul_comm, ← mul_assoc, (key s).1, hdr, inv_mul_cancel]
    refine ⟨_, SF.2.2.1 _ κ hκ, fun i s hs => ?_, fun i s => ?_⟩
    · fin_cases i
      · have h2 : (φ * θ) s = 1 := hm ▸ dirG_unr _ (not_over hl.out hA hN) hs
        show κ 0 s * D s = cycBar ℚ Ω l s ^ ((k : ℤ) - 1)
        rw [hI0 s hs, one_mul, hD, MonoidHom.mul_apply, h2, mul_one, MonoidHom.pow_apply,
          show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      · show κ 1 s * D s = cycBar ℚ Ω l s ^ (0 : ℤ)
        rw [h1, hI0 s hs, inv_one, zpow_zero]
    · fin_cases i
      · show Cong (κ 0 s * D s) (Φ s)
        rw [hDΦ, mul_comm, mul_assoc]
        exact cong_mul (hΦn s) (mul_mem (hθU s) (key s).2)
      · show Cong (κ 1 s * D s) 1
        rw [h1]
        exact inv_mem (key s).2
private theorem dirG_dvd {O : Type} [CommRing O] {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (χ : DirichletCharacter O M) (s : G ℚ Ω) :
    (Chr.dirG ℚ Ω χ s : O) = χ ((((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N).val : ℕ) : ZMod M) := by
  rw [dirG_val, ← (Chr.clsFacts ℚ Ω N).2.1 M h, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]
private theorem dirG_ne_one {M : ℕ} [NeZero M] {O : Type} [CommRing O] {χ : DirichletCharacter O M} (h : Chr.dirG ℚ Ω χ ≠ 1) : M ≠ 1 := by
  rintro rfl
  refine h (MonoidHom.ext fun s => ?_)
  rw [Chr.dirG, MonoidHom.comp_apply, Subsingleton.elim (Chr.cls ℚ Ω 1 s) 1, map_one, MonoidHom.one_apply]
end Gal
private theorem exists_mul {M w : ℕ} [NeZero (M * w)] (φ : DirichletCharacter ℂ M) (θ : DirichletCharacter ℂ w) :
    ∃ χ : DirichletCharacter ℂ (M * w), ∀ n : ℕ, χ (n : ZMod (M * w)) = φ (n : ZMod M) * θ (n : ZMod w) := by
  refine ⟨DirichletCharacter.changeLevel (dvd_mul_right M w) φ * DirichletCharacter.changeLevel (dvd_mul_left w M) θ, fun n => ?_⟩
  by_cases h : n.Coprime (M * w)
  · have h' : IsCoprime (n : ℤ) ((M * w : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 h
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' φ (dvd_mul_right M w) h'
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' θ (dvd_mul_left w M) h'
    rw [Int.cast_natCast, Int.cast_natCast] at h1 h2
    rw [MulChar.mul_apply, h1, h2]
  · rw [MulChar.map_nonunit _ (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h'))]
    rw [Nat.coprime_mul_iff_right, not_and_or] at h
    rcases h with h | h
    · rw [φ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), zero_mul]
    · rw [θ.map_nonunit (fun h' => h ((ZMod.isUnit_iff_coprime _ _).1 h')), mul_zero]
end UpperTheory.V.Sd.EG
open UpperTheory.V.Sd UpperTheory.V.Sd.EG in
theorem UpperTheory.V.Z.Sym.W.prop_eg_complex_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.W.PropEGc := by
  intro P l hl Ω _ _ _ ι c hc N w φ θ hx hs hφ
  obtain ⟨M, _, φ₀, hMN, hφp, rfl⟩ := dirOf l Ω ι N hx.pos φ hs.1
  obtain ⟨w', _, θ₀, hw, -, hθ⟩ := dirOf l Ω ι w hx.prime.pos θ hx.mu
  obtain rfl : w' = w := ((Nat.dvd_prime hx.prime).1 hw).resolve_left (dirG_ne_one (hθ ▸ hx.ne))
  haveI : NeZero N := ⟨hx.pos.ne'⟩
  haveI : NeZero (M * w') := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne w')⟩
  haveI : Fact w'.Prime := ⟨hx.prime⟩
  obtain ⟨χ, hχ⟩ := exists_mul φ₀ θ₀
  have hne : θ₀ ≠ 1 := by
    rintro rfl
    refine hx.ne (hθ.trans ?_)
    ext s
    rw [dirG_val]
    simp
  have hpow : θ₀ ^ l = 1 := by
    ext u
    obtain ⟨s, rfl⟩ := (Chr.clsOnto Ω w').1 u
    have h1 := congrArg Units.val (DFunLike.congr_fun hx.pow s)
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hθ, dirG_val] at h1
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    apply ι.symm.injective
    rw [map_pow, map_one]
    exact h1
  have hdvd : l ∣ w' - 1 := by
    have h1 : orderOf θ₀ = l := orderOf_eq_prime hpow hne
    rw [← h1, ← ZMod.card_units w']
    refine orderOf_dvd_of_pow_eq_one ?_
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hφw : φ₀ (w' : ZMod M) = 1 := by
    have hcop : w'.Coprime N := (Nat.Prime.coprime_iff_not_dvd hx.prime).2 hx.wN
    obtain ⟨s, hs1⟩ := (Chr.clsOnto Ω N).1 (ZMod.unitOfCoprime w' hcop)
    have h1 : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ ^ w' := fun ζ hζ => by
      rw [Chr.cls_spec N s ζ hζ, hs1, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod w' hζ]
    have h2 := congrArg Units.val (hs.2 s h1)
    rw [dirG_val, cls_pow (hcop.coprime_dvd_right hMN) fun ζ hζ => h1 ζ (by
      obtain ⟨d, rfl⟩ := hMN
      rw [pow_mul, hζ, one_pow])] at h2
    apply ι.symm.injective
    rw [map_one]
    exact h2
  have E : EDat l M w' φ₀ θ₀ χ :=
    ⟨hx.odd, lt_of_le_of_ne (NeZero.pos M) (dirG_ne_one hφ).symm, fun h => hx.cop (h.trans hMN), hφp, hx.prime, hdvd,
      fun h => hx.wN (h.trans hMN), hφw, hne, hpow, hχ⟩
  have hlN : ¬ l ∣ M * w' := by
    intro hd
    rcases (Nat.Prime.dvd_mul hl.out).1 hd with hd | hd
    · exact E.cop hd
    · have h1 : l ∣ w' - (w' - 1) := Nat.dvd_sub hd hdvd
      have := hx.prime.pos
      rw [show w' - (w' - 1) = 1 by omega] at h1
      exact hl.out.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨k₀, hk₀⟩ := UpperTheory.V.Z.Sym.Unl.propEC l ι M w' φ₀ θ₀ χ E
  refine ⟨max k₀ 3, fun k hk hpar => ?_⟩
  obtain ⟨g, hcj, hg⟩ := hk₀ k (le_of_max_le_left hk) (by
    have h1 := congrArg Units.val hpar
    rw [dirG_val, (Chr.clsFacts ℚ Ω M).2.2.2.1 c hc, Units.val_neg, Units.val_one] at h1
    apply ι.symm.injective
    rw [map_pow, map_neg ι.symm, map_one ι.symm]
    simpa using h1)
  suffices hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = Chr.dirG ℚ Ω (φ₀.ringHomComp ι.symm.toRingHom) * θ by
    obtain ⟨ρ, h1, h2, h3, h4⟩ := core P hx.odd ι (le_of_max_le_right hk) hlN (ePrim l M w' φ₀ θ₀ χ E) g hg hm hx.pow hcj
    exact ⟨ρ, h1, h2, h3, h4⟩
  ext s
  rw [hθ, MonoidHom.mul_apply, Units.val_mul, dirG_dvd dvd_rfl, dirG_dvd (dvd_mul_right M w'), dirG_dvd (dvd_mul_left w' M)]
  simp only [MulChar.ringHomComp_apply]
  rw [hχ, map_mul]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Sym.W.prop_eg_w_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.W.PropEGW :=
  fun P l _ Ω _ _ _ ι c hc N w φ θ h1 h2 h3 =>
    (_root_.UpperTheory.V.Z.Sym.W.prop_eg_complex_of_printed_hida P l Ω ι c hc N w φ θ h1 h2 h3).imp fun _ H k hk hp =>
      (H k hk hp).imp fun ρ hρ =>
        ⟨hρ.1, hρ.2.1, UpperTheory.V.Z.Sym.Unl.adUnl ℚ Ω l ι ρ hρ.2.2.1 hρ.2.2.2⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private UpperTheory.V.Z.Sym.W.adjoint_zero_twist from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.SeedInW
open UpperTheory.GalN.V
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix
namespace UpperTheory.V.Z.Sym.W
private theorem open_ker_of_kills {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [Group C] {M : ℕ} (hM : 0 < M)
    {f : G ℚ Ω →* C} (hf : KillsMu M f) : IsOpen (f.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hf s fun ζ hζ => hs ζ hζ
private theorem cont_of_open_ker {Γ C : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group C] [TopologicalSpace C]
    (f : Γ →* C) (h : IsOpen (f.ker : Set Γ)) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open f).2 fun x =>
    ⟨(fun y => x * y) '' (f.ker : Set Γ), (Homeomorph.mulLeft x).isOpenMap _ h, ⟨1, one_mem _, by simp⟩, ?_⟩)
  rintro _ ⟨y, hy, rfl⟩
  simp [MonoidHom.mem_ker.1 hy]
private theorem cont_twist {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} {δ : Γ →* (Qbar l)ˣ} (h : Continuous r) (hδ : Continuous δ) : Continuous (tw r δ) := by
  have hv : Continuous fun s => ((tw r δ) s).val := by
    have e : (fun s => ((tw r δ) s).val) = fun s => (δ s).val • (r s).val := funext fun s => tw_val r δ s
    rw [e]
    exact (Units.continuous_val.comp hδ).smul (Units.continuous_val.comp h)
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [Function.comp_def, ← Units.val_inv_eq_inv_val, ← map_inv]
  exact hv.comp continuous_inv
private theorem cc_mul_self {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {c : G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  refine AlgEquiv.ext fun x => j.injective ?_
  simp [AlgEquiv.mul_apply, hj]
private theorem not_lt_of_dvd {Ω : Type} [Field Ω] {l M : ℕ} (h : l ∣ M) {A : ValuationSubring Ω} (hA : ¬ A.valuation (M : Ω) < 1) :
    ¬ A.valuation (l : Ω) < 1 := fun hl => hA (by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le hl ((A.valuation_le_one_iff _).2 (natCast_mem A t)))
private theorem closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
private theorem tower_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω] (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) :
    ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := closure_of Ω L
  have h1 : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) _).2 fun f => h (galEmb_mem ℚ L Ω f) x
  choose f hf using h1
  have hi := (algebraMap L Ω).injective
  let g : K →+* L :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun a b => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun a b => hi (by simp [hf]) }
  letI := g.toAlgebra
  exact ⟨_, IsScalarTower.of_algebraMap_eq fun x => (hf x).symm⟩
private theorem gram_two {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) :
    Mᵀ * !![0, 1; -1, 0] * M = M.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pair_of {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] (ρ : Γ →* GL (Fin 2) k) (e : Δ →* Γ) (c : Γ) :
    ∃ P : GL (Fin 2) k, ∀ s s' : Δ, e s' = c * e s * c⁻¹ →
      (ρ (e s) : Matrix (Fin 2) (Fin 2) k)ᵀ * (P : Matrix (Fin 2) (Fin 2) k) * (ρ (e s') : Matrix (Fin 2) (Fin 2) k) =
        (ρ (e s) : Matrix (Fin 2) (Fin 2) k).det • (P : Matrix (Fin 2) (Fin 2) k) := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp)
  have eJ : (J : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  refine ⟨J * (ρ c)⁻¹, fun s s' h => ?_⟩
  have e1 : J * (ρ c)⁻¹ * ρ (e s') = J * ρ (e s) * (ρ c)⁻¹ := by
    rw [h, map_mul, map_mul, map_inv]; group
  have e2 : (J : Matrix (Fin 2) (Fin 2) k) * (ρ (e s) : Matrix (Fin 2) (Fin 2) k) *
      (((ρ c)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ((J * (ρ c)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (ρ (e s') : Matrix (Fin 2) (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, e1]
  rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, eJ, gram_two, Units.val_mul, eJ, Matrix.smul_mul]
private theorem cc_diff {Ω L : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω]
    {c c₁ : G ℚ Ω} (h : Sd.IsCC c) (h₁ : Sd.IsCC c₁) : c₁ * c⁻¹ ∈ galOf ℚ L Ω := by
  have key : ∀ {d : G ℚ Ω}, Sd.IsCC d → ∀ x : L, d (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
    rintro d ⟨j, hj⟩ x
    apply j.injective
    have := IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x
    rw [hj]
    exact this.symm
  intro x
  have e : (c⁻¹ : G ℚ Ω) (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
    have h2 := key h (IsCMField.complexConj L x)
    have h3 : IsCMField.complexConj L (IsCMField.complexConj L x) = x := by simp
    rw [h3] at h2
    rw [← h2]
    exact (c.symm_apply_apply _).trans rfl
  rw [AlgEquiv.mul_apply, e, key h₁]
  simp
end UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Sym.W UpperTheory.V.Z.Sym UpperTheory.V.Z.Win.Birth in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.Z.Sym.W.seedInW_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.W.SeedInW := by
  intro hH K L Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι c N w χ' η θ j D M hM hlM hU hχ' m ρ hm hρ hirr hpr hun hpar
  haveI := D.imag
  haveI := D.ab
  haveI := closure_of Ω K
  haveI : Fact ((2 : ℕ) = 2) := ⟨rfl⟩
  have hTw : UpperTheory.V.Z.Sym.TwEx := Pl.twEx (Pl.lemTWM hH.litN.aut.art) (_root_.UpperTheory.V.Af.algOfCyc_s hH)
  have hl : l.Prime := Fact.out
  have hcc := cc_mul_self D.cc
  have hθc : θ c = 1 := by
    obtain ⟨u, hu⟩ := hl.odd_of_ne_two D.aux.odd
    have h1 : θ c ^ l = 1 := by rw [← MonoidHom.pow_apply, D.aux.pow]; rfl
    have h2 : θ c * θ c = 1 := by rw [← map_mul, hcc, map_one]
    have h3 : θ c ^ (2 * u + 1) = 1 := by rw [← hu]; exact h1
    rwa [pow_succ, pow_mul, sq, h2, one_pow, one_mul] at h3
  have hηL : ∀ s ∈ galOf ℚ L Ω, η s = 1 := fun s hs => by
    rw [← MonoidHom.mem_ker, D.η_ker]; exact D.KL hs
  have hθL : ∀ s ∈ galOf ℚ L Ω, θ s = 1 := fun s hs => D.θL hs
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = χ' * η * θ := ⟨_, rfl⟩
  have hΘL : ∀ s : G L Ω, Θ (galEmb ℚ L Ω s) = χ' (galEmb ℚ L Ω s) := fun s => by
    simp [hΘ, hηL _ (galEmb_mem ℚ L Ω s), hθL _ (galEmb_mem ℚ L Ω s)]
  have hker : IsOpen (Θ.ker : Set (G ℚ Ω)) := by
    have hN := open_ker_of_kills D.aux.pos D.χ_split.1
    have hN' := open_ker_of_kills D.aux.pos D.η_split.1
    have hw := open_ker_of_kills D.aux.prime.pos D.aux.mu
    refine Subgroup.isOpen_mono (H₁ := χ'.ker ⊓ η.ker ⊓ θ.ker) ?_ ?_
    · rintro s ⟨⟨h1, h2⟩, h3⟩
      have a1 : χ' s = 1 := h1
      have a2 : η s = 1 := h2
      have a3 : θ s = 1 := h3
      simp [hΘ, MonoidHom.mem_ker, a1, a2, a3]
    · exact (hN.inter hN').inter hw
  have hkerI : IsOpen ((Θ⁻¹).ker : Set (G ℚ Ω)) := by
    have : (Θ⁻¹).ker = Θ.ker := by ext s; simp [MonoidHom.mem_ker]
    rwa [this]
  have hΘc : Θ c = (-1) ^ (m + 1) := by
    rw [hΘ, MonoidHom.mul_apply, hpar, hθc, mul_one]
  obtain ⟨κ, hκa, hκc, hκu, hκl⟩ := hTw L Ω l D.aux.odd ι c D.cc M hM hlM hU Θ⁻¹ (-((m : ℤ) + 1)) hkerI
    (by
      rw [MonoidHom.inv_apply, hΘc, zpow_neg]
      congr 1)
    (fun A hA s hs => by rw [MonoidHom.inv_apply, hΘL, hχ' A hA s hs, inv_one])
  have RL := resFacts ℚ L Ω l 2 ρ
  have RK := resFacts ℚ K Ω l 2 ρ
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (ρ s) = cycBar ℚ Ω l s ^ m * Θ s := fun s => by
    have := DFunLike.congr_fun hρ.det s
    simpa [hΘ] using this
  have hcyc : ∀ s : G L Ω, cycBar ℚ Ω l (galEmb ℚ L Ω s) = cycBar L Ω l s := fun s => DFunLike.congr_fun RL.2.2.1 s
  have hid : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ →
      Matrix.GeneralLinearGroup.det (ρ (galEmb ℚ L Ω s)) * (κ s * κ s') = (cycBar L Ω l s)⁻¹ := fun s s' h => by
    rw [hκc s s' h, hdet, hcyc, MonoidHom.inv_apply, zpow_neg]
    have e : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [e, zpow_natCast, pow_succ, mul_inv]
    generalize cycBar L Ω l s = a
    generalize Θ (galEmb ℚ L Ω s) = b
    calc a ^ m * b * ((a ^ m)⁻¹ * a⁻¹ * b⁻¹) = (a ^ m * (a ^ m)⁻¹) * (b * b⁻¹) * a⁻¹ := by ac_rfl
      _ = a⁻¹ := by simp
  have hid' : ∀ c₁ : G ℚ Ω, Sd.IsCC c₁ → ∀ s s' : G L Ω, galEmb ℚ L Ω s' = c₁ * galEmb ℚ L Ω s * c₁⁻¹ →
      Matrix.GeneralLinearGroup.det (ρ (galEmb ℚ L Ω s)) * (κ s * κ s') = (cycBar L Ω l s)⁻¹ := fun c₁ h₁ s s' h => by
    obtain ⟨u, hu⟩ : ∃ u : G L Ω, galEmb ℚ L Ω u = c₁ * c⁻¹ := by
      have h2 := cc_diff (L := L) D.cc h₁
      rw [← range_galEmb] at h2
      exact h2
    have e1 : galEmb ℚ L Ω (u⁻¹ * s' * u) = c * galEmb ℚ L Ω s * c⁻¹ := by
      rw [map_mul, map_mul, map_inv, hu, h]; group
    have e2 : κ (u⁻¹ * s' * u) = κ s' := by
      rw [map_mul, map_mul, map_inv, mul_comm (κ u)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    have h3 := hid s _ e1
    rwa [e2] at h3
  have hpr2 : ∀ c₁ : G ℚ Ω, Sd.IsCC c₁ → ∃ P, Sd.IsPair c₁ (tw (ρ.comp (galEmb ℚ L Ω)) κ) (cycBar L Ω l ^ (1 - ((2 : ℕ) : ℤ))) P := fun c₁ h₁ => by
    obtain ⟨P, hP1⟩ := pair_of ρ (galEmb ℚ L Ω) c₁
    refine ⟨P, fun s s' h => ?_⟩
    have a := hid' c₁ h₁ s s' h
    have ee : (1 - ((2 : ℕ) : ℤ)) = -1 := by norm_num
    rw [tw_val, tw_val, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, MonoidHom.comp_apply,
      MonoidHom.comp_apply, hP1 s s' h, smul_smul, smul_smul, ee, zpow_neg_one, MonoidHom.inv_apply, ← a]
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    ring
  obtain ⟨_, _⟩ := tower_of (Ω := Ω) K L D.KL
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm fun a b => mul_comm' a b
  haveI : IsAbelianGalois ℚ K := IsAbelianGalois.tower_bot ℚ K L
  haveI : IsCMField K := IsCMField.of_isAbelianGalois K
  have hiK : IsIrr (ρ.comp (galEmb ℚ K Ω)) := RK.2.2.2.1.1 (hirr _ RK.2.1)
  have hiL : IsIrr (ρ.comp (galEmb ℚ L Ω)) := RL.2.2.2.1.1 (hirr _ RL.2.1)
  have e : (ρ.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) = ρ.comp (galEmb ℚ L Ω) := MonoidHom.ext fun s => rfl
  have hA : IsAutC ι (ρ.comp (galEmb ℚ K Ω)) := _root_.UpperTheory.V.Sd.up_quad_of_printed_results hH.toClassicalTheorems ℚ K Ω l ι D.quad 2 (by norm_num) ρ hρ.cont hρ.aut hiK
  have hcK : Continuous (ρ.comp (galEmb ℚ K Ω)) := hρ.cont.comp RK.1
  have hAL := _root_.UpperTheory.V.Z.Bc.upSol_of_alt hH.toClassicalTheorems hH.cyc K L Ω l ι 2 (by norm_num) _ hcK hA (e ▸ hiL)
  rw [e] at hAL
  have hT := _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems L Ω l ι 2 _ κ hκa hAL
  have hW0 := awReal ℚ K Ω D.quad l ι ρ hρ.cont hiK hpr
  have hW1 := awUp (_root_.UpperTheory.V.Z.Bc.upCyc_of_alt hH.toClassicalTheorems hH.cyc) K L Ω l ι 2 le_rfl _ hcK hA (e ▸ hiL) hW0
  rw [e] at hW1
  have hW2 := awTw L Ω l 2 le_rfl ι _ κ hκa hAL hW1
  have hab : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      OrdAt (ρ.comp (galEmb ℚ L Ω)) ![(((m + 1 : ℕ) : ℤ)) - 1, 0]
        (fun i => (![cycBar ℚ Ω l ^ (m + 1 - 1) * (χ' * η), 1] i).comp (galEmb ℚ L Ω)) A :=
    fun A hA => RL.2.2.2.2.2.2 _ _ A (hρ.above A hA)
  have hwit : UpperTheory.V.Z.Win.WitA ι (tw (ρ.comp (galEmb ℚ L Ω)) κ) :=
    hW2.witA (potOrd L Ω l 2 _ _ _ κ (fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega) hab)
  have hunl : Unlinked (ad0 (tw (ρ.comp (galEmb ℚ L Ω)) κ)) := by
    rw [UpperTheory.V.Z.Sym.W.adjoint_zero_twist]
    exact UpperTheory.GalN.V.L.wup ℚ Ω l 3 (ad0 ρ) L hun
  refine ⟨κ, ?_⟩
  have SF := shapeFacts l (G L Ω) 2 (ρ.comp (galEmb ℚ L Ω)) κ
  have hoff : TypeAway (tw (ρ.comp (galEmb ℚ L Ω)) κ) fun i => (![1, Θ] i).comp (galEmb ℚ L Ω) * κ := by
    have h0 : TypeAway ρ ![1, Θ] := by
      rw [hΘ]; exact hρ.away
    exact fun A hA => SF.1 _ _ (RL.2.2.2.2.2.1 _ h0 A hA)
  refine ⟨cont_twist (hρ.cont.comp RL.1) hκa.1, _root_.UpperTheory.GalN.V.aut_csd_zero_of_complex_conj_pair_automorphic hH.toClassicalTheorems L Ω l ι 2 (by norm_num) _ c D.cc (hpr2 c D.cc) hT, hwit, hunl, ?_, ?_, hm, ?_, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨j', hj'⟩ := hc'
    let c₁ : G ℚ Ω := AlgEquiv.ofRingEquiv (f := c'.toRingEquiv) fun q => by simp
    obtain ⟨P, hP⟩ := hpr2 c₁ ⟨j', hj'⟩
    exact ⟨P, fun s s' h => hP s s' (AlgEquiv.ext fun x => DFunLike.congr_fun h x)⟩
  · intro H hH'
    have h1 := RL.2.2.2.2.1 hirr H hH'
    have e' : (tw (ρ.comp (galEmb ℚ L Ω)) κ).comp H.subtype =
        tw ((ρ.comp (galEmb ℚ L Ω)).comp H.subtype) (κ.comp H.subtype) := MonoidHom.ext fun s => rfl
    rw [e']
    exact (shapeFacts l _ 2 _ _).2.2.2.2.2 h1
  · intro A hA s hs
    obtain ⟨g, hg⟩ := hoff A (not_lt_of_dvd hlM hA)
    have h1 := hg s hs
    have hv : κ s = 1 := hκu A hA s hs
    have hd : (Matrix.diagonal fun i => ((((![1, Θ] i).comp (galEmb ℚ L Ω) * κ) s : (Qbar l)ˣ) : Qbar l)) = 1 := by
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hv, hΘL, hχ' A hA s hs]
    have h2 : g * (tw (ρ.comp (galEmb ℚ L Ω)) κ) s * g⁻¹ = 1 := Units.ext (h1.trans hd)
    have h3 : (tw (ρ.comp (galEmb ℚ L Ω)) κ) s = g⁻¹ * (g * (tw (ρ.comp (galEmb ℚ L Ω)) κ) s * g⁻¹) * g := by group
    rw [h3, h2]
    group
  · have hc : Continuous Θ := cont_of_open_ker Θ hker
    have h : ∀ i, Continuous (![1, Θ] i) := fun i => by
      fin_cases i
      · exact continuous_const
      · exact hc
    exact ⟨fun i => (![1, Θ] i).comp (galEmb ℚ L Ω) * κ, fun i => ((h i).comp RL.1).mul hκa.1, hoff⟩
  · intro A hA
    obtain ⟨b, k, hk, hb⟩ := hκl A hA
    obtain ⟨κ', hfl, hin, -⟩ := RL.2.2.2.2.2.2 _ _ A (hρ.above A hA)
    refine ⟨b, k, fun i => κ' i * κ.comp (Dec (F := L) A).subtype, hk, SF.2.2.1 _ _ hfl, fun s hs => ?_⟩
    have h0 : κ' 0 s = cycBar L Ω l s ^ (m : ℤ) := by simpa using hin 0 s hs
    have h1 : κ' 1 s = 1 := by simpa using hin 1 s hs
    constructor
    · change (κ' 0 s * κ s) ^ k = _
      rw [mul_pow, h0, hb _ hs, zpow_add, mul_pow, mul_comm]
    · change (κ' 1 s * κ s) ^ k = _
      rw [h1, one_mul, hb _ hs]
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Sym.W
theorem weight_compatible_descent (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility :=
  ⟨hH.toClassicalTheorems, _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT hH (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge hH.litN.aut.bc hH.litN.loc.bern)) hR,
    Z.Win.compatTOf hR Z.Win.plainRec, _root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT hH.toClassicalTheorems hR, Z.Win.plainRec, Top.descUse_of_weak hH.descU⟩
theorem adjoint_automorphy_w_of_printed_hida_window (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : AdAutW := _root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_pure_weight_adjoint_lift (_root_.UpperTheory.V.Z.Sym.W.weight_compatible_descent hH hR) (_root_.UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out hH.litN specOutS)
theorem unitary_three_automorphy_dense_of_prints_and_row (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.adjoint_lift_from_eisenstein_of_propagation (_root_.UpperTheory.V.Z.Sym.W.prop_eg_w_of_printed_hida hH) (_root_.UpperTheory.V.Z.Sym.W.seedInW_alt hH) (_root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_printed_hida_window hH hR)
theorem unitary_three_automorphy_dense_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints_and_row hH (_root_.UpperTheory.Gal.SV.rowOf' hH.litN.aut.gal)
end UpperTheory.V.Z.Sym.W
end
end
