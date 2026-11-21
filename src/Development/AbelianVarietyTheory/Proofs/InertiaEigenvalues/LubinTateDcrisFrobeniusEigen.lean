import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusLiftLubinTate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCompatibleThetaZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionSequence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusOrderOnMaxUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcrisToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

namespace GlobalTheory.SepSection

section
variable {Q K₀ : Type} (K B : Type) [Field Q] [Field K₀] [Field K] [CommRing B] [Algebra Q K₀] [Algebra Q K]
    [Algebra K₀ K] [IsScalarTower Q K₀ K] [Algebra Q B] [Algebra K₀ B] [IsScalarTower Q K₀ B]

noncomputable def push : K₀ ⊗[Q] K₀ →ₐ[Q] K ⊗[Q] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom Q K₀ K) (IsScalarTower.toAlgHom Q K₀ B)

variable (Q K₀) in

noncomputable def toBal : K ⊗[Q] B →ₐ[Q] K ⊗[K₀] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := K₀) (S := Q) (A := K) (B := B))
    ((Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := B)).restrictScalars Q)
    (fun _ _ => Commute.all _ _)

variable {K B}

end

end GlobalTheory.SepSection
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_power_series_shift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    ∀ (x : AK K), thetaK K x = 0 → ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y →
    ∃ (L' : PowerSeries ↥K.1) (u : GlobalTheory.AcrisK.BK K), OnDisc l (oK K) L' ∧
      (∀ k, PowerSeries.coeff k L' = PowerSeries.coeff (k + 1) L) ∧ Ev L' x u ∧
      y = inK K (PowerSeries.coeff 0 L) + toB K (ofA K x) * u := by
  first | exact @GlobalTheory.AcrisK.ev_shift | exact GlobalTheory.AcrisK.ev_shift | (intros; apply GlobalTheory.AcrisK.ev_shift <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisNZD

theorem eq_zero_of_smul_free {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Free R M] {a : R} (ha : a ≠ 0) {x : M} (h : a • x = 0) : x = 0 := by
  refine (Module.Free.chooseBasis R M).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis R M).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (mul_eq_zero.1 h1).resolve_left ha

theorem acris_dom (l : ℕ) [Fact l.Prime] : IsDomain (Per.Acris l) ∧ Function.Injective (aC l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1
  refine ⟨(GlobalTheory.MemLoc.crisP_injective l C.j C.j_cris).isDomain C.j, fun a b h => ?_⟩
  have h1 : C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      C.j (algebraMap (Per.Ainf l) (Per.Acris l) b) := congrArg C.j h
  rw [C.j_cris.on_ainf, C.j_cris.on_ainf] at h1
  exact (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2 (GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l h1)

variable {l : ℕ} [Fact l.Prime] (K : FinExt l)

theorem eq_zero_of_inC_mul {a : Ainf l} (ha : a ≠ 0) {z : CK K} (h : inC K (aC l a) * z = 0) : z = 0 := by
  haveI := (acris_dom l).1
  have ha' : aC l a ≠ 0 := fun h0 => ha ((acris_dom l).2 (h0.trans (map_zero _).symm))
  rw [← Algebra.smul_def] at h
  exact eq_zero_of_smul_free ha' h

theorem exists_dvd_inA {x : AK K} (hx : x ≠ 0) : ∃ N : Ainf l, N ≠ 0 ∧ ∃ w : AK K, inA K N = x * w := by
  obtain ⟨r, hr, w, hw⟩ := (IsIntegral.of_finite (Ainf l) x).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hx)
  exact ⟨r, hr, w, hw⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : AK K), x ≠ 0 → ∀ y : GlobalTheory.AcrisK.BK K,
    toB K (ofA K x) * y = 0 → y = 0 := by
  intro l _ K x hx y hy
  obtain ⟨N, hN, w, hw⟩ := exists_dvd_inA K hx
  obtain ⟨D, z, hz⟩ := exists_pow_mul y
  have h1 : toB K (ofA K x * z) = 0 := by
    rw [map_mul, ← hz, mul_left_comm, hy, mul_zero]
  have h2 : ofA K x * z = 0 := toB_injective K (h1.trans (map_zero _).symm)
  have h3 : inC K (aC l N) * z = 0 := by
    rw [← ofA_inA, hw, map_mul, mul_right_comm, h2, zero_mul]
  have h4 : z = 0 := eq_zero_of_inC_mul K hN h3
  rw [h4, map_zero] at hz
  exact ((isUnit_l K).pow D).mul_right_eq_zero.1 hz

end GlobalTheory.AcrisNZD
end
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_no_zero_divisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : AK K), x ≠ 0 → ∀ y : GlobalTheory.AcrisK.BK K,
    toB K (ofA K x) * y = 0 → y = 0 := by
  first | exact @GlobalTheory.AcrisNZD.main | exact GlobalTheory.AcrisNZD.main | (intros; apply GlobalTheory.AcrisNZD.main <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisK

theorem exists_thetaB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ ψ : GlobalTheory.AcrisK.BK K →+* ℂ_[l],
    ∀ x : AK K, ψ (toB K (ofA K x)) = ((thetaK K x : OC l) : ℂ_[l]) := by
  intro l _ K
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  let v : ↥K.1 →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp K.1.val.toRingHom
  have h : ∀ w : W0 K, ((Per.θD l).comp C.j) (aC l (wA l (fK K) w)) = v (oK K (thetaW (fK K) K w)) := by
    intro w
    rw [RingHom.comp_apply, GlobalTheory.MemLoc.FundOnto.theta_j_alg]
    change _ = ((intToOC K (thetaW (fK K) K w) : OC l) : ℂ_[l])
    rw [intToOC_thetaW]
  refine ⟨liftB ((Per.θD l).comp C.j) v h, fun x => ?_⟩
  have e := AinfK.ringHom_ext (u := ((liftB ((Per.θD l).comp C.j) v h).comp (toB K)).comp (ofA K))
    (v := (Subring.subtype _).comp (thetaK K)) (fun a => by
      simp only [RingHom.comp_apply]
      rw [ofA_inA, liftB_inC, RingHom.comp_apply, GlobalTheory.MemLoc.FundOnto.theta_j_alg, thetaK_inA]
      rfl) (fun c => by
      simp only [RingHom.comp_apply]
      rw [ofA_inO, ← inK_oK, liftB_inK, thetaK_inO]
      rfl)
  exact RingHom.congr_fun e x

end GlobalTheory.AcrisK
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_extension_to_complete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ ψ : GlobalTheory.AcrisK.BK K →+* ℂ_[l],
    ∀ x : AK K, ψ (toB K (ofA K x)) = ((thetaK K x : OC l) : ℂ_[l]) := by
  atlas_forward_decl GlobalTheory.AcrisK.exists_thetaB
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

namespace GlobalTheory.WittCompat

theorem u_eq_aB (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (c : ↥(MaximalUnramifiedExtension l))
    (hw : ((Per.θ l (wA l a w) : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (c : Om l)) :
    C.u c = Per.aB l (wA l a w) := by
  have ho := GlobalTheory.SeedSec.o_eq_aDp_wA l a C w (c : Om l) hw
  apply (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.2.1
  have hB : C.ι (Per.aB l (wA l a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l a w)
  rw [hB, ← ho, C.ι_u]

theorem exists_unramified_witt_element : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (w : W0 K),
    ∃ c : ↥(K0 K), algebraMap ↥(K0 K) ↥K.1 c = oK K (thetaW (fK K) K w) ∧
      algebraMap ↥(K0 K) P.R.B c = T.eB.symm (Per.aB l (wA l (fK K) w)) := by
  intro l _ P AI T K w
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have h1 : ((Per.θ l (wA l (fK K) w) : Per.OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) :=
    (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) K w)).symm
  have h2 : ((Per.θ l (wA l (fK K) w) : Per.OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (GlobalTheory.TameFrob.iotaO l (fK K) w) :=
    (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) (unrExt l (fK K)) w)).symm
  have h3 : ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) = GlobalTheory.TameFrob.iotaO l (fK K) w :=
    (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans h2)
  have hm : ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) ∈ K0 K := by
    rw [h3, ← Kunr_fK K]
    exact GlobalTheory.TameFrob.iotaO_mem l (fK K) w
  refine ⟨⟨_, hm⟩, Subtype.ext rfl, ?_⟩
  rw [RingEquiv.eq_symm_apply]
  exact (hC.u ⟨_, hm.2⟩).trans (u_eq_aB l (fK K) C w ⟨_, hm.2⟩ h1)

end GlobalTheory.WittCompat
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrisInj

theorem li_of_frac {W O F L ι : Type*} [CommRing W] [IsDomain W] [CommRing O] [Algebra W O] [Field F] [Field L]
    [Algebra F L] (o : O →+* L) (ho : Function.Injective o) (hW : Function.Injective (algebraMap W O))
    (hfrac : ∀ y : F, ∃ w s : W, s ≠ 0 ∧ algebraMap F L y * o (algebraMap W O s) = o (algebraMap W O w))
    (v : ι → O) (hv : LinearIndependent W v) : LinearIndependent F fun i => o (v i) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  choose w d hd h using hfrac
  have h1 : ∑ k ∈ s, (w (g k) * ∏ m ∈ s.erase k, d (g m)) • v k = 0 := ho (by
    rw [map_zero, map_sum, ← mul_zero (o (algebraMap W O (∏ m ∈ s, d (g m)))), ← hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.mul_prod_erase s _ hk, Algebra.smul_def, Algebra.smul_def]
    simp only [map_mul]
    rw [← h]
    ring)
  have h2 : w (g i) = 0 :=
    (mul_eq_zero.1 (hv s _ h1 i hi)).resolve_right (Finset.prod_ne_zero_iff.2 fun m _ => hd _)
  have h3 := h (g i)
  rw [h2, map_zero, map_zero] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact (algebraMap F L).injective (h4.trans (map_zero _).symm)
  · exact absurd (hW (ho (h4.trans (by rw [map_zero, map_zero])))) (hd _)

theorem eq_zero_of_sum_tmul {F V B ι : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup B] [Module F B]
    [Fintype ι] {v : ι → V} (hv : LinearIndependent F v) {β : ι → B} (h : ∑ i, v i ⊗ₜ[F] β i = 0) (i : ι) :
    β i = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply i : (ι →₀ F) →ₗ[F] F).comp hv.repr)
  have h1 : ∀ k, φ (v k) = (Finsupp.single k (1 : F)) i := fun k => by
    have hm : v k ∈ Submodule.span F (Set.range v) := Submodule.subset_span ⟨k, rfl⟩
    have := LinearMap.congr_fun hφ ⟨v k, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hv.repr_eq_single k ⟨v k, hm⟩ rfl] at this
    exact this
  have h2 := congrArg (fun x => TensorProduct.lid F B (φ.rTensor B x)) h
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, map_zero, Finsupp.single_apply] at h2
  simpa using h2

theorem exists_coord {W A O ι : Type*} [CommRing W] [CommRing A] [CommRing O] [Algebra W A] [Algebra W O]
    [Fintype ι] (b : Module.Basis ι W O) (z : A ⊗[W] O) : ∃ a : ι → A, z = ∑ i, a i ⊗ₜ[W] b i := by
  refine ⟨fun i => (Algebra.TensorProduct.basis A b).repr z i, ?_⟩
  conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem injective_abstract {A O C S F L B ι : Type*} [CommRing A] [CommRing O] [CommRing C] [CommRing S] [Field F]
    [Field L] [Algebra F L] [CommRing B] [Algebra F B] [Fintype ι] (p : A →+* C) (q : O →+* C) (t : C →+* S)
    (o : O →+* L) (κ : L →+* S) (hκ : ∀ c, κ (o c) = t (q c)) (v : ι → O)
    (hv : LinearIndependent F fun i => o (v i)) (hC : ∀ z : C, ∃ a : ι → A, z = ∑ i, p (a i) * q (v i))
    (u : S) (hu : IsUnit u) (hS : ∀ y : S, ∃ (D : ℕ) (z : C), u ^ D * y = t z) (j : A →+* B)
    (hj : Function.Injective j) (Λ : S →+* L ⊗[F] B) (h1 : ∀ c, Λ (κ c) = c ⊗ₜ[F] (1 : B))
    (h2 : ∀ a, Λ (t (p a)) = (1 : L) ⊗ₜ[F] j a) : Function.Injective Λ := by
  refine (injective_iff_map_eq_zero Λ).2 fun y hy => ?_
  obtain ⟨D, z, hz⟩ := hS y
  obtain ⟨a, rfl⟩ := hC z
  have h3 := congrArg Λ hz
  rw [map_mul, hy, mul_zero, map_sum, map_sum] at h3
  simp only [map_mul, ← hκ, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
  have h4 : ∀ i, a i = 0 := fun i => hj ((eq_zero_of_sum_tmul hv h3.symm i).trans (map_zero j).symm)
  simp only [h4, map_zero, zero_mul, Finset.sum_const_zero] at hz
  exact (hu.pow D).mul_right_eq_zero.1 hz

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem coe_thetaW (w : W0 K) :
    ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) = GlobalTheory.TameFrob.iotaO l (fK K) w :=
  (algebraMap (Om l) ℂ_[l]).injective
    (congrArg Subtype.val ((intToOC_thetaW _ K w).trans (intToOC_thetaW _ (unrExt l (fK K)) w).symm))

theorem exists_frac (y : ↥(K0 K)) : ∃ w s : W0 K, s ≠ 0 ∧
    algebraMap ↥(K0 K) ↥K.1 y * oK K (algebraMap (W0 K) ↥(OL K) s) = oK K (algebraMap (W0 K) ↥(OL K) w) := by
  have hy : (y : Om l) ∈ Kunr l (fK K) := by rw [Kunr_fK]; exact y.2
  obtain ⟨w, s, hs, h⟩ := GlobalTheory.TameFrob.exists_frac l (fK K) ⟨y, hy⟩
  refine ⟨w, s, hs, Subtype.ext ?_⟩
  rw [← coe_thetaW, ← coe_thetaW] at h
  exact h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (B : Type) [CommRing B] [Algebra ↥(K0 K) B] (j : Per.Acris l →+* B),
    Function.Injective j → ∀ Λ : GlobalTheory.AcrisK.BK K →+* ↥K.1 ⊗[↥(K0 K)] B,
    (∀ c : ↥K.1, Λ (inK K c) = c ⊗ₜ[↥(K0 K)] (1 : B)) →
    (∀ a : Per.Acris l, Λ (toB K (inC K a)) = (1 : ↥K.1) ⊗ₜ[↥(K0 K)] j a) → Function.Injective Λ := by
  intro l _ K B _ _ j hj Λ h1 h2
  exact injective_abstract (inC K) (inI K) (toB K) (oK K) (inK K) (inK_oK K)
    (Module.Free.chooseBasis (W0 K) ↥(OL K))
    (li_of_frac (W := W0 K) (oK K) (IsFractionRing.injective ↥(OL K) ↥K.1) (thetaW_injective K) (exists_frac K) _
      (Module.Free.chooseBasis (W0 K) ↥(OL K)).linearIndependent)
    (fun z => (exists_coord (A := Per.Acris l) (Module.Free.chooseBasis (W0 K) ↥(OL K)) z).imp fun a ha =>
      ha.trans (Finset.sum_congr (M := CK K) rfl fun i _ => GlobalTheory.AcrisK.tmul_eq K _ _))
    (l : GlobalTheory.AcrisK.BK K) (isUnit_l K) exists_pow_mul j hj Λ h1 h2

end GlobalTheory.CrisInj
end
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PZ.ColmezVec

theorem ev_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    PowerSeries.constantCoeff L = 0 → PowerSeries.coeff 1 L = 1 → ∀ (x : AK K), thetaK K x = 0 → x ≠ 0 →
    ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y → y ≠ 0 := by
  intro l _ K L hL h0 h1 x hx hx0 y hy e
  obtain ⟨L', u, hL', hc, hu, hyu⟩ := GlobalTheory.T.evaluation_power_series_shift l K L hL x hx y hy
  obtain ⟨L'', u', -, -, -, hu'⟩ := GlobalTheory.T.evaluation_power_series_shift l K L' hL' x hx u hu
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.theta_extension_to_complete l K
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero, zero_add, e] at hyu
  have h2 := congrArg ψ hu'
  rw [GlobalTheory.T.period_ring_no_zero_divisors l K x hx0 u hyu.symm, hc, zero_add, h1, map_zero, map_one, map_add, map_one, map_mul, hψ, hx] at h2
  simp at h2

theorem exists_period (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l)
    (h : LTData K χ π z) : ∃ t : GlobalTheory.AcrisK.BK K, t ≠ 0 ∧ frobB K t = inK K (π : ↥K.1) * t ∧
      ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  obtain ⟨hπ, hF, v, hv0, hv1, hv, hg⟩ := GlobalTheory.T.lubin_tate_torsion_sequence l K χ π z h
  have hπu := GlobalTheory.LTTilt.not_isUnit_intToOC K hπ
  have hcomp : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ Ideal.span {intToOC K π} := fun n =>
    Ideal.mem_span_singleton.2 ⟨-v (n + 1), by rw [← hv n]; ring⟩
  obtain ⟨x, hx, -⟩ := GlobalTheory.LTTilt.existsUnique_isTiltOf (fK K) (NeZero.pos _) (intToOC K π) hπu
    (GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ) v hcomp
  obtain ⟨ω₀, hred, hω₀⟩ := GlobalTheory.T.exists_frobenius_lift_lubin_tate l K π hπ x
  choose r hr using (frobq_bijective K).2
  let ω : ℕ → AK K := fun n => r^[n] ω₀
  have hch : ∀ n, frobq K (ω (n + 1)) = ω n := fun n => by
    simp only [ω, Function.iterate_succ_apply', hr]
  have hθ : ∀ n, thetaK K (ω n) = v n := GlobalTheory.T.theta_of_tilt_compatible_sequence l K π hπ v ω hv (hred ▸ hx) hch hω₀
  have h0 : thetaK K ω₀ = 0 := (hθ 0).trans hv0
  have hne : ω₀ ≠ 0 := fun e => hv1 (by
    have : ω 1 = 0 := (frobq_bijective K).1 (by rw [hch, map_zero]; exact e)
    rw [← hθ, this, map_zero])
  have hker : ∀ (M : ℕ) (y : AK K), ω₀ ^ M ∣ y → y ∈ RingHom.ker (thetaK K) ^ M := fun M y ⟨c, hc⟩ =>
    hc ▸ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (show ω₀ ∈ RingHom.ker (thetaK K) from h0) M)
  have hev := ev_ltLog hπ hF ω₀ h0
  refine ⟨ltLog hπ hF ω₀ h0, ev_ne_zero l K _ (onDisc_log hπ hF) (GlobalTheory.LTLog.constantCoeff_log _ hπ hF)
    (GlobalTheory.LTLog.coeff_one_log _ hπ hF) ω₀ h0 hne _ hev, ?_, fun g => ?_⟩
  · refine ev_log_self hπ hF h0 (fun n => hker n _ ?_) hev.frob
    have hq : resCard K = l ^ fK K := rfl
    have e : ∀ j, inO K (PowerSeries.coeff j (ltSeries K π)) * ω₀ ^ j =
        (if j = 1 then inO K π * ω₀ ^ j else 0) + if j = l ^ fK K then ω₀ ^ j else 0 := fun j => by
      rw [ltSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, hq]
      split_ifs <;> simp [add_mul]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, hω₀]
    rw [add_sub_add_comm]
    refine dvd_add ?_ ?_
    · split_ifs with h1
      · simp
      · rw [sub_zero]
        exact Dvd.dvd.mul_left (by simpa using pow_dvd_pow ω₀ (not_lt.1 h1)) _
    · split_ifs with h1
      · simp
      · rw [sub_zero]
        exact pow_dvd_pow ω₀ (not_lt.1 h1)
  · obtain ⟨a, ha, hs⟩ := hg g
    obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.T.exists_compatible_power_series_value l K ω (lubinTateHom hπ hF hF a).toPowerSeries
      (fun n => Per.σO (g : GQ l) (v n)) hch
      (fun n => by rw [hθ]; exact GlobalTheory.LTTilt.norm_lt_one_of_compat K hπ hcomp hv0 n)
      (fun n => by rw [hθ]; exact hs n)
    have hy : gal K g ω₀ = y 0 := sub_eq_zero.1 (GlobalTheory.T.frobenius_compatible_theta_zero l K (fun n => gal K g (ω n) - y n)
      (fun n => by rw [map_sub, hy1, ← gal_frobq, hch])
      (fun n => by rw [map_sub, hy2, thetaK_gal, hθ, sub_self]))
    rw [← ha]
    exact ev_log_hom hπ hF a h0 (fun n => hker n _ (hy ▸ hy3 n)) (hev.gal g)

section Abstract

variable {G : Type} [Group G] {Q K₀ K : Type} [Field Q] [Field K₀] [Field K]
    [Algebra Q K₀] [Algebra Q K] [Algebra K₀ K] [IsScalarTower Q K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Q B] [Algebra K₀ B] [IsScalarTower Q K₀ B]
    [Algebra Q BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Q K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Q K₀ BdR]
    (PD : PeriodData G Q K₀ K B BdR)

theorem pow_phi_algebraMap (k : ℕ) (c : K₀) : (PD.φ ^ k) (algebraMap _ B c) = algebraMap _ B ((⇑PD.σ)^[k] c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, ih, PD.φ_K₀, Function.iterate_succ_apply']

def phiPow (f : ℕ) (hσ : ∀ c, (⇑PD.σ)^[f] c = c) : B →ₐ[K₀] B where
  toRingHom := (PD.φ ^ f).toRingHom
  commutes' := fun c => (pow_phi_algebraMap PD _ c).trans (congrArg _ (hσ c))

end Abstract

theorem ext_BK {l : ℕ} [Fact l.Prime] {K : FinExt l} {S : Type} [CommRing S] (u v : GlobalTheory.AcrisK.BK K →+* S)
    (hK : ∀ c, u (inK K c) = v (inK K c)) (hA : ∀ a, u (toB K (inC K a)) = v (toB K (inC K a))) : u = v := by
  refine ringHom_extB fun c => ?_
  refine RingHom.congr_fun (GlobalTheory.AcrisK.ringHom_ext (u := u.comp (toB K)) (v := v.comp (toB K)) hA fun c => ?_) c
  simp only [RingHom.comp_apply, ← inK_oK, hK]

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K : FinExt l)

theorem pow_phi_acris (k : ℕ) (a : Per.Acris l) :
    ((P.PD K).φ ^ k) (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(phiA l))^[k] a)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, Function.iterate_succ_apply', P.PD_φ]
    apply T.eB.injective
    rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← plusToB_alg, ← plusToB_alg,
      ← plusToB_phi, phiP_alg]

theorem act_acris (g : ↥(GK K)) (a : Per.Acris l) :
    (P.PD K).actB g (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) a)) := by
  apply T.eB.injective
  rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, ← plusToB_alg, ← plusToB_alg,
    ← plusToB_sig, sigP_alg]

end Tied

end GlobalTheory.PZ.ColmezVec

end
end
