import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateCharpoly
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFrobenius
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldArtin
import GroundTheory.GlobalFields.WeilGroups.SignSymbol
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformizationClassification

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

section VC

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem homPt_vcHom (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    homPt (vcHom C hC) R = vcPoint C hC R := by
  have h0 : vcHom C hC ≠ 0 := fun h ↦ vcPt_ne_zero C hC (congrArg Subtype.val h)
  rw [homPt, dif_neg h0, Isogeny.pointHom_apply]
  exact pointMap_eq_vcPoint C hC _ (isogOfHom_val _ h0) R

variable {A' B' : WeierstrassCurve F} [A'.IsElliptic] [B'.IsElliptic]

theorem homConstSet_conj (V : VariableChange F) (hV : V • A = B) (V' : VariableChange F)
    (hV' : V' • A' = B') :
    (homConstSet A A' : Set F) =
      ((homConst B' A' (vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')) *
        homConst A B (vcHom V hV)) * ·) '' homConstSet B B' := by
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set Q' := vcHom V⁻¹ (inv_smul_eq_of_smul_eq V hV)
  set R' := vcHom V' hV'
  have e1 : homConst B A Q' * homConst A B Q = 1 := homConst_vcHom_mul_inv V hV
  have e2 : homConst B' A' R * homConst A' B' R' = 1 := homConst_vcHom_mul_inv V' hV'
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst A' B' R' * z * homConst B A Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination (homConst A B Q * homConst B A Q' * z) * e2 + z * e1
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end VC

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

theorem latticeEnd_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    latticeEnd L = latticeEnd L' := by
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔ (∀ l ∈ L'.lattice, α * l ∈ L'.lattice)
  rw [h]

include hK in

theorem latticeEnd_eq_cmRing_of_lattice_eq {L : PeriodPair} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : L.lattice = idealLattice σ₀ 𝔞) : latticeEnd L = cmRing σ₀ := by
  rw [latticeEnd_eq_of_lattice_eq (L' := idealPeriodPair σ₀ hK 𝔞)
    (h.trans (lattice_idealPeriodPair σ₀ hK 𝔞).symm), latticeEnd_idealPeriodPair]

include hK in

theorem exists_unit_of_forall_mem_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℂ}
    (hc : ∀ z, z ∈ idealLattice σ₀ J ↔ c * z ∈ idealLattice σ₀ J) :
    ∃ ε : (𝓞 K)ˣ, c = σ₀ (algebraMap (𝓞 K) K ε) := by
  have hP := lattice_idealPeriodPair σ₀ hK J
  have hPend := latticeEnd_idealPeriodPair σ₀ hK J
  have hne : ∃ z, z ∉ idealLattice σ₀ J := by
    by_contra h
    push Not at h
    have h1 : (Real.sqrt 2 : ℂ) * (idealPeriodPair σ₀ hK J).ω₁ ∉ (idealPeriodPair σ₀ hK J).lattice :=
      sqrt_two_mul_notMem _
    rw [hP] at h1
    exact h1 (h _)
  obtain ⟨z₀, hz₀⟩ := hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hz₀ ((hc z₀).2 (by rw [zero_mul]; exact zero_mem _))
  have mult : ∀ d : ℂ, (∀ l ∈ idealLattice σ₀ J, d * l ∈ idealLattice σ₀ J) → d ∈ cmRing σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    exact hd l hl
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c fun l hl ↦ (hc l).1 hl)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ fun l hl ↦ (hc _).2 (by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; exact hl))
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc0])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

include hK in

theorem exists_unit_pointMap_vcPoint (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair)
    (hL : L.lattice = idealLattice σ₀ 𝔞) (hL' : L'.lattice = idealLattice σ₀ ↑(𝔟 * 𝔞))
    {A A' : WeierstrassCurve ℂ} [A.IsElliptic] [A'.IsElliptic]
    (V : VariableChange ℂ) (hV : V • weierstrassCurve L = A)
    (V' : VariableChange ℂ) (hV' : V' • weierstrassCurve L' = A') (φ : Isogeny A A')
    (hφ : (homConstSet A A' : Set ℂ) = (invConst φ * ·) '' idealLattice σ₀ 𝔟) :
    ∃ u : (𝓞 K)ˣ, ∀ z : ℂ, φ.pointMap (vcPoint V hV (toPoint L z)) =
      vcPoint V' hV' (toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z)) := by
  classical
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set c := homConst A' (weierstrassCurve L') R * homConst (weierstrassCurve L) A Q
  have hset := homConstSet_conj V hV V' hV'

  set Φ := homComp R (homComp φ.toHom Q)
  have hΦ : homConst _ _ Φ = c * invConst φ := by
    rw [homConst_homComp, homConst_homComp, homConst_toHom]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    have e := homConst_vcHom_mul_inv V' hV'
    have e' := homConst_vcHom_mul_inv V hV
    simp only [c, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_mul] at e; exact zero_ne_one e
    · rw [h0, mul_zero] at e'; exact zero_ne_one e'
  have hΦ0 : Φ ≠ 0 := by
    intro h
    have := congrArg (homConst _ _) h
    rw [hΦ, map_zero] at this
    exact mul_ne_zero hc0 (invConst_ne_zero φ) this
  set ψ := isogOfHom Φ hΦ0
  have hψc : invConst ψ = c * invConst φ := by
    rw [← homConst_toHom, isogOfHom_toHom, hΦ]
  have hLend := latticeEnd_eq_cmRing_of_lattice_eq σ₀ hK hL
  have hL'' : L'.lattice = idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ * L.lattice := by
    rw [hL', inv_inv, hL, Units.val_mul, idealLattice_mul]
  have hψ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst ψ * ·) '' idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ := by
    rw [inv_inv, hset, hφ, Set.image_image, hψc]
    congr 1
    funext x
    ring
  obtain ⟨u, -, hu⟩ := exists_unit_of_homConstSet_eq σ₀ hK L L' hLend 𝔟⁻¹ hL'' ψ hψ
  refine ⟨u, fun z ↦ ?_⟩
  have h1 := hu z
  rw [isogOfHom_toHom, TateCharpoly.homPt_homComp, TateCharpoly.homPt_homComp, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, homPt_vcHom, homPt_vcHom, homPt_toHom, Isogeny.pointHom_apply] at h1
  have h2 := congrArg (vcPoint V' hV') h1
  rwa [vcPoint_vcPoint_of_eq_inv V'⁻¹ V' (inv_inv V').symm] at h2

end Lattice

end

end Elliptic
end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem le_one_of_forall_count_nonneg {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ count K v I) : I ≤ 1 := by
  rw [← finprod_heightOneSpectrum_factorization' (K := K) hI]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb ↦ ?_) fun v ↦ ?_
  · calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ = b := one_mul b
      _ ≤ 1 := hb
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← coeIdeal_pow]
    exact coeIdeal_le_one

theorem le_iff_forall_count_le {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 K), count K v J ≤ count K v I := by
  refine ⟨fun h v ↦ count_mono K v hI h, fun h ↦ ?_⟩
  have hJ' : J⁻¹ ≠ 0 := inv_ne_zero hJ
  have hle : I * J⁻¹ ≤ 1 := le_one_of_forall_count_nonneg (mul_ne_zero hI hJ') fun v ↦ by
    rw [count_mul K v hI hJ', count_inv]
    linarith [h v]
  calc I = I * J⁻¹ * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := mul_le_mul_left hle J
    _ = J := one_mul J

theorem mem_iff_forall_valuation_le {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x ≤ exp (-count K v I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact iff_of_true (FractionalIdeal.zero_mem I) fun v ↦ by simp only [map_zero, _root_.zero_le]
  have hs : spanSingleton (𝓞 K)⁰ x ≠ 0 := spanSingleton_ne_zero_iff.2 hx
  rw [← spanSingleton_le_iff_mem, le_iff_forall_count_le hs hI]
  refine forall_congr' fun v ↦ ?_
  have hv : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [count_spanSingleton v hx, le_neg, ← log_le_iff_le_exp hv]

theorem le_exp_sub_one_of_lt {y : ℤᵐ⁰} {n : ℤ} (h : y < exp n) : y ≤ exp (n - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_le
  rw [← log_le_iff_le_exp hy]
  have := (log_lt_iff_lt_exp hy).2 h
  omega

theorem exists_mem_valuation_eq {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : ∃ a ∈ I, v.valuation K a = exp (-count K v I) := by
  set P : FractionalIdeal (𝓞 K)⁰ K := (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) with hPdef
  have hP : P ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have hIP : I * P ≠ 0 := mul_ne_zero hI hP
  have hne : ¬ I ≤ I * P := fun h ↦ by
    have := count_mono K v hI h
    rw [count_mul K v hI hP, hPdef, count_self] at this
    omega
  obtain ⟨a, haI, haIP⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨a, haI, le_antisymm ((mem_iff_forall_valuation_le hI).1 haI v) ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  apply haIP
  rw [mem_iff_forall_valuation_le hIP]
  intro w
  rw [count_mul K w hI hP]
  by_cases hw : w = v
  · subst hw
    rw [hPdef, count_self, show -(count K w I + 1) = -count K w I - 1 by ring]
    exact le_exp_sub_one_of_lt hlt
  · rw [hPdef, count_maximal_coprime K w (Ne.symm hw), add_zero]
    exact (mem_iff_forall_valuation_le hI).1 haI w

def localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Submodule.span _ ((fun x : K ↦ (x : v.adicCompletion K)) '' (I : Set K))

theorem coe_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (v : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ∈ I) : (x : v.adicCompletion K) ∈ localIdeal I v :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem mem_localIdeal_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal I v ↔ Valued.v y ≤ exp (-count K v I) := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ ↦ Valued.v y ≤ exp (-count K v I)) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [valuedAdicCompletion_eq_valuation']
      exact (mem_iff_forall_valuation_le hI).1 hx v
    · simp only [map_zero, _root_.zero_le]
    · intro a b _ _ ha hb
      exact (Valuation.map_add _ a b).trans (max_le ha hb)
    · intro r a _ ha
      change Valued.v ((r : v.adicCompletion K) * a) ≤ _
      rw [map_mul]
      exact (mul_le_of_le_one_left' r.2).trans ha
  · intro hy
    obtain ⟨a, haI, ha⟩ := exists_mem_valuation_eq hI v
    have ha' : Valued.v (a : v.adicCompletion K) = exp (-count K v I) := by
      rw [valuedAdicCompletion_eq_valuation', ha]
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h
      rw [h, map_zero] at ha'
      exact exp_ne_zero ha'.symm
    have hr : y / a ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, ha']
      exact div_le_one_of_le₀ hy _root_.zero_le
    have hy' : y = (⟨y / a, hr⟩ : v.adicCompletionIntegers K) • (a : v.adicCompletion K) := by
      change y = y / a * a
      rw [div_mul_cancel₀ _ ha0]
    rw [hy']
    exact Submodule.smul_mem _ _ (coe_mem_localIdeal v haI)

theorem mem_iff_forall_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K), (x : v.adicCompletion K) ∈ localIdeal I v := by
  rw [mem_iff_forall_valuation_le hI]
  refine forall_congr' fun v ↦ ?_
  rw [mem_localIdeal_iff hI, valuedAdicCompletion_eq_valuation']

theorem mem_localIdeal_one_iff (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) v ↔ y ∈ v.adicCompletionIntegers K := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simpa only [Units.val_one] using (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero
  rw [mem_localIdeal_iff h1, count_one, neg_zero, exp_zero, mem_adicCompletionIntegers]


theorem eventually_coe_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    ∀ᶠ v in Filter.cofinite, (x : v.adicCompletion K) ∈ localIdeal I v := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, count K v I = 0 :=
    FractionalIdeal.finite_factors (K := K) I
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) x).2
  filter_upwards [h1, h2] with v hv1 hv2
  rw [mem_localIdeal_iff hI, hv1, neg_zero, exp_zero]
  exact hv2

namespace IdeleGroup

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

theorem valued_eq_exp_neg_ord (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) :
    Valued.v ((s : 𝔸[K]).2 v) = exp (-ord v s) := by
  rw [ord, neg_neg, exp_log (valued_ne_zero v s)]

theorem component_ne_zero (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) :
    (s : 𝔸[K]).2 v ≠ 0 :=
  (Valuation.ne_zero_iff _).1 (valued_ne_zero v s)

instance : MulAction (IdeleGroup K) 𝓘 where
  smul s I := toFractionalIdeal s * I
  one_smul I := by
    change toFractionalIdeal 1 * I = I
    rw [map_one, one_mul]
  mul_smul s t I := by
    change toFractionalIdeal (s * t) * I = toFractionalIdeal s * (toFractionalIdeal t * I)
    rw [map_mul, mul_assoc]

theorem smul_def (s : IdeleGroup K) (I : 𝓘) : s • I = toFractionalIdeal s * I :=
  rfl


instance : IsScalarTower (IdeleGroup K) 𝓘 𝓘 :=
  ⟨fun s I J ↦ by simp only [smul_def, smul_eq_mul, mul_assoc]⟩

instance : SMulCommClass (IdeleGroup K) 𝓘 𝓘 :=
  ⟨fun s I J ↦ by simp only [smul_def, smul_eq_mul, mul_left_comm]⟩


theorem count_smul (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) (I : 𝓘) :
    count K v ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [smul_def, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
    count_toFractionalIdeal]


instance : MulAction.IsPretransitive (IdeleGroup K) 𝓘 :=
  ⟨fun I J ↦ by
    obtain ⟨s, hs⟩ := toFractionalIdeal_surjective (J * I⁻¹)
    exact ⟨s, by rw [smul_def, hs, inv_mul_cancel_right]⟩⟩


theorem smul_eq_self_iff {s : IdeleGroup K} {I : 𝓘} :
    s • I = I ↔ s ∈ standardOpenSubgroup K := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, smul_def, mul_eq_right]

theorem stabilizer_eq (I : 𝓘) :
    MulAction.stabilizer (IdeleGroup K) I = standardOpenSubgroup K := by
  ext s
  exact smul_eq_self_iff

theorem diagonal_smul (a : Kˣ) (I : 𝓘) :
    diagonal K a • I = toPrincipalIdeal (𝓞 K) K a * I := by
  rw [smul_def, toFractionalIdeal_diagonal]

theorem coe_diagonal_smul (a : Kˣ) (I : 𝓘) :
    ((diagonal K a • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (a : K) * I := by
  rw [diagonal_smul, Units.val_mul, coe_toPrincipalIdeal]

theorem localIdeal_smul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  ext y
  rw [mem_localIdeal_iff (Units.ne_zero _), Submodule.mem_map, count_smul]
  have ht := component_ne_zero v s
  constructor
  · intro hy
    refine ⟨((s : 𝔸[K]).2 v)⁻¹ * y, ?_, ?_⟩
    · rw [mem_localIdeal_iff (Units.ne_zero _), map_mul, map_inv₀, valued_eq_exp_neg_ord]
      calc (exp (-ord v s))⁻¹ * Valued.v y
          ≤ (exp (-ord v s))⁻¹ * exp (-(ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K))) :=
            mul_le_mul_right hy _
        _ = exp (-count K v (I : FractionalIdeal (𝓞 K)⁰ K)) := by
            rw [← exp_neg, neg_neg, ← exp_add]
            congr 1
            ring
    · rw [LinearMap.mulLeft_apply, mul_inv_cancel_left₀ ht]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_localIdeal_iff (Units.ne_zero _)] at hz
    rw [LinearMap.mulLeft_apply, map_mul, valued_eq_exp_neg_ord, neg_add, exp_add]
    exact mul_le_mul_right hz _

end IdeleGroup

end

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_sub_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ k : K, ∀ v : HeightOneSpectrum (𝓞 K), a v - (k : v.adicCompletion K) ∈ localIdeal I v := by
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.2 hI)
  obtain ⟨k', hk'⟩ := exists_sub_mem_integralFiniteAdeles
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) d⁻¹ * a)
  refine ⟨d * k', fun v ↦ ?_⟩
  have ht : ((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K) ∈
      v.adicCompletionIntegers K :=
    (mem_integralFiniteAdeles.1 hk') v
  have h1 : (d : v.adicCompletion K) * ((d⁻¹ : K) : v.adicCompletion K) = 1 := by
    rw [← adicCompletion.coe_mul, mul_inv_cancel₀ hd0, adicCompletion.coe_one]
  have h : a v - ((d * k' : K) : v.adicCompletion K) =
      (⟨_, ht⟩ : v.adicCompletionIntegers K) • (d : v.adicCompletion K) := by
    change _ = (((d⁻¹ : K) : v.adicCompletion K) * a v - (k' : v.adicCompletion K)) *
      (d : v.adicCompletion K)
    rw [adicCompletion.coe_mul]
    linear_combination -(a v) * h1
  rw [h]
  exact Submodule.smul_mem _ _ (coe_mem_localIdeal v hdI)

def dfinsuppOfFinite {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i :=
  ⟨f, Trunc.mk ⟨hf.toFinset.val, fun i ↦ by
    by_cases h : f i = 0
    · exact Or.inr h
    · left
      rw [Finset.mem_val]
      exact hf.mem_toFinset.2 h⟩⟩

@[simp]
theorem dfinsuppOfFinite_apply {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) (i : ι) : dfinsuppOfFinite f hf i = f i :=
  rfl

instance (v : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  adicCompletion.instIsScalarTower' (𝓞 K) K v

abbrev LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :=
  v.adicCompletion K ⧸ localIdeal I v

def toLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    K →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun x := dfinsuppOfFinite (fun v ↦ Submodule.Quotient.mk (x : v.adicCompletion K))
    (Filter.eventually_cofinite.1 ((eventually_coe_mem_localIdeal hI x).mono fun v hv ↦
      (Submodule.Quotient.mk_eq_zero _).2 hv))
  map_add' x y := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [DirectSum.add_apply]
    change Submodule.Quotient.mk ((x + y : K) : v.adicCompletion K) =
      Submodule.Quotient.mk (x : v.adicCompletion K) + Submodule.Quotient.mk (y : v.adicCompletion K)
    rw [adicCompletion.coe_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    refine DFinsupp.ext fun v ↦ ?_
    rw [RingHom.id_apply, DirectSum.smul_apply]
    change Submodule.Quotient.mk ((r • x : K) : v.adicCompletion K) =
      r • Submodule.Quotient.mk (p := localIdeal I v) (x : v.adicCompletion K)
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def (A := v.adicCompletion K),
      adicCompletion.coe_mul]
    rfl

theorem toLocalQuotients_apply {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K)
    (v : HeightOneSpectrum (𝓞 K)) :
    toLocalQuotients hI x v = Submodule.Quotient.mk (x : v.adicCompletion K) :=
  rfl

theorem toLocalQuotients_eq_zero_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    toLocalQuotients hI x = 0 ↔ x ∈ I := by
  rw [mem_iff_forall_mem_localIdeal hI, DFinsupp.ext_iff]
  simp only [toLocalQuotients_apply, DFinsupp.coe_zero, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero]


theorem toLocalQuotients_surjective {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    Function.Surjective (toLocalQuotients hI) := by
  classical
  intro f
  choose y hy using fun v ↦ Submodule.Quotient.mk_surjective _ (f v)
  let z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v ↦ if f v = 0 then 0 else y v
  have hz : ∀ v, Submodule.Quotient.mk (p := localIdeal I v) (z v) = f v := by
    intro v
    by_cases h : f v = 0
    · simp only [z, h, if_true, Submodule.Quotient.mk_zero]
    · simp only [z, h, if_false, hy]
  have hfin : {v | f v ≠ 0}.Finite :=
    f.support.finite_toSet.subset fun v hv ↦ DFinsupp.mem_support_iff.2 hv
  let a : FiniteAdeleRing (𝓞 K) K := ⟨z, Filter.eventually_cofinite.2 (hfin.subset fun v hv h ↦
    hv (by simp only [z, h, if_true]; exact (v.adicCompletionIntegers K).zero_mem))⟩
  obtain ⟨k, hk⟩ := exists_sub_mem_localIdeal hI a
  refine ⟨k, DFinsupp.ext fun v ↦ ?_⟩
  rw [toLocalQuotients_apply, ← hz v]
  exact ((Submodule.Quotient.eq _).2 (hk v)).symm

def quotientToLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) →ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) where
  toFun q := Quotient.liftOn' q (toLocalQuotients hI) fun a b h ↦ by
    rw [Submodule.quotientRel_def] at h
    have h0 := (toLocalQuotients_eq_zero_iff hI).2 h
    calc toLocalQuotients hI a = toLocalQuotients hI (b + (a - b)) :=
          congrArg (toLocalQuotients hI) (by abel)
      _ = toLocalQuotients hI b + toLocalQuotients hI (a - b) := map_add _ _ _
      _ = toLocalQuotients hI b := by rw [h0, add_zero]
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (toLocalQuotients hI) a b
  map_smul' := by
    rintro r ⟨a⟩
    exact map_smul (toLocalQuotients hI) r a


def quotientEquivLocalQuotients {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K] DirectSum (HeightOneSpectrum (𝓞 K)) (LocalQuotient I) :=
  LinearEquiv.ofBijective (quotientToLocalQuotients hI) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a⟩ h
      have h' : toLocalQuotients hI a = 0 := h
      exact (Submodule.Quotient.mk_eq_zero _).2 ((toLocalQuotients_eq_zero_iff hI).1 h'), by
      intro y
      obtain ⟨x, rfl⟩ := toLocalQuotients_surjective hI y
      exact ⟨Submodule.Quotient.mk x, rfl⟩⟩

@[simp]
theorem quotientEquivLocalQuotients_mk {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    quotientEquivLocalQuotients hI (Submodule.Quotient.mk x) = toLocalQuotients hI x :=
  rfl

namespace IdeleGroup

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

def localMul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    LocalQuotient (I : FractionalIdeal (𝓞 K)⁰ K) v ≃ₗ[𝓞 K]
      LocalQuotient ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v :=
  (Submodule.Quotient.equiv (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v)
    (localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v)
    ((finiteProj v s).mulLeftLinearEquiv (v.adicCompletionIntegers K) (v.adicCompletion K))
    (by
      rw [localIdeal_smul, Units.toLinearMap_mulLeftLinearEquiv, coe_finiteProj])).restrictScalars
    (𝓞 K)

theorem localMul_mk (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    localMul s I v (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((finiteProj v s : v.adicCompletion K) * y) :=
  rfl

def smulQuotient (s : IdeleGroup K) (I : 𝓘) :
    (K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ≃ₗ[𝓞 K]
      K ⧸ (((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  (quotientEquivLocalQuotients I.ne_zero).trans
    ((DFinsupp.mapRange.linearEquiv (localMul s I)).trans
      (quotientEquivLocalQuotients (s • I).ne_zero).symm)

theorem quotientEquivLocalQuotients_smulQuotient (s : IdeleGroup K) (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    quotientEquivLocalQuotients (s • I).ne_zero (smulQuotient s I q) =
      DFinsupp.mapRange.linearEquiv (localMul s I) (quotientEquivLocalQuotients I.ne_zero q) := by
  rw [smulQuotient, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

theorem smulQuotient_mk_eq_mk_iff (s : IdeleGroup K) (I : 𝓘) (x y : K) :
    smulQuotient s I (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum (𝓞 K), (finiteProj v s : v.adicCompletion K) * (x : v.adicCompletion K) -
        (y : v.adicCompletion K) ∈ localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by
  rw [← (quotientEquivLocalQuotients (s • I).ne_zero).injective.eq_iff,
    quotientEquivLocalQuotients_smulQuotient, quotientEquivLocalQuotients_mk,
    quotientEquivLocalQuotients_mk, DFinsupp.ext_iff]
  refine forall_congr' fun v ↦ ?_
  rw [DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply, toLocalQuotients_apply,
    toLocalQuotients_apply, localMul_mk, Submodule.Quotient.eq]

theorem mul_mem_localIdeal_smul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    {w : v.adicCompletion K} (hw : w ∈ localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v) :
    (finiteProj v s : v.adicCompletion K) * w ∈
      localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v := by
  rw [localIdeal_smul]
  exact ⟨w, hw, by simp only [LinearMap.mulLeft_apply, coe_finiteProj]⟩




end IdeleGroup

end

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IntermediateField IdeleGroup WithZero
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension maximalAbelianExtension)
open scoped nonZeroDivisors NumberField.AdeleRing

noncomputable section

variable {K : Type} [Field K] [NumberField K]

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

namespace Modulus

def ofNat (m : ℕ) (hm : m ≠ 0) : Modulus K where
  ideal := Ideal.span {(m : 𝓞 K)}
  ideal_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  real := ∅

theorem ofNat_ideal (m : ℕ) (hm : m ≠ 0) :
    (ofNat (K := K) m hm).ideal = Ideal.span {(m : 𝓞 K)} :=
  rfl

theorem asIdeal_dvd_ofNat_iff (m : ℕ) (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ (ofNat (K := K) m hm).ideal ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [ofNat_ideal, Ideal.dvd_span_singleton]

theorem valued_natCast (m : ℕ) (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((m : K) : v.adicCompletion K) = exp (-((ofNat (K := K) m hm).exponent v : ℤ)) := by
  have hm' : (m : 𝓞 K) ≠ 0 := by exact_mod_cast hm
  rw [valuedAdicCompletion_eq_valuation', show (m : K) = algebraMap (𝓞 K) K (m : 𝓞 K) by simp,
    valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity _ hm']
  rfl

end Modulus

section Symbol

variable [Algebra K ℂ]

theorem ideleSymbol_apply_eq_of_artinMap (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (M : IntermediateField K ℂ) [FiniteDimensional K M] [IsAbelianGalois K M] (z : M) :
    ((ideleSymbol K M s z : M) : ℂ) = σ (z : ℂ) := by
  have hM : M ≤ algebraicClosure K ℂ := le_algebraicClosure K ℂ M
  let e : M ≃ₐ[K] restrict hM := restrictAlgEquiv hM
  have : FiniteDimensional K (restrict hM) := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : IsAbelianGalois K (restrict hM) := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have he : ∀ w : M, (((e w : restrict hM) : algebraicClosure K ℂ) : ℂ) = (w : ℂ) := fun w ↦ rfl
  have h1 := artinMap_apply (restrict hM) (IdeleClassGroup.mk K s) (e z)
  rw [reciprocityMap_mk, ideleSymbol_apply_algEquiv e] at h1
  have h2 := hs ⟨((e z : restrict hM) : algebraicClosure K ℂ), le_maximalAbelianExtension _ (e z).2⟩
  rw [h1] at h2
  rw [← he, h2, he]

end Symbol

section Decomposition

variable [Algebra K ℂ]

theorem exists_eq_diagonal_mul_mul_finiteEmbedding (m : ℕ) (hm : m ≠ 0) (σ : ℂ ≃ₐ[K] ℂ)
    (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hL : (Modulus.ofNat m hm).rayClassField ℂ ≤ L)
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    (h𝔓 : IsArithFrobAt (𝓞 K) (σ.restrictNormal L) 𝔓.asIdeal) :
    ∃ (x : Kˣ) (u : IdeleGroup K) (π : (𝔭.adicCompletion K)ˣ),
      u ∈ (Modulus.ofNat m hm).congruenceSubgroup ∧
      toFractionalIdeal (finiteEmbedding 𝔭 π) = primeIdealUnit 𝔭 ∧
      s = diagonal K x * u * finiteEmbedding 𝔭 π := by
  classical
  set 𝔪 := Modulus.ofNat (K := K) m hm
  set M := 𝔪.rayClassField ℂ
  have hv : ¬ 𝔭.asIdeal ∣ 𝔪.ideal := by rwa [Modulus.asIdeal_dvd_ofNat_iff]
  set τ : L ≃ₐ[K] L := σ.restrictNormal L
  obtain ⟨w, hw, hfrob⟩ := Elliptic.exists_isArithFrobAt_galRestrict hL 𝔭 𝔓 τ h𝔓
  have : w.asIdeal.LiesOver 𝔭.asIdeal := hw
  have hram := 𝔪.ramificationIdx_rayClassField_eq_one ℂ hv w
  have hI : w.asIdeal.inertia (M ≃ₐ[K] M) = ⊥ := by
    rw [← Subgroup.card_eq_one, natCard_inertia 𝔭 w, hram]
  obtain ⟨π, hπ, -, hπI⟩ := 𝔪.exists_uniformizer_finiteEmbedding_mem_idelesOneMod hv
  have hsym : ideleSymbol K M s = ideleSymbol K M (finiteEmbedding 𝔭 π) := by
    rw [ideleSymbol_finiteEmbedding_eq_arithFrobAt 𝔭 w hram hπ]
    refine IsArithFrobAt.eq_of_inertia_eq_bot hI ?_ (IsArithFrobAt.arithFrobAt _ _ _)
    convert hfrob using 1
    refine AlgEquiv.ext fun z ↦ Subtype.ext ?_
    rw [ideleSymbol_apply_eq_of_artinMap σ s hs M z, Elliptic.galRestrict_apply]
    exact (AlgEquiv.restrictNormal_commutes σ L (inclusion hL z)).symm
  have hker : IdeleClassGroup.mk K (s * (finiteEmbedding 𝔭 π)⁻¹) ∈ (ideleClassNorm K M).range := by
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk, map_mul, map_inv, hsym,
      mul_inv_cancel]
  rw [𝔪.range_ideleClassNorm_rayClassField ℂ] at hker
  obtain ⟨u, hu, huq⟩ := hker
  obtain ⟨x, hx⟩ : u⁻¹ * (s * (finiteEmbedding 𝔭 π)⁻¹) ∈ (diagonal K).range :=
    QuotientGroup.eq.1 huq
  refine ⟨x, u, π, hu, hπI, ?_⟩
  rw [hx, mul_comm (u⁻¹ * _) u, ← mul_assoc u u⁻¹, mul_inv_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one]

variable {m : ℕ} {hm : m ≠ 0} {s : IdeleGroup K} {x : Kˣ} {u : IdeleGroup K}
  {𝔭 : HeightOneSpectrum (𝓞 K)} {π : (𝔭.adicCompletion K)ˣ}

omit [Algebra K ℂ] in

theorem inv_smul_eq_of_eq (hu : u ∈ (Modulus.ofNat m hm).congruenceSubgroup)
    (hπ : toFractionalIdeal (finiteEmbedding 𝔭 π) = primeIdealUnit 𝔭)
    (hs : s = diagonal K x * u * finiteEmbedding 𝔭 π) (𝔞 : 𝓘) :
    s⁻¹ • 𝔞 = diagonal K x⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞) := by
  have hu' : u⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞) = (primeIdealUnit 𝔭)⁻¹ * 𝔞 :=
    smul_eq_self_iff.2 (inv_mem (Modulus.congruenceSubgroup_le_standardOpenSubgroup _ hu))
  have hπ' : (finiteEmbedding 𝔭 π)⁻¹ • 𝔞 = (primeIdealUnit 𝔭)⁻¹ * 𝔞 := by
    rw [IdeleGroup.smul_def, map_inv, hπ]
  rw [hs, mul_inv, mul_inv, mul_smul, mul_smul, hπ', hu', map_inv]

omit [Algebra K ℂ] in

theorem smulQuotient_inv_mk_of_eq (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (hu : u ∈ (Modulus.ofNat m hm).congruenceSubgroup)
    (hπ : toFractionalIdeal (finiteEmbedding 𝔭 π) = primeIdealUnit 𝔭)
    (hs : s = diagonal K x * u * finiteEmbedding 𝔭 π) (𝔞 : 𝓘) {t : K}
    (ht : (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk ((x⁻¹ : K) * t) := by
  classical
  rw [smulQuotient_mk_eq_mk_iff]
  intro v
  rw [localIdeal_smul]
  set S : v.adicCompletion K := (finiteProj v s : v.adicCompletion K) with hSdef
  set W : v.adicCompletion K := (finiteProj v (u * finiteEmbedding 𝔭 π) : v.adicCompletion K) with hWdef
  set X : v.adicCompletion K := ((x : K) : v.adicCompletion K) with hXdef
  have hX0 : X ≠ 0 := by
    refine (Valuation.ne_zero_iff (Valued.v (R := v.adicCompletion K))).1 ?_
    rw [hXdef, valuedAdicCompletion_eq_valuation']
    exact (Valuation.ne_zero_iff _).2 x.ne_zero
  have hW0 : W ≠ 0 := (finiteProj v (u * finiteEmbedding 𝔭 π)).ne_zero
  have hSXW : S = X * W := by
    rw [hSdef, hs, mul_assoc, map_mul, Units.val_mul, coe_finiteProj_diagonal]
  have hc : ((s⁻¹ : IdeleGroup K) : 𝔸[K]).2 v = S⁻¹ := by
    rw [← coe_finiteProj, map_inv, Units.val_inv_eq_inv_val]
  refine ⟨(t : v.adicCompletion K) * (1 - W), ?_, ?_⟩
  ·
    have hmv := Modulus.valued_natCast (K := K) m hm v
    have huv := (Modulus.mem_congruenceSubgroup _).1 hu
    have hW : Valued.v (1 - W) ≤ Valued.v ((m : K) : v.adicCompletion K) := by
      rw [hmv]
      by_cases hv : v = 𝔭
      · subst hv
        have he : (Modulus.ofNat (K := K) m hm).exponent v = 0 :=
          ((Modulus.ofNat m hm).exponent_eq_zero_iff v).2
            (by rwa [Modulus.asIdeal_dvd_ofNat_iff])
        rw [he, Nat.cast_zero, neg_zero, exp_zero]
        have hu1 : Valued.v ((finiteProj v u : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
          (huv.1 v).1
        have hπ1 : Valued.v (π : v.adicCompletion K) ≤ 1 := by
          have hord : ord v (finiteEmbedding v π) = 1 := by
            rw [← count_toFractionalIdeal, hπ, count_primeIdealUnit, if_pos rfl]
          have := valued_eq_exp_neg_ord v (finiteEmbedding v π)
          rw [hord, ← coe_finiteProj, finiteProj_finiteEmbedding] at this
          rw [this]
          exact exp_le_exp.2 (by norm_num)
        refine (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) ?_)
        rw [hWdef, map_mul, Units.val_mul, map_mul, hu1, one_mul, finiteProj_finiteEmbedding]
        exact hπ1
      · rw [hWdef, map_mul, finiteProj_finiteEmbedding_of_ne hv, mul_one, Valuation.map_sub_swap]
        exact (huv.1 v).2
    rw [SetLike.mem_coe, mem_localIdeal_iff 𝔞.ne_zero, map_mul]
    have hmt : Valued.v (((m : K) * t : K) : v.adicCompletion K) ≤ exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :=
      (mem_localIdeal_iff 𝔞.ne_zero v).1 (coe_mem_localIdeal v ht)
    rw [adicCompletion.coe_mul, map_mul] at hmt
    calc Valued.v (t : v.adicCompletion K) * Valued.v (1 - W)
        ≤ Valued.v (t : v.adicCompletion K) * Valued.v ((m : K) : v.adicCompletion K) :=
          mul_le_mul_right hW _
      _ = Valued.v ((m : K) : v.adicCompletion K) * Valued.v (t : v.adicCompletion K) := mul_comm _ _
      _ ≤ exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := hmt
  · have hc' : ((finiteProj v s⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = S⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    have hXi : ((((x : K)⁻¹ : K)) : v.adicCompletion K) = X⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [hXdef, ← adicCompletion.coe_mul, inv_mul_cancel₀ x.ne_zero, adicCompletion.coe_one]
    rw [LinearMap.mulLeft_apply, hc, hc', adicCompletion.coe_mul, hXi, hSXW]
    field_simp

end Decomposition

section Main

variable [Algebra K ℂ]

theorem exists_diagonal_of_isArithFrobAt (m : ℕ) (hm : m ≠ 0) (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hL : (Modulus.ofNat m hm).rayClassField ℂ ≤ L)
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    (h𝔓 : IsArithFrobAt (𝓞 K) (σ.restrictNormal L) 𝔓.asIdeal) :
    ∃ x : Kˣ, ∀ 𝔞 : 𝓘, s⁻¹ • 𝔞 = diagonal K x⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞) ∧
      ∀ t : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk ((x⁻¹ : K) * t) := by
  obtain ⟨x, u, π, hu, hπ, hsx⟩ :=
    exists_eq_diagonal_mul_mul_finiteEmbedding m hm σ s hs 𝔭 h𝔭 L hL 𝔓 h𝔓
  exact ⟨x, fun 𝔞 ↦ ⟨inv_smul_eq_of_eq hu hπ hsx 𝔞,
    fun t ht ↦ smulQuotient_inv_mk_of_eq h𝔭 hu hπ hsx 𝔞 ht⟩⟩

end Main

theorem mem_diagonal_smul_iff (a : Kˣ) (J : 𝓘) (k : K) :
    k ∈ ((diagonal K a • J : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) ↔
      (a⁻¹ : K) * k ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_diagonal_smul, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]⟩

@[simp]
theorem coe_primeIdealUnit_inv_mul (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔞 : 𝓘) :
    (((primeIdealUnit 𝔭)⁻¹ * 𝔞 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * 𝔞 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_primeIdealUnit]

end

end GroundTheory.Global
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Points

variable {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']

omit [DecidableEq F] [DecidableEq F'] in
theorem point_some_eq_some {W : WeierstrassCurve F'} {x y x' y' : F'} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  subst hx
  subst hy
  rfl

theorem pointMapRing_vcPoint (f : F →+* F') {W₁ W₂ : WeierstrassCurve F} (C : VariableChange F)
    (h : C • W₁ = W₂) (P : W₁.toAffine.Point) :
    pointMapRing f W₂ (vcPoint C h P) =
      vcPoint (C.map f) (by rw [map_variableChange, h]) (pointMapRing f W₁ P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · exact point_some_eq_some _ _ (map_vcX C f x) (map_vcY C f x y)

theorem toPointHom_apply' (L : PeriodPair) (z : ℂ) : toPointHom L z = toPoint L z := rfl

theorem IsAnalyticUniformization.pointCongr {Λ : Submodule ℤ ℂ} {E E' : WeierstrassCurve ℂ}
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization Λ f) (e : E = E') :
    IsAnalyticUniformization Λ ((pointCongr e).toAddMonoidHom.comp f) := by
  subst e
  exact hf

end Points

section BaseChange

variable {L : Type} [Field L] [Algebra L ℂ] [DecidableEq L]

theorem exists_constMap_eq (A : WeierstrassCurve L) (P : (A.baseChange ℂ).toAffine.Point)
    (hP : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y), P = .some x y h →
      x ∈ (algebraMap L ℂ).range ∧ y ∈ (algebraMap L ℂ).range) :
    ∃ t : A.toAffine.Point, constMap A ℂ t = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hP _ _ h rfl
    have h' : A.toAffine.Nonsingular a b :=
      (A.toAffine.baseChange_nonsingular (f := Algebra.ofId L ℂ) (algebraMap L ℂ).injective a b).1 h
    exact ⟨.some a b h', rfl⟩

omit [DecidableEq L] in

theorem baseChange_map_eq (A : WeierstrassCurve L) (τ : L →+* L) (σ : ℂ →+* ℂ)
    (hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (τ a)) :
    (A.baseChange ℂ).map σ = (A.map τ).baseChange ℂ := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    WeierstrassCurve.map_map]
  congr 1
  ext a
  exact hτσ a

omit [Algebra L ℂ] in

theorem constMap_eq_pointMapRing {M : Type} [Field M] [Algebra L M] [DecidableEq M]
    (A : WeierstrassCurve L) (t : A.toAffine.Point) :
    constMap A M t = pointMapRing (algebraMap L M) A t := by
  rcases t with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem pointMapRing_constMap (A : WeierstrassCurve L) (τ : L →+* L) (σ : ℂ →+* ℂ)
    (hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (τ a)) (t : A.toAffine.Point) :
    pointMapRing σ (A.baseChange ℂ) (constMap A ℂ t) =
      pointCongr (baseChange_map_eq A τ σ hτσ).symm (constMap (A.map τ) ℂ (pointMapRing τ A t)) := by
  have e : σ.comp (algebraMap L ℂ) = (algebraMap L ℂ).comp τ := RingHom.ext hτσ
  rw [constMap_eq_pointMapRing, constMap_eq_pointMapRing]
  have h1 := pointMapRing_pointMapRing (algebraMap L ℂ) σ A t
  have h2 := pointMapRing_pointMapRing τ (algebraMap L ℂ) A t
  rw [pointMapRing_congr e] at h1
  refine h1.trans ?_
  rw [← h2]
  rfl

end BaseChange

section Ideals

variable {K : Type} [Field K] [NumberField K] (σ₀ : K →+* ℂ)

theorem mem_idealLattice_unit_mul_iff (J : FractionalIdeal (𝓞 K)⁰ K) (v : (𝓞 K)ˣ) (w : ℂ) :
    σ₀ (algebraMap (𝓞 K) K v) * w ∈ idealLattice σ₀ J ↔ w ∈ idealLattice σ₀ J := by
  have key : ∀ (v : (𝓞 K)ˣ) (w : ℂ), w ∈ idealLattice σ₀ J →
      σ₀ (algebraMap (𝓞 K) K v) * w ∈ idealLattice σ₀ J := by
    intro v w hw
    obtain ⟨k, hk, rfl⟩ := (mem_idealLattice σ₀).1 hw
    refine (mem_idealLattice σ₀).2 ⟨algebraMap (𝓞 K) K v * k, ?_, by rw [map_mul]⟩
    rw [← Algebra.smul_def]
    exact (J : Submodule (𝓞 K) K).smul_mem (v : 𝓞 K) hk
  refine ⟨fun h ↦ ?_, key v w⟩
  have := key v⁻¹ _ h
  rwa [← mul_assoc, ← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
    map_one, one_mul] at this

theorem mem_idealLattice_diagonal_smul_iff (x : Kˣ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : ℂ) :
    z ∈ idealLattice σ₀ ↑(IdeleGroup.diagonal K x⁻¹ • J) ↔ σ₀ x * z ∈ idealLattice σ₀ J := by
  rw [mem_idealLattice, mem_idealLattice]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_diagonal_smul_iff, Units.val_inv_eq_inv_val, inv_inv] at hk
    exact ⟨x * k, hk, by rw [map_mul]⟩
  · rintro ⟨k, hk, hkz⟩
    refine ⟨(x⁻¹ : K) * k, ?_, ?_⟩
    · rw [mem_diagonal_smul_iff, Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
        mul_inv_cancel₀ x.ne_zero, one_mul]
      exact hk
    · rw [map_mul, hkz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ x.ne_zero, map_one, one_mul]

end Ideals

section Level

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

theorem exists_uniformization_of_data (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    {m : ℕ} {L : IntermediateField K ℂ} [NumberField L] (τ : L ≃ₐ[K] L)
    (hτσ : ∀ a : L, σ (algebraMap L ℂ a) = algebraMap L ℂ (τ a))
    {A : WeierstrassCurve L} [A.IsElliptic] (V₀ : VariableChange ℂ) (hV₀ : V₀ • E = A.baseChange ℂ)
    (htors : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y),
      m • (Point.some x y h : (A.baseChange ℂ).toAffine.Point) = 0 →
        x ∈ (algebraMap L ℂ).range ∧ y ∈ (algebraMap L ℂ).range)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (x : Kˣ)
    (hs𝔞 : s⁻¹ • 𝔞 = IdeleGroup.diagonal K x⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞))
    (hsq : ∀ t : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
      IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) =
        Submodule.Quotient.mk ((x⁻¹ : K) * t))
    (φ : Isogeny A (A.map (τ : L →+* L)))
    (hφ : (homConstSet (A.baseChange ℂ) ((A.map (τ : L →+* L)).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (D : VariableChange L) (hD : D • A.map (τ : L →+* L) = A.map (τ : L →+* L))
    (hDφ : ∀ t : A.toAffine.Point, m • t = 0 →
      pointHomOver ℂ φ t = vcPoint D hD (pointMapRing (τ : L →+* L) A t))
    (V' : VariableChange ℂ)
    (hV' : V' • weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)) =
      (A.map (τ : L →+* L)).baseChange ℂ) :
    ∃ f' : ℂ →+ (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞)) f' ∧
      ∀ t y : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk y →
          f' (algebraMap K ℂ y) = pointMapRing (σ : ℂ →+* ℂ) E (f (algebraMap K ℂ t)) := by
  classical

  have hL₁ := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hL₂ := lattice_idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞)
  generalize idealPeriodPair (algebraMap K ℂ) hK 𝔞 = L₁ at hL₁
  generalize idealPeriodPair (algebraMap K ℂ) hK ((primeIdealUnit 𝔭)⁻¹ * 𝔞) = L₂ at hL₂ hV'

  have hfA := hf.vcPoint V₀ hV₀
  rw [← hL₁] at hfA
  obtain ⟨V, hV, hfV⟩ := exists_vcPoint_of_isAnalyticUniformization hfA

  have hφℂ : (homConstSet (A.baseChange ℂ) ((A.map (τ : L →+* L)).baseChange ℂ) : Set ℂ) =
      (invConst (isogBaseChange (F' := ℂ) φ) * ·) ''
        idealLattice (algebraMap K ℂ) ↑((primeIdealUnit 𝔭)⁻¹) := by
    rw [invConst_isogBaseChange, hφ, Units.val_inv_eq_inv_val, coe_primeIdealUnit]
  obtain ⟨u, hu⟩ := exists_unit_pointMap_vcPoint (algebraMap K ℂ) hK 𝔞 (primeIdealUnit 𝔭)⁻¹ L₁ L₂
    hL₁ hL₂ V hV V' hV' (isogBaseChange (F' := ℂ) φ) hφℂ

  have hDℂ := Elliptic.baseChange_smul_eq D ℂ hD
  have hg₁ := (isAnalyticUniformization_toPointHom L₂).vcPoint V' hV'
  have hg₂ := hg₁.vcPoint (D.baseChange ℂ) hDℂ
  obtain ⟨c, hc0, hcl, hcg⟩ := exists_mul_eq_of_isAnalyticUniformization hg₁ hg₂
  rw [hL₂] at hcl
  obtain ⟨ε, hε⟩ := exists_unit_of_forall_mem_iff (algebraMap K ℂ) hK _ hcl

  have hεinv : algebraMap K ℂ (algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) * c = 1 := by
    rw [hε, ← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hcinv : c⁻¹ * algebraMap K ℂ (algebraMap (𝓞 K) K u) =
      algebraMap K ℂ (algebraMap (𝓞 K) K ((ε⁻¹ * u : (𝓞 K)ˣ) : 𝓞 K)) := by
    rw [Units.val_mul, map_mul, map_mul, inv_eq_of_mul_eq_one_left hεinv]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = c⁻¹ * algebraMap K ℂ (algebraMap (𝓞 K) K u) * algebraMap K ℂ x :=
    ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ, hcinv]
    refine mul_ne_zero ((map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2
      (Units.ne_zero _))) ((map_ne_zero _).2 x.ne_zero)
  have hΛ : ∀ z, z ∈ idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞) ↔ κ * z ∈ L₂.lattice := by
    intro z
    rw [hs𝔞, mem_idealLattice_diagonal_smul_iff, hL₂, hκ, hcinv, mul_assoc,
      mem_idealLattice_unit_mul_iff]

  have h₄ : (V₀.map (σ : ℂ →+* ℂ)) • E.map (σ : ℂ →+* ℂ) = (A.baseChange ℂ).map (σ : ℂ →+* ℂ) := by
    rw [map_variableChange, hV₀]
  have h₃ := inv_smul_eq_of_smul_eq _ h₄
  have e₂ : (A.map (τ : L →+* L)).baseChange ℂ = (A.baseChange ℂ).map (σ : ℂ →+* ℂ) :=
    (baseChange_map_eq A (τ : L →+* L) σ hτσ).symm
  have hf' := ((hg₁.comp_mul hκ0 hΛ).pointCongr e₂).vcPoint _ h₃
  refine ⟨_, hf', fun t y hmt hq ↦ ?_⟩

  have hdiff : algebraMap K ℂ y - algebraMap K ℂ ((x⁻¹ : K) * t) ∈
      idealLattice (algebraMap K ℂ) ↑(s⁻¹ • 𝔞) := by
    rw [hsq t hmt] at hq
    have h1 := (Submodule.Quotient.eq _).1 hq
    rw [← map_sub]
    refine map_mem_idealLattice _ ?_
    rw [← neg_sub]
    exact Submodule.neg_mem _ h1
  rw [← sub_add_cancel (algebraMap K ℂ y) (algebraMap K ℂ ((x⁻¹ : K) * t)), map_add,
    (hf'.map_eq_zero_iff _).2 hdiff, zero_add]

  set z := algebraMap K ℂ t with hz
  have hmz : (m : ℂ) * z ∈ L₁.lattice := by
    rw [hL₁, hz, ← map_natCast (algebraMap K ℂ), ← map_mul]
    exact map_mem_idealLattice _ hmt
  have hPA : vcPoint V₀ hV₀ (f z) = vcPoint V hV (toPoint L₁ z) := hfV z
  have hPAm : m • vcPoint V₀ hV₀ (f z) = 0 := by
    rw [hPA, ← toPointHom_apply', ← vcPointEquiv_apply, ← map_nsmul, ← map_nsmul, nsmul_eq_mul,
      toPointHom_apply', toPoint_of_mem hmz, map_zero]
  obtain ⟨tL, htL⟩ := exists_constMap_eq A (vcPoint V₀ hV₀ (f z)) (fun a b h hP ↦
    htors a b h (by rw [← hP]; exact hPAm))
  have htLm : m • tL = 0 := by
    apply constMap_injective A ℂ
    rw [map_nsmul, htL, hPAm, map_zero]

  have key := congrArg (constMap (A.map (τ : L →+* L)) ℂ) (hDφ tL htLm)
  rw [constMap_pointHomOver, htL, hPA, hu z, constMap_eq_pointMapRing, pointMapRing_vcPoint,
    ← constMap_eq_pointMapRing] at key

  have hw : c * (c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z)) =
      algebraMap K ℂ (algebraMap (𝓞 K) K u) * z := by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hcg' := hcg (c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z))
  rw [hw] at hcg'
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
    toPointHom_apply'] at hcg'
  have h5 : vcPoint (D.baseChange ℂ) hDℂ
      (constMap (A.map (τ : L →+* L)) ℂ (pointMapRing (τ : L →+* L) A tL)) =
      vcPoint (D.baseChange ℂ) hDℂ
        (vcPoint V' hV' (toPoint L₂ (c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z)))) :=
    key.symm.trans hcg'.symm
  have h6 := vcPoint_injective _ _ h5

  have h7 := pointMapRing_constMap A (τ : L →+* L) σ hτσ tL
  rw [htL, pointMapRing_vcPoint] at h7
  change vcPoint _ h₃ (pointCongr e₂ (vcPoint V' hV'
    (toPoint L₂ (κ * algebraMap K ℂ ((x⁻¹ : K) * t))))) = pointMapRing (σ : ℂ →+* ℂ) E (f z)
  have e3 : κ * algebraMap K ℂ ((x⁻¹ : K) * t) =
      c⁻¹ * (algebraMap K ℂ (algebraMap (𝓞 K) K u) * z) := by
    rw [hκ, hz, map_mul, map_inv₀]
    field_simp
  rw [e3, ← h6]
  have h8 : pointCongr e₂ (constMap (A.map (τ : L →+* L)) ℂ (pointMapRing (τ : L →+* L) A tL)) =
      vcPoint (V₀.map (σ : ℂ →+* ℂ)) h₄ (pointMapRing (σ : ℂ →+* ℂ) E (f z)) := h7.symm
  rw [h8]
  exact vcPoint_vcPoint_of_eq_inv _ _ rfl _ _ _

end Level

end

end Elliptic
end GroundTheory.Global
end
