import Mathlib
import GroundTheory.PAdicHodge.BCrisEigenFixed
import GroundTheory.PAdicHodge.BCrisEigenWitt
import GroundTheory.PAdicHodge.LocalBridge
import GroundTheory.PAdicHodge.ACrisGalois
import GroundTheory.LocalFields.PrincipalUnitsRank
import GroundTheory.PAdicHodge.UnramifiedClosure
import GroundTheory.LocalFields.WeilGroupDefs
import GroundTheory.PAdicHodge.SenTateCharTrace

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ValuativeRel IsLocalRing

namespace UnramifiedACris

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in

theorem irreducible_p : Irreducible (p : 𝒪[ℚ_[p]]) := by
  have h := (MulEquiv.irreducible_iff
    (f := (GroundTheory.LocalField.PadicRank.padicIntEquivInteger p).toMulEquiv)
    (x := (p : ℤ_[p]))).2 PadicInt.irreducible_p
  simpa using h

variable (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K₀]

omit [FiniteDimensional ℚ_[p] K₀] in

theorem mem_integer_iff (x : K₀) : x ∈ 𝒪[K₀] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  rw [integer_eq_normInteger, mem_normInteger]
  rfl

theorem natCast_p_mem_maximalIdeal : (p : 𝒪[K₀]) ∈ 𝓂[K₀] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) = 1 := by rw [hv]; rfl
  have hv1 : ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ ≤ 1 := (mem_integer_iff K₀ _).1 v.2
  have h2 : ‖((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ < 1 := by
    have : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) =
        (p : PadicAlgCl p) * (((v : 𝒪[K₀]) : K₀) : PadicAlgCl p) := by
      simp
    rw [this, norm_mul]
    calc ‖(p : PadicAlgCl p)‖ * ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖
        ≤ ‖(p : PadicAlgCl p)‖ * 1 := by gcongr
      _ < 1 := by
        rw [mul_one, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

instance charP_residueField : CharP 𝓀[K₀] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue 𝒪[K₀]), residue_eq_zero_iff]
    exact natCast_p_mem_maximalIdeal K₀)

theorem exists_eq_p_mul_of_mem_maximalIdeal
    [GroundTheory.LocalField.IsUnramified ℚ_[p] K₀] {x : 𝒪[K₀]} (hx : x ∈ 𝓂[K₀]) :
    ∃ y : 𝒪[K₀], x = p * y := by
  rw [← (GroundTheory.LocalField.map_maximalIdeal_eq_iff ℚ_[p] K₀).2 inferInstance,
    (irreducible_p p).maximalIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.mem_span_singleton] at hx
  exact hx

def integerToCp : 𝒪[K₀] →+* normInteger ℂ_[p] :=
  RingHom.codRestrict ((algebraMap (PadicAlgCl p) ℂ_[p]).comp
    ((algebraMap K₀ (PadicAlgCl p)).comp (𝒪[K₀]).subtype)) (normInteger ℂ_[p]) fun x => by
    rw [mem_normInteger, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
    exact (mem_integer_iff K₀ x).1 x.2

variable [GroundTheory.LocalField.IsUnramified ℚ_[p] K₀]

def residueToModP : 𝓀[K₀] →+* ModP (normInteger ℂ_[p]) p :=
  Ideal.Quotient.lift (𝓂[K₀]) ((Ideal.Quotient.mk _).comp (integerToCp K₀)) fun x hx => by
    obtain ⟨y, rfl⟩ := exists_eq_p_mul_of_mem_maximalIdeal K₀ hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def residueToPreTilt : 𝓀[K₀] →+* PreTilt (normInteger ℂ_[p]) p :=
  Perfection.lift p 𝓀[K₀] (ModP (normInteger ℂ_[p]) p) (residueToModP K₀)

def wittToAInf : WittVector p 𝓀[K₀] →+* AInf ℂ_[p] p :=
  WittVector.map (residueToPreTilt K₀)

end UnramifiedACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenWitt

open Polynomial GroundTheory.LocalField

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

theorem exists_padicAlgCl_eq_of_pow_eq_one {z : ℂ_[p]} {m : ℕ} (hm : 0 < m) (hz : z ^ m = 1) :
    ∃ ζ : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] ζ = z ∧ ζ ^ m = 1 := by
  classical
  set P : (PadicAlgCl p)[X] := X ^ m - C 1 with hP
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  have hroots := (IsAlgClosed.splits P).roots_map_of_injective hinj
  have hmem : z ∈ (P.map (algebraMap (PadicAlgCl p) ℂ_[p])).roots := by
    rw [show P.map (algebraMap (PadicAlgCl p) ℂ_[p]) = X ^ m - C 1 by simp [hP],
      mem_roots (X_pow_sub_C_ne_zero hm 1)]
    simp [hz]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨ζ, hζ, hζz⟩ := hmem
  refine ⟨ζ, hζz, ?_⟩
  rw [mem_roots (X_pow_sub_C_ne_zero hm 1)] at hζ
  simpa [sub_eq_zero] using hζ

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

abbrev untiltC (x : 𝒪♭) : ℂ_[p] := ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p])

theorem untiltC_pow (x : 𝒪♭) (k : ℕ) : untiltC (x ^ k) = untiltC x ^ k := by
  simp [untiltC, map_pow]

theorem norm_natCast_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem eq_of_untiltC_eq {x y : 𝒪♭} {n : ℕ} (hn : 0 < n) (hx : x ^ p ^ n = x) (hy : y ^ p ^ n = y)
    (h : untiltC x = untiltC y) : x = y := by
  set z := x - y with hz
  have hzp : z ^ p ^ n = z := by rw [hz, sub_pow_char_pow, hx, hy]
  have hsum := norm_untilt_add_sub_le (K := ℂ_[p]) (p := p) z y
  have hzy : z + y = x := by rw [hz, sub_add_cancel]
  rw [hzy] at hsum
  have e : ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) -
      (((PreTilt.untilt z : normInteger ℂ_[p]) : ℂ_[p]) +
        ((PreTilt.untilt y : normInteger ℂ_[p]) : ℂ_[p])) = -untiltC z := by
    simp only [untiltC] at h ⊢
    rw [h]
    ring
  rw [e, norm_neg] at hsum
  have hpow : ‖untiltC z‖ ^ p ^ n = ‖untiltC z‖ := by rw [← norm_pow, ← untiltC_pow, hzp]
  have hz0 : untiltC z = 0 := by
    by_contra hne
    have hpos : 0 < ‖untiltC z‖ := norm_pos_iff.2 hne
    have hpn : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
    have h1 : ‖untiltC z‖ = 1 := by
      rcases lt_trichotomy ‖untiltC z‖ 1 with hlt | heq | hgt
      · have : ‖untiltC z‖ ^ p ^ n < ‖untiltC z‖ ^ 1 := pow_lt_pow_right_of_lt_one₀ hpos hlt hpn
        rw [pow_one, hpow] at this
        exact absurd this (lt_irrefl _)
      · exact heq
      · have : ‖untiltC z‖ ^ 1 < ‖untiltC z‖ ^ p ^ n := pow_lt_pow_right₀ hgt hpn
        rw [pow_one, hpow] at this
        exact absurd this (lt_irrefl _)
    rw [h1] at hsum
    exact absurd (lt_of_le_of_lt hsum norm_natCast_p_lt_one) (lt_irrefl _)
  have hz' : z = 0 := (untilt_eq_zero_iff (K := ℂ_[p])).1 hz0
  exact sub_eq_zero.1 hz'

theorem galFlat_eq_pow {σ : Gal(PadicAlgCl p/K)} {n a : ℕ} (hn : 0 < n) (ha : 0 < a)
    (hσ : ∀ ζ : PadicAlgCl p, ζ ^ (p ^ n - 1) = 1 → σ ζ = ζ ^ a) {x : 𝒪♭} (hx : x ^ p ^ n = x) :
    galFlat σ x = x ^ a := by
  have hy : (galFlat σ x) ^ p ^ n = galFlat σ x := by rw [← map_pow, hx]
  have hxa : (x ^ a) ^ p ^ n = x ^ a := by rw [← pow_mul, mul_comm, pow_mul, hx]
  refine eq_of_untiltC_eq hn hy hxa ?_
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  by_cases h0 : untiltC x = 0
  · have hx0 : x = 0 := (untilt_eq_zero_iff (K := ℂ_[p])).1 h0
    rw [hx0, map_zero, zero_pow ha.ne']
  · have hux : untiltC x ^ p ^ n = untiltC x := by rw [← untiltC_pow, hx]
    have hux1 : untiltC x ^ (p ^ n - 1) = 1 := by
      have e : untiltC x ^ (p ^ n - 1) * untiltC x = 1 * untiltC x := by
        rw [← pow_succ, Nat.sub_add_cancel hpn, hux, one_mul]
      exact mul_right_cancel₀ h0 e
    have hm : 0 < p ^ n - 1 := by
      have := Nat.one_lt_pow hn.ne' hp.out.one_lt
      omega
    obtain ⟨ζ, hζ, hζ1⟩ := exists_padicAlgCl_eq_of_pow_eq_one hm hux1
    have e1 : untiltC (galFlat σ x) = σ • untiltC x := AInf.coe_untilt_gal σ x
    rw [e1, untiltC_pow, ← hζ, ← PadicComplex.coe_eq, gal_smul_coe, hσ ζ hζ1, PadicComplex.coe_eq,
      map_pow]
    rfl

open ValuativeRel

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] L] in
theorem isSepClosure_padicAlgCl : IsSepClosure L (PadicAlgCl p) :=
  ⟨inferInstance, inferInstance⟩

theorem natCast_pow_sub_one_ne_zero {n : ℕ} (hn : 0 < n) :
    ((p ^ n - 1 : ℕ) : 𝓀[L]) ≠ 0 := by
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  rw [Nat.cast_sub hpn, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne', Nat.cast_one, zero_sub]
  exact neg_ne_zero.2 one_ne_zero

theorem mem_unramifiedRoots_of_pow_eq_one {ζ : PadicAlgCl p} {n : ℕ} (hn : 0 < n)
    (hζ : ζ ^ (p ^ n - 1) = 1) : ζ ∈ unramifiedRoots L (PadicAlgCl p) :=
  mem_unramifiedRoots_iff.2 ⟨p ^ n - 1, natCast_pow_sub_one_ne_zero hn, hζ⟩

theorem galFpbar_eq_pow_of_degree_one {σ : Gal(PadicAlgCl p/L)}
    (hσ : unramifiedDegree L (PadicAlgCl p) σ = Multiplicative.ofAdd 1) (a : Fpbar p) :
    galFpbar σ a = a ^ Nat.card 𝓀[L] := by
  apply fpbarToPreTilt_injective
  obtain ⟨n, hn, hx⟩ := fpbarToPreTilt_pow_eq_self a
  rw [fpbarToPreTilt_galFpbar, map_pow]
  exact galFlat_eq_pow hn Nat.card_pos (fun ζ hζ =>
    (unramifiedDegree_eq_ofAdd_one_iff σ).1 hσ ζ (mem_unramifiedRoots_of_pow_eq_one hn hζ)) hx

theorem galFpbar_eq_self {σ : Gal(PadicAlgCl p/L)} (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1)
    (a : Fpbar p) : galFpbar σ a = a := by
  have hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hσ
  apply fpbarToPreTilt_injective
  obtain ⟨n, hn, hx⟩ := fpbarToPreTilt_pow_eq_self a
  rw [fpbarToPreTilt_galFpbar]
  have := galFlat_eq_pow (σ := σ) hn one_pos (fun ζ hζ => by
    rw [pow_one]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ
      (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_of_pow_eq_one hn hζ))) hx
  rwa [pow_one] at this

theorem map_iterateFrobenius (f : ℕ) (x : WittVector p (Fpbar p)) :
    WittVector.map (iterateFrobenius (Fpbar p) p f) x = WittVector.frobenius^[f] x := by
  ext n
  rw [WittVector.map_coeff, iterateFrobenius_def]
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ← ih, ← pow_mul, ← pow_succ]

theorem iterate_frobenius_eq_mul {w : ℤ_[p]ˣ} {b : WittVector p (Fpbar p)}
    (hb : WittVector.frobenius b = b * padicIntToWittFpbar (w : ℤ_[p])) (f : ℕ) :
    WittVector.frobenius^[f] b = b * padicIntToWittFpbar ((w : ℤ_[p]) ^ f) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, hb, frobenius_padicIntToWittFpbar, map_pow,
      map_pow, pow_succ]
    ring

theorem gal_smul_twist_of_degree_one {w : ℤ_[p]ˣ} {b : WittVector p (Fpbar p)}
    (hb : WittVector.frobenius b = b * padicIntToWittFpbar (w : ℤ_[p])) {f : ℕ}
    (hq : Nat.card 𝓀[L] = p ^ f) {σ : Gal(PadicAlgCl p/L)}
    (hσ : unramifiedDegree L (PadicAlgCl p) σ = Multiplicative.ofAdd 1) :
    σ • wittToAInf b = IsPerfectoidField.padicIntToWitt p ((w : ℤ_[p]) ^ f) * wittToAInf b := by
  have e : galFpbar σ = iterateFrobenius (Fpbar p) p f := by
    ext a
    rw [galFpbar_eq_pow_of_degree_one hσ, hq, iterateFrobenius_def]
  rw [gal_smul_wittToAInf, e, map_iterateFrobenius, iterate_frobenius_eq_mul hb, map_mul,
    wittToAInf_padicIntToWittFpbar, mul_comm]

theorem gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) {σ : Gal(PadicAlgCl p/L)}
    (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1) : σ • wittToAInf b = wittToAInf b := by
  have e : galFpbar σ = RingHom.id (Fpbar p) := RingHom.ext (galFpbar_eq_self hσ)
  rw [gal_smul_wittToAInf, e, WittVector.map_id]
  rfl

theorem exists_card_residueField_eq_pow : ∃ f : ℕ, 0 < f ∧ Nat.card 𝓀[L] = p ^ f := by
  let := Fintype.ofFinite 𝓀[L]
  obtain ⟨n, -, hcard⟩ := FiniteField.card 𝓀[L] p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem eq_one_of_degree_one (ρ : Gal(PadicAlgCl p/L) →* ℂ_[p]) (hρ : Continuous ρ)
    {σ₀ : Gal(PadicAlgCl p/L)}
    (hσ₀ : unramifiedDegree L (PadicAlgCl p) σ₀ = Multiplicative.ofAdd 1) (h₀ : ρ σ₀ = 1)
    (hI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → ρ σ = 1) (σ : Gal(PadicAlgCl p/L)) :
    ρ σ = 1 := by
  have := isSepClosure_padicAlgCl (L := L)
  let H : Subgroup Gal(PadicAlgCl p/L) :=
    { carrier := {τ | ρ τ = 1}
      mul_mem' := fun {a b} (ha : ρ a = 1) (hb : ρ b = 1) => show ρ (a * b) = 1 by
        rw [map_mul, ha, hb, one_mul]
      one_mem' := map_one ρ
      inv_mem' := fun {a} (ha : ρ a = 1) => show ρ a⁻¹ = 1 by
        calc ρ a⁻¹ = ρ a⁻¹ * ρ a := by rw [ha, mul_one]
          _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one] }
  have hclosed : IsClosed (H : Set Gal(PadicAlgCl p/L)) := isClosed_eq hρ continuous_const
  have hW : (weilSubgroup L (PadicAlgCl p) : Set Gal(PadicAlgCl p/L)) ⊆ H := by
    intro τ hτ
    obtain ⟨n, hn⟩ := mem_weilSubgroup_iff_unramifiedDegree.1 hτ
    have hdeg : unramifiedDegree L (PadicAlgCl p) (σ₀ ^ n) = unramifiedDegree L (PadicAlgCl p) τ := by
      rw [map_zpow, hσ₀, hn, ← ofAdd_zsmul, zsmul_one]
    have h1 : unramifiedDegree L (PadicAlgCl p) ((σ₀ ^ n)⁻¹ * τ) = 1 := by
      rw [map_mul, map_inv, hdeg, inv_mul_cancel]
    have hσ₀H : σ₀ ∈ H := h₀
    have hpow : σ₀ ^ n ∈ H := H.zpow_mem hσ₀H n
    have hrest : (σ₀ ^ n)⁻¹ * τ ∈ H := hI _ h1
    have := H.mul_mem hpow hrest
    rwa [mul_inv_cancel_left] at this
  have hsub : closure (weilSubgroup L (PadicAlgCl p) : Set Gal(PadicAlgCl p/L)) ⊆ H :=
    closure_minimal hW hclosed
  rw [(dense_weilSubgroup L (PadicAlgCl p)).closure_eq] at hsub
  exact hsub (Set.mem_univ σ)

end EigenWitt

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenChar

open GroundTheory.LocalField EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

theorem algebraMap_padic_cp_injective : Function.Injective (algebraMap ℚ_[p] ℂ_[p]) :=
  (algebraMap ℚ_[p] ℂ_[p]).injective

theorem isometry_algebraMap_padic_cp : Isometry (algebraMap ℚ_[p] ℂ_[p]) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' ℂ_[p])

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem eq_of_mul_eq {x : ℂ_[p]} (hx : x ≠ 0) {q q' : ℚ_[p]}
    (h : algebraMap ℚ_[p] ℂ_[p] q * x = algebraMap ℚ_[p] ℂ_[p] q' * x) : q = q' :=
  algebraMap_padic_cp_injective (mul_right_cancel₀ hx h)

theorem exists_eigenChar {x : ℂ_[p]} (hx : x ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) :
    ∃ ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ, Continuous ψ ∧
      ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x := by
  choose q hq using h
  let ψ₀ : Gal(PadicAlgCl p/K) →* ℚ_[p] :=
    { toFun := q
      map_one' := eq_of_mul_eq hx (by rw [← hq, one_smul, map_one, one_mul])
      map_mul' := fun σ τ => eq_of_mul_eq hx (by
        rw [← hq, mul_smul, hq τ, smul_mul', gal_smul_algebraMap, hq σ, map_mul]
        ring) }
  have hcont₀ : Continuous ψ₀ := by
    rw [isometry_algebraMap_padic_cp.isEmbedding.continuous_iff]
    have e : (algebraMap ℚ_[p] ℂ_[p]) ∘ ψ₀ = fun σ => (σ • x) * x⁻¹ := by
      funext σ
      simp only [Function.comp_apply]
      change algebraMap ℚ_[p] ℂ_[p] (q σ) = _
      rw [hq σ, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [e]
    exact (continuous_id.smul continuous_const).mul continuous_const
  refine ⟨ψ₀.toHomUnits, ?_, fun σ => hq σ⟩
  rw [Units.continuous_iff]
  refine ⟨hcont₀, ?_⟩
  have e : (fun σ => (((ψ₀.toHomUnits σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) = ψ₀ ∘ fun σ => σ⁻¹ := by
    funext σ
    rw [← map_inv]
    rfl
  rw [e]
  exact hcont₀.comp continuous_inv

theorem norm_eigen_eq_one {x : ℂ_[p]} (hx : x ≠ 0) {σ : Gal(PadicAlgCl p/K)} {q : ℚ_[p]}
    (h : σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) : ‖q‖ = 1 := by
  have h1 := norm_smul_gal σ x
  rw [h, norm_mul, norm_algebraMap'] at h1
  exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx) (h1.trans (one_mul _).symm)

def galRes {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Gal(PadicAlgCl p/L) →* Gal(PadicAlgCl p/K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun k => σ.commutes ⟨(k : PadicAlgCl p), hKL k.2⟩)
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

theorem galRes_apply {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L)
    (σ : Gal(PadicAlgCl p/L)) (y : PadicAlgCl p) : galRes hKL σ y = σ y := rfl


theorem exists_fixingSubgroup_of_finite_image (ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ) (hψ : Continuous ψ)
    (S : Set Gal(PadicAlgCl p/K)) (hfin : (ψ '' S).Finite) :
    ∃ E : IntermediateField K (PadicAlgCl p), FiniteDimensional K E ∧
      ∀ σ ∈ E.fixingSubgroup, σ ∈ S → ψ σ = 1 := by
  set F := ψ '' S \ {1} with hF
  have hFc : IsClosed F := (hfin.subset Set.sdiff_subset).isClosed
  have hO : ψ ⁻¹' Fᶜ ∈ nhds (1 : Gal(PadicAlgCl p/K)) := by
    refine (hFc.isOpen_compl.preimage hψ).mem_nhds ?_
    simp [hF]
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K (PadicAlgCl p) _).1 hO
  refine ⟨E, hE, fun σ hσ hS => ?_⟩
  by_contra hne
  exact hsub hσ ⟨⟨σ, hS, rfl⟩, hne⟩

theorem mem_inertia_of_degree {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    {σ : Gal(PadicAlgCl p/L)} (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1) :
    ∀ u ∈ unramifiedClosure p, σ u = u := by
  have hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hσ
  have hroot : ∀ ζ ∈ primeToPRoots p, σ ζ = ζ := by
    rintro ζ ⟨m, hm, hcop, hζ⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ
      (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_iff.2 ⟨m, ?_, hζ⟩))
    intro h0
    rw [CharP.cast_eq_zero_iff _ p] at h0
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop.symm h0
  intro u hu
  induction hu using IntermediateField.adjoin_induction with
  | mem x hx => exact hroot x hx
  | algebraMap q =>
    exact σ.commutes (algebraMap ℚ_[p] L q)
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem exists_twist_of_unramified {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] L] {x : ℂ_[p]} (hx : x ≠ 0) (ψ : Gal(PadicAlgCl p/L) →* ℚ_[p]ˣ)
    (hψx : ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x)
    (hI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ c : (AInf ℂ_[p] p)ˣ, ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p],
      (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
      σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  have := isSepClosure_padicAlgCl (L := L)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := L) (Ω := PadicAlgCl p)
    (Multiplicative.ofAdd 1)
  have hw : ‖((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := norm_eigen_eq_one hx (hψx σ₀)
  set w : ℤ_[p]ˣ := PadicInt.mkUnits hw with hwdef
  have hwcoe : ((w : ℤ_[p]) : ℚ_[p]) = ((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p]) := rfl
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (L := L)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := L) w
  set cA := wittToAInf (b : WittVector p (Fpbar p)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[p]) p
  set xc : ℂ_[p] := ((θ cA : normInteger ℂ_[p]) : ℂ_[p]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[p] ℂ_[p] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz0 : ∀ σ, (z σ : ℚ_[p]) ≠ 0 := fun σ h => by
    have := norm_eigen_eq_one hxc (hxcσ σ)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set X := x ^ f * xc⁻¹ with hXdef
  have hX : X ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (inv_ne_zero hxc)
  have hXσ : ∀ σ, σ • X = algebraMap ℚ_[p] ℂ_[p]
      (((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹) * X := fun σ => by
    rw [hXdef, ← galCp_apply, map_mul, map_pow, map_inv₀, galCp_apply, galCp_apply, hψx σ, hxcσ σ,
      map_mul, map_pow, map_inv₀]
    have hz' : algebraMap ℚ_[p] ℂ_[p] (z σ : ℚ_[p]) ≠ 0 :=
      (map_ne_zero_iff _ algebraMap_padic_cp_injective).2 (hz0 σ)
    field_simp
    ring
  obtain ⟨ρ, hρc, hρ⟩ := exists_eigenChar hX (fun σ => ⟨_, hXσ σ⟩)
  have hρeq : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) =
      ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹ := fun σ =>
    eq_of_mul_eq hX ((hρ σ).symm.trans (hXσ σ))
  have hz₀ : (z σ₀ : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → (z σ : ℚ_[p]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt p (z σ) * cA = IsPerfectoidField.padicIntToWitt p 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  let ρC : Gal(PadicAlgCl p/L) →* ℂ_[p] :=
    (algebraMap ℚ_[p] ℂ_[p]).toMonoidHom.comp ((Units.coeHom ℚ_[p]).comp ρ)
  have hρC : Continuous ρC :=
    isometry_algebraMap_padic_cp.continuous.comp (Units.continuous_val.comp hρc)
  have hρ1 : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 → ρC σ = 1 := fun σ h => by
    change algebraMap ℚ_[p] ℂ_[p] ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1
    rw [h, map_one]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (hρ1 σ₀ (by rw [hρeq, hz₀, hwcoe, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _))]))
    (fun σ hσ => hρ1 σ (by rw [hρeq, hzI σ hσ, hI σ hσ, Units.val_one, one_pow, inv_one, mul_one]))
  refine ⟨f, hf, hcu.unit, fun σ => ⟨z σ, ?_, hz σ⟩⟩
  have h1 : ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 := algebraMap_padic_cp_injective (by
    rw [map_one]
    exact hall σ)
  rw [hρeq] at h1
  exact (mul_inv_eq_one₀ (hz0 σ)).1 h1 |>.symm

end EigenChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in
set_option maxHeartbeats 1600000 in
theorem iotaB_algebraMap_padic_bdRPlus (q : ℚ_[p]) :
    iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) q) = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ (iotaPlus_algebraMap_padic q))

def aInfToBCris : AInf ℂ_[p] p →+* BCris hε :=
  (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)).comp
    ((algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)))

include hζ in
set_option maxHeartbeats 1600000 in
theorem iotaB_aInfToBCris (w : AInf ℂ_[p] p) :
    iotaB hε hζ (aInfToBCris hε w) =
      algebraMap 𝔹 𝔹dR (wittToBDeRhamPlus (normInteger ℂ_[p]) p w) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ ((iotaPlus_algebraMap _).trans (iota_algebraMap w)))

include hζ in
set_option maxHeartbeats 1600000 in
theorem iotaB_periodTCris_eq :
    iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (fontaineT ε hε) :=
  (iotaB_periodTCris hε hζ).trans (congrArg _ (iota_periodT hε))

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hζ in
set_option maxHeartbeats 1600000 in
theorem galB_eq_of_smul_iotaB (σ : Gal(PadicAlgCl p/L)) {B : BCris hε}
    (h : σ • iotaB hε hζ B = iotaB hε hζ B) : galB hε σ B = B :=
  iotaB_injective hε hζ ((iotaB_galB (K := L) hε hζ σ B).trans h)

include hζ in
set_option maxHeartbeats 3200000 in

theorem isUnit_of_galB_fixed [FiniteDimensional ℚ_[p] L] {B : BCris hε} (hB0 : B ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/L), galB hε σ B = B) : IsUnit B := by
  obtain ⟨k, hk, hBk⟩ := bCris_fixed_mem_maxUnramified hε hζ (K := L) B h
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hB0
    apply iotaB_injective hε hζ
    rw [hBk, map_zero, map_zero, map_zero]
  obtain ⟨B', -, hB'⟩ := exists_bCris_fixed (K := L) hε hζ (inv_mem hk)
  have e : algebraMap 𝔹 𝔹dR (algClToBdR p k) * algebraMap 𝔹 𝔹dR (algClToBdR p k⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk0, map_one, map_one]
  have h1 : B * B' = 1 := iotaB_injective hε hζ ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) hBk hB').trans (e.trans (map_one _).symm)))
  exact isUnit_iff_exists_inv.2 ⟨B', h1⟩

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open GroundTheory.LocalField EigenWitt EigenChar

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in

theorem exists_eq_zpow_mul_unit {y : 𝔹dR} (hy : y ≠ 0) :
    ∃ (i : ℤ) (u : 𝔹ˣ), y = algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹) := by
  have ht : Irreducible (fontaineT ε hε) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 (maximalIdeal_eq_span_fontaineT hε hζ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝔹) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hy
    exact hy rfl
  obtain ⟨m, u₁, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 ht
  obtain ⟨n, u₂, hb'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 ht
  refine ⟨(m : ℤ) - n, u₁ * u₂⁻¹, ?_⟩
  have hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 ht.ne_zero
  have hu₂ : algebraMap 𝔹 𝔹dR (u₂ : 𝔹) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 u₂.ne_zero
  have hinv : algebraMap 𝔹 𝔹dR ((u₂⁻¹ : 𝔹ˣ) : 𝔹) = (algebraMap 𝔹 𝔹dR (u₂ : 𝔹))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [ha, hb', Units.val_mul]
  simp only [map_mul, map_pow]
  rw [hinv, zpow_sub₀ hT, zpow_natCast, zpow_natCast]
  field_simp

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_gal_smul_unit (σ : Gal(PadicAlgCl p/L)) {i : ℤ} {u : 𝔹} {q : ℚ_[p]}
    (h : σ • (algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR u) =
      algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) *
        (algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR u))
    (hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0) :
    ∃ q' : ℚ_[p], σ • u = algebraMap ℚ_[p] 𝔹 q' * u := by
  set χ : ℚ_[p] := ((cycloChar L σ : ℤ_[p]) : ℚ_[p])
  have hχ : χ ≠ 0 := by
    intro h0
    have := (cycloChar L σ).isUnit.map (PadicInt.Coe.ringHom (p := p))
    exact this.ne_zero h0
  refine ⟨q * χ⁻¹ ^ i, IsFractionRing.injective 𝔹 𝔹dR ?_⟩
  set A := algebraMap 𝔹 𝔹dR
  have hσT : σ • A (fontaineT ε hε) = A (algebraMap ℚ_[p] 𝔹 χ) * A (fontaineT ε hε) := by
    rw [gal_smul_algebraMap_bDeRham, gal_smul_fontaineT, map_mul]
  have hAχ : A (algebraMap ℚ_[p] 𝔹 χ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
      ((map_ne_zero_iff _ (algebraMap ℚ_[p] 𝔹).injective).2 hχ)
  rw [gal_smul_bDeRham_def, map_mul, map_zpow₀, ← gal_smul_bDeRham_def, ← gal_smul_bDeRham_def,
    hσT, gal_smul_algebraMap_bDeRham] at h
  set Aq : ℚ_[p] →+* 𝔹dR := A.comp (algebraMap ℚ_[p] 𝔹) with hAq
  have eAq : ∀ r : ℚ_[p], A (algebraMap ℚ_[p] 𝔹 r) = Aq r := fun r => rfl
  rw [map_mul, eAq, map_mul, map_zpow₀, map_inv₀]
  rw [eAq, eAq] at h
  rw [eAq] at hAχ
  have hTi : A (fontaineT ε hε) ^ i ≠ 0 := zpow_ne_zero _ hT
  have hχi : Aq χ ^ i ≠ 0 := zpow_ne_zero _ hAχ
  rw [mul_zpow] at h
  have h2 : A (fontaineT ε hε) ^ i * (Aq χ ^ i * A (σ • u)) =
      A (fontaineT ε hε) ^ i * (Aq q * A u) := by
    linear_combination h
  have h3 := mul_left_cancel₀ hTi h2
  rw [inv_zpow', zpow_neg]
  field_simp
  linear_combination h3

variable (p) in

def SenTateCharacters : Prop :=
  ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ), Continuous η →
    ∀ x : ℂ_[p], x ≠ 0 → (∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (η σ) * x) →
      (η '' {σ | ∀ u ∈ unramifiedClosure p, σ u = u}).Finite

theorem exists_twist_of_finite_image {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] K] {x : ℂ_[p]} (hx0 : x ≠ 0) (ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ)
    (hψc : Continuous ψ) (hψx : ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x)
    (hfin : (ψ '' {σ | ∀ u ∈ unramifiedClosure p, σ u = u}).Finite) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), ∃ hKL : K ≤ L, FiniteDimensional ℚ_[p] L ∧
      ∃ (f : ℕ) (c : (AInf ℂ_[p] p)ˣ), 0 < f ∧
        ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p],
          (z : ℚ_[p]) = ((ψ (galRes hKL σ) : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
          σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  obtain ⟨E, hE, hEψ⟩ := exists_fixingSubgroup_of_finite_image ψ hψc _ hfin
  have : IsScalarTower ℚ_[p] K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hE' : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  obtain ⟨L, hL⟩ : ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), L = E.restrictScalars ℚ_[p] :=
    ⟨_, rfl⟩
  have hLE : ∀ y, y ∈ L ↔ y ∈ E := fun y => by rw [hL]; exact IntermediateField.mem_restrictScalars _
  have hKL : K ≤ L := fun k hk => (hLE _).2 (E.algebraMap_mem ⟨k, hk⟩)
  have : FiniteDimensional ℚ_[p] L := by subst hL; exact hE'
  have hres : ∀ σ : Gal(PadicAlgCl p/L), galRes hKL σ ∈ E.fixingSubgroup := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun e he => σ.commutes ⟨e, (hLE e).2 he⟩
  obtain ⟨ψL, -, hψLx⟩ := exists_eigenChar (K := L) hx0 (fun σ => ⟨_, hψx (galRes hKL σ)⟩)
  have hψL : ∀ σ, ψL σ = ψ (galRes hKL σ) := fun σ =>
    Units.ext (eq_of_mul_eq hx0 ((hψLx σ).symm.trans (hψx (galRes hKL σ))))
  obtain ⟨f, hf, c, hc⟩ := exists_twist_of_unramified hx0 ψL hψLx (fun σ hσ => by
    have h3 := mem_inertia_of_degree hσ
    rw [hψL]
    refine hEψ _ (hres σ) fun u hu => ?_
    rw [galRes_apply]
    exact h3 u hu)
  refine ⟨L, hKL, this, f, c, hf, fun σ => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hc σ
  exact ⟨z, by rw [hz, hψL], hzc⟩

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_unramified_twist (hST : SenTateCharacters p)
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K] {y : 𝔹dR}
    (hy0 : y ≠ 0) (hyσ : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p],
      σ • y = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) * y) :
    ∃ (i : ℤ) (u : 𝔹ˣ), y = algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹) ∧
      ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ FiniteDimensional ℚ_[p] L ∧
      ∃ (f : ℕ) (c : (AInf ℂ_[p] p)ˣ) (ψ : Gal(PadicAlgCl p/L) → ℚ_[p]ˣ), 0 < f ∧
        (∀ σ : Gal(PadicAlgCl p/L), σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 (ψ σ) * u) ∧
        ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p], (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
          σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  classical
  obtain ⟨i, u, hyu⟩ := exists_eq_zpow_mul_unit hε hζ hy0
  have hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 (fontaineT_ne_zero hε hζ)
  have huσ : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 q * u :=
    fun σ => by
      obtain ⟨q, hq⟩ := hyσ σ
      exact exists_gal_smul_unit hε σ (by rw [← hyu]; exact hq) hT
  have hx0 : thetaAlgHom p (u : 𝔹) ≠ 0 := (u.isUnit.map (thetaAlgHom p)).ne_zero
  have hθ : ∀ {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/L)) (q : ℚ_[p]),
      σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 q * u →
        σ • thetaAlgHom p (u : 𝔹) = algebraMap ℚ_[p] ℂ_[p] q * thetaAlgHom p (u : 𝔹) := by
    intro L σ q h
    rw [thetaAlgHom_apply, ← thetaBDeRhamPlusField_gal_smul, h, ← thetaAlgHom_apply, map_mul,
      AlgHom.commutes]
    rfl
  obtain ⟨ψ, hψc, hψx⟩ := exists_eigenChar hx0 fun σ => (huσ σ).imp fun q h => hθ σ q h
  obtain ⟨L, hKL, hL, f, c, hf, hc⟩ := exists_twist_of_finite_image hx0 ψ hψc hψx
    (hST K ψ hψc _ hx0 hψx)
  refine ⟨i, u, hyu, L, hKL, hL, f, c, fun σ => ψ (galRes hKL σ), hf, fun σ => ?_, hc⟩
  obtain ⟨q, hq⟩ := huσ (galRes hKL σ)
  have hq' : σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 q * u := hq
  have h2 : q = ψ (galRes hKL σ) := eq_of_mul_eq hx0 ((hθ σ q hq').symm.trans (hψx (galRes hKL σ)))
  rw [hq', h2]

theorem isUnit_of_fixed_twist {R F G : Type*} [CommRing R] [IsDomain R] [Field F] [Group G]
    [MulSemiringAction G F] (g : R →+* F) (hg : Function.Injective g) (act : G → R → R)
    (hequiv : ∀ σ y, g (act σ y) = σ • g y)
    (hunit : ∀ B : R, B ≠ 0 → (∀ σ, act σ B = B) → IsUnit B)
    {b : R} (hb0 : b ≠ 0) {f : ℕ} (hf : 0 < f) (c T : Rˣ) (n : ℤ)
    (hfix : ∀ σ : G, σ • (g b ^ f * (g ↑c)⁻¹ * g ↑T ^ n) = g b ^ f * (g ↑c)⁻¹ * g ↑T ^ n) :
    IsUnit b := by
  set B := b ^ f * ↑c⁻¹ * ↑(T ^ n) with hB
  have hgT : g ↑(T ^ n) = g ↑T ^ n := by
    have h := congrArg Units.val (map_zpow (Units.map (g : R →* F)) T n)
    rw [Units.val_zpow_eq_zpow_val] at h
    exact h
  have hgB : g B = g b ^ f * (g ↑c)⁻¹ * g ↑T ^ n := by
    rw [hB, map_mul, map_mul, map_pow, map_units_inv, hgT]
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hb0) (Units.ne_zero _)) (Units.ne_zero _)
  have hBu : IsUnit B := hunit B hB0 fun σ => hg (by rw [hequiv, hgB, hfix])
  have hbf : b ^ f = B * ↑c * ↑(T ^ (-n)) := by
    rw [hB]
    have e1 : (↑c⁻¹ : R) * ↑c = 1 := Units.inv_mul c
    have e2 : (↑(T ^ n) : R) * ↑(T ^ (-n)) = 1 := by
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    calc b ^ f = b ^ f * ((↑c⁻¹ * ↑c) * (↑(T ^ n) * ↑(T ^ (-n)))) := by rw [e1, e2, one_mul, mul_one]
      _ = _ := by ring
  have hbfu : IsUnit (b ^ f) := by
    rw [hbf]
    exact (hBu.mul c.isUnit).mul (Units.isUnit _)
  exact (isUnit_pow_iff hf.ne').1 hbfu

include hζ in
set_option maxHeartbeats 3200000 in

theorem isUnit_of_twist {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    {b : BCris hε} (hb0 : b ≠ 0) {i : ℤ} {u : 𝔹ˣ}
    (hyu : iotaB hε hζ b = algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹))
    {f : ℕ} (hf : 0 < f) {c : (AInf ℂ_[p] p)ˣ} {ψ : Gal(PadicAlgCl p/L) → ℚ_[p]ˣ}
    (huL : ∀ σ : Gal(PadicAlgCl p/L), σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 (ψ σ) * u)
    (hc : ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p], (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
      σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p)) :
    IsUnit b := by
  have := isDomain_bCris hε hζ
  have hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 (fontaineT_ne_zero hε hζ)
  obtain ⟨C, hCdef⟩ : ∃ C : 𝔹dR,
      C = algebraMap 𝔹 𝔹dR (wittToBDeRhamPlus (normInteger ℂ_[p]) p (c : AInf ℂ_[p] p)) := ⟨_, rfl⟩
  have hC0 : C ≠ 0 := by
    rw [hCdef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
      ((c.isUnit.map (wittToBDeRhamPlus (normInteger ℂ_[p]) p)).ne_zero)
  have hCσ : ∀ σ : Gal(PadicAlgCl p/L),
      σ • C = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 (ψ σ)) ^ f * C := fun σ => by
    obtain ⟨z, hz, hzc⟩ := hc σ
    rw [hCdef, gal_smul_algebraMap_bDeRham, gal_smul_wittToBDeRhamPlus, hzc, map_mul, map_mul,
      ← IsPerfectoidField.algebraMap_padic_coe, hz, map_pow, map_pow]
  obtain ⟨cB, hcBdef⟩ : ∃ cB : BCris hε, cB = aInfToBCris hε (c : AInf ℂ_[p] p) := ⟨_, rfl⟩
  have hcB : IsUnit cB := by rw [hcBdef]; exact c.isUnit.map _
  have hιc : iotaB hε hζ ↑hcB.unit = C := by rw [IsUnit.unit_spec, hcBdef, hCdef, iotaB_aInfToBCris]
  have hιT : iotaB hε hζ ↑(isUnit_periodTCris hε).unit = algebraMap 𝔹 𝔹dR (fontaineT ε hε) := by
    rw [IsUnit.unit_spec, iotaB_periodTCris_eq]
  refine isUnit_of_fixed_twist (G := Gal(PadicAlgCl p/L)) (iotaB hε hζ) (iotaB_injective hε hζ)
    (fun σ y => galB hε σ y) (fun σ y => iotaB_galB (K := L) hε hζ σ y)
    (fun B hB0 hB => isUnit_of_galB_fixed hε hζ (L := L) hB0 hB) hb0 hf hcB.unit
    (isUnit_periodTCris hε).unit (-(i * f)) fun σ => ?_
  rw [hιc, hιT, hyu]
  have hψ0 : algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 (ψ σ)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
      ((map_ne_zero_iff _ (algebraMap ℚ_[p] 𝔹).injective).2 (Units.ne_zero _))
  have hsimp : (algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹)) ^ f * C⁻¹ *
      algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ (-(i * f)) = algebraMap 𝔹 𝔹dR (u : 𝔹) ^ f * C⁻¹ := by
    rw [mul_pow, ← zpow_natCast (_ ^ i), ← zpow_mul, zpow_neg]
    have hTz : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ (i * (f : ℤ)) ≠ 0 := zpow_ne_zero _ hT
    field_simp
  rw [hsimp, gal_smul_bDeRham_def, map_mul, map_pow, map_inv₀, ← gal_smul_bDeRham_def,
    ← gal_smul_bDeRham_def, gal_smul_algebraMap_bDeRham, huL σ, hCσ σ, map_mul, mul_pow]
  field_simp

include hζ in
set_option maxHeartbeats 3200000 in

theorem isUnit_of_forall_galB_eq_mul (hST : SenTateCharacters p)
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K] {b : BCris hε}
    (hb0 : b ≠ 0)
    (hb : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], galB hε σ b = algebraMap ℚ_[p] (BCris hε) q * b) :
    IsUnit b := by
  have hy0 : iotaB hε hζ b ≠ 0 := (map_ne_zero_iff _ (iotaB_injective hε hζ)).2 hb0
  obtain ⟨i, u, hyu, L, -, hL, f, c, ψ, hf, huL, hc⟩ := exists_unramified_twist hε hζ hST hy0
    (fun σ => by
      obtain ⟨q, hq⟩ := hb σ
      refine ⟨q, ?_⟩
      rw [← iotaB_galB (K := K) hε hζ σ b, hq, map_mul, iotaB_algebraMap_padic_bdRPlus])
  exact isUnit_of_twist hε hζ (L := L) hb0 hyu hf huL hc

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isRegular_bCris (hST : SenTateCharacters p) {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] K] :
    letI := isDomain_bCris hε hζ
    letI := galBAction (K := K) hε
    haveI := smulCommClass_galBAction (K := K) hε
    IsRegular Gal(PadicAlgCl p/K) ℚ_[p] (BCris hε) :=
  letI := isDomain_bCris hε hζ
  letI := galBAction (K := K) hε
  haveI := smulCommClass_galBAction (K := K) hε
  { image_fixedPoints := image_fixedPoints_fractionRing (K := K) hε hζ
    isUnit_of_mem_span := fun b hb0 hb => isUnit_of_forall_galB_eq_mul hε hζ hST hb0 fun σ => by
      obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.1 (hb σ)
      exact ⟨q, (hq.symm.trans (Algebra.smul_def q b) :)⟩ }

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

theorem norm_eq_one_of_compactSpace (η : G →* ℚ_[p]ˣ) (hη : Continuous η) (σ : G) :
    ‖((η σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  set f : G → ℝ := fun τ => ‖((η τ : ℚ_[p]ˣ) : ℚ_[p])‖ with hf
  have hcont : Continuous f := (Units.continuous_val.comp hη).norm
  obtain ⟨τ₀, -, hτ₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hbound : ∀ τ, f τ ≤ f τ₀ := fun τ => hτ₀ (Set.mem_univ τ)
  have hpow : ∀ τ : G, ∀ n : ℕ, f (τ ^ n) = f τ ^ n := by
    intro τ n
    simp only [hf, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ τ, f τ ≤ 1 := by
    intro τ
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop (f τ₀) |>.exists
    have := hbound (τ ^ n)
    rw [hpow] at this
    linarith
  have hmul : f σ * f σ⁻¹ = 1 := by
    simp only [hf, map_inv, ← norm_mul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero _), norm_one]
  have h0 : 0 ≤ f σ⁻¹ := norm_nonneg _
  apply le_antisymm (hle σ)
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt (hle σ⁻¹)
  linarith

theorem exists_continuous_units_padicInt_lift (η : G →* ℚ_[p]ˣ) (hη : Continuous η) :
    ∃ η' : G →* ℤ_[p]ˣ, Continuous η' ∧ ∀ σ, (((η' σ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = η σ := by
  have h1 := norm_eq_one_of_compactSpace η hη
  let η' : G →* ℤ_[p]ˣ :=
    { toFun := fun σ => PadicInt.mkUnits (h1 σ)
      map_one' := by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, map_one]
        rfl
      map_mul' := fun σ τ => by
        apply Units.ext
        apply PadicInt.ext
        rw [PadicInt.mkUnits_eq, Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq,
          PadicInt.mkUnits_eq, map_mul, Units.val_mul] }
  refine ⟨η', ?_, fun σ => PadicInt.mkUnits_eq (h1 σ)⟩
  have hval : Continuous fun σ => ((η σ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_val.comp hη
  have hinv : Continuous fun σ => (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) :=
    Units.continuous_val.comp (continuous_inv.comp hη)
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun σ => (⟨((η σ : ℚ_[p]ˣ) : ℚ_[p]), (h1 σ).le⟩ : ℤ_[p])
    exact hval.subtype_mk _
  · have hn : ∀ σ, ‖(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := fun σ => by
      rw [← map_inv]; exact (h1 σ⁻¹).le
    have e : (fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) =
        fun σ => (⟨(((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), hn σ⟩ : ℤ_[p]) := by
      funext σ
      apply PadicInt.ext
      rw [← map_inv η' σ]
      show ((PadicInt.mkUnits (h1 σ⁻¹) : ℤ_[p]) : ℚ_[p]) = (((η σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])
      rw [PadicInt.mkUnits_eq, map_inv]
    change Continuous fun σ => (((η' σ)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
    rw [e]
    exact hinv.subtype_mk _

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open CyclNorms GroundTheory.LocalField ValuativeRel SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]

namespace SenTateChar

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
  {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

theorem eq_zero_of_mem_inertiaGal (hη : Continuous η) {τ : Gal(PadicAlgCl p/K)}
    (hτ : τ ∈ inertiaGal K) (hτ2 : η τ ∈ unitsOneAdd p 2) (hτ1 : η τ ≠ 1) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  have hA := artinImage_ne_bot hη hτ hτ2 hτ1
  have hfin : ∀ k, FiniteDimensional K (charTower η k) := fun k => finiteDimensional_charTower hη k
  have : IsAbelianGalois K (charTower η 2) := isAbelianGalois_charTower hη 2

  have h2 : ∀ n, conductor (charTower η 2) ≤ n → 2 ≤ artinLevel K η n := by
    intro n hn
    obtain ⟨-, a, ha, ha'⟩ := artinLevel_spec (hA n)
    have ha2 := artinImage_le_of_conductor_le hη hn ha
    by_contra hlt
    push Not at hlt
    exact ha' (unitsOneAdd_antitone (by omega) ha2)

  obtain ⟨n₁, hn₁⟩ := exists_map_pow_unitFiltrationUnits (K := K) p
  set n₀ := max (conductor (charTower η 2)) n₁
  have hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1 :=
    fun n hn => artinLevel_add hη hA (h2 n (le_of_max_le_left hn)) (hn₁ n (le_of_max_le_right hn))
  have h2₀ : 2 ≤ artinLevel K η n₀ := h2 n₀ (le_max_left _ _)

  obtain ⟨b, hb, hb'⟩ := exists_level hτ1
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) hτ2)

  set π : PadicAlgCl p := algebraMap K (PadicAlgCl p) (baseUnif K : K)
  set C : ℝ := ‖π ^ (-(2 * absRamificationIndex K : ℤ))‖
  have hbound : ∀ n, max (artinLevel K η n₀) b ≤ n → ∀ m, ∀ y ∈ charTower η m,
      ‖normTrace (charTower η n) y‖ ≤ C * ‖y‖ := by
    intro n hn m y hy
    have h := nrm_normTrace_charTower_le hη hA le_rfl h2₀ hper hb2 hb hb'
      (le_of_max_le_right hn) (le_of_max_le_left hn) hy
    have e : baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) =
        nrm K (π ^ (-(2 * absRamificationIndex K : ℤ))) := by
      rw [nrm_zpow, ← Real.rpow_intCast]
      push_cast
      rfl
    rw [e, ← nrm_mul, nrm_le_nrm_iff_norm_le', norm_mul] at h
    exact h
  refine eq_zero_of_tower K η (charTower η) (charTower_mono η)
    (fun σ k y hy => map_mem_charTower hη σ hy) (fun σ hσ => ?_) C (max (artinLevel K η n₀) b)
    hbound (fun n hn => ?_) hx
  · refine eq_one_of_forall_mem_unitsOneAdd fun k => ?_
    have := hσ k
    rwa [fixingSubgroup_charTower hη, mem_charTowerGal] at this
  · obtain ⟨h1, h1'⟩ := pow_prime_pow_mem_not_mem hb2 hb hb' (n - b)
    rw [Nat.add_sub_cancel' (le_of_max_le_right hn)] at h1 h1'
    refine ⟨τ ^ p ^ (n - b), ?_, ?_⟩
    · rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_pow]
      exact h1
    · rw [map_pow]
      intro h
      exact h1' (h ▸ one_mem _)

end SenTateChar

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

theorem finite_image_inertiaGal_of_invariant (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (hη : Continuous η)
    (hx : ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ σ : Gal(PadicAlgCl p/K),
      algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Finite := by
  by_contra hinf
  obtain ⟨τ, hτ, hτ2, hτ1⟩ := exists_mem_inertiaGal_unitsOneAdd_two K η hη hinf
  obtain ⟨x, hx0, hx⟩ := hx
  exact hx0 (eq_zero_of_mem_inertiaGal hη hτ hτ2 hτ1 hx)

theorem finite_image_inertiaGal_of_invariant_padic (η : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ)
    (hη : Continuous η)
    (hx : ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ σ : Gal(PadicAlgCl p/K),
      algebraMap ℚ_[p] ℂ_[p] (η σ : ℚ_[p]) * (σ • x) = x) :
    (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Finite := by
  obtain ⟨η', hη', hηη'⟩ := exists_continuous_units_padicInt_lift η hη
  have h := finite_image_inertiaGal_of_invariant K η' hη' (by
    obtain ⟨x, hx0, hx⟩ := hx
    exact ⟨x, hx0, fun σ => by rw [hηη']; exact hx σ⟩)
  refine (h.image (Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨η' σ, ⟨σ, hσ, rfl⟩, ?_⟩
  ext
  rw [Units.coe_map, ← hηη' σ]
  rfl

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_inertiaGal_of_forall_unramifiedClosure {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {σ : Gal(PadicAlgCl p/K)} (hσ : ∀ u ∈ unramifiedClosure p, σ u = u) : σ ∈ inertiaGal K := by
  intro y hy
  have hc : ‖(y : ℂ_[p])‖ ≤ 1 := by rwa [PadicComplex.norm_extends]
  obtain ⟨k, hk⟩ := eventually_approx_pow hc 1
  obtain ⟨u, hu, hyu⟩ := hk k le_rfl
  set n := p ^ k with hn
  have hpn : ‖(p : ℂ_[p])‖ = ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.norm_extends]
    congr 1
    simp
  have hd : ‖y ^ n - u‖ ≤ ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.norm_extends, ← hpn]
    have e : ((y ^ n - u : PadicAlgCl p) : ℂ_[p]) = (y : ℂ_[p]) ^ n - (u : ℂ_[p]) := by
      simp only [UniformSpace.Completion.coe_sub, PadicComplex.coe_eq, map_pow]
    rw [e]
    simpa using hyu
  have hσn : ‖σ y ^ n - y ^ n‖ ≤ ‖(p : PadicAlgCl p)‖ := by
    have e : σ y ^ n - y ^ n = σ (y ^ n - u) - (y ^ n - u) := by
      rw [map_sub, map_pow, hσ u hu]
      ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans (max_le ?_ hd)
    rw [norm_gal_apply]
    exact hd
  have hσy : ‖σ y‖ ≤ 1 := by rwa [norm_gal_apply]
  have hdiff : ‖σ y - y‖ ≤ 1 := (norm_sub_le_max_of_ultrametric _ _).trans (max_le hσy hy)
  let a : normInteger (PadicAlgCl p) := ⟨σ y - y, mem_normInteger.2 hdiff⟩
  let b : normInteger (PadicAlgCl p) := ⟨y, mem_normInteger.2 hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out a b k
  have hr' := congrArg (fun z : normInteger (PadicAlgCl p) => (z : PadicAlgCl p)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, a, b,
    sub_add_cancel] at hr'
  have e : (σ y - y) ^ n = (σ y ^ n - y ^ n) - (p : PadicAlgCl p) * (σ y - y) * y * r := by
    rw [hn, hr']
    ring
  have hr1 : ‖(r : PadicAlgCl p)‖ ≤ 1 := mem_normInteger.1 r.2
  have hlt : ‖σ y - y‖ ^ n < 1 := by
    rw [← norm_pow, e]
    refine (norm_sub_le_max_of_ultrametric (σ y ^ n - y ^ n)
      ((p : PadicAlgCl p) * (σ y - y) * y * r)).trans_lt (max_lt (hσn.trans_lt
      norm_natCast_p_algCl_lt_one) ?_)
    rw [norm_mul, norm_mul, norm_mul]
    rw [mul_assoc, mul_assoc]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg (p : PadicAlgCl p)) ?_)
      (norm_natCast_p_algCl_lt_one (p := p))
    exact mul_le_one₀ hdiff (by positivity) (mul_le_one₀ hy (norm_nonneg _) hr1)
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hp.out.ne_zero)).1 hlt

namespace ACris

theorem senTateCharacters : SenTateCharacters p := by
  intro K _ η hη x hx0 hx
  have hfin := finite_image_inertiaGal_of_invariant_padic K η⁻¹
    (show Continuous fun σ => (η σ)⁻¹ from hη.inv) ⟨x, hx0, fun σ => by
      rw [hx σ, ← mul_assoc, ← map_mul, MonoidHom.inv_apply, Units.inv_mul, map_one, one_mul]⟩
  refine (hfin.image (·⁻¹)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  exact ⟨η⁻¹ σ, ⟨σ, mem_inertiaGal_of_forall_unramifiedClosure hσ, rfl⟩, by simp⟩

end ACris

end GroundTheory.PAdicHodge
end
end
