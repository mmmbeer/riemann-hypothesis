import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMassConstOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA
import Formalism.FlagUnipotentLattices.ArithmeticIdentityEntries
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVR

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mem_loc_iff (p : Ideal (𝓞 K)) (N : Submodule (𝓞 K) K) (x : K) :
    x ∈ loc (K := K) p N ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ N := Iff.rfl

theorem hcompl_le_primeCompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    hcompl (K := K) p ≤ p.primeCompl := by
  have := hp.isPrime
  unfold hcompl
  rw [Submonoid.closure_le]
  intro s hs
  exact hs.1

theorem one_mem_locR (p : Ideal (𝓞 K)) : (1 : K) ∈ locR (K := K) p :=
  ⟨1, (hcompl (K := K) p).one_mem, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩

theorem mul_mem_locR {p : Ideal (𝓞 K)} {x y : K} (hx : x ∈ locR (K := K) p) (hy : y ∈ locR (K := K) p) :
    x * y ∈ locR (K := K) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, (hcompl (K := K) p).mul_mem hs ht, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hty
  refine Submodule.mem_one.2 ⟨r * r', ?_⟩
  rw [map_mul, hr, hr', Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ hcompl (K := K) p) :
    conjO K s ∈ hcompl (K := K) p := by
  have key : hcompl (K := K) p ≤ (hcompl (K := K) p).comap (conjO K : 𝓞 K →* 𝓞 K) := by
    conv_lhs => unfold hcompl
    rw [Submonoid.closure_le]
    intro s hs
    show conjO K s ∈ hcompl (K := K) p
    apply Submonoid.subset_closure
    refine ⟨hs.2 (conjO K s) rfl, fun t ht => ?_⟩
    have e : t = s := by
      apply RingOfIntegers.ext
      have : (t : K) = star (star (s : K)) := ht
      rw [star_star] at this
      exact this
    rw [e]
    exact hs.1
  exact key hs

theorem star_mem_locR {p : Ideal (𝓞 K)} {x : K} (hx : x ∈ locR (K := K) p) :
    star x ∈ locR (K := K) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨conjO K s, conjO_mem_hcompl hs, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
  refine Submodule.mem_one.2 ⟨conjO K r, ?_⟩
  rw [Algebra.smul_def] at hr ⊢
  have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl
  have e2 : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s) := rfl
  rw [e1, e2, hr, star_mul']

theorem mem_one_of_locR {x : K} (hx : ∀ p : Ideal (𝓞 K), p.IsMaximal → x ∈ locR (K := K) p) :
    x ∈ (1 : Submodule (𝓞 K) K) := by
  let J : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K x)
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hs, hsx⟩ := hx p hp
    have hsJ : s ∈ J := by
      show LinearMap.toSpanSingleton (𝓞 K) K x s ∈ (1 : Submodule (𝓞 K) K)
      rw [LinearMap.toSpanSingleton_apply]
      exact hsx
    exact hcompl_le_primeCompl hp hs (hJp hsJ)
  have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
  change LinearMap.toSpanSingleton (𝓞 K) K x 1 ∈ (1 : Submodule (𝓞 K) K) at h1
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at h1

theorem exists_local (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ z : K, star z * z = 1 ∧ ∀ y : K, y ∈ loc (K := K) p M ↔ ∃ r ∈ locR (K := K) p, y = r * z := by
  obtain ⟨g, hg, hgM⟩ := hM.2 p hp
  refine ⟨g 1, (mem_isom_iff h1 g).1 hg, fun y => ?_⟩
  have hgx : ∀ x, g x = x * g 1 := by
    intro x
    have : g x = g (x • (1 : K)) := by simp
    rw [this, map_smul, smul_eq_mul]
  rw [← hgM, mem_gmap]
  constructor
  · intro hy
    refine ⟨g.symm y, hy, ?_⟩
    rw [← hgx, LinearEquiv.apply_symm_apply]
  · rintro ⟨r, hr, rfl⟩
    rw [← hgx, LinearEquiv.symm_apply_apply]
    exact hr

theorem norm_unit (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M M' : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) (hM' : M' ∈ genus h (1 : Submodule (𝓞 K) K)) {a : K}
    (he : M = Submodule.span (𝓞 K) {a} * M') :
    a * star a ∈ (1 : Submodule (𝓞 K) K) ∧ (a * star a)⁻¹ ∈ (1 : Submodule (𝓞 K) K) := by
  have key : ∀ p : Ideal (𝓞 K), p.IsMaximal →
      a * star a ∈ locR (K := K) p ∧ (a * star a)⁻¹ ∈ locR (K := K) p := by
    intro p hp
    obtain ⟨z, hz, hzM⟩ := exists_local h h1 hM hp
    obtain ⟨z', hz', hzM'⟩ := exists_local h h1 hM' hp
    have hl : loc (K := K) p M = Submodule.span (𝓞 K) {a} * loc (K := K) p M' := by
      rw [he, loc_mul hp]
    have hzin : z ∈ loc (K := K) p M := (hzM z).2 ⟨1, one_mem_locR p, (one_mul z).symm⟩
    rw [hl, Submodule.mem_span_singleton_mul] at hzin
    obtain ⟨m, hm, hmz⟩ := hzin
    obtain ⟨r, hr, rfl⟩ := (hzM' m).1 hm
    have haz : a * z' ∈ loc (K := K) p M := by
      rw [hl, Submodule.mem_span_singleton_mul]
      exact ⟨z', (hzM' z').2 ⟨1, one_mem_locR p, (one_mul z').symm⟩, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := (hzM _).1 haz
    have hz1 : z * star z = 1 := by rw [mul_comm]; exact hz
    have hz1' : z' * star z' = 1 := by rw [mul_comm]; exact hz'
    have t1 := congrArg (fun t => t * star t) hr'e
    simp only [star_mul'] at t1
    have e1 : a * star a = r' * star r' := by
      linear_combination t1 - (a * star a) * hz1' + (r' * star r') * hz1
    have t2 := congrArg (fun t => t * star t) hmz
    simp only [star_mul'] at t2
    have e2 : a * star a * (r * star r) = 1 := by
      linear_combination t2 - (a * star a * r * star r) * hz1' + hz1
    refine ⟨e1 ▸ mul_mem_locR hr' (star_mem_locR hr'), ?_⟩
    rw [inv_eq_of_mul_eq_one_right e2]
    exact mul_mem_locR hr (star_mem_locR hr)
  exact ⟨mem_one_of_locR fun p hp => (key p hp).1, mem_one_of_locR fun p hp => (key p hp).2⟩

end Formalism.MainNotions.BridgeLemVR

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVC

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isFrac {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : IsFractional (𝓞 K)⁰ M :=
  FractionalIdeal.isFractional_of_fg hM.fg

def fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M, isFrac hM⟩

theorem coe_fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) :
    ((fracI hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M := FractionalIdeal.coe_mk _ _

theorem frac_ne_zero {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : fracI hM ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := exists_ne_zero_of_isLattice hM
  intro e
  have h1 : a ∈ fracI hM := by rw [← FractionalIdeal.mem_coe, coe_fracI]; exact ha
  rw [e] at h1
  exact h0 ((FractionalIdeal.mem_zero_iff _).1 h1)

def fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 _ (frac_ne_zero hM)

theorem coe_fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) :
    (((fracU hM : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M :=
  coe_fracI hM

theorem exists_eq_span_mul {M M' : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M)
    (hM' : Submodule.IsLattice K M') (he : ClassGroup.mk K (fracU hM) = ClassGroup.mk K (fracU hM')) :
    ∃ a : K, a ≠ 0 ∧ M = Submodule.span (𝓞 K) {a} * M' := by
  have h1 : ClassGroup.mk K (fracU hM * (fracU hM')⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨⟨a, ha⟩⟩ := h1
  have hMa : M = Submodule.span (𝓞 K) {a} * M' := by
    calc M = (((fracU hM * (fracU hM')⁻¹ * fracU hM' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by rw [inv_mul_cancel_right, coe_fracU]
      _ = Submodule.span (𝓞 K) {a} * M' := by
          rw [Units.val_mul, FractionalIdeal.coe_mul, ha, coe_fracU]
  refine ⟨a, fun h0 => ?_, hMa⟩
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_isLattice hM
  rw [hMa, h0, Submodule.mem_span_singleton_mul] at hx
  obtain ⟨y, -, hy⟩ := hx
  rw [zero_mul] at hy
  exact hx0 hy.symm

theorem exists_unitF {u : K} (hu0 : u ≠ 0) (hu : u ∈ (1 : Submodule (𝓞 K) K))
    (hu' : u⁻¹ ∈ (1 : Submodule (𝓞 K) K)) (hs : star u = u) :
    ∃ t : (𝓞 (cmF K))ˣ, (((t : 𝓞 (cmF K)) : cmF K) : K) = u := by
  have intF : ∀ x : cmF K, (x : K) ∈ (1 : Submodule (𝓞 K) K) → IsIntegral ℤ x := by
    intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hx
    have hK : IsIntegral ℤ (x : K) := by rw [← hr]; exact RingOfIntegers.isIntegral_coe r
    exact (isIntegral_algHom_iff ((cmF K).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hK
  have hs' : star u⁻¹ = u⁻¹ := by rw [star_inv₀, hs]
  let x : cmF K := ⟨u, (mem_cmF_iff K u).2 hs⟩
  let y : cmF K := ⟨u⁻¹, (mem_cmF_iff K _).2 hs'⟩
  let t0 : 𝓞 (cmF K) := ⟨x, intF x hu⟩
  let t1 : 𝓞 (cmF K) := ⟨y, intF y hu'⟩
  have hxy : t0 * t1 = 1 := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    show u * u⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  exact ⟨⟨t0, t1, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

def iota (K : Type) [Field K] [NumberField K] [StarRing K] : (𝓞 (cmF K))ˣ →* K :=
  ((cmF K).val.toRingHom.comp (algebraMap (𝓞 (cmF K)) (cmF K))).toMonoidHom.comp (Units.coeHom _)

theorem exists_unitK (v : (𝓞 (cmF K))ˣ) : ∃ w : (𝓞 K)ˣ, algebraMap (𝓞 K) K (w : 𝓞 K) = iota K v :=
  ⟨Units.map (RingOfIntegers.mapRingHom ((cmF K).val.toRingHom)).toMonoidHom v, rfl⟩

theorem gmap_smul {b : K} (hb : b ≠ 0) (N : Submodule (𝓞 K) K) :
    gmap (LinearEquiv.smulOfNeZero K K b hb) N = Submodule.span (𝓞 K) {b} * N := by
  ext y
  rw [mem_gmap, Submodule.mem_span_singleton_mul]
  have hs : ∀ z, (LinearEquiv.smulOfNeZero K K b hb).symm z = b⁻¹ * z := fun z => rfl
  constructor
  · intro hy
    refine ⟨b⁻¹ * y, by rw [← hs]; exact hy, ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  · rintro ⟨n, hn, rfl⟩
    rw [hs, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
    exact hn

theorem gmap_one (N : Submodule (𝓞 K) K) : gmap (1 : K ≃ₗ[K] K) N = N := by
  ext y
  rw [mem_gmap]
  rfl

theorem span_unit_mul (w : (𝓞 K)ˣ) (N : Submodule (𝓞 K) K) :
    Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (w : 𝓞 K)} * N = N := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [← Algebra.smul_def]
    exact N.smul_mem _ hn
  · intro hy
    refine ⟨((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • y, N.smul_mem _ hy, ?_⟩
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end Formalism.MainNotions.BridgeLemVC

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVN

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fixF (K : Type) [Field K] [NumberField K] [StarRing K] :
    ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap (cmF K) K) := by
  intro a
  constructor
  · intro h
    exact ⟨⟨a, (mem_cmF_iff K a).2 h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact star_coe_cmF K x

theorem card_quot (hK : IsCMUnram K) :
    Nat.card ((𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range) = 2 ^ fDeg K := by
  rw [Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.unitsSquareIndex (cmF K) (isReal_cmF hK),
    (discrTower K (cmF K) hK (fixF K)).2.1]

theorem span_mul_span1 (x y : K) :
    Submodule.span (𝓞 K) {x} * Submodule.span (𝓞 K) {y} = Submodule.span (𝓞 K) {x * y} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem iota_inv (x : (𝓞 (cmF K))ˣ) : iota K x⁻¹ = (iota K x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

theorem iota_ne_zero (x : (𝓞 (cmF K))ˣ) : iota K x ≠ 0 := by
  intro h0
  have := congrArg (iota K) (mul_inv_cancel x)
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

theorem star_iota (x : (𝓞 (cmF K))ˣ) : star (iota K x) = iota K x := star_coe_cmF K _

theorem card_classReps_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0)
    (s : Finset (Submodule (𝓞 K) K)) (hs : IsClassReps h (1 : Submodule (𝓞 K) K) s) :
    s.card ≤ classNumber K * 2 ^ fDeg K := by
  classical
  have hlat : ∀ M : s, Submodule.IsLattice K (M : Submodule (𝓞 K) K) := fun M => (hs.1 M M.2).1
  let cl : s → ClassGroup (𝓞 K) := fun M => ClassGroup.mk K (fracU (hlat M))
  let base : s → s := fun M => Classical.choose (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have hbase : ∀ M, cl (base M) = cl M := fun M =>
    Classical.choose_spec (⟨M, rfl⟩ : ∃ B : s, cl B = cl M)
  have gen : ∀ (γ γ' : ClassGroup (𝓞 K)) (hγ : ∃ B : s, cl B = γ) (hγ' : ∃ B : s, cl B = γ'),
      γ = γ' → Classical.choose hγ = Classical.choose hγ' := by
    intro γ γ' hγ hγ' e
    subst e
    rfl
  have hbase_eq : ∀ M M', cl M = cl M' → base M = base M' := fun M M' e => gen _ _ _ _ e
  have hex : ∀ M : s, ∃ a : K, a ≠ 0 ∧
      (M : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) {a} * ((base M : s) : Submodule (𝓞 K) K) :=
    fun M => exists_eq_span_mul (hlat M) (hlat (base M)) (hbase M).symm
  choose a ha0 haM using hex
  have hu : ∀ M : s, ∃ t : (𝓞 (cmF K))ˣ, iota K t = a M * star (a M) := by
    intro M
    obtain ⟨i1, i2⟩ := norm_unit h h1 (hs.1 M M.2) (hs.1 _ (base M).2) (haM M)
    exact exists_unitF (mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))) i1 i2
      (by rw [star_mul', star_star, mul_comm])
  choose t ht using hu
  let Q := (𝓞 (cmF K))ˣ ⧸ (powMonoidHom 2 : (𝓞 (cmF K))ˣ →* (𝓞 (cmF K))ˣ).range
  let Ψ : s → ClassGroup (𝓞 K) × Q := fun M => (cl M, ((t M : (𝓞 (cmF K))ˣ) : Q))
  have hinj : Function.Injective Ψ := by
    intro M M' e
    have ecl : cl M = cl M' := congrArg Prod.fst e
    have eB : base M = base M' := hbase_eq M M' ecl
    have eq : ((t M : (𝓞 (cmF K))ˣ) : Q) = ((t M' : (𝓞 (cmF K))ˣ) : Q) := congrArg Prod.snd e
    rw [QuotientGroup.eq] at eq
    obtain ⟨v, hv⟩ := eq
    set ν : K := iota K v with hνdef
    have hν0 : ν ≠ 0 := iota_ne_zero v
    have hνs : star ν = ν := star_iota v
    have hv' : ν ^ 2 = (iota K (t M))⁻¹ * iota K (t M') := by
      rw [hνdef, ← map_pow, ← iota_inv, ← map_mul, ← hv, powMonoidHom_apply]
    have hu0 : a M * star (a M) ≠ 0 := mul_ne_zero (ha0 M) (star_ne_zero.2 (ha0 M))
    have key : a M' * star (a M') = a M * star (a M) * ν ^ 2 := by
      rw [← ht M, ← ht M', hv', mul_inv_cancel_left₀ (iota_ne_zero _)]
    set b : K := a M' * (a M * ν)⁻¹ with hbdef
    have hb0 : b ≠ 0 := mul_ne_zero (ha0 M') (inv_ne_zero (mul_ne_zero (ha0 M) hν0))
    have hb : star b * b = 1 := by
      have e : star b * b = (a M' * star (a M')) * (a M * star (a M) * ν ^ 2)⁻¹ := by
        rw [hbdef, star_mul', star_inv₀, star_mul', hνs]
        have hsa : star (a M) ≠ 0 := star_ne_zero.2 (ha0 M)
        field_simp
      rw [e, key, mul_inv_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hν0))]
    let g : K ≃ₗ[K] K := LinearEquiv.smulOfNeZero K K b hb0
    have hg : g ∈ isom h := by
      refine (mem_isom_iff h1 g).2 ?_
      show star (b • (1 : K)) * (b • (1 : K)) = 1
      rw [smul_eq_mul, mul_one]
      exact hb
    obtain ⟨w, hw⟩ := exists_unitK v
    have hwinv : algebraMap (𝓞 K) K ((w⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ν⁻¹ := by
      rw [hνdef, ← hw]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    have hgM : gmap g (M : Submodule (𝓞 K) K) = M' := by
      rw [gmap_smul, haM M, haM M', ← eB, ← mul_assoc, span_mul_span1]
      have e : b * a M = a M' * ν⁻¹ := by
        rw [hbdef]
        field_simp
        exact mul_div_cancel_right₀ _ (ha0 M)
      rw [e, ← span_mul_span1, mul_assoc, ← hwinv, span_unit_mul]
    have hU := hs.2 M' (hs.1 M' M'.2)
    exact Subtype.ext (hU.unique ⟨M.2, g, hg, hgM⟩ ⟨M'.2, 1, (isom h).one_mem, gmap_one _⟩)
  have hQ : Nat.card Q = 2 ^ fDeg K := card_quot hK
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  have hc := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, hQ, Nat.card_eq_fintype_card (α := ClassGroup (𝓞 K)), Nat.card_eq_fintype_card,
    Fintype.card_coe] at hc
  exact hc

theorem mass_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) :
    mass h (1 : Submodule (𝓞 K) K) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  unfold mass
  split_ifs with hex
  · refine le_trans ?_ (Nat.cast_le.2 (card_classReps_le hK h h1 _ hex.choose_spec))
    calc ∑ M ∈ hex.choose, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ _M ∈ hex.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (autL h M)) with h0 | hpos
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
      _ = (hex.choose.card : ℝ) := by simp
  · positivity

theorem isLattice_one : Submodule.IsLattice K (1 : Submodule (𝓞 K) K) :=
  ⟨⟨{1}, by rw [Finset.coe_singleton, ← Submodule.one_eq_span]⟩,
    span_eq_top_of_ne_zero (Submodule.mem_one.2 ⟨1, map_one _⟩) one_ne_zero⟩

theorem mass_std_one_le (hK : IsCMUnram K) :
    mass (stdForm K 1) (stdLat K 1) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  have hs := stdForm_isSymm K 1
  have ho := stdLat_isOrtho K 1
  have := finiteDimensional_of_ortho ho
  obtain ⟨h', A, hn, hA, hex, e⟩ := exists_model hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isLattice_of_ortho ho)
  rw [← e, ← mass_eq_of_lattices hn hn hA isLattice_one hex]
  exact mass_le hK h' hn

end Formalism.MainNotions.BridgeLemVN

end
end
