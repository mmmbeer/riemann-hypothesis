import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFrameGenStatement

section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨hs0, hs⟩ := hs
  obtain ⟨ht0, ht⟩ := ht
  have h1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht, hs]
    exact Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs, ht]
    exact Submodule.mem_span_singleton_self t
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp h2
  refine ⟨div_ne_zero hs0 ht0, ?_, ?_⟩
  · have e : s / t = (u : Ω) := by
      rw [← hu, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self ht0, mul_one]
    rw [e]
    exact u.2
  · have e : (s / t)⁻¹ = (w : Ω) := by
      rw [inv_div, ← hw, Subring.smul_def, smul_eq_mul, mul_div_assoc, div_self hs0, mul_one]
    rw [e]
    exact w.2

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  obtain ⟨ht0, htl⟩ := h
  have hg : ∃ g, Λ.IsGenAt p g := by
    by_contra hno
    push_neg at hno
    have hmem : t ∈ (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p := by
      rw [htl]
      exact Submodule.mem_span_singleton_self t
    have hbot : (Lat.tens (fun _ : Unit => Λ) fun _ => σ) p = ⊥ := by
      unfold Lat.tens
      rw [Submodule.span_eq_bot]
      rintro x ⟨s, hs, -⟩
      exact absurd (hs ()) (hno (s ()))
    rw [hbot, Submodule.mem_bot] at hmem
    exact ht0 hmem
  obtain ⟨g, hg⟩ := hg
  have hg0 : g ≠ 0 := hg.1
  have hT : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p (g ^ σ) := by
    refine ⟨zpow_ne_zero σ hg0, ?_⟩
    unfold Lat.tens
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨s, hs, rfl⟩
      have hu := uZpow (gen_unit (hs ()) hg) σ
      have e : ∏ i : Unit, s i ^ σ = (⟨(s () / g) ^ σ, hu.2.1⟩ : regAt ξ p) • g ^ σ := by
        rw [Subring.smul_def, smul_eq_mul, Fintype.prod_unique]
        show s () ^ σ = (s () / g) ^ σ * g ^ σ
        rw [div_zpow, div_mul_cancel₀ _ (zpow_ne_zero σ hg0)]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.subset_span
      exact ⟨fun _ => g, fun _ => hg, by simp⟩
  have hu := gen_unit ⟨ht0, htl⟩ hT
  have hu2 := uZpow hu σ
  have heq : (t / g ^ σ) ^ σ = t ^ σ / g := by
    rw [div_zpow, ← zpow_mul, hσ, zpow_one]
  rw [heq] at hu2
  exact gen_of_unit hg hu2

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

end LevelTowerAlt
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Gram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}
  {f : X' ⟶ X} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {i : Ω →+* Ω'}
  {Li Li' : Type} [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li'] [Module Ω' Li']

theorem val_unique (hξ : IsCptGen ξ) (M : LieModel t.G ξ Li) {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) {e : Li}
    {w : epsAt z ⟶ t.G} (hw : M.ValAt z e w) : e ∈ M.lat ⟨centre z, hq⟩ ∧ ∀ w', M.ValAt z e w' → w' = w := by
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X t.G ℂ z
  obtain ⟨ev, hev1, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X t.G Ω ξ Li M ℂ z hq Vz MR hξ t.semi.smooth
  obtain ⟨x, rfl⟩ := MR.onto w (GrNorm.tan_of_valAt hw)
  obtain ⟨he, e2⟩ := (hev1 _ _).1 hw
  refine ⟨he, fun w' hw' => ?_⟩
  obtain ⟨x', rfl⟩ := MR.onto w' (GrNorm.tan_of_valAt hw')
  obtain ⟨_, e3⟩ := (hev1 _ _).1 hw'
  rw [← e2, ← e3]

theorem gram_up (m : SABMap t' t f) (hξ : IsCptGen ξ) (hξ' : IsCptGen ξ') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i)
    (M : LieModel t.G ξ Li) (M' : LieModel t'.G ξ' Li') (j : Li →+ Li')
    (hpt : ∀ e, (M'.pt (j e)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    (z : Sp ℂ ⟶ X') (hq : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) :
    ∃ φ : regAt ξ' ⟨centre z, hq⟩ →+* ℂ, (∀ a : regAt ξ' ⟨centre z, hq⟩, ValAt ξ' z (a : Ω') (φ a)) ∧
      ∀ (r : ℕ) (b : Fin r → Li) (Γ : Matrix (Fin r) (Fin r) ℂ) (b' : Fin r → Li')
        (P : Matrix (Fin r) (Fin r) (regAt ξ' ⟨centre z, hq⟩)), M.GramAt t.PP.L (z ≫ f) b Γ →
        (∀ k, b' k = ∑ l, (P l k : Ω') • j (b l)) → M'.GramAt t'.PP.L z b' ((P.map φ)ᴴ * Γ * P.map φ) := by
  classical
  set p' : Cpt ξ' := ⟨centre z, hq⟩ with hp'
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X' t'.G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X' t'.G Ω' ξ' Li' M' ℂ z hq Vz MR hξ' t'.semi.smooth
  let eA : X'.presheaf.stalk p'.1 ≃+* regAt ξ' p' :=
    RingEquiv.ofBijective (genMap ξ' p').rangeRestrict ⟨fun a b e => hξ'.inj p' (congrArg Subtype.val e),
      (genMap ξ' p').rangeRestrict_surjective⟩
  let φ : regAt ξ' p' →+* ℂ := (Scheme.stalkClosedPointTo z).hom.comp (eA.symm : regAt ξ' p' →+* X'.presheaf.stalk p'.1)
  have hφ : ∀ a : regAt ξ' p', ValAt ξ' z (a : Ω') (φ a) := fun a =>
    ⟨hq, eA.symm a, congrArg Subtype.val (eA.apply_symm_apply a), rfl⟩
  refine ⟨φ, hφ, fun r b Γ b' P ⟨v, hv, hI⟩ hP => ?_⟩
  let val : Li' → Vz := fun e => if he : e ∈ M'.lat p' then ev ⟨e, he⟩ else 0
  have hval : ∀ e (he : e ∈ M'.lat p'), val e = ev ⟨e, he⟩ := fun e he => dif_pos he
  have h0 : val 0 = 0 := by
    rw [hval 0 (zero_mem _)]
    exact map_zero ev
  have hadd : ∀ e ∈ M'.lat p', ∀ e' ∈ M'.lat p', val (e + e') = val e + val e' := fun e he e' he' => by
    rw [hval _ (add_mem he he'), hval e he, hval e' he']
    exact map_add ev ⟨e, he⟩ ⟨e', he'⟩
  have hsmul : ∀ a : regAt ξ' p', ∀ e ∈ M'.lat p', val ((a : Ω') • e) = φ a • val e := fun a e he => by
    have hm : (a : Ω') • e ∈ M'.lat p' := (M'.lat p').smul_mem a he
    rw [hval _ hm, hval e he]
    exact hev2 a (φ a) ⟨e, he⟩ (hφ a)
  have hpick : ∀ e (w : epsAt z ⟶ t'.G), M'.ValAt z e w → e ∈ M'.lat p' ∧ w = MR.pt (val e) := by
    intro e w hw
    obtain ⟨x, hx⟩ := MR.onto w (GrNorm.tan_of_valAt hw)
    rw [← hx] at hw ⊢
    obtain ⟨he, e2⟩ := (hev1 _ _).1 hw
    exact ⟨he, by rw [hval e he, e2]⟩
  have hu := fun k => val_unique hξ M (z := z ≫ f) hp (hv k)
  have hdown := fun k => HodgePull.value_pull (M' := M') (j := j) hd m.cart hpt hq hp (hu k).1
  choose w w' hw hw' hww using hdown
  have hwv : ∀ k, w k = v k := fun k => (hu k).2 _ (hw k)
  have hjL : ∀ k, j (b k) ∈ M'.lat p' := fun k => (hpick _ _ (hw' k)).1
  have hw'e : ∀ k, w' k = MR.pt (val (j (b k))) := fun k => (hpick _ _ (hw' k)).2
  have hb'L : ∀ k, b' k ∈ M'.lat p' := fun k => by
    rw [hP k]
    exact Submodule.sum_mem _ fun l _ => (M'.lat p').smul_mem (P l k) (hjL l)
  have hbv : ∀ k, val (b' k) = ∑ l, (P.map φ) l k • val (j (b l)) := fun k => by
    rw [hP k]
    exact GrNorm.val_sum h0 hadd hsmul hjL (fun l => P l k) Finset.univ
  refine ⟨fun k => MR.pt (val (b' k)), fun k => (hev1 _ _).2 ⟨hb'L k, (hval _ _).symm⟩, fun p q => ?_⟩
  simp only [hbv]
  refine HodgePull.gram_comb MR (fun l => val (j (b l))) Γ p (fun a c => ?_) (HodgePull.hodgeInnerProduct_unique m) _ p q
  rw [← hw'e, ← hw'e]
  refine ((GlobalTheory.T.hodge_inner_product_pullback_unique E H X' X t' t f m z (w' a) (w' c) (w a) (w c) (hww a) (hww c)).1 _).2 ?_
  rw [hwv, hwv]
  exact hI a c

end Gram

section Alg

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem det_tri {b₀ c : Fin r → V} (hb₀ : LinearIndependent Ω b₀) {t : Fin r → Ω}
    (ht : ∀ k : Fin r, c k - t k • b₀ k ∈ flagStep Ω b₀ k) (Q : Matrix (Fin r) (Fin r) Ω) (hQ : ∀ k, c k = ∑ l, Q l k • b₀ l) :
    Q.det = ∏ k, t k := by
  classical
  choose d hd0 hd using fun k => GrNorm.exists_coeff_of_mem_flagStep (ht k)
  have key : ∀ k, (fun l => Q l k) = fun l => d k l + (Pi.single k (t k) : Fin r → Ω) l := fun k =>
    GrNorm.coeff_eq_of_li hb₀ (by
      rw [← hQ k]
      simp only [add_smul, Finset.sum_add_distrib, ← hd k]
      simp [Pi.single_apply, ite_smul])
  have h1 : Q.BlockTriangular id := fun l k hlk => by
    have h := congrFun (key k) l
    have hlk' : k < l := hlk
    rw [hd0 k l hlk'.le, Pi.single_eq_of_ne hlk'.ne', add_zero] at h
    exact h
  rw [Matrix.det_of_upperTriangular h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := congrFun (key k) k
  rwa [hd0 k k le_rfl, Pi.single_eq_same, zero_add] at h

theorem frame_mat (A : Subring Ω) {b b' : Fin r → V} (hb' : LinearIndependent Ω b')
    (hs : Submodule.span A (Set.range b) = Submodule.span A (Set.range b')) :
    ∃ P : Matrix (Fin r) (Fin r) A, (∀ k, b' k = ∑ l, (P l k : Ω) • b l) ∧ IsUnit P.det := by
  classical
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun A).1
    (show b' k ∈ Submodule.span A (Set.range b) from hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  choose c' hc' using fun k => (Submodule.mem_span_range_iff_exists_fun A).1
    (show b k ∈ Submodule.span A (Set.range b') from hs ▸ Submodule.subset_span ⟨k, rfl⟩)
  let P : Matrix (Fin r) (Fin r) A := Matrix.of fun l k => c k l
  let P' : Matrix (Fin r) (Fin r) A := Matrix.of fun l k => c' k l
  have h1 : P' * P = 1 := by
    ext l k
    have key : (fun l => ((P' * P) l k : Ω)) = (Pi.single k 1 : Fin r → Ω) := GrNorm.coeff_eq_of_li hb' (by
      have e1 : ∑ l, (Pi.single k 1 : Fin r → Ω) l • b' l = b' k := by simp [Pi.single_apply, ite_smul]
      rw [e1, ← hc k]
      simp only [← hc', Finset.smul_sum, smul_smul, Matrix.mul_apply, P, P', Matrix.of_apply, AddSubmonoidClass.coe_finset_sum,
        Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      rw [mul_comm]
      rfl)
    rw [congrFun key l, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  exact ⟨P, fun k => (hc k).symm, Matrix.isUnit_det_of_left_inverse h1⟩

theorem prod_sqrt_lead {Γ : Matrix (Fin r) (Fin r) ℂ} (h : Γ.PosDef) :
    ∏ k : Fin r, Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k) = Real.sqrt Γ.det.re := by
  have key : ∀ n, n ≤ r → ∏ k ∈ Finset.range n, Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k) =
      Real.sqrt (leadMinor Γ n) := by
    intro n hn
    induction n with
    | zero => simp [leadMinor_size_zero]
    | succ n ih =>
      have h1 := leadMinor_pos_of_posDef h (Nat.le_of_succ_le hn)
      rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hn), ← Real.sqrt_mul h1.le, mul_div_cancel₀ _ h1.ne']
  rw [Fin.prod_univ_eq_prod_range (fun k => Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k)), key r le_rfl,
    leadMinor_size_self]

theorem sqrt_det_conj (Γ C : Matrix (Fin r) (Fin r) ℂ) :
    Real.sqrt (Cᴴ * Γ * C).det.re = ‖C.det‖ * Real.sqrt Γ.det.re := by
  have e : (Cᴴ * Γ * C).det = ((‖C.det‖ ^ 2 : ℝ) : ℂ) * Γ.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [e, Complex.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Alg

section Sec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω}

theorem mono_sum {F : Type} [Field F] {I : Type} (z : K → F) (hz : ∀ k, z k ≠ 0) (s : Finset I) (a : I → K → ℤ) :
    ∏ k, z k ^ (∑ j ∈ s, a j) k = ∏ j ∈ s, ∏ k, z k ^ a j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hz k) _ _

theorem valAt_prod {I : Type} {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) (s : Finset I) {a : I → Ω} {u : I → ℂ}
    (h : ∀ j, ValAt ξ z (a j) (u j)) : ValAt ξ z (∏ j ∈ s, a j) (∏ j ∈ s, u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hq, 1, by simp, by rw [Finset.prod_empty]; exact map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact CxVal.mul (h j) ih

theorem secNorm_prod {I : Type} [Fintype I] {z : Sp ℂ ⟶ X} (hq : genPt ξ ⤳ centre z) {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt ξ y z w) {L : I → HermLine J} {e t : I → Ω} {ν : I → ℝ}
    (h : ∀ j, SecNorm ξ y (L j) (e j) z w (t j) (ν j)) {A : HermLine J} (ha : A.a = ∑ j, (L j).a)
    (hh : A.h w = ∏ j, (L j).h w) : SecNorm ξ y A (∏ j, e j) z w (∏ j, t j) (∏ j, ν j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (h j).1, hw, fun c hc => ?_⟩
  choose u hu hν using fun j => (h j).2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).1
  refine ⟨∏ j, u j, ?_, ?_⟩
  · rw [ha, mono_sum _ hy, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    exact valAt_prod hq _ hu
  · rw [ha, mono_sum (fun k => ‖w ⟨k, c k⟩‖) (fun k => norm_ne_zero_iff.2 (hc k)), hh, norm_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hν j

end Sec

end LevelTowerAlt.Comparison₂
end
end
