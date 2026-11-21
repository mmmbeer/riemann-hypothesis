import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

noncomputable section

namespace GlobalTheory.UnRep.Compare

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem evalAt_apply (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) : evalAt v a = a v := rfl

theorem loc_tmul (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    loc E v (a ⊗ₜ[F] x) = a v ⊗ₜ[F] x := rfl

theorem eq_zero_of_loc {x : RA F E} (h : ∀ v, loc E v x = 0) : x = 0 := by
  let b := Module.Basis.ofVectorSpace F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (i) (y : RA F E),
      (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr y i v =
        (Algebra.TensorProduct.basis (v.adicCompletion F) b).repr (loc E v y) i := by
    intro v i y
    rw [← evalAt_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [loc_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes,
        evalAt_apply v a]
    | add s t hs ht => simp only [map_add, Finsupp.add_apply, hs, ht]
  apply (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr.injective
  ext i : 1
  refine DFunLike.ext _ _ fun v => ?_
  rw [key, h, map_zero, map_zero]
  rfl

theorem eq_of_loc {x y : RA F E} (h : ∀ v, loc E v x = loc E v y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_loc fun v => by rw [map_sub, h, sub_self])

open Classical in

def ind (S : Set (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [if_pos h]; exact one_mem _
    · simp only [if_neg h]; exact zero_mem _⟩

theorem ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) : ind S w = 1 := if_pos h

theorem ind_neg {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∉ S) : ind S w = 0 := if_neg h

theorem loc_ind_pos {S : Set (HeightOneSpectrum (𝓞 F))} {w} (h : w ∈ S) :
    loc E w (ind S ⊗ₜ[F] (1 : E)) = 1 := by rw [loc_tmul, ind_pos h]; rfl

theorem exists_inv (m : ℕ) (hm : m ≠ 0) (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (m : 𝓞 F) ∉ v.asIdeal) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      (m : RA F E) * (a ⊗ₜ[F] (1 : E)) = ind S ⊗ₜ[F] (1 : E) := by
  have hm' : (m : F) ≠ 0 := by exact_mod_cast hm
  refine ⟨ind S * algebraMap F _ (m : F)⁻¹, fun v => ?_, ?_⟩
  · have : (ind S * algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)⁻¹) v
        = ind S v * (((m : F)⁻¹ : F) : v.adicCompletion F) := rfl
    rw [this]
    by_cases hv : v ∈ S
    · rw [ind_pos hv, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
      have h1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 (hS v hv)
      rw [map_natCast] at h1
      rw [h1, inv_one]
    · rw [ind_neg hv, zero_mul]; exact zero_mem _
  · rw [← nsmul_eq_mul, TensorProduct.smul_tmul', nsmul_eq_mul,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, mul_left_comm, ← map_mul,
      mul_inv_cancel₀ hm', map_one, mul_one]

theorem isUnA_iff (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (RA F E)) : IsUnA c G g ↔ IsUnitaryA c G g := Iff.rfl

theorem fm_eq_ratM {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : fm F γ = ratM F γ := rfl

theorem isSplitPlace_of_splitPl (c : E ≃ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (h : SplitPl c v) :
    IsSplitPlace E v := by
  obtain ⟨P, hP, hPv, a, ha, b, hb, hbP⟩ := h
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  refine ⟨P, P.comap σ, fun h => hbP ?_, hP, inferInstance, hPv, ?_⟩
  · rw [h, Ideal.mem_comap] at ha
    rwa [show b = σ a from Subtype.ext hb]
  · rw [← hPv]
    ext x
    have : σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
      Subtype.ext (c.commutes (x : F))
    simp only [Ideal.mem_comap, this]

theorem aut_eq (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (σ : E ≃ₐ[F] E) :
    σ = 1 ∨ σ = c := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr ((hy σ h).trans (hy c hc).symm)

theorem conj_conj (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (x : E) : c (c x) = x := by
  rcases aut_eq c h2 hc (c * c) with h | h
  · exact DFunLike.congr_fun h x
  · exact absurd (mul_eq_left.1 h) hc

theorem moved_of_not_le (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {P Q : Ideal (𝓞 E)} (hQ : Q.IsPrime)
    (h : P.comap (algebraMap (𝓞 F) (𝓞 E)) = Q.comap (algebraMap (𝓞 F) (𝓞 E))) (hPQ : ¬ P ≤ Q) :
    Moved c Q := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hPQ
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  obtain ⟨m, hm⟩ : ((a * σ a : 𝓞 E) : E) ∈ Set.range (algebraMap F E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    rcases aut_eq c h2 hc f with rfl | rfl
    · rfl
    · change f ((a : E) * f a) = (a : E) * f a
      rw [map_mul, conj_conj f h2 hc, mul_comm]
  have hint : IsIntegral ℤ m := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hm]
    exact (a * σ a).2
  obtain ⟨m', hm'⟩ : ∃ m' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) m' = a * σ a := ⟨⟨m, hint⟩, Subtype.ext hm⟩
  have h1 : a * σ a ∈ Q := by
    rw [← hm', ← Ideal.mem_comap, ← h, Ideal.mem_comap, hm']
    exact P.mul_mem_right _ haP
  exact ⟨σ a, (hQ.mem_or_mem h1).resolve_left haQ, a, (conj_conj c h2 hc _).symm, haQ⟩

theorem splitPl_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (v : HeightOneSpectrum (𝓞 F)) : SplitPl c v ↔ IsSplitPlace E v := by
  refine ⟨isSplitPlace_of_splitPl c, ?_⟩
  rintro ⟨w, w', hne, hw, hw', h, h'⟩
  by_cases hle : w ≤ w'
  · exact ⟨w, hw, h, moved_of_not_le c h2 hc hw (h'.trans h.symm) fun h => hne (le_antisymm hle h)⟩
  · exact ⟨w', hw', h', moved_of_not_le c h2 hc hw' (h.trans h'.symm) hle⟩

theorem support_iff (p : HeightOneSpectrum (𝓞 F) → Prop) {n : ℕ} (h : Matrix (Fin n) (Fin n) (RA F E)) :
    (∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
      (∀ v, e v ≠ 0 → p v) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1) ↔
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ T, p v) ∧ ∀ v ∉ T, h.map (loc E v) = 1 := by
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), h.map (loc E v) = 1 ↔ ∀ i j, loc E v ((h - 1) i j) = 0 := by
    intro v
    rw [← Matrix.map_one (loc E v) (map_zero _) (map_one _), ← Matrix.ext_iff]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]
  constructor
  · rintro ⟨e, -, hfin, hp, he⟩
    refine ⟨hfin.toFinset, fun v hv => hp v (hfin.mem_toFinset.1 hv), fun v hv => (hone v).2 fun i j => ?_⟩
    have h0 : e v = 0 := by
      by_contra h0
      exact hv (hfin.mem_toFinset.2 h0)
    rw [← he, Matrix.smul_apply, smul_eq_mul, map_mul, loc_tmul, h0, TensorProduct.zero_tmul, zero_mul]
  · rintro ⟨T, hp, hT⟩
    have hs : ∀ v, ind (T : Set (HeightOneSpectrum (𝓞 F))) v ≠ 0 → v ∈ T := fun v hv => by
      by_contra h0
      exact hv (ind_neg h0)
    refine ⟨ind T, ?_, T.finite_toSet.subset hs, fun v hv => hp v (hs v hv), ?_⟩
    · refine DFunLike.ext _ _ fun v => ?_
      change ind _ v * ind _ v = ind _ v
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [ind_pos hv, one_mul]
      · rw [ind_neg hv, zero_mul]
    · ext i j
      refine eq_of_loc fun v => ?_
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [loc_ind_pos hv, one_mul]
      · rw [(hone v).1 (hT v hv), mul_zero]

theorem suppSplit_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ} (N : ℕ)
    (h : Matrix (Fin n) (Fin n) (RA F E)) : SuppSplit c N h ↔ SupportedAtSplit N h := by
  rw [SuppSplit, support_iff (fun v => SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal), SupportedAtSplit]
  simp only [splitPl_iff c h2 hc]

theorem notMem_of_coprime {t N : ℕ} (ht : t.Coprime N) {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∈ v.asIdeal) : (t : 𝓞 F) ∉ v.asIdeal := fun h => by
  obtain ⟨p, q, hpq⟩ : IsCoprime (t : 𝓞 F) (N : 𝓞 F) := Nat.Coprime.cast ht
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hpq ▸ add_mem (v.asIdeal.mul_mem_left _ h) (v.asIdeal.mul_mem_left _ hv)))

theorem inc_injective : Function.Injective
    (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)) := by
  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := (evalAt v).toRingHom.domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F _).injective

theorem unitary_iff_matrix {R : Type} [CommRing R] {n : ℕ} (s : R →+* R) (G g : Matrix (Fin n) (Fin n) R) :
    (∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) = ∑ a, ∑ b, x a * G a b * s (y b)) ↔
      gᵀ * G * g.map s = G := by
  have key : ∀ (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R),
      ∑ a, ∑ b, x a * M a b * s (y b) = x ⬝ᵥ (M *ᵥ fun b => s (y b)) := fun M x y => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e : ∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) =
      ∑ a, ∑ b, x a * (gᵀ * G * g.map s) a b * s (y b) := fun x y => by
    have e : (fun b => s ((g *ᵥ y) b)) = g.map s *ᵥ fun b => s (y b) := by
      funext b
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    rw [key, key, e, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
      ← Matrix.dotProduct_mulVec, mul_assoc]
  constructor
  · intro h
    ext a b
    have := (e (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)
    simpa [Pi.single_apply, apply_ite s] using this
  · intro h x y
    rw [e, h]

theorem isUnA_iff_matrix (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (g : Matrix (Fin n) (Fin n) (RA F E)) :
    IsUnA c G g ↔ gᵀ * fm F G * g.map (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom = fm F G :=
  unitary_iff_matrix (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom (fm F G) g

theorem fm_eq_map {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : fm F γ =
    γ.map (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom := rfl

theorem isUnE_iff (c : E ≃ₐ[F] E) {n : ℕ} (G γ : Matrix (Fin n) (Fin n) E) :
    IsUnE c G γ ↔ IsUnitaryA c G (ratM F γ) := by
  have h1 : IsUnE c G γ ↔ γᵀ * G * γ.map (c : E →+* E) = G := unitary_iff_matrix (c : E →+* E) G γ
  have h2 : (fm F γ).map (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom = fm F (γ.map (c : E →+* E)) := by
    ext a b
    simp [fm, sg]
  rw [← isUnA_iff, ← fm_eq_ratM, isUnA_iff_matrix, h1, h2, fm_eq_map, fm_eq_map, fm_eq_map,
    ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective inc_injective).eq_iff.symm

theorem isUnit_of_isUnA (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c G g) : IsUnit g := by
  have h := congrArg Matrix.det ((isUnA_iff_matrix c G g).1 hg)
  have hu : IsUnit (fm F G).det := by
    rw [fm_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hG).map _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left (h.symm ▸ hu)

omit [NumberField F] in
theorem isUnit_of_isUnE (c : E ≃ₐ[F] E) {n : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ) : IsUnit γ := by
  have h := congrArg Matrix.det ((unitary_iff_matrix (c : E →+* E) G γ).1 hγ)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left (h.symm ▸ IsUnit.mk0 _ hG)

def HasRep (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (N : ℕ) : Prop :=
  ∀ g : GL (Fin n) (RA F E), IsUnA c G g.1 → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)),
    IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧
    (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧
    ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E))

theorem of_hasRep (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ)
    (H : HasRep c G L (N * D)) : HasSplitRepresentatives c G (L : Set (Fin n → E)) N D := by
  intro g hg
  obtain ⟨g, rfl⟩ := isUnit_of_isUnA c hG hg
  obtain ⟨γ, h, k, hγ, hh, hk, e, hs, hcong, hinv⟩ := H g hg
  obtain ⟨T, hT, hT'⟩ := (suppSplit_iff c h2 hc _ _).1 hs
  refine ⟨γ.1, h.1, k.1, (isUnE_iff c G _).1 hγ, ⟨hh, T, fun v hv => ⟨(hT v hv).1, fun h => (hT v hv).2 ?_⟩, hT'⟩,
    ⟨hk, ?_, fun v _ z hz => ?_⟩, e⟩
  · rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ h
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, e⟩ := hcong z hz
      rw [sub_eq_iff_eq_add.1 e]
      exact add_mem (nsmul_mem hw _) hz
    · intro z hz
      exact ⟨_, hinv z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  · obtain ⟨w, hw, e⟩ := hcong z hz
    refine ⟨N • w, nsmul_mem hw _, fun i => ?_⟩
    rw [smul_smul, mul_comm D, ← e]
    rfl

def RepStatement (n₀ : ℕ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ),
    n₀ ≤ n → ∀ G : Matrix (Fin n) (Fin n) E, IsHermForm c G → Module.finrank F E = 2 →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
    ∀ N : ℕ, 0 < N → HasRep c G L N

theorem RepStatement.mono {a b : ℕ} (hab : a ≤ b) (H : RepStatement a) : RepStatement b :=
  fun F E _ _ _ _ _ c n hn => H F E c n (hab.trans hn)

end GlobalTheory.UnRep.Compare
