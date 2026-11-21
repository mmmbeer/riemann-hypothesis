import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClasses
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import BuildAid.ForwardExisting

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix

namespace GlobalTheory.PrimeOrderScalar

open scoped TensorProduct

section Generic

variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}

theorem zsmul_eq_zero_iff (hT : T.Prime) (hM : Nat.card M = T) (n : ℤ) :
    (∀ m : M, n • m = 0) ↔ (T : ℤ) ∣ n := by
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hT.ne_zero)
  constructor
  · intro h
    haveI : Nontrivial M :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact hT.one_lt)
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    have hord : addOrderOf a = T := by
      have hdvd := addOrderOf_dvd_natCard a
      rw [hM] at hdvd
      rcases (Nat.dvd_prime hT).mp hdvd with h1 | h1
      · exfalso
        apply ha
        have := addOrderOf_nsmul_eq_zero a
        rwa [h1, one_smul] at this
      · exact h1
    rw [← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr (h a)
  · rintro ⟨c, rfl⟩ m
    have hT0 : (T : ℤ) • m = 0 := by
      rw [natCast_zsmul, ← hM]
      exact card_nsmul_eq_zero'
    rw [mul_comm, mul_smul, hT0, smul_zero]

theorem exists_int_smul (hT : T.Prime) (hM : Nat.card M = T) (s : S) :
    ∃ k : ℤ, ∀ m : M, s • m = k • m := by
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : IsAddCyclic M := isAddCyclic_of_prime_card hM
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := M)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg (s • g))
  refine ⟨k, fun m => ?_⟩
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg m)
  rw [smul_comm s j g, ← hk, smul_comm k j g]

theorem not_isUnit_of_kills (hT : T.Prime) (hM : Nat.card M = T) {u : S}
    (hu : ∀ m : M, u • m = 0) : ¬ IsUnit u := by
  intro h
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hT.ne_zero)
  haveI : Nontrivial M :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact hT.one_lt)
  obtain ⟨a, ha⟩ := exists_ne (0 : M)
  exact ha ((h.smul_eq_zero).mp (hu a))

theorem int_dvd_of_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) (hT : T.Prime)
    (hTI : (T : R) ∈ I) {n : ℤ} (hn : (n : R) ∈ I) : (T : ℤ) ∣ n := by
  by_contra h
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hT).coprime_iff_not_dvd).mpr h
  apply hI
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * (T : ℤ) + b * n : ℤ) : R) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact I.add_mem (I.mul_mem_left _ hTI) (I.mul_mem_left _ hn)

variable {A B : Type} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]

theorem same_int_of_local {O : Type} [CommRing O] [IsLocalRing O] (ψ : O →+* S)
    (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T) (y : O) :
    ∃ k : ℤ, (∀ m : A, ψ y • m = k • m) ∧ ∀ m : B, ψ y • m = k • m := by
  obtain ⟨kA, hkA⟩ := exists_int_smul hT hA (ψ y)
  obtain ⟨kB, hkB⟩ := exists_int_smul hT hB (ψ y)
  have memA : y - (kA : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hA (u := ψ (y - kA)) (fun m => ?_) (hu.map ψ)
    rw [map_sub, map_intCast, sub_smul, hkA, Int.cast_smul_eq_zsmul, sub_self]
  have memB : y - (kB : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hB (u := ψ (y - kB)) (fun m => ?_) (hu.map ψ)
    rw [map_sub, map_intCast, sub_smul, hkB, Int.cast_smul_eq_zsmul, sub_self]
  have hTm : (T : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine not_isUnit_of_kills hT hB (u := ψ (T : O)) (fun m => ?_) (hu.map ψ)
    rw [map_natCast, Nat.cast_smul_eq_nsmul, ← hB]
    exact card_nsmul_eq_zero'
  have hd : ((kB - kA : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have he : ((kB - kA : ℤ) : O) = (y - kA) - (y - kB) := by push_cast; ring
    rw [he]
    exact sub_mem memA memB
  have hdvd := int_dvd_of_mem (IsLocalRing.maximalIdeal.isMaximal O).ne_top hT hTm hd
  refine ⟨kA, hkA, fun m => ?_⟩
  have h0 := (zsmul_eq_zero_iff hT hB (kB - kA)).mpr hdvd m
  rw [sub_smul, sub_eq_zero] at h0
  rw [hkB, h0]

theorem same_int_of_mul (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T)
    (X C D : S) (δ γ : ℤ) (hDA : ∀ m : A, D • m = δ • m) (hDB : ∀ m : B, D • m = δ • m)
    (hCA : ∀ m : A, C • m = γ • m) (hCB : ∀ m : B, C • m = γ • m)
    (hXA : ∀ m : A, D • X • m = C • m) (hXB : ∀ m : B, D • X • m = C • m)
    (hδ : ¬ (T : ℤ) ∣ δ) :
    ∃ k : ℤ, (∀ m : A, X • m = k • m) ∧ ∀ m : B, X • m = k • m := by
  obtain ⟨kA, hkA⟩ := exists_int_smul hT hA X
  obtain ⟨kB, hkB⟩ := exists_int_smul hT hB X
  have h1 : (T : ℤ) ∣ δ * kA - γ := by
    refine (zsmul_eq_zero_iff hT hA _).mp fun m => ?_
    have := hXA m
    rw [hkA, hDA, hCA, smul_smul] at this
    rw [sub_smul, this, sub_self]
  have h2 : (T : ℤ) ∣ δ * kB - γ := by
    refine (zsmul_eq_zero_iff hT hB _).mp fun m => ?_
    have := hXB m
    rw [hkB, hDB, hCB, smul_smul] at this
    rw [sub_smul, this, sub_self]
  have h3 : (T : ℤ) ∣ δ * (kB - kA) := by
    have he : δ * (kB - kA) = (δ * kB - γ) - (δ * kA - γ) := by ring
    rw [he]
    exact dvd_sub h2 h1
  have h4 : (T : ℤ) ∣ kB - kA :=
    ((Nat.prime_iff_prime_int.mp hT).dvd_or_dvd h3).resolve_left hδ
  refine ⟨kA, hkA, fun m => ?_⟩
  have h0 := (zsmul_eq_zero_iff hT hB (kB - kA)).mpr h4 m
  rw [sub_smul, sub_eq_zero] at h0
  rw [hkB, h0]

end Generic

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def inclW (w : HeightOneSpectrum (𝓞 F)) :
    w.adicCompletionIntegers F →+* intV E w :=
  ((Algebra.TensorProduct.includeRight (R := F) (A := E)
      (B := w.adicCompletion F)).toRingHom.comp
    (w.adicCompletionIntegers F).subtype).codRestrict (intV E w)
    (fun y => Subring.subset_closure (Or.inr ⟨⟨y.1, y.2⟩, rfl⟩))

noncomputable def inclO (w : HeightOneSpectrum (𝓞 F)) : 𝓞 E →+* intV E w :=
  ((Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
      (B := w.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E w)
    (fun o => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E o, ⟨o, rfl⟩⟩, rfl⟩))

theorem coe_inclW (w : HeightOneSpectrum (𝓞 F)) (y : w.adicCompletionIntegers F) :
    ((inclW (E := E) w y : intV E w) : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ (y : w.adicCompletion F) :=
  rfl

theorem coe_inclO (w : HeightOneSpectrum (𝓞 F)) (o : 𝓞 E) :
    ((inclO w o : intV E w) : E ⊗[F] w.adicCompletion F) = (o : E) ⊗ₜ (1 : w.adicCompletion F) :=
  rfl

theorem inclW_algebraMap (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    ((inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) : intV E w) :
      E ⊗[F] w.adicCompletion F) = algebraMap F E (d : F) ⊗ₜ (1 : w.adicCompletion F) := by
  rw [coe_inclW, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  rfl

theorem isUnit_algebraMap (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) (hd : d ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact hd

end Local

section Main

theorem sub_kill_eq {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] (P P' X X' : S)
    (hP : ∀ m : M, P • m = 0) (m : M) : ((P + P') * X) • m = (X * P' + X' * P) • m := by
  simp only [add_mul, add_smul, mul_smul, hP, smul_zero, zero_add, add_zero]
  exact smul_comm _ _ _

theorem acts_by_same_integer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  intro F E _ _ _ _ _ σ w hinv hfix T hT hTw p hd A B _ _ _ _ hA hB hpA hpB s
  let Q : intV E w → Prop := fun s =>
    ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m
  have hadd : ∀ a b, Q a → Q b → Q (a + b) := by
    rintro a b ⟨k1, h1A, h1B⟩ ⟨k2, h2A, h2B⟩
    exact ⟨k1 + k2, fun m => by rw [add_smul, add_smul, h1A, h2A],
      fun m => by rw [add_smul, add_smul, h1B, h2B]⟩
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := by
    rintro a b ⟨k1, h1A, h1B⟩ ⟨k2, h2A, h2B⟩
    refine ⟨k1 * k2, fun m => ?_, fun m => ?_⟩
    · rw [mul_smul, h2A, smul_comm, h1A, smul_smul, mul_comm]
    · rw [mul_smul, h2B, smul_comm, h1B, smul_smul, mul_comm]
  have hneg : ∀ a, Q a → Q (-a) := by
    rintro a ⟨k, hkA, hkB⟩
    exact ⟨-k, fun m => by rw [neg_smul, neg_smul, hkA], fun m => by rw [neg_smul, neg_smul, hkB]⟩
  have h0 : Q 0 := ⟨0, fun m => by simp, fun m => by simp⟩
  have h1 : Q 1 := ⟨1, fun m => by simp, fun m => by simp⟩
  have hW : ∀ y, Q (inclW w y) := fun y => same_int_of_local (inclW w) hT hA hB y
  have hσint : ∀ o : 𝓞 E, IsIntegral ℤ (σ (o : E)) := fun o => map_isIntegral_int σ o.2
  let σO : 𝓞 E → 𝓞 E := fun o => ⟨σ (o : E), hσint o⟩
  have hdesc : ∀ e : E, IsIntegral ℤ e → σ e = e → ∃ f : 𝓞 F, algebraMap F E (f : F) = e := by
    intro e he hσe
    obtain ⟨f, hf⟩ := hfix e hσe
    have hfi : IsIntegral ℤ f :=
      (isIntegral_algebraMap_iff (algebraMap F E).injective).mp (hf ▸ he)
    exact ⟨⟨f, hfi⟩, hf⟩
  have hE : ∀ o : 𝓞 E, Q (inclO w o) := by
    intro o
    obtain ⟨d', hd'⟩ := hdesc ((p : E) + σ p) (IsIntegral.add p.2 (hσint p))
      (by rw [map_add, hinv, add_comm])
    obtain ⟨c', hc'⟩ := hdesc ((o : E) * σ p + σ o * p)
      (IsIntegral.add (IsIntegral.mul o.2 (hσint p)) (IsIntegral.mul (hσint o) p.2))
      (by rw [map_add, map_mul, map_mul, hinv, hinv]; ring)
    obtain ⟨δ, hδA, hδB⟩ := hW (algebraMap (𝓞 F) _ d')
    obtain ⟨γ, hγA, hγB⟩ := hW (algebraMap (𝓞 F) _ c')
    have hD : inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') =
        inclO w p + inclO w (σO p) := by
      rw [← map_add]
      apply Subtype.ext
      rw [inclW_algebraMap, coe_inclO, hd']
      rfl
    have hC : inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') =
        inclO w o * inclO w (σO p) + inclO w (σO o) * inclO w p := by
      rw [← map_mul, ← map_mul, ← map_add]
      apply Subtype.ext
      rw [inclW_algebraMap, coe_inclO, hc']
      rfl
    have hPA : ∀ m : A, inclO w p • m = 0 := hpA _ rfl
    have hPB : ∀ m : B, inclO w p • m = 0 := hpB _ rfl
    have hXA : ∀ m : A, inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') • inclO w o • m =
        inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') • m := by
      intro m
      rw [← mul_smul, hD, hC]
      exact sub_kill_eq _ _ _ _ hPA m
    have hXB : ∀ m : B, inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d') • inclO w o • m =
        inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) c') • m := by
      intro m
      rw [← mul_smul, hD, hC]
      exact sub_kill_eq _ _ _ _ hPB m
    have hδ : ¬ (T : ℤ) ∣ δ := fun h =>
      not_isUnit_of_kills hT hA (u := inclW w (algebraMap (𝓞 F) _ d'))
        (fun m => by rw [hδA]; exact (zsmul_eq_zero_iff hT hA δ).mpr h m)
        ((isUnit_algebraMap w d' (hd d' hd')).map _)
    exact same_int_of_mul hT hA hB _ _ _ δ γ hδA hδB hγA hγB hXA hXB hδ
  have key : ∀ z (hz : z ∈ intV E w), Q ⟨z, hz⟩ := by
    intro z hz
    refine Subring.closure_induction (p := fun z hz => Q ⟨z, hz⟩) ?_ h0 h1
      (fun x y hx hy qx qy => hadd _ _ qx qy) (fun x hx qx => hneg _ qx)
      (fun x y hx hy qx qy => hmul _ _ qx qy) hz
    rintro x (⟨⟨_, o, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact hE o
    · exact hW ⟨y.1, y.2⟩
  exact key s.1 s.2

end Main

end GlobalTheory.PrimeOrderScalar
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acts_by_same_integer_statement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  atlas_forward_decl GlobalTheory.PrimeOrderScalar.acts_by_same_integer
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LocalDualBase

theorem localDual_eq_add_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL _
  subst hJ
  have hform1 : ∀ x y : Fin n → E, hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun t => ⟨0, ?_⟩⟩
    have : (t - (0 : intV E w) • (0 : latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin 0) (Fin 0) E) L)))).1 = 0 :=
      Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

  set R := w.adicCompletion F
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl : l.1 + 1 = n := by simp [l]; omega
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  obtain ⟨pb, hpb⟩ := hσO p
  have hpb0 : (algebraMap (𝓞 E) E pb) ≠ 0 := by
    rw [hpb]
    intro h
    exact hp (by simpa using (map_eq_zero σ).1 h)
  set e0 : Fin n → E := Pi.single l (algebraMap (𝓞 E) E pb)⁻¹ with he0def
  have he0 : e0 ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L := by
    intro x hx
    rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [e0, hb]) (by simp)]
    obtain ⟨r, hr, hd⟩ := (hL x).1 hx l
    obtain ⟨s, rfl⟩ := hd hl
    obtain ⟨u, hu⟩ := hσO s
    refine ⟨u, ?_⟩
    rw [hu, hr]
    simp only [e0, Pi.single_eq_same]
    push_cast
    rw [map_mul, ← hpb]
    field_simp
  have hglob : ∀ y ∈ Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L),
      ∃ r : 𝓞 E, y - (algebraMap (𝓞 E) E r) • e0 ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      have hxl : Pi.single l (p : E) ∈ L := by
        refine (hL _).2 fun i => ?_
        by_cases h : i = l
        · subst h
          exact ⟨p, by simp, fun _ => dvd_rfl⟩
        · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
      have h1 := hy _ hxl
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)] at h1
      simp only [Pi.single_eq_same] at h1
      obtain ⟨r, hr⟩ := h1
      refine ⟨r, (hL _).2 fun j => ?_⟩
      by_cases hj : j = l
      · subst hj
        refine ⟨0, ?_, fun _ => dvd_zero _⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, hr, ← hpb]
        push_cast
        field_simp
        ring
      · have hxj : Pi.single j (1 : E) ∈ L := by
          refine (hL _).2 fun i => ?_
          by_cases h : i = j
          · subst h
            exact ⟨1, by simp, fun hi => absurd (Fin.ext (by omega)) hj⟩
          · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
        have h2 := hy _ hxj
        rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at h2
        simp only [Pi.single_eq_same, map_one, one_mul] at h2
        obtain ⟨u, hu⟩ := h2
        refine ⟨u, ?_, fun hj' => absurd (Fin.ext (by omega)) hj⟩
        simp [e0, hj, hu]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨r1, hr1⟩ := h1
      obtain ⟨r2, hr2⟩ := h2
      refine ⟨r1 + r2, ?_⟩
      have : y + z - (algebraMap (𝓞 E) E (r1 + r2)) • e0 =
          (y - (algebraMap (𝓞 E) E r1) • e0) + (z - (algebraMap (𝓞 E) E r2) • e0) := by
        rw [map_add, add_smul]; abel
      rw [this]
      exact L.add_mem hr1 hr2
    | smul c y _ h =>
      obtain ⟨r, hr⟩ := h
      refine ⟨c * r, ?_⟩
      have : c • y - (algebraMap (𝓞 E) E (c * r)) • e0 = c • (y - (algebraMap (𝓞 E) E r) • e0) := by
        ext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul]
        simp only [Algebra.smul_def]
        ring
      rw [this]
      exact L.smul_mem c hr
  have hincl : ∀ r : 𝓞 E, inclE (F := F) R (algebraMap (𝓞 E) E r) ∈ intV E w := by
    intro r
    exact Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)
  refine ⟨⟨fun i => inclE (F := F) R (e0 i),
    Submodule.subset_span ⟨e0, Submodule.subset_span he0, rfl⟩⟩, fun t => ?_⟩
  obtain ⟨t, ht⟩ := t
  suffices H : ∃ s : intV E w, t - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) ∈
      latS (F := F) R (intV E w) L by
    obtain ⟨s, hs⟩ := H
    exact ⟨s, hs⟩
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨r, hr⟩ := hglob y' hy'
    refine ⟨⟨_, hincl r⟩, ?_⟩
    have : (fun i => inclE (F := F) R (y' i)) - inclE (F := F) R (algebraMap (𝓞 E) E r) •
        (fun i => inclE (F := F) R (e0 i)) =
        fun i => inclE (F := F) R ((y' - (algebraMap (𝓞 E) E r) • e0) i) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
    rw [this]
    exact Submodule.subset_span ⟨_, hr, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    refine ⟨s1 + s2, ?_⟩
    have : x + y - ((s1 + s2 : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        (x - (s1 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) +
        (y - (s2 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hs1 hs2
  | smul a x _ h =>
    obtain ⟨s, hs⟩ := h
    refine ⟨a * s, ?_⟩
    have : a • x - ((a * s : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        a • (x - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_mul, mul_smul, smul_sub]
      rfl
    rw [this]
    exact Submodule.smul_mem _ a hs

end GlobalTheory.Mem.LocalDualBase
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  atlas_forward_decl GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem sigR_int (σ : E →ₐ[F] E) (x : E ⊗[F] 𝔸)
    (hx : x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) :
    sigR σ 𝔸 x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  have hle : tensInt (F := F) 𝔸 (intOE E) (intAd F) ≤
      (tensInt (F := F) 𝔸 (intOE E) (intAd F)).comap (sigR σ 𝔸) := by
    conv_lhs => unfold tensInt
    rw [Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨y, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      obtain ⟨a, r, hr⟩ := a
      subst hr
      have hi : IsIntegral ℤ (σ (r : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)
      change (σ (r : E)) ⊗ₜ[F] (1 : 𝔸) ∈ _
      exact Subring.subset_closure (Or.inl ⟨⟨σ (r : E), ⟨⟨σ (r : E), hi⟩, rfl⟩⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap]
      change (σ (1 : E)) ⊗ₜ[F] (y : 𝔸) ∈ _
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  exact hle hx


end GlobalTheory.Mem.LevDual

namespace GlobalTheory.Mem.LevDual

theorem hform_one {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (x y : Fin n → E) :
    hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.one_apply]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma prV_mem_latS (w : HeightOneSpectrum (𝓞 F)) {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E))
    {v : Fin m → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hv : v ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) :
    (fun i => _root_.Formalism.UG.prV w (v i)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L := by
  unfold _root_.Formalism.UG.latS at hv ⊢
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨x, hx, ?_⟩
    funext i
    exact (_root_.Formalism.UG.P.afsplit_prV_inclE w (x i)).symm
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext i
    simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    funext i
    simp
  | smul c a _ ha =>
    have hc : _root_.Formalism.UG.prV w (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w :=
      by unfold _root_.Formalism.BasicNotions.intV; exact _root_.Formalism.UG.P.afsplit_prV_int w _ c.2
    convert Submodule.smul_mem _ (⟨_, hc⟩ : _root_.Formalism.BasicNotions.intV (F := F) E w) ha using 1
    funext i
    simp [Subring.smul_def]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma inclE_mem_intV_of_mem_intOE (w : HeightOneSpectrum (𝓞 F)) {a : E} (ha : a ∈ _root_.Formalism.UG.intOE E) :
    _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) a ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
  unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt
  exact Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma hform_one_apply {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (x y : Fin m → A) :
    _root_.Formalism.UG.hform σ 1 x y = ∑ i, σ (x i) * y i := by
  unfold _root_.Formalism.UG.hform
  simp [Matrix.one_apply]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma algHom_coe_mem_intOE (σ : E →ₐ[F] E) (r : 𝓞 E) : σ (r : E) ∈ _root_.Formalism.UG.intOE E := by
  unfold _root_.Formalism.UG.intOE
  exact ⟨⟨σ r, (r.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)⟩, rfl⟩

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma sigR_mem_intV' (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F))
    {c : E ⊗[F] w.adicCompletion F} (hc : c ∈ _root_.Formalism.BasicNotions.intV (F := F) E w) :
    _root_.Formalism.UG.sigR σ (w.adicCompletion F) c ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
  unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt at *
  have hle : Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F]
        (1 : w.adicCompletion F)) ∪
      Set.range fun y : (w.adicCompletionIntegers F).toSubring => (1 : E) ⊗ₜ[F] (y : w.adicCompletion F)) ≤
      (Subring.closure ((Set.range fun x : _root_.Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : w.adicCompletion F)) ∪
      Set.range fun y : (w.adicCompletionIntegers F).toSubring =>
        (1 : E) ⊗ₜ[F] (y : w.adicCompletion F))).comap (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) := by
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨r, hr⟩ : (x : E) ∈ (algebraMap (𝓞 E) E).range := x.2
      have hσ : σ (x : E) ∈ _root_.Formalism.UG.intOE E := by rw [← hr]; exact algHom_coe_mem_intOE σ r
      apply Subring.subset_closure
      left
      refine ⟨⟨σ x, hσ⟩, ?_⟩
      unfold _root_.Formalism.UG.sigR
      simp
    · apply Subring.subset_closure
      right
      refine ⟨y, ?_⟩
      unfold _root_.Formalism.UG.sigR
      simp
  exact hle hc

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
private lemma pairing_mem_intV_of_mem_dualSet (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {m : ℕ}
    (L : Submodule (𝓞 E) (Fin m → E)) {z : Fin m → E} (hz : z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L)
    {x : Fin m → E ⊗[F] w.adicCompletion F}
    (hx : x ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L) :
    ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) (x j) * _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z j) ∈
      _root_.Formalism.BasicNotions.intV (F := F) E w := by
  have hz' : ∀ y ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 y z ∈ (algebraMap (𝓞 E) E).range := hz
  unfold _root_.Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    have h := inclE_mem_intV_of_mem_intOE (F := F) w (hz' y hy)
    rw [hform_one_apply, map_sum] at h
    convert h using 2 with j
    rw [map_mul]
    congr 1
    all_goals (unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE; simp)
  | zero => simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    simp [map_add, add_mul, Finset.sum_add_distrib]
  | smul c a _ ha =>
    convert mul_mem (sigR_mem_intV' σ w c.2) ha using 1
    simp [Subring.smul_def, map_mul, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.Mem.LevDual.unitary_carry_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ _root_.Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L) → ∀ z ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L', ((_root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a)) ∈ _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J L)) := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL L' Y hY hLat z hz
  subst hJ
  cases n with
  | zero =>
    convert Submodule.zero_mem _ using 1
  | succ m =>
    set Yw := _root_.Formalism.UG.bc (_root_.Formalism.UG.prV (E := E) w) Y with hYw_def
    have hYwU : Yw ∈ _root_.Formalism.UG.UPts σ 1 (w.adicCompletion F) := _root_.Formalism.UG.P.afsplit_bc_mem σ 1 w Y hY
    have hunit : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *
        (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) = 1 := by
      have h := hYwU
      unfold _root_.Formalism.UG.UPts _root_.Formalism.UG.UJ at h
      change _ * _ * _ = _ at h
      rwa [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h
    have hinv : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) =
        _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) := by
      calc ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) _)
          = (_root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (w.adicCompletion F)) (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *
              (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _)) * ((Yw⁻¹ : GL (Fin (m + 1)) _) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) _) := by rw [hunit, one_mul]
        _ = _ := by rw [mul_assoc, Units.mul_inv, mul_one]
    set v : Fin (m + 1) → E ⊗[F] w.adicCompletion F :=
      fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (z a) with hv
    have hu_apply : ∀ i, (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i =
        ∑ j, _root_.Formalism.UG.sigR σ (w.adicCompletion F) ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j i) * v j := by
      intro i
      rw [hinv]
      unfold _root_.Formalism.UG.cT
      simp [Matrix.mulVec, dotProduct]
    have hcol : ∀ x ∈ L, (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
        (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (x a)) ∈
        _root_.Formalism.UG.latS (F := F) (w.adicCompletion F) (_root_.Formalism.BasicNotions.intV E w) L' := by
      intro x hx
      have hA : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
          (fun a => _root_.Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x a)) ∈
          _root_.Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
            (_root_.Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (_root_.Formalism.UG.intOE E) (_root_.Formalism.UG.intAd F)) L' := by
        rw [hLat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      have h := prV_mem_latS w L' hA
      convert h using 1
      funext i
      rw [hYw_def, _root_.Formalism.UG.P.afsplit_coe_bc_prV, RingHom.map_mulVec]
      congr 1
    have hlast : ∀ j : Fin (m + 1), j.1 + 1 = m + 1 ↔ j = Fin.last m := fun j => by
      rw [Fin.ext_iff, Fin.val_last]
      omega
    have hsingle : ∀ i, i ≠ Fin.last m → (Pi.single i 1 : Fin (m + 1) → E) ∈ L := by
      intro i hi
      rw [hL]
      intro j
      by_cases hj : j = i
      · subst hj
        exact ⟨1, by simp, fun h => absurd ((hlast j).1 h) hi⟩
      · exact ⟨0, by simp [hj], fun _ => dvd_zero p⟩
    have hpL : (Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) ∈ L := by
      rw [hL]
      intro j
      by_cases hj : j = Fin.last m
      · subst hj
        exact ⟨p, by simp, fun _ => dvd_refl _⟩
      · exact ⟨0, by simp [hj], fun _ => dvd_zero p⟩
    have hcoef_low : ∀ i, i ≠ Fin.last m → (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) i ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
      intro i hi
      have h := pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ (hsingle i hi))
      rw [hu_apply]
      convert h using 2 with j
      congr 2
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hcoef_last : _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) *
        (((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v) (Fin.last m) ∈ _root_.Formalism.BasicNotions.intV (F := F) E w := by
      have h := pairing_mem_intV_of_mem_dualSet σ w L' hz (hcol _ hpL)
      rw [hu_apply, Finset.mul_sum]
      convert h using 2 with j
      have hc : ((Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ
          (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F)
            ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a))) j =
          (Yw : Matrix (Fin (m + 1)) (Fin (m + 1)) _) j (Fin.last m) *
            _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E) := by
        have hv' : (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F)
            ((Pi.single (Fin.last m) (p : E) : Fin (m + 1) → E) a)) =
            Pi.single (Fin.last m) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) := by
          funext a
          by_cases ha : a = Fin.last m
          · subst ha
            simp
          · simp [ha]
        rw [hv']
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hc, map_mul]
      have hs : _root_.Formalism.UG.sigR σ (w.adicCompletion F) (_root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (p : E)) =
          _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (σ (p : E)) := by
        unfold _root_.Formalism.UG.sigR _root_.Formalism.UG.inclE
        simp
      rw [hs]
      ring
    have hd_single : ∀ i, (Pi.single i 1 : Fin (m + 1) → E) ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      intro i
      show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x _ ∈ (algebraMap (𝓞 E) E).range
      intro x hx
      obtain ⟨r, hr, _⟩ := (hL x).1 hx i
      have hc : σ (r : E) ∈ (algebraMap (𝓞 E) E).range := algHom_coe_mem_intOE σ r
      rw [hform_one_apply]
      simpa [Pi.single_apply, hr] using hc
    have hq : σ (p : E) ≠ 0 := by
      intro h
      apply hp
      have h' : (p : E) = 0 := σ.injective (h.trans (map_zero σ).symm)
      exact_mod_cast h'
    set e0 : Fin (m + 1) → E := Pi.single (Fin.last m) (σ (p : E))⁻¹ with he0_def
    have he0 : e0 ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      show ∀ x ∈ L, _root_.Formalism.UG.hform (σ : E →+* E) 1 x e0 ∈ (algebraMap (𝓞 E) E).range
      intro x hx
      obtain ⟨r, hxr, hdiv⟩ := (hL x).1 hx (Fin.last m)
      obtain ⟨c, rfl⟩ := hdiv (by simp)
      rw [hform_one_apply]
      have hc : σ (c : E) ∈ (algebraMap (𝓞 E) E).range := algHom_coe_mem_intOE σ c
      have key : σ (x (Fin.last m)) * (σ (p : E))⁻¹ = σ (c : E) := by
        rw [hxr]
        push_cast
        rw [map_mul]
        field_simp
      simpa [he0_def, Pi.single_apply, key] using hc
    let d : Fin (m + 1) → Fin (m + 1) → E := fun i => if i = Fin.last m then e0 else Pi.single i 1
    have hd : ∀ i, d i ∈ _root_.Formalism.BasicNotions.dualSet (σ : E →+* E) 1 L := by
      intro i
      by_cases h : i = Fin.last m
      · simp only [d, h, if_true]
        exact he0
      · simp only [d, h, if_false]
        exact hd_single i
    let c : Fin (m + 1) → _root_.Formalism.BasicNotions.intV (F := F) E w := fun i =>
      if h : i = Fin.last m then ⟨_, hcoef_last⟩ else ⟨_, hcoef_low i h⟩
    have hsum : ((Yw⁻¹ : GL (Fin (m + 1)) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) _) *ᵥ v =
        ∑ i, c i • (fun a => _root_.Formalism.UG.inclE (F := F) (w.adicCompletion F) (d i a)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · by_cases hk : k = Fin.last m
        · subst hk
          simp only [c, d, dif_pos, if_pos, Pi.smul_apply, Subring.smul_def, smul_eq_mul, he0_def,
            Pi.single_eq_same]
          rw [mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
        · simp [c, d, hk, Subring.smul_def]
      · intro b _ hb
        by_cases hbl : b = Fin.last m
        · subst hbl
          simp [c, d, he0_def, Pi.single_apply, Ne.symm hb, Subring.smul_def]
        · simp [c, d, hbl, Pi.single_apply, Ne.symm hb, Subring.smul_def]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨d i, Submodule.subset_span (hd i), rfl⟩)

end GlobalTheory.Mem.LevDual
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_maps_latS_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L) → ∀ z ∈ dualSet (σ : E →+* E) J L', ((bc (prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z a)) ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)) := by
  atlas_forward_decl GlobalTheory.Mem.LevDual.unitary_carry_dual
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

open scoped TensorProduct in

theorem frLat_of_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {a b : ℕ} (hab : a = b) (Lb : Submodule (𝓞 E) (Fin a → E))
    (phi : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) (fr : GL (Fin a) (v.adicCompletion F))
    (h : ∀ x : Fin b → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (reL hab Lb), ∀ c, phi (y c) = x c) ↔
        ∀ c, (((reGL hab (v.adicCompletion F) fr)⁻¹ : GL (Fin b) (v.adicCompletion F)) :
          Matrix (Fin b) (Fin b) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F)
    (t : Fin a → v.adicCompletion F) :
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb, ∀ c, phi (y c) = t c) ↔
      ∀ c, ((fr⁻¹ : GL (Fin a) (v.adicCompletion F)) : Matrix (Fin a) (Fin a) (v.adicCompletion F)).mulVec t c ∈
        v.adicCompletionIntegers F := by
  subst hab
  have h1 : reL (rfl : a = a) Lb = Lb := by
    ext x; simp [reL, reV]
  have h2 : reGL (rfl : a = a) (v.adicCompletion F) fr = fr := by
    ext i j; simp [reGL]
  rw [h1, h2] at h
  exact h t

theorem surj_of_card_prime {M A : Type} [AddCommGroup M] [AddCommGroup A] {T : ℕ} (hT : T.Prime) (hA : Nat.card A = T)
    (f : M →+ A) {m : M} (hm : f m ≠ 0) : Function.Surjective f := by
  haveI : Fact (Nat.card A).Prime := ⟨hA ▸ hT⟩
  rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card f.range with h | h
  · exact absurd ((AddSubgroup.eq_bot_iff_forall _).1 h _ ⟨m, rfl⟩) hm
  · exact AddMonoidHom.range_eq_top.1 h

theorem zsmul_eq_zero_iff_of_card_prime {A : Type} [AddCommGroup A] {T : ℕ} (hT : T.Prime) (hA : Nat.card A = T)
    {a : A} (ha : a ≠ 0) (k : ℤ) : k • a = 0 ↔ (T : ℤ) ∣ k := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (hA ▸ hT.ne_zero)
  have h1 : addOrderOf a = T := by
    rcases (Nat.dvd_prime hT).1 (hA ▸ addOrderOf_dvd_natCard a) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) ha
    · exact h
  rw [← h1, addOrderOf_dvd_iff_zsmul_eq_zero]

theorem exists_equiv_of_cyclic {S M A B : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup A] [Module S A]
    [AddCommGroup B] [Module S B] {T : ℕ} (hT : T.Prime) (hA : Nat.card A = T) (hB : Nat.card B = T)
    (f : M →ₗ[S] A) (g : M →ₗ[S] B) (hf : f ≠ 0) (hg : g ≠ 0) (P : M → Prop) (hfP : ∀ m, P m → f m = 0)
    (hgP : ∀ m, P m → g m = 0) (e : M) (he : ∀ t, ∃ s : S, P (t - s • e))
    (hs : ∀ s : S, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m) :
    ∃ φ : A ≃+ B, ∀ t, φ (f t) = g t := by
  have key : ∀ t, ∃ k : ℤ, f t = k • f e ∧ g t = k • g e := by
    intro t
    obtain ⟨s, h⟩ := he t
    obtain ⟨k, h1, h2⟩ := hs s
    have a1 := hfP _ h
    have a2 := hgP _ h
    rw [map_sub, map_smul, sub_eq_zero] at a1 a2
    exact ⟨k, a1.trans (h1 _), a2.trans (h2 _)⟩
  have fe : f e ≠ 0 := fun h => hf (LinearMap.ext fun t => by obtain ⟨k, h1, -⟩ := key t; simp [h1, h])
  have ge : g e ≠ 0 := fun h => hg (LinearMap.ext fun t => by obtain ⟨k, -, h1⟩ := key t; simp [h1, h])
  have hk : f.toAddMonoidHom.ker = g.toAddMonoidHom.ker := by
    ext t
    obtain ⟨k, h1, h2⟩ := key t
    simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]
    rw [h1, h2, zsmul_eq_zero_iff_of_card_prime hT hA fe, zsmul_eq_zero_iff_of_card_prime hT hB ge]
  have sf := surj_of_card_prime hT hA f.toAddMonoidHom (m := e) fe
  have sg := surj_of_card_prime hT hB g.toAddMonoidHom (m := e) ge
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective _ sf).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hk).trans (QuotientAddGroup.quotientKerEquivOfSurjective _ sg)), fun t => ?_⟩
  have : (QuotientAddGroup.quotientKerEquivOfSurjective _ sf).symm (f t) = QuotientAddGroup.mk t := by
    rw [AddEquiv.symm_apply_eq]; rfl
  rw [AddEquiv.trans_apply, this]
  rfl

open scoped TensorProduct in

theorem functional_of_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →+* E) (w : HeightOneSpectrum (𝓞 F)) {a b : ℕ} (h : a = b)
    (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E) (hJ : J' = J.reindex (finCongr h) (finCongr h))
    (L : Submodule (𝓞 E) (Fin a → E)) (L' : Submodule (𝓞 E) (Fin b → E)) (hL : L' = reL h L)
    {B : Type} [AddCommGroup B] [Module (intV E w) B]
    (g' : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' L')) →ₗ[intV E w] B)
    (hne : g' ≠ 0) (hz : ∀ x, x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L' → g' x = 0) :
    ∃ g : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J L)) →ₗ[intV E w] B,
      g ≠ 0 ∧ (∀ x, x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L → g x = 0) ∧
      ∀ (y : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (y' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
        (z : Fin a → E) (z' : Fin b → E) t, y' = reGL h _ y → z' = reV h E z →
        (bc (prV (E := E) w) y).1 *ᵥ t.1 = (fun i => inclE (F := F) (w.adicCompletion F) (z i)) →
        ∃ hz : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ
            (fun i => inclE (F := F) (w.adicCompletion F) (z' i)) ∈
          latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' L')),
          g' ⟨_, hz⟩ = g t := by
  subst h
  obtain rfl : J' = J := by rw [hJ]; ext i j; simp
  obtain rfl : L' = L := by rw [hL]; ext x; simp [reL, reV]
  refine ⟨g', hne, hz, fun y y' z z' t hy hz' ht => ?_⟩
  subst hy hz'
  have h2 : reGL (rfl : a = a) _ y = y := by
    ext i j; simp [reGL]
  have ht' : ((bc (prV (E := E) w) (reGL (rfl : a = a) _ y))⁻¹).1 *ᵥ
      (fun i => inclE (F := F) (w.adicCompletion F) (reV (rfl : a = a) E z i)) = t.1 := by
    have e : (fun i => inclE (F := F) (w.adicCompletion F) (reV (rfl : a = a) E z i)) =
        fun i => inclE (F := F) (w.adicCompletion F) (z i) := rfl
    rw [h2, e, ← ht, Matrix.mulVec_mulVec]
    simp
  exact ⟨ht' ▸ t.2, congrArg g' (Subtype.ext ht')⟩

open scoped TensorProduct in
set_option maxHeartbeats 1000000 in

theorem colLevel_functional {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (hgram : sp.gram0 = 1) (p : 𝓞 E) (hp0 : p ≠ 0)
    (hL : ∀ x, x ∈ L.Lb ↔ ∀ j : Fin R.k, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = R.k → p ∣ r))
    (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (hπ : ∀ a : intV E w, (a : E ⊗[F] w.adicCompletion F) = inclE (F := F) (w.adicCompletion F) (p : E) →
      ∀ m : L.fM w h, a • m = 0)
    (hd : ∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + sp.cm.sig (p : E) → d ∉ w.asIdeal)
    {B K : Type} [AddCommGroup B] [Module (intV E w) B] [AddCommGroup K] (hB : Nat.card B = A.T)
    (g : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)) →ₗ[intV E w] B) (gne : g ≠ 0)
    (gL : ∀ x, x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L.Lb → g x = 0) (ψ : B ≃+ K)
    (fz : ∀ c : C.cls 0, Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → K)
    (hne : ∀ c, ∃ z, fz c z ≠ 0) (hp : ∀ c z, fz c (p • z) = 0)
    (tie : ∀ c (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c)) (t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
      (bc (prV (E := E) w) (L.y c).1).1 *ᵥ t.1 = (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
      fz c z = ψ (g t)) :
    ∃ e : L.fM w h ≃+ K, ∀ c (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c)) (t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
      (bc (prV (E := E) w) (L.y c).1).1 *ᵥ t.1 = (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
      fz c z = e (L.fT w h t) := by
  have hTp := A.T_prime
  have hinv : ∀ x, sp.cm.sig (sp.cm.sig x) = x := fun x => star_star x
  have hfix : ∀ x, sp.cm.sig x = x → x ∈ (algebraMap F E).range := fun x hx => (sp.cm.fixed x).1 hx
  have hgπ : ∀ a : intV E w, (a : E ⊗[F] w.adicCompletion F) = inclE (F := F) (w.adicCompletion F) (p : E) →
      ∀ m : B, a • m = 0 := by
    intro a ha m
    have hc := L.y_bij.2 (Quotient.mk'' 1)
    obtain ⟨c, -⟩ := hc
    obtain ⟨z, hq⟩ := hne c
    have hzd : sp.crd0 z.1 ∈ dualSet (sp.cm.sig : E →+* E) sp.gram0 (sp.crdLat0 (clsLat 0 c)) := by
      rintro x ⟨x0, hx0, rfl⟩
      have h1 : (sp.X 0).hT x0 z.1 ∈ (1 : Submodule (𝓞 E) E) := by
        have := z.2
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
        exact this x0 hx0
      rw [sp.hermitianForm_base_coordinates] at h1
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
      exact ⟨r, hr⟩
    have hm := GlobalTheory.T.unitary_maps_latS_dual F E sp.cm.sig w R.k sp.gram0 L.Lb p hgram hp0 hL _ (L.y c).1 (L.y c).2 (L.y_lat c) _ hzd
    have ht : (bc (prV (E := E) w) (L.y c).1).1 *ᵥ (((bc (prV (E := E) w) (L.y c).1)⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a))) =
        (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have t1 := tie c z ⟨_, hm⟩ ht
    have t2 := tie c (p • z) (a • ⟨_, hm⟩) (by
      have e1 : ∀ x : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)), (a • x).1 = (a : E ⊗[F] w.adicCompletion F) • x.1 := fun x => rfl
      rw [e1, Matrix.mulVec_smul, ht, ha]
      funext i
      have e2 : ((p • z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c)) : (sp.X 0).V) = (p : E) • (z : (sp.X 0).V) :=
        (algebraMap_smul E p (z : (sp.X 0).V)).symm
      rw [e2, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul])
    rw [hp, map_smul] at t2
    have t3 := (AddEquiv.map_eq_zero_iff _).1 t2.symm
    have t4 : g ⟨_, hm⟩ ≠ 0 := fun h0 => hq (by rw [t1, h0, map_zero])
    obtain ⟨k, rfl⟩ := surj_of_card_prime hTp hB (zmultiplesHom _ (g ⟨_, hm⟩)) (m := 1) (by simpa using t4) m
    rw [zmultiplesHom_apply, smul_comm, t3, smul_zero]
  have hex := GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd F E sp.cm.sig w R.k sp.gram0 L.Lb p hgram hp0 hL hinv
  obtain ⟨e, he⟩ := hex
  have hex := exists_equiv_of_cyclic hTp (L.fM_card w h) hB (L.fT w h) g (L.fT_ne w h) gne
    (fun x => x.1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L.Lb) (L.fT_L w h) gL e he
    (GlobalTheory.T.acts_by_same_integer_statement F E sp.cm.sig w hinv hfix _ hTp h p hd _ _ (L.fM_card w h) hB hπ hgπ)
  obtain ⟨φ, hφ⟩ := hex
  refine ⟨φ.trans ψ, fun c z t ht => ?_⟩
  rw [tie c z t ht, AddEquiv.trans_apply, hφ]

open scoped TensorProduct in
set_option maxHeartbeats 1000000 in

theorem stepZeroLevel_functional_residueField {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (hgram : D.sp.gram0 = 1)
    (hL : ∀ x, x ∈ (H.lev0 u).Lb ↔ ∀ j : Fin D.R.k, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = D.R.k → (A u).piU ∣ r))
    (v : (D.mem u).A.vT) (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w = ((F u).atT.eV v).1)
    (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal)
    (hπ : ∀ a : intV D.host.E w, (a : D.host.E ⊗[D.host.F] w.adicCompletion D.host.F) =
      inclE (F := D.host.F) (w.adicCompletion D.host.F) ((A u).piU : D.host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) :
    ∃ e : (H.lev0 u).fM w h ≃+ (D.mem u).A.Fv v, ∀ (c : (D.mem u).C.cls 0) (z : Formalism.L2.Herm.Ld D u 0 c)
      (t : latS (F := D.host.F) (w.adicCompletion D.host.F) (intV D.host.E w) (Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb))),
      (bc (prV (E := D.host.E) w) ((H.lev0 u).y c).1).1 *ᵥ t.1 =
        (fun a => inclE (F := D.host.F) (w.adicCompletion D.host.F) (D.sp.crd0 z.1 a)) →
      (D.fm u).fv 0 v c ((A u).pr 0 v c z) = e ((H.lev0 u).fT w h t) := by
  subst hw
  have hc := hH.car0 u
  have hTp := (D.mem u).A.T_prime
  have hex := functional_of_reindex (F := D.host.F) (D.sp.cm.sig : D.host.E →+* D.host.E) ((F u).atT.eV v).1
    (rank_eq_first_level D.R) D.sp.gram0 (gramN D 0 (Nat.zero_le _)) (by ext i j; rfl) (H.lev0 u).Lb ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb hc.Lb_eq
    (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT _ ((F u).atT.eV v).2)
    (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_ne _ _) (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_L _ _)
  obtain ⟨g, gne, gL, hg⟩ := hex
  have hB := ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_card _ ((F u).atT.eV v).2
  have tie : ∀ (c : (D.mem u).C.cls 0) (z : Formalism.L2.Herm.Ld D u 0 c)
      (t : latS (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F) (intV D.host.E ((F u).atT.eV v).1) (Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb))),
      (bc (prV (E := D.host.E) ((F u).atT.eV v).1) ((H.lev0 u).y c).1).1 *ᵥ t.1 =
        (fun a => inclE (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F) (D.sp.crd0 z.1 a)) →
      (D.fm u).fv 0 v c ((A u).pr 0 v c z) = (F u).fMe 0 (Nat.zero_le _) (Or.inl rfl) v (g t) := by
    intro c z t ht
    have hz' := crdN_mem_Ld u 0 (Nat.zero_le _) c z
    have e3 : crdN D 0 (Nat.zero_le _) z.1 = reV (rank_eq_first_level D.R) D.host.E (D.sp.crd0 z.1) := by
      funext a; rfl
    have hex := hg ((H.lev0 u).y c).1 (((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1 _ _ t (hc.y_eq c) e3 ht
    obtain ⟨hz, e0⟩ := hex
    have e1 := (F u).fv 0 (Nat.zero_le _) (Or.inl rfl) v c ⟨_, hz'⟩ hz
    have e2 := hT.pr u 0 (Nat.zero_le _) v c z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv 0 v c p) e2.symm).trans (e1.trans (congrArg _ e0))
  have hp0 : (A u).piU ≠ 0 := by
    intro h0
    have := (A u).piU_norm
    rw [h0] at this
    exact hTp.ne_zero (by simpa using this.symm)
  have hd : ∀ d : 𝓞 D.host.F, algebraMap D.host.F D.host.E (d : D.host.F) =
      ((A u).piU : D.host.E) + D.sp.cm.sig ((A u).piU : D.host.E) → d ∉ ((F u).atT.eV v).1.asIdeal := by
    intro d hd hmem
    have h1 := ((F u).atT.res_v v d).1 hmem
    refine (F u).atT.res_conj v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d - (F u).atT.piU) ?_ ?_
    · rw [hT.piU u, ← Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D]
      push_cast
      rw [sub_eq_iff_eq_add']
      exact hd
    · rw [map_sub, h1, (F u).atT.res_pi, sub_zero]
  have hne : ∀ c, ∃ z : Formalism.L2.Herm.Ld D u 0 c, (D.fm u).fv 0 v c ((A u).pr 0 v c z) ≠ 0 := by
    intro c
    by_contra hn
    push Not at hn
    refine (D.fm u).fv_ne 0 v c (LinearMap.ext fun q => ?_)
    obtain ⟨z, rfl⟩ := (A u).pr_surj 0 (Nat.zero_le _) v c q
    exact hn z
  have hp : ∀ c (z : Formalism.L2.Herm.Ld D u 0 c), (D.fm u).fv 0 v c ((A u).pr 0 v c ((A u).piU • z)) = 0 := by
    intro c z
    have hres : (A u).res v (A u).piU = 0 := by
      rw [← RingHom.mem_ker, (A u).res_ker]; exact (A u).Pv_pi v
    rw [(A u).pr_smul, hres, zero_smul, map_zero]
  exact colLevel_functional (H.lev0 u) hgram (A u).piU hp0 hL _ h hπ hd hB g gne gL
    ((F u).fMe 0 (Nat.zero_le _) (Or.inl rfl) v) (fun c z => (D.fm u).fv 0 v c ((A u).pr 0 v c z)) hne hp tie

set_option maxHeartbeats 4000000 in

theorem intV_coe_eq_inclE_of_T_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → ∀ u, ∃ x : Formalism.L2.Herm.ColLevelX (H.lev0 u) (fun x => x ∈ (I.rec7 l Z).host.K) (A u).piU (H.vT u) (fun v c z => ((I.rec7 l Z).fm u).fv 0 v c ((A u).pr 0 v c z)), x.piG = X.piG := by
  intro B X I hOk hP l Z H F A hS hH hT hπ u
  have hpi := (hS u).1.gl.piG
  obtain ⟨-, -, -, hN⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hP l Z
  obtain ⟨hgram, -, -⟩ := hN 0 (Nat.zero_le _)
  have hgram0 : (I.rec7 l Z).sp.gram0 = 1 := by
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)
    have e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b := by simp [Fin.ext_iff]
    simp only [Matrix.one_apply, e] at this
    rw [Matrix.one_apply]
    exact this
  obtain ⟨k, hk⟩ := (hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb := (hH.car0 u).Lb_eq
  have hpU : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  have hL : ∀ x, x ∈ (H.lev0 u).Lb ↔ ∀ j : Fin (I.rec7 l Z).R.k, ∃ r : 𝓞 (I.rec7 l Z).host.E,
      x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = (I.rec7 l Z).R.k → (A u).piU ∣ r) := by
    intro x
    have e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb := by
      rw [hLb]
      constructor
      · exact fun h => ⟨x, h, rfl⟩
      · rintro ⟨y, hy, e⟩
        have : y = x := (reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e
        exact this ▸ hy
    rw [hpU]
    refine e1.trans ((hk.lb () _).trans ?_)
    constructor
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩
  choose e he using fun w h => stepZeroLevel_functional_residueField H F A hH hT u hgram0 hL ((H.vT u).symm ⟨w, h⟩) w
    (by rw [hH.eV u, Equiv.apply_symm_apply]) h (hπ u w h)
  refine ⟨{ piG := X.piG, piG_K := ?_, piG_norm := ?_, splitG_pi := ?_, splitG_alg := ?_, frG_lat := ?_, fM_pi := hπ u, fMe := e, fv0 := he }, rfl⟩
  · intro i; have h := (F u).gl_K i; rw [hpi] at h; exact h
  · intro i; have h := (F u).gl.piG_norm i; rw [hpi] at h; exact h
  · intro i v hv; have h := (F u).gl.sp_pi i v hv; rw [hpi, hH.sp u] at h; exact h
  · intro i v hv a; have h := (F u).gl.sp_alg i v hv a; rw [hH.sp u] at h; exact h
  · intro i v hv t
    have h := (F u).glev0.fr_lat i v hv
    rw [(hH.car0 u).Lb_eq, hH.fr0 u] at h
    have hphi : (F u).gl.phi i v hv = (RingHom.fst _ _).comp ((H.lev0 u).splitG i v hv).toRingHom := by
      simp only [GLoc.phi, hH.sp u]
    rw [hphi] at h
    exact frLat_of_reindex (rank_eq_first_level _) _ _ _ h t

end GlobalTheory.Mem.Col2.TC
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → ∀ u, ∃ x : Formalism.L2.Herm.ColLevelX (H.lev0 u) (fun x => x ∈ (I.rec7 l Z).host.K) (A u).piU (H.vT u) (fun v c z => ((I.rec7 l Z).fm u).fv 0 v c ((A u).pr 0 v c z)), x.piG = X.piG := by
  atlas_forward_decl GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem
end
