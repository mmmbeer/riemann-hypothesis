import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV

section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def FixLoc : Prop :=
  IsCMExt F E σ → ∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, sigR (Fv F v) σ x = x → sigR (Fv F v) σ y = y →
    IsU v (x + y) → IsU v x ∨ IsU v y

def TrNd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ π : Fv F v, IsUnif v π → ∀ c ∈ OEv (E := E) v,
    sc (E := E) v (π⁻¹) * c ∉ OEv (E := E) v → ∃ t ∈ OEv (E := E) v, IsU v (t * c + sigR (Fv F v) σ (t * c))

def PrimPerp : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ π : Fv F v, IsUnif v π ∧ ∃ p ∈ PerpG σ J v Λ X, sc (E := E) v (π⁻¹) • p ∉ latLoc (E := E) v Λ

theorem isU_neg {z : Fv F v ⊗[F] E} (h : IsU v (-z)) : IsU v z := by
  obtain ⟨w, hw0, hw⟩ := h
  exact ⟨-w, oev_neg v hw0, by rw [mul_neg, ← neg_mul]; exact hw⟩

theorem isU_of_mul {a z : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (h : IsU v (a * z)) : IsU v z := by
  obtain ⟨w, hw0, hw⟩ := h
  exact ⟨a * w, (oSub v).2 _ ha _ hw0, by rw [← hw]; ring⟩

theorem unit_of_pair (hF : FixLoc σ v) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E)
    (p q : Fin n → Fv F v ⊗[F] E) (hp : p ∈ PerpG σ J v Λ X) (hq : q ∈ PerpG σ J v Λ X)
    (t : Fv F v ⊗[F] E) (ht : t ∈ OEv (E := E) v)
    (hu : IsU v (t * hR (Fv F v) σ J q p + sigR (Fv F v) σ (t * hR (Fv F v) σ J q p))) :
    ∃ r ∈ PerpG σ J v Λ X, IsU v (hR (Fv F v) σ J r r) := by
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  set s := sigR (Fv F v) σ t with hs
  have hs0 : s ∈ OEv (E := E) v := sigR_mem σ v ht
  have hss : sigR (Fv F v) σ s = t := sigR_invol σ v hcm t
  set r := p + s • q with hr
  have hrP : r ∈ PerpG σ J v Λ X := by
    refine ⟨Submodule.add_mem _ hp.1 (oSmul v Λ hL s hs0 q hq.1), fun i => ?_⟩
    rw [hr, hR_add_right', hR_smul_right, hp.2 i, hq.2 i, mul_zero, add_zero]
  set α := hR (Fv F v) σ J p p
  set β := hR (Fv F v) σ J q q
  set c := hR (Fv F v) σ J q p
  have hpq : hR (Fv F v) σ J p q = sigR (Fv F v) σ c := (hR_conj σ J v hcm hJ q p).symm
  have hrr : hR (Fv F v) σ J r r = (t * c + sigR (Fv F v) σ (t * c)) + (α + t * s * β) := by
    rw [hr, hR_add_left', hR_add_right', hR_add_right', hR_smul_left, hR_smul_left, hR_smul_right,
      hR_smul_right, hpq, hss, map_mul]
    rw [hs]; ring
  have hα0 : α ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  have hβ0 : β ∈ OEv (E := E) v := (hsd q).1 hq.1 q hq.1
  have hr0 : hR (Fv F v) σ J r r ∈ OEv (E := E) v := (hsd r).1 hrP.1 r hrP.1
  have hαf : sigR (Fv F v) σ α = α := hR_conj σ J v hcm hJ p p
  have hβf : sigR (Fv F v) σ β = β := hR_conj σ J v hcm hJ q q
  have hrf : sigR (Fv F v) σ (hR (Fv F v) σ J r r) = hR (Fv F v) σ J r r := hR_conj σ J v hcm hJ r r
  have hts0 : t * s ∈ OEv (E := E) v := (oSub v).2 _ ht _ hs0
  have htsβ0 : t * s * β ∈ OEv (E := E) v := (oSub v).2 _ hts0 _ hβ0
  have htsβf : sigR (Fv F v) σ (t * s * β) = t * s * β := by
    rw [map_mul, map_mul, hss, hβf, hs]; ring
  have hm0 : -(α + t * s * β) ∈ OEv (E := E) v := oev_neg v (oev_add v hα0 htsβ0)
  have hmf : sigR (Fv F v) σ (-(α + t * s * β)) = -(α + t * s * β) := by
    rw [map_neg, map_add, hαf, htsβf]
  have hsum : hR (Fv F v) σ J r r + -(α + t * s * β) = t * c + sigR (Fv F v) σ (t * c) := by
    rw [hrr]; ring
  rcases hF hcm _ hr0 _ hm0 hrf hmf (by rw [hsum]; exact hu) with h | h
  · exact ⟨r, hrP, h⟩
  · have h' : IsU v (-α + -(t * s * β)) := by rw [← neg_add]; exact h
    rcases hF hcm _ (oev_neg v hα0) _ (oev_neg v htsβ0) (by rw [map_neg, hαf]) (by rw [map_neg, htsβf]) h'
      with h2 | h2
    · exact ⟨p, hp, isU_neg v h2⟩
    · exact ⟨q, hq, isU_of_mul v hts0 (isU_neg v h2)⟩

theorem partner (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ) (hU : UniG σ J v X) (π : Fv F v)
    (p : Fin n → Fv F v ⊗[F] E) (hp : p ∈ PerpG σ J v Λ X) (hpn : sc (E := E) v (π⁻¹) • p ∉ latLoc (E := E) v Λ) :
    ∃ q ∈ PerpG σ J v Λ X, sc (E := E) v (π⁻¹) * hR (Fv F v) σ J q p ∉ OEv (E := E) v := by
  have h1 : ¬ ∀ x ∈ latLoc (E := E) v Λ, hR (Fv F v) σ J x (sc (E := E) v (π⁻¹) • p) ∈ OEv (E := E) v :=
    fun h => hpn ((hsd _).2 h)
  push_neg at h1
  obtain ⟨x, hx, hxn⟩ := h1
  obtain ⟨c, -, hc⟩ := splitG σ J v Λ hL hsd X hX hU x hx
  refine ⟨_, hc, ?_⟩
  rw [← hR_smul_right, hR_sub_left', hR_sum_left']
  have : ∀ i, hR (Fv F v) σ J (c i • X i) (sc (E := E) v (π⁻¹) • p) = 0 := by
    intro i
    rw [hR_smul_left, hR_smul_right, hp.2 i, mul_zero, mul_zero]
  simp only [this, Finset.sum_const_zero, sub_zero]
  exact hxn

theorem unitNorm_of (hF : FixLoc σ v) (hT : TrNd σ J ψ v) (hP : PrimPerp σ J ψ v Λ) : UnitNorm σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨π, hπ, p, hp, hpn⟩ := hP hstd hL hsd hun ι X hX hUX hc
  obtain ⟨q, hq, hqp⟩ := partner σ J v Λ hL hsd X hX hUX π p hp hpn
  obtain ⟨t, ht0, htu⟩ := hT hstd hun π hπ _ ((hsd p).1 hp.1 q hq.1) hqp
  obtain ⟨r, hr, u', hu'0, hu'⟩ := unit_of_pair σ J ψ v Λ hF hstd hL hsd X p q hp hq t ht0 htu
  exact ⟨r, hr, u', hu'0, hu'⟩

end PI.OmLocU.UnN
end
end

section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem fixed_mem_F (hcm : IsCMExt F E σ) (e : E) (he : σ e = e) : ∃ f : F, algebraMap F E f = e := by
  obtain ⟨-, hE, hdeg, hconj⟩ := hcm
  by_contra hne
  have hbot : e ∉ (⊥ : IntermediateField F E) := by
    intro hmem
    obtain ⟨f, hf⟩ := IntermediateField.mem_bot.mp hmem
    exact hne ⟨f, hf⟩
  have hint : IsIntegral F e := Algebra.IsIntegral.isIntegral e
  have htop : (IntermediateField.adjoin F {e}) = ⊤ := by
    have hd : Module.finrank F (IntermediateField.adjoin F {e}) ∣ 2 := by
      have := IntermediateField.finrank_dvd_of_le_right (K := F) (le_top : (IntermediateField.adjoin F {e}) ≤ ⊤)
      rwa [IntermediateField.finrank_top', hdeg] at this
    have h1 : Module.finrank F (IntermediateField.adjoin F {e}) ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff]
      exact hbot
    have h22 : Module.finrank F (IntermediateField.adjoin F {e}) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd h h1
      · exact h
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [h22, IntermediateField.finrank_top', hdeg]
  have hfix : ∀ x : E, σ x = x := by
    intro x
    have hx : x ∈ Algebra.adjoin F ({e} : Set E) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]
      trivial
    have hle : Algebra.adjoin F ({e} : Set E) ≤ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [Algebra.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact he
    exact hle hx
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hE.isComplex w)
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  ext x
  have h := hconj w.embedding x
  rw [hfix] at h
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h]

theorem sc_eq (a : Fv F v) : sc (E := E) v a = algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  simp [sc, Algebra.TensorProduct.algebraMap_apply]

theorem add_sig_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : ∃ t : Fv F v, z + sigR (Fv F v) σ z = sc (E := E) v t := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [sc_eq]⟩
  | tmul r e =>
    obtain ⟨f, hf⟩ := fixed_mem_F σ hcm (e + σ e) (by rw [map_add, sigma_invol σ hcm, add_comm])
    refine ⟨f • r, ?_⟩
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    rw [hs, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨t1, h1⟩ := hx
    obtain ⟨t2, h2⟩ := hy
    refine ⟨t1 + t2, ?_⟩
    rw [map_add, sc_eq, map_add, ← sc_eq, ← sc_eq, ← h1, ← h2]
    abel

theorem two_ne_zero_v : (2 : Fv F v) ≠ 0 := by
  have h : (2 : F) ≠ 0 := two_ne_zero
  intro h2
  apply h
  apply (algebraMap F (Fv F v)).injective
  rw [map_ofNat, map_zero]
  exact h2

theorem fix_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) :
    ∃ a : Fv F v, z = sc (E := E) v a := by
  obtain ⟨t, ht⟩ := add_sig_sc σ v hcm z
  rw [hz] at ht
  refine ⟨t / 2, ?_⟩
  rw [div_eq_inv_mul, ← sc_mul, ← ht, ← smul_eq_sc, ← two_smul (Fv F v) z, smul_smul,
    inv_mul_cancel₀ (two_ne_zero_v v), one_smul]

theorem one_mem_oEv : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using gen_mem (E := E) v 1

theorem sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  simpa using sc_mul_mem_oEv (E := E) v hc (one_mem_oEv v)

theorem sc_mem_int {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hle : OEv (E := E) v ⊆ {z | IsIntegral (v.adicCompletionIntegers F) z} := by
    show (Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) : Set (Fv F v ⊗[F] E)) ⊆ _
    intro z hz
    have hsp : Submodule.span (v.adicCompletionIntegers F)
        ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) ≤
        (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      exact IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F)) (inclR (F := F) (Fv F v))
        (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
    exact hsp hz
  have hint : IsIntegral (v.adicCompletionIntegers F) (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) := by
    rw [← sc_eq]
    exact hle ha
  have hint' : IsIntegral (v.adicCompletionIntegers F) a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers F) (Fv F v) (Fv F v ⊗[F] E))
      (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).mp hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  rw [← hy]
  exact y.2

theorem fix_int (hcm : IsCMExt F E σ) {z : Fv F v ⊗[F] E} (hz0 : z ∈ OEv (E := E) v) (hz : sigR (Fv F v) σ z = z) :
    ∃ a ∈ v.adicCompletionIntegers F, z = sc (E := E) v a := by
  obtain ⟨a, ha⟩ := fix_sc σ v hcm z hz
  exact ⟨a, sc_mem_int v (ha ▸ hz0), ha⟩

theorem isU_sc {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F)
    (hu : IsUnit (⟨a, ha⟩ : v.adicCompletionIntegers F)) : IsU v (sc (E := E) v a) := by
  obtain ⟨u, hu'⟩ := hu
  refine ⟨sc v ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F), sc_mem v (SetLike.coe_mem _), ?_⟩
  have h1 : a * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) = 1 := by
    have h2 := congrArg (fun r : v.adicCompletionIntegers F => (r : Fv F v)) u.mul_inv
    rw [hu'] at h2
    simpa using h2
  rw [sc_mul, h1, sc_one]

private theorem fixLoc_holds_lemma {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (h : IsU (E := E) v (sc v c)) : IsUnit (⟨c, hc⟩ : v.adicCompletionIntegers F) := by
  obtain ⟨w, hw, hcw⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [sc_eq, map_zero, zero_mul] at hcw
    exact zero_ne_one hcw
  have hweq : w = sc v c⁻¹ := by
    have h1 : sc (E := E) v c⁻¹ * (sc v c * w) = sc v c⁻¹ := by rw [hcw, mul_one]
    rw [← mul_assoc, sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at h1
    exact h1
  have hinv : c⁻¹ ∈ v.adicCompletionIntegers F := sc_mem_int v (hweq ▸ hw)
  have hprod : (⟨c, hc⟩ : v.adicCompletionIntegers F) * ⟨c⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    simp [mul_inv_cancel₀ hc0]
  exact IsUnit.of_mul_eq_one _ hprod

theorem fixLoc_holds : FixLoc σ v := by
  intro hcm x hx y hy hfx hfy hu
  obtain ⟨a, ha, rfl⟩ := fix_int σ v hcm hx hfx
  obtain ⟨b, hb, rfl⟩ := fix_int σ v hcm hy hfy
  have hab : a + b ∈ v.adicCompletionIntegers F := add_mem ha hb
  rw [sc_eq, sc_eq, ← map_add, ← sc_eq] at hu
  have hU : IsUnit ((⟨a, ha⟩ : v.adicCompletionIntegers F) + ⟨b, hb⟩) := fixLoc_holds_lemma v hab hu
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h | h
  · exact Or.inl (isU_sc v ha h)
  · exact Or.inr (isU_sc v hb h)

end PI.OmLocU.UnN
end
end

section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem hR_smul_right_F (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v) :
    hR (Fv F v) σ J x (c • w) = c • hR (Fv F v) σ J x w := by
  rw [← algebraMap_smul (Fv F v ⊗[F] E) c w, hR_smul_right, Algebra.smul_def]

def perpMap {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) where
  toFun w i := hR (Fv F v) σ J (X i) w
  map_add' x y := funext fun i => hR_add_right' σ J v (X i) x y
  map_smul' c w := funext fun i => hR_smul_right_F σ J v (X i) w c

theorem exists_perp_ne_zero (hcm : IsCMExt F E σ) {ι : Type} [Fintype ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hc : Fintype.card ι < n) : ∃ w : Fin n → Fv F v ⊗[F] E, w ≠ 0 ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0 := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have hlt : Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E) < Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := perpMap σ J v X) hlt
  obtain ⟨w, hw, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨w, hne, fun i => congrFun (LinearMap.mem_ker.1 hw) i⟩

theorem primPerp_holds : PrimPerp σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨L, hLat, rfl⟩ := hL
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = b i := fun i => Module.Basis.mk_apply hli hsp i
  have hsymm : ∀ c : Fin m → Fv F v, B.equivFun.symm c = ∑ i, c i • b i := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp only [hB]
  obtain ⟨w, hw0, hwp⟩ := exists_perp_ne_zero σ J v hstd.1 X hc
  set c := B.equivFun w with hcdef
  have hcw : w = ∑ i, c i • b i := by rw [← hsymm, hcdef, LinearEquiv.symm_apply_apply]
  have hcne : ∃ i, c i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw0
    rw [hcw]
    simp [h]
  obtain ⟨i0, hi0⟩ := hcne
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (c i)) hne
  have hcj : c j ≠ 0 := by
    intro h
    have h1 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le'))
  have hvj : Valued.v (c j) ≠ 0 := (Valuation.ne_zero_iff _).2 hcj
  set p := (c j)⁻¹ • w with hp
  have hcp : B.equivFun p = (c j)⁻¹ • c := by rw [hp, map_smul]
  have hpmem : p ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
    refine (hmem p).2 ⟨fun i => ⟨(c j)⁻¹ * c i, ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      calc (Valued.v (c j))⁻¹ * Valued.v (c i) ≤ (Valued.v (c j))⁻¹ * Valued.v (c j) :=
            mul_le_mul' le_rfl (hj i (Finset.mem_univ _))
        _ = 1 := inv_mul_cancel₀ hvj
    · rw [← hsymm]
      change p = B.equivFun.symm ((c j)⁻¹ • c)
      rw [← hcp, LinearEquiv.symm_apply_apply]
  refine ⟨ϖ, hϖ, p, ⟨hpmem, fun i => ?_⟩, ?_⟩
  · rw [hp, hR_smul_right_F, hwp i, smul_zero]
  · intro hin
    rw [sc_eq, algebraMap_smul] at hin
    obtain ⟨d, hd⟩ := (hmem _).1 hin
    have hd' : ϖ⁻¹ • p = B.equivFun.symm (fun i => (d i : Fv F v)) := by rw [hsymm]; exact hd
    have hcoord := congrFun (congrArg B.equivFun hd') j
    rw [LinearEquiv.apply_symm_apply, map_smul, hcp] at hcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    rw [inv_mul_cancel₀ hcj, mul_one] at hcoord
    have hint : ϖ⁻¹ ∈ v.adicCompletionIntegers F := by rw [hcoord]; exact (d j).2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hint
    have h1 : Valued.v (ϖ * ϖ⁻¹) ≤ WithZero.exp (-1 : ℤ) := by
      rw [map_mul, hv]
      calc WithZero.exp (-1 : ℤ) * Valued.v ϖ⁻¹ ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl hint
        _ = _ := mul_one _
    rw [mul_inv_cancel₀ hϖ0, map_one] at h1
    exact absurd h1 (by decide)

end PI.OmLocU.UnN
end
end

section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
  PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem tr_nd_field {k K : Type} [Field k] [Field K] [Algebra k K] (σ' : K ≃ₐ[k] K) (hne : σ' ≠ AlgEquiv.refl)
    (z : K) (hz : z ≠ 0) : ∃ t : K, t * z + σ' (t * z) ≠ 0 := by
  have hu : ∃ u : K, u + σ' u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    have h1 : (1 : K) + 1 = 0 := by simpa using h 1
    ext u
    have h2 : σ' u = -u := eq_neg_of_add_eq_zero_right (h u)
    rw [h2]
    show -u = u
    have h3 : u + u = 0 := by rw [← mul_one u, ← mul_add, h1, mul_zero]
    exact (eq_neg_of_add_eq_zero_left h3).symm
  obtain ⟨u, hu⟩ := hu
  refine ⟨u * z⁻¹, ?_⟩
  rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  exact hu

theorem tr_nd_prod {k : Type} [Field k] (z : k × k) (hz : z ≠ 0) :
    ∃ t : k × k, t * z + (RingEquiv.prodComm (R := k) (S := k)).toRingHom (t * z) ≠ 0 := by
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by
      intro h2
      exact hz (Prod.ext h1 h2)
    refine ⟨(0, z.2⁻¹), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h2] at this
  · refine ⟨(z.1⁻¹, 0), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h1] at this

theorem trNd_of_res {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hcm : IsCMExt F E σ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (hres : IsRes σ v ϖ τ π) (hnd : ∀ z : K, z ≠ 0 → ∃ t : K, t * z + τ (t * z) ≠ 0)
    (c : Fv F v ⊗[F] E) (hc : c ∈ OEv (E := E) v) (hcn : sc (E := E) v (ϖ⁻¹) * c ∉ OEv (E := E) v) :
    ∃ t ∈ OEv (E := E) v, IsU v (t * c + sigR (Fv F v) σ (t * c)) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨hsurj, hker, hsig⟩ := hres
  let cO : OR (E := E) v := ⟨c, hc⟩
  have hc0 : π cO ≠ 0 := by
    intro h
    obtain ⟨d, hd0, hd⟩ := (hker cO).1 h
    apply hcn
    have hd' : c = sc (E := E) v ϖ * d := hd
    rw [hd', ← mul_assoc, sc_eq, sc_eq, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_mul]
    exact hd0
  obtain ⟨tb, htb⟩ := hnd _ hc0
  obtain ⟨tO, htO⟩ := hsurj tb
  have ht0 : (tO : Fv F v ⊗[F] E) ∈ OEv (E := E) v := tO.2
  have htc0 : (tO : Fv F v ⊗[F] E) * c ∈ OEv (E := E) v := (tO * cO).2
  let yO : OR (E := E) v := ⟨sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c), sigR_mem σ v htc0⟩
  have hy : π yO = τ (π (tO * cO)) := hsig (tO * cO) yO rfl
  set s := (tO : Fv F v ⊗[F] E) * c + sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c) with hs
  have hsO : π (tO * cO + yO) ≠ 0 := by
    rw [map_add, hy, map_mul, htO]
    exact htb
  have hs0 : s ∈ OEv (E := E) v := (tO * cO + yO).2
  have hsf : sigR (Fv F v) σ s = s := by
    rw [hs, map_add, sigR_invol σ v hcm, add_comm]
  refine ⟨tO, ht0, ?_⟩
  obtain ⟨a, ha, hsa⟩ := fix_int σ v hcm hs0 hsf
  rw [← hs, hsa]
  by_cases hva : Valued.v a < 1
  · exfalso
    obtain ⟨d, hd⟩ := (mem_unifO_iff v hϖ ⟨a, ha⟩).2 hva
    apply hsO
    apply (hker _).2
    refine ⟨sc (E := E) v (d : Fv F v), sc_mem v d.2, ?_⟩
    show s = _
    rw [hsa, sc_eq, sc_eq, sc_eq, ← map_mul]
    exact congrArg _ hd
  · have ha1 : Valued.v a = 1 := le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 ha) (not_lt.1 hva)
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact zero_ne_one ha1
    have hai : a⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ha1, inv_one]
    refine ⟨sc (E := E) v (a⁻¹), sc_mem v hai, ?_⟩
    rw [sc_eq, sc_eq, ← map_mul, mul_inv_cancel₀ ha0, map_one]

theorem trNd_of (hR : ResAlg σ J ψ v) : TrNd σ J ψ v := by
  intro hstd hun ϖ hϖ c hc hcn
  obtain ⟨k, _, _, -, hcase⟩ := hR hstd hun ϖ hϖ
  rcases hcase with ⟨-, K, _, _, σ', π, -, -, hne, hres⟩ | ⟨-, π, hres⟩
  · exact trNd_of_res σ v (σ' : K →+* K) π hstd.1 hϖ hres (fun z hz => tr_nd_field σ' hne z hz) c hc hcn
  · exact trNd_of_res σ v _ π hstd.1 hϖ hres (fun z hz => tr_nd_prod z hz) c hc hcn

theorem unitNorm_of_res (hR : ResAlg σ J ψ v) : UnitNorm σ J ψ v Λ :=
  unitNorm_of σ J ψ v Λ (fixLoc_holds σ v) (trNd_of σ J ψ v hR) (primPerp_holds σ J ψ v Λ)

theorem orbAll_of_res (a : ℕ) (Y : TupV (E := E) v n a) (hN : NormOne σ J ψ v) (hR : ResAlg σ J ψ v) :
    OrbAll σ J ψ v Λ a Y :=
  orbAll_of_norm σ J ψ v Λ a Y hN (unitNorm_of_res σ J ψ v Λ hR)

end PI.OmLocU.UnN
end
end
