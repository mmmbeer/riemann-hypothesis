import Mathlib
import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
set_option maxSynthPendingDepth 1

noncomputable section

open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal

namespace GroundTheory.BlockD

namespace ThmBHecke

section Single

variable {K : Type} [Field K] [NumberField K]

open Classical in

def finSingleOne (w : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K :=
  ⟨Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu ↦ ?_)
    by_contra h
    exact hu (by rw [Pi.single_eq_of_ne h]; exact zero_mem _)⟩

theorem finSingleOne_self (w : HeightOneSpectrum (𝓞 K)) : finSingleOne w w = 1 := by
  classical
  exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1

theorem finSingleOne_of_ne {w u : HeightOneSpectrum (𝓞 K)} (h : u ≠ w) : finSingleOne w u = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) h 1


end Single

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idemAt (P : HeightOneSpectrum (𝓞 E)) : 𝔸[E] := (0, finSingleOne P)

@[simp]
theorem idemAt_fst (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).1 = 0 := rfl

@[simp]
theorem idemAt_snd_self (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).2 P = 1 := finSingleOne_self P

theorem idemAt_snd_of_ne {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) : (idemAt P).2 w = 0 :=
  finSingleOne_of_ne h

theorem adele_fst_mul (a b : 𝔸[E]) : (a * b).1 = a.1 * b.1 := rfl

theorem adeleMap_snd_apply (a : AF F) (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E a).2 w = completionMap (below F w) w (a.2 (below F w)) :=
  rfl

theorem adeleMap_fst_of_isPlaceIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε) :
    (adeleMap F E ε).1 = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))

open Classical in
theorem adeleMap_snd_of_isPlaceIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε)
    (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E ε).2 w = if below F w = v then 1 else 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  rw [adeleMap_snd_apply]
  split_ifs with hw
  · have : (pairA F 0 α).2 (below F w) = 1 := by rw [hw]; exact h1
    rw [this, map_one]
  · have : (pairA F 0 α).2 (below F w) = 0 := h0 _ hw
    rw [this, map_zero]


theorem finPart_mem_intAE_iff (z : AE F E) :
    finPart F E z ∈ intAE F E ↔ ∀ w, (adeleEquiv F E z).2 w ∈ w.adicCompletionIntegers E := by
  rw [mem_intAE_iff, ← adeleEquiv_snd]
  rfl

theorem finPart_mul_incA_mem_iff (e : AE F E) (x : E) :
    finPart F E (e * incA F E x) ∈ intAE F E ↔
      ∀ w, (adeleEquiv F E e).2 w * algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E := by
  rw [finPart_mem_intAE_iff, map_mul, adeleEquiv_incA]
  rfl

theorem inv_mem_adicCompletionIntegers_iff (w : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    algebraMap E (w.adicCompletion E) ((x : E)⁻¹) ∈ w.adicCompletionIntegers E ↔ x ∉ w.asIdeal := by
  have hc : algebraMap E (w.adicCompletion E) ((x : E)⁻¹) = (((x : E)⁻¹ : E) : w.adicCompletion E) := rfl
  rw [hc, coe_mem_adicCompletionIntegers_iff, map_inv₀]
  have hx0 : w.valuation E (x : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hx
  rw [inv_le_one₀ (zero_lt_iff.2 hx0), ← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
  exact ⟨fun h ↦ le_antisymm (w.valuation_le_one x) h, fun h ↦ h.ge⟩

theorem char_iff_exists {e : AE F E} (h01 : ∀ w, (adeleEquiv F E e).2 w = 0 ∨ (adeleEquiv F E e).2 w = 1)
    {x : 𝓞 E} (hx : x ≠ 0) :
    finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E ↔
      ∃ w, (adeleEquiv F E e).2 w = 1 ∧ x ∈ w.asIdeal := by
  rw [finPart_mul_incA_mem_iff]
  constructor
  · intro h
    push_neg at h
    obtain ⟨w, hw⟩ := h
    rcases h01 w with h0 | h1
    · rw [h0, zero_mul] at hw
      exact absurd (zero_mem _) hw
    · rw [h1, one_mul, inv_mem_adicCompletionIntegers_iff w hx, not_not] at hw
      exact ⟨w, h1, hw⟩
  · rintro ⟨w, h1, hxw⟩ hall
    have := hall w
    rw [h1, one_mul, inv_mem_adicCompletionIntegers_iff w hx] at this
    exact this hxw

theorem exists_mem_not_mem {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) :
    ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ x ∉ P.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hc))



section Conj

variable {σ : E →ₐ[F] E}

theorem cA_tmul (a : AF F) (x : E) : cA σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl

theorem cA_incA (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

theorem IsCMExt.sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rw [cA_tmul, cA_tmul, IsCMExt.sigma_sigma h]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem IsCMExt.exists_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hreal : w.IsReal := by
    rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x ↦ ?_
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    change star (w.embedding x) = w.embedding x
    rw [← h.2.2.2, hc]
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal

end Conj

end ThmBHecke

end GroundTheory.BlockD
