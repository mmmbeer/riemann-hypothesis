import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

namespace GlobalTheory.LKTorus.Model

open Complex

def conjC : ℂ →ₐ[ℝ] ℂ := (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)

def conjCC : (ℂ × ℂ) →ₐ[ℝ] (ℂ × ℂ) := AlgHom.prodMap conjC conjC

theorem conjCC_apply (z : ℂ × ℂ) : conjCC z = ((starRingEnd ℂ) z.1, (starRingEnd ℂ) z.2) := rfl


theorem mem_normSub_iff {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] (c : A →ₐ[k] A)
    (a : fixU k c) :
    a ∈ normSub k c ↔ ∃ (t : kˣ) (x : Aˣ), ((a : Aˣ) : A) = algebraMap k A t * (x * c x) := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem a ha => exact ha
    | one => exact ⟨1, 1, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨s, x, hs⟩ := ha
      obtain ⟨t, y, ht⟩ := hb
      refine ⟨s * t, x * y, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul, map_mul, hs, ht]
      ring
    | inv a _ ha =>
      obtain ⟨s, x, hs⟩ := ha
      refine ⟨s⁻¹, x⁻¹, ?_⟩
      have h1 : ((a : Aˣ) : A) * (algebraMap k A ((s⁻¹ : kˣ) : k) * (((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A))) = 1 := by
        rw [hs]
        calc _ = (algebraMap k A (s : k) * algebraMap k A ((s⁻¹ : kˣ) : k)) * (((x : Aˣ) : A) * ((x⁻¹ : Aˣ) : A))
              * (c ((x : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)) := by ring
          _ = 1 := by rw [← map_mul, ← map_mul]; simp
      rw [Subgroup.coe_inv]
      exact Units.inv_eq_of_mul_eq_one_right h1
  · intro h
    exact Subgroup.subset_closure h


def u : (ℂ × ℂ)ˣ := ⟨(1, -1), (1, -1), by ext <;> simp, by ext <;> simp⟩

theorem u_mem : u ∈ fixU ℝ conjCC := by
  show conjCC ((1, -1) : ℂ × ℂ) = (1, -1)
  simp [conjCC_apply]

theorem u_not_mem : (⟨u, u_mem⟩ : fixU ℝ conjCC) ∉ normSub ℝ conjCC := by
  rw [mem_normSub_iff]
  rintro ⟨t, x, h⟩
  have h' : ((1, -1) : ℂ × ℂ) = algebraMap ℝ (ℂ × ℂ) t * (x * conjCC x) := h
  have h1 := congrArg (fun z : ℂ × ℂ => z.1.re) h'
  have h2 := congrArg (fun z : ℂ × ℂ => z.2.re) h'
  simp only [conjCC_apply, Prod.fst_mul, Prod.snd_mul, Complex.mul_conj, Prod.algebraMap_apply,
    Complex.coe_algebraMap, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.one_re, Complex.neg_re] at h1 h2
  have a := Complex.normSq_nonneg (x : ℂ × ℂ).1
  have b := Complex.normSq_nonneg (x : ℂ × ℂ).2
  rcases le_total 0 (t : ℝ) with ht | ht
  · nlinarith [mul_nonneg ht b]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos ht (neg_nonpos.mpr a)]

theorem nontrivial_prod : Nontrivial (H1 ℝ conjCC) := by
  unfold H1
  exact ⟨⟨QuotientGroup.mk ⟨u, u_mem⟩, 1, fun h => u_not_mem ((QuotientGroup.eq_one_iff _).mp h)⟩⟩


end GlobalTheory.LKTorus.Model
