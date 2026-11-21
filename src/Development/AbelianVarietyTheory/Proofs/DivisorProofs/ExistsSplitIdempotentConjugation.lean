import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

def conjF (G : HTGroup p) : G.F →ₐ[ℚ] G.F :=
  ((IsCMField.complexConj G.F : G.F →+* G.F)).toRatAlgHom

variable {G : HTGroup p} {P : Pair G}

theorem algebraMap_injective (G : HTGroup p) (P : Pair G) :
    Function.Injective (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] algF P)) := by
  intro a b h
  have hL : Function.Injective (algebraMap ℚ (algF P)) := (algebraMap ℚ (algF P)).injective
  apply Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ_[p]) (A := ℚ_[p]) (B := algF P) hL
  simpa [Algebra.TensorProduct.algebraMap_apply] using h

theorem mem_simT_iff {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {x : Aˣ} :
    x ∈ GlobalTheory.LKTorus.simT k c ↔ ∃ t : kˣ, (x : A) * c x = algebraMap k A t := Iff.rfl

section Phi

variable (G P) (c : algF P →ₐ[ℚ] algF P)

def nuP : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* ℚ_[p]ˣ where
  toFun s := Classical.choose (mem_simT_iff.1 s.2)
  map_one' := by
    apply Units.ext
    apply algebraMap_injective G P
    rw [← Classical.choose_spec (mem_simT_iff.1 (1 : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)).2)]
    simp [Algebra.TensorProduct.one_def]
  map_mul' s t := by
    apply Units.ext
    apply algebraMap_injective G P
    rw [← Classical.choose_spec (mem_simT_iff.1 (s * t).2), Units.val_mul, map_mul,
      ← Classical.choose_spec (mem_simT_iff.1 s.2), ← Classical.choose_spec (mem_simT_iff.1 t.2)]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    ring

variable {G P c}

variable (G P c)

end Phi

end GlobalTheory.CentAtP
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus GlobalTheory.CentAtP
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_ne (G : HTGroup p) : ∃ x ∈ G.Kq, IsCMField.complexConj G.F x ≠ x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  obtain ⟨x, hx, him⟩ := G.hKq.2 v.embedding
  refine ⟨x, hx, fun h => him ?_⟩
  have h2 := IsCMField.complexEmbedding_complexConj G.F v.embedding x
  rw [h] at h2
  have := congrArg Complex.im h2
  simp only [Complex.conj_im] at this
  linarith

end GlobalTheory.CentAtP
end
end
