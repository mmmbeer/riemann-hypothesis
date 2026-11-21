import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerToCoinvIffInvFactor

section
noncomputable section

open GlobalTheory.WeilM GlobalTheory.LinPair
open scoped Matrix

namespace GlobalTheory.KSTransfer

end GlobalTheory.KSTransfer

end
end

section
noncomputable section

open GlobalTheory.WeilM GlobalTheory.KSTransfer MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

section Defs

variable {k E : Type} [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E)

theorem map_mul_c {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    (A * B).map c = A.map c * B.map c := Matrix.map_mul (f := c.toRingHom)

def stabX {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (J : Matrix ι ι E) (X : Matrix ι (Fin r) E) :
    Subgroup (UG c J) where
  carrier := {q | ∃ a : GL (Fin r) E, ((q : GL ι E) : Matrix ι ι E) * X = X * (a : Matrix (Fin r) (Fin r) E)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by
      rw [Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro q ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    calc _ = (((q : GL ι E)⁻¹ : GL ι E) : Matrix ι ι E) * (X * (a : Matrix (Fin r) (Fin r) E)) *
          ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]; rfl
      _ = _ := by rw [← ha, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

def skew (r : ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {s | sᵀ + s.map c = 0}
  zero_mem' := by ext i j; simp
  add_mem' := by
    intro s t hs ht
    ext i j
    have h1 := congrFun (congrFun hs i) j
    have h2 := congrFun (congrFun ht i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, map_add, Matrix.zero_apply] at *
    linear_combination h1 + h2
  neg_mem' := by
    intro s hs
    ext i j
    have h1 := congrFun (congrFun hs i) j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.map_apply, map_neg, Matrix.neg_apply,
      Matrix.zero_apply] at *
    linear_combination -h1

def dualGL {r : ℕ} (a : GL (Fin r) E) : GL (Fin r) E where
  val := (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map c)ᵀ
  inv := ((a : Matrix (Fin r) (Fin r) E).map c)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← map_mul_c, Units.mul_inv, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← map_mul_c, Units.inv_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]

def parMat {m' r : ℕ} (J' : Matrix (Fin m') (Fin m') E) (a : GL (Fin r) E) (g : GL (Fin m') E)
    (w : Matrix (Fin m') (Fin r) E) (s : Matrix (Fin r) (Fin r) E) :
    Matrix (Fin m' ⊕ (Fin r ⊕ Fin r)) (Fin m' ⊕ (Fin r ⊕ Fin r)) E :=
  Matrix.fromBlocks (g : Matrix (Fin m') (Fin m') E) (Matrix.fromCols 0 ((g : Matrix (Fin m') (Fin m') E) * w))
    (Matrix.fromRows (-((a : Matrix (Fin r) (Fin r) E) * ((w.map c)ᵀ * J'ᵀ))) 0)
    (Matrix.fromBlocks (a : Matrix (Fin r) (Fin r) E)
      ((a : Matrix (Fin r) (Fin r) E) * (s - (2 : E)⁻¹ • ((w.map c)ᵀ * J'ᵀ * w))) 0
      ((dualGL c a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))

def omega {m' r : ℕ} (J' : Matrix (Fin m') (Fin m') E) (w w' : Matrix (Fin m') (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  (2 : E)⁻¹ • ((w'.map c)ᵀ * J'ᵀ * w - (w.map c)ᵀ * J'ᵀ * w')

end Defs

section Top

variable {k E : Type} [Field k] [Field E] [Algebra k E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end Top

section Mod

variable {k E : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Field E] [Algebra k E]
  {c : E →ₐ[k] E} {r : ℕ}

end Mod

section Steps

end Steps

section Law

end Law

end GlobalTheory.ParAvg

end
end

section
noncomputable section

open GlobalTheory.WeilM GlobalTheory.KSTransfer GlobalTheory.ParAvg MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

theorem isMulRightInvariant_of_modular {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, modularCharacterFun g = 1) : μ.IsMulRightInvariant :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

theorem modularCharacterFun_GL {r : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [LocallyCompactSpace (GL (Fin r) E)] (a : GL (Fin r) E) : modularCharacterFun a = 1 := by
  borelize (GL (Fin r) E)
  refine GlobalTheory.SplitFlip.hom_eq_one_of_center (modularCharacter : GL (Fin r) E →* ℝ≥0) (fun z hz => ?_) a
  change modularCharacterFun z = 1
  have e : map (fun x : GL (Fin r) E => x * z) (haar : Measure (GL (Fin r) E)) = haar := by
    rw [show (fun x : GL (Fin r) E => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      map_mul_left_eq_self]
  rw [modularCharacterFun_eq_haarScalarFactor (haar : Measure (GL (Fin r) E)) z]
  simp only [e, haarScalarFactor_self]

end GlobalTheory.ParAvg
end
end
