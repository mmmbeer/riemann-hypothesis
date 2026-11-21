import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed
import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo

section
set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds

section Perm

variable {d : ℕ} (c : Composition d)

end Perm

section Minor

variable {E : Type} [Field E] {d : ℕ}

end Minor

theorem max_mul_le {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : max 1 (x * z) ≤ max 1 x * max 1 z := by
  have h1 : (1 : ℝ) ≤ max 1 x := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 z := le_max_left _ _
  apply max_le
  · nlinarith
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hz (by linarith)

def pre (y : ℕ → ℝ) (a : ℕ) : ℝ := ∏ i ∈ range (a + 1), y i

section Ends

variable {E : Type} [Field E] {d : ℕ}

end Ends

end Formalism.MainNotions.S.Pv.HH

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def K1 : ℝ := 4 ^ (D.R.rS + 1) * ((D.R.rS + 1).factorial : ℝ) ^ 2 * rho0 D ^ (2 * (D.R.rS + 1))

end Formalism.MainNotions.S.Pv.HH

end
end

section
set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem rdE_pos' : 0 < D.host.rdE := lt_of_lt_of_le zero_lt_one (one_le_rdE D)

theorem one_le_prod_norm (x : D.host.E) (hx : x ∈ intS D) (h0 : x ≠ 0) : 1 ≤ ∏ τ, ‖embS D τ x‖ :=
  Formalism.MainNotions.BesselShellMomentBounds.prod_absV_ge_one D x hx h0


def qS : ℝ := D.host.rdE ^ (-(D.R.rS : ℝ))






def R0 : ℝ := ((qS D)⁻¹) ^ (2 * (D.R.rS + 1))


def rhoIJ {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : ℝ := ∏ a, (rhoF D (I a) * rhoF D (J a))





theorem frameExp_le (l : ℕ) (hl : l ≤ D.R.rS + 1) : frameExp D.R.rS l ≤ (D.R.rS + 1) ^ 2 := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (D.R.rS + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, (D.R.rS + 1) :=
        Finset.sum_le_sum fun a _ => Nat.sub_le _ _
    _ = l * (D.R.rS + 1) := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; congr 1
    _ ≤ (D.R.rS + 1) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hl

def R1 : ℝ := D.host.rdE ^ (2 * ((D.R.rS : ℝ) + 1) ^ 2)






end Formalism.MainNotions.S.Pv.HH

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

end Formalism.MainNotions.S.Pv.HH

end
end

section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)


def Gbd (b C β : ℝ) (Z : GramM D) : ℝ := (2 * β ^ 2 * (b ^ (C * (D.R.m : ℝ) ^ 2)) ^ 2) ^ D.R.f * sizeZ D b C Z ^ 2



theorem embS_star (τ : D.what₂.Tau) (x : D.host.E) : embS D τ (star x) = starRingEnd ℂ (embS D τ x) := by
  unfold embS
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj _ _
  | exact NumberField.IsCMField.embedding_complexConj _ _
  | exact NumberField.IsCMField.map_complexConj _ _
  | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (D.host.emb _) x : _)

theorem frameExp_succ : frameExp D.R.rS (D.R.rS + 1) = frameExp D.R.rS D.R.rS := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

def wG : ℝ := D.host.rdE ^ (-(2 * (frameExp D.R.rS D.R.rS : ℝ)))

private theorem one_le_host_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero D.host.E
  have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
  have h'' : ((1 : ℤ) : ℝ) ≤ ((|discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h'
  simpa [Int.cast_abs] using h''


theorem wG_pos : 0 < wG D := by
  unfold wG
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_host_rdE D)) _



theorem absGz_eq {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : FlagU D u')
    (τ : D.what₂.Tau) :
    |Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ| = ‖embS D τ (Gval (lf D F0) F')‖ * wG D ^ 2 := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (lf D F0) F') =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (lf D F0) F') D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (lf D F0).fl F'.fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.norm_real, Real.norm_eq_abs]
  unfold Cnt.Gz absDl absReal
  rw [frameExp_succ]
  simp only [Complex.normSq_eq_norm_sq]
  rw [← abs_of_pos (pow_pos (wG_pos D) 2), ← abs_mul]
  congr 1
  unfold wG
  ring


end Formalism.MainNotions.S.Pv.HH

end
end
