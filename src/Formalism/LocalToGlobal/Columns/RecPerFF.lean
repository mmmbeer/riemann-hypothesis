import Formalism.LocalToGlobal.Columns.GFamEv
import Formalism.LocalToGlobal.Columns.StabMapRLInjective
import Formalism.LocalToGlobal.Columns.RecChainCUnfPol
import Formalism.LocalToGlobal.Columns.RefXi1Above
import Formalism.LocalToGlobal.Columns.RecChainYUnfPol
import Mathlib

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Vec

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

def VecAt (E : Type) [Field E] [NumberField E] (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) (all : Prop) : Type :=
  {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal // all ∨ v = 0}

instance (all : Prop) : Finite (VecAt E n SG all) := Subtype.finite

instance vecAct (Λ : LevFam E K n SG) (all : Prop) : MulAction ↥Λ.grp (VecAt E n SG all) where
  smul h v := ⟨fun w => ((h.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w), by
    rcases v.2 with h1 | h1
    · exact Or.inl h1
    · right
      funext w
      rw [h1]
      exact Matrix.mulVec_zero _⟩
  one_smul v := Subtype.ext (funext fun w => Matrix.one_mulVec _)
  mul_smul g h v := Subtype.ext (funext fun w => by
    show ((((g * h : ↥Λ.grp) : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w) =
      ((g.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec
        (((h.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w))
    rw [Matrix.mulVec_mulVec]
    rfl)

abbrev yIdx (Λ : LevFam E K n SG) (all : Prop) : Type := MulAction.orbitRel.Quotient ↥Λ.grp (VecAt E n SG all)

def yIdx.vec {Λ : LevFam E K n SG} {all : Prop} (o : yIdx Λ all) : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal := (Quotient.out o).1

def stabLev (Λ : LevFam E K n SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : LevFam E K n SG := fun w =>
  { H := (Λ w).H ⊓
      { carrier := {h | (h : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w}
        one_mem' := Matrix.one_mulVec _
        mul_mem' := fun {a b} ha hb => by
          show ((a * b : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha]
        inv_mem' := fun {a} ha => by
          show ((a⁻¹ : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w
          conv_lhs => rw [← show (a : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v w) = v w from ha]
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] }
    lam := (Λ w).lam.comp (Subgroup.inclusion inf_le_left) }

end Vec

section Ref

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def refLevCh (m2 : ℕ) : LevCh X Pr R where
  β j := Σ b : L.β j, yIdx (L.levG j b) (j = m2 + 1)
  finβ _ := Fintype.ofFinite _
  decβ _ := Classical.decEq _
  lev j b := stabLev (L.levG j b.1) b.2.vec

end Ref

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)

variable {W Λ u} in

def rcol1To (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1))) (hX : X.Ok) :
    ∀ j, (stepGSD W Λ u 0).EqFun →ₗ[X.K] (stepGSD W Λ u j).EqFun
  | 0 => LinearMap.id
  | j + 1 => (kk j).op (stepOk W Λ hX u j) ∘ₗ rcol1To kk hX j

def rcol1Start (h0 : Λ 0 = colLev Ch 0) : MfV W Ch u →ₗ[X.K] (stepGSD W Λ u 0).EqFun where
  toFun φ := ⟨φ.1, show φ.1 ∈ (formGSD (colVal W u 0 (Pr.vT u) Pr.vGs) (Λ 0)).EqFun by rw [h0]; exact φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hQ in
theorem rcol_rowSG_eq : Pr.vGs = rowSG Pr sel mu := by
  classical
  unfold rowSG uSG
  rw [hQ, Finset.union_empty]

def rcolRow {n : ℕ} (d : DecoSet X.E n ∅ Pr.vGs) : DecoSet X.E n ∅ (rowSG Pr sel mu) := rcol_rowSG_eq sel mu hQ ▸ d

end Defs

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}
  (hX : X.Ok) {Gc : ChGlob X R.m} (hL : L.Ok Ch sel mu cst Gc m2) (h0 : Λ 0 = colLev Ch 0)
  (hΛ : ∀ j, j ≤ m2 + 1 → ∀ b : L.β j, L.levG j b = Λ j) (h1 : ∀ j, j ≤ m2 + 1 → ∀ b b' : L.β j, b = b')
  (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
  {b₁ : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b₁} {P : LevFam X.E X.K R.r Pr.vGs}
  (hK : KerEquivC W Ch sel mu cst L Am u m2 b₁ hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (φ : MfV W Ch u)

end Main

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

def zOfRow0 (σ₀ : X.K →+* ℂ) (hM : (rowGSD W ΛM).Ok) (F : (rowGSD W ΛM).EqFun) : Fin ((rowGSD W ΛM).hDim hM) → ℂ :=
  fun a => σ₀ (((rowGSD W ΛM).hB hM).repr F a)

end Gen

section Cast

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem levFam_eq_cast {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG')
    (A : LevFam E K n SG) (B : LevFam E K n SG') (h : ∀ (w : SG') (hw : w.1 ∈ SG), B w = A ⟨w.1, hw⟩) : B = e ▸ A := by
  subst e
  funext w
  exact h w w.2

variable {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
  (Λ' : LevFam X.E X.K (R.N R.m - 1) SG')

def rowCast (hΛ : Λ' = e ▸ A) (F : (formGSD (rowVal W SG') Λ').EqFun) : (rowGSD W A).EqFun := by
  subst hΛ
  subst e
  exact F

end Cast

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs)

theorem rowTy_inv_cast : (rowTy Ch sel mu P).inv = rcol_rowSG_eq sel mu hQ ▸ (rowTyG Ch P).inv := by
  refine levFam_eq_cast (rcol_rowSG_eq sel mu hQ) _ _ fun w hw => ?_
  first
  | (simp only [LevFam.inv, rowTy, LevFam.glue, dif_pos hw]; done)
  | (unfold LevFam.inv rowTy LevFam.glue; rw [dif_pos hw])
  | (simp [LevFam.inv, rowTy, LevFam.glue, hw])

def zOfRow (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) (F : MtildeV W Ch sel mu P) : Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ :=
  zOfRow0 W (rowTyG Ch P).inv σ₀ hM (rowCast W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P) F)

end Main

end Formalism.L2.Col
end
end
