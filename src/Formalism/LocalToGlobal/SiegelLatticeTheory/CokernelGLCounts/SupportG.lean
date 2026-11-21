import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist

noncomputable section

namespace Formalism.L2.SG.SupportG

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract




end Abstract

variable {D : Formalism.BasicNotions.D7}

def normG (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : ℚ := |Algebra.norm ℚ (Gpt T T' w)|

def SupportLoc (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (p : PlF D), Agree δ M p →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)), kind w = kind w' → KtopP M δ T T' p w w' ≠ 0 →
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) = (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
    (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))

def SupportLemma (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)),
    (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite →
    KtopG M δ T T' w w' ≠ 0 → normG T T' w = normG T T' w'

def SupportVec (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) (κ : Option D.host.E)
    (th : ∀ p, Option ((M p).Cls D.R.rS)),
    (Function.mulSupport fun p => BBtop M δ T T' p w (th p)).Finite →
    (Function.mulSupport fun p => BBtop M δ T T' p w' (th p)).Finite →
    BBG M δ T T' w κ th ≠ 0 → BBG M δ T T' w' κ th ≠ 0 → normG T T' w = normG T T' w'

theorem n0_eq_of_normG_eq {T T' : ℕ} {w w' : Point D.host.E (D.R.rS + 1)} (h : normG T T' w = normG T T' w') (c : ℝ) :
    n0 c T T' w = n0 c T T' w' := by
  have e : |Algebra.norm ℚ (Gpt T T' w / ((Lat.gS D : D.host.E) ^ D.R.m))| =
      |Algebra.norm ℚ (Gpt T T' w' / ((Lat.gS D : D.host.E) ^ D.R.m))| := by
    unfold normG at h
    rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_mul, abs_mul, abs_mul, h]
  unfold n0
  rw [← Rat.cast_abs, ← Rat.cast_abs, e]


def NormProd (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ x : D.host.E, x ≠ 0 →
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹

theorem norm_conjF (x : D.host.E) : Algebra.norm ℚ (D.conjF x) = Algebra.norm ℚ x := by
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofBijective (D.conjF.restrictScalars ℚ) (AlgHom.bijective _)) x

theorem absNorm_eq_of_prod (hN : NormProd D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {x y : D.host.E} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : ∀ p, (M p).modK ((D.s.atP p).ιE x) = (M p).modK ((D.s.atP p).ιE y)) :
    |Algebra.norm ℚ x| = |Algebra.norm ℚ y| := by
  have e : (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹ = (((|Algebra.norm ℚ y| : ℚ)) : ℝ)⁻¹ := by
    rw [← hN δ M hA x hx, ← hN δ M hA y hy]
    exact finprod_congr h
  exact_mod_cast inv_injective e



def PartnerSum {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') : Prop :=
  ∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 →
    HasSum (fun P : {P : D.s.Pair u u' // Formalism.MainNotions.S.scalarP D.s P ∧ D.s.pfst P = γ ∧ D.s.ptOf (D.s.psnd P) = w'} =>
        star (D.s.cTerm (D.s.psnd P.1)))
      (star (BBG M δ (D.mem u).A.T (D.mem u').A.T w' (kind (D.s.ptOf γ)) (thCls X γ)))

def SupportUnderDensityBound (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    {Y : TermTie D} (X : ∀ u u' : D.what₂.Word, TermLoc D Y δ M u u') (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  (∀ p, Agree δ M p) →
  ∀ u u' : D.what₂.Word, (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
  Formalism.MainNotions.LocalBesselAndTopKernel.GLOB.CNT (X u u') (cN u u') → PartnerSum (X u u') →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ Dsup : ℝ, 0 ≤ Dsup →
    (∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
      densT (X u u') ϖ γ ≤ Dsup) →
    ∀ (ι : Type) [Fintype ι] (w : ι → Point D.host.E (D.R.rS + 1)),
      (∀ x, Gpt (D.mem u).A.T (D.mem u').A.T (w x) ≠ 0) →
      ((Dsup : ℂ) • (Matrix.of fun x y => KtopG M δ (D.mem u).A.T (D.mem u').A.T (w x) (w y)) -
        Matrix.of fun x y => Formalism.MainNotions.S.Kgs D.s u u' (w x) (w y) /
          ((Real.sqrt (n0 (cN u u') (D.mem u).A.T (D.mem u').A.T (w x) *
            n0 (cN u u') (D.mem u).A.T (D.mem u').A.T (w y)) : ℝ) : ℂ)).PosSemidef

end Formalism.L2.SG.SupportG
