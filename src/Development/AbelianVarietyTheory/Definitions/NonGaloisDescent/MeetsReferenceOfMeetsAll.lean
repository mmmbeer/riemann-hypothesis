import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivSupOfIsotypicPartsInternalDirectSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTripleForOfOff

noncomputable section

namespace GlobalTheory.TwInputs.EigModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.Triple (heckeVal satake muBase)

variable {D : D7}


variable {cf : CharFrame D} {Rw : RowSide D} {Sb : Finset (PlE D.host)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}




theorem sig_all_of (hN : NoFormsOff D) (hM : MeetsAll D) (hC : CommAll D)
    (hall : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b ev, GlobalTheory.EigTie.IsEigSys D.nexp i j b ev →
      ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, HkIdx i k P → GlobalTheory.EigTie.sigEv s k P = ev k P) :
    D.nexp.sig_all := by
  intro i j b x ev hx he hk
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · let W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
      Eigsp D.nexp i j b ev ⊓ LinearMap.ker (eG D.nexp i j b - LinearMap.id)
    have mW : ∀ y, y ∈ W ↔ (∀ k P, HkIdx i k P → D.nexp.hkF i j b k P y = ev k P • y) ∧ eG D.nexp i j b y = y := by
      intro y
      simp only [W, Eigsp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hxW : x ∈ W := (mW x).2 ⟨fun k P h => hk k P h.1 h.2.1 h.2.2.1 h.2.2.2, he⟩
    have hst : GStable D.nexp i j b W := by
      intro g y hy
      obtain ⟨a, c⟩ := (mW y).1 hy
      refine (mW _).2 ⟨fun k P h => by rw [hC i j hj b k P h, a k P h, map_smul], ?_⟩
      have e := congrArg (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
        (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)))
        (D.nexp.eAlg_central i b (MonoidAlgebra.of _ _ g))
      rw [map_mul, map_mul, MonoidAlgebra.lift_of] at e
      have e2 := LinearMap.congr_fun e y
      change eG D.nexp i j b (D.nexp.actG i j b g y) = D.nexp.actG i j b g (eG D.nexp i j b y) at e2
      rw [e2, c]
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1
      (hM i j b W ((Submodule.ne_bot_iff _).2 ⟨x, hxW, hx⟩) hst fun y hy => ((mW y).1 hy).2)
    obtain ⟨a, c⟩ := (mW y).1 hy1
    obtain ⟨s, e1, e2, e3⟩ := hall i j hj b ev ⟨y, ⟨y, hy2, c⟩, hy0, a⟩
    exact ⟨s, e1, e2, fun k P p q r t => e3 k P ⟨p, q, r, t⟩⟩
  · exact absurd ((hN i j hj b).elim x 0) hx

section Laws

open GlobalTheory.SupLaw.Model

variable (D) (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)



theorem commAll (t) : CommAll (GlobalTheory.SupLaw.Model.rec D (scal D t) s) := fun i j _ b k P _ g x =>
  ((transl D i j g).map_smul (t i k) x).symm




end Laws

end GlobalTheory.TwInputs.EigModel

end
