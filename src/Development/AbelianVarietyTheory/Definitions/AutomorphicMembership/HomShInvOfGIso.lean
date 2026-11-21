import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Check

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem nrm_nonneg (ct : At S κ p) {Z : ct.Mdl} (F : ct.Sh Z) (f : ct.Sec F) (y : ct.Pt Z) : 0 ≤ ct.nrm F f y := by
  refine Real.sSup_nonneg ?_
  rintro r ⟨U, -, h, k, g, lam, -, rfl⟩
  positivity

theorem mult_tau (t : D.what₂.Tau) : S.Dw.mult (DV.tauEmb D t) = j := by
  simp [Datum.mult, A.cm t, S.p_eq]

def zeroSh (ct : At S κ p) (Z : ct.Mdl) : ct.Sh Z := ⟨0, 0, 0, 0, 𝟙 _⟩



theorem tau_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conj_not_cm (A : Amb D) (t : D.what₂.Tau) : conjEmb (DV.tauEmb D t) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
  intro h
  have h1 : starRingEnd ℂ A.H.rt0 = A.H.rt0 := by
    have h0 : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0 := A.cm t
    rw [← h0] at h ⊢
    exact h
  have hd : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  have h2 := congrArg Complex.re A.H.sqrt_neg_disc_sq
  have h3 : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  simp [pow_two, h3] at h2
  nlinarith [sq_nonneg A.H.rt0.re]

theorem tau_ne_conj (A : Amb D) (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := fun h =>
  conj_not_cm A t' (h ▸ A.cm t)

theorem mult_conj (t : D.what₂.Tau) : S.Dw.mult (conjEmb (DV.tauEmb D t)) + j = N := by
  have := S.p_eq
  have := S.rank_eq
  rw [Datum.mult, if_neg (conj_not_cm A t)]
  omega


theorem expo_conj (ct : At S κ p) (l : PsiT D → ℕ → ℤ) (t : D.what₂.Tau)
    (i : Fin (S.Dw.mult (conjEmb (DV.tauEmb D t)))) :
    ct.expo l (conjEmb (DV.tauEmb D t)) i = -l (D.eTau t) (N - (i : ℕ)) := by
  classical
  unfold At.expo
  rw [Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tau_ne_conj A t t).symm, zero_add]
  · intro s _ hs
    rw [if_neg (tau_ne_conj A s t).symm, if_neg, add_zero]
    intro h
    refine hs (tau_inj (RingHom.ext fun x => ?_)).symm
    have := congrArg (fun φ : D.host.E →+* ℂ => starRingEnd ℂ (φ x)) h
    simpa [conjEmb] using this
  · intro h; exact absurd (Finset.mem_univ t) h








theorem blowUp_i (ct : At S κ p) (Z : ct.Mdl) (J : ct.Idl Z) : (ct.blowUp Z J).i = Z.i := by
  unfold At.blowUp GlobalTheory.LocM.blowUp
  split_ifs with h
  · exact h.choose_spec.1
  · rfl



end GlobalTheory.LocM.Check
