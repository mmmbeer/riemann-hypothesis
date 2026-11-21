import Formalism.LocalToGlobal.UnitaryNorms.CharRat
import Formalism.LocalToGlobal.UnitaryNorms.RealPl

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace HChar

variable {L : Type} [Field L] [NumberField L]

theorem inf_eq_one_of_order [IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) :
    χ.inf k = 1 := by

  have hpow : ∀ (w : InfinitePlace L) (u : (w.Completion)ˣ), ∃ y : (w.Completion)ˣ, y ^ n = u := by
    intro w u
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hn
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact u.ne_zero (e.injective (by rw [map_zero]; exact hz.symm))
    refine ⟨Units.mk0 (e.symm z) (by simpa using hz0), Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, RingEquiv.symm_apply_apply]
  have hχn : ∀ x, ((χ : Ideles L →* ℂˣ) x) ^ n = 1 := by
    intro x
    have h' := congrArg (fun ψ : HChar L => (ψ : Ideles L →* ℂˣ) x) (show χ ^ n = 1 from h)
    first
      | simpa using h'
      | exact h'
  show (χ : Ideles L →* ℂˣ) (infDiag k) = 1
  simp only [infDiag, MonoidHom.finset_prod_apply, map_prod, MonoidHom.comp_apply]
  apply Finset.prod_eq_one
  intro w _
  obtain ⟨y, hy⟩ := hpow w (atInf w k)
  rw [← hy, map_pow, map_pow, hχn]

end HChar

section Frame

variable {D : D7} (C : CharFrame D)

end Frame

section Tup

variable {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

theorem TupTied.xi_unitary (μ : D.what₂.Tup) : (Tp.xi μ).IsUnitary := by
  obtain ⟨n, hn, h⟩ := Tp.xi_fin μ
  intro x
  have h' := congrArg (fun ψ : HChar D.host.E => (ψ : Ideles D.host.E →* ℂˣ) x) (show Tp.xi μ ^ n = 1 from h)
  have e : ((Tp.xi μ : Ideles D.host.E →* ℂˣ) x) ^ n = 1 := by
    first
      | simpa using h'
      | exact h'
  have e2 : ‖(((Tp.xi μ : Ideles D.host.E →* ℂˣ) x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp e2

theorem TupTied.tup_unitary (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).IsUnitary := fun x => by
  show ‖((((C.mu0 j).1 x * (Tp.xi μ).1 x : ℂˣ)) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, (C.isMu0 j).unitary x, Tp.xi_unitary μ x, one_mul]

end Tup

theorem mul_cc_not_mem_Psi_of_mem_Psi {R : Ranks} {g : R.GG} (hg : g ∈ R.Psi) : g * R.cc ∉ R.Psi := by
  intro h
  have h1 : R.chD g = 1 := MonoidHom.mem_ker.mp hg
  have h2 : R.chD (g * R.cc) = 1 := MonoidHom.mem_ker.mp h
  rw [map_mul, h1, one_mul] at h2
  simp only [Formalism.HC.Frame.chD, Formalism.HC.Frame.cc, MonoidHom.comp_apply, MonoidHom.coe_fst,
    MonoidHom.coe_snd] at h2
  first
    | (simp [c0] at h2; done)
    | (simp only [c0] at h2; revert h2; decide)
    | (revert h2; unfold c0; decide)
    | (simp [c0] at h2; exact absurd h2 (by decide))

theorem cc_mul_cc (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 :=
  Prod.ext
    (by
      first
        | decide
        | exact Prod.ext (Int.units_mul_self _) (Int.units_mul_self _)
        | (simp [Formalism.HC.Frame.cc]; done))
    (by
      show (1 : φ.MA) * 1 = 1
      exact mul_one 1)

section TupAlg

variable {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

end TupAlg

section TupCsd

variable {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

end TupCsd

end Formalism.L2.Host
