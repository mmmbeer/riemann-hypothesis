import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF)

theorem N_eq : d.O.N = GlobalTheory.ChiGrid.bigN D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  have : D.R.r + 6 = D.R.k + D.R.m + 5 := by unfold Ranks.r; omega
  rw [this]

theorem nr_eq : d.O.nr = GlobalTheory.ChiGrid.nRk D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m = D.R.r + 1
  unfold Ranks.r; omega

theorem s_eq : d.O.s = GlobalTheory.ChiGrid.sLen D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m + 5 = D.R.r + 6
  unfold Ranks.r; omega

theorem PPF_eq (C b : ℝ) : d.O.PPF C b = GlobalTheory.ChiGrid.sizeP D C b := by
  unfold FunData.PPF GlobalTheory.ChiGrid.sizeP
  rw [nr_eq]; rfl

theorem Lc_eq : d.O.Lc = GlobalTheory.ChiGrid.cloudLen D := by
  classical
  have h : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  unfold FunData.Lc GlobalTheory.ChiGrid.cloudLen
  refine le_antisymm (Finset.sup_le fun τ hτ => ?_) (Finset.sup_le fun τ _ => ?_)
  · have hτ' : τ < Fintype.card D.what₂.Tau := h ▸ Finset.mem_range.1 hτ
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ =>
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat)
      (Finset.mem_univ ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, hτ'⟩)))
    show (cloud D τ 2 - cloud D τ D.R.k).toNat = _
    simp only [cloud, dif_pos hτ']
  · refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ => (d.O.cl τ 2 - d.O.cl τ d.O.k).toNat)
      (Finset.mem_range.2 (show ((Fintype.equivFin D.what₂.Tau τ : Fin _) : ℕ) < D.R.f from h ▸ (Fintype.equivFin D.what₂.Tau τ).2)))
    show _ = (cloud D _ 2 - cloud D _ D.R.k).toNat
    simp only [cloud, dif_pos (Fintype.equivFin D.what₂.Tau τ).2, Fin.eta, Equiv.symm_apply_apply]

theorem ga_eq (C : ℝ) : d.O.ga C = GlobalTheory.ChiGrid.gap D C := by
  unfold FunData.ga GlobalTheory.ChiGrid.gap
  rw [N_eq, nr_eq, s_eq, Lc_eq d]; rfl

theorem ee_eq (h : Ideal.absNorm d.G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    d.O.ee CF p.Z.b v = d.G.pl.depth ⟨1, CF, p.Z.b⟩ v := by
  unfold FunData.ee GlobalTheory.ChiGrid.Places.depth GlobalTheory.ChiGrid.depth0
  rw [PPF_eq]
  have e : d.O.qq d.O.sv0 = GlobalTheory.ChiGrid.q0 D := h
  rw [e]
  by_cases hv : v = d.G.pl.v0
  · rw [if_pos hv]; exact if_pos hv
  · rw [if_neg hv]; exact if_neg hv

end GlobalTheory.BigTop.Fun.Model

namespace GlobalTheory.BigTop.Fun.FieldProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pow_le_finrank {K : Type} [Field K] [NumberField K] {q e : ℕ} (hq : q.Prime) {z : K}
    (hz : IsPrimitiveRoot z (q ^ (e + 1))) : q ^ e ≤ Module.finrank ℚ K := by
  have h0 : 0 < q ^ (e+1) := pow_pos hq.pos _
  have h1 := (IsPrimitiveRoot.lcm_totient_le_finrank hz hz (by
    rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat h0) : _ ≤ Module.finrank ℚ K)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hq] at h1
  have : 1 ≤ q - 1 := by have := hq.two_le; omega
  nlinarith [pow_pos hq.pos e]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


end GlobalTheory.BigTop.Fun.FieldProbe

end
