import Mathlib
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParallelSig {D : D7} (V : HSp D) (p q : ℕ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (V.gram.map τ) p q

theorem parallelSig_of_sigOK {D : D7} {V : HSp D} {p q : ℕ} (h : V.SigOK) (hs : ∀ τ, V.sig τ = (p, q)) :
    ParallelSig V p q := fun τ => by
  have := h τ
  rwa [hs τ] at this

example (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Odd (D.sp.W j).rank ∧ (D.R.k + j - 1) + (D.R.m - j) = (D.sp.W j).rank ∧ D.R.m - j < D.R.k + j - 1 ∧
      ParallelSig (D.sp.W j : HSp D) (D.R.k + j - 1) (D.R.m - j) := by
  have hr := D.sp.W_rank j h1 h2
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  unfold Ranks.r at hr
  refine ⟨⟨a + b - 1, by omega⟩, by omega, by omega,
    parallelSig_of_sigOK (D.sp.W_sig j) (D.sp.W_sigval j h1 h2)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

end
