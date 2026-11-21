import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX.Check

variable {D : D7}

theorem one_le_Lg (L : SizeData₂ D) : 1 ≤ TwistedPlaces.large₂ L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le


theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (le_trans zero_le_one (one_le_Lg L))

theorem sizes (D : D7) : (1 : ℝ) ≤ D.R.t ∧ (1 : ℝ) ≤ D.R.n ∧ (1 : ℝ) ≤ D.R.nV := by
  have h := D.R.three_m_lt_t
  refine ⟨by exact_mod_cast (by omega : 1 ≤ D.R.t), ?_, ?_⟩
  · exact_mod_cast (D.R.ord_pos : 0 < D.R.n)
  · have : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
    exact_mod_cast this

variable {L : SizeData₂ D} {HW : HWOf D.loc} {R : KillingConditions.RowK} {X : KillingConditions.HubData D}



theorem not_inert {l : ℕ} (h1 : TwistedPlaces.SplitK D l) : ¬ TwistedPlaces.InertK D l := by
  intro h2
  unfold TwistedPlaces.SplitK at h1
  unfold TwistedPlaces.InertK at h2
  rw [h1] at h2
  rcases h2 with h2 | h2 <;> cases h2

theorem decl (h : Canon L HW R X) (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D)
    (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i))
    (hex : ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc hJ.choose) : EmbeddingTypes.hypDecl i (X.dc i) hJ.choose := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  have hsp : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
    refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have he : epJ D = hJ.choose := epJ_eq hJ
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) :=
    ⟨hsp, by rw [he]; exact hex⟩
  rw [h.dc i (not_inert hs), dcOf, dif_pos hc, ← he]
  exact hc.2.choose_spec


theorem window (L : SizeData₂ D) (hJ : AdmissibleParameterJ.JumpAbsoluteBound L) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (up : Bool)
    (a : ℤ) (ha : (a : ℚ) ∈ AdmissibleParameterJ.JJ D up j ρ) :
    (-(⌊2 * L.sc.b⌋₊ : ℤ) ≤ a ∧ a + 1 ≤ (⌊2 * L.sc.b⌋₊ : ℤ)) ∧ D.R.t ≤ ⌊2 * L.sc.b⌋₊ := by
  obtain ⟨k1, -, -, k4⟩ := hJ
  have k := abs_le.1 (k1 j h1 h2 ρ up _ ha)
  have ht : (3 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    have := D.R.two_le_m
    exact_mod_cast (by omega : 3 ≤ D.R.t)
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  unfold AdmissibleParameterJ.hJ at k4
  unfold AdmissibleParameterJ.c0 at k
  push_cast at k
  have hc : ((⌊2 * L.sc.b⌋₊ : ℕ) : ℤ) = ⌊2 * L.sc.b⌋ := Int.natCast_floor_eq_floor (by linarith)
  refine ⟨⟨?_, ?_⟩, Nat.le_floor (by linarith)⟩
  · rw [hc, neg_le, Int.le_floor]; push_cast; linarith [k.1]
  · rw [hc, Int.le_floor]; push_cast; linarith [k.2]

theorem exists_canon (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (I : TwIn D) (exc : Finset ℕ)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (hr : ∀ i, ∃ r, GoodR D.nd i r) :
    ∃ X, Canon L HW R X ∧ X.I = I ∧ X.exc = exc := by
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.PtFam.exists_pair hC hr
  exact ⟨_, canon_ourX L HW R r ρ (fun _ _ => 0) exc I h, rfl, rfl⟩


end GlobalTheory.HubX.Check

end
