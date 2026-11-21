import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FullIffBijective

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.CoverPinCounterexample

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ}

theorem exists_trivial (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (Tup : Type) :
    ∃ d : DeltaDat Xo c n, d.pd = 1 ∧ d.I = ⊤ ∧ d.l₂ = l ∧ d.cδ = 1 ∧ CovPin Xo c (fun _ : Tup => d) := by
  obtain ⟨d, h1, h2, hl, -, -, h3, hlev, hs⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c hr n 1 ⊤ l Xo c rfl
    ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm (top_sup_eq _)
  exact ⟨d, h1, h2, hl, h3, fun _ => ⟨hlev, by rw [hl]; exact hA, hs⟩⟩



set_option synthInstance.maxHeartbeats 200000 in

theorem covPin_smul {Tup : Type} (dδ : Tup → DeltaDat Xo c n) (h : CovPin Xo c dδ) (a : ∀ t, (dδ t).c₂.F)
    (ha : ∀ t, a t ≠ 0) : CovPin Xo c (fun t => { dδ t with cδ := a t • (dδ t).cδ }) :=
  fun t => ⟨GlobalTheory.LevelCoverDatum.isLev_smul (dδ t) (h t).1 (a t) (ha t), (h t).2.1, (h t).2.2⟩

variable {Xo c}

theorem pd_mem (d : DeltaDat Xo c n) (h : d.IsLev) {P : Ideal (𝓞 E)} (hI : d.I ≤ P) : (d.pd : 𝓞 E) ∈ P := by
  have h1 := GlobalTheory.LevelCoverDatum.half_mul_conj d h
  have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I := h1 ▸ Ideal.mul_le_left
  exact hI (this (Ideal.subset_span rfl))

omit [IsCMField E] in
theorem not_both {a b : ℕ} (hab : Nat.Coprime a b) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) (ha : (a : 𝓞 E) ∈ P) :
    (b : 𝓞 E) ∉ P := by
  intro hb
  obtain ⟨u, v, huv⟩ : IsCoprime (a : 𝓞 E) (b : 𝓞 E) := Nat.Coprime.cast hab
  exact hP ((Ideal.eq_top_iff_one _).2 (huv ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))



theorem prime_under (d : DeltaDat Xo c n) (h : d.IsLev) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) (hI : d.I ≤ P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) : q ∣ d.pd ∧ zeta q ∈ c.F ∧ q - 1 ≤ Module.finrank ℚ c.F := by
  have h1 : q ∣ d.pd := by
    by_contra hne
    exact not_both ((Nat.Prime.coprime_iff_not_dvd hq).2 hne) hP hqP (pd_mem d h hI)
  have h2 : zeta q ∈ c.F := GlobalTheory.CoeffRingTest.zeta_mem_of_dvd (GlobalTheory.LevelCoverDatum.pd_pos d h).ne' h1
    (GlobalTheory.CoeffRingTest.zeta_pd_mem d h)
  refine ⟨h1, h2, ?_⟩
  have := c.fin
  have hle : (minpoly ℚ (⟨_, h2⟩ : c.F)).natDegree ≤ Module.finrank ℚ c.F := minpoly.natDegree_le _
  have he : minpoly ℚ (zeta q) = minpoly ℚ (⟨_, h2⟩ : c.F) :=
    minpoly.algHom_eq c.F.val Subtype.val_injective (⟨_, h2⟩ : c.F)
  rwa [← he, ← Polynomial.cyclotomic_eq_minpoly_rat (GlobalTheory.CoeffRingTest.zeta_prim hq.ne_zero) hq.pos,
    Polynomial.natDegree_cyclotomic, Nat.totient_prime hq] at hle

end Gen

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}


end Row

end GlobalTheory.Survey.CoverPinCounterexample
