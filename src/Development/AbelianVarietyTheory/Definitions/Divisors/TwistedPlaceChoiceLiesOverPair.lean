import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharGal
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpaceOfSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatLatSmulLeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGridModel

variable {D : D7}

def IsSum (A B : LSp D) (c : ℕ) (ε : D.host.E) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Prop :=
  ∃ d : HermitianOrthogonalExtensionData A.sp B.sp c ε, B.lat = d.lat A.lat 𝔟

theorem exists_sum (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ) (neg : Bool)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h0 : ∀ p, 𝔟 p ≠ 0)
    (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) {ν' q' : ℕ} (h1 : ν + c = ν')
    (h2 : q + (if neg then (c + 1) / 2 else c / 2) = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (if neg then -1 else 1) 𝔟 := by
  obtain ⟨B, ⟨d⟩, hB, hs⟩ := GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature D X.sp (ν - q) q c neg hX.sigOK hX.sig
  refine ⟨⟨B, d.lat X.lat 𝔟⟩, ⟨?_, hB, fun τ => ?_, ?_⟩, d, rfl⟩
  · have := d.rank
    rw [hX.rank] at this
    exact this.symm.trans h1
  · rw [hs τ]
    cases neg <;> simp only [Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h2 ⊢ <;> omega
  · exact GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D X.sp B c _ d X.lat 𝔟 (by cases neg <;> simp) hX.sd h0 hd

theorem exists_line (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) :
    ∃ Y : LSp D, Y.IsV (ν + 1) q ∧ IsSum X Y 1 1 fun _ => 1 := by
  refine exists_sum X hX hq 1 false (fun _ => 1) (fun _ => one_ne_zero) (fun _ x => ?_) rfl rfl
  rw [inv_one, FractionalIdeal.mem_one_iff, FractionalIdeal.mem_one_iff]
  have key : ∀ y : D.host.E, (∃ a : 𝓞 D.host.E, algebraMap _ _ a = y) → ∃ a : 𝓞 D.host.E, algebraMap _ _ a = star y := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, Examples₂.star_isIntegral _ a.2⟩, rfl⟩
  exact ⟨key x, fun h => by simpa using key _ h⟩

theorem exists_stair (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ)
    {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h0 : 𝔞 ≠ 0) (hc : ∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) {ν' q' : ℕ}
    (h1 : ν + c = ν') (h2 : q + (c + 1) / 2 = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (-1) (stairId 𝔞 𝔞' c) :=
  exists_sum X hX hq c true _ (fun p => (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D 𝔞 𝔞' h0 hc c p).1)
    (fun p => (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D 𝔞 𝔞' h0 hc c p).2) h1 h2

theorem nonempty_vertices : ∀ (D : D7) (T : Type) (L : LevCh D T) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
    IsSelfDualC (Yc D 0) (L.ΛY 0) → 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → Nonempty (Vertices L 𝔞 𝔞') := by
  intro D T L 𝔞 𝔞' hY h0 hc
  classical
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  obtain ⟨μ, hμ⟩ := D.R.m_even
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = (D.R.r + 5) + 1 := rfl
  have hVr : ∀ i j, D.R.m ≤ rankV D i j := fun i j => by unfold rankV; omega
  have hPr : ∀ i, D.R.m ≤ rankP D i := fun i => by unfold rankP nRk; omega
  obtain ⟨hA0, hAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1

  have hstd : ∀ ν q : ℕ, ∃ X : LSp D, q ≤ ν → X.IsV ν q := fun ν q => by
    by_cases h : q ≤ ν
    · exact (GlobalTheory.ChiGrid.exists_isV D ν q h).imp fun _ hX _ => hX
    · exact ⟨⟨Yc D 0, L.ΛY 0⟩, fun h' => absurd h' h⟩
  choose S hS using hstd

  have hY0 : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV D.R.r (D.R.m / 2) := by
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, hY⟩
    · exact (D.sp.Y_rank 0 (Nat.zero_le _)).trans (by simp [Ranks.rankY])
    · refine (D.sp.baseSpace_signature_eq τ).trans ?_
      simp only [Ranks.sigY0, Ranks.rS, Prod.mk.injEq]
      omega
  obtain ⟨P₀, hP₀, d0, hd0⟩ := exists_line _ hY0 (by omega)
  let P : ℕ → LSp D := xOf P₀ fun i => S (rankP D i) ((D.R.m - i + 1) / 2)
  have hP : ∀ i, i ≤ D.R.m → (P i).IsV (rankP D i) ((D.R.m - i + 1) / 2) := by
    rintro (_ | i) hi
    · have e1 : rankP D 0 = D.R.r + 1 := by simp [rankP, nRk]
      have e2 : (D.R.m - 0 + 1) / 2 = D.R.m / 2 := by omega
      rw [e1, e2]; exact hP₀
    · exact hS _ _ (by have := hPr (i + 1); omega)

  have hVm : (S (rankV D D.R.m D.R.m) 0).IsV (rankV D D.R.m D.R.m) 0 := hS _ _ (Nat.zero_le _)
  obtain ⟨Xm, hXm, htop⟩ := exists_line _ hVm (Nat.zero_le _)
  let Xs : ℕ → LSp D := fun j => if j = D.R.m then Xm else S (rankX D j) 0
  have hX : ∀ j, (Xs j).IsV (rankX D j) 0 := fun j => by
    by_cases h : j = D.R.m
    · have e1 : rankX D j = rankV D D.R.m D.R.m + 1 := by
        simp only [h, rankX, rankP, rankV, nRk, hs, Nat.add_sub_cancel]; ring
      simp only [Xs, if_pos h]
      rw [e1]; exact hXm
    · simp only [Xs, if_neg h]
      exact hS _ _ (Nat.zero_le _)

  have hcol : ∀ i, ∃ Y : LSp D, 1 ≤ i → i ≤ D.R.m →
      Y.IsV (rankV D i 0) ((D.R.m - 0) / 2) ∧ IsSum (P i) Y (i - 1) (-1) (stairId 𝔞 𝔞' (i - 1)) := fun i => by
    by_cases h : 1 ≤ i ∧ i ≤ D.R.m
    · refine (exists_stair (P i) (hP i h.2) (by have := hPr i; omega) (i - 1) h0 hc ?_ (by omega)).imp fun _ hZ _ _ => hZ
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [rankP, rankV, nRk, hs, Nat.add_sub_cancel]; ring
    · exact ⟨P₀, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose C hC using hcol

  have hrow : ∀ j, ∃ Y : LSp D, j < D.R.m →
      Y.IsV (rankV D D.R.m j) ((D.R.m - j) / 2) ∧
        IsSum (Xs j) Y (D.R.m - 1 - j) (-1) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := fun j => by
    by_cases h : j < D.R.m
    · refine (exists_stair (Xs j) (hX j) (Nat.zero_le _) (D.R.m - 1 - j) hA0 hAc ?_ (by omega)).imp fun _ hZ _ => hZ
      simp only [rankX, rankP, rankV, nRk, hs, Nat.add_sub_cancel, mul_add, mul_one]; omega
    · exact ⟨P₀, fun h1 => absurd h1 h⟩
  choose R hR using hrow
  let Vs : ℕ → ℕ → LSp D := fun i j =>
    if j = 0 then C i else if i = D.R.m ∧ j < D.R.m then R j else S (rankV D i j) ((D.R.m - j) / 2)
  have hv : ∀ i j, 1 ≤ i → vtxOf L Vs i j = Vs i j := by
    rintro (_ | i) j hi
    · omega
    · rfl
  have hx : ∀ X₀ j, 1 ≤ j → xOf X₀ Xs j = Xs j := by
    rintro X₀ (_ | j) hj
    · omega
    · rfl
  have hV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → (Vs i j).IsV (rankV D i j) ((D.R.m - j) / 2) := by
    intro i j h1 h2 h3
    simp only [Vs]
    split_ifs with ha hb
    · subst ha; exact (hC i h1 h2).1
    · rw [hb.1]; exact (hR j hb.2).1
    · exact hS _ _ (by have := hVr i j; omega)
  have h1 : ∀ i, 1 ≤ i → i ≤ D.R.m → IsSum (P i) (vtxOf L Vs i 0) (i - 1) (-1) (stairId 𝔞 𝔞' (i - 1)) := by
    intro i h h'
    rw [hv i 0 h]
    exact (hC i h h').2
  have h2 : ∀ j, j + 1 < D.R.m → IsSum (Xs (j + 1)) (vtxOf L Vs D.R.m (j + 1)) (D.R.m - 1 - (j + 1)) (-1)
      (stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) := by
    intro j h
    have e : Vs D.R.m (j + 1) = R (j + 1) := by
      simp only [Vs]
      rw [if_neg (Nat.succ_ne_zero j), if_pos ⟨trivial, h⟩]
    rw [hv _ _ (by omega), e]
    exact (hR _ h).2
  have h3 : IsSum (vtxOf L Vs D.R.m D.R.m) (xOf (P D.R.m) Xs D.R.m) 1 1 fun _ => 1 := by
    have e : Vs D.R.m D.R.m = S (rankV D D.R.m D.R.m) 0 := by
      simp only [Vs]
      rw [if_neg (by omega), if_neg (by omega), Nat.sub_self]
    have e' : Xs D.R.m = Xm := if_pos rfl
    rw [hv _ _ (by omega), hx _ _ (by omega), e, e']
    exact htop
  choose d1 hd1 using h1
  choose d2 hd2 using h2
  obtain ⟨d3, hd3⟩ := h3
  exact ⟨⟨Vs, P, Xs, hV, hP, fun j _ _ => hX j, d0, hd0, d1, hd1, d2, hd2, d3, hd3⟩⟩

theorem exists_gridData {T : Type} (L : LevCh D T) (sc : Consts) (P : Places L) (h0 : P.v0 ∉ S1 D)
    (hY : IsSelfDualC (Yc D 0) (L.ΛY 0)) : ∃ G : GridData L sc, G.pl = P := by
  obtain ⟨X⟩ := GlobalTheory.GridChars.nonempty_chars D T L P sc.cGap h0
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc
  obtain ⟨V⟩ := nonempty_vertices D T L _ _ hY h1 h2
  exact ⟨⟨P, X, V⟩, rfl⟩

theorem nonempty_gridData_iff {T : Type} (L : LevCh D T) (μ0 : T) (hL : L.Is μ0) (sc : Consts) :
    Nonempty (GridData L sc) ↔ ∃ P : Places L, P.v0 ∉ S1 D := by
  refine ⟨fun ⟨G⟩ => ⟨G.pl, G.ch.basePlace_not_mem_chiGridBadPlaces⟩, fun ⟨P, h⟩ => ?_⟩
  obtain ⟨G, -⟩ := exists_gridData L sc P h (GlobalTheory.ChiGrid.colY_isV D T L μ0 hL 0 (Nat.zero_le _)).sd
  exact ⟨G⟩




theorem nonempty_gridData {T : Type} (L : LevCh D T) (μ0 : T) (hL : L.Is μ0) (sc : Consts)
    (hg : ∀ k, D.host.g k % LevelStarExponents.condE D = 1) (h1 : D.host.pde % LevelStarExponents.condE D = 1) (h2 : D.host.pde' % LevelStarExponents.condE D = 1)
    (h3 : ∀ k, q0 D ≠ D.host.g k) (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    Nonempty (GridData L sc) :=
  (nonempty_gridData_iff L μ0 hL sc).2 (GlobalTheory.GridPlaces.exists_places D T L μ0 hL hg h1 h2 h3 h4)

theorem exists_levCh_gridData (C : Formalism.L2.Host.CharFrame D) (sc : Consts)
    (hg : ∀ k, D.host.g k % LevelStarExponents.condE D = 1) (h1 : D.host.pde % LevelStarExponents.condE D = 1) (h2 : D.host.pde' % LevelStarExponents.condE D = 1)
    (h3 : ∀ k, q0 D ≠ D.host.g k) : ∃ L : LevCh D Unit, L.C = C ∧ L.Is () ∧ Nonempty (GridData L sc) := by
  obtain ⟨L, hC, hL⟩ := GlobalTheory.LevelChoices.exists_levCh_unit D C
  refine ⟨L, hC, hL, nonempty_gridData L () hL sc hg h1 h2 h3 fun t PP hP => ?_⟩
  exact absurd (by rw [hL.xi_base]; intro x _; rfl) ((hL.Q_ram () PP).2 (Or.inl hP))



open GlobalTheory.SignedHC in

theorem par_core {T : Type} (C : ℝ) (τ : D.what₂.Tau) {i : ℕ} (h : (Pair.core i : Pair T).InRange D.R.m) :
    Node.par D C (Pair.core i : Pair T).big τ =
      lift (Pair.core i : Pair T).ori (Pair.centre D C (Pair.core i : Pair T) τ) (Pair.len D (Pair.core i : Pair T))
        (Node.par D C (Pair.core i : Pair T).small τ) := by
  change (num D C τ).parPi (i + 1) = liftMinus ((num D C τ).cen ((num D C τ).m - i)) ((num D C τ).s - 1) ((num D C τ).parPi i)
  have hi : i + 1 ≤ (num D C τ).m := h
  have hm := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hs2 : 2 ≤ (num D C τ).s := by change 2 ≤ D.R.r + 6; omega
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  generalize num D C τ = G at *
  have hc := abs_le.1 (hm (G.m - i) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
  rw [G.mid_eq (by omega)] at hc
  have hga : (3 : ℚ) ≤ G.ga := by exact_mod_cast (by omega : 3 ≤ G.ga)
  have hle : ∀ {a b : ℕ}, a ≤ b → G.a b ≤ G.a a := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := G) h]
  have up : ∀ l, l < G.m - i → (G.cen (G.m - i) : ℚ) < G.a l := fun l hl => by linarith [a_add_le (G := G) hl, hc.2]
  have dn : ∀ l, G.m - i ≤ l → G.a l < (G.cen (G.m - i) : ℚ) := fun l hl => by linarith [hle hl, hc.1]
  have cl : ∀ x ∈ G.cloudHalf, x < (G.cen (G.m - i) : ℚ) := fun x hx => (cloudHalf_lt hx).trans (dn _ (by omega))
  have bl : ∀ l, G.m - i + 1 ≤ l → l ≤ G.m → ∀ x ∈ G.blockC' l, x < (G.cen (G.m - i) : ℚ) := fun l h1 h2 x hx => by
    linarith [(blockC'_between hm hs hg (by omega) h2 hx).2, a_add_le (G := G) (show G.m - i < l by omega), dn _ le_rfl]
  have sg1 : ∀ l, G.m - i ≤ l → decide (G.m - (i + 1) ≤ l ∨ Even (G.m - (i + 1) - l)) = decide (G.m - i ≤ l ∨ Even (G.m - i - l)) :=
    fun l hl => by rw [decide_eq_true (Or.inl (by omega)), decide_eq_true (Or.inl hl)]
  have sg2 : ∀ l, l < G.m - i → decide (G.m - (i + 1) ≤ l ∨ Even (G.m - (i + 1) - l)) = !decide (G.m - i ≤ l ∨ Even (G.m - i - l)) :=
    fun l hl => by
      rw [← decide_not, decide_eq_decide, Nat.even_iff, Nat.even_iff]; omega
  ext ⟨x, s⟩
  simp only [mem_liftMinus, GlobalTheory.SignedHC.GridData.mem_parPi, Prod.mk.injEq]
  constructor
  · rintro (⟨l, hl, rfl, rfl⟩ | ⟨hx, rfl⟩ | ⟨l, h1, h2, hx, rfl⟩)
    · rcases lt_or_ge l (G.m - i) with h' | h'
      · exact Or.inr (Or.inl ⟨up l h', Or.inl ⟨l, hl, rfl, by rw [sg2 l h', Bool.not_not]⟩⟩)
      · exact Or.inl ⟨(dn l h').le, Or.inl ⟨l, hl, rfl, sg1 l h'⟩⟩
    · exact Or.inl ⟨(cl x hx).le, Or.inr (Or.inl ⟨hx, rfl⟩)⟩
    · by_cases e : l = G.m - i
      · exact Or.inr (Or.inr ⟨e ▸ hx, rfl⟩)
      · exact Or.inl ⟨(bl l (by omega) h2 x hx).le, Or.inr (Or.inr ⟨l, by omega, h2, hx, rfl⟩)⟩
  · rintro (⟨h0, ⟨l, hl, rfl, rfl⟩ | ⟨hx, rfl⟩ | ⟨l, h1, h2, hx, rfl⟩⟩ | ⟨h0, ⟨l, hl, rfl, hs'⟩ | ⟨hx, -⟩ | ⟨l, h1, h2, hx, -⟩⟩ | ⟨hx, rfl⟩)
    · have : G.m - i ≤ l := by by_contra h'; exact absurd (up l (by omega)) (not_lt.2 h0)
      exact Or.inl ⟨l, hl, rfl, (sg1 l this).symm⟩
    · exact Or.inr (Or.inl ⟨hx, rfl⟩)
    · exact Or.inr (Or.inr ⟨l, by omega, h2, hx, rfl⟩)
    · have : l < G.m - i := by by_contra h'; exact absurd (dn l (by omega)) (not_lt.2 h0.le)
      exact Or.inl ⟨l, hl, rfl, by rw [sg2 l this, ← hs', Bool.not_not]⟩
    · exact absurd (cl x hx) (not_lt.2 h0.le)
    · exact absurd (bl l h1 h2 x hx) (not_lt.2 h0.le)
    · exact Or.inr (Or.inr ⟨G.m - i, by omega, by omega, hx, rfl⟩)

end GlobalTheory.ChiGridModel
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

abbrev Df (p : PtAt ex Csz) : DefSide p.P.A3.fam3.base3 := lv (p.F.fc (p.R.toCx3 p.F).zs) false

abbrev Tup (p : PtAt ex Csz) : Type := p.P.A3.fam3.base3.Tup

abbrev PlL (D : D7) : Type := HeightOneSpectrum (𝓞 D.what₂.LL)

abbrev Sq (D : D7) : Type := Fin D.R.m × Fin D.R.m

abbrev Grid (p : PtAt ex Csz) (CF : ℝ) : Type 1 := GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure FunIn (p : PtAt ex Csz) (CF : ℝ) where

  G : GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩

  W : G.Weil

  ext : W.Over p.R.toRealDat

  n : ℕ

  X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ

  M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)

  V : ∀ t : Tup p, Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL

  rq : Tup p → Sq D → D.what₂.LL

  dl : PlL D → ℝ

  Sd : Finset ℕ

  Se : Finset ℕ

  N0 : Sq D → ℤ → ℕ → ℝ

  zA : Sq D → D.what₂.LL

  zA' : Sq D → D.what₂.LL

  zT : Sq D → ℤ → D.what₂.LL

  zTd : Sq D → Bool → ℤ → D.what₂.LL

  gT : Sq D → ℤ → PlL D → ℤ

  ch : PlL D → Bool

  Bw : ℝ

open Classical in

def cloud (D : D7) (τ i : ℕ) : ℤ :=
  if h : τ < Fintype.card D.what₂.Tau then
    (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)) 0 0 0).v i else 0

def sqRank (D : D7) (ij : Sq D) : ℕ :=
  GlobalTheory.ChiGrid.rankV D ij.1 ((ij.2 : ℕ) + 1) + GlobalTheory.ChiGrid.rankV D ((ij.1 : ℕ) + 1) ij.2

open Classical in

def FunIn.data {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (ze : Tup p → D.what₂.LL) (Tf : Finset (PlL D)) (dF : PlL D → ℤ) :
    FunData D.what₂.LL (Df p) where
  n := d.n
  X' := d.X'
  M := d.M
  vmu t := (ze t)⁻¹ • d.V t
  Tf := Tf
  dF := dF
  m := D.R.m
  rq := d.rq
  dl := d.dl
  Sd := d.Sd
  Se := d.Se
  N0 := d.N0
  zA := d.zA
  zA' := d.zA'
  zT := d.zT
  zTd := d.zTd
  gT := d.gT
  ch := d.ch
  dd := sqRank D
  hd ij := sqRank D ij / 2
  yy ij := D.R.m - 1 - ij.2
  Sq := HeightOneSpectrum (𝓞 D.host.F)
  S0 := d.G.pl.S0
  sv0 := d.G.pl.v0
  cc v := if v = d.G.pl.v0 then 1 else 2
  qq v := Ideal.absNorm v.asIdeal
  f := D.R.f
  k := D.R.k
  tt := D.R.t
  cl := cloud D
  g1 := D.host.g 0
  g2 := D.host.g 1
  pd := D.host.pde
  pd' := D.host.pde'
  dE := discr D.host.E
  Bw := d.Bw

abbrev FunIn.O {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : FunData D.what₂.LL (Df p) := d.data (fun _ => 1) ∅ fun _ => 0

abbrev TieT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ), FunIn p CF → Prop

abbrev PropT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ), FunIn p CF → ℝ → ℝ → Prop

def trivialTieCondition : TieT := fun _ _ _ => True

section Fit

open GlobalTheory.ChiGrid Formalism.L2.Host

variable {T : Type} {Lc : LevCh D T} {sc : Consts}

def lamOf (G : GridData Lc sc) : GlobalTheory.LamTie.LamDat D where
  C := Lc.C
  q0 := q0 D
  w0 := G.pl.w G.pl.v0
  c a g := cen D sc.cGap (D.eTau.symm g) (a.1 + 1)
  chi a := G.ch.chiH (a.1 + 1)

structure FieldHas (G : GridData Lc sc) {K : Type} [Field K] (e : K →+* ℂ) : Prop where

  values : ∀ i, 1 ≤ i → i ≤ D.R.m → (G.ch.chiH i).ValuesIn 0 e

  roots : ∀ v ∈ G.pl.S0, ∃ z : K, IsPrimitiveRoot z (Ideal.absNorm v.asIdeal ^ G.pl.depth sc v)

theorem lambdaGrid_apply (G : GridData Lc sc) (l : ℕ) (j a : Fin D.R.m) :
    (lamOf G).lam0 l j a = Lc.C.mu0 j * Lc.C.delAt l / G.ch.chiH (a.1 + 1) := (div_eq_mul_inv _ _).symm

theorem lamOf_hasInfQ (G : GridData Lc sc) (a : Fin D.R.m) :
    ((lamOf G).chi a).HasInfQ (embPsi D.host) fun g => ((lamOf G).c a g : ℚ) := by
  refine ⟨fun g => 2 * cen D sc.cGap (D.eTau.symm g) (a.1 + 1), fun g => by simp [lamOf], fun k => ?_⟩
  refine (G.ch.inf (a.1 + 1) (by omega) a.2 k).trans (Fintype.prod_equiv D.eTau _ _ fun τ => ?_)
  simp only [Equiv.symm_apply_apply]
  rfl

theorem lamOf_teich (G : GridData Lc sc) : (lamOf G).Teich := fun a w hw x hx =>
  G.ch.wild (a.1 + 1) (by omega) a.2 w hw x (by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hx)

theorem FieldHas.map {G : GridData Lc sc} {K K' : Type} [Field K] [Field K'] {e' : K' →+* ℂ} (j : K →+* K')
    (h : FieldHas G (e'.comp j)) : FieldHas G e' :=
  ⟨fun i h1 h2 v hv => (h.values i h1 h2 v hv).elim fun y hy => ⟨j y, hy⟩,
    fun v hv => (h.roots v hv).elim fun z hz => ⟨j z, hz.map_of_injective j.injective⟩⟩

theorem exists_fieldHas (G : GridData Lc sc) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ FieldHas G M.val.toRingHom := by
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hpos : ∀ v : HeightOneSpectrum (𝓞 D.host.F), 0 < Ideal.absNorm v.asIdeal ^ G.pl.depth sc v := fun v =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have h1 : ∀ a : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      (G.ch.chiH (a.1 + 1)).ValuesIn 0 M.val.toRingHom := fun a => by
    obtain ⟨n, hn, hi⟩ := lamOf_hasInfQ G a
    have := GlobalTheory.T.algebraicHeckeChar_values_in_numberField D.host.F D.host.E c (D.R.Psi) (embPsi D.host) hcm _ n 0 hi fun g => by
      have h3 : (n g : ℚ) = 2 * ((lamOf G).c a g : ℚ) := hn g
      have h2 : n g = 2 * (lamOf G).c a g := by exact_mod_cast h3
      exact ⟨(lamOf G).c a g, by rw [h2]; ring⟩
    rw [Int.cast_zero, zero_div] at this
    exact this
  choose Mc hMc hMc' using h1
  choose Mr hMr hMr' using fun v : G.pl.S0 => GlobalTheory.Mem.FrameVal.exists_roots _ (hpos v)
  refine ⟨(⨆ a, Mc a) ⊔ ⨆ v, Mr v, inferInstance, fun i a b => ?_, fun v hv => ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact GlobalTheory.Mem.FrameVal.valuesIn_mono (hMc' ⟨i, b⟩) ((le_iSup Mc _).trans le_sup_left)
  · have hz := Complex.isPrimitiveRoot_exp _ (hpos v).ne'
    exact ⟨⟨_, ((le_iSup Mr ⟨v, hv⟩).trans le_sup_right) (hMr' ⟨v, hv⟩ _ hz.pow_eq_one)⟩,
      IsPrimitiveRoot.of_map_of_injective (f := IntermediateField.val _) hz Subtype.val_injective⟩

def TwistedPlaceChoiceLiesOverPair (D : D7) (c : NChoice D) : Prop :=
  (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (c.twI w) = D.what₂.places.resChar w ∧
    (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (c.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (c.twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → c.Q w ≠ ∅ → c.twI w = c.twI w'

theorem TwistedPlaceChoiceLiesOverPair.inW1 {D : D7} {c : NChoice D} (h : TwistedPlaceChoiceLiesOverPair D c) {w : D.what₂.places.Pl} (hw : GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w) :
    D.ntw.NonzeroIndexPlace (c.twI w) :=
  (h.1 w hw).2.elim (fun h1 => ⟨w, hw, h1⟩) fun h1 => ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw, h1⟩

structure GridFit (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) : Prop where

  frame : ValLL0 D p.R.C

  field : FieldHas G (embLL0 D)

  setting : TwistedPlaceChoiceLiesOverPair D ex.nch

  cond : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w)

  powers : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
    BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w))

  psi : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp

  list : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)

theorem GridFit.fieldLL {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (h : GridFit p G) : FieldHas G D.what₂.embLL :=
  h.field.map D.LL0.val.toRingHom


end Fit

abbrev FldT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF), G.Weil → Prop

def HasGrid (Fld : FldT) (p : PtAt ex Csz) (CF : ℝ) : Prop :=
  ∃ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat ∧ GridFit p G ∧ Fld p CF G W

def Fitted (Comparison₂ : TieT) : TieT := fun p CF d => GridFit p d.G ∧ Comparison₂ p CF d

def Lf (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → EvPt Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH

def Ex (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  EvPt Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d

def MM (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun _ _ d C _ => LeafMM d.O C

def OneMap (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d _ _ =>
  ∃ ze : Tup p → _, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
    LeafC (p.S false) (d.data ze ∅ fun _ => 0)

def Ker (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun _ _ d _ _ => LeafKer d.O

def FP (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b

def IPa (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ =>
  ∀ vb : Matrix (Fin d.n) (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0)) _,
    vb * (Df p).Pq p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 →
      Formalism.HN.htMap (Pi.basisFun _ (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0))) ((Df p).XQ p.P.A3.fam3.base3.μ0)
        (Pi.basisFun _ (Fin d.n)) d.X' (Matrix.mulVecLin vb) ≤ d.O.bIPa C p.Z.b

def IPb : Prop := Lf trivialTieCondition fun p _ d C _ =>
  ∃ g : InfinitePlace _ → ℝ, (∀ v q, (Df p).Qp p.P.A3.fam3.base3.μ0 q ≠ ⊥ →
      g v ≤ ∑ j, Real.log ((p.S false).lam j p.P.A3.fam3.base3.μ0 q v)) ∧
    -(3 * C * d.O.f * d.O.m * (d.O.N : ℝ) ^ 2 * Real.log p.Z.b) ≤ Formalism.PairingDivisionLocalBalance.meanInf _ g

def OneSq (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafOneSquare d.O (p.S false).μ C p.Z.b

def Den (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => PrimeCountingSumBound d.O C p.Z.x p.Z.b

def Int (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafINT d.O C p.Z.b

def Arch (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafARCH d.O C p.Z.b

def Thb (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafTHB d.O C p.Z.x p.Z.b

def Wt (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b

def DesH : Prop := Lf trivialTieCondition fun p _ d _ _ => leafHypothesesConst d.O ∧ LatticeConstantBound d.O p.Z.b

def RankGapBound : Prop := Lf trivialTieCondition fun p _ d C _ => DegreeAndSizeBounds d.O C p.Z.b

def RamifiedSumBound : Prop := Lf trivialTieCondition fun p _ d C _ => PrimePowerModuliSumBound d.O C p.Z.b ∧ LeafCS d.O p.Z.b

def DesPol : Prop := Lf trivialTieCondition fun p _ d C CH => LeafPol d.O C p.Z.x CH p.Z.b

def Scale : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun _ _ _ p =>
  1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b

def Bundle : Prop := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows →
  (Df p).WF ∧ ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false

def Fun0Fit (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  EvPt Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)

theorem evPt_and {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : EvPt Fm P) (hQ : EvPt Fm Q) : EvPt Fm fun x hx i p => P x hx i p ∧ Q x hx i p :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun x hx h i p hp => ⟨ha x hx (le_of_max_le_left h) i p hp, hb x hx (le_of_max_le_right h) i p hp⟩⟩

theorem evPt_imp {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : EvPt Fm P) (h : ∀ x hx i p, p.Rows → P x hx i p → Q x hx i p) : EvPt Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩

theorem Lf.mono {Comparison₂ Tie' : TieT} {Q Q' : PropT} (h : Lf Comparison₂ Q)
    (h' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF) (C CH : ℝ), p.Rows → Tie' p CF d →
      Comparison₂ p CF d ∧ (Q p CF d C CH → Q' p CF d C CH)) : Lf Tie' Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ a hN => ?_⟩
  obtain ⟨C0, a⟩ := a hN
  exact ⟨C0, fun C hC => evPt_imp (a C hC) fun _ _ _ p hp b d hd =>
    (h' p CF d C CH hp hd).2 (b d (h' p CF d C CH hp hd).1)⟩

theorem Lf.and {Comparison₂ : TieT} {Q Q' : PropT} (h : Lf Comparison₂ Q) (h' : Lf Comparison₂ Q') :
    Lf Comparison₂ fun p CF d C CH => Q p CF d C CH ∧ Q' p CF d C CH := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  refine ⟨max a b, fun CF hCF => ((h CF (le_of_max_le_left hCF)).and (h' CF (le_of_max_le_right hCF))).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1 hN
  obtain ⟨C1, c2⟩ := c.2 hN
  exact ⟨max C0 C1, fun C hC => evPt_imp (evPt_and (c1 C (le_of_max_le_left hC)) (c2 C (le_of_max_le_right hC)))
    fun _ _ _ _ _ e d hd => ⟨e.1 d hd, e.2 d hd⟩⟩

theorem Lf.of_noTie {Q : PropT} (h : Lf trivialTieCondition Q) (Comparison₂ : TieT) : Lf Comparison₂ Q :=
  h.mono fun _ _ _ _ _ _ _ => ⟨trivial, id⟩

theorem fun0Fit_of_leaves (Fld : FldT) (Comparison₂ : TieT) (hB : Bundle) (hS : Scale) (hE : Ex Fld Comparison₂) (h1 : MM Comparison₂) (h2 : OneMap Comparison₂)
    (h3 : Ker Comparison₂) (h4 : FP Comparison₂) (h5 : IPa Comparison₂) (h6 : IPb) (h7 : OneSq Comparison₂) (h8 : Den Comparison₂) (h9 : Int Comparison₂) (h10 : Arch Comparison₂)
    (h11 : Thb Comparison₂) (h12 : Wt Comparison₂) (h13 : DesH) (h14 : RankGapBound) (h15 : RamifiedSumBound) (h16 : DesPol) : Fun0Fit Fld := by
  obtain ⟨a, hA⟩ := Lf.and h1 <| Lf.and h2 <| Lf.and h3 <| Lf.and h4 <| Lf.and h5 <| Lf.and (Lf.of_noTie h6 _) <| Lf.and h7 <|
    Lf.and h8 <| Lf.and h9 <| Lf.and h10 <| Lf.and h11 <| Lf.and h12 <| Lf.and (Lf.of_noTie h13 _) <|
    Lf.and (Lf.of_noTie h14 _) <| Lf.and (Lf.of_noTie h15 _) (Lf.of_noTie h16 _)
  obtain ⟨b, hE⟩ := hE
  refine ⟨max a b, fun CF hCF => (((hA CF (le_of_max_le_left hCF)).and (hE CF (le_of_max_le_right hCF))).and hS).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1.1 hN
  refine evPt_imp (evPt_and (evPt_and (c1 (max C0 1) (le_max_left _ _)) (c.1.2 hN)) c.2) fun x hx i p hp e hG C => ?_
  obtain ⟨⟨e1, e2⟩, s1, s2, s3⟩ := e
  obtain ⟨G, W, g1, g2, g3⟩ := hG
  obtain ⟨d, rfl, hd⟩ := e2 G W g1 g2 g3
  obtain ⟨l1, ⟨ze, z1, z2, l2⟩, l3, ⟨Tf, dF, l4⟩, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16⟩ := e1 d ⟨g2, hd⟩
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have v0 : (d.data ze Tf dF).vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (ze _)⁻¹ • _ = _
    rw [z1, inv_one]
    exact one_smul _ _
  have v1 : ∀ Tf dF t, (d.data (fun _ => 1) Tf dF).vmu t = d.V t := fun _ _ _ => by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  have hRR := R0.RR_spec Formalism.DivisionValues.lattice_gluing wf
  refine functional_lower_bound_of_conditions_numeric wf (p.S false) p.Z C CH (d.data ze Tf dF) (max C0 1) (hR ▸ R0.D_pos) (hR ▸ R0.h0) (hR ▸ R0.l1a)
    (hR ▸ R0.l1c) (hR ▸ R0.frames.1) (hR ▸ hRR.1) (hR ▸ hRR.2) (le_max_right _ _) s1 s2 s3 l1 l2 ?_ ?_ ⟨?_, l6⟩ l7 l8 l9 l10
    l11 l13.1 l13.2 l14 l15.1 l15.2 l12 l16
  · have : LinearMap.ker (d.O.vmu _).mulVecLin = _ := l3
    rw [v1] at this
    show LinearMap.ker ((d.data ze Tf dF).vmu _).mulVecLin = _
    rw [v0]
    exact this
  · have := GlobalTheory.finitePlaceBound_inv_rootOfUnity_smul _ ze _ _ _ z2 l4
    simp only [v1] at this
    exact this
  · intro vb hvb
    exact l5 vb (hvb.trans v0)

def FunIn.ofGrid {p : PtAt ex Csz} {CF : ℝ} (G : Grid p CF) (W : G.Weil) (h : W.Over p.R.toRealDat) (n : ℕ)
    (V : ∀ t : Tup p, Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL) : FunIn p CF :=
  ⟨G, W, h, n, fun _ => 1, Submodule.span _ (Set.range (Pi.basisFun D.what₂.LL (Fin n))), V, fun _ _ => 1, fun _ => 0, ∅, ∅,
    fun _ _ _ => 0, fun _ => 1, fun _ => 1, fun _ _ => 1, fun _ _ _ => 1, fun _ _ _ => 0, fun _ => true, 1⟩

example (p : PtAt ex Csz) : p.Z.b = L.sc.b ∧ p.Z.x = L.sc.x := ⟨rfl, rfl⟩

example (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF) (h : GridFit p G) : ∃ z : D.what₂.LL,
    IsPrimitiveRoot z (Ideal.absNorm G.pl.v0.asIdeal ^ GlobalTheory.ChiGrid.depth0 D CF p.Z.b) := by
  simpa [GlobalTheory.ChiGrid.Places.depth] using h.fieldLL.roots _ (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))

example (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF) (h : GridFit p G) (w) (hw : TwistedAt D w) :
    Nonempty (D.ntw.abelian₂ (ex.nch.twI w)) := h.list.nonempty (h.setting.inW1 hw)

example (Fld : FldT) (h : Fun0) : Fun0Fit Fld :=
  ⟨0, fun _ _ => h.imp fun _ _ _ a hN => evPt_imp (a hN) fun _ _ _ _ _ b _ => b⟩

end GlobalTheory.BigTop.Fun

end
end
