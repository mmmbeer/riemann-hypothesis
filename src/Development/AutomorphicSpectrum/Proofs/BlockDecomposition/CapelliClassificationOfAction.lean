import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaSelfH
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotient
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionUnipotentRadicalReal
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand

section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.CapProdProof

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem evalPair_injLeft_eq_eval (E1 E2 : Fin n → Fin n → Module.End ℂ W) (s : Bool) (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    ev2 E1 E2 (injL s z) = CompanionTheory.D.LK.ev (if s then E1 else E2) z := by
  have e : (ev2 E1 E2).comp (injL s) = CompanionTheory.D.LK.ev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s <;> simp [ev2, injL, CompanionTheory.D.LK.ev]
  exact DFunLike.congr_fun e z

theorem evB_injL (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evB lev X1 X2 (injL s z) = CompanionTheory.RgExh.U.evL lev (if s then X1 else X2) z := by
  have e : (evB lev X1 X2).comp (injL s) = CompanionTheory.RgExh.U.evL lev (if s then X1 else X2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s <;> simp [evB, injL, CompanionTheory.RgExh.U.evL]
  exact DFunLike.congr_fun e z

theorem commute_ev (T : Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ p q, Commute T (E p q))
    (z : FreeAlgebra ℂ (Fin n × Fin n)) : Commute T (CompanionTheory.D.LK.ev E z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r T).symm
  | grade1 p => simpa [CompanionTheory.D.LK.ev] using h p.1 p.2
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

def wL {V : Type} [AddCommGroup V] [Module ℂ V] (s : Bool) (w : Pos n → V) (l : Lt n) : V :=
  (1 / 2 : ℂ) • (if l.1 || s then w l.2 else -w l.2)

theorem sum_letters (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ W) (s : Bool) (w : Pos n → W) :
    (∑ l : Lt n, if inUL lev l then Tl E1 E2 l (wL s w l) else 0) =
      ∑ i : Pos n, if CompanionTheory.RgExh.U.inU lev i then (if s then E1 else E2) i.1.1 i.1.2 (w i) else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : lev i.1.1 < lev i.1.2
  · cases s <;> simp [hi, Tl, Ts, wL, CompanionTheory.RgExh.U.inU] <;> module
  · simp [hi, CompanionTheory.RgExh.U.inU]

theorem isSubL_inUL (lev : Fin n → ℕ) : IsSubL lev (inUL lev) := by
  refine ⟨fun l h => h, fun s t i j k h1 h2 h3 hi hj => ?_⟩
  show lev k.1.1 < lev k.1.2
  have a : lev i.1.1 < lev i.1.2 := hi
  have b : lev j.1.1 < lev j.1.2 := hj
  rw [h2, h3]
  rw [h1] at a
  exact a.trans b

theorem commute_levi_boundary_and_lift (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (hlev : ∀ (i : Fin M) (p : Fin (sz lev M i)), lev (GlobalTheory.SmGL.stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ))
    (s : Bool) (Y : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (hP : PairRel E1 E2) :
    (∀ l, inUL lev l → Commute (Tl E1 E2 l) (ev2 E1 E2 (injL s (fa n Y)))) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 (injL s (fa n Y)) x - evB lev E1 E2 (injL s (fb (sz lev M) h Y)) x =
        ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0 := by
  have hG : GlRel (if s then E1 else E2) := by
    cases s
    · simpa using hP.2.1
    · simpa using hP.1
  obtain ⟨c1, c2⟩ := GlobalTheory.CompanionTheory.RgCOBlock.co_hyp n M lev (sz lev M) h Y hm hlev V _ hG
  refine ⟨fun l hl => ?_, fun x => ?_⟩
  · rw [evalPair_injLeft_eq_eval]
    have hc := c1 l.2 hl
    have h1 : Commute (E1 l.2.1.1 l.2.1.2) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
      cases s
      · exact commute_ev _ _ (fun p q => hP.2.2 _ _ p q) _
      · simpa using hc
    have h2 : Commute (E2 l.2.1.1 l.2.1.2) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
      cases s
      · simpa using hc
      · exact commute_ev _ _ (fun p q => (hP.2.2 p q _ _).symm) _
    rcases l with ⟨b, i⟩
    cases b
    · simpa [Tl, Ts] using h1.sub_left h2
    · simpa [Tl, Ts] using h1.add_left h2
  · obtain ⟨w, hw⟩ := c2 x
    refine ⟨wL s w, ?_⟩
    rw [sum_letters, evalPair_injLeft_eq_eval, evB_injL]
    exact hw

theorem capProd : GenCOU2 → CapProd := by
  intro hG n M lev h hm hM V _ _ E1 E2 hP s Y r hq j x hS hD hc
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  obtain ⟨w, w1, w2, w3⟩ := hG n lev (inUL lev) (injL s (fa n Y)) (injL s (fb (sz lev M) h Y)) hm (isSubL_inUL lev)
    (fun V _ _ E1 E2 hP => commute_levi_boundary_and_lift n M lev h hm hlev s Y V E1 E2 hP) V E1 E2 hP j x hS hD hc
  refine ⟨w, w1, w2, ?_⟩
  rw [← w3, evalPair_injLeft_eq_eval, GlobalTheory.CompanionTheory.RgCOBlock.ev_fa, hq]
  congr 1

end GlobalTheory.CompanionTheory.PairMult.CapProdProof
end
end

section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.Asm

open Formalism.REAL (GlRel qdet)
open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RgCOBlock (sz shift fb)
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

theorem mem_down {S : Finset (Fin n)} (hS : ∀ a b, b ≤ a → a ∈ S → b ∈ S) (a : Fin n) :
    a ∈ S ↔ (a : ℕ) < S.card :=
  _root_.UpperTheory.Reformulated.B.DYlb8.main hS a

theorem twice_sum_Ico (m d : ℕ) :
    2 * ∑ k ∈ Finset.Ico m (m + d), (k : ℝ) = 2 * (d : ℝ) * m + d * ((d : ℝ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem level_sum (lev : Fin n → ℕ) (hm : Monotone lev) (c : ℕ) :
    2 * ∑ a ∈ univ.filter (fun a => lev a = c), ((a : ℕ) : ℝ) =
      2 * ((univ.filter fun a => lev a = c).card : ℝ) * ((univ.filter fun a => lev a < c).card : ℝ) +
        ((univ.filter fun a => lev a = c).card : ℝ) * (((univ.filter fun a => lev a = c).card : ℝ) - 1) := by
  set d := (univ.filter fun a => lev a = c).card with hd
  set m := (univ.filter fun a => lev a < c).card with hmm
  have hlow : ∀ a, lev a < c ↔ (a : ℕ) < m := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    simpa using this
  have hcard : (univ.filter fun a => lev a < c + 1).card = m + d := by
    rw [hmm, hd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro a h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
  have hup : ∀ a, lev a < c + 1 ↔ (a : ℕ) < m + d := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c + 1) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    rw [hcard] at this
    simpa using this
  have hle : m + d ≤ n := by
    rw [← hcard]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have hmap : (univ.filter fun a => lev a = c).map Fin.valEmbedding = Finset.Ico m (m + d) := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hlow a
      have h2 := hup a
      omega
    · rintro ⟨k1, k2⟩
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      have h1 := hlow ⟨k, by omega⟩
      have h2 := hup ⟨k, by omega⟩
      simp only at h1 h2
      omega
  rw [← twice_sum_Ico, ← hmap, Finset.sum_map]
  rfl

section Alg

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end Alg

section Spaces

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def cycQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppQ (inUL lev) x ∧ DegQ j x ∧ bdq E1 E2 x = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun A hA i hi => ?_, fun A hA => ?_, by rw [map_add, h3, g3, add_zero]⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), by rw [map_smul, h3, smul_zero]⟩

def bdyQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {x | ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧ bdq E1 E2 w = x}
  add_mem' := by
    rintro _ _ ⟨x, h1, h2, rfl⟩ ⟨y, g1, g2, rfl⟩
    refine ⟨x + y, fun A hA i hi => ?_, fun A hA => ?_, map_add _ _ _⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨0, fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, h1, h2, rfl⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨c • x, fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), map_smul _ _ _⟩

end Spaces

end GlobalTheory.CompanionTheory.PairMult.Asm
end
end

section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeSM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qminor_restrict {n m t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (ι : Fin m → Fin n)
    (hι : Function.Injective ι) (a b : Fin t → Fin m) (w : ℂ) :
    qminor (fun a b => E (ι a) (ι b)) a b w = qminor E (ι ∘ a) (ι ∘ b) w := by
  unfold qminor Tm
  simp only [Function.comp, hι.eq_iff]

theorem tm_of_ne {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (w : ℂ) {a b : Fin n} (h : a ≠ b) :
    Tm E w a b = E a b := by
  unfold Tm
  simp [h]

theorem qdet_eq_qminor {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (r : Fin n → Fin n)
    (hr : Function.Bijective r) (u : ℂ) : qdet E u = qminor E r r u := by
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective r hr
  have e : r = id ∘ τ := rfl
  have h1 : qdet E u = qminor E id id u := by
    unfold qdet qminor Tm
    simp only [id]
  rw [h1, e, quantumMinorRowSkew_holds, quantumMinorColSkew_holds _ _ _ _ hE, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self]
  simp

theorem succAbove_castSucc_last {N : ℕ} (c : Fin (N + 1)) :
    (Fin.castSucc c).succAbove (Fin.last N) = Fin.last (N + 1) := by
  exact Fin.succAbove_of_le_castSucc _ _ (by
    simpa [Fin.le_def] using Nat.lt_succ_iff.1 c.isLt) |>.trans (by simp)

end GlobalTheory.CompanionTheory.RgHeSM
end
end

section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CapClsProof

open Formalism.REAL (GlRel qdet qminor)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)
open GlobalTheory.SmGL (stdBlocks)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def inj (s : Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => (1 / 2 : ℂ) •
    (if s then FreeAlgebra.ι ℂ (false, p) + FreeAlgebra.ι ℂ (true, p)
      else FreeAlgebra.ι ℂ (false, p) - FreeAlgebra.ι ℂ (true, p))

section Eval

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evalCartan_inclusion (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evKP E1 E2 (inj s z) = CompanionTheory.D.LK.ev (if s then E1 else E2) z := by
  have e : (evKP E1 E2).comp (inj s) = CompanionTheory.D.LK.ev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s
    · simp [evKP, inj, CompanionTheory.D.LK.ev, kA, pA]
      module
    · simp [evKP, inj, CompanionTheory.D.LK.ev, kA, pA]
      module
  exact DFunLike.congr_fun e z

theorem evLv_inj (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evLv lev E1 E2 (inj s z) = CompanionTheory.RgExh.U.evL lev (if s then E1 else E2) z := by
  have e : (evLv lev E1 E2).comp (inj s) = CompanionTheory.RgExh.U.evL lev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    by_cases hp : lev p.1 = lev p.2
    · cases s
      · simp [evLv, inj, CompanionTheory.RgExh.U.evL, kA, pA, hp]
        module
      · simp [evLv, inj, CompanionTheory.RgExh.U.evL, kA, pA, hp]
        module
    · cases s <;> simp [evLv, inj, CompanionTheory.RgExh.U.evL, hp]
  exact DFunLike.congr_fun e z

theorem evLc_inj (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evLc lev E1 E2 (inj s z) = CompanionTheory.RgExh.U.evL lev (if s then firstLeviFamily lev E1 E2 else secondLeviFamily lev E1 E2) z := by
  have e : (evLc lev E1 E2).comp (inj s) = CompanionTheory.RgExh.U.evL lev (if s then firstLeviFamily lev E1 E2 else secondLeviFamily lev E1 E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    by_cases hp : lev p.1 = lev p.2
    · cases s <;> simp [inj, CompanionTheory.RgExh.U.evL, hp, firstLeviFamily, secondLeviFamily]
    · cases s <;> simp [inj, evLc, CompanionTheory.RgExh.U.evL, hp]
  exact DFunLike.congr_fun e z

def wL (s : Bool) (w : Pos n → V) (l : Lt n) : V :=
  (1 / 2 : ℂ) • (if l.1 && !s then -w l.2 else w l.2)

theorem sum_letters (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (w : Pos n → V) :
    (∑ i : Pos n, if CompanionTheory.RgExh.U.inU lev i then (if s then E1 else E2) i.1.1 i.1.2 (w i) else 0) =
      ∑ l : Lt n, if inUU lev l then xL E1 E2 l (wL s w l) else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : lev i.1.1 < lev i.1.2
  · cases s <;> simp [hi, xL, kA, pA, wL, CompanionTheory.RgExh.U.inU] <;> module
  · simp [hi, CompanionTheory.RgExh.U.inU]

end Eval

theorem central (s : Bool) (Y : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (hP : IsPairA E1 E2) (c d : Fin n) : Commute (kA E1 E2 c d) (evKP E1 E2 (inj s (fa n Y))) := by
  rw [evalCartan_inclusion]
  have hG : GlRel (if s then E1 else E2) := by
    cases s
    · simpa using hP.2.1
    · simpa using hP.1
  have hc : ∀ p q, Commute ((if s then E1 else E2) p q) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := fun p q => by
    rw [GlobalTheory.CompanionTheory.RgCOBlock.ev_fa]
    exact (Formalism.REAL.qDetCentral (Module.End ℂ V) n _ hG _ p q).symm
  have h1 : Commute (E1 c d) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
    cases s
    · exact GlobalTheory.CompanionTheory.PairMult.CapProdProof.commute_ev _ _ (fun p q => hP.2.2 _ _ p q) _
    · simpa using hc c d
  have h2 : Commute (E2 c d) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
    cases s
    · simpa using hc c d
    · exact GlobalTheory.CompanionTheory.PairMult.CapProdProof.commute_ev _ _ (fun p q => (hP.2.2 p q _ _).symm) _
  exact h1.add_left h2

theorem co_class (hAct : ActUU) (M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (hM : ∀ a, lev a < M) (s : Bool) (Y r : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (hP : IsPairA E1 E2)
    (hq : qdet (if s then E1 else E2) (Y + ((n : ℂ) - 1) / 2) = r • (1 : Module.End ℂ V)) (v : V)
    (hv : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0) :
    r • (Pi.single (omU lev) v : Cq n V) -
      CompanionTheory.RgExh.U.evL lev (if s then firstLeviFamily lev E1 E2 else secondLeviFamily lev E1 E2) (fb (sz lev M) h Y) (Pi.single (omU lev) v) ∈
      bdSub lev E1 E2 := by
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  obtain ⟨w, w1, w2, w3⟩ := hAct n lev hm (inj s (fa n Y)) (inj s (fb (sz lev M) h Y))
    (fun V _ _ E1 E2 hP c d => central s Y V E1 E2 hP c d)
    (fun V _ _ E1 E2 hP x => by
      have hG : GlRel (if s then E1 else E2) := by
        cases s
        · simpa using hP.2.1
        · simpa using hP.1
      obtain ⟨w, hw⟩ := (GlobalTheory.CompanionTheory.RgCOBlock.co_hyp n M lev (sz lev M) h Y hm hlev V _ hG).2 x
      refine ⟨wL s w, ?_⟩
      rw [← sum_letters, evalCartan_inclusion, evLv_inj]
      exact hw) V E1 E2 hP v hv
  refine ⟨w, ⟨w1, w2⟩, ?_⟩
  show bdL (inUU lev) E1 E2 w = _
  rw [← w3, evalCartan_inclusion, evLc_inj, GlobalTheory.CompanionTheory.RgCOBlock.ev_fa, hq]
  congr 1
  funext A
  by_cases hA : A = omU lev
  · subst hA
    simp
  · simp [Pi.single_eq_of_ne hA]

def sg (lev : Fin n → ℕ) (j : ℕ) : ℂ :=
  (((univ.filter fun b => j < lev b).card : ℂ) - ((univ.filter fun b => lev b < j).card : ℂ)) / 2

theorem sum_sz (M : ℕ) (lev : Fin n → ℕ) (hM : ∀ a, lev a < M) (P : ℕ → Prop) [DecidablePred P] :
    ∑ b ∈ univ.filter (fun b : Fin M => P (b : ℕ)), sz lev M b = (univ.filter fun a => P (lev a)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (⟨lev a, hM a⟩ : Fin M))
    (t := univ.filter fun b : Fin M => P (b : ℕ))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : P (b : ℕ) := (Finset.mem_filter.1 hb).2
    unfold sz
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, Fin.ext_iff]
    constructor
    · intro h
      exact ⟨h ▸ hb', h⟩
    · exact fun h => h.2
  · intro a ha
    simpa using ha

theorem modExp_sz (M : ℕ) (lev : Fin n → ℕ) (hM : ∀ a, lev a < M) (i : Fin M) :
    ((GlobalTheory.SmGL.modExp (fun i => Fin (sz lev M i)) i : ℤ) : ℂ) / 2 = sg lev i := by
  have h1 := sum_sz M lev hM (fun b => (i : ℕ) < b)
  have h2 := sum_sz M lev hM (fun b => b < (i : ℕ))
  have e1 : (univ.filter fun b : Fin M => i < b) = univ.filter fun b : Fin M => (i : ℕ) < b := rfl
  have e2 : (univ.filter fun b : Fin M => b < i) = univ.filter fun b : Fin M => (b : ℕ) < i := rfl
  simp only [GlobalTheory.SmGL.modExp, Fintype.card_fin, sg]
  rw [e1, e2]
  push_cast
  rw [← Nat.cast_sum, ← Nat.cast_sum, h1, h2]

theorem std_eq_blkE (M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev) (i : Fin M) :
    (fun p : Fin (sz lev M i) => stdBlocks (sz lev M) h ⟨i, p⟩) = blkE lev (i : ℕ) := by
  have hs : StrictMono fun p : Fin (sz lev M i) => stdBlocks (sz lev M) h ⟨i, p⟩ := fun p q hpq => by
    rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
    have : (p : ℕ) < q := hpq
    omega
  have hf : ∀ p : Fin (sz lev M i), stdBlocks (sz lev M) h ⟨i, p⟩ ∈ blk lev (i : ℕ) := fun p => by
    simpa [blk] using GlobalTheory.CompanionTheory.RgCOBlock.lev_stdBlocks lev h hm i p
  exact Finset.orderEmbOfFin_unique (s := blk lev (i : ℕ)) rfl hf hs

theorem capS_empty {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (lev : Fin n → ℕ)
    (j : ℕ) (u : ℂ) (hj : j ∉ univ.image lev) : capS F lev j u = 1 := by
  have e : ∀ (t : ℕ) (a b : Fin t → Fin n) (x : ℂ), t = 0 → qminor F a b x = 1 := by
    rintro t a b x rfl
    simp [qminor]
  refine e _ _ _ _ ?_
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun a _ ha => hj ?_)
  exact Finset.mem_image.2 ⟨a, mem_univ _, ha⟩

theorem prod_filter {A : Type} [Monoid A] (g : ℕ → A) (p : ℕ → Prop) [DecidablePred p] (hg : ∀ j, ¬p j → g j = 1) (l : List ℕ) :
    ((l.filter fun j => decide (p j)).map g).prod = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x
    · simp [List.filter_cons, hx, ih]
    · simp [List.filter_cons, hx, ih, hg x hx]

theorem levs_eq (M : ℕ) (lev : Fin n → ℕ) (hM : ∀ a, lev a < M) :
    levs lev = (List.range M).filter fun j => decide (j ∈ univ.image lev) := by
  have hp : (univ.image lev).sort (· ≤ ·) |>.Perm ((List.range M).filter fun j => decide (j ∈ univ.image lev)) := by
    refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ((List.nodup_range).filter _)).2 fun j => ?_
    simp only [Finset.mem_sort, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hj
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hj
      exact ⟨hM a, Finset.mem_image.2 ⟨a, mem_univ _, rfl⟩⟩
    · exact fun hj => hj.2
  exact hp.eq_of_pairwise' (Finset.pairwise_sort _ _) ((List.pairwise_lt_range.imp le_of_lt).filter _)

theorem evL_fb_capProd (M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev) (hM : ∀ a, lev a < M)
    {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (Y : ℂ) :
    CompanionTheory.RgExh.U.evL lev F (fb (sz lev M) h Y) = capProd F lev (sg lev) Y := by
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  rw [GlobalTheory.CompanionTheory.RgCOBlock.evL_fb lev (sz lev M) h hlev]
  have hblk : ∀ i : Fin M, qdet (fun p q : Fin (sz lev M i) => F (stdBlocks (sz lev M) h ⟨i, p⟩) (stdBlocks (sz lev M) h ⟨i, q⟩))
      (Y + ((sz lev M i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (sz lev M i)) i : ℂ) / 2) =
      capS F lev (i : ℕ) (Y - sg lev i) := fun i => by
    have hinj : Function.Injective fun p : Fin (sz lev M i) => stdBlocks (sz lev M) h ⟨i, p⟩ := fun p q hpq => by
      have := (stdBlocks (sz lev M) h).injective hpq
      simpa using this
    unfold qdet capS
    rw [GlobalTheory.CompanionTheory.RgHeSM.qminor_restrict F _ hinj, modExp_sz M lev hM i]
    simp only [Function.comp_id]
    rw [std_eq_blkE M lev h hm i]
    congr 1
    show _ = Y - sg lev i + (((sz lev M i : ℕ) : ℂ) - 1) / 2
    ring
  have hg : (List.ofFn fun i : Fin M => capS F lev (i : ℕ) (Y - sg lev i)) =
      (List.range M).map fun j => capS F lev j (Y - sg lev j) := by
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  simp only [hblk]
  rw [hg, capProd, levs_eq M lev hM, prod_filter _ _ (fun j hj => capS_empty F lev j _ hj)]

theorem shift_real (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hm : Monotone lev) (j : ℕ) :
    (∑ a ∈ blk lev j, (muQ lam lev a + 2 * rhoU lev a)) - ((blk lev j).card : ℝ) *
      (((univ.filter fun b => j < lev b).card : ℝ) - ((univ.filter fun b => lev b < j).card : ℝ)) =
      2 * ∑ a ∈ blk lev j, Lr lam a := by
  have hcard : (((univ.filter fun b => j < lev b).card : ℝ) + ((univ.filter fun b => lev b < j).card : ℝ) +
      ((blk lev j).card : ℝ)) = n := by
    have e : (univ.filter fun b => j < lev b).card + (univ.filter fun b => lev b < j).card + (blk lev j).card = n := by
      unfold blk
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      have : ∀ a : Fin n, ((if j < lev a then 1 else 0) + (if lev a < j then 1 else 0) + (if lev a = j then 1 else 0) : ℕ) = 1 := by
        intro a
        split_ifs <;> omega
      simp [this]
    exact_mod_cast e
  have hs := GlobalTheory.CompanionTheory.PairMult.Asm.level_sum lev hm j
  have hr : ∀ a ∈ blk lev j, rhoU lev a =
      (((univ.filter fun b => j < lev b).card : ℝ) - ((univ.filter fun b => lev b < j).card : ℝ)) / 2 := fun a ha => by
    have : lev a = j := (Finset.mem_filter.1 ha).2
    simp only [rhoU, this]
  have e1 : ∑ a ∈ blk lev j, (muQ lam lev a + 2 * rhoU lev a) = 2 * ∑ a ∈ blk lev j, (lam a : ℝ) +
      ((blk lev j).card : ℝ) * (2 * (((univ.filter fun b => j < lev b).card : ℝ) - ((univ.filter fun b => lev b < j).card : ℝ))) := by
    rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [muQ, hr a ha]
    ring
  have e2 : ∑ a ∈ blk lev j, Lr lam a = ∑ a ∈ blk lev j, (lam a : ℝ) + ((blk lev j).card : ℝ) * (((n : ℝ) - 1) / 2) -
      ∑ a ∈ blk lev j, ((a : ℕ) : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rfl
  change 2 * ∑ a ∈ blk lev j, ((a : ℕ) : ℝ) = 2 * ((blk lev j).card : ℝ) * ((univ.filter fun a => lev a < j).card : ℝ) +
    ((blk lev j).card : ℝ) * (((blk lev j).card : ℝ) - 1) at hs
  rw [e1, e2]
  linear_combination ((blk lev j).card : ℝ) * hcard + hs

theorem shift_id (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hm : Monotone lev) (j : ℕ) :
    (∑ a ∈ blk lev j, ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ)) - ((blk lev j).card : ℂ) * (sg lev j + sg lev j) =
      2 * ∑ a ∈ blk lev j, (Lr lam a : ℂ) := by
  have e := congrArg (fun x : ℝ => (x : ℂ)) (shift_real lam lev hm j)
  simp only [sg]
  push_cast at e ⊢
  rw [← e]
  ring

theorem capCls_of (hAct : ActUU) (hC : GlobalTheory.CompanionTheory.PairMult.CapOne) (hD : GlobalTheory.CompanionTheory.PairMult.DualCap) : CapCls := by
  intro n lam _ lev hlev
  refine ⟨sg lev, sg lev, shift_id lam lev hlev.1, ?_⟩
  intro V _ _ E1 E2 hA v hv u
  obtain ⟨M, hM⟩ : ∃ M, ∀ a, lev a < M :=
    ⟨univ.sup lev + 1, fun a => Nat.lt_succ_of_le (Finset.le_sup (f := lev) (mem_univ a))⟩
  have h : ∑ i, sz lev M i = n := by
    simpa using sum_sz M lev hM (fun _ => True)
  have hP : IsPairA E1 E2 := ⟨hA.gl1, hA.gl2, hA.comm⟩
  have hLχ : (fun a => ((Lr lam a : ℝ) : ℂ)) = infOf lam true := by
    funext a
    simp [Lr, infOf]
  have hneg : (fun a => -infOf lam true a) = infOf lam false := by
    funext a
    simp [infOf]
  have hcap : Formalism.QuantumDeterminants.capP (infOf lam true) u = ∏ a, (u + (Lr lam a : ℂ)) := by
    rw [← hLχ]
    rfl
  have hq1 : qdet E1 (u + ((n : ℂ) - 1) / 2) = (∏ a, (u + (Lr lam a : ℂ))) • (1 : Module.End ℂ V) := by
    rw [← hcap]
    exact hC n V E1 (infOf lam true) hA.gl1 hA.ch1 u
  have hq2 : qdet E2 (u + ((n : ℂ) - 1) / 2) = (∏ a, (u + (Lr lam a : ℂ))) • (1 : Module.End ℂ V) := by
    rw [← hcap]
    exact hD n V E2 (infOf lam true) hA.gl2 (by rw [hneg]; exact hA.ch2) u
  have hk : ∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0 := by
    rintro ⟨s, i⟩ rfl -
    exact hv.2 i.1.1 i.1.2 i.2 rfl
  have c1 := co_class hAct M lev h hlev.1 hM true u _ V E1 E2 hP hq1 v hk
  have c2 := co_class hAct M lev h hlev.1 hM false u _ V E1 E2 hP hq2 v hk
  rw [evL_fb_capProd M lev h hlev.1 hM] at c1 c2
  constructor
  · simpa using (bdSub lev E1 E2).neg_mem c1
  · simpa using (bdSub lev E1 E2).neg_mem c2

end GlobalTheory.CompanionTheory.CapClsProof
end
end

section
namespace GlobalTheory.CompanionTheory.PairMult

section Powers

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem epowLeft_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    PositivityTheory.RgBcC.RealD.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [PositivityTheory.RgBcC.RealD.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [PositivityTheory.RgBcC.RealD.epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem epowRight_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    Formalism.REAL.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [Formalism.REAL.epow, pow_succ, Matrix.mul_apply, Matrix.of_apply, ih]

theorem etr_eq_gelA (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) :
    Formalism.REAL.etr E m = PositivityTheory.RgBcC.RealD.gelA E m := by
  simp only [Formalism.REAL.etr, PositivityTheory.RgBcC.RealD.gelA, epowLeft_eq_pow, epowRight_eq_pow]

end Powers

end GlobalTheory.CompanionTheory.PairMult
end

section
namespace GlobalTheory.CompanionTheory.PairMult

theorem capelliPoly_neg {n : ℕ} (χ : Fin n → ℂ) (Y : ℂ) :
    Formalism.QuantumDeterminants.capP (fun a => -χ a) (-Y) = (-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y := by
  have h : ∀ s : Fin n, -Y + -χ s = (-1 : ℂ) * (Y + χ s) := fun s => by ring
  simp only [Formalism.QuantumDeterminants.capP, h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.CompanionTheory.PairMult
end

section
section
namespace GlobalTheory.CompanionTheory.CapClsA

open GlobalTheory.CompanionTheory.PairMult

theorem capOne_newton : CapOne := by
  intro n V _ _ E χ hE hg Y
  refine LinearMap.ext fun v => ?_
  have h := GlobalTheory.CapelliNewton.capelli_of_gelfand V n E χ hE
    (fun k x => by rw [etr_eq_gelA]; exact hg (k + 1) x) Y v
  simpa [Formalism.QuantumDeterminants.capP] using h

theorem dualCap_newton : DualCap := by
  intro n V _ _ E χ hE hg Y
  obtain ⟨hF, hq⟩ := GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  have h := capOne_newton n V (PositivityTheory.RgBcC.RealD.barF E) (fun a => -χ a) hF hg (-Y)
  have hq' := hq (-Y + ((n : ℂ) - 1) / 2)
  have harg : (n : ℂ) - 1 - (-Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2 := by ring
  rw [harg] at hq'
  have hne : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]; simp
  have h2 : ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) =
      ((-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y) • (1 : Module.End ℂ V) := by
    rw [← hq', ← capelliPoly_neg]
    exact h
  calc Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
      = ((-1 : ℂ) ^ n) • (((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)) := by
        rw [smul_smul, hne, one_smul]
    _ = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
        rw [h2, smul_smul, ← mul_assoc, hne, one_mul]

theorem capCls_of_actUU : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := fun hAct =>
  GlobalTheory.CompanionTheory.CapClsProof.capCls_of hAct capOne_newton dualCap_newton

end GlobalTheory.CompanionTheory.CapClsA
end

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_classification_of_action : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU
end
