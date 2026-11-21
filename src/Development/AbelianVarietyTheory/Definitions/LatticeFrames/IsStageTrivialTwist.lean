import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def tw0 (c : Com D) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Twist D := ⟨c.Pg, ∅, c.chi, ξ⟩

theorem eq_triv {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) (h : P.H = ⊥) : P = LevelP.triv _ _ _ := by
  obtain ⟨H, χ⟩ := P
  obtain rfl : H = ⊥ := h
  unfold LevelP.triv
  congr 1
  ext x
  rw [Subsingleton.elim x 1]; simp




open Classical in

def comQ (c : Com D) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Com D :=
  { c with
    P := ⟨⨅ PP : {PP : c.Pg // PP.1 ∉ Q}, (Pi.evalMonoidHom (fun PP : c.Pg => GL (Fin D.R.r) (kP PP.1)) PP.1).ker, 1⟩
    chi := fun j PP => if PP ∈ Q then (ξ PP)⁻¹ else c.chi j PP }

open Classical in

theorem twist_is {c : Com D} (hc : c.Is) {Q : Finset (Pl D.host.E)} (hQ : Q ⊆ c.Pg) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hξ : ∀ PP ∈ Q, ξ PP ≠ 1) (hχ : ∀ j : Fin D.R.m, ∀ PP ∈ Q, c.chi ((j : ℕ) + 1) PP = (ξ PP)⁻¹) :
    (⟨c.Pg \ Q, Q, c.chi, ξ⟩ : Twist D).Is (comQ c Q ξ) where
  com := ⟨hc.inf, hc.std, hc.chars, hc.exp, hc.unr, fun j => by
    obtain ⟨H, h1, h2⟩ := hc.res j
    refine ⟨H, h1, fun PP hP => ?_⟩
    have := h2 PP hP
    by_cases h : PP ∈ Q
    · simpa [comQ, h, hχ j PP h] using this
    · simpa [comQ, h] using this, hc.split⟩
  union := (Finset.sdiff_union_of_subset hQ).symm
  disj := Finset.sdiff_disjoint
  chiPg := fun j PP h => by simp [comQ, (Finset.mem_sdiff.1 h).2]
  chiQ := fun j PP h => by
    have h' : PP ∈ Q := h
    simp [comQ, h']
  ne := hξ
  grp := fun g => by
    refine (Subgroup.mem_iInf (S := fun PP : {PP : c.Pg // PP.1 ∉ Q} =>
      (Pi.evalMonoidHom (fun PP : c.Pg => GL (Fin D.R.r) (kP PP.1)) PP.1).ker)).trans ?_
    exact ⟨fun h PP hP => h ⟨PP, (Finset.mem_sdiff.1 hP).2⟩, fun h PP => h PP.1 (Finset.mem_sdiff.2 ⟨PP.1.2, PP.2⟩)⟩
  chr := rfl

def twStage (w : Twist D) (j : ℕ) (s : PiLocalization₂ D) (hr : D.R.r ≤ s.V.rank) : PiLocalization₂ D :=
  { s with L := Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B }


theorem one_lt_norm (PP : Pl D.host.E) : (1 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
  exact_mod_cast GlobalTheory.LFun.one_lt_absNorm PP

theorem zinv_pos (PP : Pl D.host.E) (a b : ℕ) : 0 < zinv PP a b := by
  refine Finset.prod_pos fun n hn => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_norm PP) ?_))
  have := (Finset.mem_Ioc.1 hn).1
  omega

theorem zinv_mul (PP : Pl D.host.E) {a b c : ℕ} (h : a ≤ b) (h' : b ≤ c) : zinv PP a b * zinv PP b c = zinv PP a c :=
  Finset.prod_Ioc_consecutive _ h h'

theorem idx_vol (PP : Pl D.host.E) (k : ℕ) :
    idxQ PP (k + 1) * volOne PP (k + 1) * zinv PP D.R.t ((k + 1) * D.R.t) = zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) := by
  have h1 : D.R.t ≤ (k + 1) * D.R.t := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have e1 := zinv_mul PP (Nat.zero_le D.R.t) h1
  have e2 := zinv_mul PP (Nat.zero_le D.R.t) (h1.trans (Nat.le_add_left _ D.R.r))
  have p0 := (zinv_pos PP 0 D.R.t).ne'
  have p1 := (zinv_pos PP 0 D.R.r).ne'
  have p2 := (zinv_pos PP D.R.t ((k + 1) * D.R.t)).ne'
  have p3 : (Ideal.absNorm PP.asIdeal : ℝ) ≠ 0 := (zero_lt_one.trans (one_lt_norm PP)).ne'
  unfold idxQ volOne
  rw [← e1, ← e2]
  field_simp

theorem const_eq {c : Com D} {s s' : PiLocalization₂ D} (w : Twist D) (k : ℕ) (p : Step c s s') (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (mR : Measure (GinfC s.V)) (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec) (L H H₀ : ℂ)
    (hH : H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) (h0 : dS w.S₀ s s' ≠ 0)
    (hd : dS (c.S : Set _) s s' = dS w.S₀ s s' * ((∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t) : ℝ) : ℂ)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℂ) * (L * H / dS (c.S : Set _) s s') * locQ c w k * ∫ g, zReal p m X φ v g ∂mR =
      kapOf w k p m X mR φ v H₀ * L := by
  have e : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) =
      (∏ PP ∈ w.Q, idxQ PP (k + 1)) * (∏ PP ∈ w.Q, volOne PP (k + 1)) * ∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun PP _ => (idx_vol PP k).symm
  have n : (∏ PP ∈ w.Q, zinv PP D.R.t (D.R.r + (k + 1) * D.R.t)) ≠ 0 :=
    (Finset.prod_pos fun PP _ => zinv_pos PP _ _).ne'
  rw [e] at n
  have n1 : ((∏ PP ∈ w.Q, idxQ PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n2 : ((∏ PP ∈ w.Q, volOne PP (k + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul (left_ne_zero_of_mul n)
  have n3 : ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul n
  have l : locQ c w k = (∏ PP ∈ w.Q, blockL c k PP) * ((∏ PP ∈ w.Q, zinv PP D.R.t ((k + 1) * D.R.t) : ℝ) : ℂ) := by
    rw [locQ, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [kapOf, hd, e, l, hH, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp

end GlobalTheory.ChainTw.Check

end
