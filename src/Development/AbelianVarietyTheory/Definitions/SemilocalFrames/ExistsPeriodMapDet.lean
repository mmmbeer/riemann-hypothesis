import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def sgnCN (k r : ℕ) : Fin (2 * r + k + 1) → Bool := fun i =>
  if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def IsShape (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (bv : ℝ) : Prop :=
  IsHCParam lam ∧ (∀ i, i.val < k - 1 → 0 ≤ lam i ∧ lam i ≤ bv / 8) ∧
    ∀ i, k - 1 ≤ i.val → -(2 * bv) ≤ lam i ∧ lam i ≤ -bv

def IsRange (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c h q : ℝ) : Prop :=
  0 < c ∧ GapAtLeast (sgnCN k r) lam h ∧ 100 * max 1 c * q * Real.sqrt (2 * r + 2) ≤ c * h ∧
    ∀ i j : Fin (2 * r + k + 1), i < j → j.val < k - 1 → 100 * max 1 c * q ≤ lam i - lam j

def dist1 {n : ℕ} (μ lam : Fin n → ℝ) : ℝ := ∑ a, |μ a - lam a|

def InPP {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) (μ : Fin n → ℝ) : Prop :=
  (∀ a, ∃ m : ℤ, μ a - lam a = (m : ℝ)) ∧ dist1 μ lam ≤ t

structure HRep (k r : ℕ) where
  H : Type
  [nG : NormedAddCommGroup H]
  [iP : InnerProductSpace ℂ H]
  σ : Mat k r → (H →L[ℂ] H)

attribute [instance] HRep.nG HRep.iP

variable {k r : ℕ}

def HRep.onJ (A : HRep k r) (P : Mat k r) : Mat k r → (A.H →L[ℂ] A.H) := fun g => A.σ (P⁻¹ * g * P)

def HRep.IsDSAt (A : HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ) : Prop :=
  IsDS (sgnCN k r) μ (A.onJ P)

def HRep.gl (A : HRep k r) (X : Mat k r) (v : A.H) : A.H :=
  dsig A.σ ((1 / 2 : ℂ) • (X - Hpk k r * Xᴴ * Hpk k r)) v +
    Complex.I • dsig A.σ ((-Complex.I / 2) • (X + Hpk k r * Xᴴ * Hpk k r)) v

def HRep.E (A : HRep k r) (P : Mat k r) (a b : Fin (2 * r + k + 1)) (v : A.H) : A.H :=
  A.gl (P⁻¹ * Matrix.single a b (1 : ℂ) * P) v

def HRep.iso (A : HRep k r) (P : Mat k r) (ν : Fin (2 * r + k + 1) → ℝ) : Submodule ℂ A.H :=
  sSup {S | IsKTypeOf (sgnCN k r) (A.onJ P) ν S}

def HRep.filt (A : HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ) (j : ℕ) : Submodule ℂ A.H :=
  Submodule.span ℂ {v | ∃ ν ω, dist1 ν (lowK (sgnCN k r) μ) ≤ j ∧ dist1 ω (lowK (sgnCN k r) μ) ≤ j ∧
    v ∈ A.iso P ν ∧ IsWtOn (Formalism.REAL.Kset (sgnCN k r)) (A.onJ P) ω v}

def IsMeasSG (z : Fin (2 * r + k + 1) → ℂ) (μG μS ν : Measure (Mt k r)) : Prop :=
  IsHaarOn (UH (Hpk k r)) μG ∧ IsHaarOn (Sset k r z) μS ∧ IsQuotMeas μG μS ν

def HRep.mass (A : HRep k r) {W : Type} [NormedAddCommGroup W] (ν : Measure (Mt k r)) (B : A.H → W)
    (φ : Mat k r → ℝ) (w : A.H) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (φ (Matrix.of x)) * ‖B (A.σ (Matrix.of x) w)‖ₑ ^ 2 ∂ν

def HRep.IsIsoB (A : HRep k r) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (z : Fin (2 * r + k + 1) → ℂ)
    (c : ℂ) (π : Mat k r → (W →L[ℂ] W)) (ν : Measure (Mt k r)) (B : A.H → W) : Prop :=
  IsBesselMapSm z (psi k r z c) A.σ π B ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) A.σ, A.mass ν B (fun _ => 1) w = ‖w‖ₑ ^ 2

abbrev Idx (k r l : ℕ) := {I : Finset (Fin (2 * r + k + 1)) // I.card = l}

def minorIJ {l : ℕ} (M : Mat k r) (I J : Idx k r l) : ℂ :=
  (M.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)).det

def stdMat (dual : Bool) (P g : Mat k r) : Mat k r := if dual then ((P * g * P⁻¹)⁻¹)ᵀ else P * g * P⁻¹

def wtI (dual : Bool) {l : ℕ} (I : Idx k r l) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if a ∈ I.1 then (if dual then -1 else 1) else 0

def epsI {l : ℕ} (I : Idx k r l) : ℝ := ∏ a ∈ I.1, (if sgnCN k r a then (1 : ℝ) else -1)

def HRep.tens (A : HRep k r) (dual : Bool) (P : Mat k r) {l : ℕ} (g : Mat k r) (x : Idx k r l → A.H) :
    Idx k r l → A.H :=
  fun I => ∑ J, minorIJ (stdMat dual P g) I J • A.σ g (x J)

def HRep.hh (A : HRep k r) {l : ℕ} (x y : Idx k r l → A.H) : ℂ := ∑ I, (epsI I : ℂ) * ⟪y I, x I⟫_ℂ

def HRep.SmT (A : HRep k r) {l : ℕ} (x : Idx k r l → A.H) : Prop := ∀ I, x I ∈ smoothVecs (k := k) (r := r) A.σ

structure IsTensDec (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (dual : Bool) (P : Mat k r) (l : ℕ)
    (μ : Fin (2 * r + k + 1) → ℝ)
    (ι : ∀ I : Idx k r l, (R (μ + wtI dual I)).H → Idx k r l → (R μ).H)
    (p : ∀ I : Idx k r l, (Idx k r l → (R μ).H) → (R (μ + wtI dual I)).H) : Prop where
  ι_smooth : ∀ I, ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, (R μ).SmT (ι I y)
  p_smooth : ∀ I x, (R μ).SmT x → p I x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ
  ι_lin : ∀ I (a : ℂ), ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ∀ y' ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, ι I (a • y + y') = a • ι I y + ι I y'
  p_lin : ∀ I (a : ℂ) x x', (R μ).SmT x → (R μ).SmT x' → p I (a • x + x') = a • p I x + p I x'
  ι_equiv : ∀ I, ∀ g ∈ UH (Hpk k r), ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ι I ((R (μ + wtI dual I)).σ g y) = (R μ).tens dual P g (ι I y)
  sum_ι_p : ∀ x, (R μ).SmT x → ∑ I, ι I (p I x) = x
  p_ι_self : ∀ I, ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, p I (ι I y) = y
  p_ι_ne : ∀ I J, I ≠ J → ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual J)).σ, p I (ι J y) = 0
  ι_cont : ∀ I J (w : List (Mat k r)), (∀ X ∈ w, InLieHpk k r X) →
    IsCWCont (k := k) (r := r) (R (μ + wtI dual I)).σ (fun y => dsigW (R μ).σ w (ι I y J))
  p_cont : ∀ I (w : List (Mat k r)), (∀ X ∈ w, InLieHpk k r X) → ∃ (C : ℝ) (Ws : List (List (Mat k r))),
    (∀ w' ∈ Ws, ∀ X ∈ w', InLieHpk k r X) ∧ ∀ x, (R μ).SmT x →
      ‖dsigW (R (μ + wtI dual I)).σ w (p I x)‖ ≤ C * (Ws.map fun w' => ∑ J, ‖dsigW (R μ).σ w' (x J)‖).sum

def IsHHNorm (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (dual : Bool) (l : ℕ) (μ : Fin (2 * r + k + 1) → ℝ)
    (ι : ∀ I : Idx k r l, (R (μ + wtI dual I)).H → Idx k r l → (R μ).H) (ep : Idx k r l → ℝ) : Prop :=
  (∀ I, ep I = 1 ∨ ep I = -1) ∧
  (∀ I, ∀ x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, (R μ).hh (ι I x) (ι I y) = (ep I : ℂ) * ⟪y, x⟫_ℂ) ∧
  ∀ I J, I ≠ J → ∀ x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
    ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual J)).σ, (R μ).hh (ι I x) (ι J y) = 0

def Amax (r : ℕ) (T κ b CA : ℝ) : ℝ := T * max κ κ⁻¹ ^ (2 * r) * b ^ CA

def H0 (k r : ℕ) (T κ b CA bv : ℝ) : ℝ :=
  (2 * r + k + 1 : ℕ) * Real.sqrt (Amax r T κ b CA) * (6 * bv) ^ (2 * r + 2)

def H1 (k r : ℕ) (T κ b CA bv : ℝ) : ℝ := H0 k r T κ b CA bv * max 1 (9 * (2 * r + k + 1 : ℕ) * bv / κ) ^ r

def Gam (k r : ℕ) (T T' κ b CA bv : ℝ) : ℝ :=
  2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) * H1 k r T κ b CA bv * H1 k r T' κ b CA bv

theorem IsRange.gap_opp {lam : Fin (2 * r + k + 1) → ℝ} {c h q : ℝ} (H : IsRange k r lam c h q)
    {a b : Fin (2 * r + k + 1)} (hab : sgnCN k r a ≠ sgnCN k r b) : 100 * q ≤ |lam a - lam b| := by
  obtain ⟨hc, hg, hq, -⟩ := H
  rcases le_or_gt q 0 with h0 | h0
  · exact le_trans (by linarith) (abs_nonneg _)
  refine le_trans ?_ (hg a b hab)
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : 1 ≤ Real.sqrt (2 * r + 2) := Real.one_le_sqrt.2 (by linarith)
  have hm : c ≤ max 1 c := le_max_right _ _
  have h1 : c * (100 * q) ≤ 100 * max 1 c * q := by nlinarith
  have h2 : 100 * max 1 c * q ≤ 100 * max 1 c * q * Real.sqrt (2 * r + 2) :=
    le_mul_of_one_le_right (by positivity) hs
  exact le_of_mul_le_mul_left (h1.trans (h2.trans hq)) hc

theorem sgnCN_succ_ne {a b : Fin (2 * r + k + 1)} (ha : k - 1 ≤ a.val) (hb : b.val = a.val + 1) :
    sgnCN k r a ≠ sgnCN k r b := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : ¬ b.val < k - 1 := by omega
  simp only [sgnCN, h1, h2, if_false, ne_eq, decide_eq_decide]
  omega

theorem IsRange.le_bv {lam : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (hk : 1 ≤ k) (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) : 100 * q ≤ bv := by
  have h1 := H.gap_opp (sgnCN_succ_ne (a := ⟨k - 1, by omega⟩) (b := ⟨k, by omega⟩) le_rfl (by simp; omega))
  have h2 := S.2.2 ⟨k - 1, by omega⟩ le_rfl
  have h3 := S.2.2 ⟨k, by omega⟩ (by simp)
  refine h1.trans (abs_le.2 ⟨?_, ?_⟩) <;> linarith [h2.1, h2.2, h3.1, h3.2]

theorem IsRange.le_gap {lam : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) {a b : Fin (2 * r + k + 1)} (hab : a < b) : 100 * q ≤ lam a - lam b := by
  have hab' : a.val < b.val := hab
  have hpos : lam b < lam a := S.1.1 hab
  by_cases hb : b.val < k - 1
  · have h1 := H.2.2.2 a b hab hb
    rcases le_or_gt q 0 with h0 | h0
    · linarith
    · have : 1 ≤ max 1 c := le_max_left _ _
      nlinarith
  by_cases ha : a.val < k - 1
  · have h1 := H.le_bv (by omega) S
    have h2 := (S.2.1 a ha).1
    have h3 := (S.2.2 b (by omega)).2
    linarith
  · have hlt : a.val + 1 < 2 * r + k + 1 := by have := b.2; omega
    have h1 := H.gap_opp (sgnCN_succ_ne (a := a) (b := ⟨a.val + 1, hlt⟩) (by omega) rfl)
    have h2 : lam ⟨a.val + 1, hlt⟩ < lam a := S.1.1 (show a.val < a.val + 1 by omega)
    have h3 : lam b ≤ lam ⟨a.val + 1, hlt⟩ := S.1.1.antitone (show a.val + 1 ≤ b.val by omega)
    rw [abs_of_pos (by linarith)] at h1
    linarith

theorem abs_add_abs_le_dist1 {n : ℕ} (μ lam : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    |μ a - lam a| + |μ b - lam b| ≤ dist1 μ lam := by
  rw [← Finset.sum_pair (f := fun a => |μ a - lam a|) hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _

theorem InPP.gap_ge {lam μ : Fin (2 * r + k + 1) → ℝ} {bv c h q : ℝ} (hμ : InPP lam q μ) (S : IsShape k r lam bv)
    (H : IsRange k r lam c h q) {a b : Fin (2 * r + k + 1)} (hab : a < b) :
    99 / 100 * (lam a - lam b) ≤ μ a - μ b := by
  have h1 := H.le_gap S hab
  have h2 := (abs_add_abs_le_dist1 μ lam hab.ne).trans hμ.2
  have h3 := neg_abs_le (μ a - lam a)
  have h4 := le_abs_self (μ b - lam b)
  linarith


namespace Ex

open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def stdRep (k r : ℕ) : HRep k r where
  H := EuclideanSpace ℂ (Fin (2 * r + k + 1))
  σ := fun g => Matrix.toEuclideanCLM (𝕜 := ℂ) g

def detRep (k r : ℕ) (μ : Fin (2 * r + k + 1) → ℝ) : HRep k r where
  H := ℂ
  σ := fun g => (g.det ^ ⌊μ 0⌋₊) • ContinuousLinearMap.id ℂ ℂ


theorem contDiff_entry (i j : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g : Mat k r => g i j) :=
  (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin (2 * r + k + 1) → ℂ) i)

theorem contDiff_det : ContDiff ℝ ∞ (fun g : Mat k r => g.det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => ContDiff.mul contDiff_const (contDiff_prod fun i _ => contDiff_entry (s i) i)



theorem subsingleton_idx_top : Subsingleton (Idx k r (2 * r + k + 1)) :=
  ⟨fun I J => Subtype.ext (by
    rw [(Finset.card_eq_iff_eq_univ I.1).1 (by simpa using I.2),
      (Finset.card_eq_iff_eq_univ J.1).1 (by simpa using J.2)])⟩

attribute [local instance] subsingleton_idx_top

theorem idx_univ (I : Idx k r (2 * r + k + 1)) : I.1 = Finset.univ :=
  (Finset.card_eq_iff_eq_univ I.1).1 (by simpa using I.2)





theorem subsingleton_idx_zero : Subsingleton (Idx k r 0) :=
  ⟨fun I J => Subtype.ext ((Finset.card_eq_zero.mp I.2).trans (Finset.card_eq_zero.mp J.2).symm)⟩

attribute [local instance] subsingleton_idx_zero



example : (List.finRange 5).map (sgnCN 2 1) = [true, true, false, true, false] := by decide

end Ex

end GlobalTheory.Mom
end
end

section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

variable {k r : ℕ}

def Setup (k r : ℕ) (c Ch : ℝ) (P : Mat k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv h q : ℝ)
    (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) : Prop :=
  IsCayleyU k r (sgnCN k r) P ∧ IsShape k r lam bv ∧ IsRange k r lam c h q ∧
    Ch * (2 * r + 2 : ℝ) ^ (9 / 2 : ℝ) *
      (3 * (r + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ≤ h ∧
    ∀ μ, InPP lam q μ → (R μ).IsDSAt P μ

def Standing (k r : ℕ) (c Ch Cg C₀ : ℝ) (P : Mat k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv h q : ℝ)
    (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) : Prop :=
  1 ≤ k ∧ 0 < c ∧ 915 ≤ Ch ∧ 1 ≤ Cg ∧ 10 ^ 4 ≤ C₀ ∧ 0 ≤ q ∧ Setup k r c Ch P lam bv h q R ∧
    (∀ i j, i < j → Cg * (2 * r + 2 : ℝ) ^ 3 ≤ lam i - lam j) ∧ C₀ * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧
    ∀ μ, InPP lam (q + r + 2) μ → (R μ).IsDSAt P μ

structure Flag (k r : ℕ) where
  z : Fin (2 * r + k + 1) → ℂ
  u : Fin k → ℝ
  W : Type
  [nG : NormedAddCommGroup W]
  [iP : InnerProductSpace ℂ W]
  π : Mat k r → (W →L[ℂ] W)
  cψ : ℂ
  μG : Measure (Mt k r)
  μS : Measure (Mt k r)
  ν : Measure (Mt k r)

attribute [instance] Flag.nG Flag.iP

def Flag.Ok (F : Flag k r) (κ : ℝ) : Prop :=
  inWb k r F.z ∧ 0 < Tz k r F.z ∧ IsHCTypeW k r F.z F.u F.π ∧ 0 < κ ∧ ‖F.cψ‖ = 2 * κ ∧ IsMeasSG F.z F.μG F.μS F.ν

def Flag.Size (F : Flag k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv b : ℝ) : Prop :=
  InterlaceS (by omega) F.u lam ∧ (∀ s, |lam s| ≤ b) ∧ (∀ i, |F.u i| ≤ b) ∧ bv ≤ b

def Flag.Iso (F : Flag k r) (A : HRep k r) (B : A.H → F.W) : Prop := A.IsIsoB F.z F.cψ F.π F.ν B

def el (I : Idx k r 1) : Fin (2 * r + k + 1) := I.1.orderEmbOfFin I.2 0

def HRep.EE (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -∑ c, A.E P (el b) (el c) (x c)

def HRep.EEd (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -A.E P (el b) (el b) (x b)

def HRep.EEo (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -∑ c ∈ univ.erase b, A.E P (el b) (el c) (x c)


def xS (μ : Fin (2 * r + k + 1) → ℝ) (s : Idx k r 1) : ℝ := -μ (el s) + (1 - ((2 * r + k + 1 : ℕ) : ℝ)) / 2

def VV (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (P : Mat k r) (μ : Fin (2 * r + k + 1) → ℝ)
    (p : ∀ I : Idx k r 1, (Idx k r 1 → (R μ).H) → (R (μ + wtI true I)).H) (j : ℕ) : Set (Idx k r 1 → (R μ).H) :=
  {x | (R μ).SmT x ∧ ∀ s, p s x ∈ (R (μ + wtI true s)).filt P μ (j + 1)}

section Proj

variable (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (μ : Fin (2 * r + k + 1) → ℝ)
  (ι : ∀ I : Idx k r 1, (R (μ + wtI true I)).H → Idx k r 1 → (R μ).H)
  (p : ∀ I : Idx k r 1, (Idx k r 1 → (R μ).H) → (R (μ + wtI true I)).H)

def prS (s : Idx k r 1) (x : Idx k r 1 → (R μ).H) : Idx k r 1 → (R μ).H := ι s (p s x)

def prCloud (x : Idx k r 1 → (R μ).H) : Idx k r 1 → (R μ).H :=
  ∑ s ∈ univ.filter (fun s : Idx k r 1 => (el s).val < k - 1), prS R μ ι p s x

def prNode (x : Idx k r 1 → (R μ).H) : Idx k r 1 → (R μ).H :=
  ∑ s ∈ univ.filter (fun s : Idx k r 1 => ¬ (el s).val < k - 1), prS R μ ι p s x

variable {R μ ι p}


end Proj

def HypJ (k r : ℕ) (bv : ℝ) (j : ℕ) : Prop :=
  ((j : ℝ) + 2) * (8704 * ((2 * r + k + 1 : ℕ) : ℝ)) ≤ bv ∧ 8704 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ bv

def bStar {n : ℕ} (μ : Fin n → ℝ) : ℝ := ‖μ‖ + n

def QQ (r : ℕ) (bv : ℝ) : ℝ := 4 + 9 * (2 * r + 2 : ℝ) * (6 * bv) ^ (2 * (2 * r + 2) - 2)

def HRep.expect (A : HRep k r) {W : Type} [NormedAddCommGroup W] (ν : Measure (Mt k r)) (B : A.H → W)
    (φ : Mat k r → ℝ) (w : A.H) : ℝ≥0∞ := A.mass ν B φ w / ‖w‖ₑ ^ 2



def MomAll (A : HRep k r) (F : Flag k r) (B : A.H → F.W) (H : ℝ) (q : ℕ) (w : A.H) : Prop :=
  (∀ a, A.mass F.ν B (fun g => lA k r F.z g a ^ (2 * q)) w ≤ ENNReal.ofReal (H ^ (2 * q)) * ‖w‖ₑ ^ 2 ∧
    A.mass F.ν B (fun g => (lA k r F.z g a)⁻¹ ^ (2 * q)) w ≤ ENNReal.ofReal (H ^ (2 * q)) * ‖w‖ₑ ^ 2) ∧
  ∀ t : ℝ, 0 < t → A.mass F.ν B (Set.indicator {g | ∃ a, t * H ≤ max (lA k r F.z g a) (lA k r F.z g a)⁻¹} 1) w ≤
    ENNReal.ofReal ((2 * r + 2 : ℝ) * (t ^ (2 * q))⁻¹) * ‖w‖ₑ ^ 2

def MomProd (A : HRep k r) (F : Flag k r) (B : A.H → F.W) (H : ℝ) {l : ℕ} (hl : l ≤ r + 1) (q : ℕ) (w : A.H) : Prop :=
  A.mass F.ν B (fun g => (∏ a : Fin l, lA k r F.z g (Fin.castLE hl a)) ^ (2 * q)) w ≤
    ENNReal.ofReal (H ^ (2 * q * l)) * ‖w‖ₑ ^ 2

theorem InPP.mono {n : ℕ} {lam μ : Fin n → ℝ} {s t : ℝ} (h : InPP lam s μ) (hst : s ≤ t) : InPP lam t μ :=
  ⟨h.1, h.2.trans hst⟩


theorem InPP.abs_le {n : ℕ} {lam μ : Fin n → ℝ} {t : ℝ} (h : InPP lam t μ) (a : Fin n) : |μ a - lam a| ≤ t :=
  (single_le_sum (f := fun a => |μ a - lam a|) (fun _ _ => abs_nonneg _) (mem_univ a)).trans h.2

theorem InPP.gap {n : ℕ} {lam μ : Fin n → ℝ} {t : ℝ} (h : InPP lam t μ) {a b : Fin n} (hab : a ≠ b) :
    lam a - lam b - t ≤ μ a - μ b := by
  have h1 := abs_add_abs_le_dist1 μ lam hab
  linarith [h.2, neg_abs_le (μ a - lam a), le_abs_self (μ b - lam b)]



section Conseq

variable {c Ch Cg C₀ bv h q : ℝ} {P : Mat k r} {lam μ : Fin (2 * r + k + 1) → ℝ}
  {R : (Fin (2 * r + k + 1) → ℝ) → HRep k r}



theorem IsRange.radius_le (hr : IsRange k r lam c h q) (hq : 0 ≤ q) : 100 * q ≤ h := by
  obtain ⟨hc, -, h0, -⟩ := hr
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 * r + 2) := Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have h2 : c * (100 * q) ≤ 100 * max 1 c * q := by nlinarith [le_max_right 1 c]
  have h3 : 0 ≤ 100 * max 1 c * q := le_trans (by positivity) h2
  refine le_of_mul_le_mul_left ?_ hc
  nlinarith

theorem IsRange.mono {q' : ℝ} (hr : IsRange k r lam c h q') (hq : q ≤ q') : IsRange k r lam c h q := by
  have h0 : 100 * max 1 c * q ≤ 100 * max 1 c * q' :=
    mul_le_mul_of_nonneg_left hq (by linarith [le_max_left 1 c])
  exact ⟨hr.1, hr.2.1, (mul_le_mul_of_nonneg_right h0 (Real.sqrt_nonneg _)).trans hr.2.2.1,
    fun i j hij hj => h0.trans (hr.2.2.2 i j hij hj)⟩

theorem Setup.mono {q' : ℝ} (hS : Setup k r c Ch P lam bv h q' R) (hq : q ≤ q') : Setup k r c Ch P lam bv h q R :=
  ⟨hS.1, hS.2.1, hS.2.2.1.mono hq, hS.2.2.2.1, fun μ hμ => hS.2.2.2.2 μ (hμ.mono hq)⟩

namespace Standing

theorem setup (H : Standing k r c Ch Cg C₀ P lam bv h q R) : Setup k r c Ch P lam bv h q R := H.2.2.2.2.2.2.1

theorem mono {q' : ℝ} (H : Standing k r c Ch Cg C₀ P lam bv h q' R) (h0 : 0 ≤ q) (hq : q ≤ q') :
    Standing k r c Ch Cg C₀ P lam bv h q R := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7, a8, a9, a10⟩ := H
  exact ⟨a1, a2, a3, a4, a5, h0, a7.mono hq, a8, a9, fun μ hμ => a10 μ (hμ.mono (by linarith))⟩


theorem radius_le_gap (H : Standing k r c Ch Cg C₀ P lam bv h q R) {i j : Fin (2 * r + k + 1)} (hij : i < j) :
    100 * q ≤ lam i - lam j :=
  H.setup.2.2.1.le_gap H.setup.2.1 hij



theorem gap_ge (H : Standing k r c Ch Cg C₀ P lam bv h q R) (hμ : InPP lam q μ) {i j : Fin (2 * r + k + 1)}
    (hij : i < j) : 0.98 * (lam i - lam j) ≤ μ i - μ j := by
  linarith [hμ.gap hij.ne, H.radius_le_gap hij, H.2.2.2.2.2.1]





theorem entries (H : Standing k r c Ch Cg C₀ P lam bv h q R) (hμ : InPP lam q μ) (i : Fin (2 * r + k + 1)) :
    (i.val < k - 1 → -q ≤ μ i ∧ μ i ≤ bv / 8 + q) ∧ (k - 1 ≤ i.val → -(2 * bv) - q ≤ μ i ∧ μ i ≤ -bv + q) := by
  have h1 := abs_le.1 (hμ.abs_le i)
  constructor
  · intro hi; have := H.setup.2.1.2.1 i hi; constructor <;> linarith
  · intro hi; have := H.setup.2.1.2.2 i hi; constructor <;> linarith


end Standing

end Conseq

example : bStar ![(1 : ℝ), -3] = 5 := by
  have : ‖![(1 : ℝ), -3]‖ = 3 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by fin_cases i <;> simp) ?_
    simpa using norm_le_pi_norm ![(1 : ℝ), -3] 1
  rw [bStar, this]; norm_num

example : QQ 0 1 = 652 := by norm_num [QQ]

example : HypJ 1 0 (10 ^ 5) 3 ∧ ¬ HypJ 1 0 (10 ^ 5) 4 := by norm_num [HypJ]

example (μ : Fin (2 * 0 + 1 + 1) → ℝ) (s : Idx 1 0 1) : xS μ s = -μ (el s) - 1 / 2 := by
  unfold xS; norm_num; ring

end GlobalTheory.Mom
end
end

section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.Inh

variable {k r : ℕ}

@[reducible] def uniqueIdxZero : Unique (Idx k r 0) :=
  ⟨⟨⟨∅, rfl⟩⟩, fun I => Subtype.ext (Finset.card_eq_zero.1 I.2)⟩

attribute [local instance] uniqueIdxZero

def z0 (k : ℕ) : Fin (2 * 0 + k + 1) → ℂ := bvec (wI k 0 (Fin.last k))

end GlobalTheory.Mom.Inh
end
end

section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

variable {k r : ℕ}

def LowestK : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ, IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    IsKTypeOf (sgnCN k r) (A.onJ P) (lowK (sgnCN k r) μ) (A.iso P (lowK (sgnCN k r) μ)) ∧
    ∀ a b, a < b → sgnCN k r a ≠ sgnCN k r b → A.iso P (lowK (sgnCN k r) μ - Formalism.REAL.root a b) = ⊥

def MomentCor : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q₀ b : ℝ) R, Setup k r c Ch P lam bv h q₀ R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → 1 ≤ Tz k r F.z → ∀ (j q : ℕ) μ B, F.Iso (R μ) B →
      ∀ w ∈ (R μ).filt P μ j,
        (InPP lam (q₀ - ((r + 1) * q : ℕ)) μ → HypJ k r bv (j + 2 * ((r + 1) * q)) →
          MomAll (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) q w) ∧
        ∀ (l : ℕ) (hl : l ≤ r + 1), InPP lam (q₀ - ((r + 1) * l * q : ℕ)) μ → HypJ k r bv (j + 2 * ((r + 1) * l * q)) →
          MomProd (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) hl q w

def LowAny : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (F : Flag k r) (κ : ℝ), IsCayleyU k r (sgnCN k r) P → IsHCParam μ →
    A.IsDSAt P μ → F.Ok κ → ∀ B, F.Iso A B → ∀ φ : Mat k r → ℝ, Measurable (fun x : Mt k r => φ (Matrix.of x)) →
      (∀ g ∈ UH (Hpk k r), ∀ s ∈ Sset k r F.z, φ (s * g) = φ g) →
      (∀ g ∈ UH (Hpk k r), ∀ t ∈ UH (Hpk k r), t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → φ (g * t) = φ g) →
      ∀ w ∈ A.iso P (lowK (sgnCN k r) μ), ∀ w₀ ∈ A.iso P (lowK (sgnCN k r) μ), ‖w‖ = ‖w₀‖ →
        A.mass F.ν B φ w = A.mass F.ν B φ w₀

def MomentLow : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q₀ b : ℝ) R, Setup k r c Ch P lam bv h q₀ R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → 1 ≤ Tz k r F.z → ∀ (q : ℕ) μ B, F.Iso (R μ) B →
      ∀ w ∈ (R μ).iso P (lowK (sgnCN k r) μ),
        (InPP lam (q₀ - ((r + 1) * q : ℕ)) μ → HypJ k r bv (2 * ((r + 1) * q)) →
          MomAll (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) q w) ∧
        ∀ (l : ℕ) (hl : l ≤ r + 1), InPP lam (q₀ - ((r + 1) * l * q : ℕ)) μ → HypJ k r bv (2 * ((r + 1) * l * q)) →
          MomProd (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) hl q w

def Dsgn (dual : Bool) (z z' : Fin (2 * r + k + 1) → ℂ) {l : ℕ} (hl : l ≤ r + 1) (g : Mat k r) : ℂ :=
  if dual then star (Dmin k r z z' g ⟨l, by omega⟩) else Dmin k r z z' g ⟨l, by omega⟩

example (dual : Bool) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Dsgn dual z z' (Nat.zero_le _) g = 1 := by
  cases dual <;> simp [Dsgn, Dmin]

example : Dsgn (k := 1) (r := 0) false (Inh.z0 1) (Inh.z0 1) (l := 1) le_rfl 1 = -1 := by
  simp [Dsgn, Dmin, Zhat, fvec, herm, Inh.z0, bvec, wI, Hpk, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.single_apply]

end GlobalTheory.Mom
end
end
