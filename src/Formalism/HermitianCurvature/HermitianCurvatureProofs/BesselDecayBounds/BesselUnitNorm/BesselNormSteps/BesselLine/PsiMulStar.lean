import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine

section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

def SideHyp (D : D7) (Ch Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)) : Prop :=
  NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ ∧ IsDSHpk D.R.k D.R.rS L.ε μ σ ∧
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG ∧
    (inWb D.R.k D.R.rS z ∧ 0 < Tz D.R.k D.R.rS z) ∧ IsHCTypeW D.R.k D.R.rS z u π ∧
    (IsHaarOn (UWset D.R.k D.R.rS z) μW ∧ μW Set.univ = 1) ∧
    IsQuotMeas μG (muSof μW L.μN) νq

def PartA {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (l : H → Wp) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
    Integrable (fun p : Mt k r × Mt k r =>
      (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
      (μW.prod μN) ∧
    ∫ p : Mt k r × Mt k r,
      (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
      ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l w)

def PartB {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (μG νq : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) (l : H → Wp) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
    ENNReal.ofReal (‖l v‖ ^ 2) * l2SG νq (fun g => l (σ g w)) =
      ENNReal.ofReal (‖w‖ ^ 2 * ‖l v‖ ^ 2 / fdegH μG σ w)

def Eventually (P : D7 → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Ch Cq : ℝ, ∃ Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, P D Ch Cg Cq

theorem Eventually.and {P Q : D7 → ℝ → ℝ → ℝ → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually (fun D Ch Cg Cq => P D Ch Cg Cq ∧ Q D Ch Cg Cq) := by
  intro Ch Cq
  obtain ⟨a, ha⟩ := hP Ch Cq
  obtain ⟨b, hb⟩ := hQ Ch Cq
  exact ⟨max a b, fun Cg h D => ⟨ha Cg (le_trans (le_max_left _ _) h) D, hb Cg (le_trans (le_max_right _ _) h) D⟩⟩

theorem Eventually.mono {P Q : D7 → ℝ → ℝ → ℝ → Prop} (hP : Eventually P)
    (h : ∀ D Ch Cg Cq, P D Ch Cg Cq → Q D Ch Cg Cq) : Eventually Q := by
  intro Ch Cq
  obtain ⟨a, ha⟩ := hP Ch Cq
  exact ⟨a, fun Cg hc D => h _ _ _ _ (ha Cg hc D)⟩

end PI.WBL
end
end

section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

section Generic

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def beF (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w v : H) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def be (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) : Wp →L[ℂ] Wp :=
  ∫ p, beF z c π σ w v p ∂(μW.prod μN)

def hsSq [FiniteDimensional ℂ Wp] (A : Wp →L[ℂ] Wp) : ℝ :=
  ∑ i, ‖A (stdOrthonormalBasis ℂ Wp i)‖ ^ 2

def trW [FiniteDimensional ℂ Wp] (A : Wp →L[ℂ] Wp) : ℂ :=
  ∑ i, ⟪stdOrthonormalBasis ℂ Wp i, A (stdOrthonormalBasis ℂ Wp i)⟫_ℂ

def ConvAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  (∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (beF z c π σ w v) (μW.prod μN)) ∧
    (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∀ x : Wp,
      IsCWCont (k := k) (r := r) σ (fun w => be z c π μW μN σ w v x)) ∧
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H,
      IsKFinHpk (k := k) (r := r) σ v →
      be z c π μW μN σ (σ (h * m) w) v = (psi k r z c m • π h).comp (be z c π μW μN σ w v)) ∧
    (∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      IsKFinHpk (k := k) (r := r) σ w → IsKFinHpk (k := k) (r := r) σ v →
      ContinuousLinearMap.adjoint (be z c π μW μN σ w v) = be z c π μW μN σ v w)

def Mult1At (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B₁ B₂ : H → Wp, IsBesselMapSm z (psi k r z c) σ π B₁ → IsBesselMapSm z (psi k r z c) σ π B₂ →
    (∃ w ∈ smoothVecs (k := k) (r := r) σ, B₂ w ≠ 0) →
    ∃ a : ℂ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B₁ w = a • B₂ w

def KDenseAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B → (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → B v = 0) →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, B w = 0

def FSAt [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → 0 < fdegH μG σ w ∧
    (∀ᵐ x ∂νq, σ (Matrix.of x) w ∈ smoothVecs (k := k) (r := r) σ) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (fun x => hsSq (be z c π μW μN σ (σ (Matrix.of x) w) v)) νq ∧
      ∫ x, hsSq (be z c π μW μN σ (σ (Matrix.of x) w) v) ∂νq =
        ‖w‖ ^ 2 * (trW (be z c π μW μN σ v v)).re / fdegH μG σ w

end Generic

def Conv (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      ConvAt z L.c π μW L.μN σ

def Mult1 (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      Mult1At z L.c π σ

def KDense (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      KDenseAt z L.c π σ

def FS (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      FSAt z L.c π μW L.μN μG νq σ

end PI.WBL
end
end

section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

def GrpF (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r)) ∧
  (∀ a ∈ UH (Hpk k r), a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r)) ∧
  (∀ a ∈ UWset k r z, a⁻¹ ∈ UWset k r z) ∧ (∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, h⁻¹ * n * h ∈ Nset k r) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, h * n * h⁻¹ ∈ Nset k r) ∧
  (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, a * b ∈ UWset k r z)

def SigU {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
    ∀ a ∈ UH (Hpk k r), ∀ x : H, ‖σ a x‖ = ‖x‖

def PiU {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) : Prop :=
  π 1 = 1 ∧ (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, π (a * b) = (π a).comp (π b)) ∧
    ∀ a ∈ UWset k r z, ∀ x : Wp, ‖π a x‖ = ‖x‖

def PsiF (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Prop :=
  (∀ n ∈ Nset k r, ∀ m ∈ Nset k r, psi k r z c (n * m) = psi k r z c n * psi k r z c m) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, psi k r z c (h⁻¹ * n * h) = psi k r z c n) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, psi k r z c (h * n * h⁻¹) = psi k r z c n) ∧
  (∀ n ∈ Nset k r, psi k r z c n⁻¹ = star (psi k r z c n))

def tEq {k r : ℕ} (h m : Mx k r) (p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (fun i j => (Matrix.of p.1 * h) i j, fun i j => (h⁻¹ * Matrix.of p.2 * h * m) i j)

def tInv {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (fun i j => (Matrix.of p.1)⁻¹ i j, fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) i j)

def MeasF {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r)) : Prop :=
  (∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) ∧
  (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, MeasurePreserving (tEq h m) (μW.prod μN) (μW.prod μN)) ∧
  MeasurePreserving tInv (μW.prod μN) (μW.prod μN) ∧
  AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹) μW

def DecayAt {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μW μN : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∃ (C : ℝ) (Ws : List (List (Mx k r))),
    (∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ,
      Integrable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ) (μW.prod μN) ∧
      ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN) ≤
        C * (Ws.map fun W => ‖dsigW σ W w‖).sum

section Lemmas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem opNorm_le_one_of_iso {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : E →L[ℂ] E)
    (h : ∀ x, ‖A x‖ = ‖x‖) : ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound A zero_le_one (fun x => by rw [h, one_mul])

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ell_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finset_sum _ (fun a _ => ?_)
  split_ifs
  · exact continuous_id.matrix_elem _ _
  · first
      | fun_prop
      | (simp only [dotProduct]
         exact continuous_finset_sum _ (fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const))

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous (psi k r z c) := by
  unfold psi
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (ell_cont z))))).cexp

theorem adjoint_eq_of_iso {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hA : ∀ x, ‖A x‖ = ‖x‖) (hAB : A.comp B = 1) : ContinuousLinearMap.adjoint A = B := by
  have h1 : (ContinuousLinearMap.adjoint A).comp A = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self A).1 hA
  ext x
  have e1 : A (B x) = x := by
    rw [← ContinuousLinearMap.comp_apply, hAB, ContinuousLinearMap.one_apply]
  calc ContinuousLinearMap.adjoint A x = ContinuousLinearMap.adjoint A (A (B x)) := by rw [e1]
    _ = ((ContinuousLinearMap.adjoint A).comp A) (B x) := rfl
    _ = B x := by rw [h1, ContinuousLinearMap.one_apply]

theorem beF_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (w v : H)
    (hπm : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹) μW)
    (hco : AEStronglyMeasurable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      (μW.prod μN)) :
    AEStronglyMeasurable (beF z c π σ w v) (μW.prod μN) := by
  have hps : Continuous fun p : Mt k r × Mt k r => star (psi k r z c (Matrix.of p.2)) :=
    (continuous_star.comp (psi_cont z c)).comp continuous_snd
  have hπ2 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹) (μW.prod μN) := by
    first
      | exact hπm.comp_fst
      | exact hπm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      | exact hπm.prod_fst
  exact (hco.mul hps.aestronglyMeasurable).smul hπ2

theorem norm_beF_le (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) (hG : GrpF k r z) (hπ : PiU z π) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z) :
    ‖beF z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have hinv : (Matrix.of p.1)⁻¹ ∈ UWset k r z := hG.2.2.1 _ hp
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 := opNorm_le_one_of_iso _ (hπ.2.2 _ hinv)
  unfold beF
  rw [norm_smul, norm_mul, norm_star, norm_psi, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn

theorem conv_int (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hπ : PiU z π) (hM : MeasF z π μW μN) (hD : DecayAt μW μN σ) :
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (beF z c π σ w v) (μW.prod μN) := by
  intro w hw v hv
  obtain ⟨C, Ws, -, hb⟩ := hD v hv
  have hint := (hb w hw).1
  refine Integrable.mono' hint.norm (beF_aesm z c π μW μN σ w v hM.2.2.2 hint.aestronglyMeasurable) ?_
  exact hM.1.mono (fun p hp => norm_beF_le z c π σ w v hG hπ p hp.1)

theorem conv_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hπ : PiU z π) (hM : MeasF z π μW μN) (hD : DecayAt μW μN σ) :
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∀ x : Wp,
      IsCWCont (k := k) (r := r) σ (fun w => be z c π μW μN σ w v x) := by
  intro v hv x
  obtain ⟨C, Ws, hWs, hb⟩ := hD v hv
  refine ⟨C * ‖x‖, Ws, hWs, fun w hw => ?_⟩
  have hint := (hb w hw).1
  have hF := conv_int z c π μW μN σ hG hπ hM hD w hw v hv
  have h1 : ‖be z c π μW μN σ w v x‖ ≤ ‖be z c π μW μN σ w v‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖be z c π μW μN σ w v‖ ≤ ∫ p, ‖beF z c π σ w v p‖ ∂(μW.prod μN) :=
    norm_integral_le_integral_norm _
  have h3 : ∫ p, ‖beF z c π σ w v p‖ ∂(μW.prod μN) ≤
      ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN) :=
    integral_mono_ae hF.norm hint.norm (hM.1.mono (fun p hp => norm_beF_le z c π σ w v hG hπ p hp.1))
  have h4 := (hb w hw).2
  calc ‖be z c π μW μN σ w v x‖ ≤ ‖be z c π μW μN σ w v‖ * ‖x‖ := h1
    _ ≤ (C * (Ws.map fun W => ‖dsigW σ W w‖).sum) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (h2.trans (h3.trans h4)) (norm_nonneg _)
    _ = C * ‖x‖ * (Ws.map fun W => ‖dsigW σ W w‖).sum := by ring

end Lemmas

end PI.WBL.Cv
end
end

section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem psi_mul_star (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) :
    psi k r z c g * star (psi k r z c g) = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  simp <;> ring

theorem beF_tEq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c)
    (h m : Mx k r) (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (w v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    beF z c π σ (σ (h * m) w) v p =
      (psi k r z c m • π h).comp (beF z c π σ w v (tEq h m p)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  obtain ⟨hs1, hsm, hsn⟩ := hσ
  obtain ⟨hp1, hpm, hpn⟩ := hπ
  obtain ⟨ψ1, ψ2, ψ3, ψ4⟩ := hψ
  obtain ⟨hP1, hP2⟩ := hp
  have hhU : h ∈ UH (Hpk k r) := hh.1
  have hmU : m ∈ UH (Hpk k r) := hm.1
  have hP1U : Matrix.of p.1 ∈ UH (Hpk k r) := hP1.1
  have hP2U : Matrix.of p.2 ∈ UH (Hpk k r) := hP2.1
  have hinv : h * h⁻¹ = 1 := (g2 h hhU).1
  have e1 : Matrix.of (tEq h m p).1 = Matrix.of p.1 * h := rfl
  have e2 : Matrix.of (tEq h m p).2 = h⁻¹ * Matrix.of p.2 * h * m := rfl
  have hQ : Matrix.of p.1 * h * (h⁻¹ * Matrix.of p.2 * h * m) =
      Matrix.of p.1 * Matrix.of p.2 * (h * m) := by
    calc _ = Matrix.of p.1 * (h * h⁻¹) * Matrix.of p.2 * (h * m) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv, Matrix.mul_one]
  have hσw : σ (Matrix.of p.1 * Matrix.of p.2) (σ (h * m) w) =
      σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w := by
    rw [hsm _ (g1 _ hP1U _ hP2U) _ (g1 _ hhU _ hmU)]
    rfl
  have hn : h⁻¹ * Matrix.of p.2 * h ∈ Nset k r := g5 h hh _ hP2
  have hψQ : psi k r z c (h⁻¹ * Matrix.of p.2 * h * m) = psi k r z c (Matrix.of p.2) * psi k r z c m := by
    rw [ψ1 _ hn _ hm, ψ2 h hh _ hP2]
  have hπQ : (π h).comp (π (Matrix.of p.1 * h)⁻¹) = π (Matrix.of p.1)⁻¹ := by
    have hu : h⁻¹ * (Matrix.of p.1)⁻¹ ∈ UWset k r z := g7 _ (g3 h hh) _ (g3 _ hP1)
    rw [Matrix.mul_inv_rev, ← hpm h hh _ hu, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hms := psi_mul_star z c m
  unfold beF
  rw [e1, e2, hQ, hσw, hψQ, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hπQ, smul_smul]
  congr 1
  rw [star_mul]
  first
  | linear_combination (-(⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w⟫_ℂ *
      star (psi k r z c (Matrix.of p.2)))) * hms
  | linear_combination (⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * (h * m)) w⟫_ℂ *
      star (psi k r z c (Matrix.of p.2))) * hms


def adjR (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] :
    (Wp →L[ℂ] Wp) →ₗᵢ[ℝ] (Wp →L[ℂ] Wp) where
  toFun T := ContinuousLinearMap.adjoint T
  map_add' S T := map_add _ S T
  map_smul' a T := by
    show ContinuousLinearMap.adjoint (a • T) = a • ContinuousLinearMap.adjoint T
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a T,
      RCLike.real_smul_eq_coe_smul (K := ℂ) a (ContinuousLinearMap.adjoint T),
      LinearIsometryEquiv.map_smulₛₗ]
    simp
  norm_map' T := ContinuousLinearMap.adjoint.norm_map T

theorem beF_tInv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c)
    (w v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    beF z c π σ v w (tInv p) = ContinuousLinearMap.adjoint (beF z c π σ w v p) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG
  obtain ⟨hs1, hsm, hsn⟩ := hσ
  obtain ⟨hp1, hpm, hpn⟩ := hπ
  obtain ⟨ψ1, ψ2, ψ3, ψ4⟩ := hψ
  obtain ⟨hP1, hP2⟩ := hp
  have hP1U : Matrix.of p.1 ∈ UH (Hpk k r) := hP1.1
  have hP2U : Matrix.of p.2 ∈ UH (Hpk k r) := hP2.1
  have hAU : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := g1 _ hP1U _ hP2U
  have e1 : Matrix.of (tInv p).1 = (Matrix.of p.1)⁻¹ := rfl
  have e2 : Matrix.of (tInv p).2 = Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ := rfl
  have hQ : (Matrix.of p.1)⁻¹ * (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
      (Matrix.of p.1 * Matrix.of p.2)⁻¹ := by
    rw [Matrix.mul_inv_rev]
    calc _ = ((Matrix.of p.1)⁻¹ * Matrix.of p.1) * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(g2 _ hP1U).2.1, Matrix.one_mul]
  have hψQ : psi k r z c (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) =
      star (psi k r z c (Matrix.of p.2)) := by
    rw [ψ3 _ hP1 _ (g4 _ hP2), ψ4 _ hP2]
  have hσadj : ⟪w, σ (Matrix.of p.1 * Matrix.of p.2)⁻¹ v⟫_ℂ = ⟪σ (Matrix.of p.1 * Matrix.of p.2) w, v⟫_ℂ := by
    set A := Matrix.of p.1 * Matrix.of p.2 with hAdef
    have hAi := g2 A hAU
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ A : H →ₗ[ℂ] H), norm_map' := hsn A hAU }
    have hv : σ A (σ A⁻¹ v) = v := by
      rw [← ContinuousLinearMap.comp_apply, ← hsm A hAU _ hAi.2.2, hAi.1, hs1, ContinuousLinearMap.one_apply]
    calc ⟪w, σ A⁻¹ v⟫_ℂ = ⟪L w, L (σ A⁻¹ v)⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪σ A w, σ A (σ A⁻¹ v)⟫_ℂ := rfl
      _ = ⟪σ A w, v⟫_ℂ := by rw [hv]
  have hπadj : ContinuousLinearMap.adjoint (π (Matrix.of p.1)⁻¹) = π ((Matrix.of p.1)⁻¹)⁻¹ := by
    set A := (Matrix.of p.1)⁻¹ with hAdef
    have hA : A ∈ UWset k r z := g3 _ hP1
    have hAi : A⁻¹ ∈ UWset k r z := g3 _ hA
    have h1 : A * A⁻¹ = 1 := (g2 A hA.1).1
    let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π A : Wp →ₗ[ℂ] Wp), norm_map' := hpn A hA }
    have hx : ∀ x : Wp, π A (π A⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.comp_apply, ← hpm A hA _ hAi, h1, hp1, ContinuousLinearMap.one_apply]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    calc ⟪π A⁻¹ x, y⟫_ℂ = ⟪L (π A⁻¹ x), L y⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪π A (π A⁻¹ x), π A y⟫_ℂ := rfl
      _ = ⟪x, π A y⟫_ℂ := by rw [hx]
  unfold beF
  rw [e1, e2, hQ, hψQ, star_star, hσadj, LinearIsometryEquiv.map_smulₛₗ, hπadj]
  congr 1
  simp only [map_mul, inner_conj_symm, Complex.star_def, Complex.conj_conj]



end PI.WBL.Cv
end
end
