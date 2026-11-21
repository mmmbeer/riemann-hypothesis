import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SemiCharImg
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ConstCopies
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.TripleSumIndep
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.MuOneOfSplit
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable (D : Car)

def SD {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSDLat D.host.E N L

def DetMul : Prop :=
  ∀ N (L L' L'' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → SD D L → SD D L' → SD D L'' →
    TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L''

def DetSmul : Prop :=
  letI := D.host.cmStar
  ∀ N (L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    Even N → SD D L₀ → SD D L →
    TaylorLogMetric.detId D L₀ (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) =
      Submodule.span (𝓞 D.host.E) {(γ : Matrix (Fin N) (Fin N) D.host.E).det} * TaylorLogMetric.detId D L₀ L

def IopSelf : Prop :=
  ∀ (T : TaylorLogMetric.Tor D) (N N' : ℕ) (La' : AddSubgroup (TaylorLogMetric.VC D N N')), ∀ G ∈ TaylorLogMetric.ThSp D T La',
    TaylorLogMetric.Iop D T La' La' G = G

def SqP (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L₁ L') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L'') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L L'') G)

def Tr0L (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N'))
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N')) G

def Tr0R (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'')
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'') G

def PullIop (T : TaylorLogMetric.Tor D) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L₁' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G ∈
                      TaylorLogMetric.Th D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
                        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') ∧
      TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L₁') G) =
        TaylorLogMetric.Iop D T
          (TaylorLogMetric.La D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'))
          (TaylorLogMetric.La D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L₁)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L₁'))
          (TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G)

variable {D}
variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1 (B : Cd.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ : Matrix.unitaryGroup (Fin N) D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2 (B : Cd.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ' : Matrix.unitaryGroup (Fin N') D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N'))

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

theorem formV_herm' (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (Ker.formV A n N N') := by
  intro x y
  simp [Ker.formV, map_sum, mul_comm]

theorem mem_ThSp_of' (D : Car) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' := by
  obtain ⟨ha, hf⟩ := h
  exact ⟨differentiableOn_univ.mp ha.differentiableOn, fun x hx z => hf x hx z⟩

theorem Iop_smul' (D : Car) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Iop D T La₁ La₂ (fun v => c * G v) z = c * TaylorLogMetric.Iop D T La₁ La₂ G z := by
  simp only [TaylorLogMetric.Iop, TaylorLogMetric.U]
  rw [mul_left_comm c, ← smul_eq_mul c (finsum _), smul_finsum]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [smul_eq_mul]
  ring

def SmulSD (D : Car) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    SD D L → SD D (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)

def NormOneUnitIdeal (D : Car) : Prop :=
  letI := D.host.cmStar
  ∀ z : unitary D.host.E, TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)})

section Paths

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

theorem admissible_of_integral_conj_le {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hN : Even N) (hN' : Even N') (h : SD D L) (h' : SD D L') :
    TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', h, h'⟩

theorem sd0 (N : ℕ) : SD D (StandardLatticesGL3.stdL D N) := Formalism.L2.Ker.Cd.Inhab.stdL_isSD D N

theorem mvTh (hL : B.LatAll) {N N' : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h1 : TaylorLogMetric.admitted D N N' L₁ L₁') (h2 : TaylorLogMetric.admitted D N N' L₂ L₂')
    {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁')) :
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') G ∈
      Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor L₂ L₂') :=
  Formalism.L2.Th1.H.interTh _ _ (formV_herm' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L₂ L₂' h2).2 (hL.2 N N' _ _ _ _ h1 h2).1 _ hG

variable {B}

theorem S1 (hSq : SqP D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N')
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hLs : SD D L) (hX : SD D X) :
    B.thMoved N N' L X = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X) (TaylorLogMetric.La D B.tor L X)
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X)
        (B.thZero N N')) :=
  hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') X hN hN' (sd0 N) hLs (sd0 N') hX (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)

theorem e1path (hSq : SqP D B.tor) (hR : Tr0R D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (h1 : SD D L') (h2 : SD D L'') :
    B.thMoved N N' L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved N N' L L') := by
  have hΦ := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) h0
  rw [S1 hSq hL hN hN' h0 hLs h2, S1 hSq hL hN hN' h0 hLs h1,
    hSq N N' (StandardLatticesGL3.stdL D N) L L' L'' hN hN' (sd0 N) hLs h1 h2 _ (mem_ThSp_of' _ _ _ _ hΦ),
    hR N N' L' L'' hN hN' h1 h2 _ (mem_ThSp_of' _ _ _ _ h0)]

theorem e2path (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (hL1 : SD D L₁) (h1 : SD D L') :
    B.thMoved N N' L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved N N' L L') := by
  have hθ : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of' D B.tor _ _ h0
  have hH : B.thHalf N N' L ∈ TaylorLogMetric.Th D B.tor L (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of' D B.tor _ _ (mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))
      (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) (G := B.thZero N N') h0)
  have e : B.thHalf N N' L₁ = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) (B.thHalf N N' L) :=
    (hTL N N' L L₁ hN hN' hLs hL1 _ hθ).symm
  show TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ L') (B.thHalf N N' L₁) =
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thHalf N N' L))
  rw [e]
  exact hSq N N' L L₁ (StandardLatticesGL3.stdL D N') L' hN hN' hLs hL1 (sd0 N') h1 _ hH

end Paths

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

theorem iopSelf (D : Car) : IopSelf D := by
  intro T N N' La' G hG
  funext z
  have hq : ∀ q : ↥La' ⧸ La'.addSubgroupOf La', q = 0 := by
    intro q
    refine QuotientAddGroup.induction_on q fun x => ?_
    exact (QuotientAddGroup.eq_zero_iff x).2 (by simp [AddSubgroup.addSubgroupOf_self])
  have hidx : (La'.addSubgroupOf La').index = 1 := by
    rw [AddSubgroup.addSubgroupOf_self, AddSubgroup.index_top]
  simp only [TaylorLogMetric.Iop, hidx, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul]
  rw [finsum_eq_single _ 0 (fun q hq' => absurd (hq q) hq')]
  exact hG.2 _ (Quotient.out (0 : ↥La' ⧸ La'.addSubgroupOf La')).2 z

section Chi

variable {D : Car}

theorem character_factor_change_right (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN' : Even N')
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h1 : SD D L') (h2 : SD D L'') :
    Cd.Base.chiFac χ N N' L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Cd.Base.chiFac χ N N' L L' := by
  unfold Cd.Base.chiFac
  rw [hM N' (StandardLatticesGL3.stdL D N') L' L'' hN' (sd0 N') h1 h2,
    hχ.1 _ _ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h1)
      (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' h1 h2), mul_zpow]
  ring

theorem character_factor_change_left (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN : Even N)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h1 : SD D L) (h2 : SD D L₁) :
    Cd.Base.chiFac χ N N' L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Cd.Base.chiFac χ N N' L L' := by
  unfold Cd.Base.chiFac
  rw [hM N (StandardLatticesGL3.stdL D N) L L₁ hN (sd0 N) h1 h2,
    hχ.1 _ _ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1)
      (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN h1 h2), mul_zpow]
  ring

theorem emb_star_unit (τ : D.what₂.Tau) (x : D.host.E) (hx : letI := D.host.cmStar; x * star x = 1) :
    (letI := D.host.cmStar; TaylorLogMetric.embT D τ (star x)) = (TaylorLogMetric.embT D τ x)⁻¹ := by
  letI := D.host.cmStar
  have h := congrArg (TaylorLogMetric.embT D τ) hx
  rw [map_mul, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

private theorem inv_mul_zpow_mul_inv_mul_zpow_neg (a b P Q : ℂ) (m n : ℕ) :
    (P⁻¹ * a) ^ (m : ℤ) * (Q⁻¹ * b) ^ (-(n : ℤ)) = a ^ (m : ℤ) * b ^ (-(n : ℤ)) * (P⁻¹ ^ m * Q ^ n) := by
  rw [mul_zpow, mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    inv_pow, inv_pow, inv_inv]
  ring

theorem character_factor_unitary_action (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hS : DetSmul D) (hU : NormOneUnitIdeal D) {N N' : ℕ}
    (hN : Even N) (hN' : Even N') :
    letI := D.host.cmStar
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E), SD D L → SD D L' →
    Cd.Base.chiFac χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') =
      Cd.Base.chiFac χ N N' L L' *
        ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) *
          (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2)) := by
  intro L L' γ γ' hL hL'
  letI := D.host.cmStar
  have hd : (γ : Matrix (Fin N) (Fin N) D.host.E).det ∈ unitary D.host.E :=
    Matrix.det_of_mem_unitary γ.2
  have hd' : (γ' : Matrix (Fin N') (Fin N') D.host.E).det ∈ unitary D.host.E :=
    Matrix.det_of_mem_unitary γ'.2
  have e1 := hS N (StandardLatticesGL3.stdL D N) L γ hN (sd0 N) hL
  have e2 := hS N' (StandardLatticesGL3.stdL D N') L' γ' hN' (sd0 N') hL'
  have c1 := hχ.1 (𝓞 D.host.E ∙ (γ : Matrix (Fin N) (Fin N) D.host.E).det) _ (hU ⟨_, hd⟩)
    (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ L hN (sd0 N) hL)
  have c2 := hχ.1 (𝓞 D.host.E ∙ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) _ (hU ⟨_, hd'⟩)
    (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ L' hN' (sd0 N') hL')
  have u1 : χ (𝓞 D.host.E ∙ (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ := hχ.2 ⟨_, hd⟩
  have u2 : χ (𝓞 D.host.E ∙ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det)⁻¹ := hχ.2 ⟨_, hd'⟩
  have s1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ :=
    Finset.prod_congr rfl fun τ _ => emb_star_unit τ _ hd.2
  simp only [Cd.Base.chiFac]
  rw [e1, e2, c1, c2, u1, u2, s1, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  exact inv_mul_zpow_mul_inv_mul_zpow_neg _ _ _ _ _ _

end Chi

section Pull

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem pull_smul (T : TaylorLogMetric.Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D T γ γ' (c • G) = c • TaylorLogMetric.pull D T γ γ' G := rfl

theorem pull_comp {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ' G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.mul_assoc]
  rfl

end Pull

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem Iop_smulF (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.Iop D T La₁ La₂ (c • G) = c • TaylorLogMetric.Iop D T La₁ La₂ G := by
  funext z
  simp only [TaylorLogMetric.Iop, TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm c, ← smul_eq_mul c (∑ᶠ _, _), smul_finsum]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [smul_eq_mul]
  ring

theorem e3a (hP : PullIop D B.tor) (hTL : Tr0L D B.tor) (hSm : SmulSD D) (hL : B.LatAll) (hJ : J1 B)
    {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D X →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L X) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) X := by
  intro γ L X hLs hXs
  have sS : ∀ n, SD D (StandardLatticesGL3.stdL D n) := fun n => Inhab.stdL_isSD D n
  have h1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := by simp
  have hs1 : ∀ Y : Submodule (𝓞 D.host.E) (Fin N' → D.host.E),
      SDLat.smulLat (1 : Matrix (Fin N') (Fin N') D.host.E) Y = Y := by
    intro Y
    simp [SDLat.smulLat]
  have hγS := hSm N (StandardLatticesGL3.stdL D N) γ (sS N)
  have hγL := hSm N L γ hLs
  have m0 : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := mem_ThSp_of' _ _ _ _ h0
  have mH : B.thHalf N N' L ∈ TaylorLogMetric.Th D B.tor L (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of' _ _ _ _ (mvTh B hL (admissible_of_integral_conj_le hN hN' (sS N) (sS N')) (admissible_of_integral_conj_le hN hN' hLs (sS N')) h0)
  have eB := (hP N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ 1 hN hN' (sS N) hLs (sS N')
    (sS N') _ m0).2
  have eA := (hP N N' L L (StandardLatticesGL3.stdL D N') X γ 1 hN hN' hLs hLs (sS N') hXs _ mH).2
  simp only [h1, hs1] at eA eB
  have eC := hJ N N' γ hN hN'
  have eE := hTL N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
    (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) hN hN' hγS hγL _ m0
  have eH : TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) 1 (B.thHalf N N' L) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) := by
    change TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) 1
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (B.thZero N N')) = _
    rw [eB, eC, Iop_smulF]
    congr 1
  simp only [Cd.Base.thMoved]
  rw [eA, eH, Iop_smulF]

theorem e3b (hP : PullIop D B.tor) (hSq : SqP D B.tor) (hTR : Tr0R D B.tor) (hSm : SmulSD D) (hL : B.LatAll)
    (hJ : J2 B) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L L') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' L (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') := by
  intro γ' L L' hLs hL's
  have sS : ∀ n, SD D (StandardLatticesGL3.stdL D n) := fun n => Inhab.stdL_isSD D n
  have h1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := by simp
  have hs1 : ∀ Y : Submodule (𝓞 D.host.E) (Fin N → D.host.E),
      SDLat.smulLat (1 : Matrix (Fin N) (Fin N) D.host.E) Y = Y := by
    intro Y
    simp [SDLat.smulLat]
  have hγS := hSm N' (StandardLatticesGL3.stdL D N') γ' (sS N')
  have hγL := hSm N' L' γ' hL's
  have m0 : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := mem_ThSp_of' _ _ _ _ h0
  have mH : TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (B.thZero N N') ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) L' :=
    mem_ThSp_of' _ _ _ _ (mvTh B hL (admissible_of_integral_conj_le hN hN' (sS N) (sS N')) (admissible_of_integral_conj_le hN hN' (sS N) hL's) h0)
  have sq1 := hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') L' hN hN' (sS N) hLs (sS N') hL's _ m0
  have sq2 := hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N')
    (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') hN hN' (sS N) hLs (sS N') hγL _ m0
  have eA := (hP N N' (StandardLatticesGL3.stdL D N) L L' L' 1 γ' hN hN' (sS N) hLs hL's hL's _ mH).2
  have eB := (hP N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') L' 1 γ' hN hN' (sS N) (sS N)
    (sS N') hL's _ m0).2
  simp only [h1, hs1] at eA eB
  have eC := hJ N N' γ' hN hN'
  have eI := iopSelf D B.tor N N' (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) _ m0
  have eR := hTR N N' (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N'))
    (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') hN hN' hγS hγL _ m0
  have eT : B.thMoved N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')))
        (B.thZero N N') := by
    simp only [Cd.Base.thMoved, Cd.Base.thHalf]
    rw [eI]
  simp only [Cd.Base.thMoved, Cd.Base.thHalf]
  rw [sq1, sq2, eA, eB, eC, Iop_smulF, Iop_smulF, eT, eR]

theorem reduction_of (hM : DetMul D) (hS : DetSmul D) (hU : NormOneUnitIdeal D) (hSm : SmulSD D)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hL : B.LatAll)
    (h0 : ∀ N N', Even N → Even N' → B.ThZeroMem N N')
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hP : PullIop D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) :
    B.EqP χ := by
  letI := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · intro N N' L L' hN hN' γ γ'
    have h1 := hSm N' L'.1 γ' L'.2
    show TaylorLogMetric.pull D B.tor _ _ (Cd.Base.chiFac χ N N' L.1 L'.1 • B.thMoved N N' L.1 L'.1) =
      Cd.Base.chiFac χ N N' _ _ • B.thMoved N N' _ _
    rw [pull_smul, pull_comp, e3b hP hSq hTR hSm hL hJ2 hN hN' (h0 N N' hN hN') γ' L.1 L'.1 L.2 L'.2, pull_smul,
      e3a hP hTL hSm hL hJ1 hN hN' (h0 N N' hN hN') γ L.1 _ L.2 h1, smul_smul, smul_smul,
      character_factor_unitary_action χ hχ hS hU hN hN' L.1 L'.1 γ γ' L.2 L'.2]
    congr 1
    ring
  · intro N N' L L' L'' hN hN'
    funext z
    show Cd.Base.chiFac χ N N' L.1 L''.1 * B.thMoved N N' L.1 L''.1 z =
      χ (TaylorLogMetric.detId D L'.1 L''.1) ^ (-((N / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Cd.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e1path hSq hTR hL hN hN' (h0 N N' hN hN') L.2 L'.2 L''.2,
      character_factor_change_right χ hχ hM hN' L.1 L'.2 L''.2]
    ring
  · intro N N' L L₁ L' hN hN'
    funext z
    show Cd.Base.chiFac χ N N' L₁.1 L'.1 * B.thMoved N N' L₁.1 L'.1 z =
      χ (TaylorLogMetric.detId D L.1 L₁.1) ^ (((N' / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Cd.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e2path hSq hTL hL hN hN' (h0 N N' hN hN') L.2 L₁.2 L'.2,
      character_factor_change_left χ hχ hM hN L'.1 L.2 L₁.2]
    ring

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Matrix
open Formalism.L2.Ker.Cd.IntegralLatticeDensity

variable (D : Car)

theorem detId_eq_vol {N : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    TaylorLogMetric.detId D L L' = DN.vol D L' * CU.cS D (DN.vol D L) := by
  refine le_antisymm ?_ (DN.vol_mul_cS_le D L L' (DN.sd_int D hL))
  have hu : DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
    le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)
  calc TaylorLogMetric.detId D L L' = TaylorLogMetric.detId D L L' * (DN.vol D L * CU.cS D (DN.vol D L)) := by
        rw [hu, mul_one]
    _ = TaylorLogMetric.detId D L L' * DN.vol D L * CU.cS D (DN.vol D L) := (mul_assoc _ _ _).symm
    _ ≤ DN.vol D L' * CU.cS D (DN.vol D L) := by
        have h := DN.detId_mul_vol_le D L L'
        rw [Submodule.mul_le]
        intro m hm n hn
        exact Submodule.mul_mem_mul (h hm) hn

theorem vol_unit {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    DN.vol D L * CU.cS D (DN.vol D L) = 1 := by
  exact le_antisymm (DN.vol_mul_cS_le_one D L (DN.sd_int D hL)) (DN.unitDisc D N L hL)

theorem detMul : DetMul D := by
  intro N L L' L'' _ hL hL' hL''
  rw [detId_eq_vol D hL, detId_eq_vol D hL, detId_eq_vol D hL']
  calc DN.vol D L'' * CU.cS D (DN.vol D L)
      = DN.vol D L'' * CU.cS D (DN.vol D L) * (DN.vol D L' * CU.cS D (DN.vol D L')) := by
        rw [vol_unit D hL', mul_one]
    _ = DN.vol D L' * CU.cS D (DN.vol D L) * (DN.vol D L'' * CU.cS D (DN.vol D L')) := by ring

theorem norm_one_unit_ideal : NormOneUnitIdeal D := by
  intro z
  refine ⟨CU.cS D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}), fun x => Iff.rfl, ?_⟩
  rw [CU.cS_span, Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.one_eq_span]
  congr 2
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj D.host (z : D.host.E)]
  exact z.2.2

private theorem smulLat_mem_lemma {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (γ γ' : Matrix (Fin N) (Fin N) D.host.E) (h1 : γ' * γ = 1) (h2 : γ * γ' = 1) (z : Fin N → D.host.E) :
    z ∈ SDLat.smulLat γ L ↔ γ' *ᵥ z ∈ L := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    show γ' *ᵥ (γ *ᵥ v) ∈ L
    rwa [mulVec_mulVec, h1, one_mulVec]
  · intro h
    refine ⟨γ' *ᵥ z, h, ?_⟩
    show γ *ᵥ (γ' *ᵥ z) = z
    rw [mulVec_mulVec, h2, one_mulVec]

theorem detSmul : DetSmul D := by
  intro N L₀ L γ _ hL₀ hL
  letI := D.host.cmStar
  have hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := γ.2.1
  have hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := γ.2.2
  rw [detId_eq_vol D hL₀, detId_eq_vol D hL₀, ← mul_assoc]
  congr 1
  unfold DN.vol
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨U', hU', rfl⟩
    refine ⟨_, rfl, (star (γ : Matrix (Fin N) (Fin N) D.host.E) * U').det, ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) * U', fun j => ?_, rfl⟩, ?_⟩
    · exact (smulLat_mem_lemma D L _ _ hγ hγ' _).mp (hU' j)
    · rw [← det_mul, ← mul_assoc, hγ', one_mul]
  · rintro ⟨_, rfl, _, ⟨U, hU, rfl⟩, rfl⟩
    refine ⟨(γ : Matrix (Fin N) (Fin N) D.host.E) * U, fun j => ?_, (det_mul _ _).symm⟩
    rw [smulLat_mem_lemma D L _ _ hγ hγ']
    show star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ fun i => U i j) ∈ L
    rw [mulVec_mulVec, hγ, one_mulVec]
    exact hU j

theorem stdH_unitary {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (hu' : (letI := D.host.cmStar; star γ * γ) = 1) (a b : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N (γ *ᵥ a) (γ *ᵥ b)) = (letI := D.host.cmStar; stdH D.host.E N a b) := by
  letI := D.host.cmStar
  show dotProduct (star (γ *ᵥ a)) (γ *ᵥ b) = dotProduct (star a) b
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose, hu', vecMul_one]

theorem smulSD : SmulSD D := by
  intro N L γ hL
  letI := D.host.cmStar
  have hγ : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := γ.2.1
  have hγ' : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := γ.2.2
  have hin : ∀ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L := fun v hv => by
    rw [smulLat_mem_lemma D L _ _ hγ hγ', mulVec_mulVec, hγ, one_mulVec]
    exact hv
  have hex : ∀ x ∈ SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L, ∃ v ∈ L, (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v = x := fun x hx =>
    ⟨_, (smulLat_mem_lemma D L _ _ hγ hγ' x).mp hx, by rw [mulVec_mulVec, hγ', one_mulVec]⟩
  unfold SD Formalism.BasicNotions.IsSDLat at hL
  obtain ⟨hfg, hspan, hdual⟩ := hL
  unfold SD Formalism.BasicNotions.IsSDLat
  refine ⟨?_, ?_, ?_⟩
  · unfold SDLat.smulLat
    exact hfg.map _
  · unfold SDLat.smulLat
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan, Submodule.map_top,
      LinearMap.range_eq_top]
    intro y
    refine ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, mulVec_mulVec, hγ', one_mulVec]
  · intro y

    have key : ∀ v, stdH D.host.E N ((γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v) y = stdH D.host.E N v (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := by
      intro v
      have hy : y = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := by rw [mulVec_mulVec, hγ', one_mulVec]
      conv_lhs => rw [hy]
      exact stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hγ v _
    rw [smulLat_mem_lemma D L _ _ hγ hγ', hdual]
    constructor
    · intro h x hx
      obtain ⟨v, hv, rfl⟩ := hex x hx
      rw [key v]
      exact h v hv
    · intro h v hv
      rw [← key v]
      exact h _ (hin v hv)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car}

def gM {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  γ.map (TaylorLogMetric.embT D τ)

theorem embT_star' (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.embT D τ (letI := D.host.cmStar; star x) = star (TaylorLogMetric.embT D τ x) := by
  rw [Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj, Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.emb_conj]
  rfl

theorem gM_conjTranspose {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (gM γ τ)ᴴ = gM (letI := D.host.cmStar; star γ) τ := by
  letI := D.host.cmStar
  ext i j
  simp only [gM, conjTranspose_apply, map_apply, star_apply]
  rw [embT_star']

theorem gM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A * B) τ = gM A τ * gM B τ := by
  simp [gM, Matrix.map_mul]

theorem gM_one {n : ℕ} (τ : D.what₂.Tau) : gM (1 : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp [gM, Matrix.map_one]

theorem gM_unit {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; star γ * γ) = 1)
    (τ : D.what₂.Tau) : (gM γ τ)ᴴ * gM γ τ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

theorem gM_unit' {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; γ * star γ) = 1)
    (τ : D.what₂.Tau) : gM γ τ * (gM γ τ)ᴴ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

variable {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)

def phiL (h1 : (letI := D.host.cmStar; star γ * γ) = 1) (h2 : (letI := D.host.cmStar; γ * star γ) = 1)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) (h2' : (letI := D.host.cmStar; γ' * star γ') = 1) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ => (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ : Matrix _ _ ℂ)
  invFun z := fun τ => (Matrix.conjTranspose (γ'.map (TaylorLogMetric.embT D τ)) * (Matrix.of (z τ)) * γ.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  map_add' x y := by
    funext τ
    show gM γ' τ * (Matrix.of (x τ) + Matrix.of (y τ)) * (gM γ τ)ᴴ = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c x := by
    funext τ
    show gM γ' τ * (c • Matrix.of (x τ)) * (gM γ τ)ᴴ = c • (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv z := by
    funext τ
    show (gM γ' τ)ᴴ * (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ) * gM γ τ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit γ h1, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit γ' h1',
      Matrix.one_mul]
  right_inv z := by
    funext τ
    show gM γ' τ * ((gM γ' τ)ᴴ * Matrix.of (z τ) * gM γ τ) * (gM γ τ)ᴴ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit' γ h2, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit' γ' h2',
      Matrix.one_mul]

theorem sum_trace {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ) :
    ∑ i, ∑ j, X i j * (starRingEnd ℂ) (Y i j) = Matrix.trace (X * Yᴴ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem trace_unit {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) (Z W : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (P * Z * Q * (P * W * Q)ᴴ) = Matrix.trace (Z * Wᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have e : P * Z * Q * (Qᴴ * (Wᴴ * Pᴴ)) = P * (Z * Wᴴ) * Pᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qᴴ, hQ, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem phiL_isom (h1 h2 h1' h2') (A : ℝ) :
    IsIsom (Ker.formV A D.what₂.Tau N N') (Ker.formV A D.what₂.Tau N N')
      ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') := by
  intro x y
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_trace (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ) (gM γ' τ * Matrix.of (y τ) * (gM γ τ)ᴴ)
  have e2 := sum_trace (Matrix.of (x τ)) (Matrix.of (y τ))
  rw [trace_unit _ _ (gM_unit γ' h1' τ) (by rw [Matrix.conjTranspose_conjTranspose]; exact gM_unit γ h1 τ)] at e
  exact e.trans e2.symm

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car}

theorem mem_smulLat {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (x : Fin n → D.host.E) : x ∈ SDLat.smulLat γ L ↔ ∃ w ∈ L, γ *ᵥ w = x := by
  simp [SDLat.smulLat, Submodule.mem_map, Matrix.toLin'_apply]

theorem homL_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 : (letI := D.host.cmStar; star γ * γ) = 1) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.homL D L L') :
    (letI := D.host.cmStar; γ' * A * star γ) ∈ TaylorLogMetric.homL D (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  induction hA using Submodule.span_induction with
  | mem A hA' =>
    apply Submodule.subset_span
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (mem_smulLat γ L x).1 hx
    refine (mem_smulLat γ' L' _).2 ⟨A *ᵥ w, hA' w hw, ?_⟩
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]
  | zero => simp
  | add A B _ _ ha hb => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem ha hb
  | smul c A _ ha => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c ha

theorem yy_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 : (letI := D.host.cmStar; star γ * γ) = 1) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.YYl D L L') :
    (letI := D.host.cmStar; γ' * A * star γ) ∈ TaylorLogMetric.YYl D (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨a, ha, _, homL_conj γ γ' h1 hA, by simp [Matrix.mul_smul, Matrix.smul_mul]⟩
  | zero => simp
  | add A B _ _ ha hb => simpa [Matrix.mul_add, Matrix.add_mul] using add_mem ha hb
  | smul c A _ ha => simpa [Matrix.mul_smul, Matrix.smul_mul] using Submodule.smul_mem _ c ha

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem embV_conj {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (A : Matrix (Fin N') (Fin N) D.host.E) :
    TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (letI := D.host.cmStar; γ' * A * star γ) =
      phiL γ γ' h1 h2 h1' h2' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) := by
  funext τ i j
  have hm : (γ' * A * star γ).map (TaylorLogMetric.embT D τ) =
      gM γ' τ * of (fun i j => TaylorLogMetric.embT D τ (A i j)) * (gM γ τ)ᴴ := by
    rw [gM_conjTranspose]
    simp only [gM, Matrix.map_mul]
    rfl
  exact congrFun (congrFun hm i) j

private theorem smulLat_star_smulLat_of_unitary {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : star γ * γ = 1)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : SDLat.smulLat (star γ) (SDLat.smulLat γ L) = L := by
  ext x
  simp only [mem_smulLat]
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  · intro hx
    exact ⟨γ *ᵥ x, ⟨x, hx, rfl⟩, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩

theorem la_img {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    imgLat ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat γ L) (SDLat.smulLat γ' L') := by
  apply le_antisymm
  · rw [imgLat, AddSubgroup.map_le_iff_le_comap]
    apply (AddSubgroup.closure_le _).2
    rintro z ⟨w, hw, A, hA, rfl⟩
    change phiL γ γ' h1 h2 h1' h2' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) ∈
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat γ L) (SDLat.smulLat γ' L')
    rw [map_smul, ← embV_conj γ γ' h1 h2 h1' h2']
    exact AddSubgroup.subset_closure ⟨w, hw, _, yy_conj γ γ' h1 hA, rfl⟩
  · apply (AddSubgroup.closure_le _).2
    rintro z ⟨w, hw, B, hB, rfl⟩
    have hB' := yy_conj (star γ) (star γ') (by rw [star_star]; exact h2) hB
    rw [smulLat_star_smulLat_of_unitary γ h1, smulLat_star_smulLat_of_unitary γ' h1'] at hB'
    refine ⟨w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (star γ' * B * star (star γ)),
      AddSubgroup.subset_closure ⟨w, hw, _, hB', rfl⟩, ?_⟩
    change phiL γ γ' h1 h2 h1' h2' _ = _
    rw [map_smul, ← embV_conj γ γ' h1 h2 h1' h2']
    congr 2
    simp only [star_star, ← Matrix.mul_assoc, h2', Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem Hf_eq' (T : TaylorLogMetric.Tor D) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Hf D T z w = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z w := rfl

theorem pull_eq {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (F : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' F = pullInv (phiL γ γ' h1 h2 h1' h2') F := rfl

theorem al_phi {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1 h2 h1' h2') (x : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (phiL γ γ' h1 h2 h1' h2' x) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x := by
  have h := phiL_isom γ γ' h1 h2 h1' h2' (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) x x
  simp only [LinearEquiv.coe_coe] at h
  simp only [TaylorLogMetric.al, Hf_eq']
  rw [h]

private theorem pull_core_lemma {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ)
    (φ : V ≃ₗ[ℂ] V) (hI : IsIsom H H (φ : V →ₗ[ℂ] V)) (hα : ∀ x, α (φ x) = α x)
    (Λ₁ Λ₂ : AddSubgroup V) (G : V → ℂ)
    (hcl : ∀ x ∈ Λ₂, ∀ y ∈ Λ₂, y ∈ Λ₁ → ∀ z, α (x + y) * opU H (x + y) G z = α x * opU H x G z) (z : V) :
    (((Real.sqrt ((Λ₁.addSubgroupOf Λ₂).index : ℝ)) : ℂ))⁻¹ *
        ∑ᶠ q : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂, α ↑(Quotient.out q) * opU H ↑(Quotient.out q) G (φ.symm z) =
      (((Real.sqrt (((imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)).index : ℝ)) : ℂ))⁻¹ *
        ∑ᶠ q : imgLat (φ : V →ₗ[ℂ] V) Λ₂ ⧸ (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂),
          α ↑(Quotient.out q) * opU H ↑(Quotient.out q) (pullInv φ G) z := by
  have hmem : ∀ (Λ : AddSubgroup V) (a : V), φ a ∈ imgLat (φ : V →ₗ[ℂ] V) Λ ↔ a ∈ Λ := fun Λ a =>
    AddSubgroup.mem_map_iff_mem (f := (φ : V →ₗ[ℂ] V).toAddMonoidHom) φ.injective
  let e0 : Λ₂ ≃ imgLat (φ : V →ₗ[ℂ] V) Λ₂ := Equiv.subtypeEquiv φ.toEquiv (fun a => (hmem Λ₂ a).symm)
  have hrelq : ∀ a b : Λ₂, (-a + b ∈ Λ₁.addSubgroupOf Λ₂ ↔
      -(e0 a) + e0 b ∈ (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)) := by
    intro a b
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf]
    have h5 : ((-(e0 a) + e0 b : imgLat (φ : V →ₗ[ℂ] V) Λ₂) : V) = φ ((-a + b : Λ₂) : V) := by
      simp [e0]
    rw [h5, hmem]
  let e : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃ (imgLat (φ : V →ₗ[ℂ] V) Λ₂ ⧸
      (imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)) :=
    Quotient.congr e0 (fun a b => by
      rw [QuotientAddGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
      exact hrelq a b)
  have hidx : (Λ₁.addSubgroupOf Λ₂).index =
      ((imgLat (φ : V →ₗ[ℂ] V) Λ₁).addSubgroupOf (imgLat (φ : V →ₗ[ℂ] V) Λ₂)).index := Nat.card_congr e
  rw [hidx]
  congr 1
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro q
  have hq : e q = QuotientAddGroup.mk (e0 (Quotient.out q)) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' q]
    rfl
  have hrel := QuotientAddGroup.eq.mp ((QuotientAddGroup.out_eq' (e q)).trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hrel
  obtain ⟨x, hφx⟩ : ∃ x, φ x = ↑(Quotient.out (e q)) := ⟨_, φ.apply_symm_apply _⟩
  have hxΛ : x ∈ Λ₂ := by
    rw [← hmem, hφx]
    exact (Quotient.out (e q)).2
  have hy : x - ↑(Quotient.out q) ∈ Λ₁ := by
    have h3 : φ (-(x - ↑(Quotient.out q))) ∈ imgLat (φ : V →ₗ[ℂ] V) Λ₁ := by
      convert hrel using 1
      simp [e0, hφx]
      abel
    rwa [hmem, neg_mem_iff] at h3
  rw [← hφx, hα, ← pullOpU V H φ hI x G z]
  simp only [pullInv]
  have h4 := hcl (↑(Quotient.out q)) (Quotient.out q).2 (x - ↑(Quotient.out q))
    (sub_mem hxΛ (Quotient.out q).2) hy (φ.symm z)
  have h6 : (↑(Quotient.out q) : V) + (x - ↑(Quotient.out q)) = x := by abel
  rw [h6] at h4
  exact h4.symm

theorem pull_core {B : Cd.Base D cc δ} (hL : B.LatAll) {N N' : ℕ} (φ : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N')
    (hI : IsIsom (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N'))
    (hα : ∀ x, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (φ x) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x)
    {L L₁ M M₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' M' M₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L L') (a2 : TaylorLogMetric.admitted D N N' L₁ L₁')
    (i1 : imgLat (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M')
    (i2 : imgLat (φ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M₁ M₁')
    (G : TaylorLogMetric.VC D N N' → ℂ) (hG : G ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) L L') :
    pullInv φ G ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) M M' ∧
      pullInv φ (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁') G) =
        TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M₁ M₁') (pullInv φ G) := by
  have hUo : ∀ (x : TaylorLogMetric.VC D N N') (F : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N'),
      TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) x F z =
        opU (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') x F z := by
    intro x F z
    simp only [TaylorLogMetric.U, opU, Hf_eq']
  have hG1 : Differentiable ℂ G := hG.1
  have hG2 : ∀ x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L', ∀ z,
      TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) x G z = G z := hG.2
  simp only [TaylorLogMetric.Th]
  rw [← i1, ← i2]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hG1.comp (LinearMap.toContinuousLinearMap (φ.symm : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')).differentiable
  · rintro _ ⟨y, hy, rfl⟩ z
    change TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (φ y) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (φ y) (pullInv φ G) z = pullInv φ G z
    rw [hα, hUo, ← pullOpU _ _ φ hI y G z]
    simp only [pullInv]
    rw [← hUo]
    exact hG2 y hy _
  · funext z
    have hsemi := (hL.1 N N' L₁ L₁' a2).2
    have hfix : G ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
        (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') := by
      intro x hx z
      rw [← hUo]
      exact hG2 x hx z
    have hcl := interClass (TaylorLogMetric.VC D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (formV_herm _ _ _ _) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁')
      (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) hsemi G hfix
    simp only [TaylorLogMetric.Iop, hUo]
    exact pull_core_lemma _ _ φ hI hα _ _ G hcl z

theorem pullIop_of {B : Cd.Base D cc δ} (hL : B.LatAll) : PullIop D B.tor := by
  intro N N' L L₁ L' L₁' γ γ' hN hN' hSL hSL₁ hSL' hSL₁' G hG
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Unitary.star_mul_self_of_mem γ.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Unitary.mul_star_self_of_mem γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Unitary.star_mul_self_of_mem γ'.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Unitary.mul_star_self_of_mem γ'.2
  simp only [Cd.Base.tor, pull_eq (cc := cc) (δ := δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) h1 h2 h1' h2']
  exact pull_core hL (phiL _ _ h1 h2 h1' h2') (phiL_isom _ _ h1 h2 h1' h2' _) (al_phi _ _ h1 h2 h1' h2')
    ⟨hN, hN', hSL, hSL'⟩ ⟨hN, hN', hSL₁, hSL₁'⟩ (la_img _ _ h1 h2 h1' h2' L L') (la_img _ _ h1 h2 h1' h2' L₁ L₁') G hG

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end
