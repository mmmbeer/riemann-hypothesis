import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable (D : D7)

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

def J1 (B : Ker.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ : Matrix.unitaryGroup (Fin N) D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2 (B : Ker.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ' : Matrix.unitaryGroup (Fin N') D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N'))

end Formalism.L2.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

theorem formV_herm' (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (Ker.formV A n N N') := by
  intro x y
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_ThSp_of' (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' :=
  ⟨fun z => (h.1 z (Set.mem_univ z)).differentiableAt, fun x hx z => h.2 x hx z⟩

theorem Iop_smul' (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Iop D T La₁ La₂ (fun v => c * G v) z = c * TaylorLogMetric.Iop D T La₁ La₂ G z := by
  unfold TaylorLogMetric.Iop
  have : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      TaylorLogMetric.al D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') *
        TaylorLogMetric.U D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') (fun v => c * G v) z
      = c • (TaylorLogMetric.al D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') *
        TaylorLogMetric.U D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') G z) := by
    intro q; simp only [TaylorLogMetric.U, smul_eq_mul]; ring
  simp only [this]
  rw [← smul_finsum, smul_eq_mul]; ring

def SmulSD (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    SD D L → SD D (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)

def NormOneUnitIdeal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ z : unitary D.host.E, TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)})

section Paths

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ)

theorem admissible_of_integral_conj_le {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hN : Even N) (hN' : Even N') (h : SD D L) (h' : SD D L') :
    TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', h, h'⟩

theorem sd0 (N : ℕ) : SD D (StandardLatticesGL3.stdL D N) := Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N

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
  have hH := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) h0
  have hs := hSq N N' L L₁ (StandardLatticesGL3.stdL D N') L' hN hN' hLs hL1 (sd0 N') h1 (B.thHalf N N' L)
    (mem_ThSp_of' _ _ _ _ hH)
  have ht : TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N'))
      (B.thHalf N N' L) = B.thHalf N N' L₁ :=
    hTL N N' L L₁ hN hN' hLs hL1 _ (mem_ThSp_of' _ _ _ _ h0)
  show TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' L₁) = _
  rw [← ht]
  exact hs

end Paths

end Formalism.L2.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

theorem iopSelf (D : D7) : IopSelf D := by
  intro T N N' La' G hG
  funext z
  unfold TaylorLogMetric.Iop
  have hidx : (La'.addSubgroupOf La').index = 1 := by
    rw [AddSubgroup.addSubgroupOf_self, AddSubgroup.index_top]
  have hq : ∀ q : La' ⧸ La'.addSubgroupOf La',
      TaylorLogMetric.al D T ((Quotient.out q : La') : TaylorLogMetric.VC D N N') * TaylorLogMetric.U D T ((Quotient.out q : La') : TaylorLogMetric.VC D N N') G z
        = G z := fun q => hG.2 _ (Quotient.out q).2 z
  simp_rw [hq]
  have h0 : ∀ q : La' ⧸ La'.addSubgroupOf La', q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x => exact (QuotientAddGroup.eq_zero_iff _).mpr (by simp)
  rw [finsum_eq_single (fun _ => G z) (0 : La' ⧸ La'.addSubgroupOf La') (fun q hq => absurd (h0 q) hq), hidx]
  simp

section Chi

variable {D : D7}

theorem character_factor_change_right (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN' : Even N')
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h1 : SD D L') (h2 : SD D L'') :
    Ker.Base.chiFac χ N N' L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Ker.Base.chiFac χ N N' L L' := by
  unfold Ker.Base.chiFac
  rw [hM N' (StandardLatticesGL3.stdL D N') L' L'' hN' (sd0 N') h1 h2,
    hχ.1 _ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h1)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' h1 h2), mul_zpow]
  ring

theorem character_factor_change_left (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN : Even N)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h1 : SD D L) (h2 : SD D L₁) :
    Ker.Base.chiFac χ N N' L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Ker.Base.chiFac χ N N' L L' := by
  unfold Ker.Base.chiFac
  rw [hM N (StandardLatticesGL3.stdL D N) L L₁ hN (sd0 N) h1 h2,
    hχ.1 _ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN h1 h2), mul_zpow]
  ring

theorem emb_star_unit (τ : D.what₂.Tau) (x : D.host.E) (hx : letI := D.host.cmStar; x * star x = 1) :
    (letI := D.host.cmStar; TaylorLogMetric.embT D τ (star x)) = (TaylorLogMetric.embT D τ x)⁻¹ := by
  letI := D.host.cmStar
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, hx, map_one]

theorem character_factor_unitary_action (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hS : DetSmul D) (hU : NormOneUnitIdeal D) {N N' : ℕ}
    (hN : Even N) (hN' : Even N') :
    letI := D.host.cmStar
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E), SD D L → SD D L' →
    Ker.Base.chiFac χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') =
      Ker.Base.chiFac χ N N' L L' *
        ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) *
          (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2)) := by
  letI := D.host.cmStar
  intro L L' γ γ' h1 h2
  have u1 := Matrix.det_of_mem_unitary γ.2
  have u2 := Matrix.det_of_mem_unitary γ'.2
  have c1 : χ (Submodule.span (𝓞 D.host.E) {(γ : Matrix (Fin N) (Fin N) D.host.E).det}) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ := hχ.2 ⟨_, u1⟩
  have c2 : χ (Submodule.span (𝓞 D.host.E) {(γ' : Matrix (Fin N') (Fin N') D.host.E).det}) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det)⁻¹ := hχ.2 ⟨_, u2⟩
  have s1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ :=
    Finset.prod_congr rfl fun τ _ => emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  unfold Ker.Base.chiFac
  rw [hS N (StandardLatticesGL3.stdL D N) L γ hN (sd0 N) h1, hS N' (StandardLatticesGL3.stdL D N') L' γ' hN' (sd0 N') h2,
    hχ.1 _ _ (hU ⟨_, u1⟩) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1),
    hχ.1 _ _ (hU ⟨_, u2⟩) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h2), c1, c2, s1,
]
  simp only [Finset.prod_inv_distrib, mul_zpow, zpow_neg, zpow_natCast, inv_pow]
  ring_nf
  simp only [inv_inv]

end Chi

section Pull

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

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

end Formalism.L2.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem Iop_smulF (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.Iop D T La₁ La₂ (c • G) = c • TaylorLogMetric.Iop D T La₁ La₂ G :=
  funext fun z => Iop_smul' D T La₁ La₂ c G z

theorem e3a (hP : PullIop D B.tor) (hTL : Tr0L D B.tor) (hSm : SmulSD D) (hL : B.LatAll) (hJ : J1 B)
    {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D X →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L X) =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thMoved N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) X := by
  letI := D.host.cmStar
  intro γ L X hLs hX
  have e1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := rfl
  have hγL := hSm N L γ hLs
  have hγ0 := hSm N (StandardLatticesGL3.stdL D N) γ (sd0 N)
  have hH := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) h0
  have p1 := (hP N N' L L (StandardLatticesGL3.stdL D N') X γ 1 hN hN' hLs hLs (sd0 N') hX (B.thHalf N N' L)
    (mem_ThSp_of' _ _ _ _ hH)).2
  have p2 := (hP N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ 1 hN hN' (sd0 N) hLs (sd0 N') (sd0 N')
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one, Formalism.BasicNotions.Examples₂.smulLat_one] at p1
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p2
  have j := hJ N N' γ hN hN'
  have t : TaylorLogMetric.Iop D B.tor
      (TaylorLogMetric.La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N)) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) (StandardLatticesGL3.stdL D N'))
      (B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))) =
      B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) :=
    hTL N N' _ _ hN hN' hγ0 hγL _ (mem_ThSp_of' _ _ _ _ h0)
  show TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' L)) = _ • TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' _)
  rw [p1]
  show TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N'))) = _
  rw [p2, j, Iop_smulF, Iop_smulF, t]

theorem e3b (hP : PullIop D B.tor) (hSq : SqP D B.tor) (hTR : Tr0R D B.tor) (hSm : SmulSD D) (hL : B.LatAll)
    (hJ : J2 B) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thMoved N N' L L') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' L (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') := by
  letI := D.host.cmStar
  intro γ' L L' hLs h1
  have e1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := rfl
  have hγL' := hSm N' L' γ' h1
  have hγ0 := hSm N' (StandardLatticesGL3.stdL D N') γ' (sd0 N')
  have hΦ := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) h0
  have p1 := (hP N N' (StandardLatticesGL3.stdL D N) L L' L' 1 γ' hN hN' (sd0 N) hLs h1 h1 _ (mem_ThSp_of' _ _ _ _ hΦ)).2
  have p2 := (hP N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') L' 1 γ' hN hN' (sd0 N) (sd0 N) (sd0 N') h1
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one, Formalism.BasicNotions.Examples₂.smulLat_one] at p1
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p2
  have j := hJ N N' γ' hN hN'

  have hself : ∀ M : Submodule (𝓞 D.host.E) (Fin N' → D.host.E), B.thMoved N N' (StandardLatticesGL3.stdL D N) M =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) M)
        (B.thZero N N') := by
    intro M
    show TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
    rw [iopSelf D B.tor N N' _ _ (mem_ThSp_of' _ _ _ _ h0)]
  have t := hTR N N' _ _ hN hN' hγ0 hγL' _ (mem_ThSp_of' _ _ _ _ h0)
  rw [S1 hSq hL hN hN' h0 hLs h1, p1, p2, j, hself, Iop_smulF, Iop_smulF, t, S1 hSq hL hN hN' h0 hLs hγL']

theorem reduction_of (hM : DetMul D) (hS : DetSmul D) (hU : NormOneUnitIdeal D) (hSm : SmulSD D)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hL : B.LatAll)
    (h0 : ∀ N N', Even N → Even N' → B.ThZeroMem N N')
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hP : PullIop D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) :
    B.EqP χ := by
  letI := D.host.cmStar
  refine ⟨?_, ?_, ?_⟩
  · intro N N' L L' hN hN' γ γ'
    have h1 := hSm N' L'.1 γ' L'.2
    show TaylorLogMetric.pull D B.tor _ _ (Ker.Base.chiFac χ N N' L.1 L'.1 • B.thMoved N N' L.1 L'.1) =
      Ker.Base.chiFac χ N N' _ _ • B.thMoved N N' _ _
    rw [pull_smul, pull_comp, e3b hP hSq hTR hSm hL hJ2 hN hN' (h0 N N' hN hN') γ' L.1 L'.1 L.2 L'.2, pull_smul,
      e3a hP hTL hSm hL hJ1 hN hN' (h0 N N' hN hN') γ L.1 _ L.2 h1, smul_smul, smul_smul,
      character_factor_unitary_action χ hχ hS hU hN hN' L.1 L'.1 γ γ' L.2 L'.2]
    congr 1
    ring
  · intro N N' L L' L'' hN hN'
    funext z
    show Ker.Base.chiFac χ N N' L.1 L''.1 * B.thMoved N N' L.1 L''.1 z =
      χ (TaylorLogMetric.detId D L'.1 L''.1) ^ (-((N / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Ker.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e1path hSq hTR hL hN hN' (h0 N N' hN hN') L.2 L'.2 L''.2,
      character_factor_change_right χ hχ hM hN' L.1 L'.2 L''.2]
    ring
  · intro N N' L L₁ L' hN hN'
    funext z
    show Ker.Base.chiFac χ N N' L₁.1 L'.1 * B.thMoved N N' L₁.1 L'.1 z =
      χ (TaylorLogMetric.detId D L.1 L₁.1) ^ (((N' / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor _ _ (fun v => Ker.Base.chiFac χ N N' L.1 L'.1 * B.thMoved N N' L.1 L'.1 v) z
    rw [Iop_smul', e2path hSq hTL hL hN hN' (h0 N N' hN hN') L.2 L₁.2 L'.2,
      character_factor_change_left χ hχ hM hN L'.1 L.2 L₁.2]
    ring

end Formalism.L2.PairingIndexBounds.Eq
end
end

section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Matrix

variable (D : D7)

theorem detId_eq_vol {N : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    TaylorLogMetric.detId D L L' = DN.vol D L' * CU.cS D (DN.vol D L) := by
  have h1 : DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
    le_antisymm (DN.vol_mul_cS_le_one (D := D) L (DN.sd_int (D := D) hL)) (DN.unitDisc (D := D) N L hL)
  apply le_antisymm
  · calc TaylorLogMetric.detId D L L' = TaylorLogMetric.detId D L L' * (DN.vol D L * CU.cS D (DN.vol D L)) := by rw [h1, mul_one]
      _ = TaylorLogMetric.detId D L L' * DN.vol D L * CU.cS D (DN.vol D L) := by rw [mul_assoc]
      _ ≤ DN.vol D L' * CU.cS D (DN.vol D L) :=
        Submodule.mul_le.mpr fun a ha b hb =>
          Submodule.mul_mem_mul (DN.detId_mul_vol_le (D := D) L L' ha) hb
  · exact DN.vol_mul_cS_le (D := D) L L' (DN.sd_int (D := D) hL)

theorem vol_unit {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) :
    DN.vol D L * CU.cS D (DN.vol D L) = 1 :=
  le_antisymm (DN.vol_mul_cS_le_one (D := D) L (DN.sd_int (D := D) hL)) (DN.unitDisc (D := D) N L hL)

theorem detMul : DetMul D := by
  intro N L L' L'' _ hL hL' hL''
  rw [detId_eq_vol D hL, detId_eq_vol D hL, detId_eq_vol D hL']
  calc DN.vol D L'' * CU.cS D (DN.vol D L)
      = DN.vol D L'' * CU.cS D (DN.vol D L) * (DN.vol D L' * CU.cS D (DN.vol D L')) := by
        rw [vol_unit D hL', mul_one]
    _ = DN.vol D L' * CU.cS D (DN.vol D L) * (DN.vol D L'' * CU.cS D (DN.vol D L')) := by ring

theorem norm_one_unit_ideal : NormOneUnitIdeal D := by
  intro z
  letI := D.host.cmStar
  have hz : star (z : D.host.E) * (z : D.host.E) = 1 := (show _ ∧ _ from z.2).1
  have hint : ∀ a : 𝓞 D.host.E, star ((algebraMap (𝓞 D.host.E) D.host.E) a) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun a =>
    ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) a, rfl⟩
  have hz0 : (z : D.host.E) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hz
    exact zero_ne_one hz
  obtain ⟨L, hL⟩ : ∃ L : Submodule (𝓞 D.host.E) (Fin 1 → D.host.E),
      L = Submodule.span (𝓞 D.host.E) {(fun _ : Fin 1 => (z : D.host.E))} := ⟨_, rfl⟩
  have hmemL : ∀ y : Fin 1 → D.host.E, y ∈ L ↔ ∃ a : 𝓞 D.host.E, (algebraMap (𝓞 D.host.E) D.host.E) a * (z : D.host.E) = y 0 := by
    intro y
    rw [hL, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [Pi.smul_apply, Algebra.smul_def]⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, funext fun i => ?_⟩
      rw [Subsingleton.elim i 0, Pi.smul_apply, Algebra.smul_def]
      exact ha
  have hH : ∀ x y : Fin 1 → D.host.E, stdH D.host.E 1 x y = star (x 0) * y 0 := fun x y => by
    simp only [stdH, Fin.sum_univ_one]
  have hSD : SD D L := by
    unfold SD IsSDLat
    refine ⟨by rw [hL]; exact Submodule.fg_span_singleton _, ?_, ?_⟩
    · rw [hL, Submodule.span_span_of_tower, eq_top_iff]
      intro w _
      rw [Submodule.mem_span_singleton]
      refine ⟨w 0 * (z : D.host.E)⁻¹, funext fun i => ?_⟩
      rw [Subsingleton.elim i 0, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_right₀ hz0]
    · intro y
      rw [hmemL]
      constructor
      · rintro ⟨b, hb⟩ x hx
        obtain ⟨a, ha⟩ := (hmemL x).1 hx
        have e : stdH D.host.E 1 x y = star ((algebraMap (𝓞 D.host.E) D.host.E) a) * (algebraMap (𝓞 D.host.E) D.host.E) b := by
          rw [hH, ← ha, ← hb, star_mul']
          linear_combination star ((algebraMap (𝓞 D.host.E) D.host.E) a) * (algebraMap (𝓞 D.host.E) D.host.E) b * hz
        rw [e]
        exact (algebraMap (𝓞 D.host.E) D.host.E).range.mul_mem (hint a) (RingHom.mem_range_self _ b)
      · intro H
        obtain ⟨c, hc⟩ := H (fun _ : Fin 1 => (z : D.host.E)) ((hmemL _).2 ⟨1, by rw [map_one, one_mul]⟩)
        refine ⟨c, ?_⟩
        rw [hc, hH]
        linear_combination y 0 * hz
  have hvol : DN.vol D L = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    unfold DN.vol
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨U, hU, rfl⟩
      obtain ⟨a, ha⟩ := (hmemL _).1 (hU 0)
      rw [Matrix.det_fin_one, SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def]; exact ha⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Submodule.subset_span
      refine ⟨Matrix.of fun _ _ => (z : D.host.E), fun j => ?_, by rw [Matrix.det_fin_one, Matrix.of_apply]⟩
      rw [hL]
      exact Submodule.subset_span rfl
  have h1 := vol_unit D hSD
  rw [hvol] at h1
  exact ⟨CU.cS D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}), fun x => Iff.rfl, h1⟩

private theorem mem_smulLat_lemma [StarRing D.host.E] {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (g g' : Matrix (Fin N) (Fin N) D.host.E) (h1 : g' * g = 1) (h2 : g * g' = 1) (w : Fin N → D.host.E) :
    w ∈ SDLat.smulLat g L ↔ g' *ᵥ w ∈ L := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w', hw', rfl⟩
    change g' *ᵥ (g *ᵥ w') ∈ L
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    change g *ᵥ (g' *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

private theorem vol_smul_lemma_2 [StarRing D.host.E] {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (g g' : Matrix (Fin N) (Fin N) D.host.E) (h1 : g' * g = 1) (h2 : g * g' = 1) :
    DN.vol D (SDLat.smulLat g L) = Submodule.span (𝓞 D.host.E) {g.det} * DN.vol D L := by
  have hc : ∀ (A B : Matrix (Fin N) (Fin N) D.host.E) (j : Fin N),
      (fun i => (A * B) i j) = A *ᵥ (fun i => B i j) := fun A B j => by
    funext i
    rfl
  unfold DN.vol
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨U, hU, rfl⟩
    have e : U.det = g.det * (g' * U).det := by
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [e]
    refine Set.mul_mem_mul (Set.mem_singleton _) ⟨g' * U, fun j => ?_, rfl⟩
    rw [hc]
    exact (mem_smulLat_lemma D L g g' h1 h2 _).1 (hU j)
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨U, hU, rfl⟩ := hb
    refine ⟨g * U, fun j => ?_, (Matrix.det_mul _ _).symm⟩
    rw [mem_smulLat_lemma D L g g' h1 h2, hc, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    exact hU j

theorem detSmul : DetSmul D := by
  intro N L₀ L γ _ hL₀ hL
  letI := D.host.cmStar
  have hu : star (γ : Matrix (Fin N) (Fin N) D.host.E) * (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).1
  have hu2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).2
  rw [detId_eq_vol D hL₀, detId_eq_vol D hL₀, vol_smul_lemma_2 D L _ _ hu hu2, mul_assoc]

theorem stdH_unitary {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (hu' : (letI := D.host.cmStar; star γ * γ) = 1) (a b : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N (γ *ᵥ a) (γ *ᵥ b)) = (letI := D.host.cmStar; stdH D.host.E N a b) := by
  letI := D.host.cmStar
  have key : ∀ v w : Fin N → D.host.E, stdH D.host.E N v w = star v ⬝ᵥ w := fun v w => rfl
  rw [key, key, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, hu', Matrix.vecMul_one]

theorem smulSD : SmulSD D := by
  intro N L γ hL
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, hdual⟩ := hL
  have hu : star (γ : Matrix (Fin N) (Fin N) D.host.E) * (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).1
  have hu2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 := (show _ ∧ _ from γ.2).2
  have happ : ∀ v, ((toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)).restrictScalars (𝓞 D.host.E)) v = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v := fun v => rfl
  have hy : ∀ y, y = (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, hu2, Matrix.one_mulVec]
  have hmem : ∀ w, w ∈ L.map ((toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)).restrictScalars (𝓞 D.host.E)) ↔ star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ w ∈ L := by
    intro w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w', hw', rfl⟩
      rwa [happ, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
    · intro h
      exact ⟨_, h, by rw [happ, ← hy]⟩
  unfold SD SDLat.smulLat
  refine ⟨hfg.map _, ?_, ?_⟩
  · have himg : ((L.map ((toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)).restrictScalars (𝓞 D.host.E)) : Submodule _ _) : Set (Fin N → D.host.E)) =
        (toLin' (γ : Matrix (Fin N) (Fin N) D.host.E)) '' (L : Set (Fin N → D.host.E)) := by
      rw [Submodule.map_coe]; rfl
    rw [himg, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro v
    exact ⟨star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ v, by rw [Matrix.toLin'_apply, ← hy]⟩
  · intro y
    rw [hmem, hdual]
    constructor
    · intro H x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      have h1 := H x' hx'
      rw [← stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hu x' (star (γ : Matrix (Fin N) (Fin N) D.host.E) *ᵥ y), ← hy] at h1
      rwa [happ]
    · intro H x' hx'
      have h1 := H _ (Submodule.mem_map_of_mem hx')
      rw [happ, hy y, stdH_unitary D (γ : Matrix (Fin N) (Fin N) D.host.E) hu] at h1
      exact h1

end Formalism.L2.PairingIndexBounds.Eq
end
end
