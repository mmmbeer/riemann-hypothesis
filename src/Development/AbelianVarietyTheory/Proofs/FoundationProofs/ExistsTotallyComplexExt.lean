import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IntegralCoordinatesNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open GlobalTheory.NormSum GlobalTheory.IndefiniteRowSideFullHecke.IntegralCoordinatesNorm

namespace GlobalTheory.NormSum.Compare

theorem sqrt_le_rd (D : D7) : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem three_le (D : D7) : (3 : ℝ) ≤ D.host.q ∧ (3 : ℝ) ≤ D.host.d := by
  obtain ⟨hq, hd, -, hq2, hd2⟩ := D.host.hypOdd
  have := hq.two_le
  have := hd.two_le
  constructor
  · exact_mod_cast (show 3 ≤ D.host.q by omega)
  · exact_mod_cast (show 3 ≤ D.host.d by omega)

theorem log_d_le (D : D7) : Real.log D.host.d ≤ 2 * Real.log D.host.rdE := by
  obtain ⟨hq, hd⟩ := three_le D
  have h2 := sqrt_le_rd D
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity)
  have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have h5 : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by nlinarith
  have := Real.log_le_log (by linarith) h5
  rwa [Real.log_pow, Nat.cast_ofNat] at this

def ArchOne (G : D7 → ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (Q : ℕ), Crv D cc δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → G D Q →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type) (N : ℕ) (B L : ℝ)
      (P P' : ι → Pair D cc δ t0 Q) (zA zA' : ι → K),
      1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L →
      (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
      (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
      ArchimedeanHeightBound zA zA' (bArch C (fF D) N B L Q)

theorem ArchOne.mono {G G' : D7 → ℕ → Prop} (hG : ∀ D Q, G' D Q → G D Q) (h : ArchOne G) : ArchOne G' := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun D cc δ t0 Q h1 h2 h3 => h D cc δ t0 Q h1 h2 (hG D Q h3)⟩

section Places

open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl)
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

end Places

def CoordClauses {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (l : ℕ) [Fact l.Prime]
    (e_vp : ℝ) : Prop :=
  (∀ h : GA D P.d, ∃ γ ∈ ratG D P.d, ∃ j ∈ P.J, IntOver D l (γ * h * j)) ∧
    (∀ h : GA D P.d, gam D P.J h ≠ 0 ∧ (padicValNat l (gam D P.J h) : ℝ) ≤ e_vp) ∧
    ∀ h : GA D P.d, IntOver D l h → ∀ T, ∃ hz : P.coord h T ∈ Qbar,
      ∀ lam : Qbar →+* ℂ_[l], ‖lam ⟨P.coord h T, hz⟩‖ ≤ (l : ℝ) ^ e_vp

theorem CoordClauses.mono {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {l : ℕ}
    [hl : Fact l.Prime] {e e' : ℝ} (h : CoordClauses P l e) (he : e ≤ e') : CoordClauses P l e' :=
  ⟨h.1, fun g => ⟨(h.2.1 g).1, (h.2.1 g).2.trans he⟩, fun g hg T => (h.2.2 g hg T).imp fun _ hb lam =>
    (hb lam).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_le) he)⟩

def CoordsLev (D : D7) (G : ℕ → Prop) (N : ℕ) (B : ℝ) (Q : ℕ) (del_vp : ℕ → ℝ) : Prop :=
  ∀ (δ t0 : ℂ) (l : ℕ) [Fact l.Prime] (Q' : ℕ), G Q' → Nat.Coprime Q' l → ∀ P : Pair D ⊤ δ t0 (Q * Q'), P.Small N B →
    CoordClauses P l (del_vp l)

def IntLev (G : D7 → ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Del S del_vp (bInt C (fF D) N B L Q) ∧
      CoordsLev D (G D) N B Q del_vp ∧ NormsInt D {⊤} N B Q S del_vp (bInt C (fF D) N B L Q)

theorem IntLev.mono {G G' : D7 → ℕ → Prop} (hG : ∀ D Q, G' D Q → G D Q) (h : IntLev G) : IntLev G' := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun D N B L Q hs => ?_⟩
  obtain ⟨S, del, h1, h2, h3⟩ := h D N B L Q hs
  exact ⟨S, del, h1, fun δ t0 l _ Q' hQ => h2 δ t0 l Q' (hG D Q' hQ), h3⟩

end GlobalTheory.NormSum.Compare
