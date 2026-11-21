import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def IsWachBasis {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  LinearIndependent (LetA O n) b ∧ Submodule.span (LetA O n) (Set.range b) = W.N T ∧
    LinearIndependent W.EE b ∧ Submodule.span W.EE (Set.range b) = ⊤

def IsLetterBasis (i : ZMod n) {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  (∀ k, b k ∈ W.Nl T i) ∧
    ∀ x ∈ W.Nl T i, ∃! c : Fin r → PowerSeries O,
      x = ∑ k, (Pi.single i (c k) : LetA O n) • b k

def FrobBounds (M₀ h₀ : ℕ) : Prop :=
  (∀ x ∈ W.N T, W.Q ^ M₀ • W.φD T x ∈ W.N T) ∧ ∀ y ∈ W.N T, W.Q ^ h₀ • y ∈ W.φpull T

def FreeLetters : Prop :=
  (∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, IsWachBasis W T b) ∧
    (∀ i : ZMod n, ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, IsLetterBasis W T i b) ∧
    ∃ M₀ h₀ : ℕ, FrobBounds W T M₀ h₀

theorem FrobBounds.pull {M₀ h₀ : ℕ} (hF : FrobBounds W T M₀ h₀) :
    ∀ y ∈ W.φpull T, W.Q ^ M₀ • y ∈ W.N T := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨z, hz, rfl⟩ := hx; exact hF.1 z hz
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact (W.N T).add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact (W.N T).smul_mem a hx

end Generic

def WachLettersFree (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    FreeLetters (H.W K s LL h) T

end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
