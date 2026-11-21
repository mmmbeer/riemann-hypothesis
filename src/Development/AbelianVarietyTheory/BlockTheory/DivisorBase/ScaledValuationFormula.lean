import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

open Formalism.DivisionValues Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K]

def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)

def ValGE_vw {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) (y : Fin d → K)
    (c : ℝ) : Prop :=
  ∃ n : ℤ, c ≤ (n : ℝ) ∧ y ∈ scaledAt w n B

def DenLE_vw {d d' : ℕ} (w : HeightOneSpectrum (𝓞 K)) (φ : Matrix (Fin d') (Fin d) K)
    (A : Submodule (𝓞 K) (Fin d → K)) (B : Submodule (𝓞 K) (Fin d' → K)) (c : ℝ) : Prop :=
  ∃ a : ℤ, (a : ℝ) ≤ c ∧ ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A, φ.mulVec x ∈ scaledAt w (-a) B

def dualCoord {d : ℕ} (MM : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) where
  carrier := {y | ∀ x ∈ MM, y ⬝ᵥ x ∈ Set.range (algebraMap (𝓞 K) K)}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro y z hy hz x hx
    obtain ⟨a, ha⟩ := hy x hx
    obtain ⟨c, hc⟩ := hz x hx
    exact ⟨a + c, by rw [map_add, ha, hc, add_dotProduct]⟩
  smul_mem' := by
    rintro r y hy x hx
    obtain ⟨a, ha⟩ := hy x hx
    exact ⟨r * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩

def bound (C f m N L b Sig0 : ℝ) : ℝ :=
  C * f * b * N * m * (m * L + m * Sig0) + C * f * m ^ 2 * N ^ 2 * (L + Sig0) * b

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def ClauseA (S : IndefData Df) {d : ℕ} (MV : Submodule (𝓞 K) (Fin d → K))
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (dF : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Df.Mt (S.μ w)),
    ValGE_vw w MV ((v (S.μ w)).mulVec F) (-dF w)

def FormulaTwo (S : IndefData Df) {d : ℕ} (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K)
    (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), r (S.μ w) ≠ 0 ∧
    PSI * S.ι (S.μ w) * Df.Pq (S.μ w) = (r (S.μ w))⁻¹ • v (S.μ w)

def ClauseAConsequence (S : IndefData Df) {d : ℕ} (MV : Submodule (𝓞 K) (Fin d → K))
    (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K) (dF : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), DenLE_vw w PSI S.RR MV ((vw w (r (S.μ w)) : ℝ) + dF w)

omit [StarRing K] in

def ClauseB (dF : HeightOneSpectrum (𝓞 K) → ℝ) (B : ℝ) : Prop :=
  (Function.support dF).Finite ∧ ∑ᶠ w : HeightOneSpectrum (𝓞 K), 2 * lw w * dF w ≤ B

def DenominatorsLE (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MV : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K MV]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (B : ℝ) : Prop :=
  ∃ dF : HeightOneSpectrum (𝓞 K) → ℝ,
    ClauseA S MV v dF ∧
    (∀ (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K), FormulaTwo S v PSI r → ClauseAConsequence S MV PSI r dF) ∧
    ClauseB dF B

def FP (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MV : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K MV]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (C : ℝ) (f m N : ℕ) (L b Sig0 : ℝ) : Prop :=
  DenominatorsLE S MV v (bound C f m N L b Sig0)

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
