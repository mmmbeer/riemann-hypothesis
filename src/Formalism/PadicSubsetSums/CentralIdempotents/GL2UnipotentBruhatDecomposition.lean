import Formalism.PadicSubsetSums.CentralIdempotents.ArchimedeanComponents

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial TensorProduct

def brk (l : ℕ) [Fact l.Prime] (ω : ℤ_[l]) : PowerSeries ℤ_[l] :=
  PowerSeries.binomialSeries ℤ_[l] ω - 1

def piP (l : ℕ) [Fact l.Prime] (s : ℕ) : PowerSeries ℤ_[l] :=
  ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), brk l ω

def DictConcrete : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e s : ℕ), e * s = l - 1 → ∀ (u : ℤ_[l]) (q : PowerSeries ℤ_[l]),
    PowerSeries.X * q = brk l (l : ℤ_[l]) →
    (Polynomial.nthRootsFinset s (1 : ℤ_[l])).card = s ∧
    (∃ ε : (PowerSeries ℤ_[l])ˣ, piP l s = (ε : PowerSeries ℤ_[l]) * PowerSeries.X ^ s) ∧
    (∃ ε : (PowerSeries ℤ_[l])ˣ,
      PowerSeries.subst (brk l (l : ℤ_[l])) (piP l s) = (ε : PowerSeries ℤ_[l]) * piP l s * q ^ s) ∧
    (piP l s) ^ 2 ∣ PowerSeries.subst (brk l u) (piP l s) - PowerSeries.C (u ^ s) * piP l s

def GL2UnipotentBruhatDecomposition : Prop :=
  ∀ (F : Type) [Field F] (x : F), x ≠ 0 →
    (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; x⁻¹, 1] * !![0, x; -x⁻¹, 0] * !![1, 0; x⁻¹, 1]

def IwahoriUnit : Prop :=
  ∀ (Hk : Type) [Ring Hk] (q : ℕ) (T : Hk), IsUnit (q : Hk) →
    T * T = (q : Hk) + ((q : Hk) - 1) * T → IsUnit T

end Formalism.IrreducibleCountingLemmas.WindowSums
