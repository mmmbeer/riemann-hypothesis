import Mathlib
import Formalism.PeriodIntegrals.FunEqAll

section
noncomputable section

open Classical MvPowerSeries

namespace PI.FunEqAllProof

open PI.FunEqAll

abbrev Var (d : ℕ) := Fin 3 × ZMod d

def phi (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* ℂ_[l] :=
  (algebraMap ℚ_[l] ℂ_[l]).comp PadicInt.Coe.ringHom

def Sr (l : ℕ) [Fact l.Prime] : Subring ℂ_[l] := (phi l).range

def zv (l d : ℕ) [Fact l.Prime] (A : ZMod d → MvPowerSeries (Var d) ℂ_[l]) (s : ZMod d) :
    MvPowerSeries (Var d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range (JetTdeg n + 1),
    ((l : ℂ_[l]) ^ e)⁻¹ * coeff n (A (s - 2 * (e : ZMod d)) ^ ((l ^ 2) ^ e))

def Xv (l d : ℕ) [Fact l.Prime] (c : Fin 3) : ZMod d → MvPowerSeries (Var d) ℂ_[l] :=
  fun k => X (c, k)

end PI.FunEqAllProof
end
end

section
noncomputable section

open MvPowerSeries

namespace PI.FunEqAllProof

open PI.FunEqAll

section

variable (l d : ℕ) [Fact l.Prime]

def mono (s : ZMod d) (e : ℕ) : ZMod d × Unit →₀ ℕ :=
  Finsupp.single (s - 2 * (e : ZMod d), ()) ((l ^ 2) ^ e)

end

end PI.FunEqAllProof
end
end
