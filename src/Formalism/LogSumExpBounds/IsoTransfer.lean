import Mathlib
import Formalism.LogSumExpBounds.CharacterSumPhase.LogSumExpBoundHolds
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds
import Formalism.LogSumExpBounds.CharacterSumPhase.RankLeOfSupport
import Formalism.LogSumExpBounds.CharacterSumPhase.WeightedOffDiagonalHolds
import Formalism.LogSumExpBounds.CharacterSumPhase.KappaModulusHolds
import Formalism.LogSumExpBounds.CharacterSumPhase.DetMulDiagonalMulEqSum
import Formalism.LogSumExpBounds.CharacterSumPhase.DescEquivLiftEquiv
import Formalism.LogSumExpBounds.CharacterSumPhase.LatSum
import Formalism.LogSumExpBounds.CharacterSumPhase.DecayAsm
import Formalism.LogSumExpBounds.CharacterSumPhase.ZLiftAsm

section
namespace Formalism.NuclearRankWeightBounds.E

section
variable {K : Type*} [CommRing K] [StarRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsHerm (h : V →ₗ[K] V →ₗ⋆[K] K) : Prop := ∀ v w, h w v = star (h v w)

def tau (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V) (v : V) : V :=
  v + h v x • u - h v u • x
end

def mass {C : Type*} [Fintype C] (wt : C → C → ℝ) (c : C) : ℝ := ∑ c', wt c c'

end Formalism.NuclearRankWeightBounds.E
end

section
namespace Formalism.NuclearRankWeightBounds.Top

theorem latSum : Formalism.NuclearRankWeightBounds.Z.LatSum := Formalism.NuclearRankWeightBounds.P.lattice_sum_holds

theorem decay : Formalism.NuclearRankWeightBounds.D.Decay :=
  Formalism.NuclearRankWeightBounds.P.decay_of_facts Formalism.NuclearRankWeightBounds.P.cb_weights Formalism.NuclearRankWeightBounds.P.nuclear_norm_bound_holds
    Formalism.NuclearRankWeightBounds.P.rank_block_holds Formalism.NuclearRankWeightBounds.P.log_sum_exp_bound_holds Formalism.NuclearRankWeightBounds.P.weighted_off_diagonal_holds

end Formalism.NuclearRankWeightBounds.Top
end
