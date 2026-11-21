import Formalism.SuccessiveMinima.StatementNP

open Filter Topology

noncomputable section

namespace Formalism.FN

def cmul {K : Type*} [NormedField K] (a b : ℕ → K) : ℕ → K :=
  fun n => ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

end Formalism.FN
