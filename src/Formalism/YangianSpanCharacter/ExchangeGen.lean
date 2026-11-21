import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.T

open Matrix

def Gauge : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (p c ci hi θ : A) (Y : R),
    hi * c = c * hi → hi * ci = ci * hi → p * hi = hi * p - hi * θ →
      Tm Y p c ci * Matrix.diagonal (fun _ => hi) =
        Matrix.diagonal (fun _ => hi) * (Tm Y p c ci - !![θ, 0; 0, 0])

def E1 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def E2 {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  Matrix.of fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

def ExchangeGen : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (M0 Mb : Matrix (Fin 2) (Fin 2) A) (d : R),
    (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 Mb * E2 M0 =
        E2 M0 * E1 Mb * (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) →
      E2 Mbᵀ * pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M0 =
        E1 M0 * pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E2 Mbᵀ

end Formalism.YangianSpanCharacter.T
