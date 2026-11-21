import Mathlib
import GroundTheory.AutomorphicForms.UnitaryGroupScheme
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.MemRangeIffIsIntegral

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

open NumberField GroundTheory.Automorphic Module TensorProduct Matrix FunctionalEquationAlt

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

section Rational

variable (B : HermitianForm F E V)

def perp (W : Submodule E V) : Submodule E V := W.orthogonalBilin B.toSesq

def nn (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | (∀ u v, B.toSesq (X u) v + B.toSesq u (X v) = 0) ∧ (∀ y, X y ∈ perp B W) ∧
    (∀ y ∈ perp B W, X y ∈ W) ∧ ∀ y ∈ W, X y = 0}

def zz (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | X ∈ nn B W ∧ ∀ y ∈ perp B W, X y = 0}

def NR (W : Submodule E V) : Set (V ≃ₗ[E] V) :=
  {g | g ∈ B.unitaryGroup ∧ (∀ y, g y - y ∈ perp B W) ∧ (∀ y ∈ perp B W, g y - y ∈ W) ∧
    ∀ y ∈ W, g y = y}

def nexp (X : V →ₗ[E] V) : V →ₗ[E] V := 1 + X + (2⁻¹ : E) • (X * X)

def IsIntegralMul (L : Submodule (𝓞 E) V) (c : E) (X : V →ₗ[E] V) : Prop :=
  ∀ y ∈ L, ∃ l ∈ L, X y = c • l

def Gam (L : Submodule (𝓞 E) V) (W : Submodule E V) (g : ℕ) : Set (V ≃ₗ[E] V) :=
  {γ | γ ∈ NR B W ∧ (∀ y, γ y ∈ L ↔ y ∈ L) ∧
    IsIntegralMul L (g : E) ((γ : V →ₗ[E] V) - 1)}

def nnImage (W : Submodule E V) (X : V →ₗ[E] V) : perp B W →ₗ[E] V :=
  X.domRestrict (perp B W)

def hhR (W : Submodule E V) : Set (perp B W →ₗ[E] V) :=
  {T | (∀ y, T y ∈ W) ∧ ∀ y : perp B W, (y : V) ∈ W → T y = 0}

def Lam1 (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (perp B W →ₗ[E] V) :=
  {T | T ∈ hhR B W ∧ ∀ y : perp B W, (y : V) ∈ L → T y ∈ L}

end Rational

section Algebras

variable (B : HermitianForm F E V) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
variable (k : Type) [CommRing k] [Algebra F k]

def coordK (y : V) : ι → k ⊗[F] E :=
  fun i => (Algebra.TensorProduct.includeRight : E →ₐ[F] k ⊗[F] E) (b.repr y i)

def subK (W : Submodule E V) : Submodule (k ⊗[F] E) (ι → k ⊗[F] E) :=
  Submodule.span (k ⊗[F] E) (coordK b k '' (W : Set V))

def gramK : Matrix ι ι (k ⊗[F] E) :=
  (gram B.toSesq b).map (Algebra.TensorProduct.includeRight : E →ₐ[F] k ⊗[F] E)

def nnK (W : Submodule E V) : Set (Matrix ι ι (k ⊗[F] E)) :=
  {X | (X.map (conjBase F E k))ᵀ * gramK B b k + gramK B b k * X = 0 ∧
    (∀ y, X *ᵥ y ∈ subK b k (perp B W)) ∧ (∀ y ∈ subK b k (perp B W), X *ᵥ y ∈ subK b k W) ∧
    ∀ y ∈ subK b k W, X *ᵥ y = 0}

def zzK (W : Submodule E V) : Set (Matrix ι ι (k ⊗[F] E)) :=
  {X | X ∈ nnK B b k W ∧ ∀ y ∈ subK b k (perp B W), X *ᵥ y = 0}

def NRK (W : Submodule E V) : Set (GL ι (k ⊗[F] E)) :=
  {g | g ∈ unitaryPoints F E (gram B.toSesq b) k ∧
    (∀ y, ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y ∈ subK b k (perp B W)) ∧
    (∀ y ∈ subK b k (perp B W), ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y ∈ subK b k W) ∧
    ∀ y ∈ subK b k W, ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y = 0}

def nexpK (X : Matrix ι ι (k ⊗[F] E)) : Matrix ι ι (k ⊗[F] E) :=
  1 + X + (algebraMap F (k ⊗[F] E) 2⁻¹) • (X * X)

end Algebras

def UnipotentAlgebra.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (R : Submodule (𝓞 E) V), IsIsotropic B R →
  let W := espan R
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
    (k : Type) [CommRing k] [Algebra F k],
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W, ∀ X'' ∈ nnK B b k W, X * X' * X'' = 0) ∧
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W,
      (∀ y ∈ subK b k (perp B W), (X * X') *ᵥ y = 0) ∧ ∀ y, (X * X') *ᵥ y ∈ subK b k W) ∧
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W, X * X' - X' * X ∈ zzK B b k W) ∧
    (∀ Z ∈ zzK B b k W, ∀ X ∈ nnK B b k W, Z * X = X * Z) ∧
    Set.BijOn (nexpK k) (nnK B b k W)
      ((fun g : GL ι (k ⊗[F] E) => (g : Matrix ι ι (k ⊗[F] E))) '' NRK B b k W) ∧
    ∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W,
      nexpK k X * nexpK k X' =
        nexpK k (X + X' + (algebraMap F (k ⊗[F] E) 2⁻¹) • (X * X' - X' * X))

def ExpIntegral.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V), L.FG → IsSelfDual B L →
  ∀ R : Submodule (𝓞 E) V, IsIsotropic B R → ∀ g : ℕ, 1 ≤ g →
  ∀ X ∈ nn B (espan R), IsIntegralMul L (2 * g : E) X →
    ∃ γ ∈ Gam B L (espan R) g, (γ : V →ₗ[E] V) = nexp X

def Lifting.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V), L.FG → IsSelfDual B L →
  ∀ R : Submodule (𝓞 E) V, SatIn R L → IsIsotropic B R →
    (∀ T ∈ Lam1 B L (espan R), ∃ X ∈ nn B (espan R),
      IsIntegralMul L 1 X ∧ nnImage B (espan R) X = (2 : E) • T) ∧
    ∀ g : ℕ, 1 ≤ g → ∀ T ∈ Lam1 B L (espan R), ∃ X ∈ nn B (espan R),
      IsIntegralMul L (2 * g : E) X ∧ nnImage B (espan R) X = (4 * g : E) • T

section Example

variable (F E)

def hypPlaneSesq : (Fin 2 → E) →ₛₗ[conjHom F E] (Fin 2 → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => conj F E (x 0) * y 1 + conj F E (x 1) * y 0)
    (by intros; simp only [Pi.add_apply, map_add]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [show ∀ c, conjHom F E c = conj F E c from fun _ => rfl]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

theorem hypPlaneSesq_apply (x y : Fin 2 → E) :
    hypPlaneSesq F E x y = conj F E (x 0) * y 1 + conj F E (x 1) * y 0 := rfl

def hypPlane : HermitianForm F E (Fin 2 → E) where
  toSesq := hypPlaneSesq F E
  isSymm := ⟨fun x y => by
    change conj F E (hypPlaneSesq F E x y) = hypPlaneSesq F E y x
    simp only [hypPlaneSesq_apply, map_add, map_mul, conj_conj]
    ring⟩
  nonsingular := by
    refine ⟨fun x x' h => ?_, fun φ => ?_⟩
    · have h0 := LinearMap.congr_fun h (Pi.single 1 1)
      have h1 := LinearMap.congr_fun h (Pi.single 0 1)
      simp only [hypPlaneSesq_apply, Pi.single_apply] at h0 h1
      norm_num at h0 h1
      have e0 : x 0 = x' 0 := by simpa using congrArg (conj F E) h0
      have e1 : x 1 = x' 1 := by simpa using congrArg (conj F E) h1
      funext i
      fin_cases i
      · exact e0
      · exact e1
    · refine ⟨![conj F E (φ (Pi.single 1 1)), conj F E (φ (Pi.single 0 1))], ?_⟩
      refine LinearMap.ext fun y => ?_
      have hy : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 := by
        funext i; fin_cases i <;> simp
      conv_rhs => rw [hy]
      simp only [hypPlaneSesq_apply, map_add, map_smul, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, conj_conj]
      ring

end Example

end UnitaryReduction

end GroundTheory.Heights₂.Theta
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

open NumberField GroundTheory.Automorphic Module TensorProduct FunctionalEquationAlt FunctionalEquationAlt.MetSpace
open scoped InnerProductSpace nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

section Places

variable {S S' : MetSpace E}

variable (S)

def hsInner {τ : InfinitePlace E} (X Y : S.FibSp τ →ₗ[ℂ] S'.FibSp τ) : ℝ :=
  (LinearMap.trace ℂ (S'.FibSp τ) (X ∘ₗ LinearMap.adjoint Y)).re

def eucl (T T' : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) : ℝ :=
  ∑ τ, hsInner S (T τ) (T' τ)

end Places

section Frame

variable (S : MetSpace E) (B : HermitianForm F E S.V)
  (θ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S.FibSp τ)

def formAt (τ : InfinitePlace E) (u v : S.FibSp τ) : ℂ := ⟪θ τ u, v⟫_ℂ

def rPrime (W : Submodule E S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  (S.fibSub W τ).map (θ τ)

def mPrime (W : Submodule E S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  ((S.fibSub W τ ⊔ rPrime S θ W τ).map (θ τ))ᗮ

def nnAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {X | (∀ u v, formAt S θ τ (X u) v + formAt S θ τ u (X v) = 0) ∧
    (∀ y, X y ∈ S.fibSub (perp B W) τ) ∧ (∀ y ∈ S.fibSub (perp B W) τ, X y ∈ S.fibSub W τ) ∧
    ∀ y ∈ S.fibSub W τ, X y = 0}

def zzAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {X | X ∈ nnAt S B θ W τ ∧ ∀ y ∈ S.fibSub (perp B W) τ, X y = 0}

def vvAt (W : Submodule E S.V) (τ : InfinitePlace E) : Set (S.FibSp τ →ₗ[ℂ] S.FibSp τ) :=
  {A | (∀ y ∈ S.fibSub (perp B W) τ, A y = 0) ∧ ∀ y, A y ∈ S.fibSub W τ}

def plusAt {τ : InfinitePlace E} (A : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : S.FibSp τ →ₗ[ℂ] S.FibSp τ :=
  θ τ ∘ₗ LinearMap.adjoint A ∘ₗ θ τ

def sgAt {τ : InfinitePlace E} (A : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : S.FibSp τ →ₗ[ℂ] S.FibSp τ :=
  -plusAt S θ A

end Frame

section Lattices

variable {S S' : MetSpace E}

def homSpace (A : Submodule E S.V) (B' : Submodule E S'.V) :
    Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) :=
  {T | ∀ τ, (∀ y ∈ (S.fibSub A τ)ᗮ, T τ y = 0) ∧ ∀ y, T τ y ∈ S'.fibSub B' τ}

def homImage (A : Submodule (𝓞 E) S.V) (B' : Submodule (𝓞 E) S'.V) :
    Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) :=
  {T | T ∈ homSpace (espan A) (espan B') ∧ ∃ U : S.V →ₗ[E] S'.V, (∀ a ∈ A, U a ∈ B') ∧
    ∀ τ, ∀ a ∈ A, T τ (S.pt τ a) = S'.pt τ (U a)}

variable (S)

def euclDual (𝕍 Γ : Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ)) :
    Set (∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ) :=
  {v | v ∈ 𝕍 ∧ ∀ γ ∈ Γ, ∃ z : ℤ, eucl S v γ = z}

end Lattices

def invDiff (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ 1

section Statements

def hsNorm (S : MetSpace E) {τ : InfinitePlace E} (X : S.FibSp τ →ₗ[ℂ] S.FibSp τ) : ℝ :=
  Real.sqrt (hsInner S X X)

def WittDecomp.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V), SatIn R X.L → IsIsotropic X.B R →
  let S := X.S
  let B := X.B
  let θ := X.θ
  ∀ τ : InfinitePlace E,
    let Rτ := S.fibSub (espan R) τ
    let Pτ := S.fibSub (perp B (espan R)) τ
    let R' := rPrime S θ (espan R) τ
    let M' := mPrime S θ (espan R) τ
    ((∀ u ∈ R', ∀ v ∈ R', formAt S θ τ u v = 0) ∧ Pτᗮ = R' ∧ Pτ ⊓ Rτᗮ = M' ∧
      Rτ ⟂ M' ∧ Rτ ⟂ R' ∧ M' ⟂ R' ∧ Rτ ⊔ M' ⊔ R' = ⊤ ∧
      Rτ ⊔ M' = Pτ ∧ Rτ ⊓ M' = ⊥ ∧ (∀ m ∈ M', Metric.infDist m (Rτ : Set (S.FibSp τ)) = ‖m‖) ∧
      R' ⊔ Pτ = ⊤ ∧ R' ⊓ Pτ = ⊥ ∧ (∀ y ∈ R', Metric.infDist y (Pτ : Set (S.FibSp τ)) = ‖y‖)) ∧
    ((∀ (j : ℕ) (r : OrthonormalBasis (Fin j) ℂ Rτ),
        Orthonormal ℂ (fun i => θ τ (r i : S.FibSp τ)) ∧
        Submodule.span ℂ (Set.range fun i => θ τ (r i : S.FibSp τ)) = R' ∧
        ∀ i l, formAt S θ τ (θ τ (r l : S.FibSp τ)) (r i : S.FibSp τ) = if i = l then 1 else 0) ∧
      ∀ y ∈ R', ‖(innerSL ℂ (θ τ y)).comp Rτ.subtypeL‖ = ‖y‖) ∧
    M'.map (θ τ) = M'

def BlocksAt.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V), SatIn R X.L → IsIsotropic X.B R →
  let S := X.S
  let B := X.B
  let θ := X.θ
  ∀ τ : InfinitePlace E,
    let PR : S.FibSp τ →ₗ[ℂ] S.FibSp τ := (S.fibSub (espan R) τ).starProjection
    let PM : S.FibSp τ →ₗ[ℂ] S.FibSp τ := (mPrime S θ (espan R) τ).starProjection
    let PR' : S.FibSp τ →ₗ[ℂ] S.FibSp τ := (rPrime S θ (espan R) τ).starProjection
    (∀ X ∈ nnAt S B θ (espan R) τ,
      X = X ∘ₗ PM + PR ∘ₗ X ∘ₗ PR' + PM ∘ₗ X ∘ₗ PR' ∧
      PM ∘ₗ X ∘ₗ PR' = -(θ τ ∘ₗ LinearMap.adjoint (X ∘ₗ PM) ∘ₗ θ τ) ∧
      hsNorm S (PM ∘ₗ X ∘ₗ PR') = hsNorm S (X ∘ₗ PM) ∧
      hsNorm S X ^ 2 = 2 * hsNorm S (X ∘ₗ PM) ^ 2 + hsNorm S (PR ∘ₗ X ∘ₗ PR') ^ 2) ∧
    (∀ X, X ∈ zzAt S B θ (espan R) τ ↔ X ∈ nnAt S B θ (espan R) τ ∧ X ∘ₗ PM = 0) ∧
    ∀ X ∈ nnAt S B θ (espan R) τ,
      (∀ Z ∈ zzAt S B θ (espan R) τ, hsInner S X Z = 0) ↔ PR ∘ₗ X ∘ₗ PR' = 0

def WW {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {A | (∀ y ∈ perp B W, A y = 0) ∧ (∀ y, A y ∈ W) ∧ IsIntegralMul L 1 A}

def SkewCentre.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V), SatIn R X.L → IsIsotropic X.B R →
  let S := X.S
  let B := X.B
  let θ := X.θ
  (∀ τ : InfinitePlace E,
      (∀ A ∈ vvAt S B (espan R) τ, sgAt S θ A ∈ vvAt S B (espan R) τ ∧ sgAt S θ (sgAt S θ A) = A) ∧
      (∀ A ∈ vvAt S B (espan R) τ, ∀ A' ∈ vvAt S B (espan R) τ,
        hsInner S (sgAt S θ A) (sgAt S θ A') = hsInner S A A') ∧
      (∀ A, A ∈ zzAt S B θ (espan R) τ ↔ A ∈ vvAt S B (espan R) τ ∧ sgAt S θ A = A) ∧
      ∀ (j : ℕ) (r : OrthonormalBasis (Fin j) ℂ (S.fibSub (espan R) τ)),
        ∀ A ∈ vvAt S B (espan R) τ, ∀ i l,
          ⟪(r i : S.FibSp τ), plusAt S θ A (θ τ (r l : S.FibSp τ))⟫_ℂ =
            starRingEnd ℂ ⟪(r l : S.FibSp τ), A (θ τ (r i : S.FibSp τ))⟫_ℂ) ∧
    (∀ A : S.V →ₗ[E] S.V, (∀ y ∈ perp B (espan R), A y = 0) → (∀ y, A y ∈ espan R) →
      (A ∈ WW B X.L (espan R) ↔ ∀ u ∈ X.L, ∀ u' ∈ X.L, B.toSesq u' (A u) ∈ Set.range (algebraMap (𝓞 E) E))) ∧
    ∀ A ∈ WW B X.L (espan R), ∃ A' ∈ WW B X.L (espan R), ∀ τ, sgAt S θ (S.fibMap S A τ) = S.fibMap S A' τ

def DualHom.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (S S' : MetSpace E) (A : Submodule (𝓞 E) S.V) (B' : Submodule (𝓞 E) S'.V), A.FG → B'.FG →
    euclDual S (homSpace (espan A) (espan B')) (homImage A B') =
      {T | ∃ U : S'.V →ₗ[E] S.V,
        (∀ b ∈ B', U b ∈ smulIdeal (FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E) A) ∧
        ∀ τ, T τ = LinearMap.adjoint
          (S'.fibMap S U τ ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ))}

end Statements

end UnitaryReduction

end GroundTheory.Heights₂.Theta
end
end
