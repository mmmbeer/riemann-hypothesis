import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.StatementTheta
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.ThetaLiftIndependence

def kerOp {R ι κ : Type*} [CommSemiring R] [Fintype ι] (w : ι → R) (K : ι → κ → R)
    (f : ι → R) : κ → R :=
  fun j => ∑ i, w i * f i * K i j

def chainOp {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → R) : (m : ℕ) → (ι 0 → R) → (ι m → R)
  | 0, f => f
  | m + 1, f => kerOp (w m) (K m) (chainOp w K m f)

def kerOpM {R ι κ M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Fintype ι]
    (w : ι → R) (K : ι → κ → (M →ₗ[R] N)) (f : ι → M) : κ → N :=
  fun j => ∑ i, w i • K i j (f i)

def chainOpM {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) :
    (m : ℕ) → (ι 0 → M 0) → (ι m → M m)
  | 0, f => f
  | m + 1, f => kerOpM (w m) (K m) (chainOpM w K m f)

def OrbitSum : Prop :=
  ∀ (H X : Type) [Group H] [Fintype H] [MulAction H X] [Fintype X] (k : Type) [Field k]
    [CharZero k] (F : X → k), (∀ (a : H) (x : X), F (a • x) = F x) →
    (Fintype.card H : k)⁻¹ * ∑ x, F x =
      ∑ᶠ o : MulAction.orbitRel.Quotient H X,
        (Nat.card (MulAction.stabilizer H (Quotient.out o)) : k)⁻¹ * F (Quotient.out o)

section Adelic

variable {G : Type} [Group G] {Γ K : Subgroup G}

end Adelic

def orbLift (H : Type*) {X : Type*} [Group H] [MulAction H X] (s : Finset X) (f Θ : X → ℂ) : ℂ :=
  ∑ x ∈ s, ((Nat.card (MulAction.stabilizer H x) : ℕ) : ℂ)⁻¹ * f x * Θ x

section Lat

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def autL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) :
    Set (V ≃ₗ[K] V) :=
  {g | g ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap g L = L}

def latWt (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : ℂ :=
  ((Nat.card (autL h L) : ℕ) : ℂ)⁻¹

def IsClassReps (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (s : Finset (Submodule (NumberField.RingOfIntegers K) V)) : Prop :=
  (∀ M ∈ s, M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧
    ∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃! N, N ∈ s ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M

def latLift (h : V →ₗ⋆[K] V →ₗ[K] K) (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (f Θ : Submodule (NumberField.RingOfIntegers K) V → ℂ) : ℂ :=
  ∑ L ∈ s, latWt h L * f L * Θ L

def thetaLift (h : V →ₗ⋆[K] V →ₗ[K] K) (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (f : Submodule (NumberField.RingOfIntegers K) V → ℂ) (τ : ℂ) : ℂ :=
  latLift h s f (fun L => Formalism.HermitianLatticesTheory.thetaL h L 0 τ)

end Lat

def LatLiftIndep : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (f Θ : Submodule (NumberField.RingOfIntegers K) V → ℂ),
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, f (Formalism.HermitianLatticesTheory.gmap g M) = f M) →
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, Θ (Formalism.HermitianLatticesTheory.gmap g M) = Θ M) →
    ∀ s s', IsClassReps h L s → IsClassReps h L s' → latLift h s f Θ = latLift h s' f Θ

def ClassRepsDefinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
      (∃ s, IsClassReps h L s) ∧
      (∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃ n : ℕ, 0 < n ∧ latWt h M = (n : ℂ)⁻¹) ∧
      (∃ D : ℕ, 0 < D ∧ ∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃ z : ℤ, (D : ℂ) * latWt h M = z)

def gaussOp {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ c

def gaussOpDual {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (-(c : 𝔽)) • ρ c⁻¹

def GaussOp : Prop :=
  ∀ (𝔽 V : Type) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)), ψ ≠ 1 →
    ∀ v : V, ∑ c : 𝔽ˣ, ρ c v = 0 →
      gaussOp ψ ρ (gaussOpDual ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v ∧
      gaussOpDual ψ ρ (gaussOp ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v

def FFPlancherel : Prop :=
  ∀ (𝔽 U : Type) [Field 𝔽] [Fintype 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    [Fintype (Module.Dual 𝔽 U)] (ψ : AddChar 𝔽 ℂ), ψ ≠ 1 →
    ∀ φ φ' : Module.Dual 𝔽 U → ℂ,
      ∑ e : U, star (∑ f, ψ (f e) * φ f) * (∑ f, ψ (f e) * φ' f) =
        (Fintype.card U : ℂ) * ∑ f, star (φ f) * φ' f

def downChain {𝕜 : Type*} [CommSemiring 𝕜] {E : ℕ → Type*} [∀ j, AddCommMonoid (E j)]
    [∀ j, Module 𝕜 (E j)] (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) : (m : ℕ) → (E m →ₗ[𝕜] E 0)
  | 0 => LinearMap.id
  | m + 1 => (downChain T m).comp (T m)

def ChainScalar : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (E : ℕ → Type) [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]
    (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j)) (c : ℕ → 𝕜),
    (∀ j, ∀ x ∈ S j, T j (LinearMap.adjoint (T j) x) = c j • x) →
    (∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) →
    ∀ (m : ℕ), ∀ x ∈ S 0,
      downChain T m (LinearMap.adjoint (downChain T m) x) = (∏ j ∈ Finset.range m, c j) • x

def DetSwap : Prop :=
  ∀ (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F)
    (h₁ : ∀ x ∈ (LinearMap.ker T)ᗮ, (LinearMap.adjoint T ∘ₗ T) x ∈ (LinearMap.ker T)ᗮ)
    (h₂ : ∀ y ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ,
      (T ∘ₗ LinearMap.adjoint T) y ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ),
    LinearMap.det ((LinearMap.adjoint T ∘ₗ T).restrict h₁) =
      LinearMap.det ((T ∘ₗ LinearMap.adjoint T).restrict h₂)

def EigenSwap : Prop :=
  ∀ (𝕜 E F : Type) [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (μ : 𝕜), μ ≠ 0 →
    Module.finrank 𝕜 (Module.End.eigenspace (B ∘ₗ A) μ) =
      Module.finrank 𝕜 (Module.End.eigenspace (A ∘ₗ B) μ)

end Formalism.ThetaLiftIndependence
