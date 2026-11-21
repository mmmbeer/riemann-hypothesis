import Mathlib

section
noncomputable section

namespace Formalism.LatticeLocalGlobalTheory

open IsDedekindDomain

def locAt {R EE : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup EE] [Module R EE]
    (w : HeightOneSpectrum R) (M : Submodule R EE) : Set EE :=
  {x : EE | ∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ M}

def LatticeLocalGlobal : Prop :=
  ∀ (R L EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (Λ₀ : Submodule R EE) (Λ : HeightOneSpectrum R → Submodule R EE)
    (S : Finset (HeightOneSpectrum R)),
    Λ₀.FG → Submodule.span L (Λ₀ : Set EE) = ⊤ →
    (∀ (w : HeightOneSpectrum R) (s : R), s ∉ w.asIdeal → ∀ x : EE, s • x ∈ Λ w → x ∈ Λ w) →
    (∀ w : HeightOneSpectrum R, w ∉ S → (Λ w : Set EE) = locAt w Λ₀) →
    (∀ w ∈ S, ∃ a : R, a ≠ 0 ∧ (∀ x ∈ locAt w Λ₀, a • x ∈ Λ w) ∧
      (∀ x ∈ Λ w, a • x ∈ locAt w Λ₀)) →
    (⨅ w, Λ w).FG ∧ Submodule.span L ((⨅ w, Λ w : Submodule R EE) : Set EE) = ⊤ ∧
      ∀ w, locAt w (⨅ w', Λ w') = (Λ w : Set EE)

def gram {K M n : Type} [CommRing K] [StarRing K] [AddCommGroup M] [Module K M]
    (B : M →ₗ⋆[K] M →ₗ[K] K) (v : n → M) : Matrix n n K :=
  Matrix.of fun i j => B (v i) (v j)

def GramChange : Prop :=
  ∀ (K M n : Type) [CommRing K] [StarRing K] [AddCommGroup M] [Module K M] [Fintype n]
    [DecidableEq n] (B : M →ₗ⋆[K] M →ₗ[K] K) (v : n → M) (g : Matrix n n K),
    gram B (fun j => ∑ i, g i j • v i) = g.conjTranspose * gram B v * g ∧
    (gram B (fun j => ∑ i, g i j • v i)).det = star g.det * g.det * (gram B v).det

def DualGram : Prop :=
  ∀ (K M n : Type) [Field K] [StarRing K] [AddCommGroup M] [Module K M] [Fintype n]
    [DecidableEq n] (B : M →ₗ⋆[K] M →ₗ[K] K), (∀ x y, star (B x y) = B y x) →
    ∀ (v : Module.Basis n K M) (w : n → M),
      (∀ i j, B (w i) (v j) = if i = j then 1 else 0) →
      gram B w = (gram B v)⁻¹ ∧ (gram B w).det * (gram B v).det = 1

end Formalism.LatticeLocalGlobalTheory
end
end

section
noncomputable section

namespace Formalism.LatticeLocalGlobalTheory

open IsDedekindDomain

def LatticeLocalGlobalOfGlobal : Prop :=
  ∀ (R L EE : Type) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] [AddCommGroup EE] [Module L EE] [Module R EE] [IsScalarTower R L EE]
    (Λ₀ : Submodule R EE) (Λ' : HeightOneSpectrum R → Submodule R EE)
    (S : Finset (HeightOneSpectrum R)),
    Λ₀.FG → Submodule.span L (Λ₀ : Set EE) = ⊤ →
    (∀ w, (Λ' w).FG) → (∀ w, Submodule.span L (Λ' w : Set EE) = ⊤) →
    (∀ w, w ∉ S → Λ' w = Λ₀) →
    ∃ RR : Submodule R EE, (RR : Set EE) = {x : EE | ∀ w, x ∈ locAt w (Λ' w)} ∧ RR.FG ∧
      Submodule.span L (RR : Set EE) = ⊤ ∧ ∀ w, locAt w RR = locAt w (Λ' w)

def gramσ {K M n : Type} [CommRing K] [AddCommGroup M] [Module K M] (σ : K →+* K)
    (B : M →ₛₗ[σ] M →ₗ[K] K) (v : n → M) : Matrix n n K :=
  Matrix.of fun i j => B (v i) (v j)

def GramChangeσ : Prop :=
  ∀ (K M n : Type) [CommRing K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]
    (σ : K →+* K) (B : M →ₛₗ[σ] M →ₗ[K] K) (v : n → M) (g : Matrix n n K),
    gramσ σ B (fun j => ∑ i, g i j • v i) = (g.map σ).transpose * gramσ σ B v * g ∧
    (gramσ σ B (fun j => ∑ i, g i j • v i)).det = σ g.det * g.det * (gramσ σ B v).det

def DualGramσ : Prop :=
  ∀ (K M n : Type) [Field K] [AddCommGroup M] [Module K M] [Fintype n] [DecidableEq n]
    (σ : K →+* K) (B : M →ₛₗ[σ] M →ₗ[K] K), (∀ x y, σ (B x y) = B y x) →
    ∀ (v : Module.Basis n K M) (w : n → M),
      (∀ i j, B (w i) (v j) = if i = j then 1 else 0) →
      gramσ σ B w = (gramσ σ B v)⁻¹ ∧ (gramσ σ B w).det * (gramσ σ B v).det = 1

end Formalism.LatticeLocalGlobalTheory
end
end
