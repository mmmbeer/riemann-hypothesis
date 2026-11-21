import Formalism.MahlerMeasure.HasOrder
import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds

section
namespace Formalism.GM.M

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def WtSpC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | ∀ c ∈ Cs, wt LL j c m = la c}

def GlStableC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Prop :=
  ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S

noncomputable def HWC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  WtSpC p LL j Cs la ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ Cs ∧ d ∈ Cs ∧ c < d), LinearMap.ker (glAct p LL j c d)

noncomputable def IsoC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {S | HWC p LL j Cs la ≤ S ∧ GlStableC p LL j Cs S}

def CsSaturated {r : ℕ} (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)) : Prop :=
  ∀ la la', (∀ c ∈ Cs, la c = la' c) → (la ∈ T ↔ la' ∈ T)

def IsTypeProj (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  P ∘ₗ P = P ∧ LinearMap.range P = ⨆ (la : Fin r → ℤ) (_ : la ∈ T), IsoC p LL j Cs la ∧
    LinearMap.ker P = ⨆ (la : Fin r → ℤ) (_ : la ∉ T), IsoC p LL j Cs la

noncomputable def WeylLat (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {L | h ∈ L ∧ ∀ c d : Fin r, c ≠ d → ∀ k : ℕ, ∀ x ∈ L,
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ L}

def Letters.take (LL : Letters N) (k : ℕ) (hk : k ≤ N) : Letters k where
  vec := fun i => LL.vec (Fin.castLE hk i)
  deg := fun i => LL.deg (Fin.castLE hk i)

noncomputable def MMw (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Y p LLw J M ⊓ HWC p LLw K (univ.erase ρ) w ⊓ WtSpC p LLw K univ w

noncomputable def MMwZ (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  (MMw p LLw J M ρ w).restrictScalars ℤ_[p] ⊓ IntPol p (Fin K × Fin r)

noncomputable def FilE (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  MMwZ p LLw J M ρ w ⊓ (MvPolynomial.restrictSupport ℚ_[p] {m | e ≤ m v}).restrictScalars ℤ_[p]

noncomputable def grLat (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Submodule.span ℤ_[p] (initPart v e '' (FilE p LLw J M ρ w v e : Set (MvPolynomial (Fin K × Fin r) ℚ_[p])))

end Formalism.GM.M
end

section
namespace Formalism.GM.M

open MvPolynomial Finset

def HypP (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  (∀ j ≤ N, ∀ Cs : Finset (Fin r), (Cs = univ ∨ Cs = univ.erase ρ) → ∀ T : Set (Fin r → ℤ), CsSaturated Cs T →
    ∃ P, IsTypeProj p LL j Cs T P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)) ∧
  (∀ (j j' : ℕ) (Cs Cs' : Finset (Fin r)) (T T' : Set (Fin r → ℤ)) (P P'), j ≤ j' → Cs' ⊆ Cs →
    (Cs = univ ∨ Cs = univ.erase ρ) → (Cs' = univ ∨ Cs' = univ.erase ρ) →
    IsTypeProj p LL j Cs T P → IsTypeProj p LL j' Cs' T' P' → P ∘ₗ P' = P' ∘ₗ P)

def HypW (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∀ x ∈ IsoC p LL j univ la ⊓ Pol p r LL, x ∈ IntPol p (Fin N × Fin r) →
    ((p : ℚ_[p]) ^ e1) • x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
      (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h

def HypE (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∃ P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
    P ∘ₗ P = P ∧ LinearMap.range P = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la ∧
    LinearMap.ker P ⊓ WtSpC p LL j univ la =
      (⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
        Submodule.map (glAct p LL j c d) ⊤) ⊓ WtSpC p LL j univ la ∧
    (∀ F G, F ∈ WtSpC p LL j univ la → G ∈ WtSpC p LL j univ la → fock p (P F) G = fock p F (P G)) ∧
    ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ la → ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)

def GramDeterminantGradedHypothesis (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (κ : ℝ) : Prop :=
  ∀ (w : Fin r → ℤ) (e k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
    (p : ℝ) ^ (-(κ * k)) ≤ ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖

def BadCrit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ),
    Module.Finite ℤ_[p] L → L₁ ≤ L →
    (∀ (a : ℤ_[p]) (x : Vs), a ≠ 0 → x ∈ L → a • x ∈ L₁ → x ∈ L₁) →
    (∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    bad p (fun x y => be x y) L D ≤ Module.finrank ℤ_[p] L - Module.finrank ℤ_[p] L₁

end Formalism.GM.M
end
