import Formalism.WachLatticeTwists.WachProductBases.NontrivialWachExample
import Formalism.WachLatticeTwists.HodgeTateChains.UnitCongruenceGivesPerturbation

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JW

open Matrix Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
open scoped TensorProduct

def xOf {As : Type} [CommRing As] (ℓ s : ℕ) (πs : As) : As := (1 + πs) ^ (ℓ ^ (s - 1)) - 1

def xiOf {As : Type} [CommRing As] (ℓ s : ℕ) (πs : As) : As :=
  ∑ k ∈ Finset.range ℓ, ((ℓ.choose (k + 1) : ℕ) : As) * xOf ℓ s πs ^ k

section prod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

def InN (W : NData S ι pr D) (x : ι → D) : Prop := ∀ i, x i ∈ W.N i

def Phi (W : NData S ι pr D) (x : ι → D) : ι → D := fun i => W.φ i (x (pr i))

def GenO (O : Type) {A : Type} [CommRing O] [CommRing A] [Algebra O A] {ι As : Type} [CommRing As]
    (jS : As →+* (ι → A)) : Prop :=
  ∀ a : ι → A, ∃ (n : ℕ) (c : Fin n → As) (o : Fin n → O),
    a = ∑ k, jS (c k) * (fun _ => algebraMap O A (o k))

structure BasisN {As : Type} [CommRing As] (W : NData S ι pr D) (jS : As →+* (ι → A)) {r : ℕ}
    (b : Fin r → ι → D) : Prop where
  mem : ∀ k, InN W (b k)
  span : ∀ x, InN W x → ∃ c : Fin r → As, x = ∑ k, jS (c k) • b k
  ind : ∀ c : Fin r → As, ∑ k, jS (c k) • b k = 0 → c = 0

end prod

def galT {ℓ : ℕ} [Fact ℓ.Prime] {WC : Type} [CommRing WC] [Algebra ℤ_[ℓ] WC] {Gg : Type} [Group Gg]
    (act : Gg →* (WC ≃+* WC)) {r : ℕ} (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (g : Gg)
    (v : Fin r → WC) : Fin r → WC :=
  (fun j => act g (v j)) ᵥ* (ρ g).map (algebraMap ℤ_[ℓ] WC)

structure Cmp {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
    {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jS : As →+* (ι → A)) (jA : As →+* AA) (io : AA →+* WC) (φ : WC →+* WC)
    {Gg : Type} [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC)) {r : ℕ}
    (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) where
  cmp : (ι → D) →+ (Fin r → WC)
  smul : ∀ (a : As) (x : ι → D), cmp (jS a • x) = io (jA a) • cmp x
  phi : ∀ x, cmp (Phi W x) = fun j => φ (cmp x j)
  fixH : ∀ h ∈ H, ∀ x, galT act ρ h (cmp x) = cmp x

section named

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {S : HidaSetting O A} {ι : Type}
  {pr : Equiv.Perm ι} {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {W : NData S ι pr D} {ℓ : ℕ} [Fact ℓ.Prime] {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC]
  [Algebra ℤ_[ℓ] WC] {jS : As →+* (ι → A)} {jA : As →+* AA} {io : AA →+* WC} {φ : WC →+* WC}
  {Gg : Type} [Group Gg] {H : Subgroup Gg} {act : Gg →* (WC ≃+* WC)} {r : ℕ}
  {ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]}

def xMat (C : Cmp W jS jA io φ H act ρ) (b : Fin r → ι → D) : Matrix (Fin r) (Fin r) WC :=
  Matrix.of fun k j => C.cmp (b k) j

def ComparisonMatrixInvertible (C : Cmp W jS jA io φ H act ρ) (b : Fin r → ι → D) : Prop :=
  ∃ Xi : Matrix (Fin r) (Fin r) WC, xMat C b * Xi = 1 ∧ Xi * xMat C b = 1

def TrivAt (C : Cmp W jS jA io φ H act ρ) (πs : As) (g : Gg) : Prop :=
  ∀ x, InN W x → ∃ x', InN W x' ∧ galT act ρ g (C.cmp x) = C.cmp x + C.cmp (jS πs • x')

def GammaTrivialModUniformizers (C : Cmp W jS jA io φ H act ρ) (πs : As) : Prop := ∀ g, TrivAt C πs g

end named

structure HypWf (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (πs ξ : As) (M0 h0 : ℕ) where
  Xx : Matrix (Fin r) (Fin r) WC
  Xi : Matrix (Fin r) (Fin r) WC
  inv1 : Xx * Xi = 1
  inv2 : Xi * Xx = 1
  fixH : ∀ h ∈ H, Xx.map (act h) * ((ρ h).map (algebraMap ℤ_[ℓ] WC)) = Xx
  P : Matrix (Fin r) (Fin r) WC
  W1 : Xx.map φ = P * Xx
  P1 : Matrix (Fin r) (Fin r) As
  map_eq_xi_power_smul : (P1.map jA).map ι = (ι (jA ξ)) ^ M0 • P
  Q1 : Matrix (Fin r) (Fin r) As
  product_eq_xi_power_smul_one : P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)
  Gm : Gg → Matrix (Fin r) (Fin r) As
  W2 : ∀ g, Xx.map (act g) * ((ρ g).map (algebraMap ℤ_[ℓ] WC)) = ((Gm g).map jA).map ι * Xx
  W3 : ∀ g i j, (Gm g - 1) i j ∈ Ideal.span {(ℓ : As), πs}
  W4 : ∀ E : Matrix (Fin r) (Fin r) ℤ_[ℓ], (∀ g, E * ρ g = ρ g * E) →
    ∃ E' : Matrix (Fin r) (Fin r) As, Xx * E.map (algebraMap ℤ_[ℓ] WC) = (E'.map jA).map ι * Xx

def StatXi : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι As : Type) [CommRing As]
    (jS : As →+* (ι → A)) (πs : As), (∀ i, jS πs i = S.π) →
    (∀ i, jS (xOf S.ℓ S.s πs) i = S.X) ∧ (∀ i, jS (xiOf S.ℓ S.s πs) i = S.Q) ∧
    (∃ t : As, xOf S.ℓ S.s πs = πs * t) ∧
    (1 + xOf S.ℓ S.s πs) ^ S.ℓ - 1 = xOf S.ℓ S.s πs * xiOf S.ℓ S.s πs

def StatFree : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A) (ι : Type)
    (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : NData S ι pr D) (As : Type) [CommRing As] (jS : As →+* (ι → A)) (κ : Type) [Fintype κ]
    (e : κ → O) (r₀ r : ℕ) (c : ι → Fin r₀ → D) (eq : κ × Fin r₀ ≃ Fin r),
    (∀ a : ι → A, ∃! d : κ → As, a = ∑ k, jS (d k) * (fun _ => algebraMap O A (e k))) →
    (∀ i m, c i m ∈ W.N i) →
    (∀ i, ∀ x ∈ W.N i, ∃ a : Fin r₀ → A, x = ∑ m, a m • c i m) →
    (∀ i (a : Fin r₀ → A), ∑ m, a m • c i m = 0 → a = 0) →
    BasisN W jS (fun k i => e (eq.symm k).1 • c i (eq.symm k).2) ∧ GenO O jS

def HeightBoundFromFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (S : HidaSetting O A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) (As AA WC : Type) [CommRing As] [CommRing AA]
    [CommRing WC] [Algebra ℤ_[ℓ] WC] (jS : As →+* (ι → A)) (φs : As →+* As) (jA : As →+* AA)
    (io : AA →+* WC) (φ : WC →+* WC) (Gg : Type) [Group Gg] (H : Subgroup Gg)
    (act : Gg →* (WC ≃+* WC)) (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (πs : As)
    (C : Cmp W jS jA io φ H act ρ) (b : Fin r → ι → D) (M h : ι → ℕ) (M0 h0 : ℕ)
    (Xi : Matrix (Fin r) (Fin r) WC),
    (∀ i, jS πs i = S.π) → (∀ a i, jS (φs a) i = S.φ (jS a (pr i))) → GenO O jS → BasisN W jS b →
    W.P5 M h → (∀ i, M i ≤ M0) → (∀ i, h i ≤ h0) →
    xMat C b * Xi = 1 → Xi * xMat C b = 1 →
    ∃ (P : Matrix (Fin r) (Fin r) WC) (P1 Q1 : Matrix (Fin r) (Fin r) As),
      (xMat C b).map φ = P * xMat C b ∧
      (P1.map jA).map io = (io (jA (xiOf S.ℓ S.s πs))) ^ M0 • P ∧
      P1 * Q1 = (xiOf S.ℓ S.s πs ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)

end Formalism.RepresentationBoundsCohomology.JW
