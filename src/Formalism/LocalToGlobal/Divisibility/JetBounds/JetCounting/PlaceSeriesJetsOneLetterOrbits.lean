import Formalism.LocalToGlobal.Divisibility.JetBounds.PlaceInputAllEntries
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.RelShape
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.HasSubstBlock
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.GramFrameCompositionMvExpFact
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.IntOpTwoFreeOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.AgreeOnAdjoin
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenCompatOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFrameEOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFinal

section
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual beMean xOfZ sumE phFF thetaS NormRel expF PV)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob at1)

def CurveAt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1

def HostInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ)

inductive IsHostA (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (N0 N1 : ℕ) :
    (ιr P : Type) → (PV ιr N0 N1 → P) → (S : OrbSys ℂ_[l]) → (P → MvPowerSeries S.ι ℂ_[l]) → MvPowerSeries P ℂ_[l] → ℝ → Prop
  | orbit (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (he : Even d) (hN0 : 0 < N0)
      (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l) (hO : OwOK d σ om oms) (hT : TrDual d σ om oms)
      (ζ : MaximalUnramifiedExtension l) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
      (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
      (nu1 nu2 size : ZMod d → ℕ) (h1 : ∀ s, nu1 s = colN s)
      (h22 : ∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card)
      (hs : ∀ s, size s = ∑ c, p s c)
      (hJ : ∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsHostA l Q σ be0 N0 N1 ιr (PV ιr N0 N1) (fun y => y)
        ((sysA l d N0 N1 (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean l σ be0 om oms ζ)) g (-1) colN p hp I).ap δ)
        (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms) (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))
        (expA l d N0 N1 TT nu1 nu2 size)
  | quoted (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (he : Even d)
      (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l) (hO : OwOK d σ om oms) (hT : TrDual d σ om oms)
      (ζ : MaximalUnramifiedExtension l) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
      (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1) (β : ℝ)
      (hq : Q (sysF l d N0 N1 g (Formalism.DworkPowerSeriesWeights.mvExp ((-1 : ℂ_[l]) • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → ℂ_[l])
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean l σ be0 om oms ζ)))) colN p hp I) β)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsHostA l Q σ be0 N0 N1 ιr (PV ιr N0 N1) (fun y => y)
        ((sysF l d N0 N1 g (Formalism.DworkPowerSeriesWeights.mvExp ((-1 : ℂ_[l]) • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → ℂ_[l])
          (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean l σ be0 om oms ζ)))) colN p hp I).ap δ)
        (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms) (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0)) β
  | mul {ι₁ ι₂ P₁ P₂ : Type} {e₁ : PV ι₁ N0 N1 → P₁} {e₂ : PV ι₂ N0 N1 → P₂} {S₁ S₂ : OrbSys ℂ_[l]}
      {x₁ : P₁ → MvPowerSeries S₁.ι ℂ_[l]} {x₂ : P₂ → MvPowerSeries S₂.ι ℂ_[l]}
      {Ψ₁ : MvPowerSeries P₁ ℂ_[l]} {Ψ₂ : MvPowerSeries P₂ ℂ_[l]} {β₁ β₂ : ℝ}
      (h₁ : IsHostA l Q σ be0 N0 N1 ι₁ P₁ e₁ S₁ x₁ Ψ₁ β₁) (h₂ : IsHostA l Q σ be0 N0 N1 ι₂ P₂ e₂ S₂ x₂ Ψ₂ β₂) :
      IsHostA l Q σ be0 N0 N1 (ι₁ ⊕ ι₂) (P₁ ⊕ P₂)
        (fun y => Sum.elim (fun i => Sum.inl (e₁ (y.1, i, y.2.2))) (fun i => Sum.inr (e₂ (y.1, i, y.2.2))) y.2.1)
        (S₁.mul S₂)
        (Sum.elim (fun q => serAlong Sum.inl (x₁ q)) (fun q => serAlong Sum.inr (x₂ q)))
        (serAlong Sum.inl Ψ₁ + serAlong Sum.inr Ψ₂) (β₁ + β₂)

inductive IsHostB (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (ph : PowerSeries (MaximalUnramifiedExtension l))
    (N0 N1 : ℕ) :
    (P : Type) → (S : OrbSys ℂ_[l]) → (P → MvPowerSeries S.ι ℂ_[l]) → MvPowerSeries P ℂ_[l] → ℝ → Prop
  | orbit (Cn : ℕ) (ζ : MaximalUnramifiedExtension l) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
      (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1)
      (δ : MvPolynomial (Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ minorProductsLattice (k := ℂ_[l]) p hp, ‖δ R‖ ≤ 1) :
      IsHostB l σ be0 ph N0 N1 (Fin N0 × Fin N1)
        ((sysB l N0 N1 Cn (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype
          (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : MaximalUnramifiedExtension l)) (fun _ => 1) ζ)) 1 g (-1) p hp I).ap δ)
        (fun y => at1 y (expF ℂ_[l] l)) (∑ y, at1 y (PowerSeries.map (MaximalUnramifiedExtension l).subtype ph))
        (expB l N0 N1 Cn p)
  | mul {P₁ P₂ : Type} {S₁ S₂ : OrbSys ℂ_[l]}
      {x₁ : P₁ → MvPowerSeries S₁.ι ℂ_[l]} {x₂ : P₂ → MvPowerSeries S₂.ι ℂ_[l]}
      {Ψ₁ : MvPowerSeries P₁ ℂ_[l]} {Ψ₂ : MvPowerSeries P₂ ℂ_[l]} {β₁ β₂ : ℝ}
      (h₁ : IsHostB l σ be0 ph N0 N1 P₁ S₁ x₁ Ψ₁ β₁) (h₂ : IsHostB l σ be0 ph N0 N1 P₂ S₂ x₂ Ψ₂ β₂) :
      IsHostB l σ be0 ph N0 N1 (P₁ ⊕ P₂) (S₁.mul S₂)
        (Sum.elim (fun q => serAlong Sum.inl (x₁ q)) (fun q => serAlong Sum.inr (x₂ q)))
        (serAlong Sum.inl Ψ₁ + serAlong Sum.inr Ψ₂) (β₁ + β₂)

end Formalism.L2.DIV.C
end
end

section
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (phFF thetaS NormRel PV)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open Formalism.L2.Th1.Top (IsHypPair inHyp IsLTNorm IsLatH IsFrameH thetaH)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.L2.Th1.GD (LocNorm thetaLin frameM InMul IsPairFrame)

def PlaceSeriesJetsCyclicOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l])
    (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β → IsSysW l Q S β

def IntegralSeriesCyclicOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l])
    (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ Θ : MvPowerSeries n ℂ_[l], HostInt l g2 g3 s2 ε Θ →
    ∃ U : MvPowerSeries S.ι ℂ_[l], Integral U ∧
      MvPowerSeries.subst x (serAlong e (inHyp l f f' Θ)) = MvPowerSeries.subst S.g U * S.E

def PlaceSeriesJetsOneLetterOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (P : Type) (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostB l σ (cob F (phFF l g2 g3 s2 ε)) (phFF l g2 g3 s2 ε) N0 N1 P S x Ψ β → IsSysW l Q S β

def HostIntFree : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  (∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F →
    CurveAt l g2 g3 s2 ε σ F) ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
    ∃ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix (n) (n) ℂ_[l]), IsFrameH σ ι g₁ γ B') ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → (∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F) →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
    HostInt l g2 g3 s2 ε (thetaH l ι B' h t θ)

end Formalism.L2.DIV.C
end
end
