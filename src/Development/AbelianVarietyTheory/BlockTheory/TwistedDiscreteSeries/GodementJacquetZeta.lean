import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

def IsLevelOneConstituent (σ : Representation ℂ (GL n k) V) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL n 𝓀[k]) Y) : Prop :=
  τ.IsIrreducible ∧ ∃ f : Y →ₗ[ℂ] V, Function.Injective f ∧
    ∀ (g : GL n 𝒪[k]) (y : Y),
      σ (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) (f y) =
        f (τ (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g) y)

def TwistPlace (σ : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  IsSpherical σ ∧ ¬ IsUnram μ

abbrev blockSizes (r t j : ℕ) : Fin (j + 1) → ℕ := Fin.cons r fun _ => t

theorem sum_blockSizes (r t j : ℕ) : ∑ a, blockSizes r t j a = r + j * t := by
  simp [Fin.sum_univ_succ]

def chainLevi {r : ℕ} (t : ℕ) {j : ℕ} (σ : Representation ℂ (GL (Fin r) k) V)
    (μ : Fin j → kˣ →* ℂˣ) :
    Representation ℂ (Levi k fun a => Fin (blockSizes r t j a)) V :=
  twist (σ.comp (Pi.evalMonoidHom (fun a => GL (Fin (blockSizes r t j a)) k) 0))
    (∏ i : Fin j, (detChar (Fin (blockSizes r t j i.succ)) (μ i)).comp
      (Pi.evalMonoidHom (fun a => GL (Fin (blockSizes r t j a)) k) i.succ))

def chain {r : ℕ} (t : ℕ) {j : ℕ} (σ : Representation ℂ (GL (Fin r) k) V) (μ : Fin j → kˣ →* ℂˣ) :=
  parInd (stdBlocks (blockSizes r t j) (sum_blockSizes r t j)) (chainLevi t σ μ)

def NoUnramTwist (π : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  ∀ ν : kˣ →* ℂˣ, IsUnram ν → ¬ InSupport π (μ * ν)

variable [MeasurableSpace k] [BorelSpace k]

def gjIntegrand (π : Representation ℂ (GL n k) V) (Φ : Matrix n n k → ℂ) (v : V)
    (l : smoothPart π.dual) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * (l : Module.Dual ℂ V) (π g v) *
    (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

end Local

section Examples

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

example {N : ℕ} (μ : kˣ →* ℂˣ) : ¬ NoUnramTwist (detRep (Fin (N + 1)) μ) μ := fun h =>
  h _ (isUnram_absPow k _) (inSupport_detRep μ 0)

example {N : ℕ} {μ : kˣ →* ℂˣ} (h : ¬ IsUnram μ) : TwistPlace (detRep (Fin N) (1 : kˣ →* ℂˣ)) μ :=
  ⟨isSpherical_detRep fun _ _ => rfl, h⟩

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces
