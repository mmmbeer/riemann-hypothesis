import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.TeichmullerFactorisation

def laSer (l : ℕ) [Fact l.Prime] {σ : Type} (back : ℕ → σ) : MvPowerSeries σ ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (back e) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

section Beta

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

def CoefProp (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop := GL3Theta.CoefWf be

def TeichInv (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be

def degEven (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if Even s.val then n s else 0

def degOdd (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if Even s.val then 0 else n s

def NoLowTerms (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ n : ZMod d →₀ ℕ, (degEven n = 0 ∨ degOdd n = 0 ∨ (degEven n = 1 ∧ degOdd n = 1)) → MvPowerSeries.coeff n be = 0

example : NoLowTerms (0 : MvPowerSeries (ZMod d) ℂ_[l]) ∧ TeichInv (0 : MvPowerSeries (ZMod d) ℂ_[l]) :=
  ⟨fun _ _ => by simp, fun _ _ => map_zero _⟩

example : ¬ NoLowTerms (MvPowerSeries.monomial (Finsupp.single (0 : ZMod 2) 1 + Finsupp.single 1 1) (1 : ℂ_[l])) := by
  intro h
  have := h (Finsupp.single (0 : ZMod 2) 1 + Finsupp.single 1 1) (Or.inr (Or.inr ⟨?_, ?_⟩))
  · simp at this
  all_goals
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    have hv : (1 : ZMod 2).val = 1 := rfl
    simp [degEven, degOdd, hu, Finset.sum_pair h01, hv, h01, h01.symm]

end Beta

section Local

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[l])

def embL (x : D.host.E) : D.what₂.Tau → ℂ_[l] × ℂ_[l] :=
  fun τ => (TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ x), TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (D.host.conj x)))

def OEl : Set (D.what₂.Tau → ℂ_[l] × ℂ_[l]) := closure (Set.range fun a : 𝓞 D.host.E => embL D lam (a : D.host.E))

def latL {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l]) :=
  closure ((fun x : Fin N → D.host.E => fun k => embL D lam (x k)) '' (L : Set (Fin N → D.host.E)))

def OrthoL {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (m : Fin N → Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l]) : Prop :=
  (∀ a, m a ∈ latL D lam L) ∧
  (∀ a a' τ, GL3Theta.hP (fun k => m a k τ) (fun k => m a' k τ) = if a = a' then 1 else 0) ∧
  ∀ y ∈ latL D lam L, ∃ c : Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l], (∀ a, c a ∈ OEl D lam) ∧
    y = fun k τ => ∑ a, c a τ * m a k τ

def letter (l : ℕ) (z : Bool × G.HH D) (s : ZMod (G.nP D l)) : Bool × G.HH D := posPl D l z s.val

end Local

abbrev Var (D : D7) (N N' : ℕ) : Type := (Bool × G.HH D) × Fin N × Fin N'

def zOf (D : D7) (l : ℕ) [Fact l.Prime] {N N' : ℕ} (x : Var D N N') : MvPowerSeries (Var D N N') ℂ_[l] :=
  laSer l fun e => (letter D l x.1 (-(2 * (e : ZMod (G.nP D l)))), x.2)

def InertNotConj (D : D7) (l : ℕ) : Prop :=
  5 ≤ l ∧ (G.IsResidueClassZero D l ∨ G.IsSg D l) ∧ (G.IsResidueClassZero D l → G.HEv D l)

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (m : Fin (D.R.N i) → Fin (D.R.N i) → D.what₂.Tau →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (m' : Fin (D.R.N (i + 1)) → Fin (D.R.N (i + 1)) → D.what₂.Tau →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      OrthoL D (E.lam w) (O.lat i c).1 m ∧ OrthoL D (E.lam w) (O.lat (i + 1) c').1 m' ∧ (∀ τ, ‖c0 τ‖ = 1) ∧
      E.Th u μ w i c c' =
        linAt (fun (k : D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i)) (x : Var D (D.R.N i) (D.R.N (i + 1))) =>
          if tauPl D x.1 = k.1 then c0 k.1 * ((m' x.2.2 k.2.1 k.1).1 * (m x.2.1 k.2.2 k.1).2) else 0)
          (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

end GlobalTheory.IndefiniteRowSideFullHecke.TeichmullerFactorisation
