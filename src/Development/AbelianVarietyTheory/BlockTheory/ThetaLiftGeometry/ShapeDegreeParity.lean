import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShapeDegreeParity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

section Local

variable (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]

def laSer (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun α => ∑ e ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

variable {d}

def laAt {σ : Type} (t : ZMod d → MvPowerSeries σ ℂ_[l]) (s : ZMod d) : MvPowerSeries σ ℂ_[l] :=
  MvPowerSeries.subst t (laSer l d s)

variable {l}

end Local

abbrev Lt (D : D7) : Type := Bool × HH D

abbrev Var (D : D7) (N N' : ℕ) : Type := Lt D × Fin N × Fin N'

def CaseA (D : D7) (l : ℕ) : Prop := 5 ≤ l ∧ InertK D l ∧ (IsResidueClassZero D l → Formalism.MainNotions.G.HEv D l)

section Coord

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoZ (z : Lt D) : D.host.E → ℂ_[l] := tauEmb D lam (tauPl D z)

def Ow (r : Lt D) (ε : ℕ) : Set (ZMod (nP D l) → ℂ_[l]) :=
  closure (Set.range fun a : 𝓞 D.host.E => fun s : ZMod (nP D l) =>
    if s.val % 2 = ε then rhoZ D lam (posPl D l r s.val) (a : D.host.E) else 0)

variable (l)

def zSer {N N' : ℕ} (x : Var D N N') : MvPowerSeries (Var D N N') ℂ_[l] :=
  laAt l (fun s : ZMod (nP D l) => MvPowerSeries.X ((posPl D l x.1 s.val, x.2) : Var D N N')) 0

variable {l}

def beSum (N N' : ℕ) (r : Lt D) (be : MvPowerSeries (ZMod (nP D l)) ℂ_[l]) : MvPowerSeries (Var D N N') ℂ_[l] :=
  ∑ a : Fin N, ∑ b : Fin N',
    MvPowerSeries.subst (fun s : ZMod (nP D l) => zSer D l ((posPl D l r s.val, a, b) : Var D N N')) be

def Shape {N N' : ℕ} (T : Finset (Lt D)) (be : Lt D → MvPowerSeries (ZMod (nP D l)) ℂ_[l]) (κ : Lt D → ℂ_[l])
    (Θ : MvPowerSeries (Var D N N') ℂ_[l]) : Prop :=
  ∃ U : MvPowerSeries (Var D N N') ℂ_[l], IntegralMv U ∧
    MvPowerSeries.subst (fun x : Var D N N' => MvPowerSeries.C (κ x.1) * zSer D l x) Θ =
      U * ∏ r ∈ T, expMv (-beSum D N N' r (be r))

end Coord

def KerTie (D : D7) (T : Tor D) (e : FamE D) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
    (O : LiftObj D C) (i : ℕ) : Prop :=
  ∀ c c', IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')

end GlobalTheory.IndefiniteRowSideFullHecke.ShapeDegreeParity
