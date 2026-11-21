import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.DownChainSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup GlobalTheory.CompanionTheory.Sep
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.UnitaryDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Place

variable {r n : ℕ}

def vnorm (y : Fin n → ℂ) : ℝ := Real.sqrt (∑ i, ‖y i‖ ^ 2)

def embM (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) (h : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ι * h * ιᴴ + vecMulVec z (star z)

structure IsAdapted (ε : Fin r → Bool) (ε' : Fin n → Bool) (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  rank : r + 1 = n
  orth : ιᴴ * ι = 1
  perp : ιᴴ *ᵥ z = 0
  unit : star z ⬝ᵥ z = 1
  form : Formalism.REAL.Jm ε' * ι = ι * Formalism.REAL.Jm ε
  formz : Formalism.REAL.Jm ε' *ᵥ z = z

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def coef (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ := ⟪v, π g v⟫_ℂ

structure PlaceOK (ε : Fin r → Bool) (ε' : Fin n → Bool) (ι : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin r) (Fin r) ℂ → (H' →L[ℂ] H')) (v : H) (w : H')
    (c Λ : ℝ) : Prop where
  unit : ‖v‖ = 1
  ne : w ≠ 0
  pos : 0 < c
  decay : ∃ C : ℝ, ∀ g : Formalism.REAL.UJ ε',
    ‖coef π v (Formalism.MainNotions.S.uMat g)‖ ≤ C * Formalism.REAL.hs (Formalism.MainNotions.S.uMat g) ^ (-(3 * (n : ℝ) ^ 2))
  eigen : ∀ ξ : H', ∫ h : Formalism.REAL.UJ ε, coef π v (embM ι z (Formalism.MainNotions.S.uMat h)) * ⟪ξ, ρ (Formalism.MainNotions.S.uMat h) w⟫_ℂ
    ∂(Formalism.REAL.muG ε) = c * ⟪ξ, w⟫_ℂ
  coset : ∀ g : Formalism.REAL.UJ ε', ∫⁻ h : Formalism.REAL.UJ ε, ‖coef π v (Formalism.MainNotions.S.uMat g * embM ι z (Formalism.MainNotions.S.uMat h))‖ₑ
    ∂(Formalism.REAL.muG ε) ≤ ENNReal.ofReal (c * Λ * vnorm (Formalism.MainNotions.S.uMat g *ᵥ z) ^ (-(2 * (n : ℝ) + 5)))
  lip : ∀ X : Matrix (Fin r) (Fin r) ℂ, Formalism.REAL.inG ε X →
    ∫⁻ h : Formalism.REAL.UJ ε, ‖coef π v (embM ι z (NormedSpace.exp (-X) * Formalism.MainNotions.S.uMat h)) -
      coef π v (embM ι z (Formalism.MainNotions.S.uMat h))‖ₑ ∂(Formalism.REAL.muG ε) ≤ ENNReal.ofReal (c * Λ * Real.sqrt (Formalism.REAL.hs X))

end Place

section Adelic

variable {D : D7} (θ : InfFam D) {Y V : HSp D} {SY SV : D.what₂.Tau → SPar}

variable (V) in

def latAt (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (x : GA D V) : Set (Fin V.rank → D.host.E) :=
  {y | (Lev.finE V x⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (y i)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) Λ}

variable (d : HermitianOrthogonalExtensionData Y V 1 1)

def zVec : Fin V.rank → D.host.E := fun i => d.a i 0

def latV (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  d.lat Λ fun _ => 1

def iotaAt (MY : DSModel Y SY) (MV : DSModel V SV) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin Y.rank) ℂ :=
  MV.fr τ * (frameMat V Y d.ι).map (tauE D τ) * (MY.fr τ)⁻¹

def zAt (MV : DSModel V SV) (τ : D.what₂.Tau) : Fin V.rank → ℂ := MV.fr τ *ᵥ fun i => tauE D τ (zVec d i)

structure Std (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) (MY : DSModel Y SY) (MV : DSModel V SV) : Prop where
  fam : IsInfFam θ
  sigY : Y.SigOK
  sigV : V.SigOK
  sdY : IsSelfDualC Y Λ
  sdV : IsSelfDualC V (latV d Λ)
  adapted : ∀ τ, IsAdapted (MY.ε τ) (MV.ε τ) (iotaAt d MY MV τ) (zAt d MV τ)

structure FinOK (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (𝔞 : Ideal (𝓞 D.host.E))
    (K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (J : Set (GA D Y)) (χ : GA D Y → ℂ) (A : ℕ) (kf : GA D V → ℂ) : Prop where
  ne : 𝔞 ≠ ⊥
  opn : IsOpen ((K₀.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))
  inf : ∀ g, ∀ a ∈ GinfC V, kf (g * a) = kf g ∧ kf (a * g) = kf g
  lev : ∀ g, ∀ k ∈ Lev.levA V K₀, kf (g * k) = kf g ∧ kf (k * g) = kf g
  bdd : ∀ g, ‖kf g‖ ≤ 1
  supp : ∀ g, kf g ≠ 0 → Lev.finE V g ∈ congLev D.sp.cm V.gram L 𝔞
  cusp : ∀ (j : ℕ) (C : Matrix (Fin V.rank) (Fin j) D.host.E), IsIsoFrame V C → ∀ x, ∃ s : Finset (GA D V), s.Nonempty ∧
    (∀ u ∈ s, u ∈ NI V C ∧ u ∈ GfC V) ∧ ∀ g, ∑ u ∈ s, kf (g * u * x) = 0
  ident : ∃ U KH : Subgroup (GA D Y),
    (∀ h, h ∈ KH ↔ h ∈ GfC Y ∧ Lev.finE V (stabilizerEmbedding d h) ∈ congLev D.sp.cm V.gram L 𝔞) ∧ U ≤ KH ∧
    U.relIndex KH ≠ 0 ∧ U.relIndex KH ≤ A ∧ (∀ h ∈ U, h ∈ J ∧ kf (stabilizerEmbedding d h) * χ h = 1) ∧
    ∀ h ∈ GfC Y, h ∉ U → kf (stabilizerEmbedding d h) = 0

structure RowOK (MY : DSModel Y SY) (Λ : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)) (g : ℕ) (J : Set (GA D Y))
    (χ : GA D Y → ℂ) (w : MY.Vec) (u : GA D Y → ℂ) : Prop where
  val : ∃ t : MMap MY, IsMultMap θ MY J χ t ∧ u = t w
  ne : u ≠ 0
  bdd : ∃ N : ℝ, ∀ x, ‖u x‖ ≤ N
  pos : 1 ≤ g
  lev : ∀ k ∈ Lev.levA Y (congLev D.sp.cm Y.gram Λ (Ideal.span {(g : 𝓞 D.host.E)})), ∀ x, u (x * k) = u x

end Adelic

def IsGenLevel {D : D7} {Pg : Finset (Pl D.host.E)} (PP : Pg) (ψ₀ : AddChar (kP PP.1) ℂ) (P : LevelP Pg D.R.r ℂ) : Prop :=
  (∀ g : G0 Pg D.R.r, g ∈ P.H ↔ (∀ PP', PP' ≠ PP → g PP' = 1) ∧ (∀ a, (g PP).1 a a = 1) ∧
    ∀ a b, b < a → (g PP).1 a b = 0) ∧
  ∀ g : P.H, ((P.chi g : ℂˣ) : ℂ) = ψ₀ (∑ a : Fin D.R.r, ∑ b : Fin D.R.r,
    if (b : ℕ) = a + 1 then ((g : G0 Pg D.R.r) PP).1 a b else 0)

end GlobalTheory.CompanionTheory.UnitaryDecomposition

end
