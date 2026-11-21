import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP

def wR : InfinitePlace ℚ := Rat.infinitePlace

theorem wR_isReal : wR.IsReal := Rat.isReal_infinitePlace

def eR : wR.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal wR_isReal

def gR (g : G3) : GL (Fin 3) ℝ := Units.map eR.toRingHom.mapMatrix.toMonoidHom (Reduction.infAt wR g)

abbrev psiF (v : Pl) : AddChar (Qv v) Circle := localAdelicChar ℚ v

abbrev sph (D : Dat) (v : Pl) : GL (Fin 3) (Qv v) → ℂ := sphW (psiF v) (D.ν v)

def pw (Wi : GL (Fin 3) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 3) (Qv v) → ℂ) (g : G3) : ℂ :=
  Wi (gR g) * ∏ᶠ v, Wf v (Reduction.finAt v g)

structure Loc (D : Dat) where
  VF : ∀ v : Pl, Submodule ℂ (GL (Fin 3) (Qv v) → ℂ)
  hF : ∀ v, WhF (psiF v) (D.ν v) (VF v)
  sp : ∀ v, v ∉ D.bad → sph D v ∈ VF v
  VR : Submodule ℂ (GL (Fin 3) ℝ → ℂ)
  E : Fin 3 → Fin 3 → Module.End ℂ VR
  hR : WhR D.k VR E

variable {D : Dat}

structure IsFac (L : Loc D) (Wi : GL (Fin 3) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 3) (Qv v) → ℂ) : Prop where
  inf : Wi ∈ L.VR
  fin : ∀ v, Wf v ∈ L.VF v
  ae : ∃ S : Finset Pl, ∀ v ∉ S, Wf v = sph D v

def Gen (L : Loc D) : Set (G3 → ℂ) := {W | ∃ Wi Wf, IsFac L Wi Wf ∧ W = pw Wi Wf}

def VA (L : Loc D) : Submodule ℂ (G3 → ℂ) := Submodule.span ℂ (Gen L)

def StdChar : Prop := ∀ v : Pl, IsStd (psiF v)

abbrev md (x : IdeleGroup ℚ) : ℝ := (IdeleGroup.ideleModule ℚ x : ℝ)

abbrev ιQ (a : ℚˣ) : IdeleGroup ℚ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a

def f1 (W : G3 → ℂ) (x : IdeleGroup ℚ) : ℂ := W (dg x 1 1) * ((md x : ℂ) ^ (-(1 / 2 : ℂ)))

def f2 (W : G3 → ℂ) (x : IdeleGroup ℚ) : ℂ :=
  (∫ u, W (mm x u) ∂adeleMeasure ℚ) * ((md x : ℂ) ^ ((1 / 2 : ℂ)))

def Gauge (W : G3 → ℂ) : Prop :=
  ∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)

def GenStable : Prop := StdChar → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L, ∀ h, (fun g => W (g * h)) ∈ Gen L

def IntB : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  Integrable (fun x => ‖f2 W x‖ * md x ^ (-3 : ℝ)) (ideleMeasure ℚ)

def BndI : Prop := StdChar → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  ∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, ∀ x,
    f1 W (x * IdeleGroup.ofFinite u) = f1 W x ∧ f2 W (x * IdeleGroup.ofFinite u) = f2 W x

end Ad3.GP
