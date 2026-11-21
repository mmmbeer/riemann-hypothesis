import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions MeasureTheory GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Lit.JL

def SqInt {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (φ : G → ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  ∃ (μ : Measure G) (S : Set G), μ.IsHaarMeasure ∧ MeasurableSet S ∧ (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) ∧ ∫⁻ g in S, ‖φ g‖ₑ ^ 2 ∂μ < ⊤

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

variable (F) in

def eId : Ideles F := TR.infId F (Units.map (Pi.constRingHom (InfinitePlace F) ℝ).toMonoidHom (Units.mk0 (Real.exp 1) (Real.exp_ne_zero 1)))

def IsUnitary (ω : HChar F) : Prop := ∀ z : Ideles F, ‖((ω.1 z : ℂˣ) : ℂ)‖ = 1

variable (F) in

def latG : Subgroup (GA F 2) := (ratGL F 2).range ⊔ Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar (Fin 2) (eId F))

variable (F) in

structure DiscG where
  V : Submodule ℂ (TR.Sm F 2)
  aut : ∀ φ ∈ V, TR.IsAutForm φ
  stable : TR.IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, TR.IsStable W → W = ⊥ ∨ W = V
  cen : ∃ ω : HChar F, IsUnitary ω ∧ ∀ (z : Ideles F), ∀ φ ∈ V, ∀ g,
    φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g
  sq : ∀ φ ∈ V, SqInt (latG F) φ.1

def LocG (V : Submodule ℂ (TR.Sm F 2)) (w : HeightOneSpectrum (𝓞 F)) (τ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] TR.Sm F 2, f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (τ.ρ g x) = TR.finRep F 2 (locGL F 2 w g) (f x)

def HasCen (V : Submodule ℂ (TR.Sm F 2)) (v : InfinitePlace F) (c : ℂ) : Prop := ∀ φ ∈ V, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = c • φ

def IsChr (V : Submodule ℂ (TR.Sm F 2)) (v : InfinitePlace F) (c : ℂ) : Prop :=
  HasCen V v c ∧ ∀ φ ∈ V, TR.Eop v 0 1 φ = 0 ∧ TR.Eop v 1 0 φ = 0

def IsDS (V : Submodule ℂ (TR.Sm F 2)) (v : InfinitePlace F) (m : ℕ) (c : ℂ) : Prop :=
  HasCen V v c ∧ ∃ φ ∈ V, φ ≠ 0 ∧ TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (m + 2)) • φ ∧
    TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)

def Compatible (V : Submodule ℂ (TR.Sm F 2)) : Prop := ∀ v, ∃ c, IsChr V v c ∨ ∃ m, IsDS V v m c

variable (Q : DefQuat F)

def Hv (v : InfinitePlace F) : Subgroup (GL (Fin 2) ℂ) := (Algebra.adjoin ℝ (Set.range (Q.jc v))).toSubmonoid.units

abbrev DA : Type := (∀ v, Hv Q v) × GL (Fin 2) (Af F)

def toHv (v : InfinitePlace F) : Q.Dˣ →* Hv Q v :=
  (Units.map (Q.jc v).toMonoidHom).codRestrict _ fun γ =>
    ⟨Algebra.subset_adjoin ⟨γ, rfl⟩, Algebra.subset_adjoin ⟨(γ⁻¹ : Q.Dˣ), rfl⟩⟩

def toDA : Q.Dˣ →* DA Q := (Pi.monoidHom (toHv Q)).prod Q.toFin

variable {Q} in

def IsScalar (z : Ideles F) (x : DA Q) : Prop :=
  (∀ v, ((x.1 v : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.scalar (Fin 2) ((TR.pInf F (z : Ad F) v : ℝ) : ℂ)) ∧
    (x.2 : Matrix (Fin 2) (Fin 2) (Af F)) = Matrix.scalar (Fin 2) (pFin F (z : Ad F))

def latD : Subgroup (DA Q) := (toDA Q).range ⊔ Subgroup.closure {x | IsScalar (eId F) x}

abbrev RD : Representation ℂ (DA Q) (DA Q → ℂ) := GlobalTheory.PRep.rightReg ℂ (DA Q) ℂ

structure DiscD where
  V : Submodule ℂ (DA Q → ℂ)
  cont : ∀ φ ∈ V, Continuous φ
  left : ∀ φ ∈ V, ∀ γ g, φ (toDA Q γ * g) = φ g
  level : ∀ φ ∈ V, IsOpen {k : GL (Fin 2) (Af F) | RD Q (1, k) φ = φ}
  kfin : ∀ φ ∈ V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y : ∀ v, Hv Q v => RD Q (y, 1) φ))
  stable : ∀ x, ∀ φ ∈ V, RD Q x φ ∈ V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, (∀ x, ∀ φ ∈ W, RD Q x φ ∈ W) → W = ⊥ ∨ W = V
  cen : ∃ ω : HChar F, IsUnitary ω ∧ ∀ (z : Ideles F) (x : DA Q), IsScalar z x → ∀ φ ∈ V, ∀ g, φ (x * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g
  sq : ∀ φ ∈ V, SqInt (latD Q) φ

variable {Q}

def LocD (V : Submodule ℂ (DA Q → ℂ)) (w : HeightOneSpectrum (𝓞 F)) (τ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] (DA Q → ℂ), f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (τ.ρ g x) = RD Q (1, locGL F 2 w g) (f x)

def symWt (m : ℕ) : DomWeight 2 := ⟨![m, 0], fun i j h => by
  fin_cases i <;> fin_cases j <;> simp_all⟩

open Classical in

def InfD (V : Submodule ℂ (DA Q → ℂ)) (v : InfinitePlace F) (m : ℕ) (c : ℂ) : Prop :=
  ∃ f : nablaSq ℂ 2 (symWt m) →ₗ[ℂ] (DA Q → ℂ), f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ (g : Hv Q v) x, RD Q (Pi.mulSingle v g, 1) (f x) =
    ((‖((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ : ℝ) : ℂ) ^ ((c - m) / 2) • f (GlobalTheory.Branching.sqRep ℂ 2 (symWt m) g x)

structure Match (π' : DiscD Q) (π : DiscG F) : Prop where
  real : ∀ v, ∃ c, (IsChr π.V v c ∧ InfD π'.V v 0 c) ∨ ∃ m, IsDS π.V v m c ∧ InfD π'.V v m c
  fin : ∀ w τ, LocG π.V w τ ↔ LocD π'.V w τ

end UpperTheory.V.Lit.JL

namespace UpperTheory.V.Lit

open JL

def GlobalJL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F),
    (∀ π' : DiscD Q, ∃ π : DiscG F, Match π' π) ∧ ∀ π : DiscG F, Compatible π.V → ∃ π' : DiscD Q, Match π' π

end UpperTheory.V.Lit
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Lit.JL

variable {F : Type} [Field F] [NumberField F]

def LocF (τ : SmIrr (GL (Fin 2) (Af F))) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] τ.V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = τ.ρ (locGL F 2 w g) (f x)

variable [IsTotallyReal F]

omit [IsTotallyReal F] in

def IsTw (s : ℂ) (τ τ' : SmIrr (GL (Fin 2) (Af F))) : Prop :=
  ∃ e : τ.V ≃ₗ[ℂ] τ'.V, ∀ g x, τ'.ρ g (e x) = ((chiDet 2 (Model.absC F s) (finGL F 2 g) : ℂˣ) : ℂ) • e (τ.ρ g x)

end UpperTheory.V.Lit.JL
end
end
