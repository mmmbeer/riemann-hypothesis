import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodFormsSpanInduced

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {K LL : Type} [Field K] [Field LL] [Algebra K LL] {C : Type} [AddCommGroup C] [Module K C]
  {G : Type} [Group G]

def chiL (LL : Type) [Field LL] [Algebra K LL] (chi : G →* Kˣ) : G →* LLˣ :=
  (Units.map (algebraMap K LL).toMonoidHom).comp chi

end Alg

section Alg2

variable {K LL : Type} [Field K] [Field LL] [NumberField LL] [Algebra K LL] {C : Type} [AddCommGroup C] [Module K C]
  {G : Type} [Group G]

def algType (ρ : G →* (C →ₗ[K] C)) (chi : G →* Kˣ) (H : Subgroup G) (lam : H →* LLˣ) : Submodule LL (LL ⊗[K] C) :=
  ⨅ p : H, LinearMap.eqLocus (rhoOf LL ρ p) (((chiL LL chi p * lam p : LLˣ) : LL) • LinearMap.id)

def algProj [Fintype G] (ρ : G →* (C →ₗ[K] C)) (chi : G →* Kˣ) (e : MonoidAlgebra LL G) :
    LL ⊗[K] C →ₗ[LL] LL ⊗[K] C :=
  ∑ g, (e.coeff g * (((chiL LL chi g)⁻¹ : LLˣ) : LL)) • rhoOf LL ρ g

def algGood [Fintype G] (ρ : G →* (C →ₗ[K] C)) (chi : G →* Kˣ) (H : Subgroup G) (lam : H →* LLˣ)
    (e : MonoidAlgebra LL G) : Submodule LL (LL ⊗[K] C) :=
  algType ρ chi H lam ⊓ LinearMap.range (algProj ρ chi e)

end Alg2

section Cx

variable {D : D7}

def levelAt {LL : Type} [Field LL] {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} (σ : LL →+* ℂ)
    (P : Formalism.L2.DIV.LevelP Pg r LL) : Formalism.L2.DIV.LevelP Pg r ℂ :=
  ⟨P.H, (Units.map σ.toMonoidHom).comp P.chi⟩

def datW (V : HSp D) {r : ℕ} (hr : V.rank = r) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) :
    Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  Lev.datY V.rank r 1 0 hr.ge Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.A

def frameOn (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (Lev.EAf D)) : GL (Fin V.rank) (Lev.EAf D) :=
  Units.map (Matrix.reindexRingEquiv (Lev.EAf D) (finCongr hr.symm)).toMonoidHom β

def IsLift (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (Lev.EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (g : Formalism.L2.DIV.G0 Pg r) (κ : GA D V) : Prop :=
  Lev.IsLevelLift V (frameOn V hr β) (datW V hr Pg (Formalism.L2.DIV.LevelP.triv Pg r ℂ)) g κ

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem actG0_add (g : Formalism.L2.DIV.G0 L.Pg L.r) (F F' : GA D V → ℂ) (h : GA D V) :
    Lev.actG0 V β L g (F + F') h = Lev.actG0 V β L g F h + Lev.actG0 V β L g F' h := by
  unfold Lev.actG0; split_ifs <;> simp [mul_add]

theorem actG0_smul (g : Formalism.L2.DIV.G0 L.Pg L.r) (a : ℂ) (F : GA D V → ℂ) (h : GA D V) :
    Lev.actG0 V β L g (a • F) h = a * Lev.actG0 V β L g F h := by
  unfold Lev.actG0
  split_ifs
  · exact mul_left_comm _ _ _
  · exact (mul_zero a).symm

variable (V β L)

def typeGood (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | Lev.HasType V β L F ∧ Lev.eAct V β L e F = F}
  zero_mem' := ⟨fun κ _ h => by simp, by
    funext h
    have := fun g => actG0_smul (β := β) (L := L) g 0 0 h
    simp only [zero_smul, zero_mul] at this
    simp [Lev.eAct, Finsupp.sum, this]⟩
  add_mem' := by
    rintro F F' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun κ hκ h => by simp [h1 κ hκ h, h1' κ hκ h, mul_add], ?_⟩
    funext h
    have a := congrFun h2 h
    have b := congrFun h2' h
    simp only [Lev.eAct, Finsupp.sum] at a b ⊢
    simp only [actG0_add, mul_add, Finset.sum_add_distrib, Pi.add_apply, a, b]
  smul_mem' := by
    rintro a F ⟨h1, h2⟩
    refine ⟨fun κ hκ h => by simp [h1 κ hκ h, mul_left_comm], ?_⟩
    funext h
    have b := congrFun h2 h
    simp only [Lev.eAct, Finsupp.sum] at b ⊢
    simp only [actG0_smul, Pi.smul_apply, smul_eq_mul]
    rw [← b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

end Cx

section At

variable {D : D7} {K LL : Type} [Field K] [Field LL] [NumberField LL] [Algebra K LL]
  {C : Type} [AddCommGroup C] [Module K C] {r : ℕ} {Comp : Type}
  (σ : LL →+* ℂ) (V : HSp D) (hr : V.rank = r) {X : Comp → Data D.host.E r} (la : ∀ c, Wt (X c).Ψ r)
  (rd : C →ₛₗ[σ.comp (algebraMap K LL)] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ)
  (β : GL (Fin r) (Lev.EAf D)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}

variable [Fintype (Formalism.L2.DIV.G0 Pg r)] (ρ : Formalism.L2.DIV.G0 Pg r →* (C →ₗ[K] C)) (chi : Formalism.L2.DIV.G0 Pg r →* Kˣ)

end At

section Closed

variable {D : D7} (T : CoreJ D) (j : ℕ) (hr : ∀ σ, GoodEmb T.Q.c σ → (T.V j σ).rank = D.R.r)
  (β : GL (Fin D.R.r) (Lev.EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))

end Closed

example {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) (r : ℕ) : Finite (Formalism.L2.DIV.G0 Pg r) := by
  haveI : ∀ PP : Formalism.L2.DIV.Pl E, Finite (Formalism.L2.DIV.kP PP) := fun PP =>
    Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  infer_instance

example {D : D7} {LL : Type} [Field LL] (V : HSp D) {r : ℕ} (hr : V.rank = r) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (σ : LL →+* ℂ) (P : Formalism.L2.DIV.LevelP Pg r LL) : (datW V hr Pg (levelAt σ P)).P = levelAt σ P.conj := by
  show (levelAt σ P).conj = _
  unfold levelAt Formalism.L2.DIV.LevelP.conj
  congr 1

example {K LL : Type} [Field K] [Field LL] [NumberField LL] [Algebra K LL] {C : Type} [AddCommGroup C] [Module K C]
    {G : Type} [Group G] [Fintype G] (ρ : G →* (C →ₗ[K] C)) (chi : G →* Kˣ) :
    algGood (LL := LL) ρ chi ⊥ 1 1 = ⊤ := by
  classical
  have h1 : algProj (LL := LL) ρ chi 1 = LinearMap.id := by
    unfold algProj
    rw [Finset.sum_eq_single 1]
    · simp [MonoidAlgebra.one_def, Module.End.one_eq_id]
    · intro g _ hg
      simp [MonoidAlgebra.one_def, Finsupp.single_apply, hg.symm]
    · simp
  have h2 : algType (LL := LL) ρ chi ⊥ 1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    simp only [algType, Submodule.mem_iInf, LinearMap.mem_eqLocus]
    rintro ⟨p, hp⟩
    obtain rfl := Subgroup.mem_bot.1 hp
    simp
  simp [algGood, h1, h2]

end GlobalTheory.IndefiniteRowSideFullHecke.GoodFormsSpanInduced
