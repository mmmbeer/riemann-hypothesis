import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullCompOfEq

noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}


end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

def ω₂ : LinearMap.BilinForm k (k × k) :=
  LinearMap.mk₂ k (fun x y => x.1 * y.2 - x.2 * y.1) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

def L₁ : Submodule k (k × k) := LinearMap.ker (LinearMap.snd k k k)

theorem mem_L₁ (x : k × k) : x ∈ L₁ k ↔ x.2 = 0 := Iff.rfl



def diag : (k × k) →+* Module.End k (k × k) := (Algebra.lmul k (k × k)).toRingHom



def ω₄ : LinearMap.BilinForm k (Fin 4 → k) :=
  LinearMap.mk₂ k (fun x y => x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)

def act₄ : (k × k) →+* Module.End k (Fin 4 → k) :=
  (Algebra.lmul k (Fin 4 → k)).toRingHom.comp
    (RingHom.pi ![RingHom.fst k k, RingHom.fst k k, RingHom.snd k k, RingHom.snd k k])

def F₄ : Submodule k (Fin 4 → k) := LinearMap.ker (LinearMap.proj 1) ⊓ LinearMap.ker (LinearMap.proj 2)

theorem mem_F₄ (x : Fin 4 → k) : x ∈ F₄ k ↔ x 1 = 0 ∧ x 2 = 0 := Iff.rfl

theorem act₄_apply (a : k × k) (x : Fin 4 → k) : act₄ k a x = ![a.1 * x 0, a.1 * x 1, a.2 * x 2, a.2 * x 3] := by
  funext i; fin_cases i <;> rfl


end Examples

end GlobalTheory.UPel.Sm.Model
