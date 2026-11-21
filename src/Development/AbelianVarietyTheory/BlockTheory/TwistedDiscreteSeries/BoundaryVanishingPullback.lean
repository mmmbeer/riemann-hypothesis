import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.IndefiniteRowSideFullHecke.RankStratification

def pullRep {Γ X : Type} [Group Γ] [TopologicalSpace X] (τ : Γ → X → X)
    (hc : ∀ γ, Continuous (τ γ)) (h1 : ∀ x, τ 1 x = x) (hm : ∀ γ δ x, τ (γ * δ) x = τ δ (τ γ x)) :
    Representation ℂ Γ (SB X) where
  toFun γ :=
    { toFun := fun Φ => ⟨fun x => Φ.1 (τ γ x), Φ.2.1.comp_continuous (hc γ),
        Φ.2.2.comp_homeomorph
          { toFun := τ γ, invFun := τ γ⁻¹
            left_inv := fun x => by rw [← hm, mul_inv_cancel, h1]
            right_inv := fun x => by rw [← hm, inv_mul_cancel, h1]
            continuous_toFun := hc γ, continuous_invFun := hc γ⁻¹ }⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
    show Φ.1 (τ 1 x) = Φ.1 x
    rw [h1]
  map_mul' γ δ := by
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
    show Φ.1 (τ (γ * δ) x) = Φ.1 (τ δ (τ γ x))
    rw [hm]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Model

variable {a b : ℕ}

def move (γ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    Matrix (Fin b) (Fin a) k :=
  (γ.2⁻¹ : GL (Fin b) k).val * x * γ.1.val

theorem continuous_move (γ : GL (Fin a) k × GL (Fin b) k) : Continuous (move γ) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem move_one (x : Matrix (Fin b) (Fin a) k) : move 1 x = x := by simp [move]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem move_mul (γ δ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    move (γ * δ) x = move δ (move γ x) := by
  simp [move, Matrix.mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem rank_move (γ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    (move γ x).rank = x.rank := by
  unfold move
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units γ.1),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units γ.2⁻¹)]

variable (k) in

abbrev Stratum (a b r : ℕ) : Type := {x : Matrix (Fin b) (Fin a) k // x.rank = r}

end Model

def AvoidsExponents {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + (j : ℂ))))

example (a b : ℕ) : ∃ φ : SB (Stratum k a b 0), φ ≠ 0 := by
  have hs : Subsingleton (Stratum k a b 0) := ⟨fun x y => Subtype.ext (by
    have key : ∀ z : Stratum k a b 0, z.1 = 0 := fun z => by
      have h0 : LinearMap.range z.1.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 z.2
      apply Matrix.toLin'.injective
      rw [map_zero]
      exact LinearMap.range_eq_bot.1 h0
    rw [key x, key y])⟩
  refine ⟨⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩, fun h => ?_⟩
  simpa using congrFun (congrArg Subtype.val h) ⟨0, Matrix.rank_zero⟩

example (μ : kˣ →* ℂˣ) : ¬ AvoidsExponents 1 μ (detRep (Fin 1) (μ * absPow k (-1))) := by
  intro h
  have := inSupport_detRep (N := 1) (μ * absPow k (-1)) 0
  apply h 0
  simpa using this

end GlobalTheory.IndefiniteRowSideFullHecke.RankStratification
