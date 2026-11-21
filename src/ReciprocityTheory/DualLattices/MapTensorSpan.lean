import ReciprocityTheory.DualLattices.TensorSpan

noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem map_tensorSpan {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by
  rw [tensorSpan, tensorSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨_, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hg, _, Submodule.mem_map_of_mem hh, by
      funext p; simp [LinearMap.funLeft_apply]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, h, hh, rfl⟩, by funext p; simp [LinearMap.funLeft_apply]⟩

def slice2 {X : Type} (E : (X → C) →ₗ[C] (X → C)) : (X × X → C) →ₗ[C] (X × X → C) where
  toFun F p := E (fun a => E (fun b => F (a, b)) p.2) p.1
  map_add' F G := by
    funext p
    have h2 : (fun a => E (fun b => (F + G) (a, b)) p.2) =
        (fun a => E (fun b => F (a, b)) p.2) + (fun a => E (fun b => G (a, b)) p.2) := by
      funext a
      rw [show (fun b => (F + G) (a, b)) = (fun b => F (a, b)) + (fun b => G (a, b)) from rfl,
        map_add]
      rfl
    show E (fun a => E (fun b => (F + G) (a, b)) p.2) p.1 =
      E (fun a => E (fun b => F (a, b)) p.2) p.1 + E (fun a => E (fun b => G (a, b)) p.2) p.1
    rw [h2, map_add]
    rfl
  map_smul' c F := by
    funext p
    have h2 : (fun a => E (fun b => (c • F) (a, b)) p.2) =
        c • (fun a => E (fun b => F (a, b)) p.2) := by
      funext a
      rw [show (fun b => (c • F) (a, b)) = c • (fun b => F (a, b)) from rfl, map_smul]
      rfl
    show E (fun a => E (fun b => (c • F) (a, b)) p.2) p.1 =
      c • E (fun a => E (fun b => F (a, b)) p.2) p.1
    rw [h2, map_smul]
    rfl




end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
