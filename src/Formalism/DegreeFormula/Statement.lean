import Mathlib
import Formalism.MoebiusJetDuality.StatementU

noncomputable section

open Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.DegreeFormula

open Formalism.MJ Formalism.UG

section One

variable {p q : ℕ}

def kapP (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁).map (starRingEnd ℂ) +
    ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂).map (starRingEnd ℂ) * zᵀ

def kapQ (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂

def hQ (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ := 1 - zᴴ * z

def hP (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ := 1 - z * zᴴ

def toGL {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : GL (Fin m) ℂ :=
  open Classical in
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1

end One

section Two

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def DomI (ι : Type) (p q : ℕ) : Set (ι → Matrix (Fin p) (Fin q) ℂ) := {z | ∀ i, z i ∈ hcDom p q}

def UpqI (ι : Type) (p q : ℕ) : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  Subgroup.pi Set.univ (fun _ => Upq p q)

def moebI (g : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ) :
    ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => moeb (g i : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z i)

def jI (g : ι → GL (Fin p ⊕ Fin q) ℂ) (z : ι → Matrix (Fin p) (Fin q) ℂ) :
    ι → GL (Fin p) ℂ × GL (Fin q) ℂ :=
  fun i => (toGL (kapP (g i) (z i)), toGL (kapQ (g i) (z i)))

def unflat (v : ι × Fin p × Fin q → ℂ) : ι → Matrix (Fin p) (Fin q) ℂ :=
  fun i => Matrix.of (fun a b => v (i, a, b))

def flat (z : ι → Matrix (Fin p) (Fin q) ℂ) : ι × Fin p × Fin q → ℂ := fun x => z x.1 x.2.1 x.2.2

def DomFlat (ι : Type) (p q : ℕ) : Set (ι × Fin p × Fin q → ℂ) := {v | unflat v ∈ DomI ι p q}

def IsHoloOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → V) : Prop :=
  DifferentiableOn ℂ (fun v => f (unflat v)) (DomFlat ι p q)

def AutForm (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) :
    Submodule ℂ ((ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) where
  carrier := {f | IsHoloOn f ∧ (∀ z, z ∉ DomI ι p q → f z = 0) ∧
    ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, f (moebI γ z) = (ρ (jI γ z) : Matrix (Fin r) (Fin r) ℂ).mulVec (f z)}
  zero_mem' := ⟨by simpa [IsHoloOn] using (differentiableOn_const (c := (0 : Fin r → ℂ))),
    fun _ _ => rfl, fun γ _ z _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨hf1.add hg1, fun z hz => by simp [hf2 z hz, hg2 z hz], fun γ hγ z hz => ?_⟩
    simp [hf3 γ hγ z hz, hg3 γ hγ z hz, Matrix.mulVec_add]
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨hf1.const_smul c, fun z hz => by simp [hf2 z hz], fun γ hγ z hz => ?_⟩
    simp [hf3 γ hγ z hz, Matrix.mulVec_smul]

def slash (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (g : ι → GL (Fin p ⊕ Fin q) ℂ)
    (f : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ)) : (ι → Matrix (Fin p) (Fin q) ℂ) → (Fin r → ℂ) :=
  open Classical in
  fun z => if z ∈ DomI ι p q then
    (((ρ (jI g z))⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec (f (moebI g z)) else 0

def detChar (ι : Type) [Fintype ι] (p q : ℕ) (k₁ k₂ : ι → ℤ) :
    (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin 1) ℂ :=
  (Units.map (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ)).toMonoidHom).comp
    { toFun := fun g => ∏ i, (Matrix.GeneralLinearGroup.det (g i).1) ^ (k₁ i) *
        (Matrix.GeneralLinearGroup.det (g i).2) ^ (k₂ i)
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        simp only [Pi.mul_apply, Prod.fst_mul, Prod.snd_mul, map_mul, mul_zpow]
        exact mul_mul_mul_comm _ _ _ _ }

end Two

section Three

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def liftPt (ι : Type) [Fintype ι] (p q : ℕ) (z : ι → Matrix (Fin p) (Fin q) ℂ) : ι → GL (Fin p ⊕ Fin q) ℂ :=
  open Classical in
  if h : ∃ g ∈ UpqI ι p q, moebI g 0 = z then h.choose else 1

end Three

section Four

variable {ι : Type} [Fintype ι] {p q r : ℕ}

def muD (ι : Type) [Fintype ι] (p q : ℕ) : Measure (ι × Fin p × Fin q → ℂ) :=
  (volume.restrict (DomFlat ι p q)).withDensity
    (fun v => ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))))

def IsFD (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (F : Set (ι × Fin p × Fin q → ℂ)) : Prop :=
  MeasurableSet F ∧ F ⊆ DomFlat ι p q ∧
    (∀ z ∈ DomI ι p q, ∃ γ ∈ Γ, flat (moebI γ z) ∈ F) ∧
    muD ι p q {v | v ∈ F ∧ ∃ γ ∈ Γ, flat (moebI γ (unflat v)) ∈ F ∧ moebI γ (unflat v) ≠ unflat v} = 0

end Four

section Five

variable {ι : Type} [Fintype ι] {p q r : ℕ} {G Gf : Type} [Group G] [Group Gf]

def AutFormAd (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (U K : Subgroup Gf)
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) :
    Submodule ℂ ((ι → Matrix (Fin p) (Fin q) ℂ) × Gf → (Fin r → ℂ)) where
  carrier := {F | (∀ g, IsHoloOn (fun z => F (z, g))) ∧ (∀ z g, z ∉ DomI ι p q → F (z, g) = 0) ∧
    (∀ z g, g ∉ U → F (z, g) = 0) ∧
    ∀ γ : G, ∀ z ∈ DomI ι p q, ∀ g : Gf, ∀ κ ∈ K,
      F (moebI (φ γ) z, ψ γ * g * κ) = (ρ (jI (φ γ) z) : Matrix (Fin r) (Fin r) ℂ).mulVec (F (z, g))}
  zero_mem' := ⟨fun g => by simpa [IsHoloOn] using (differentiableOn_const (c := (0 : Fin r → ℂ))),
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun γ z _ g κ _ => by simp⟩
  add_mem' := by
    rintro F F' ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨fun g => (h1 g).add (h1' g), fun z g hz => by simp [h2 z g hz, h2' z g hz],
      fun z g hg => by simp [h3 z g hg, h3' z g hg], fun γ z hz g κ hκ => ?_⟩
    simp [h4 γ z hz g κ hκ, h4' γ z hz g κ hκ, Matrix.mulVec_add]
  smul_mem' := by
    rintro c F ⟨h1, h2, h3, h4⟩
    refine ⟨fun g => (h1 g).const_smul c, fun z g hz => by simp [h2 z g hz],
      fun z g hg => by simp [h3 z g hg], fun γ z hz g κ hκ => ?_⟩
    simp [h4 γ z hz g κ hκ, Matrix.mulVec_smul]

def compGamma (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (K : Subgroup Gf) (g : Gf) :
    Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  ((K.map (MulAut.conj g).toMonoidHom).comap ψ).map φ

def AdComp : Prop :=
  ∀ (ι : Type) [Fintype ι] (p q r : ℕ) (G Gf : Type) [Group G] [Group Gf]
    (φ : G →* (ι → GL (Fin p ⊕ Fin q) ℂ)) (ψ : G →* Gf) (U K : Subgroup Gf)
    (ρ : (ι → GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ) (F : (ι → Matrix (Fin p) (Fin q) ℂ) × Gf → (Fin r → ℂ)),
    F ∈ AutFormAd φ ψ U K ρ → ∀ g : Gf, (fun z => F (z, g)) ∈ AutForm (compGamma φ ψ K g) ρ

end Five

section CompanionTheory

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} {p q : ℕ}

def embI (τ : ι → E →+* ℂ) (e : ι → n ≃ Fin p ⊕ Fin q) (P : ι → GL (Fin p ⊕ Fin q) ℂ) :
    GL n E →* (ι → GL (Fin p ⊕ Fin q) ℂ) :=
  MonoidHom.pi (fun i => (MulAut.conj (P i)⁻¹).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.map (τ i)).comp
      (Units.map (Matrix.reindexAlgEquiv E E (e i)).toMonoidHom)))

end CompanionTheory

section LateralTheory

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def latDeg (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] : ℝ :=
  -Real.log (ZLattice.covolume L)

end LateralTheory

end Formalism.DegreeFormula
