import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LubinTateDeformation

section
noncomputable section

open CategoryTheory Module Matrix

namespace GlobalTheory.VDiv

section Modules

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (S : Type) [CommRing S] [Algebra O S]

structure VarpiDivModule : Type 1 where

  G : PDivGroup p S

  ι : PDivGroup.Action O G

  isNilpotent_p : IsNilpotent (p : S)

  lie_smul : ∀ (a : O) (x : G.Lie), ι.onLie a x = algebraMap O S a • x

namespace VarpiDivModule

variable {p O S}


theorem ι_algebraMap [Algebra ℤ_[p] O] (H : VarpiDivModule p O S) (a : ℤ_[p]) :
    H.ι (algebraMap ℤ_[p] O a) = algebraMap ℤ_[p] (End H.G) a :=
  H.ι.map_algebraMap a

@[ext] structure Hom (H H' : VarpiDivModule p O S) : Type where

  f : H.G ⟶ H'.G

  comm : ∀ a : O, (H.ι a : H.G ⟶ H.G) ≫ f = f ≫ (H'.ι a : H'.G ⟶ H'.G)

instance : Category (VarpiDivModule p O S) where
  Hom := Hom
  id H := ⟨𝟙 _, fun a => by rw [Category.comp_id, Category.id_comp]⟩
  comp f g := ⟨f.f ≫ g.f, fun a => by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp f.f)
  comp_id f := Hom.ext (Category.comp_id f.f)
  assoc f g h := Hom.ext (Category.assoc f.f g.f h.f)

@[simp] theorem id_f (H : VarpiDivModule p O S) : Hom.f (𝟙 H) = 𝟙 H.G := rfl

@[simp] theorem comp_f {H H' H'' : VarpiDivModule p O S} (f : H ⟶ H') (g : H' ⟶ H'') :
    Hom.f (f ≫ g) = f.f ≫ g.f := rfl

@[ext] theorem hom_ext {H H' : VarpiDivModule p O S} {f g : H ⟶ H'} (h : f.f = g.f) : f = g :=
  Hom.ext h

def HasOHeight [Algebra ℤ_[p] O] (H : VarpiDivModule p O S) (n : ℕ) : Prop :=
  Module.Free ℤ_[p] O ∧ Module.Finite ℤ_[p] O ∧ H.G.height = n * Module.finrank ℤ_[p] O

theorem padicAction_onLie [Algebra ℤ_[p] S] (G : PDivGroup p S) (a : ℤ_[p]) (x : G.Lie) :
    (PDivGroup.padicAction G).onLie a x = algebraMap ℤ_[p] S a • x := by
  rw [PDivGroup.Action.onLie_apply, PDivGroup.padicAction, Algebra.algebraMap_eq_smul_one,
    PDivGroup.lieMap_smul (algebraMap ℤ_[p] S)]
  simp

variable (p) in

def ofPDiv [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    VarpiDivModule p ℤ_[p] S :=
  ⟨G, G.padicAction, h, padicAction_onLie G⟩

@[simp] theorem ofPDiv_G [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    (ofPDiv p G h).G = G := rfl

theorem ofPDiv_hasOHeight [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    (ofPDiv p G h).HasOHeight G.height :=
  ⟨inferInstance, inferInstance, by rw [Module.finrank_self, mul_one]; rfl⟩

variable (p) in

abbrev ResRing : Type := ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}

theorem natCast_resRing : ((p : ℕ) : ResRing p) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}))]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

variable (p) in

def muMod : VarpiDivModule p ℤ_[p] (ResRing p) :=
  ofPDiv p (PDivGroup.mu p (ResRing p)) ⟨1, by rw [pow_one, natCast_resRing]⟩

theorem muMod_hasOHeight : (muMod p).HasOHeight 1 := ofPDiv_hasOHeight _ _

example : ¬ (muMod p).HasOHeight 0 := fun h => by
  exact one_ne_zero (h.2.2.trans (zero_mul _))

end VarpiDivModule

end Modules

section Bset

variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]

def unifDiag (ϖ : R) : Matrix (Fin n) (Fin n) R := diagonal (Function.update 1 0 ϖ)

def coUnifDiag (ϖ : R) : Matrix (Fin n) (Fin n) R := diagonal (Function.update (fun _ => ϖ) 0 1)

theorem unifDiag_apply (ϖ : R) (i j : Fin n) :
    unifDiag ϖ i j = if i = j then (if i = 0 then ϖ else 1) else 0 := by
  by_cases h : i = j
  · subst h; by_cases h0 : i = 0 <;> simp [unifDiag, h0]
  · simp [unifDiag, h]

theorem unifDiag_mul_coUnifDiag (ϖ : R) :
    (unifDiag ϖ : Matrix (Fin n) (Fin n) R) * coUnifDiag ϖ = ϖ • 1 := by
  rw [unifDiag, coUnifDiag, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i = 0 <;> simp [diagonal, h]
  · simp [diagonal, hij]

theorem coUnifDiag_mul_unifDiag (ϖ : R) :
    (coUnifDiag ϖ : Matrix (Fin n) (Fin n) R) * unifDiag ϖ = ϖ • 1 := by
  rw [unifDiag, coUnifDiag, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i = 0 <;> simp [diagonal, h]
  · simp [diagonal, hij]

variable (n) in

def BsetInt (ϖ : R) : Set (Matrix (Fin n) (Fin n) R) :=
  {β | ∃ k₁ k₂ : GL (Fin n) R, β = k₁.val * unifDiag ϖ * k₂.val}

variable (n) in

def Bset (K : Type) [Field K] [Algebra R K] (ϖ : R) : Set (GL (Fin n) K) :=
  {g | ∃ β ∈ BsetInt n ϖ, g.val = β.map (algebraMap R K)}

theorem unifDiag_mem (ϖ : R) : unifDiag ϖ ∈ BsetInt n ϖ := ⟨1, 1, by simp⟩

theorem exists_mul_eq_smul {ϖ : R} {β : Matrix (Fin n) (Fin n) R} (hβ : β ∈ BsetInt n ϖ) :
    ∃ γ : Matrix (Fin n) (Fin n) R, β * γ = ϖ • 1 ∧ γ * β = ϖ • 1 := by
  obtain ⟨k₁, k₂, rfl⟩ := hβ
  refine ⟨(k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val, ?_, ?_⟩
  · calc k₁.val * unifDiag ϖ * k₂.val * ((k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val)
        = k₁.val * (unifDiag ϖ * ((k₂.val * (k₂⁻¹).val) * coUnifDiag ϖ)) * (k₁⁻¹).val := by
          simp only [Matrix.mul_assoc]
      _ = ϖ • 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
            unifDiag_mul_coUnifDiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · calc (k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val * (k₁.val * unifDiag ϖ * k₂.val)
        = (k₂⁻¹).val * (coUnifDiag ϖ * (((k₁⁻¹).val * k₁.val) * unifDiag ϖ)) * k₂.val := by
          simp only [Matrix.mul_assoc]
      _ = ϖ • 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
            coUnifDiag_mul_unifDiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            ← Units.val_mul, inv_mul_cancel, Units.val_one]

def sigmaGL (σ : R ≃+* R) : GL (Fin n) R →* GL (Fin n) R :=
  GeneralLinearGroup.map (σ : R →+* R)

@[simp] theorem sigmaGL_val (σ : R ≃+* R) (g : GL (Fin n) R) :
    (sigmaGL σ g).val = (g.val).map σ := rfl

def sigmaConj (σ : R ≃+* R) (g : GL (Fin n) R) (β : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  g.val * β * (sigmaGL σ g⁻¹).val

@[simp] theorem sigmaConj_one (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) :
    sigmaConj σ 1 β = β := by
  simp only [sigmaConj, inv_one, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem sigmaConj_mul (σ : R ≃+* R) (g h : GL (Fin n) R) (β : Matrix (Fin n) (Fin n) R) :
    sigmaConj σ (g * h) β = sigmaConj σ g (sigmaConj σ h β) := by
  simp only [sigmaConj, _root_.mul_inv_rev, map_mul, Units.val_mul, Matrix.mul_assoc]


variable (n) in

def sigmaSetoid (σ : R ≃+* R) (ϖ : R) : Setoid (BsetInt n ϖ) where
  r β β' := ∃ g : GL (Fin n) R, β'.1 = sigmaConj σ g β.1
  iseqv := ⟨fun β => ⟨1, (sigmaConj_one σ β.1).symm⟩,
    fun {β β'} ⟨g, h⟩ => ⟨g⁻¹, by rw [h, ← sigmaConj_mul, inv_mul_cancel, sigmaConj_one]⟩,
    fun {β β' β''} ⟨g, h⟩ ⟨g', h'⟩ => ⟨g' * g, by rw [h', h, sigmaConj_mul]⟩⟩

variable (n) in

def BsetClasses (σ : R ≃+* R) (ϖ : R) : Type := Quotient (sigmaSetoid n σ ϖ)

end Bset

section Dieudonne

variable (R : Type) [CommRing R]

structure RelDieudonne (σ : R ≃+* R) (ϖ : R) : Type 1 where

  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [free : Module.Free R M]
  [finite : Module.Finite R M]

  F : M →ₛₗ[(σ : R →+* R)] M

  V : M →ₛₗ[(σ.symm : R →+* R)] M

  F_V : ∀ x, F (V x) = ϖ • x

  V_F : ∀ x, V (F x) = ϖ • x

attribute [instance] RelDieudonne.addCommGroup RelDieudonne.module RelDieudonne.free
  RelDieudonne.finite

variable {R}

namespace RelDieudonne

variable {σ : R ≃+* R} {ϖ : R}

structure Iso (D D' : RelDieudonne R σ ϖ) : Type where

  e : D.M ≃ₗ[R] D'.M

  F_comm : ∀ x, e (D.F x) = D'.F (e x)

  V_comm : ∀ x, e (D.V x) = D'.V (e x)

def Iso.refl (D : RelDieudonne R σ ϖ) : Iso D D :=
  ⟨LinearEquiv.refl R D.M, fun _ => rfl, fun _ => rfl⟩

def Iso.symm {D D' : RelDieudonne R σ ϖ} (i : Iso D D') : Iso D' D :=
  ⟨i.e.symm, fun x => i.e.injective (by rw [i.F_comm, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]), fun x => i.e.injective (by rw [i.V_comm,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])⟩

def Iso.trans {D D' D'' : RelDieudonne R σ ϖ} (i : Iso D D') (j : Iso D' D'') : Iso D D'' :=
  ⟨i.e.trans j.e, fun x => by simp [i.F_comm, j.F_comm], fun x => by simp [i.V_comm, j.V_comm]⟩

end RelDieudonne

variable {n : ℕ}

def dieuF (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) :
    (Fin n → R) →ₛₗ[(σ : R →+* R)] (Fin n → R) where
  toFun x := β *ᵥ fun i => σ (x i)
  map_add' x y := by
    rw [← mulVec_add]
    congr 1
    funext i
    simp
  map_smul' c x := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp

def dieuV (σ : R ≃+* R) (γ : Matrix (Fin n) (Fin n) R) :
    (Fin n → R) →ₛₗ[(σ.symm : R →+* R)] (Fin n → R) where
  toFun y i := σ.symm ((γ *ᵥ y) i)
  map_add' x y := by
    funext i
    simp [mulVec_add]
  map_smul' c x := by
    funext i
    simp [mulVec_smul]

@[simp] theorem dieuF_apply (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    dieuF σ β x = β *ᵥ fun i => σ (x i) := rfl

@[simp] theorem dieuV_apply (σ : R ≃+* R) (γ : Matrix (Fin n) (Fin n) R) (y : Fin n → R)
    (i : Fin n) : dieuV σ γ y i = σ.symm ((γ *ᵥ y) i) := rfl

variable [NeZero n]

def coMat {ϖ : R} (β : BsetInt n ϖ) : Matrix (Fin n) (Fin n) R :=
  (exists_mul_eq_smul β.2).choose

theorem mul_coMat {ϖ : R} (β : BsetInt n ϖ) : β.1 * coMat β = ϖ • 1 :=
  (exists_mul_eq_smul β.2).choose_spec.1

theorem coMat_mul {ϖ : R} (β : BsetInt n ϖ) : coMat β * β.1 = ϖ • 1 :=
  (exists_mul_eq_smul β.2).choose_spec.2

def dieu (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ) : RelDieudonne R σ ϖ where
  M := Fin n → R
  F := dieuF σ β.1
  V := dieuV σ (coMat β)
  F_V y := by
    have h1 : (fun i => σ (dieuV σ (coMat β) y i)) = coMat β *ᵥ y := by
      funext i; rw [dieuV_apply, RingEquiv.apply_symm_apply]
    rw [dieuF_apply, h1, mulVec_mulVec, mul_coMat, smul_mulVec, one_mulVec]
  V_F x := by
    funext i
    rw [dieuV_apply, dieuF_apply, mulVec_mulVec, coMat_mul, smul_mulVec, one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    rw [show σ.symm ϖ = ϖ from σ.symm_apply_eq.2 hϖ.symm]

@[simp] theorem dieu_F (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ)
    (x : Fin n → R) : (dieu σ hϖ β).F x = β.1 *ᵥ fun i => σ (x i) := rfl

theorem finrank_dieu [Nontrivial R] (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ) :
    Module.finrank R (dieu σ hϖ β).M = n :=
  Module.finrank_fin_fun R



theorem dieu_unifDiag_not_surjective (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (hu : ¬ IsUnit ϖ) :
    ¬ Function.Surjective (dieu σ hϖ ⟨unifDiag (n := n) ϖ, unifDiag_mem ϖ⟩).F := by
  intro h
  obtain ⟨x, hx⟩ := h (Pi.single (0 : Fin n) (1 : R))
  have h0 := congrFun hx 0
  change (unifDiag ϖ *ᵥ fun i => σ (x i)) 0 = (Pi.single (0 : Fin n) (1 : R) : Fin n → R) 0 at h0
  simp only [mulVec, dotProduct, unifDiag_apply] at h0
  simp at h0
  exact hu (isUnit_iff_exists_inv.2 ⟨_, h0⟩)

end Dieudonne

section Example

variable (p : ℕ) [Fact p.Prime]

example : ¬ Function.Surjective (dieu (RingEquiv.refl ℤ_[p]) (ϖ := (p : ℤ_[p])) rfl
    ⟨unifDiag (n := 2) (p : ℤ_[p]), unifDiag_mem _⟩).F :=
  dieu_unifDiag_not_surjective _ _
    fun h => by
      have h1 := PadicInt.isUnit_iff.1 h
      rw [PadicInt.norm_p, inv_eq_one, Nat.cast_eq_one] at h1
      exact (Fact.out : p.Prime).one_lt.ne' h1

example : Module.finrank ℤ_[p] (dieu (RingEquiv.refl ℤ_[p]) (ϖ := (p : ℤ_[p])) rfl
    ⟨unifDiag (n := 3) (p : ℤ_[p]), unifDiag_mem _⟩).M = 3 := finrank_dieu _ _ _

end Example

section Conj

variable {R : Type} [CommRing R] {σ : R ≃+* R} {ϖ : R}

theorem RelDieudonne.V_comm_of_F_comm {D D' : RelDieudonne R σ ϖ} (e : D.M ≃ₗ[R] D'.M)
    (hF : ∀ x, e (D.F x) = D'.F (e x)) (hreg : ∀ y : D'.M, ϖ • y = 0 → y = 0) (x : D.M) :
    e (D.V x) = D'.V (e x) := by
  have hinj : ∀ y z : D'.M, D'.F y = D'.F z → y = z := fun y z h => by
    have h1 := congrArg D'.V h
    rw [D'.V_F, D'.V_F, ← sub_eq_zero, ← smul_sub] at h1
    exact sub_eq_zero.1 (hreg _ h1)
  apply hinj
  rw [← hF, D.F_V, D'.F_V, map_smul]

variable {n : ℕ}

def glEquiv (g : GL (Fin n) R) : (Fin n → R) ≃ₗ[R] (Fin n → R) where
  toFun x := g.val *ᵥ x
  invFun y := (g⁻¹).val *ᵥ y
  map_add' x y := mulVec_add _ _ _
  map_smul' c x := mulVec_smul _ _ _
  left_inv x := by
    change (g⁻¹).val *ᵥ (g.val *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv y := by
    change g.val *ᵥ ((g⁻¹).val *ᵥ y) = y
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

@[simp] theorem glEquiv_apply (g : GL (Fin n) R) (x : Fin n → R) : glEquiv g x = g.val *ᵥ x := rfl

theorem sigma_mulVec (σ : R ≃+* R) (g : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    (fun i => σ ((g *ᵥ x) i)) = g.map σ *ᵥ fun i => σ (x i) := by
  funext i
  exact RingHom.map_mulVec (σ : R →+* R) g x i

variable [NeZero n]

def dieuIsoOfConj (hϖ : σ ϖ = ϖ) (hreg : ϖ ∈ nonZeroDivisors R) (β β' : BsetInt n ϖ)
    (g : GL (Fin n) R) (h : β'.1 = sigmaConj σ g β.1) :
    RelDieudonne.Iso (dieu σ hϖ β) (dieu σ hϖ β') :=
  have hF : ∀ x : Fin n → R, glEquiv g ((dieu σ hϖ β).F x) = (dieu σ hϖ β').F (glEquiv g x) :=
    fun x => by
    change g.val *ᵥ (β.1 *ᵥ fun i => σ (x i)) = β'.1 *ᵥ fun i => σ ((g.val *ᵥ x) i)
    rw [sigma_mulVec, h, sigmaConj, mulVec_mulVec, mulVec_mulVec, sigmaGL_val, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one]
  ⟨glEquiv g, hF, RelDieudonne.V_comm_of_F_comm (D := dieu σ hϖ β) (D' := dieu σ hϖ β')
    (glEquiv g) hF fun y hy => funext fun i => by
      have : ϖ * y i = 0 := congrFun hy i
      exact (mem_nonZeroDivisors_iff.1 hreg |>.1) _ this⟩


end Conj

section BsetField

variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]

theorem det_unifDiag (ϖ : R) : (unifDiag ϖ : Matrix (Fin n) (Fin n) R).det = ϖ := by
  rw [unifDiag, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

theorem exists_mem_Bset (K : Type) [Field K] [Algebra R K] (ϖ : R) (h : algebraMap R K ϖ ≠ 0) :
    ∃ g ∈ Bset n K ϖ, g.val = (unifDiag ϖ).map (algebraMap R K) := by
  have hd : ((unifDiag ϖ : Matrix (Fin n) (Fin n) R).map (algebraMap R K)).det ≠ 0 := by
    have h1 : ((unifDiag ϖ : Matrix (Fin n) (Fin n) R).map (algebraMap R K)).det =
        algebraMap R K ϖ := by
      rw [show ((unifDiag ϖ : Matrix (Fin n) (Fin n) R).map (algebraMap R K)) =
        (algebraMap R K).mapMatrix (unifDiag ϖ) from rfl, ← RingHom.map_det, det_unifDiag]
    rw [h1]
    exact h
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, ⟨_, unifDiag_mem ϖ, rfl⟩, rfl⟩

example (p : ℕ) [Fact p.Prime] : ∃ g ∈ Bset 2 ℚ_[p] (p : ℤ_[p]),
    g.val = (unifDiag (p : ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) :=
  exists_mem_Bset _ _ (by simp [(Fact.out : p.Prime).ne_zero])

end BsetField

end GlobalTheory.VDiv
end
end

section
noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.VDefo

open GlobalTheory.VDiv GlobalTheory.PDiv

section LocAlg

variable (O Or : Type) [CommRing O] [CommRing Or] [IsLocalRing Or] [Algebra O Or]

structure LocAlg : Type 1 where

  A : Type
  [ring : CommRing A]
  [isLocalRing : IsLocalRing A]
  [algOr : Algebra Or A]
  [algO : Algebra O A]
  [tower : IsScalarTower O Or A]
  [isLocalHom : IsLocalHom (algebraMap Or A)]

  bij : Function.Bijective (ResidueField.map (algebraMap Or A))

attribute [instance] LocAlg.ring LocAlg.isLocalRing LocAlg.algOr LocAlg.algO LocAlg.tower
  LocAlg.isLocalHom

namespace LocAlg

variable {O Or}

def red (A : LocAlg O Or) : A.A →+* ResidueField Or := FOM.resRed Or A.A A.bij

theorem red_eq_zero (A : LocAlg O Or) {a : A.A} (ha : a ∈ maximalIdeal A.A) : A.red a = 0 := by
  simp [red, FOM.resRed, (residue_eq_zero_iff a).2 ha]

@[ext] structure Hom (A B : LocAlg O Or) : Type where

  f : A.A →ₐ[Or] B.A

  isLocal : IsLocalHom (f : A.A →+* B.A)

instance : Category (LocAlg O Or) where
  Hom := Hom
  id A := ⟨AlgHom.id Or A.A, ⟨fun _ h => h⟩⟩
  comp f g := ⟨g.f.comp f.f, ⟨fun a h => f.isLocal.map_nonunit a (g.isLocal.map_nonunit (f.f a) h)⟩⟩
  id_comp f := Hom.ext (AlgHom.comp_id _)
  comp_id f := Hom.ext (AlgHom.id_comp _)
  assoc f g h := Hom.ext (AlgHom.comp_assoc _ _ _).symm

@[simp] theorem comp_f {A B C : LocAlg O Or} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.f (f ≫ g) = g.f.comp f.f := rfl

@[simp] theorem id_f (A : LocAlg O Or) : Hom.f (𝟙 A) = AlgHom.id Or A.A := rfl

@[simp] theorem red_algebraMap (A : LocAlg O Or) (r : Or) : A.red (algebraMap Or A.A r) = residue Or r := by
  simp only [red, FOM.resRed, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.symm_apply_eq]
  simp [ResidueField.map_residue]

theorem red_comp {A B : LocAlg O Or} (f : A ⟶ B) (a : A.A) : B.red (f.f a) = A.red a := by
  obtain ⟨r, hr⟩ := (A.bij.2 (residue A.A a))
  obtain ⟨r, rfl⟩ := residue_surjective r
  have h1 : a - algebraMap Or A.A r ∈ maximalIdeal A.A := by
    rw [← residue_eq_zero_iff, map_sub, ← hr, ResidueField.map_residue, sub_self]
  have h2 : f.f a - algebraMap Or B.A r ∈ maximalIdeal B.A := by
    rw [← AlgHom.commutes f.f r, ← map_sub]
    haveI := f.isLocal
    exact map_nonunit (f.f : A.A →+* B.A) _ h1
  have e : ∀ (C : LocAlg O Or) (x : C.A), x - algebraMap Or C.A r ∈ maximalIdeal C.A →
      C.red x = residue Or r := fun C x hx => by
    have := C.red_eq_zero hx
    rw [map_sub, sub_eq_zero] at this
    rw [this]
    simp only [red, FOM.resRed, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq]
    simp [ResidueField.map_residue]
  rw [e B _ h2, e A _ h1]

def residueField : LocAlg O Or where
  A := ResidueField Or
  isLocalHom := ⟨fun a h => by
    by_contra ha
    exact h.ne_zero ((residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 ha))⟩
  bij := ⟨RingHom.injective _, fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := residue_surjective x
    refine ⟨residue Or r, ?_⟩
    rw [ResidueField.map_residue]
    rfl⟩

abbrev Trunc (R : LocAlg O Or) (k : ℕ) : Type := R.A ⧸ maximalIdeal R.A ^ (k + 1)

def truncRed (R : LocAlg O Or) (k : ℕ) : R.Trunc k →+* ResidueField Or :=
  Ideal.Quotient.lift _ R.red fun _ ha => R.red_eq_zero (Ideal.pow_le_self (Nat.succ_ne_zero k) ha)

def truncMap (R : LocAlg O Or) (k : ℕ) : R.Trunc (k + 1) →+* R.Trunc k :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))

def truncLift {R A : LocAlg O Or} (g : R ⟶ A) (k : ℕ) (hk : ∀ x ∈ maximalIdeal R.A ^ (k + 1), g.f x = 0) :
    R.Trunc k →+* A.A :=
  Ideal.Quotient.lift _ (g.f : R.A →+* A.A) hk

abbrev mapMax (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] : Ideal M :=
  Ideal.map (algebraMap R.A M) (maximalIdeal R.A)

def truncTensor (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) :
    R.Trunc (k + 1) ⊗[R.A] M →ₐ[R.A] R.Trunc k ⊗[R.A] M :=
  Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R.A (Ideal.pow_le_pow_right (by omega)))
    (AlgHom.id R.A M)

@[simp] theorem truncTensor_tmul (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ)
    (r : R.A) (x : M) :
    R.truncTensor M k (Ideal.Quotient.mk _ r ⊗ₜ[R.A] x) = Ideal.Quotient.mk _ r ⊗ₜ[R.A] x := rfl

@[simp] theorem truncTensor_one_tmul (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ)
    (x : M) : R.truncTensor M k ((1 : R.Trunc (k + 1)) ⊗ₜ[R.A] x) = (1 : R.Trunc k) ⊗ₜ[R.A] x :=
  R.truncTensor_tmul M k 1 x

def truncQuot (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) :
    M ⧸ R.mapMax M ^ (k + 1) ≃+* R.Trunc k ⊗[R.A] M :=
  (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _).symm).trans
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor M (maximalIdeal R.A ^ (k + 1))).toRingEquiv

@[simp] theorem truncQuot_mk (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) (x : M) :
    R.truncQuot M k (Ideal.Quotient.mk _ x) = (1 : R.Trunc k) ⊗ₜ[R.A] x := by
  simp [truncQuot]

theorem truncQuot_symm_tmul (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ) (x : M) :
    (R.truncQuot M k).symm ((1 : R.Trunc k) ⊗ₜ[R.A] x) = Ideal.Quotient.mk _ x := by
  rw [RingEquiv.symm_apply_eq, truncQuot_mk]

theorem truncQuot_symm_truncTensor (R : LocAlg O Or) (M : Type) [CommRing M] [Algebra R.A M] (k : ℕ)
    (z : R.Trunc (k + 1) ⊗[R.A] M) :
    (R.truncQuot M k).symm (R.truncTensor M k z) =
      Ideal.Quotient.factorPow (R.mapMax M) (Nat.le_succ (k + 1)) ((R.truncQuot M (k + 1)).symm z) := by
  obtain ⟨w, rfl⟩ := (R.truncQuot M (k + 1)).surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [RingEquiv.symm_apply_apply, truncQuot_mk, truncTensor_one_tmul, truncQuot_symm_tmul]
  rfl

end LocAlg

end LocAlg

section Cart

variable {p : ℕ}

def IsCart {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {G' : PDivGroup p R'}
    {G : PDivGroup p R} (s : PDivGroup.SemiHom σ G' G) : Prop :=
  letI := σ.toAlgebra; IsIso (PDivGroup.SemiHom.lift s)

end Cart

section Defo

variable (p : ℕ) [Fact p.Prime] {O Or : Type} [CommRing O] [CommRing Or] [IsLocalRing Or]
  [Algebra O Or] (Hb : VarpiDivModule p O (ResidueField Or))

structure Defo (S : Type) [CommRing S] [Algebra O S] (red : S →+* ResidueField Or) : Type 1 where

  H : VarpiDivModule p O S

  s : PDivGroup.SemiHom red Hb.G H.G

  cart : IsCart s

  comm : ∀ (c : O) (n : ℕ) (a : H.G.A n),
    s.app n (PDivGroup.Hom.app (H.ι c) n a) = PDivGroup.Hom.app (Hb.ι c) n (s.app n a)

variable {p Hb}

section Iso

variable {S : Type} [CommRing S] [Algebra O S] {red : S →+* ResidueField Or}

structure DefoIso (D D' : Defo p Hb S red) : Type where

  e : D.H ≅ D'.H

  compat : ∀ n a, D.s.app n (PDivGroup.Hom.app e.hom.f n a) = D'.s.app n a

def DefoIso.refl (D : Defo p Hb S red) : DefoIso D D := ⟨Iso.refl _, fun _ _ => rfl⟩

def DefoIso.symm {D D' : Defo p Hb S red} (i : DefoIso D D') : DefoIso D' D :=
  ⟨i.e.symm, fun n a => by
    have h := congrArg (fun g : D.H ⟶ D.H => PDivGroup.Hom.app g.f n a) i.e.hom_inv_id
    simp only [VarpiDivModule.comp_f, VarpiDivModule.id_f, PDivGroup.comp_app,
      PDivGroup.id_app] at h
    rw [← i.compat n]
    exact congrArg (D.s.app n) h⟩

def DefoIso.trans {D D' D'' : Defo p Hb S red} (i : DefoIso D D') (j : DefoIso D' D'') :
    DefoIso D D'' :=
  ⟨i.e.trans j.e, fun n a => by
    simp only [Iso.trans_hom, VarpiDivModule.comp_f, PDivGroup.comp_app]
    exact (i.compat n _).trans (j.compat n a)⟩

variable (p Hb S red) in

def defoSetoid : Setoid (Defo p Hb S red) where
  r D D' := Nonempty (DefoIso D D')
  iseqv := ⟨fun D => ⟨DefoIso.refl D⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

end Iso

variable (p Hb) in

def DefFun (A : LocAlg O Or) : Type 1 := Quotient (defoSetoid p Hb A.A A.red)

def IsPush {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} (f : S →+* S')
    (D : Defo p Hb S red) (D' : Defo p Hb S' red') : Prop :=
  ∃ t : PDivGroup.SemiHom f D'.H.G D.H.G, IsCart t ∧
    (∀ (c : O) (n : ℕ) (a : D.H.G.A n),
      t.app n (PDivGroup.Hom.app (D.H.ι c) n a) = PDivGroup.Hom.app (D'.H.ι c) n (t.app n a)) ∧
    ∀ n a, D'.s.app n (t.app n a) = D.s.app n a

structure Push {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} (f : S →+* S')
    (D : Defo p Hb S red) (D' : Defo p Hb S' red') : Type where

  t : PDivGroup.SemiHom f D'.H.G D.H.G

  cart : IsCart t

  comm : ∀ (c : O) (n : ℕ) (a : D.H.G.A n),
    t.app n (PDivGroup.Hom.app (D.H.ι c) n a) = PDivGroup.Hom.app (D'.H.ι c) n (t.app n a)

  s_app : ∀ n a, D'.s.app n (t.app n a) = D.s.app n a

theorem Push.isPush {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
    {red : S →+* ResidueField Or} {red' : S' →+* ResidueField Or} {f : S →+* S'}
    {D : Defo p Hb S red} {D' : Defo p Hb S' red'} (P : Push f D D') : IsPush f D D' :=
  ⟨P.t, P.cart, P.comm, P.s_app⟩


variable (p Hb) in

structure ProRep (R : LocAlg O Or) : Type 1 where
  [noeth : IsNoetherianRing R.A]
  [complete : IsAdicComplete (maximalIdeal R.A) R.A]

  univ : ∀ k : ℕ, Defo p Hb (R.Trunc k) (R.truncRed k)

  tr : ∀ k, Push (R.truncMap k) (univ (k + 1)) (univ k)

  universal : ∀ (A : LocAlg O Or) [IsArtinianRing A.A] (D : Defo p Hb A.A A.red),
    ∃! g : R ⟶ A, ∃ (k : ℕ) (hk : ∀ x ∈ maximalIdeal R.A ^ (k + 1), g.f x = 0),
      IsPush (LocAlg.truncLift g k hk) (univ k) D

theorem ProRep.trans {R : LocAlg O Or} (U : ProRep p Hb R) (k : ℕ) :
    IsPush (R.truncMap k) (U.univ (k + 1)) (U.univ k) :=
  (U.tr k).isPush

end Defo

section Level

def evBC {S B : Type} [CommRing S] [CommRing B] [Algebra S B] (R' : Type) [CommRing R']
    [Algebra S R'] (x : B →ₐ[S] R') : R' ⊗[S] B →ₐ[R'] R' :=
  Algebra.TensorProduct.lift (AlgHom.id R' R') x fun _ _ => Commute.all _ _

def IsFullSet {S B T J : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing T] [Algebra S T]
    (P : J → (B →ₐ[S] T)) : Prop :=
  Finite J ∧ ∀ (R' : Type) [CommRing R'] [Nontrivial R'] [Algebra S R'] (j : T →ₐ[S] R'),
    Module.Free R' (R' ⊗[S] B) ∧ Module.Finite R' (R' ⊗[S] B) ∧
      Module.finrank R' (R' ⊗[S] B) = Nat.card J ∧
      ∀ f : R' ⊗[S] B, Algebra.norm R' f = ∏ᶠ i, evBC R' (j.comp (P i)) f

theorem IsFullSet.comp_equiv {S B T J J' : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing T]
    [Algebra S T] {P : J → (B →ₐ[S] T)} (h : IsFullSet P) (e : J' ≃ J) : IsFullSet (P ∘ e) := by
  refine ⟨(Equiv.finite_iff e).2 h.1, fun R' _ _ _ j => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.2 R' j
  refine ⟨h1, h2, h3.trans (Nat.card_congr e).symm, fun f => (h4 f).trans ?_⟩
  exact (finprod_comp_equiv e (f := fun i => evBC R' (j.comp (P i)) f)).symm

theorem IsFullSet.comp {S B T T' J : Type} [CommRing S] [CommRing B] [Algebra S B] [CommRing T]
    [Algebra S T] [CommRing T'] [Algebra S T'] {P : J → (B →ₐ[S] T)} (h : IsFullSet P)
    (g : T →ₐ[S] T') : IsFullSet fun i => g.comp (P i) :=
  ⟨h.1, fun R' _ _ _ j => by simpa only [AlgHom.comp_assoc] using h.2 R' (j.comp g)⟩

variable {p : ℕ} [Fact p.Prime] {O S : Type} [CommRing O] [CommRing S]

def torIdeal (G : PDivGroup p S) (ι : PDivGroup.Action O G) (ϖ : O) (m : ℕ) : Ideal (G.A m) :=
  kerIdeal (PDivGroup.Hom.app (ι (ϖ ^ m)) m)

variable [Algebra O S] (p)

@[ext] structure Level (G : PDivGroup p S) (ι : PDivGroup.Action O G) (ϖ : O) (n m : ℕ) (T : Type)
    [CommRing T] [Algebra S T] : Type where

  α : (Fin n → O ⧸ Ideal.span {ϖ ^ m}) → (G.A m →ₐ[S] T)

  tors : ∀ x, ∀ a ∈ torIdeal G ι ϖ m, α x a = 0

  map_add : ∀ x y, WithConv.toConv (α (x + y)) = WithConv.toConv (α x) * WithConv.toConv (α y)

  map_smul : ∀ (c : O) x,
    α (c • x) = (α x).comp (PDivGroup.Hom.app (ι c) m : G.A m →ₐ[S] G.A m)

  full : IsFullSet fun x => Ideal.Quotient.liftₐ (torIdeal G ι ϖ m) (α x) (tors x)

variable {p}

namespace Level

variable {G : PDivGroup p S} {ι : PDivGroup.Action O G} {ϖ : O} {n m : ℕ} {T T' : Type}
  [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T']

def map (L : Level p G ι ϖ n m T) (g : T →ₐ[S] T') : Level p G ι ϖ n m T' where
  α x := g.comp (L.α x)
  tors x a ha := by rw [AlgHom.comp_apply, L.tors x a ha, map_zero]
  map_add x y := by
    have h := congrArg (ptsPush (G.A m) g) (L.map_add x y)
    rw [map_mul] at h
    exact h
  map_smul c x := by rw [L.map_smul, AlgHom.comp_assoc]
  full := by
    have e : (fun x => Ideal.Quotient.liftₐ (torIdeal G ι ϖ m) (g.comp (L.α x))
        (fun a ha => by rw [AlgHom.comp_apply, L.tors x a ha, map_zero])) =
        fun x => g.comp (Ideal.Quotient.liftₐ (torIdeal G ι ϖ m) (L.α x) (L.tors x)) :=
      funext fun x => Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => rfl)
    rw [e]
    exact L.full.comp g

@[simp] theorem map_α (L : Level p G ι ϖ n m T) (g : T →ₐ[S] T') (x) : (L.map g).α x = g.comp (L.α x) :=
  rfl

def act (L : Level p G ι ϖ n m T) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) : Level p G ι ϖ n m T where
  α x := L.α (g.val.mulVec x)
  tors x := L.tors _
  map_add x y := by rw [Matrix.mulVec_add]; exact L.map_add _ _
  map_smul c x := by rw [Matrix.mulVec_smul]; exact L.map_smul _ _
  full := L.full.comp_equiv (glEquiv g).toEquiv

@[simp] theorem act_α (L : Level p G ι ϖ n m T) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (x) :
    (L.act g).α x = L.α (g.val.mulVec x) := rfl

theorem map_map {T'' : Type} [CommRing T''] [Algebra S T''] (L : Level p G ι ϖ n m T) (g : T →ₐ[S] T')
    (h : T' →ₐ[S] T'') : (L.map g).map h = L.map (h.comp g) :=
  Level.ext (funext fun _ => rfl)

@[simp] theorem map_id (L : Level p G ι ϖ n m T) : L.map (AlgHom.id S T) = L :=
  Level.ext (funext fun _ => AlgHom.id_comp _)

theorem act_map (L : Level p G ι ϖ n m T) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (h : T →ₐ[S] T') :
    (L.act g).map h = (L.map h).act g :=
  Level.ext (funext fun _ => rfl)

theorem act_mul (L : Level p G ι ϖ n m T) (a b : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    (L.act a).act b = L.act (a * b) :=
  Level.ext (funext fun x => by simp only [act_α, Units.val_mul, Matrix.mulVec_mulVec])

@[simp] theorem act_one (L : Level p G ι ϖ n m T) : L.act 1 = L :=
  Level.ext (funext fun x => by simp only [act_α, Units.val_one, Matrix.one_mulVec])

instance : MulAction (GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}))ᵐᵒᵖ (Level p G ι ϖ n m T) where
  smul g L := L.act g.unop
  one_smul L := Level.ext (funext fun x => by
    change L.α ((1 : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})).val.mulVec x) = L.α x
    rw [Units.val_one, Matrix.one_mulVec])
  mul_smul g h L := Level.ext (funext fun x => by
    change L.α ((h.unop * g.unop).val.mulVec x) = L.α (h.unop.val.mulVec (g.unop.val.mulVec x))
    rw [Units.val_mul, Matrix.mulVec_mulVec])

end Level

end Level

section LevelRep

variable {p : ℕ} [Fact p.Prime] {O Or : Type} [CommRing O] [CommRing Or] [IsLocalRing Or]
  [Algebra O Or] {Hb : VarpiDivModule p O (ResidueField Or)}

structure LevelRep {R : LocAlg O Or} (U : ProRep p Hb R) (ϖ : O) (n m : ℕ) : Type 1 where

  Rm : Type
  [ring : CommRing Rm]
  [alg : Algebra R.A Rm]

  [complete : IsAdicComplete (R.mapMax Rm) Rm]

  lev : ∀ k : ℕ, Level p (U.univ k).H.G (U.univ k).H.ι ϖ n m (R.Trunc k ⊗[R.A] Rm)

  compat : ∀ (k : ℕ) (x : Fin n → O ⧸ Ideal.span {ϖ ^ m}) (a : (U.univ (k + 1)).H.G.A m),
    (lev k).α x ((U.tr k).t.app m a) = R.truncTensor Rm k ((lev (k + 1)).α x a)

  rep : ∀ (k : ℕ) (B : Type) [CommRing B] [Algebra (R.Trunc k) B],
    Function.Bijective fun h : R.Trunc k ⊗[R.A] Rm →ₐ[R.Trunc k] B => (lev k).map h

attribute [instance] LevelRep.ring LevelRep.alg LevelRep.complete

variable {R : LocAlg O Or} {U : ProRep p Hb R} {ϖ : O} {n m : ℕ}

def LevelRep.aut (L : LevelRep U ϖ n m) (k : ℕ) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    R.Trunc k ⊗[R.A] L.Rm →ₐ[R.Trunc k] R.Trunc k ⊗[R.A] L.Rm :=
  (Equiv.ofBijective _ (L.rep k _)).symm ((L.lev k).act g)

namespace LevelRep

variable (L : LevelRep U ϖ n m)

theorem aut_spec (k : ℕ) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    (L.lev k).map (L.aut k g) = (L.lev k).act g :=
  Equiv.ofBijective_apply_symm_apply _ (L.rep k _) _

theorem aut_one (k : ℕ) : L.aut k 1 = AlgHom.id _ _ := by
  apply (L.rep k _).1
  change (L.lev k).map (L.aut k 1) = (L.lev k).map (AlgHom.id _ _)
  rw [L.aut_spec, Level.act_one, Level.map_id]

theorem aut_mul (k : ℕ) (g h : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    L.aut k (g * h) = (L.aut k g).comp (L.aut k h) := by
  apply (L.rep k _).1
  change (L.lev k).map (L.aut k (g * h)) = (L.lev k).map ((L.aut k g).comp (L.aut k h))
  rw [L.aut_spec, ← Level.map_map, L.aut_spec k h, Level.act_map, L.aut_spec k g, Level.act_mul]

theorem truncTensor_aut (k : ℕ) (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}))
    (z : R.Trunc (k + 1) ⊗[R.A] L.Rm) :
    R.truncTensor L.Rm k (L.aut (k + 1) g z) = L.aut k g (R.truncTensor L.Rm k z) := by
  letI : Algebra (R.Trunc (k + 1)) (R.Trunc k ⊗[R.A] L.Rm) :=
    ((algebraMap (R.Trunc k) (R.Trunc k ⊗[R.A] L.Rm)).comp (R.truncMap k)).toAlgebra
  have hc : ∀ r : R.Trunc (k + 1),
      R.truncTensor L.Rm k (algebraMap (R.Trunc (k + 1)) (R.Trunc (k + 1) ⊗[R.A] L.Rm) r) =
        algebraMap (R.Trunc k) (R.Trunc k ⊗[R.A] L.Rm) (R.truncMap k r) := fun r => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rfl
  let φ₁ : R.Trunc (k + 1) ⊗[R.A] L.Rm →ₐ[R.Trunc (k + 1)] R.Trunc k ⊗[R.A] L.Rm :=
    { toRingHom := (R.truncTensor L.Rm k).toRingHom.comp (L.aut (k + 1) g).toRingHom
      commutes' := fun r => by
        change R.truncTensor L.Rm k (L.aut (k + 1) g (algebraMap _ _ r)) = _
        rw [AlgHom.commutes]
        exact hc r }
  let φ₂ : R.Trunc (k + 1) ⊗[R.A] L.Rm →ₐ[R.Trunc (k + 1)] R.Trunc k ⊗[R.A] L.Rm :=
    { toRingHom := (L.aut k g).toRingHom.comp (R.truncTensor L.Rm k).toRingHom
      commutes' := fun r => by
        change L.aut k g (R.truncTensor L.Rm k (algebraMap _ _ r)) = _
        rw [hc r, AlgHom.commutes]
        rfl }
  have key : φ₁ = φ₂ := by
    apply (L.rep (k + 1) (R.Trunc k ⊗[R.A] L.Rm)).1
    refine Level.ext (funext fun x => AlgHom.ext fun a => ?_)
    change R.truncTensor L.Rm k (L.aut (k + 1) g ((L.lev (k + 1)).α x a)) =
      L.aut k g (R.truncTensor L.Rm k ((L.lev (k + 1)).α x a))
    have h1 := congrArg (fun M => M.α x a) (L.aut_spec (k + 1) g)
    have h2 := congrArg (fun M => M.α x ((U.tr k).t.app m a)) (L.aut_spec k g)
    simp only [Level.map_α, Level.act_α, AlgHom.comp_apply] at h1 h2
    rw [h1, ← L.compat k _ a, ← L.compat k x a, h2]
  exact DFunLike.congr_fun key z

theorem succ_strictMono : StrictMono fun k : ℕ => k + 1 := fun _ _ h => Nat.succ_lt_succ h

def actTrunc (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (k : ℕ) :
    L.Rm →+* L.Rm ⧸ R.mapMax L.Rm ^ (k + 1) :=
  (R.truncQuot L.Rm k).symm.toRingHom.comp
    ((L.aut k g).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom))

theorem actTrunc_compat (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) {k : ℕ} :
    (Ideal.Quotient.factorPow (R.mapMax L.Rm) (succ_strictMono.monotone k.le_succ)).comp
      (L.actTrunc g (k + 1)) = L.actTrunc g k := by
  ext x
  change Ideal.Quotient.factorPow (R.mapMax L.Rm) (succ_strictMono.monotone k.le_succ)
      ((R.truncQuot L.Rm (k + 1)).symm (L.aut (k + 1) g ((1 : R.Trunc (k + 1)) ⊗ₜ[R.A] x))) =
    (R.truncQuot L.Rm k).symm (L.aut k g ((1 : R.Trunc k) ⊗ₜ[R.A] x))
  rw [← LocAlg.truncQuot_symm_truncTensor, L.truncTensor_aut, LocAlg.truncTensor_one_tmul]

def actRing (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) : L.Rm →+* L.Rm :=
  IsAdicComplete.StrictMono.liftRingHom (R.mapMax L.Rm) succ_strictMono (L.actTrunc g)
    (L.actTrunc_compat g)

theorem eq_of_tmul {x y : L.Rm}
    (h : ∀ k, (1 : R.Trunc k) ⊗ₜ[R.A] x = (1 : R.Trunc k) ⊗ₜ[R.A] y) : x = y := by
  have := IsHausdorff.StrictMono.funext' (R.mapMax L.Rm) succ_strictMono
    (f := fun _ : Unit => x) (g := fun _ => y) (fun k _ => by
      rw [← LocAlg.truncQuot_symm_tmul, ← LocAlg.truncQuot_symm_tmul, h k])
  exact congrFun this ()

theorem tmul_actRing (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (k : ℕ) (x : L.Rm) :
    (1 : R.Trunc k) ⊗ₜ[R.A] L.actRing g x = L.aut k g ((1 : R.Trunc k) ⊗ₜ[R.A] x) := by
  apply (R.truncQuot L.Rm k).symm.injective
  rw [LocAlg.truncQuot_symm_tmul]
  exact IsAdicComplete.StrictMono.mk_liftRingHom (R.mapMax L.Rm) succ_strictMono _ _ x

theorem actRing_one : L.actRing 1 = RingHom.id _ :=
  RingHom.ext fun x => L.eq_of_tmul fun k => by rw [L.tmul_actRing, L.aut_one]; rfl

theorem actRing_mul (g h : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) :
    L.actRing (g * h) = (L.actRing g).comp (L.actRing h) :=
  RingHom.ext fun x => L.eq_of_tmul fun k => by
    rw [RingHom.comp_apply, L.tmul_actRing, L.tmul_actRing, L.tmul_actRing, L.aut_mul]
    rfl

theorem actRing_algebraMap (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (r : R.A) :
    L.actRing g (algebraMap R.A L.Rm r) = algebraMap R.A L.Rm r :=
  L.eq_of_tmul fun k => by
    rw [L.tmul_actRing]
    have e : (1 : R.Trunc k) ⊗ₜ[R.A] algebraMap R.A L.Rm r = algebraMap R.A (R.Trunc k ⊗[R.A] L.Rm) r :=
      Algebra.TensorProduct.includeRight.commutes r
    rw [e]
    exact ((L.aut k g).restrictScalars R.A).commutes r

def actEquiv : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}) →* (L.Rm ≃ₐ[R.A] L.Rm) where
  toFun g := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (L.actRing g) (L.actRing g⁻¹)
      (by rw [← L.actRing_mul, mul_inv_cancel, L.actRing_one])
      (by rw [← L.actRing_mul, inv_mul_cancel, L.actRing_one]))
    (L.actRing_algebraMap g)
  map_one' := AlgEquiv.ext fun x => by
    change L.actRing 1 x = x
    rw [L.actRing_one]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change L.actRing (g * h) x = L.actRing g (L.actRing h x)
    rw [L.actRing_mul]; rfl

instance mulSemiringAction : MulSemiringAction (GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) L.Rm :=
  MulSemiringAction.compHom L.Rm L.actEquiv

theorem smul_def (g : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) (x : L.Rm) : g • x = L.actRing g x := by
  change L.actEquiv g x = _
  rfl

end LevelRep

end LevelRep

section Examples

variable (O Or : Type) [CommRing O] [CommRing Or] [IsLocalRing Or] [Algebra O Or]

example : IsArtinianRing (LocAlg.residueField (O := O) (Or := Or)).A :=
  inferInstanceAs (IsArtinianRing (ResidueField Or))

example (r : Or) : (LocAlg.residueField (O := O) (Or := Or)).red (residue Or r) = residue Or r :=

  LocAlg.red_algebraMap LocAlg.residueField r

example (p : ℕ) [Fact p.Prime] (S T : Type) [CommRing S] [Algebra O S] [CommRing T] [Algebra S T]
    (G : PDivGroup p S) (ι : PDivGroup.Action O G) (ϖ : O) (n m : ℕ) :
    MulAction (GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m}))ᵐᵒᵖ (Level p G ι ϖ n m T) := inferInstance

example (p : ℕ) [Fact p.Prime] {Hb : GlobalTheory.VDiv.VarpiDivModule p O (ResidueField Or)} {R : LocAlg O Or}
    {U : ProRep p Hb R} {ϖ : O} {n m : ℕ} (L : LevelRep U ϖ n m) (x : L.Rm) :
    (1 : GL (Fin n) (O ⧸ Ideal.span {ϖ ^ m})) • x = L.actRing 1 x ∧ L.actRing 1 x = x :=
  ⟨L.smul_def 1 x, by rw [L.actRing_one]; rfl⟩

end Examples

end GlobalTheory.VDefo
end
end
