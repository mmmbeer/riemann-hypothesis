import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers

section
set_option autoImplicit false

noncomputable section

open NumberField TensorProduct GlobalTheory.RealMult

namespace GlobalTheory.KSSymm

end GlobalTheory.KSSymm
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSSymm

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))

theorem cupSquare (HR : AbelianDeRham) : CupSquare (dp0 R) (𝟙 _) (X.A ⊗ X.A) :=
  cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim)

variable {X}

variable (X) in

theorem exists_form_of (HR : AbelianDeRham) (c : 𝔠.elt) : ∃ φ, IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ :=
  exists_isCorrForm (cupSquare X HR) (X.isLB c) (X.rig₁ c) (X.rig₂ c)

theorem form_fil (HR : AbelianDeRham) {c : 𝔠.elt} {φ : HdR X.A →ₗ[R] HdR X.A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) φ) : ∀ a ∈ Fil X.A, ∀ b ∈ Fil X.A, φ a b = 0 := by
  intro a ha b hb
  obtain ⟨ψ, hψ, eψ⟩ := hφ.isPolForm
  have t := (HR.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab) (smooth_prod X.dim X.dim) _
    (X.isLB c) ψ hψ).1 _ (push_mem_Fil (inl X.A X.A) ha) _ (push_mem_Fil (inr X.A X.A) hb)
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one] at t
  simpa using t

end GlobalTheory.KSSymm
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBijection

open TrivSqZeroExt KSSymm

section Crystal

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem fst_surj : Function.Surjective (fstHom R R R).toRingHom := fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩

def Comp (d : Crys (epsDP R) (DeRham.epsRed R) A) (f k : HdR A) : Prop :=
  ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (f c) + TrivSqZeroExt.inr (k c)

variable {d d' : Crys (epsDP R) (DeRham.epsRed R) A} {f f' k k' : HdR A}

theorem Comp.unique (h : Comp d f k) (h' : Comp d f' k') : f = f' ∧ k = k' :=
  ⟨LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.fst ((h c).symm.trans (h' c)),
    LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.snd ((h c).symm.trans (h' c))⟩

theorem comp_zero : Comp (0 : Crys (epsDP R) (DeRham.epsRed R) A) 0 0 := fun _ ↦ by
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  simp

theorem Comp.add (h : Comp d f k) (h' : Comp d' f' k') : Comp (d + d') (f + f') (k + k') := fun c ↦ by
  rw [LinearMap.add_apply, h, h']
  ext <;> simp

theorem Comp.smul (h : Comp d f k) (r : DualNumber R) : Comp (r • d) (r.fst • f) (r.fst • k + r.snd • f) :=
  fun c ↦ by
  rw [LinearMap.smul_apply, h]
  ext <;> simp [mul_comm]

theorem Comp.ext (hm : (constMor A).IsBC) (h : Comp d f k) (h' : Comp d' f k) : d = d' :=
  JetIsotropic.ext_of_isBC hm fun c ↦ (h c).trans (h' c).symm

theorem Comp.corr (hm : (constMor A).IsBC) (h : Comp d f k) : (redMor A).Corr d f := fun c ↦ by
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smul, h, LinearMap.map_smulₛₗ, redMor_constMor, LinearMap.map_smul]
    simp

theorem Comp.push (h : Comp d f k) (u : A ⟶ A) [IsMonHom u] :
    Comp (push (epsDP R) (DeRham.epsRed R) u d) (push (dp0 R) (𝟙 _) u f) (push (dp0 R) (𝟙 _) u k) := fun c ↦ by
  have kk := (homMor (dp0 R) (𝟙 _) u).comp (constMor A)
  have hM := homMor (epsDP R) (DeRham.epsRed R) u
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) u) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, h]
  rfl

variable [IsCommMonObj A] {O : Type} [CommRing O] {a : OAct O A} (hL : LieExact A)

def graph (κ : Fil A →ₗ[R] Serre.Lie a) : Submodule (DualNumber R) (Crys (epsDP R) (DeRham.epsRed R) A) where
  carrier := {d | ∃ (f : Fil A) (k : HdR A), Comp d f k ∧ hL.toLie a k = κ f}
  zero_mem' := ⟨0, 0, comp_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨f, k, h, e⟩ ⟨f', k', h', e'⟩
    exact ⟨f + f', k + k', h.add h', by rw [map_add, map_add, e, e']⟩
  smul_mem' := by
    rintro r _ ⟨f, k, h, e⟩
    have z : hL.toLie a f = 0 := (hL.ker_toLie a).ge f.2
    exact ⟨r.fst • f, _, h.smul r, by rw [map_add, map_smul, map_smul, map_smul, e, z, smul_zero, add_zero]⟩

variable (κ : Fil A →ₗ[R] Serre.Lie a)

end Crystal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R : Type} [CommRing R]
  {X : Obj F 𝔠 (Sp R)}

end GlobalTheory.KSBijection
end
end
