import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pull_zero (d : DeltaDat Xo c 0) : Pull d 0 0 := fun _ _ _ _ _ _ y₂ y _ =>
  (evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm

theorem pull_one (d : DeltaDat Xo c 0) : Pull d 1 1 := fun k _ _ _ _ _ y₂ y _ =>
  (GlobalTheory.RawSpan.evR_one_field k y₂).trans (GlobalTheory.RawSpan.evR_one_field k y).symm

theorem pull_add {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g) (h' : Pull d f' g') :
    Pull d (f + f') (g + g') := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_add _ _ g g' y₂).trans ((congrArg₂ (· + ·) (h k hk y₂ y ho) (h' k hk y₂ y ho)).trans (evalAt_add _ _ f f' y).symm)

theorem pull_smul {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) (a : c.F) :
    Pull d (a • f) (d.eF a • g) := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_smul _ _ (d.eF a) g y₂).trans
    ((congrArg₂ (· * ·) (hk a) (h k hk y₂ y ho)).trans (evalAt_smul _ _ a f y).symm)

theorem pull_inj {d : DeltaDat Xo c 0} (hd : d.IsLev) {f f' : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g)
    (h' : Pull d f' g) (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k) :
    evR Xo c f y = evR Xo c f' y := by
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
    congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  exact (h k hk y₂ y hy).symm.trans (h' k hk y₂ y hy)


theorem intAt_zero : IntAt Xo c 0 := by
  rintro la _ ⟨y, rfl⟩
  rw [vAtV_zero]; exact le_top

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

end GlobalTheory.LevPullModel
