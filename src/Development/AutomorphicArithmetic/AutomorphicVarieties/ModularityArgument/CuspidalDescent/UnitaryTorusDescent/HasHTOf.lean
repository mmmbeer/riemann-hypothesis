import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationSymmetry
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PlainTorOfPs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
open GlobalTheory.UnitaryBC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.P

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def HtGT (r : G F Ω →* GL (Fin n) (Qbar l)) (HT : (F →+* Qbar l) → Multiset ℤ) (w : HeightOneSpectrum (𝓞 F))
    (τ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) → HasHTAt r HT w

end UpperTheory.V.Z.Desc.P
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Desc.P.typeTor :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω) (h : IsPlaceOver A w) (χ : Fin n → G E Ω →* ℂˣ) (y : WD h),
    Hi.IsTypeWD h (fun i => (χ i).comp (Ine (F := E) A).subtype) y → Z.Win.Gd y := by
  intro E Ω _ _ _ _ _ n w A h χ y hy
  obtain ⟨b, rfl, hN, hρ⟩ := hy
  have key : ∀ c : Weil h, (hc : deg c = 0) → (∀ k, χ k c.1 = 1) → LocalGlobalAboveLAlt.Triv (WD.mk b) c := by
    intro c hc hk
    have hmem : (c : G E Ω) ∈ Ine A := deg_eq_zero_iff.1 hc
    have hρ1 : b.ρ c = 1 := by
      have := hρ ⟨c, hmem⟩
      have hinc : ineIncl h ⟨c, hmem⟩ = c := rfl
      rw [hinc] at this
      rw [this]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hk, Units.val_one,
        Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    show (WD.mk b).charPol c = (Polynomial.X - 1) ^ (WD.mk b).lpDim
    rw [WD.charPol_mk, WD.lpDim_mk, hρ1, LinearMap.charpoly_one, Module.finrank_fin_fun]
  refine ⟨fun s t => key _ ?_ (fun k => ?_), (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN⟩
  · rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  · have := map_commutatorElement ((χ k).comp (Weil h).subtype) s t
    exact this.trans (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (((χ k).comp (Weil h).subtype) s) _))
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.P

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin n) (Qbar l)} {w : Plc L} {τ : SmIrr (GLw n w)} {A : ValuationSubring Ω}
  {HT : (L →+* Qbar l) → Multiset ℤ}

theorem lgAwayT (k : LocGlobT ι r w τ) (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion L) → WD h) (hrc : IsRecT h rc) : WOT ι r (rc (algNorm τ)) := (k A h rc hrc).1 hw

theorem woTypeT {h : IsPlaceOver A w} {y : WD h} (k : WOT ι r y) (χ : Fin n → G L Ω →* ℂˣ)
    (t : IsTypeWD h (fun i => (χ i).comp (Ine (F := L) A).subtype) y) : IsWDOf ι r y :=
  WDT.isWDOf k (typeTor L Ω n w A h χ y t)

omit [IsAlgClosure L Ω] in

def HtEx (r : G L Ω →* GL (Fin n) (Qbar l)) : Prop := ∃ HT, Af.HasHT r HT

end UpperTheory.V.Z.Desc.P
end
end
