import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory

theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.NoTwHom

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def IsTw {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (f : V →ₗ[ℂ] V') : Prop :=
  ∀ (σ : Weil h) (v : V), f ((((normV w : ℕ) : ℂ) ^ deg σ) • a.ρ σ v) = b.ρ σ (f v)

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

theorem IsTw.inl {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a1 : WDRep h V} {a2 : WDRep h V2} {b : WDRep h V'} {g : V × V2 →ₗ[ℂ] V'}
    (hg : IsTw (a1.sum a2) b g) : IsTw a1 b (g ∘ₗ LinearMap.inl ℂ V V2) := by
  intro σ v
  have : LinearMap.inl ℂ V V2 ((((normV w : ℕ) : ℂ) ^ deg σ) • a1.ρ σ v) =
      (((normV w : ℕ) : ℂ) ^ deg σ) • (a1.sum a2).ρ σ (LinearMap.inl ℂ V V2 v) := by
    ext <;> simp
  rw [LinearMap.comp_apply, this, hg]; rfl

theorem IsTw.inr {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a1 : WDRep h V} {a2 : WDRep h V2} {b : WDRep h V'} {g : V × V2 →ₗ[ℂ] V'}
    (hg : IsTw (a1.sum a2) b g) : IsTw a2 b (g ∘ₗ LinearMap.inr ℂ V V2) := by
  intro σ v
  have : LinearMap.inr ℂ V V2 ((((normV w : ℕ) : ℂ) ^ deg σ) • a2.ρ σ v) =
      (((normV w : ℕ) : ℂ) ^ deg σ) • (a1.sum a2).ρ σ (LinearMap.inr ℂ V V2 v) := by
    ext <;> simp
  rw [LinearMap.comp_apply, this, hg]; rfl

theorem IsTw.fst {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a : WDRep h W} {b1 : WDRep h V} {b2 : WDRep h V2} {g : W →ₗ[ℂ] V × V2}
    (hg : IsTw a (b1.sum b2) g) : IsTw a b1 (LinearMap.fst ℂ V V2 ∘ₗ g) := by
  intro σ v
  rw [LinearMap.comp_apply, hg]; rfl

theorem IsTw.snd {V2 : Type} [AddCommGroup V2] [Module ℂ V2] [FiniteDimensional ℂ V2]
    {a : WDRep h W} {b1 : WDRep h V} {b2 : WDRep h V2} {g : W →ₗ[ℂ] V × V2}
    (hg : IsTw a (b1.sum b2) g) : IsTw a b2 (LinearMap.snd ℂ V V2 ∘ₗ g) := by
  intro σ v
  rw [LinearMap.comp_apply, hg]; rfl

end

end GlobalTheory.WeilDeligne.NoTwHom
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnlinkedMono

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem noMonodromy_of_mem_weilDeligneListSum : ∀ (l : List (WD h)), (sumList l).mono0 → ∀ y ∈ l, y.mono0
  | [], _, y, hy => by simp at hy
  | z :: l, H, y, hy => by
    have H2 : (z.lpSum (sumList l)).mono0 := H
    obtain ⟨n, a, rfl⟩ := WD.exists_rep z
    obtain ⟨m, b, hb⟩ := WD.exists_rep (sumList l)
    rw [← hb, WD.lpSum_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N] at H2
    have ha : a.N = 0 := LinearMap.ext fun v => by
      simpa using congrArg Prod.fst (LinearMap.congr_fun H2 (v, 0))
    have hb' : b.N = 0 := LinearMap.ext fun v => by
      simpa using congrArg Prod.snd (LinearMap.congr_fun H2 (0, v))
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (WD.monodromyZero_ofWeilDeligneRepClass_iff a).2 ha
    · exact noMonodromy_of_mem_weilDeligneListSum l (by rw [← hb]; exact (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hb') y hy

theorem lpTw_one_ne (x : WD h) (hx : 0 < x.lpDim) : x.lpTw 1 ≠ x := GlobalTheory.WeilDeligne.WD.lpTw_one_ne x hx

section
variable {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

end

end GlobalTheory.UnlinkedMono
end
end
