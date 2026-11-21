import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Divisibility.RowSideTie

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev csdK : CSD X.K := MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev actK : Representation X.K (G0 X.E Pr.vGs R.r) (csdK W Ch sel mu hX).Forms :=
  g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev dimP : ℕ := (csdK W Ch sel mu hX).lvlDim (actK W Ch sel mu hX) P.grp P.chr

abbrev resK : (mtildeKGSD W Ch sel mu).EqFun ≃ₗ[X.K] (csdK W Ch sel mu hX).Forms :=
  (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)

abbrev formK (x : Fin (dimP W Ch sel mu P hX) → X.K) : (csdK W Ch sel mu hX).Forms :=
  LiftForms.lvlForm (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr x

theorem resK_symm_act (a : G0 X.E Pr.vGs R.r) (f : (csdK W Ch sel mu hX).Forms) :
    (resK W Ch sel mu hX).symm (actK W Ch sel mu hX a f) = g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm f) :=
  LinearEquiv.symm_apply_apply _ _

theorem resK_act (a : G0 X.E Pr.vGs R.r) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    actK W Ch sel mu hX a (resK W Ch sel mu hX φ) = resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a φ) := by
  show resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm (resK W Ch sel mu hX φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem formK_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    formK W Ch sel mu P hX x ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
  rw [← LiftForms.range_lvlForm]
  exact ⟨x, rfl⟩

theorem zOf_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine (mem_MtildeV_iff W Ch sel mu P _).2 ⟨Subtype.prop _, fun a => ?_⟩
  refine (resK_symm_act W Ch sel mu hX a.1 _).symm.trans ?_
  rw [formK_mem W Ch sel mu P hX x a, map_smul]

def zOf : (Fin (dimP W Ch sel mu P hX) → X.K) →ₗ[X.K] MtildeV W Ch sel mu P where
  toFun x := ⟨_, zOf_mem W Ch sel mu P hX x⟩
  map_add' x y := Subtype.ext (by simp only [map_add]; rfl)
  map_smul' c x := Subtype.ext (by simp only [map_smul]; rfl)

theorem zOf_val (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    (zOf W Ch sel mu P hX x).1 = ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 := rfl

theorem zOf_injective : Function.Injective (zOf W Ch sel mu P hX) := by
  intro x y h
  apply LiftForms.lvlForm_injective (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr
  apply (resK W Ch sel mu hX).symm.injective
  have h1 : (zOf W Ch sel mu P hX x).1 = (zOf W Ch sel mu P hX y).1 := congrArg Subtype.val h
  exact Subtype.ext h1

theorem zOf_surjective : Function.Surjective (zOf W Ch sel mu P hX) := by
  intro φ
  obtain ⟨hφ, hact⟩ := (mem_MtildeV_iff W Ch sel mu P φ.1).1 φ.2
  have hf : resK W Ch sel mu hX ⟨φ.1, hφ⟩ ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
    intro a
    rw [resK_act, hact a, map_smul]
  rw [← LiftForms.range_lvlForm] at hf
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, Subtype.ext ?_⟩
  rw [zOf_val]
  show ((resK W Ch sel mu hX).symm (LiftForms.lvlForm _ _ P.grp P.chr x)).1 = φ.1
  rw [hx, LinearEquiv.symm_apply_apply]

def zEquiv : (Fin (dimP W Ch sel mu P hX) → X.K) ≃ₗ[X.K] MtildeV W Ch sel mu P :=
  LinearEquiv.ofBijective (zOf W Ch sel mu P hX) ⟨zOf_injective W Ch sel mu P hX, zOf_surjective W Ch sel mu P hX⟩

end Gen

end GlobalTheory.Mem.ColTie
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Lin

variable {K M : Type} [Field K] [AddCommGroup M] [Module ℂ M] {σ : K →+* ℂ} {n : ℕ}

theorem eq_sum_single (x : Fin n → K) : x = ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_span_single (j : (Fin n → K) →ₛₗ[σ] M) (x : Fin n → K) :
    j x ∈ Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) := by
  rw [eq_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_single_eq (j : (Fin n → K) →ₛₗ[σ] M) :
    Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact mem_span_single j x

theorem exists_equiv_of_bases {M' : Type} [AddCommGroup M'] [Module ℂ M'] (j : (Fin n → K) →ₛₗ[σ] M)
    (j' : (Fin n → K) →ₛₗ[σ] M') (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (hli' : LinearIndependent ℂ fun i => j' (Pi.single i 1))
    (hsp' : Submodule.span ℂ (Set.range fun i => j' (Pi.single i 1)) = ⊤) :
    ∃ e : M ≃ₗ[ℂ] M', ∀ x, e (j x) = j' x := by
  let b := Module.Basis.mk hli hsp.ge
  let b' := Module.Basis.mk hli' hsp'.ge
  refine ⟨b.equiv b' (Equiv.refl _), fun x => ?_⟩
  rw [eq_sum_single x, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ j, map_smulₛₗ j', LinearEquiv.map_smul]
  congr 1
  have h1 : j (Pi.single i 1) = b i := (Module.Basis.mk_apply hli hsp.ge i).symm
  have h2 : j' (Pi.single i 1) = b' i := (Module.Basis.mk_apply hli' hsp'.ge i).symm
  rw [h1, h2, Module.Basis.equiv_apply, Equiv.refl_apply]

end Lin

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

def ipLev (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeGSD W Ch sel mu P).ip (mtildeOk W Ch sel mu hX P) z.1 z'.1

def ipK (z z' : MtildeV W Ch sel mu P) : X.K :=
  (mtildeKGSD W Ch sel mu).ip (mtildeKOk W Ch sel mu hX) z.1 z'.1

theorem li_zOf : LinearIndependent X.K fun i => zOf W Ch sel mu P hX (Pi.single i 1) := by
  have h := (Pi.basisFun X.K (Fin (dimP W Ch sel mu P hX))).linearIndependent.map' (zOf W Ch sel mu P hX)
    (LinearMap.ker_eq_bot.2 (zOf_injective W Ch sel mu P hX))
  simpa [Function.comp_def] using h

def jP (σ : X.K →+* ℂ) : (Fin (dimP W Ch sel mu P hX) → X.K) →ₛₗ[σ] MtP W Ch sel mu P σ :=
  (toMtP W Ch sel mu P σ).comp (zOf W Ch sel mu P hX)

theorem linearIndependent_jP_single (σ : X.K →+* ℂ) : LinearIndependent ℂ fun i => jP W Ch sel mu P hX σ (Pi.single i 1) :=
  toMtilde_linearIndependent W Ch sel mu P σ (li_zOf W Ch sel mu P hX)

theorem span_range_jP_single_eq_top (σ : X.K →+* ℂ) : Submodule.span ℂ (Set.range fun i => jP W Ch sel mu P hX σ (Pi.single i 1)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← toMtilde_span W Ch sel mu P σ hX, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := zOf_surjective W Ch sel mu P hX z
  exact mem_span_single (jP W Ch sel mu P hX σ) x

end Gen

section TC

attribute [local instance] starE

def sig (B : Base) : B.fields.K →+* ℂ := B.embLL

end TC

end GlobalTheory.Mem.ColTie
end
end
