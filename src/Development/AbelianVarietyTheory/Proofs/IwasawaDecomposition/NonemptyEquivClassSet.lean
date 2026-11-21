import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VarietyWithModels
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LevPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Comp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

theorem fr_mul (C : Ctx Xo c σ V r) (a u : GA D V) (k : Fin C.F.n) (τ : (C.M.X k).Ψ) :
    mat (C.fr (a * u) k) τ = Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) a) * mat (C.fr u k) τ := by
  have h : archM V (C.θ τ.1) (a * u) = archM V (C.θ τ.1) a * archM V (C.θ τ.1) u := by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  show Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) (a * u)) * C.x₀ τ.1 =
    _ * (Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) u) * C.x₀ τ.1)
  rw [h, ← Matrix.mul_assoc]
  congr 1
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]


end Comp

section Abstract


end Abstract

section Classes

open GlobalTheory.Mass Formalism.IndefR.Lev Formalism.L2.DIV

def finP (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (GlobalTheory.LevSplit.finE_mem_UA V)






variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}


end Classes

section Local

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem mem_hatL_iff [Module.Finite (𝓞 E) Λ] (z : Fin n → E ⊗[F] 𝔸) :
    z ∈ hatL (F := F) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (z i)) ∈ locL v Λ :=
  mem_latS_adele_iff Λ z


theorem cong_glob [Module.Finite (𝓞 E) Λ] {X : Matrix (Fin n) (Fin n) (E ⊗[F] 𝔸)} {N : ℕ} (hN : N ≠ 0)
    (h : ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ y ∈ locL v Λ, ∃ w ∈ locL v Λ, X.map (prV (E := E) v) *ᵥ y - y = N • w) :
    ∀ z ∈ hatL (F := F) Λ, ∃ w ∈ hatL (F := F) Λ, X *ᵥ z - z = N • w := by
  intro z hz
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN
  let t : E ⊗[F] 𝔸 := (N : E)⁻¹ ⊗ₜ[F] (1 : 𝔸)
  have ht : (N : E ⊗[F] 𝔸) * t = 1 := by
    have : (N : E ⊗[F] 𝔸) = (N : E) ⊗ₜ[F] (1 : 𝔸) := (map_natCast (Algebra.TensorProduct.includeLeftRingHom) N).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hNE, one_mul]
    rfl
  refine ⟨t • (X *ᵥ z - z), (mem_hatL_iff Λ _).2 fun v => ?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := h v _ ((mem_hatL_iff Λ z).1 hz v)
    have ht' : (N : E ⊗[F] v.adicCompletion F) * prV (E := E) v t = 1 := by
      rw [← map_natCast (prV (E := E) v), ← map_mul, ht, map_one]
    have : (fun i => prV (E := E) v ((t • (X *ᵥ z - z)) i)) = w := by
      have h2 := prV_mulVec (E := E) v X z
      funext i
      have e' := congrFun e i
      rw [← h2] at e'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_sub] at e' ⊢
      rw [e', nsmul_eq_mul, ← mul_assoc, mul_comm _ (N : E ⊗[F] v.adicCompletion F), ht', one_mul]
    rwa [this]
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc, ht, one_mul]

theorem exists_nsmul_eq {v : HeightOneSpectrum (𝓞 F)} {b : ℕ} (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {w : Fin n → E ⊗[F] v.adicCompletion F} (hw : w ∈ locL v Λ) : ∃ w' ∈ locL v Λ, w = b • w' := by
  have hval : Valued.v (b : v.adicCompletion F) = 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b : F)
    rw [show ((b : F) : v.adicCompletion F) = (b : v.adicCompletion F) from map_natCast (algebraMap F (v.adicCompletion F)) b,
      show (b : F) = algebraMap (𝓞 F) F ((b : ℕ) : 𝓞 F) from (map_natCast _ b).symm, v.valuation_of_algebraMap] at e
    rw [e]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hb ((v.intValuation_lt_one_iff_mem _).1 h))
  have hne : (b : v.adicCompletion F) ≠ 0 := fun h => by
    rw [h, map_zero] at hval
    exact zero_ne_one hval
  let a : v.adicCompletion F := (b : v.adicCompletion F)⁻¹
  have ha : a ∈ v.adicCompletionIntegers F := by
    show Valued.v a ≤ 1
    rw [map_inv₀, hval, inv_one]
  have hint : (1 : E) ⊗ₜ[F] a ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  refine ⟨((1 : E) ⊗ₜ[F] a) • w, Submodule.smul_mem _ (⟨_, hint⟩ : intV E v) hw, ?_⟩
  funext i
  have hb1 : (b : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] a) = 1 := by
    have : (b : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (b : v.adicCompletion F) :=
      (map_natCast (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) b).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hne]
    rfl
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc, hb1, one_mul]





theorem cong_of_princ {v : HeightOneSpectrum (𝓞 F)} {x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)} {a b : ℕ}
    (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : ∀ y ∈ locL v Λ, ∃ z ∈ locL v Λ, x *ᵥ y - y = (a : E ⊗[F] v.adicCompletion F) • z) :
    ∀ y ∈ locL v Λ, ∃ w ∈ locL v Λ, x *ᵥ y - y = (a * b) • w := by
  intro y hy
  obtain ⟨z, hz, e⟩ := h y hy
  obtain ⟨w, hw, rfl⟩ := exists_nsmul_eq Λ hb hz
  refine ⟨w, hw, ?_⟩
  rw [e, mul_nsmul', Nat.cast_smul_eq_nsmul]

end Local

section LocalLevel

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (Λ : Submodule (𝓞 E) (Fin S.rank → E))

def InLocG (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) : Prop :=
  x ∈ levelVL hc.sig S.gram v Λ ∧ ∀ i : Fin 2, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal → InPrinc hc S v (gp i) Λ x

variable {hc S gp Λ}



end LocalLevel

section Level

open Formalism.L2.Geo.Def Formalism.IndefR.Lev Formalism.L2.DIV
open Formalism.UG (levelVL levelAfL prV bc stabGL)

variable (D)

variable {D}

def HatCong (V : HSp D) (N : ℕ) (y : GA D V) : Prop :=
  ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latC V), ∃ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latC V),
    (finE V y).1 *ᵥ z - z = N • w


instance finite_latC (V : HSp D) : Module.Finite (𝓞 D.host.E) (latC V) :=
  Module.Finite.iff_fg.2 (latHat_eq_hat_and_gram D V).2.2.1


end Level

end GlobalTheory.LevPin
