import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitaryStatement
import Formalism.PadicSubsetSums.StableGradedCounts.DegreeOneSplit

section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.DzCong

def permRep (G X : Type) [Group G] [MulAction G X] : Representation ℂ G (X → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun x => g⁻¹ • x
  map_one' := by ext f x; simp [LinearMap.funLeft_apply]
  map_mul' g h := by ext f x; simp [LinearMap.funLeft_apply, mul_smul]

def Free (G X : Type) [Group G] [MulAction G X] : Prop := ∀ (g : G) (x : X), g • x = x → g = 1

structure Fam (G : Type) {X I : Type} [Group G] [MulAction G X] [Fintype X] (T : I → Matrix X X ℤ) : Prop where
  comm : ∀ i j, T i * T j = T j * T i
  equi : ∀ i (g : G) x y, T i (g • x) (g • y) = T i x y

def Eig {X I : Type} [Fintype X] (T : I → Matrix X X ℤ) (θ : I → ℂ) : Submodule ℂ (X → ℂ) where
  carrier := {f | ∀ i, ((T i).map (Int.cast : ℤ → ℂ)).mulVec f = θ i • f}
  add_mem' := fun {f g} hf hg i => by rw [Matrix.mulVec_add, hf i, hg i, smul_add]
  zero_mem' := fun i => by simp
  smul_mem' := fun c f hf i => by rw [Matrix.mulVec_smul, hf i, smul_comm]

def GenEig {F X I : Type} [Field F] [Fintype X] [DecidableEq X] (T : I → Matrix X X F) (θ : I → F) : Submodule F (X → F) :=
  ⨅ i, Module.End.maxGenEigenspace (Matrix.toLin' (T i)) (θ i)

open Classical in

def StableSubspaceMobius : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype (Submodule K V)],
    ∃ μ : Module.End K V → Submodule K V → ℤ,
      (∀ g, μ g ⊥ = 1) ∧
      (∀ g W, W ≠ ⊥ → W.map g ≤ W →
        ∑ W' ∈ Finset.univ.filter (fun W' : Submodule K V => W' ≤ W ∧ W'.map g ≤ W'), μ g W' = 0) ∧
      (∀ g g' W, W.map g ≤ W → (∀ v ∈ W, g v = g' v) → μ g W = μ g' W) ∧
      (∀ u, u ≠ 1 → IsNilpotent (u - 1) → μ u ⊤ = 0) ∧
      μ 1 ⊤ ≠ 0

end PositivityTheory.Rg.DzCong

end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.UnitaryBC GlobalTheory.CuspRep
open PositivityTheory.Rg.DzCount (FinCusp IsTypeMap Fwd)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCong

structure In : Prop where
  llc : GlobalTheory.Published.LocalLanglandsExists
  conv : GlobalTheory.Published.LocalConverseGL
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  multi : GlobalTheory.Published.LanglandsMultisegments
  cos : GlobalTheory.Published.StandardCosocleGL
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  geo : GlobalTheory.Published.GeometricLemma
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  bcs : GlobalTheory.BcSpeh.BcSpeh
  gal : GlobalTheory.Published.PolarizedGaloisRepPublished
  gk : GlobalTheory.Published.GelfandKazhdanDual

def Core : Prop :=
  ∀ (K X I : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) [MulAction (GL (Fin n) K) X] [Fintype X]
    (T : I → Matrix X X ℤ), 2 ≤ n → Free (GL (Fin n) K) X → Fam (GL (Fin n) K) T → ∀ W : (I → ℂ) → Prop,
    (∀ (l : ℕ) [Fact l.Prime], l ≠ p → ∃ ι : Qbar l ≃+* ℂ, ∀ θ θ', Eig T θ ≠ ⊥ → Eig T θ' ≠ ⊥ →
      (∀ i, ‖ι.symm (θ i) - ι.symm (θ' i)‖ < 1) → W θ → W θ') →
    (∀ θ, W θ → ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad K e ≠ ⊥ →
      ∀ f ∈ Eig T θ, (∀ u ∈ unipRad K e, permRep (GL (Fin n) K) X u f = f) → f = 0) →
    ∀ θ, Eig T θ ≠ ⊥ → ¬ W θ

section Glob

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Ix (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {u : HeightOneSpectrum (𝓞 E) // IsSplitAt u ∧ u ∉ S} × Fin (n + 1)

def hk (u : HeightOneSpectrum (𝓞 E)) (k : ℕ) (φ : UA E n → ℂ) : UA E n → ℂ :=
  GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n u).subtype) ((GlobalTheory.LFun.KGL u n).comap ((cLoc u).comp (locU n u).subtype))
    (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E u) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k))
      ((cLoc u).comp (locU n u).subtype x)) φ

def SatSys (S : Set (HeightOneSpectrum (𝓞 E))) (π : Submodule ℂ (UA E n → ℂ)) (θ : Ix E n S → ℂ) : Prop :=
  ∀ (u : HeightOneSpectrum (𝓞 E)) (hu : IsSplitAt u ∧ u ∉ S), IsUnramU π u ∧
    ∃ (σ : SmIrr (GL (Fin n) (u.adicCompletion E))) (B : Multiset ℂˣ),
      IsCompAlong π (locU n u) ((cLoc u).comp (locU n u).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL u σ.ρ B ∧
      ∀ k : Fin (n + 1), θ (⟨u, hu⟩, k) = GlobalTheory.LFun.satEig (Formalism.UG.qV E u) n B k

end Glob

def Pack : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ), 1 ≤ n → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (_ : MulAction (GL (Fin n) 𝓀[w.adicCompletion E]) X)
      (S : Set (HeightOneSpectrum (𝓞 E))) (T : Ix E n S → Matrix X X ℤ),
      S.Finite ∧ Free (GL (Fin n) 𝓀[w.adicCompletion E]) X ∧ Fam (GL (Fin n) 𝓀[w.adicCompletion E]) T ∧
      ∀ θ, ∀ f ∈ Eig T θ, f ≠ 0 → ∃ (π : Submodule ℂ (UA E n → ℂ)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
        (q : (X → ℂ) →ₗ[ℂ] σ.V), IsAutRepU π ∧ SatSys S π θ ∧
        IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ q f ≠ 0 ∧
        ∀ (g : KO (w.adicCompletion E) (Fin n)) f', q (permRep _ X (redK (w.adicCompletion E) (Fin n) g) f') =
          σ.ρ (g : GL (Fin n) (w.adicCompletion E)) (q f')

def Cong {l : ℕ} [Fact l.Prime] (P Q : (Qbar l)[X]) : Prop := ∀ i, ‖P.coeff i - Q.coeff i‖ < 1

end PositivityTheory.Rg.DzCong

end
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.DzCong.CongruenceClosure

theorem isSplitAt_of_deg_one {E : Type} [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 E))
    (hf : v.asIdeal.inertiaDeg ℤ = 1) (he : v.asIdeal.ramificationIdx ℤ = 1) : IsSplitAt v := by
  classical
  have := v.isPrime
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have he' : v.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal
    rw [he] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hc := Formalism.IrreducibleCountingLemmas.Z.degree_one_split (maximalRealSubfield E) E h2 v.asIdeal v.ne_bot hf he'
  obtain ⟨P, Q, hne, hs⟩ := Set.ncard_eq_two.mp hc
  have hX : ∃ X ∈ (v.asIdeal.under (𝓞 (maximalRealSubfield E))).primesOver (𝓞 E), X ≠ v.asIdeal := by
    by_cases h : P = v.asIdeal
    · exact ⟨Q, hs ▸ Set.mem_insert_of_mem _ rfl, fun hQ => hne (h.trans hQ.symm)⟩
    · exact ⟨P, hs ▸ Set.mem_insert _ _, h⟩
  obtain ⟨X, hX, hXv⟩ := hX
  have hXb : X ≠ ⊥ := by
    rintro rfl
    have h0 : v.asIdeal.under (𝓞 (maximalRealSubfield E)) = ⊥ := hX.2.over.trans
      (Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ (𝓞 E)))
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h0)
  have := hX.1
  refine ⟨⟨X, hX.1, hXb⟩, fun h => hXv (congrArg HeightOneSpectrum.asIdeal h), ?_⟩
  ext1
  exact hX.2.over.symm

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end PositivityTheory.Rg.DzCong.CongruenceClosure

namespace PositivityTheory.Rg.DzCong

end PositivityTheory.Rg.DzCong

end
end
