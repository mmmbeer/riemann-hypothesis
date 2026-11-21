import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Desc

def RegWt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) : Prop :=
  ∀ v : InfinitePlace E, ∃ (φ : E →+* ℂ) (lam : DomWeight n), InfinitePlace.mk φ = v ∧ StrictAnti lam.w ∧ π.HasInfChar φ (infOfWeight lam)

def DescUse : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → RegWt π → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU σ w) ∧
        ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
          ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
            IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ GlobalTheory.LFun.HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

structure EigVec {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : (Af F)ˣ →* ℂˣ) (m : HeightOneSpectrum (𝓞 F) → Fin 2 → ℤ)
    (mu : HeightOneSpectrum (𝓞 F) → ℂ) (π : TR.CuspSub F 2) (x : π.V) : Prop where
  ne : x ≠ 0
  eig : ∀ w, x ∈ Hi.fixd (π.locRep w) (K1 w (c w)) ∧ Uop w (π.locRep w) (c w) x = mu w • x
  cen : ∀ z, π.finPart (Matrix.GeneralLinearGroup.scalar (Fin 2) z) x = (ω z : ℂ) • x
  inf : ∀ w, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ τ : F →+* Qbar l, EmbAt w τ →
    π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf (m w))

end UpperTheory.V.Z.Desc
