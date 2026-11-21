import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev ccH (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingHom

def FundFor (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ, ∀ b ∈ Bor X.Ψ r, cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x0 z') b)


def FreeOn (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) : Prop :=
  ∀ γ ∈ Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ x = rmul x b → γ = 1

def SameUpToScalars (Γ Γ' : Subgroup (GL (Fin r) E)) : Prop :=
  (∀ γ ∈ Γ, ∃ s : Eˣ, ∃ γ' ∈ Γ', (γ' : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)) ∧
  ∀ γ' ∈ Γ', ∃ s : Eˣ, ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ' : Matrix (Fin r) (Fin r) E)

def SameOrbits (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)) : Prop :=
  ∀ x ∈ X.dom, ∀ y ∈ X.dom, (∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)) ↔
    ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)

end defs

def VolOfIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₁ Γ₂ : Subgroup (GL (Fin r) E))
    (x₁ x₂ : Frame X.Ψ r) (F₁ F₂ : Set (V (nd X))),
    Γ₁ ≤ uGrp (ccH E) X.Gm → Γ₂ ≤ uGrp (ccH E) X.Gm → FreeOn X Γ₁ → FreeOn X Γ₂ → EqIdx Γ₁ Γ₂ →
    IsOrth X x₁ → IsOrth X x₂ → FundFor X Γ₁ x₁ F₁ → FundFor X Γ₂ x₂ F₂ → muF X x₁ F₁ = muF X x₂ F₂

def Transport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E)
    (Γ' : Subgroup (GL (Fin r) E)) (x' : Frame X'.Ψ r) (F' : Set (V (nd X'))),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 →
    (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm →
    IsOrth X' x' → FreeOn X' Γ' → FundFor X' Γ' x' F' →
    FreeOn X (conjBy a Γ') ∧ ∃ (x : Frame X.Ψ r) (F : Set (V (nd X))),
      IsOrth X x ∧ FundFor X (conjBy a Γ') x F ∧ muF X x F = muF X' x' F'

def ScalarSwap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)),
    SameUpToScalars Γ Γ' →
    (∀ γ ∈ Γ', (∃ s : E, (γ : Matrix (Fin r) (Fin r) E) = s • (1 : Matrix (Fin r) (Fin r) E)) → γ = 1) →
    FreeOn X Γ → FreeOn X Γ' ∧ ∀ x0 FF, FundFor X Γ x0 FF → FundFor X Γ' x0 FF

def ScalarsOfOrbits : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)),
    Γ ≤ uGrp (ccH E) X.Gm → Γ' ≤ uGrp (ccH E) X.Gm → SameOrbits X Γ Γ' → SameUpToScalars Γ Γ'

def LevelFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)), IsLat Λ → IsUnit J.det →
    (Neat c 𝔞 → ∀ γ ∈ levelGrp c.toRingHom J Λ 𝔞,
      (∃ s : E, (γ : Matrix (Fin N) (Fin N) E) = s • (1 : Matrix (Fin N) (Fin N) E)) → γ = 1) ∧
    ∀ (J₀ : Matrix (Fin N) (Fin N) E) (a : GL (Fin N) E) (Λ₀ : Submodule (𝓞 E) (Fin N → E)),
      (a : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom = J →
      (∀ x, x ∈ Λ ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ Λ₀) →
      conjBy a (levelGrp c.toRingHom J Λ 𝔞) = levelGrp c.toRingHom J₀ Λ₀ 𝔞

def EqVolFD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E)
    (L L' aL' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 →
    (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm →
    (∃ e : Fin r → E, e ≠ 0 ∧ herm X.Gm e e = 0) →
    IsLat L → IsLat L' → IsLat aL' → (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') →
    AdGenus (IsCMField.complexConj E) X.Gm L aL' → 𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'



end PositivityTheory.EqVol
end
end

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SDHerm (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)

def SDTrace (ξ : E) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧ ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y

def SDPair (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (G' : Matrix (Fin r) (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (SDHerm G L ∧ SDHerm G' L') ∨ ∃ ξ : E, ξ ≠ 0 ∧ cc ξ = -ξ ∧ SDTrace ξ G L ∧ SDTrace ξ G' L'

end defs

def Isotropic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 3 ≤ r → 0 < X.p0 → X.p0 < r →
    ∃ e : Fin r → E, e ≠ 0 ∧ herm X.Gm e e = 0

def DualTransport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E) (a : GL (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)),
    (a : Matrix (Fin r) (Fin r) E)ᵀ * G * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = G' → IsLat L' →
    ∃ aL' : Submodule (𝓞 E) (Fin r → E), IsLat aL' ∧ (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') ∧
      (SDHerm G' L' → SDHerm G aL') ∧ ∀ ξ, SDTrace ξ G' L' → SDTrace ξ G aL'

def LocalToAdelic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L L' : Submodule (𝓞 E) (Fin r → E)), IsLat L → IsLat L' →
    (∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v),
      (∀ v, GlobalTheory.SelfDualGenus.IsLocalIsometry v G L' G L (γ v)) ∧ {v | γ v ≠ 1}.Finite) →
    AdGenus (IsCMField.complexConj E) G L L'

def EqVolSD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (r : ℕ) (X X' : Data E r) (L L' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 → 3 ≤ r → 0 < X.p0 → X.p0 < r → IsLat L → IsLat L' → SDPair X.Gm L X'.Gm L' →
    𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'


end PositivityTheory.EqVol
end
end

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

def LevelIdeal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔪 𝔪' : Ideal (𝓞 E)) (M A : ℕ)
    (γ : Matrix (Fin N) (Fin N) E), IsLat Λ → 0 < M → 𝔪' * 𝔪 = Ideal.span {(M : 𝓞 E)} → (∀ x ∈ Λ, γ *ᵥ x ∈ Λ) →
    (((∀ x ∈ 𝔪 • Λ, ∃ e ∈ Λ, γ *ᵥ x = x + M • e) ∧ ∀ x ∈ Λ, ∃ e ∈ Λ, γ *ᵥ x = x + A • e) ↔
      ∀ x ∈ Λ, γ *ᵥ x - x ∈ (𝔪' ⊓ Ideal.span {(A : 𝓞 E)}) • Λ)

def EqVolTr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (r : ℕ) (X X' : Data E r) (L L' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)) (ξ ξ' : E),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 → 3 ≤ r → 0 < X.p0 → X.p0 < r → IsLat L → IsLat L' →
    cc ξ = -ξ → cc ξ' = -ξ' → (∀ τ ∈ X.Ψ, 0 < (τ ξ).im * (τ ξ').im) → SDTrace ξ X.Gm L → SDTrace ξ' X'.Gm L' →
    𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'

theorem neat_mono {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {c : E ≃ₐ[F] E}
    {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) (hb : Neat c 𝔟) : Neat c 𝔞 := fun z h1 h2 => hb z h1 (h h2)

end PositivityTheory.EqVol
end
end

section
noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree

def levIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) : Ideal (𝓞 E) :=
  l.Mb ⊓ Ideal.span {(l.A : 𝓞 E)}

def levOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) {r : ℕ} (X : Data E r) :
    Subgroup (GL (Fin r) E) :=
  levelGrp (ccH E) X.Gm X.Λ (levIdeal l)

def UnfLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, SDTrace (U.X k).ξ0 (U.X k).Gm (U.X k).Λ

def UnfSign : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 0 < r → ∀ k, ∀ τ ∈ (U.X k).Ψ, (τ (U.X k).ξ0).im < 0

def UnfLevelIn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, ∀ γ ∈ levOf l (U.X k), ∀ x ∈ (U.X k).dom,
      ∃ γ' ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b

def UnfBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
      ∃ δ ∈ levOf l (U.X k), ∃ b : Frame (U.X k).Ψ r, lact γ x = rmul (lact δ x) b ∧
        ∀ τ (a a' : Fin r), (a' : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (a : ℕ) → b τ a a' = 0

def ScalarOfBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₀ : Subgroup (GL (Fin r) E))
    (γ : GL (Fin r) E), 0 < X.p0 → X.p0 < r →
    (∀ x ∈ X.dom, ∃ δ ∈ Γ₀, ∃ b : Frame X.Ψ r, lact γ x = rmul (lact δ x) b ∧
      ∀ τ (a a' : Fin r), (a' : ℕ) < X.p0 → X.p0 ≤ (a : ℕ) → b τ a a' = 0) →
    ∃ s : Eˣ, ∃ δ ∈ Γ₀, (δ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)

def OrbitsOfIncl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₀ : Subgroup (GL (Fin r) E)),
    (∀ γ ∈ X.Γ, ∃ s : Eˣ, ∃ δ ∈ Γ₀, (δ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)) →
    (∀ γ ∈ Γ₀, ∀ x ∈ X.dom, ∃ γ' ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ x = rmul (lact γ' x) b) →
    SameOrbits X X.Γ Γ₀

def EqVolUnf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 3 ≤ r → 0 < Dw.p → 0 < Dw.q →
    ∀ (k k' : U.Comp) (x : Frame (U.X k).Ψ r) (x' : Frame (U.X k').Ψ r) (FF : Set (V (nd (U.X k))))
      (FF' : Set (V (nd (U.X k')))), IsOrth (U.X k) x → IsOrth (U.X k') x' → IsFundSet (U.X k) x FF →
      IsFundSet (U.X k') x' FF' → muF (U.X k) x FF = muF (U.X k') x' FF'

theorem inf_span_ne_bot {R : Type} [CommRing R] [IsDomain R] {I J : Ideal R} {m a : R} (h : I * J = Ideal.span {m})
    (hm : m ≠ 0) (ha : a ≠ 0) : I ⊓ Ideal.span {a} ≠ ⊥ := by
  have h1 : m ∈ I * J := h ▸ Ideal.mem_span_singleton_self m
  have h2 : m * a ∈ I ⊓ Ideal.span {a} :=
    ⟨I.mul_mem_right _ (Ideal.mul_le_inf h1).1, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩
  intro h0
  rw [h0] at h2
  exact mul_ne_zero hm ha h2


end PositivityTheory.EqVol
end
end
