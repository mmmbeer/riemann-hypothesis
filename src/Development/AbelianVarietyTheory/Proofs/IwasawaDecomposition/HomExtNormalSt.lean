import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Branches

variable {X X' : Scheme.{0}}

def pre (π : X' ⟶ X) (Z : Closeds X) : Closeds X' := Z.preimage π.continuous

@[simp] theorem mem_pre {π : X' ⟶ X} {Z : Closeds X} {x : X'} : x ∈ pre π Z ↔ π x ∈ Z := Iff.rfl

theorem pre_comp {X'' : Scheme.{0}} (π' : X'' ⟶ X') (π : X' ⟶ X) (Z : Closeds X) :
    pre (π' ≫ π) Z = pre π' (pre π Z) := by
  first
  | rfl
  | (ext x; simp [mem_pre])

abbrev van (Z : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x

def tr {x y : X} (h : x = y) : X.presheaf.stalk x →+* X.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom

@[simp] theorem tr_rfl (x : X) (a : X.presheaf.stalk x) : tr (rfl : x = x) a = a := by
  simp [tr, TopCat.Presheaf.stalkCongr]

def IsRsp {A : Type} [CommRing A] [IsLocalRing A] {ι : Type} [Fintype ι] (f : ι → A) : Prop :=
  IsRegularLocalRing A ∧ Ideal.span (Set.range f) = maximalIdeal A ∧ (Fintype.card ι : WithBot ℕ∞) = ringKrullDim A

def BrAt (B : Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x) : Prop :=
  IsRsp f ∧ van B x = Ideal.span {∏ j, f (Sum.inl j)}

def HasBr (B : Closeds X) : Prop := ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x), BrAt B x f

def Unimod {m m' : ℕ} (a : Fin m → Fin m' → ℕ) : Prop :=
  ∀ (L : Type) [AddCommGroup L] (γ : Fin m → L), IsPartOfBasis γ → IsPartOfBasis (fun i => ∑ j, a j i • γ j)

def IsModif (π : X' ⟶ X) (B : Closeds X) : Prop :=
  LocallyOfFiniteType π ∧ IsIso (π ∣_ B.compl) ∧
    ∀ (x' : X') (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk (π x')), BrAt B (π x') f →
      ∃ (m' d' : ℕ) (f' : Fin m' ⊕ Fin d' → X'.presheaf.stalk x') (a : Fin m → Fin m' → ℕ),
        BrAt (pre π B) x' f' ∧ Unimod a ∧
          ∀ j, Associated ((π.stalkMap x').hom (f (Sum.inl j))) (∏ i, f' (Sum.inl i) ^ a j i)

def ColAt (B : Closeds X) {ι : Type} (E : ι → Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x)
    (c : Fin m → ι) : Prop :=
  BrAt B x f ∧ ∀ i, van (E i) x = Ideal.span {∏ j ∈ Finset.univ.filter (fun j => c j = i), f (Sum.inl j)}

def IsStrict (B : Closeds X) {ι : Type} (E : ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → ι), ColAt B E x f c ∧ Function.Injective c

def ExtAt {U Y : Scheme.{0}} (j : U ⟶ X) (g : U ⟶ Y) (π : X' ⟶ X) (x' : X') : Prop :=
  ∃ (V : X'.Opens) (h : V.toScheme ⟶ Y), x' ∈ V ∧
    ∀ (T : Scheme.{0}) (a : T ⟶ V.toScheme) (u : T ⟶ U), a ≫ V.ι ≫ π = u ≫ j → a ≫ h = u ≫ g

def IsChart (B : Closeds X) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ X) : Prop :=
  IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
  (van B (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} ∧
  ∀ p : Sp (ChartRing k m d), ξ p ∈ B ↔ ∏ i, bdParam k m d i ∈ p.asIdeal

end Branches

section Pairs

variable {K F : Type} [Field K] [Field F] {XK X X'K X' : Scheme.{0}}

def IsPair (k : K →+* F) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK) (BK : Closeds XK) : Prop :=
  CharZero K ∧ k.Finite ∧ IsProjOver sK ∧ IsPullback e s sK (spMap k) ∧ HasBr (pre e BK)

def IsMod (k : K →+* F) (sK : XK ⟶ Sp K) (s : X ⟶ Sp F) (e : X ⟶ XK) (BK : Closeds XK) (πK : X'K ⟶ XK) (π : X' ⟶ X)
    (e' : X' ⟶ X'K) : Prop :=
  IsPair k (πK ≫ sK) (π ≫ s) e' (pre πK BK) ∧ e' ≫ πK = π ≫ e ∧ IsIso (πK ∣_ BK.compl) ∧ IsModif π (pre e BK)

theorem IsMod.pre_eq {k : K →+* F} {sK : XK ⟶ Sp K} {s : X ⟶ Sp F} {e : X ⟶ XK} {BK : Closeds XK} {πK : X'K ⟶ XK}
    {π : X' ⟶ X} {e' : X' ⟶ X'K} (h : IsMod k sK s e BK πK π e') (Z : Closeds XK) :
    pre e' (pre πK Z) = pre π (pre e Z) := by
  rw [← pre_comp, h.2.1, pre_comp]

end Pairs

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsCN (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ CharZero R

def FineData {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) : Prop :=
  ∀ y : D.X, ∃ (μ₀ : D.X) (r : R), PsiCoord D (y + N • μ₀) r ∧ ∀ μ : D.X, ∃ s : R, PsiCoord D (y + N • μ) (r * s)

abbrev toBase {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp R)) :=
  Over.homMk (spMap φ) (Category.comp_id _)

def IndepAlong {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) : Prop :=
  ∀ c c' s, Lin G L N h b c s → Lin G L N h b c' s → c = c'

def FreeSec {R : Type} [CommRing R] (t : SAB H (Sp R)) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ φ : R →+* W, Function.Injective φ →
      BasisAlong t.G t.PP.L N (toBase φ) b

def AmpAt {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (m : ℕ) : Prop :=
  ∃ (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π ∧ Surjective π ∧
    Nonempty (AmpFrames t.G t.PP.L (m ^ 2))

def IsCover {O F I : Type} [CommRing O] [Field F] (β : O →+* F) (R : I → Type) [∀ i, CommRing (R i)] (a : I → O)
    (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) : Prop :=
  IsDedFrac β ∧ (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) ∧
    Ideal.span (Set.range a) = ⊤

end Sections

section Steps

def VanSt : Prop :=
  (∀ (X : Scheme.{0}) (Z : Closeds X) (x : X), (van Z x).IsRadical ∧ (x ∉ Z → van Z x = ⊤) ∧
    ∀ p : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x p ∈ Z ↔ van Z x ≤ p.asIdeal) ∧
  (∀ (X : Scheme.{0}) (Z Z' : Closeds X) (x : X), van (Z ⊓ Z') x = (van Z x ⊔ van Z' x).radical) ∧
  (∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (Z : Closeds X) (x' : X'),
    van (pre π Z) x' = ((van Z (π x')).map (π.stalkMap x').hom).radical) ∧
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X'),
    FinalTheorems.stalkId (J.comap π) x' = (FinalTheorems.stalkId J (π x')).map (π.stalkMap x').hom

def BlowProjSt : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (X : Scheme.{0}) (s : X ⟶ Sp O) (J : X.IdealSheafData), IsProjOver s →
    ∃ (X' : Scheme.{0}) (π : X' ⟶ X), FinalTheorems.Blowup π J ∧ IsProjOver (π ≫ s)

def BlowBCSt : Prop :=
  (∀ (X X' Y Y' : Scheme.{0}) (π : X' ⟶ X) (g : Y ⟶ X) (π' : Y' ⟶ Y) (g' : Y' ⟶ X') (J : X.IdealSheafData),
    FinalTheorems.Blowup π J → Flat g → IsPullback g' π' π g → FinalTheorems.Blowup π' (J.comap g)) ∧
  (∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData), FinalTheorems.Blowup π J → FinalTheorems.EffCartier J → IsIso π) ∧
  ∀ (X X' : Scheme.{0}) (π : X' ⟶ X) (J : X.IdealSheafData) (U : X.Opens), FinalTheorems.Blowup π J →
    Disjoint (U : Set X) (J.support : Set X) → IsIso (π ∣_ U)

def GlueSt : Prop :=
  ∀ (X X' U Y : Scheme.{0}) (π : X' ⟶ X) (j : U ⟶ X) (g : U ⟶ Y), IsReduced X' → IsOpenImmersion j →
    Dense (π ⁻¹' Set.range j) → Y.IsSeparated → (∀ x', ExtAt j g π x') →
    ∃ h : X' ⟶ Y, ∀ (T : Scheme.{0}) (a : T ⟶ X') (u : T ⟶ U), a ≫ π = u ≫ j → a ≫ h = u ≫ g

def ExtAtSt : Prop :=
  ∀ (X X' U Y S : Scheme.{0}) [IsLocallyNoetherian X'] (π : X' ⟶ X) (j : U ⟶ X) (g : U ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X') (y : Sp (FractionRing R) ⟶ U) (χ : Sp R ⟶ Y),
    IsOpenImmersion j → IsSeparated sY → LocallyOfFiniteType sY → g ≫ sY = j ≫ sX →
    (Scheme.stalkClosedPointTo ξ).hom.Flat → y ≫ j = jK R ≫ ξ ≫ π → jK R ≫ χ = y ≫ g → χ ≫ sY = ξ ≫ π ≫ sX →
    ExtAt j g π (ξ (closedPoint R))

def HomExtNormalSt : Prop :=
  ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
    ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f

def SabExtNormalSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X),
    Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom →
      ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ

def CmpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β)
    (Z : Model Xo c β') (ρ : gen Z ⟶ gen Y), Z.jQ ≫ ρ = Y.jQ → Geo.Tor.IsNormalScheme (gen Z) →
    ∃ (t₀ : SAB H (gen Z)) (n₁ : SABMap t₀ Z.t (genι Z)) (n₂ : SABMap t₀ Y.t (ρ ≫ genι Y)),
      ∀ (T : Scheme.{0}) (g : T ⟶ t₀.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ t₀.G.hom = g₁ ≫ Z.oF.t.G.hom ≫ Z.jQ → g ≫ n₁.φ = g₁ ≫ Z.m.φ →
        g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ n₂.φ = g₂ ≫ Y.m.φ

def DescSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.Descends →
    ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (e : gen Y ⟶ XK) (BK : Closeds XK),
      IsPullback e (genStr Y) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧ genBd Y = pre e BK ∧
      ∀ (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (ρ : gen Z ⟶ gen Y) (X'K : Scheme.{0})
        (πK : X'K ⟶ XK) (e' : gen Z ⟶ X'K), Z.jQ ≫ ρ = Y.jQ → Geo.Tor.IsNormalScheme (gen Z) →
        IsPullback e' (genStr Z) (πK ≫ sK) (spMap (IntermediateField.inclusion c.le).toRingHom) → e' ≫ πK = ρ ≫ e →
        IsIso (πK ∣_ BK.compl) → Z.Descends

def DomTransSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' O'' : Type) [CommRing O] [CommRing O'] [CommRing O''] (β : O →+* c.F) (β' : O' →+* c.F)
    (β'' : O'' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (Y'' : Model Xo c β'') (b : O →+* O') (b' : O' →+* O''),
    β''.comp b' = β' → β'.comp b = β → Dominates Y Y' b → Dominates Y' Y'' b' → Dominates Y Y'' (b'.comp b)

def CoverSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ Y : LocFam Xo,
      (∀ p W hp hW, N2 (Y p W hp hW) ∧ ∀ i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3 ∧ (Y p W hp hW i).N4) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p),
        ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i)
          (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model (Xo l) c (ω i)),
          IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧ (∀ i, Amp (C i)) ∧
          ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b₀ : 𝓞 c.F →+* c.V W),
            (∀ x, ((b₀ x : c.V W) : c.F) = (x : c.F)) →
            ∃ (i : I) (b' : R i →+* c.V W), b'.comp (b i) = b₀ ∧ (c.V W).subtype.comp b' = ω i ∧
              Dominates (C i) (Y p W hp hW ⟨l, c, hg p hp⟩) b'

def PullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsCN R' → Function.Injective φ → IsLocalHom φ → P.TorsionIso →
    ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (P' : PELUnif (maximalIdeal R') t')
      (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X), P'.TorsionIso ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)

def FreeClosedSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : ℕ), IsCN R → 1 ≤ N → FineData P.D.toPre N →
    ∃ (n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
      BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b ∧ IndepAlong t.G t.PP.L N (toBase (residue R)) b

def IndepSpreadSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsLocalRing R]
    (t : SAB H (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
    IndepAlong t.G t.PP.L N (toBase (residue R)) b →
    ∀ (k : Type) [Field k] (φ : R →+* k), IndepAlong t.G t.PP.L N (toBase φ) b

def FreeTraitSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (_ : PELUnif (maximalIdeal R) t) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))),
    BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b →
    (∀ (k : Type) [Field k] (φ : R →+* k), IndepAlong t.G t.PP.L N (toBase φ) b) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ φ : R →+* W, Function.Injective φ →
      BasisAlong t.G t.PP.L N (toBase φ) b

def FreeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : ℕ), IsCN R → 1 ≤ N → FineData P.D.toPre N → FreeSec t N

theorem freeSt_of (h₁ : FreeClosedSt) (h₂ : IndepSpreadSt) (h₃ : FreeTraitSt) : FreeSt := by
  intro E _ _ _ H R _ _ _ t P N hR hN hF
  obtain ⟨n, b, hb, hi⟩ := h₁ E H R t P N hR hN hF
  refine ⟨n, b, ?_⟩
  intro W _ _ _ hW φ hφ
  exact h₃ E H R t P N n b hb (fun k _ ψ => h₂ E H R t N n b hi k ψ) W hW φ hφ

def ExtendSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (C : Model Xo c β)
    (Y : Model Xo c β') (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R))
    (_ : SABMap t Y.t ξ) (y : Sp (FractionRing R) ⟶ Xo.XF c) (b : O →+* R) (m : ℕ), IsCN R → y ≫ Y.j = jK R ≫ ξ →
    y ≫ C.j ≫ C.s = jK R ≫ spMap b → AmpAt C m → FreeSec t 1 → FreeSec t (m ^ 2) →
    ∃ χ : Sp R ⟶ C.X, jK R ≫ χ = y ≫ C.j

end Steps

end GlobalTheory.TorRef
