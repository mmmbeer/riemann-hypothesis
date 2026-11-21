import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FamGerm

structure Pt1 (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (F : Type) [Field F] [Algebra (FractionRing V) F] where
  ϖ : V
  hϖ : Irreducible ϖ
  complete : IsAdicComplete (maximalIdeal V) V
  t : SAB H (Sp V)
  P : PELUnif (maximalIdeal V) t
  tors : P.TorsionIso
  Q : P.D.toPre.X → ℤ
  hQ : QForm.IsQ P.D.toPre ϖ Q
  v : AddValuation F (WithTop ℚ)
  hv : ValOver ϖ F v
  d : ℕ
  x : JetSer.Fam t.G (Fin d)
  hx : Chart.IsUnivChart t.G d x
  j : P.U.LG.L.ι
  hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ P.U.LG.L.U j
  u : letI := H.starRing; ∀ a : 𝓞 E, LB.Gen (LB.LinComb P.U.LG.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε)
  hu : letI := H.starRing; ∀ a, JetSer.IsNormRos P.U.LG.L _ _ (u a)
  B : letI := H.starRing; FB V d (𝓞 E)
  hB : letI := H.starRing; JetSer.IsFBOf P.U.LG P.U.cubG t.act u x j B
  ρ : LB.Gen (LB.LinComb P.U.LG.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)
  hρ : ρ.IsGen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

def Pt1.Germ (q : ℕ) (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d) : Prop :=
  ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 y.P.U.LG.L q) (fi : Fin l → ∀ α, y.P.D.toPre.SecB q α) (g : Fin l → PS V 1 y.d) (r : PS V 1 y.d),
    (∀ i e, y.P.U.ExpandsAt e q (σ i) (fi i)) ∧
    (∀ α, GeneratorPullback.SecLin y.P.D.toPre.P.L (DegPre.famφ y.P.D.toPre F α) (DegPre.famε q) (s.s α) (y.P.D.toPre.famφB α) (DegPre.famε q)
      (fun i => fi i α) (DegPre.prB y.P.D.toPre F).left (fun i => scal (fst (TF (R := V) F) y.P.D.toPre.P.A).left (c i))) ∧
    JetSer.IsSer1 y.x _ (y.ρ.s (fun _ => y.j)).val r ∧
    (∀ i, ∃ S, JetSer.IsSer1 y.x _ ((σ i).f (fun _ => y.j)) S ∧ g i * r ^ q = S) ∧
    f = ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map (TWO.algVF (V := V) (F := F)) (g i)

def Pt1.Red (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) : Prop :=
  0 ≤ Cc ∧ 0 ≤ M₀ ∧ (∀ i, (y.Q (b i) : ℝ) ≤ Cc) ∧ ∀ i z, |(QForm.bOf y.P.D.toPre y.Q (b i) z : ℝ)| ≤ M₀ * y.Q z

def Pt1.Transl (q : ℕ) (c : 𝓞 E) (s h : Fam y.P.D.toPre F q) : Prop :=
  ∃ (p : QkPt y.P.D.toPre F q) (x : TFK (R := V) F ⟶ y.P.A.A)
    (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F) (t' : Fam y.P.D.toPre F q),
    y.P.ToA F q p x ∧ (letI := H.starRing; x ≫ y.P.oA.act c = 1) ∧ w.IsGen ∧ ζ ≠ 0 ∧ FinOrd y.P.D F q p w ζ ∧
      PhiRel y.P.D.toPre F q p w s t' ∧ Fam.IsSmul y.P.D.toPre F ζ t' h

def Pt1.CharAt (a : 𝓞 E) (p : ℕ) {Λ : Type} (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) : Prop :=
  letI := H.starRing
  ∃ (κ : (TFK (R := V) F ⟶ y.P.A.A) → Fˣ) (Z : Over (Spec (CommRingCat.of (TWO.Ov y.v)))) (jZ : Z.left ⟶ y.t.G.left) (k : Γ(Z.left, ⊤)),
    (∀ z z', z ≫ y.P.oA.act a = 1 → z' ≫ y.P.oA.act a = 1 → κ (z * z') = κ z * κ z') ∧
    IsFinite Z.hom ∧ Flat Z.hom ∧ IsReduced (Pdiv.specO (TWO.Ov y.v) F ⊗ Z).left ∧
    jZ ≫ y.t.G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (TWO.fO y.v y.hϖ y.hv)) ∧
    jZ ≫ (y.t.act.act a).left = jZ ≫ (1 : y.t.G ⟶ y.t.G).left ∧
    (∀ (c : Pdiv.specO (TWO.Ov y.v) F ⟶ Z) (z : TFK (R := V) F ⟶ y.P.A.A),
      (z ≫ y.P.U.gen.inv).left ≫ pullback.fst y.t.G.hom (jK V) = c.left ≫ jZ → JetSer.fnVal c.left ⊤ k = (κ z : F)) ∧
    ∀ l, ∃ (w : Pdiv.specO (TWO.Ov y.v) (DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})) ⟶ Z)
      (φ : Chart.JetR V (Fin y.d) 1 →+* DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})),
      (∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (Ideal.Quotient.mk _ (e l i))) ∧
      w.left ≫ jZ = Spec.map (CommRingCat.ofHom φ) ≫ (y.x 1).left ∧
      JetSer.fnVal w.left ⊤ k = 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk _ (yy l))

def Pt1.colVal [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}
    (P : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) : F :=
  letI := H.starRing
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, y.B.nabVal F h H.w0 q (f b) e (MvPolynomial.monomial (colM mo b) 1)

def minorsP (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n)
    (m : ∀ τ, Fin (r τ) → ℕ) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
  ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s

def GermExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∃ gm : Fam y.P.D.toPre F q →ₗ[F] PS F 1 y.d, ∀ s f, y.Germ q s f ↔ f = gm s

def GermValSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∀ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), y.Germ q s f → (∀ r : ℚ, (∀ χ, VGe y.P.D F y.v q χ (s.s χ) r) → ∀ mo, ((r : ℚ) : WithTop ℚ) ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ (χ : y.P.D.toPre.X) (x : F) (r r' : ℚ), Val0 y.P.D F q χ (s.s χ) x → y.v x = (r : ℚ) → r < r' → (∀ β, β ≠ χ → VGe y.P.D F y.v q β (s.s β) r') → y.v (MvPowerSeries.constantCoeff f) = (r : ℚ)

def JetsSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ q n : ℕ, 4 * n + 4 ≤ q → (n : ℝ) * M₀ < q → ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Cc / q ∧ ∀ g : PS F 1 y.d, (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) → ∃ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), NuGe y.P.D y.Q F y.v q s (-gm) ∧ y.Germ q s f ∧ (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g

def PullGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : 𝓞 E) → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∃ (w : PS V 1 y.d) (κ : Vˣ), FB.toK F w = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0) ∧ ∀ (s : Fam y.P.D.toPre F k) (s' : Fam y.P.D.toPre F (k * N)) (f : PS F 1 y.d), PullAl y.P.D F y.P.oD a k N s s' → y.Germ k s f → y.Germ (k * N) s' (MvPowerSeries.C (algebraMap V F κ) * (ev (n := 1) ![y.B.actK F a] f * FB.toK F w ^ k))

def EigGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (p k : ℕ), p.Prime → 4 ≤ k → a * star a = (p : 𝓞 E) → ∀ (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) (α : Λ → TWO.Ov y.v), (∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F)) → y.CharAt a p e yy → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), Nat.Coprime p k → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∃ (pt : QkPt y.P.D.toPre F (k * p)) (x : TFK (R := V) F ⟶ y.P.A.A), y.P.ToA F (k * p) pt x ∧ x ≫ y.P.oA.act (star a) = 1 ∧ ∀ (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b) (DegPre.lineε (k * p)))), w.IsGen → ∀ (s : Fam y.P.D.toPre F k) (s' t' : Fam y.P.D.toPre F (k * p)) (c : F), PullAl y.P.D F y.P.oD a k p s s' → PhiRel y.P.D.toPre F (k * p) pt w s' t' → (∀ χ, VGe y.P.D F y.v (k * p) χ ((c • t').s χ) 0) → ∀ (h : PS F 2 y.d) (ω : PS V 1 y.d), y.B.IsCanonGauge F h → FB.toK F ω = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0) → ∀ f : PS F 1 y.d, y.Germ (k * p) (c • t') (f * FB.toK F ω ^ k) → ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) f - MvPowerSeries.C (yy l : F) * f))

section Basic₂

theorem Pt1.Red.mono {y : Pt1 E H V F} {r : ℕ} {b : Module.Basis (Fin r) ℤ y.P.D.toPre.X} {Cc Cc' M₀ : ℝ}
    (h : y.Red r b Cc M₀) (hC : Cc ≤ Cc') : y.Red r b Cc' M₀ :=
  ⟨h.1.trans hC, h.2.1, fun i => (h.2.2.1 i).trans hC, h.2.2.2⟩

theorem Pt1.Transl.mul {y : Pt1 E H V F} {q : ℕ} {c : 𝓞 E} {s h : Fam y.P.D.toPre F q} (ht : y.Transl q c s h)
    (c' : 𝓞 E) : y.Transl q (c' * c) s h := by
  let _ := H.starRing
  obtain ⟨p, x, w, ζ, t', h₁, h₂, h₃⟩ := ht
  refine ⟨p, x, w, ζ, t', h₁, ?_, h₃⟩
  have := y.P.oA.hom c'
  rw [y.P.oA.map_mul, ← Category.assoc, h₂, MonObj.one_comp]

section ColVal
variable [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}






end ColVal


example (k : Type) [CommRing k] {n : ℕ} (b : Fin n) (m : ℕ) :
    minorsP k (T := Unit) (r := fun _ => 1) (fun _ _ => b) (fun _ _ => m) = MvPolynomial.X (⟨(), 0⟩, b) ^ m := by
  simp [minorsP]

example (k : Type) [CommRing k] :
    minorsP k (T := Unit) (r := fun _ => 2) (n := 2) (fun _ i => i) (fun _ s => s.val) =
      MvPolynomial.X (⟨(), 0⟩, 0) * MvPolynomial.X (⟨(), 1⟩, 1) -
        MvPolynomial.X (⟨(), 0⟩, 1) * MvPolynomial.X (⟨(), 1⟩, 0) := by
  simp [minorsP, Fin.prod_univ_two, Matrix.det_fin_two]

end Basic₂

end GlobalTheory.FamGerm
