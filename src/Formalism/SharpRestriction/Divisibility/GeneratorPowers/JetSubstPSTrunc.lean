import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.PeriodIntegrals.DepthLegendre
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

section Crude

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ)

end Crude

section Germ

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

end Germ

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

def OrdGE (r : ℕ) (g : MvPowerSeries σ k) : Prop := ∀ e : σ →₀ ℕ, e.degree < r → coeff e g = 0

theorem ordGE_zero (r : ℕ) : OrdGE r (0 : MvPowerSeries σ k) := by
  intro e _
  simp

theorem ordGE_add {r : ℕ} {f g : MvPowerSeries σ k} (hf : OrdGE r f) (hg : OrdGE r g) : OrdGE r (f + g) := by
  intro e he
  rw [map_add, hf e he, hg e he, add_zero]

def op {d : ℕ} (a : Fin d → MvPowerSeries σ k) (cd : Fin d → σ) (g : MvPowerSeries σ k) : MvPowerSeries σ k :=
  ∑ j, a j * pderiv k (cd j) g

end Sym

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

structure GoodPair (D D₀ : MvPowerSeries σ k → MvPowerSeries σ k) : Prop where
  ord : ∀ r g, OrdGE (r + 1) g → OrdGE r (D g)
  ord₀ : ∀ r g, OrdGE (r + 1) g → OrdGE r (D₀ g)
  diff : ∀ r g, OrdGE (r + 1) g → OrdGE (r + 1) (D g - D₀ g)
  sub : ∀ f g, D (f - g) = D f - D g

theorem GoodPair.iter {D D₀ : MvPowerSeries σ k → MvPowerSeries σ k} (hP : GoodPair D D₀) (c : ℕ) :
    ∀ r g, OrdGE (c + r) g →
      OrdGE (r + 1) (D^[c] g - D₀^[c] g) ∧ OrdGE r (D^[c] g) ∧ OrdGE r (D₀^[c] g) := by
  induction c with
  | zero =>
    intro r g hg
    rw [zero_add] at hg
    refine ⟨?_, hg, hg⟩
    have e : D^[0] g - D₀^[0] g = 0 := sub_self g
    rw [e]
    exact ordGE_zero _
  | succ n ih =>
    intro r g hg
    obtain ⟨h1, h2, h3⟩ := ih (r + 1) g (by rwa [show n + (r + 1) = n + 1 + r by omega])
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨?_, hP.ord r _ h2, hP.ord₀ r _ h3⟩
    have e : D (D^[n] g) - D₀ (D₀^[n] g) = D (D^[n] g - D₀^[n] g) + (D (D₀^[n] g) - D₀ (D₀^[n] g)) := by
      rw [hP.sub]
      abel
    rw [e]
    exact ordGE_add (hP.ord (r + 1) _ h1) (hP.diff r _ h3)

end Sym

namespace Sym

variable {k : Type} [CommRing k]

private theorem const_subst_lemma {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k)
    (ha : ∀ s, constantCoeff (a s) = 0) (g : MvPowerSeries σ k) :
    constantCoeff (subst a g) = constantCoeff g := by
  have hA : HasSubst a := by
    first
      | exact hasSubst_of_constantCoeff_zero ha
      | exact HasSubst.of_constantCoeff_zero' ha
      | exact hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
      | exact HasSubst.of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
  rw [constantCoeff_subst hA, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact he (Finsupp.ext fun t => by simpa using hc t)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · rw [map_pow, ha s, zero_pow hs]

theorem const_ev {m n d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (g : PS k m d) :
    constantCoeff (ev a g) = constantCoeff g := by
  unfold ev
  exact const_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

theorem const_subst {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ k) (ha : ∀ s, constantCoeff (a s) = 0)
    (g : MvPowerSeries σ k) : constantCoeff (subst a g) = constantCoeff g := by
  exact const_subst_lemma a ha g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res h1 x) = ReciprocityTheory.ChartRestriction.G.Semi.res (h2.trans h1) x := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ← Functor.map_comp_apply])

private lemma pullU_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.pullU f V (ReciprocityTheory.ChartRestriction.G.Semi.res h x) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (fun _ hy => h hy)) (ReciprocityTheory.ChartRestriction.G.Semi.pullU f U x) := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
       Scheme.Hom.naturality]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     exact (Scheme.Hom.naturality_apply f (homOfLE h).op _).symm)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, ← Scheme.Hom.naturality_apply])

private lemma pullU_comp_lemma_3 {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.pullU (g ≫ f) U x = ReciprocityTheory.ChartRestriction.G.Semi.pullU g (f ⁻¹ᵁ U) (ReciprocityTheory.ChartRestriction.G.Semi.pullU f U x) := by
  first
  | rfl
  | (apply Units.ext; rfl)
  | (apply Units.ext; simp [ReciprocityTheory.ChartRestriction.G.Semi.pullU, Scheme.comp_app])

private lemma pullGen_isGen_lemma_4 {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {c : LB.Gen (LB.LinComb L φ ε)} (hc : c.IsGen) {h : Z ⟶ Y} :
    (LB.pullGen L φ ε c h).IsGen := by
  intro i j
  have Pi : ∀ i', LB.wchart L (fun k => h ≫ φ k) i' ≤ h ⁻¹ᵁ LB.wchart L φ i' :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have T : LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j) :=
    le_inf (inf_le_left.trans (Pi i)) (inf_le_right.trans (Pi j))
  have H0 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) inf_le_left) (@id (Γ(Y, LB.wchart L φ i)ˣ) (c.s i)) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) inf_le_right) (@id (Γ(Y, LB.wchart L φ j)ˣ) (c.s j)) := hc i j
  have H := congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res T (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ i ⊓ LB.wchart L φ j) z)) H0
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart L (fun k => h ≫ φ k) i) inf_le_left) (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi i) (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ i) (@id (Γ(Y, LB.wchart L φ i)ˣ) (c.s i)))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ (h ≫ φ k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (h ≫ φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart L (fun k => h ≫ φ k) j) inf_le_right) (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi j) (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j) (@id (Γ(Y, LB.wchart L φ j)ˣ) (c.s j))))
  simp only [map_mul, map_prod, map_zpow, res_res_lemma, pullU_res_lemma_2, pullU_comp_lemma_3] at H ⊢
  exact H

private lemma mulGen_isGen_lemma_5 {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := by
  intro i j
  have Pi : ∀ i', LB.wchart L (Sum.elim φ φ') i' ≤ LB.wchart L φ (i' ∘ Sum.inl) :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have Qi : ∀ i', LB.wchart L (Sum.elim φ φ') i' ≤ LB.wchart L φ' (i' ∘ Sum.inr) :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  have H1 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ LB.wchart L φ (i ∘ Sum.inl)) inf_le_left) (@id (Γ(Y, LB.wchart L φ (i ∘ Sum.inl))ˣ) (t.s (i ∘ Sum.inl))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ (i ∘ Sum.inl) k)) (inf_le_right.trans (LB.wchart_le L _ (j ∘ Sum.inl) k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ k) (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))) (L.g (i (Sum.inl k)) (j (Sum.inl k))))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ LB.wchart L φ (j ∘ Sum.inl)) inf_le_right) (@id (Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ) (t.s (j ∘ Sum.inl))) := ht _ _
  have H2 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ LB.wchart L φ' (i ∘ Sum.inr)) inf_le_left) (@id (Γ(Y, LB.wchart L φ' (i ∘ Sum.inr))ˣ) (t'.s (i ∘ Sum.inr))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ (i ∘ Sum.inr) k)) (inf_le_right.trans (LB.wchart_le L _ (j ∘ Sum.inr) k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ' k) (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))) (L.g (i (Sum.inr k)) (j (Sum.inr k))))) ^ ε' k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ LB.wchart L φ' (j ∘ Sum.inr)) inf_le_right) (@id (Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ) (t'.s (j ∘ Sum.inr))) := ht' _ _
  have T1 : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) :=
    inf_le_inf (Pi i) (Pi j)
  have T2 : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) :=
    inf_le_inf (Qi i) (Qi j)
  have G1 := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res T1) H1
  have G2 := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res T2) H2
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L (Sum.elim φ φ') i) inf_le_left)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi i) (@id (Γ(Y, LB.wchart L φ (i ∘ Sum.inl))ˣ) (t.s (i ∘ Sum.inl))) * ReciprocityTheory.ChartRestriction.G.Semi.res (Qi i) (@id (Γ(Y, LB.wchart L φ' (i ∘ Sum.inr))ˣ) (t'.s (i ∘ Sum.inr)))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ (Sum.elim φ φ' k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (Sum.elim φ φ' k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ (Sum.elim ε ε' k)) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L (Sum.elim φ φ') j) inf_le_right)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi j) (@id (Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ) (t.s (j ∘ Sum.inl))) * ReciprocityTheory.ChartRestriction.G.Semi.res (Qi j) (@id (Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ) (t'.s (j ∘ Sum.inr))))
  simp only [map_mul, map_prod, map_zpow, res_res_lemma, Fintype.prod_sum_type] at G1 G2 ⊢
  exact (congrArg₂ (· * ·) G1 G2).trans (mul_mul_mul_comm _ _ _ _)

private lemma corr_pull_lemma_6 {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {a : LB.Gen (LB.LinComb L φ ε)}
    {b : LB.Gen (LB.LinComb L φ' ε')} (hab : LB.Gen.Corr L φ ε φ' ε' a b) {h : Z ⟶ Y} :
    LB.Gen.Corr L (fun k => h ≫ φ k) ε (fun k => h ≫ φ' k) ε' (LB.pullGen L φ ε a h) (LB.pullGen L φ' ε' b h) := by
  intro j j' hj hj' hjj'
  have H1 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) inf_le_left) (@id (Γ(Y, LB.wchart L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') inf_le_right) (@id (Γ(Y, LB.wchart L φ' j')ˣ) (b.s j')) :=
    hab j j' (fun k₁ k₂ e => hj k₁ k₂ (by simp only [e])) (fun k₁ k₂ e => hj' k₁ k₂ (by simp only [e]))
      (fun k k' e => hjj' k k' (by simp only [e]))
  have Pa : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have Pb : LB.wchart L (fun k => h ≫ φ' k) j' ≤ h ⁻¹ᵁ LB.wchart L φ' j' := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have T : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := le_inf (inf_le_left.trans Pa) (inf_le_right.trans Pb)
  have H := congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res T (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j ⊓ LB.wchart L φ' j') z)) H1
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ LB.wchart L (fun k => h ≫ φ k) j) inf_le_left) (ReciprocityTheory.ChartRestriction.G.Semi.res Pa (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j) (@id (Γ(Y, LB.wchart L φ j)ˣ) (a.s j)))) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ LB.wchart L (fun k => h ≫ φ' k) j') inf_le_right) (ReciprocityTheory.ChartRestriction.G.Semi.res Pb (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ' j') (@id (Γ(Y, LB.wchart L φ' j')ˣ) (b.s j'))))
  simp only [res_res_lemma, pullU_res_lemma_2] at H ⊢
  exact H

private lemma corr_scale_lemma_7 {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {v : Γ(Y, ⊤)ˣ} {a : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {b : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (hab : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' a b) :
    LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' (scaleGen φ ε v a) (scaleGen φ' ε' v b) := by
  intro j j' hj hj' hjj'
  have H0 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ j) inf_le_left) (@id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ' j') inf_le_right) (@id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ' j')ˣ) (b.s j')) := hab j j' hj hj' hjj'
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ j) inf_le_left)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ≤ ⊤) le_top) v * @id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ' j') inf_le_right)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ' j' ≤ ⊤) le_top) v * @id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ' j')ˣ) (b.s j'))
  simp only [map_mul, res_res_lemma]
  rw [H0]

theorem eL_isGen (C : ChartAt Xo c y) (m : ℕ) : (eL y C.d C.x C.B.A.act C.e C.wP m).IsGen := by
  first
  | exact mulGen_isGen_lemma_5 (pullGen_isGen_lemma_4 C.prim.1) (pullGen_isGen_lemma_4 (C.frame.gen m))
  | (dsimp only [Formalism.L2.Pj.eL, Formalism.L2.Pj.pe]
     exact mulGen_isGen_lemma_5 (pullGen_isGen_lemma_4 C.prim.1) (pullGen_isGen_lemma_4 (C.frame.gen m)))

theorem scaleGen_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (v : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (hg : g.IsGen) : (scaleGen φ ε v g).IsGen := by
  intro i j
  have H := hg i j
  simp only [Formalism.L2.Pj.scaleGen, map_mul, res_res_lemma]
  rw [H]
  exact mul_left_comm _ _ _

theorem exists_tau (C : ChartAt Xo c y) (m : ℕ) :
    ∃ τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (eL y C.d C.x C.B.A.act C.e C.wP m) := by
  have hL := Xo.univ.t.PP.isLB
  have hch := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  obtain ⟨τ, hτ, hv⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (C.x m).left) (ε' := fun _ => (1 : ℤ)) (by
      intro U _ hU
      have hf : ∀ I : ULift.{0} (Finset (Fin 2)),
          (C.x m).left ≫ cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I =
            (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
              (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)] :
                Fin 2 → Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S) p.1 p.2)).left ≫
              cφ ![jpt y C.d C.x m (0 : Fin 2), jpt y C.d C.x m (1 : Fin 2)] I :=
        fun I => GermD.formEq_eL hch m I
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, hf]
      rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
      simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]) _ (eL_isGen C m)
  exact ⟨τ, hτ, corr_of_val hL fun y' J hJ => hv _ (𝟙 _) y' J hJ⟩

theorem const_hL (C : ChartAt Xo c y) : MvPowerSeries.constantCoeff (C.B.hL S C.h H.w0) = 0 := by
  have hh0 : MvPowerSeries.constantCoeff C.h = 0 := by
    have e := Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev (n := 1) ![0, Germ.pt S (n := 1) C.d 0] (by intro p q; fin_cases p <;> simp [Germ.pt])
      C.h
    rw [C.gauge.ax0, map_zero] at e
    exact e.symm
  have hact : ∀ q, MvPowerSeries.constantCoeff (Germ.comp1 (C.B.actK S H.w0) (Germ.pt S (n := 1) C.d 0) q) = 0 := by
    intro q
    unfold Germ.comp1
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev _ (by intro p' q'; fin_cases p'; simp [Germ.pt])]
    unfold Germ.FB.actK
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, C.B.A.const, map_zero]
  unfold Germ.FB.hL
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev _ (by
    intro p q
    fin_cases p
    · simp [Germ.pt]
    · exact hact q)]
  exact hh0

theorem exists_uJ (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) :
    ∃ u : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
      (u : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) := by
  have h0 : MvPowerSeries.constantCoeff (compL φ (C.B.hL S C.h H.w0)) = 0 := by
    unfold compL
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (fun p : Fin 1 × Fin C.d => hφ p.2)]
    exact const_hL C
  have h1 : MvPowerSeries.constantCoeff (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) = 1 := by
    unfold Germ.FB.expS
    rw [PowerSeries.subst, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (fun _ => by rw [map_neg, h0, neg_zero])]
    exact PowerSeries.constantCoeff_exp
  obtain ⟨v, hv⟩ : IsUnit (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h1]; exact isUnit_one)
  refine ⟨⟨psJet m (v : MvPowerSeries _ S), psJet m (↑v⁻¹ : MvPowerSeries _ S), ?_, ?_⟩, ?_⟩
  · rw [← FBIdJet.psJet_mul, Units.mul_inv, FBIdJet.psJet_one]
  · rw [← FBIdJet.psJet_mul, Units.inv_mul, FBIdJet.psJet_one]
  · simp only [hv]

def eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ) (m : ℕ) : ExpFr y (xExp y C φ) m :=
  scaleGen _ _ (unitΓ (u m)) (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left)

theorem exists_eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∃ (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1)
      (fun _ => (C.x m).left) fun _ => (1 : ℤ))) (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ),
      (∀ m, (τ m).IsGen) ∧
      (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m)) ∧
      (∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
        psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) ∧
      (∀ m, (eG C φ τ u m).IsGen) ∧ IsExpGaugeOf y C φ (eG C φ τ u) := by
  choose τ hτ hτc using exists_tau C
  choose u hu using exists_uJ C φ hφ
  refine ⟨τ, u, hτ, hτc, hu, fun m => ?_, ?_⟩
  · first
    | exact scaleGen_isGen _ _ _ _ (pullGen_isGen_lemma_4 (hτ m))
    | (unfold eG; exact scaleGen_isGen _ _ _ _ (pullGen_isGen_lemma_4 (hτ m)))
  · first
    | exact fun m => ⟨u m, hu m, corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m))⟩
    | (intro m; exact ⟨u m, hu m, corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m))⟩)
    | (intro m; refine ⟨u m, hu m, ?_⟩; unfold eG; exact corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m)))

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

section Jet

variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

private theorem jetAug_mk_lemma (P : MvPolynomial κ S) :
    (jetAug : Jet S κ 0 →ₐ[S] S) (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) P) =
      MvPolynomial.constantCoeff P := by
  show MvPolynomial.aeval (fun _ => (0 : S)) P = _
  simp [MvPolynomial.aeval_zero']

private theorem jet0_eq_lemma (x : Jet S κ 0) :
    x = algebraMap S (Jet S κ 0) ((jetAug : Jet S κ 0 →ₐ[S] S) x) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (0 + 1)) x
  rw [jetAug_mk_lemma]
  show (Ideal.Quotient.mk (orig S κ ^ (0 + 1))) P =
    Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff P))
  rw [Ideal.Quotient.eq]
  have h := sub_const_mem_orig P
  simpa using h

theorem aug_comp_eq (f : Jet S κ 0 →ₐ[S] Jet S κ' 0) :
    (jetAug : Jet S κ' 0 →ₐ[S] S).comp f = jetAug := by
  refine AlgHom.ext fun x => ?_
  have hx := jet0_eq_lemma x
  rw [AlgHom.comp_apply, hx]
  simp only [AlgHom.commutes]

private theorem mem_degLE_lemma (n : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE n ↔ (e.sum fun _ k => k) ≤ n := by
  constructor
  · intro h
    simp only [degLE, Finset.mem_filter] at h
    exact h.2
  · intro h
    have hb : ∀ i, e i < n + 1 := by
      intro i
      rcases Nat.eq_zero_or_pos (e i) with h0 | hpos
      · omega
      · have hi : i ∈ e.support := Finsupp.mem_support_iff.2 (by omega)
        have h1 := Finset.single_le_sum (f := (⇑e)) (fun _ _ => Nat.zero_le _) hi
        have h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j := rfl
        omega
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨fun i => ⟨e i, hb i⟩, ?_⟩, h⟩
    ext i
    simp

private theorem monomial_mem_orig_pow_lemma (n : ℕ) (e : κ →₀ ℕ) (c : S)
    (h : n ≤ e.sum fun _ k => k) : MvPolynomial.monomial e c ∈ orig S κ ^ n := by
  have hX : ∀ i, (MvPolynomial.X i : MvPolynomial κ S) ∈ orig S κ :=
    fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 : (e.prod fun i k => (MvPolynomial.X i : MvPolynomial κ S) ^ k) ∈
      orig S κ ^ (e.sum fun _ k => k) := by
    have h2 : (e.sum fun _ k => k) = ∑ j ∈ e.support, e j := rfl
    rw [h2, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _
  rw [MvPolynomial.monomial_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right h h1)

private theorem psTrunc_succ_sub_lemma (n : ℕ) (f : MvPowerSeries κ S) :
    psTrunc (n + 1) f - psTrunc n f ∈ orig S κ ^ (n + 1) := by
  have hsub : (degLE n : Finset (κ →₀ ℕ)) = (degLE (n + 1)).filter (fun e => (e.sum fun _ k => k) ≤ n) := by
    ext e
    simp only [Finset.mem_filter, mem_degLE_lemma]
    exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
  unfold psTrunc
  rw [hsub, ← Finset.sum_filter_add_sum_filter_not (degLE (n + 1))
    (fun e => (e.sum fun _ k => k) ≤ n), add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  rw [Finset.mem_filter, mem_degLE_lemma] at he
  have he2 := he.2
  exact monomial_mem_orig_pow_lemma _ _ _ (by omega)

private theorem cc_psTrunc_lemma (n : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.constantCoeff (psTrunc n f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq', if_pos ((mem_degLE_lemma n 0).2 (by simp))]
  rfl

private theorem jetTrunc_mk_lemma (n : ℕ) (P : MvPolynomial κ S) :
    (jetTrunc : Jet S κ (n + 1) →ₐ[S] Jet S κ n) (Ideal.Quotient.mk (orig S κ ^ (n + 1 + 1)) P) =
      Ideal.Quotient.mk (orig S κ ^ (n + 1)) P := rfl

private theorem jetSubstPS_mk_lemma (n : ℕ) (g : κ → MvPowerSeries κ' S) (P : MvPolynomial κ S) :
    (jetSubstPS (m := n) g) (Ideal.Quotient.mk (orig S κ ^ (n + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (n + 1))
        (MvPolynomial.aeval (fun i => psTrunc n (g i) -
          MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc n (g i)))) P) := rfl

theorem jetSubstPS_trunc (m : ℕ) (g : κ → MvPowerSeries κ' S) :
    (jetTrunc : Jet S κ' (m + 1) →ₐ[S] Jet S κ' m).comp (jetSubstPS (m := m + 1) g) =
      (jetSubstPS (m := m) g).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  simp only [jetTrunc_mk_lemma, jetSubstPS_mk_lemma, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq, cc_psTrunc_lemma, cc_psTrunc_lemma, sub_sub_sub_cancel_right]
  exact psTrunc_succ_sub_lemma m (g i)

theorem jetTrunc_psJet (m : ℕ) (f : MvPowerSeries κ S) :
    (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) (psJet (m + 1) f) = psJet m f := by
  show (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m)
      (Ideal.Quotient.mk (orig S κ ^ (m + 1 + 1)) (psTrunc (m + 1) f)) =
    Ideal.Quotient.mk (orig S κ ^ (m + 1)) (psTrunc m f)
  rw [jetTrunc_mk_lemma, Ideal.Quotient.eq]
  exact psTrunc_succ_sub_lemma m f

theorem mem_orig_of_cc' (P : MvPolynomial κ S) (h : MvPolynomial.constantCoeff P = 0) : P ∈ orig S κ := by
  have h1 := sub_const_mem_orig P
  simpa [h] using h1

theorem cc_psTrunc' (m : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  exact cc_psTrunc_lemma m f

theorem psJet_zero_of (f : MvPowerSeries κ S) (hf : MvPowerSeries.constantCoeff f = 1) : psJet 0 f = 1 := by
  show Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (psTrunc 0 f) = 1
  rw [← map_one (Ideal.Quotient.mk (orig S κ ^ (0 + 1))), Ideal.Quotient.eq]
  have h : psTrunc 0 f - 1 ∈ orig S κ := by
    apply mem_orig_of_cc'
    rw [map_sub, map_one, cc_psTrunc', hf, sub_self]
  simpa using h

end Jet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem const_compL {d' : ℕ} (φ : Fin d' → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d') S) :
    MvPowerSeries.constantCoeff (compL φ g) = MvPowerSeries.constantCoeff g := by
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d' => φ p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => hφ p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hφ p.2]; exact IsNilpotent.zero)
  unfold compL
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (φ s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hi) (by rw [map_pow, hφ, zero_pow hi])
    simp only [h0, smul_zero]

theorem const_expS_neg {d' : ℕ} (g : MvPowerSeries (Fin 1 × Fin d') S)
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (Germ.FB.expS S (-g)) = 1 := by
  have hg' : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg, neg_zero]
  have ha : PowerSeries.HasSubst (-g) := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero hg'
      | exact PowerSeries.hasSubst_of_constantCoeff_zero hg'
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hg'
      | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hg']; exact IsNilpotent.zero)
  show MvPowerSeries.constantCoeff (PowerSeries.subst (-g) (PowerSeries.exp S)) = 1
  rw [PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro d hd
    simp [map_pow, map_neg, hg, zero_pow hd]

theorem rig_eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u 0)
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := by
  have hL := Xo.univ.t.PP.isLB
  have hu0 : u 0 = 1 := Units.ext ((hu 0).trans (psJet_zero_of _ (const_expS_neg _
    (by rw [const_compL φ hφ]; exact ExpGA.const_hL C))))
  have hmor : ((homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left ≫
      (homAt y.x (jφ φ 0)).left) = (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left := by
    rw [← Over.comp_left, homAt_comp, aug_comp_eq]
  refine corr_of_val hL fun z J hJ => ?_
  calc val (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) (𝟙 _) z J
      = val (ExpGA.eG C φ τ u 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z J :=
        val_pull hJ _ _ _
    _ = gm (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z ⊤ (unitΓ (u 0)) *
          val (LB.pullGen Xo.univ.t.PP.L _ _ (τ 0) (homAt y.x (jφ φ 0)).left)
            (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) z J :=
        GermB.val_scale Xo.univ.t _ _ _ _ _ z J hJ
    _ = val (τ 0) ((𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left) ≫
          (homAt y.x (jφ φ 0)).left) z J := by
        rw [hu0, show unitΓ (1 : (Jet S (Fin 1 × Fin (dL Dw)) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
          _root_.one_mul]
        exact val_pull hJ _ _ _
    _ = val (eL y C.d C.x C.B.A.act C.e C.wP 0) (𝟙 _ ≫ (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
          z J := by
        rw [val_corr hJ (hτc 0), Category.id_comp, Category.id_comp, hmor]
    _ = val (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) (𝟙 _) z J :=
        (val_pull hJ _ _ _).symm.trans (val_corr hJ C.rig0 _)

theorem trunc_eG (C : ChartAt Xo c y) (htr : FrTruncC y C) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (hu : ∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
      psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
      (ExpGA.eG C φ τ u m) := by
  have hL := Xo.univ.t.PP.isLB
  have hch := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  have hT : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left)
      (eL y C.d C.x C.B.A.act C.e C.wP m) := corr_of_val hL fun z J hJ => by
    rw [val_pull hJ, Category.id_comp]
    exact GermD.val_eL_trunc hch C.e C.wP htr m z J hJ
  have hmor : (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left ≫
      (homAt y.x (jφ φ (m + 1))).left = (homAt y.x (jφ φ m)).left ≫
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin C.d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp]
    unfold jφ
    rw [jetSubstPS_trunc]
  have hUm : Units.map (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m).toMonoidHom
      (u (m + 1)) = u m :=
    Units.ext ((congrArg _ (hu (m + 1))).trans ((jetTrunc_psJet m _).trans (hu m).symm))
  have hAB : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left)
        (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left)
      (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left) := corr_of_val hL fun z J hJ => by
    rw [val_pull hJ, val_pull hJ, val_corr hJ (hτc (m + 1)), Category.id_comp]
    rw [hmor, ← val_pull hJ, val_corr hJ hT, val_pull hJ, Category.id_comp, val_corr hJ (hτc m)]
  have e1 : LB.pullGen Xo.univ.t.PP.L _ _ (ExpGA.eG C φ τ u (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left =
      scaleGenG Xo.univ.t _ _ (unitΓ (u m))
        (LB.pullGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (τ (m + 1)) (homAt y.x (jφ φ (m + 1))).left)
          (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m)).left) := by
    unfold ExpGA.eG
    erw [FBIdLB.pullGen_scaleGenG, FBIdLB.unitΓ_homAt, hUm]
    rfl
  rw [e1]
  exact FBIdLB.corr_scaleGenG Xo.univ.t hAB _

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
end
end
