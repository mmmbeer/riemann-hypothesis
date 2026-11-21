import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingValuationNorm

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisLocal

open EigenSplit LieEigen
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD)

theorem eigenBasis_map {O R R' I : Type} [CommRing O] [CommRing R] [CommRing R'] [Finite I]
    {σ : I → O →+* R} (hσ : IsSplitting σ) {n m : ℕ} (ρ : O →+* Module.End R (Fin n → R)) (f : R →+* R')
    (ρ' : O →+* Module.End R' (Fin n → R')) (hf : ∀ a x, f ∘ ρ a x = ρ' a (f ∘ x)) (τ : I)
    (b : Fin m → Fin n → R) (hb : ∀ i, b i ∈ eigenSub ρ (σ τ))
    (H : ∀ c ∈ eigenSub ρ (σ τ), ∃! d : Fin m → R, ∑ i, d i • b i = c) :
    (∀ i, f ∘ b i ∈ eigenSub ρ' (f.comp (σ τ))) ∧
      ∀ c ∈ eigenSub ρ' (f.comp (σ τ)), ∃! d : Fin m → R', ∑ i, d i • (f ∘ b i) = c := by
  let _ := f.toAlgebra
  let F : (Fin n → R) →ₗ[R] (Fin n → R') := (Algebra.linearMap R R').compLeft (Fin n)
  have hF : IsBaseChange R' F := IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R R')
  have hf' : ∀ a x, F (ρ a x) = ρ' a (F x) := hf
  have hB := isBaseChange_eigenMapAlgebra hσ hf' hF τ
  let b' : Fin m → eigenSub ρ (σ τ) := fun i => ⟨b i, hb i⟩
  have key : ∀ c : eigenSub ρ (σ τ), ∃! d, Fintype.linearCombination R b' d = c := fun c => by
    refine (existsUnique_congr fun d => ?_).1 (H _ c.2)
    rw [Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    rfl
  let B : Module.Basis (Fin m) R (eigenSub ρ (σ τ)) :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ ((Function.bijective_iff_existsUnique _).2 key)).symm
  have hBi : ∀ i, (B i : Fin n → R) = b i := fun i => by
    simp [B, b', Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply_single]
  let B' := hB.basis B
  have hB' : ∀ i, (B' i : Fin n → R') = f ∘ b i := fun i => by
    rw [← hBi, IsBaseChange.basis_apply]
    rfl
  refine ⟨fun i => hB' i ▸ (B' i).2, fun c hc => ?_⟩
  have k : ∀ d : Fin m → R', ∑ i, d i • (f ∘ b i) = c ↔ B'.equivFun ⟨c, hc⟩ = d := fun d => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff, eq_comm]
    simp [hB']
  simp only [k]
  exact existsUnique_eq'

theorem isEigBasis_iff {O R : Type} [CommRing O] [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {n m : ℕ} {e : Fin n → (epsR R ⟶ G)} (he : IsLieBasis e) {act : OAct O G}
    {ρ : O →+* Module.End R (Fin n → R)} (hρ : ∀ a c, prodPts (ρ a c) e = prodPts c e ≫ act.act a)
    (χ : O →+* R) (b : Fin m → Fin n → R) :
    EigenvectorLieDegree.IsEigBasis act χ (fun i => prodPts (b i) e) ↔ (∀ i, b i ∈ eigenSub ρ χ) ∧
      ∀ c ∈ eigenSub ρ χ, ∃! d : Fin m → R, ∑ i, d i • b i = c := by
  have mem : ∀ c, EigenvectorLieDegree.IsEigVec act χ (prodPts c e) ↔ c ∈ eigenSub ρ χ := fun c => by
    rw [mem_eigenSub]
    refine (and_iff_right (isTangent_prodPts he.1 c)).trans (forall_congr' fun a => ?_)
    rw [← hρ, ← (prodPts_injective he).eq_iff]
    rw [prodPts_smul, Over.OverMorphism.ext_iff]
    rfl
  have cb : ∀ d c, IsLieComb d (fun i => prodPts (b i) e) (prodPts c e) ↔ ∑ i, d i • b i = c := fun d c => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    rw [prodPts_prodPts he.1, eq_comm]
    exact (prodPts_injective he).eq_iff
  refine and_congr (forall_congr' fun i => mem _) ⟨fun h c hc => ?_, fun h w hw => ?_⟩
  · exact (existsUnique_congr fun d => cb d c).1 (h _ ((mem c).2 hc))
  · obtain ⟨c, rfl⟩ := exists_prodPts he hw.1
    exact (existsUnique_congr fun d => cb d c).2 (h _ ((mem c).1 hw))

theorem isEigBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  intro E _ _ _ H l c R R' _ _ _ j g t t' n τ m v v' hv hv'
  let σ₀ : (E →+* ℂ) → 𝓞 E →+* c.F := fun τ =>
    (τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E)
  have hσ₀ : Function.Injective σ₀ := fun τ τ' h =>
    (isSplitting_complex E).injective
      (RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a))
  have hσ : IsSplitting fun τ => j.comp (σ₀ τ) :=
    isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) j (by
      simpa using (isUnit_discr_of_charZero (E := E) c.F).map j)
  obtain ⟨N, e, he⟩ := Chart.exists_isLieBasis t.G t.semi.smooth
  obtain ⟨e', he', ee⟩ := exists_isLieBasis_baseChange R R' g _ _ _ n.cart t.semi.smooth N e he
  obtain ⟨ρ, hρ⟩ := exists_action he t.act
  obtain ⟨ρ', hρ'⟩ := exists_action he' t'.act
  choose b hb using fun i => exists_prodPts he (hv.1 i).1
  obtain rfl : v = fun i => prodPts (b i) e := (funext hb).symm
  obtain rfl : v' = fun i => prodPts (g ∘ b i) e' := funext fun i =>
    Over.OverMorphism.ext (n.cart.1.hom_ext ((hv' i).trans (prodPts_left n.cart ee _).symm)
      ((Over.w _).trans (Over.w _).symm))
  obtain ⟨h1, h2⟩ := (isEigBasis_iff he hρ _ b).1 hv
  exact (isEigBasis_iff he' hρ' _ _).2
    (eigenBasis_map hσ ρ g ρ' (action_baseChange n.cart he' ee n.act hρ hρ') τ b h1 h2)

end GlobalTheory.EigBasisLocal
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieEigenbasis_baseChange_localAlgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  atlas_forward_decl GlobalTheory.EigBasisLocal.isEigBasis_baseChange
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisPrime

theorem eig_localization {R R' O L L' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (S : Submonoid R)
    [IsLocalization S R'] [CommRing O] [Module.Finite ℤ O] [AddCommGroup L] [Module R L] [Module O L]
    [SMulCommClass O R L] [AddCommGroup L'] [Module R' L'] [Module O L'] [SMulCommClass O R' L'] (f : L →+ L')
    (hs : ∀ (r : R) x, f (r • x) = algebraMap R R' r • f x) (ha : ∀ (a : O) x, f (a • x) = a • f x)
    (lift : ∀ y, ∃ q ∈ S, ∃ x, f x = algebraMap R R' q • y) (uniq : ∀ x, f x = 0 → ∃ q ∈ S, q • x = 0)
    (χ : O →+* R) {m : ℕ} (v : Fin m → L)
    (hv : ∀ w : L, (∀ a, a • w = χ a • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i)
    (w : L') (hw : ∀ a, a • w = algebraMap R R' (χ a) • w) : ∃! c : Fin m → R', w = ∑ i, c i • f (v i) := by
  classical
  have unit : ∀ q ∈ S, IsUnit (algebraMap R R' q) := fun q hq => IsLocalization.map_units R' ⟨q, hq⟩
  have inj : ∀ d : Fin m → R', ∑ i, d i • f (v i) = 0 → d = 0 := fun d hd => by
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples_of_finite S d
    choose d' hd' using hqi
    have h0 : f (∑ i, d' i • v i) = 0 := by
      simp only [map_sum, hs, hd', Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum, hd, smul_zero]
    obtain ⟨r, hr, h1⟩ := uniq _ h0
    have h2 : r • d' = 0 := (hv 0 (by simp)).unique
      (by rw [← h1, Finset.smul_sum]; simp [mul_smul]) (by simp)
    funext i
    have h3 := congrArg (algebraMap R R') (congrFun h2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hd', Algebra.smul_def, Pi.zero_apply,
      map_zero] at h3
    exact (unit q hq).mul_right_eq_zero.1 ((unit r hr).mul_right_eq_zero.1 h3)
  obtain ⟨q, hq, x, hx⟩ := lift w
  have h1 : ∀ a : O, ∃ r ∈ S, r • (a • x - χ a • x) = 0 := fun a => uniq _ (by
    rw [map_sub, ha, hs, hx, smul_comm a, hw, smul_comm, sub_self])
  choose r hr h1 using h1
  obtain ⟨s, hsp⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  have hQ : ∏ a ∈ s, r a ∈ S := S.prod_mem fun a _ => hr a
  obtain ⟨c, hc, -⟩ := hv ((∏ a ∈ s, r a) • x) fun a => by
    have : a ∈ Submodule.span ℤ (s : Set O) := hsp ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_coe.1 hb)
      rw [smul_comm b, smul_comm (χ b), ← sub_eq_zero, ← smul_sub, hk, _root_.mul_comm, mul_smul, h1, smul_zero]
    | zero => simp
    | add b b' _ _ e e' => rw [add_smul, e, e', map_add, add_smul]
    | smul k b _ e => rw [smul_assoc, e, map_zsmul, smul_assoc]
  have h2 := congrArg f hc
  simp only [map_sum, hs, hx, smul_smul] at h2
  obtain ⟨u, hu⟩ := ((unit _ hQ).mul (unit q hq)).exists_left_inv
  have h3 : w = ∑ i, (u * algebraMap R R' (c i)) • f (v i) := by
    simp only [mul_smul u]
    rw [← Finset.smul_sum, ← h2, smul_smul, hu, one_smul]
  refine ⟨_, h3, fun c' hc' => sub_eq_zero.1 (inj _ ?_)⟩
  simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [← hc', ← h3, sub_self]

theorem isEigBasis_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  intro E _ _ _ H R _ p _ t t' n χ m v v' hv hv'
  have := t.semi.smooth
  have : ∀ s : R, Smooth (Chart.Gs t.G s).hom := fun s => show Smooth (pullback.snd t.G.hom _) from inferInstance
  let j := algebraMap R (Localization.AtPrime p)
  choose g hg hgu using fun x : epsR R ⟶ t.G => existsUnique_isVecOver (f := j) n.cart.1 x
  let f₀ : Serre.Lie t.act → Serre.Lie t'.act := fun x =>
    Serre.Lie.mk _ (g x.hom) ((hg _).isTangent n.cart x.isTangent)
  have hf : ∀ x y, f₀ x = y ↔ IsVecOver j n.φ x.hom y.hom := fun x y =>
    ⟨fun e => e ▸ hg _, fun e => Serre.Lie.ext (hgu _ _ e).symm⟩
  have comb : ∀ (k : ℕ) (c : Fin k → R) (x : Fin k → Serre.Lie t.act),
      f₀ (∑ i, c i • x i) = ∑ i, j (c i) • f₀ (x i) := fun k c x =>
    (hf _ _).2 ((lieComb_baseChange _ _ j t.G t'.G n.φ n.cart k (fun i => (x i).hom) _ c (fun i => (f₀ (x i)).hom) _
      (fun i => hg _) ((Serre.Lie.isLieComb_iff c x _).2 rfl)).2 ((Serre.Lie.isLieComb_iff _ _ _).2 rfl))
  let f : Serre.Lie t.act →+ Serre.Lie t'.act := AddMonoidHom.mk' f₀ fun x y => by
    simpa using comb 2 1 ![x, y]
  have hs : ∀ (r : R) x, f (r • x) = j r • f x := fun r x => by
    change f₀ _ = _ • f₀ _
    simpa using comb 1 ![r] ![x]
  have ha : ∀ (a : 𝓞 E) x, f (a • x) = a • f x := fun a x => (hf _ _).2 (by
    have := hg x.hom
    simp only [IsVecOver] at this ⊢
    change (g x.hom ≫ t'.act.act a).left ≫ _ = _ ≫ (x.hom ≫ t.act.act a).left
    rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv n.cart (epsR (Localization.AtPrime p))
    (spMap (algebraMap R (DualNumber (Localization.AtPrime p)))) (spMap_comp_spMap _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv n.cart (𝟙_ (Over (Sp (Localization.AtPrime p)))) (spMap j)
    (Category.id_comp _).symm
  have one : (1 : Over.mk (spMap j) ⟶ t.G).left = η[t'.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have lift : ∀ y, ∃ q ∈ p.primeCompl, ∃ x, f x = j q • y := fun y => by
    obtain ⟨q, hq, w, hw, hwy⟩ := Chart.tan_prime_lift p (y' := e y.hom) (Over.OverMorphism.ext (by
      refine Eq.trans ?_ one.symm
      rw [Over.comp_left, he, ← y.isTangent]
      exact (Category.assoc _ _ _).symm))
    refine ⟨q, hq, Serre.Lie.mk _ w ((Chart.isTan_iff _).1 hw), (hf _ _).2 ?_⟩
    have := congrArg (fun z => z.left) hwy
    simp only [Over.comp_left, he] at this
    exact (Category.assoc _ _ _).trans this.symm
  have uniq : ∀ x, f x = 0 → ∃ q ∈ p.primeCompl, q • x = 0 := fun x hx => by
    obtain ⟨q, hq, h⟩ := Chart.tan_prime_uniq p (w := x.hom) ((Chart.isTan_iff _).2 x.isTangent)
      (Over.OverMorphism.ext (by
        rw [← map_one e, he]
        exact ((hf _ _).1 hx).symm))
    exact ⟨q, hq, Serre.Lie.ext h⟩
  let y : Fin m → Serre.Lie t.act := fun i => Serre.Lie.mk _ (v i) (hv.1 i).1
  have hy : v' = fun i => (f (y i)).hom := funext fun i => hgu _ _ (hv' i)
  subst hy
  refine ⟨fun i => ⟨Serre.Lie.isTangent _, Serre.Lie.mem_eig_iff_left.1 fun a => ?_⟩, fun w hw => ?_⟩
  · rw [← ha, (Serre.Lie.mem_eig_iff_left (v := y i)).2 (hv.1 i).2 a, hs]
    rfl
  · refine (existsUnique_congr fun c => ?_).1 (eig_localization p.primeCompl f hs ha lift uniq χ y
      (fun z hz => (existsUnique_congr fun c => ?_).1
        (hv.2 z.hom ⟨z.isTangent, (Serre.Lie.mem_eig_iff_left (τ := χ) (v := z)).1 hz⟩))
      (Serre.Lie.mk _ w hw.1) ((Serre.Lie.mem_eig_iff_left (τ := j.comp χ) (v := Serre.Lie.mk _ w hw.1)).2 hw.2))
    · rw [Serre.Lie.isLieComb_iff]
      exact ⟨fun h => congrArg Serre.Lie.hom h, fun h => Serre.Lie.ext h⟩
    · exact (Serre.Lie.isLieComb_iff c y _).trans ⟨fun h => Serre.Lie.ext h, fun h => congrArg Serre.Lie.hom h⟩

end GlobalTheory.EigBasisPrime
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieEigenbasis_localization_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  atlas_forward_decl GlobalTheory.EigBasisPrime.isEigBasis_atPrime
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)), (∀ (p : Ideal R) [p.IsPrime], ∃ (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) ∧ EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v') → EigenvectorLieDegree.IsEigBasis t.act χ v := by
  first | exact @GlobalTheory.FlatRow.isEigBasis_of_local | exact GlobalTheory.FlatRow.isEigBasis_of_local | (intros; apply GlobalTheory.FlatRow.isEigBasis_of_local <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.IntegralEigFrame

open Matrix

section Lie

variable {R K O : Type} [CommRing R] [CommRing K] [CommRing O]

end Lie

end GlobalTheory.IntegralEigFrame
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem eigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : EigStable T c := by
  intro R R' _ _ g j x τ m v v' hv hv'
  obtain ⟨t, ⟨n⟩⟩ := exists_sab x T
  obtain ⟨t', ⟨n'⟩⟩ := exists_sab (spMap g) t
  obtain ⟨n'', e''⟩ := TraitDataOfIntrinsic.map_comp n' n rfl
  choose w hw using fun i => exists_lift n.cart (v i)
  choose w' hw' _ using fun i => existsUnique_isVecOver n'.cart.1 (w i)
  have hb := ((fibre_iff n.cart hw).2 n.act _).2 hv
  refine ((fibre_iff n''.cart (v := w') fun i => ?_).2 n''.act _).1 (GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime E H R' t' _ m w' fun q _ => ?_)
  · change _ ≫ n''.φ = _
    rw [e'', ← Category.assoc, hw' i, Category.assoc, hw, hv']
  let p := q.comap g
  let gp : Localization.AtPrime p →+* Localization.AtPrime q := Localization.localRingHom p q g rfl
  have hg : gp.comp (algebraMap R _) = (algebraMap R' _).comp g :=
    RingHom.ext fun z => Localization.localRingHom_to_map p q g rfl z
  obtain ⟨tq, ⟨nq⟩⟩ := exists_sab (spMap (algebraMap R' (Localization.AtPrime q))) t'
  obtain ⟨tp, ⟨np⟩⟩ := exists_sab (spMap (algebraMap R (Localization.AtPrime p))) t
  obtain ⟨k, ek⟩ := TraitDataOfIntrinsic.map_comp nq n' rfl
  obtain ⟨k', ek'⟩ := TraitDataOfIntrinsic.map_cancel (g := spMap gp) k np
    (by rw [spMap_comp_spMap, spMap_comp_spMap, hg])
  choose wq hq _ using fun i => existsUnique_isVecOver nq.cart.1 (w' i)
  choose wp hp _ using fun i => existsUnique_isVecOver np.cart.1 (w i)
  refine ⟨tq, nq, wq, hq, ?_⟩
  have h₁ := GlobalTheory.T.isLieEigenbasis_localization_atPrime E H R p t tp np _ m w wp hb hp
  have h₂ := GlobalTheory.T.isLieEigenbasis_baseChange_localAlgebra E H l c _ _ ((algebraMap R _).comp j) gp tp tq k' τ m wp wq h₁ fun i =>
    EllComp.isVecOver_cancel np.cart.1 k'.cart.1 (hp i)
      (by rw [← ek', ek, hg]; exact EllComp.isVecOver_comp (hw' i) (hq i))
  rwa [← RingHom.comp_assoc, hg] at h₂

variable {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

theorem isIso_fst (Y : Model Xo c (RingHom.id c.F)) : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  infer_instance

theorem isNormal_genFibre (Y : Model Xo c (RingHom.id c.F)) : Geo.Tor.IsNormalScheme (FramedFlatCoordinates.genFibre Y) := by
  intro x
  have := isIso_fst Y
  let e := (asIso ((pullback.fst Y.s (spMap (RingHom.id c.F))).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨h₁, h₂⟩ := Y.normal (pullback.fst Y.s (spMap (RingHom.id c.F)) x)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem comb_one {R : Type} [CommRing R] {t : SAB H (Sp R)} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)}
    (hv : ∀ i, IsTangent (v i)) (i : Fin m) : IsLieComb ((1 : Matrix (Fin m) (Fin m) R) i) v (v i) := by
  have : (1 : Matrix (Fin m) (Fin m) R) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  exact (LieComb.lieComb_algebra _ _ m v hv).2.2.2.1 i

section Algebraic

variable {L : Type} [Field L] [NumberField L] {j : c.F →+* L} {a : FramedFlatCoordinates.Framed Y U τ L j} {y : Sp L ⟶ Xo.XF c}
  {sig : FramedFlatCoordinates.Rule Y U τ}

end Algebraic

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ w.asIdeal := by
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have := w.isMaximal
  let _ := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem IsSqNorm.pos {sig : FramedFlatCoordinates.Rule Y U τ} (hsig : FramedFlatCoordinates.VanishesNowhere sig) {s : c.F →+* ℂ} {κ : ℝ}
    (h : IsSqNorm sig s κ) : 0 < κ := by
  obtain ⟨a, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, h₁, h₂, rfl⟩ := h
  exact mul_pos (pow_pos (norm_pos_iff.2 (hsig _ _ a).ne_zero) 2) (div_pos h₁ h₂)

section Ties

variable {D : D7} {X : DivX D} (Lc : placeRankTwoOne.Loc D X) {j : ℕ} {Z : X.Comp j} {τ : D.what₂.Tau}
  {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Y : Model Xo c (RingHom.id c.F)} {U : (Xo.XF c).Opens} {em : c.F →+* D.what₂.LL}
  (Φ : FramedFlatCoordinates.sections Y U (DV.tauEmb D τ) →ₛₗ[em] X.geo.Fn (X.Yv j Z))

end Ties

end GlobalTheory.FlatRow
end
end
