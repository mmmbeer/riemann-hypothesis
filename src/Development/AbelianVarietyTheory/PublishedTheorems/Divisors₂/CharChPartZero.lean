import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

section
set_option autoImplicit false

noncomputable section

open Set Matrix
open GlobalTheory.HermFrame

namespace GlobalTheory.CxForm

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.ArInt

structure BottChern where

  bc : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} {A : HolAtlas M n}, HermSeq A r s → A.Fld

  isRealForm : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] {n r s : ℕ} {A : HolAtlas M n}
    (T : HermSeq A r s), A.IsRealForm 1 (bc T)

  ddc_bc : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] {n r s : ℕ} {A : HolAtlas M n}
    (T : HermSeq A r s) (a : T.κ) (x : A.Pt), x.pt ∈ T.U a → A.ddc (bc T) x =
      (A.chern (T.sub a) 2 x + A.chern (T.sub a) 1 x * A.chern (T.quot a) 1 x + A.chern (T.quot a) 2 x -
        A.chern (T.mid a) 2 x : Ev n)

  pull : ∀ {M M' : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [TopologicalSpace M'] [T2Space M']
    [SecondCountableTopology M'] {n n' r s : ℕ} {A : HolAtlas M n} {A' : HolAtlas M' n'} (T : HermSeq A r s)
    (T' : HermSeq A' r s) (f : M' → M), A.IsHolo A' f → T'.IsPull T f → A'.IsExact (bc T' - A.pullback A' f (bc T))

  split : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] {n r s : ℕ} {A : HolAtlas M n}
    (T : HermSeq A r s), T.IsSplit → A.IsExact (bc T)

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

abbrev IsRegVar.coeFld (h : IsRegVar p D) (w : ∀ σ, (h.atlas σ).Pt → Ev D) : h.Fld := fun σ x => w σ x

structure ArRing (B : BottChern) (h : IsRegVar p D) where

  CH : Type

  [ring : CommRing CH]

  [alg : Algebra ℚ CH]

  gr : ℕ → Submodule ℚ CH

  [graded : GradedAlgebra gr]

  gr_eq_bot : ∀ j, D + 1 < j → gr j = ⊥

  om : CH →ₐ[ℚ] ∀ σ, (h.atlas σ).Pt → Ev D

  om_isArForm : ∀ j, ∀ x ∈ gr j, h.IsArForm j (h.coeFld (om x))

  om_closed : ∀ x σ, (h.atlas σ).del (h.coeFld (om x) σ) = 0 ∧ (h.atlas σ).dbar (h.coeFld (om x) σ) = 0

  a : h.Fld →ₗ[ℚ] CH

  a_mem : ∀ j η, h.IsArForm j η → a η ∈ gr (j + 1)

  a_exact : ∀ j η, h.IsArForm j η → (∀ σ, (h.atlas σ).IsExact (η σ)) → a η = 0

  om_a : ∀ j η, h.IsArForm j η → ∀ σ, h.coeFld (om (a η)) σ = (h.atlas σ).ddc (η σ)

  a_mul : ∀ j η, h.IsArForm j η → ∀ x, a η * x = a (η * h.coeFld (om x))

  deg : CH →ₗ[ℚ] ℝ

  deg_eq_zero : ∀ j, j ≠ D + 1 → ∀ x ∈ gr j, deg x = 0

  deg_a : ∀ η, h.IsArForm D η → deg (a η) = 1 / 2 * h.integral η

  c1 : HermLB p → CH

  constant_one_mem_nonvanishing : ∀ L, c1 L ∈ gr 1

  firstChernCongr : ∀ L M, L.Isometric M → c1 L = c1 M

  firstChernTensor : ∀ L M, c1 (L.tens M) = c1 L + c1 M

  chernForm_firstChernClass : ∀ (L : HermLB p) σ (x : (h.atlas σ).Pt) (i : L.B.ι), x.pt ∈ ptsIn p σ (L.B.U i) →
    om (c1 L) σ x = ofValues (ddc (fun v => (L.φ σ).φ i (x.ch.symm v)) x.crd)

  firstChernRaise : ∀ (L : HermLB p) u hu hc, c1 (L.raise u hu hc) = c1 L + a fun σ => (h.atlas σ).fn (u σ)

  degreeFirstChernPow : ∀ [IsIntegral X] (L : HermLB p) (t : ℝ), L.IsSelfInter t → deg (c1 L ^ (D + 1)) = t

  cl : ∀ {r : ℕ}, HermVB p r → ℕ → CH

  cl_mem : ∀ {r} (E : HermVB p r) j, cl E j ∈ gr j

  cl_zero : ∀ {r} (E : HermVB p r), cl E 0 = 1

  cl_one : ∀ {r} (E : HermVB p r), cl E 1 = c1 E.det

  cl_eq_zero : ∀ {r} (E : HermVB p r) j, r < j → cl E j = 0

  cl_congr : ∀ {r} (E E' : HermVB p r) (φ : E.E ≅ E'.E), E.h.IsIsometry E'.h φ → ∀ j, cl E j = cl E' j

  om_cl : ∀ {r} (E : HermVB p r) j σ (x : (h.atlas σ).Pt) (c : Chart E.E r), x.pt ∈ ptsIn p σ c.U →
    om (cl E j) σ x = (h.atlas σ).chern ((E.h.met σ).G c) j x

  whitney : ∀ {S : ShortComplex X.Modules} (hS : S.ShortExact) {r s : ℕ} {h₁ : VMetric p S.X₁ r}
    {h₂ : VMetric p S.X₂ (r + s)} {h₃ : VMetric p S.X₃ s} (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf) (H₃ : h₃.IsCInf),
    ∃ η, h.IsArForm 1 η ∧ (∀ σ, (h.atlas σ).IsExact (η σ - B.bc (h.seq hS H₁ H₂ H₃ σ))) ∧
      cl ⟨_, h₁, H₁⟩ 2 + cl ⟨_, h₁, H₁⟩ 1 * cl ⟨_, h₃, H₃⟩ 1 + cl ⟨_, h₃, H₃⟩ 2 - cl ⟨_, h₂, H₂⟩ 2 = a η

attribute [instance] ArRing.ring ArRing.alg ArRing.graded

def IsRegVar.pullFld (h : IsRegVar p D) (h' : IsRegVar q D') (π : Y ⟶ X) (hπ : π ≫ p = q) (η : h.Fld) : h'.Fld :=
  fun σ => (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map π hπ _) (η σ)

structure ArRing.IsPull {B : BottChern} {h : IsRegVar p D} {h' : IsRegVar q D'} (R : ArRing B h) (R' : ArRing B h')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (f : R.CH →ₐ[ℚ] R'.CH) : Prop where

  mem : ∀ j, ∀ x ∈ R.gr j, f x ∈ R'.gr j

  om : ∀ x, h'.coeFld (R'.om (f x)) = h.pullFld h' π hπ (h.coeFld (R.om x))

  a : ∀ j η, h.IsArForm j η → f (R.a η) = R'.a (h.pullFld h' π hπ η)

  c1 : ∀ L, f (R.c1 L) = R'.c1 (L.pull π hπ)

  cl : ∀ {r} (E : HermVB p r) j, f (R.cl E j) = R'.cl (E.pull π hπ) j

structure ArChow (B : BottChern) (k : Type) [CommRing k] where

  ring : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D), ArRing B h

  pull : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X), π ≫ p = q → ((ring h).CH →ₐ[ℚ] (ring h').CH)

  isPull : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q), (ring h).IsPull (ring h') π hπ (pull h h' π hπ)

  pull_id : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D),
    pull h h (𝟙 X) (Category.id_comp p) = AlgHom.id ℚ _

  pull_comp : ∀ {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k} {D D' D'' : ℕ} (h : IsRegVar p D)
    (h' : IsRegVar q D') (h'' : IsRegVar t D'') (π : Y ⟶ X) (hπ : π ≫ p = q) (ρ : Z ⟶ Y) (hρ : ρ ≫ q = t),
    pull h h'' (ρ ≫ π) (by rw [Category.assoc, hπ, hρ]) = (pull h' h'' ρ hρ).comp (pull h h' π hπ)

end GlobalTheory.CxForm

namespace GlobalTheory.Published

open GlobalTheory.CxForm

end GlobalTheory.Published

namespace GlobalTheory.CxForm.ArRing

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt MvPolynomial

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {B : BottChern} {h : IsRegVar p D}
  (R : ArRing B h) (L : HermLB p) {ι : Type} [Fintype ι]

theorem firstChern_trivial : R.c1 (.triv p) = 0 :=
  left_eq_add.1 ((R.firstChernCongr _ _ (HermLB.triv p).isometric_tens_triv).symm.trans (R.firstChernTensor _ _))

theorem firstChern_dual : R.c1 L.dual = -R.c1 L :=
  eq_neg_of_add_eq_zero_left ((R.firstChernTensor _ _).symm.trans ((R.firstChernCongr _ _ L.isometric_dual_tens).trans R.firstChern_trivial))

theorem firstChern_pow (m : ℕ) : R.c1 (L.pow m) = m • R.c1 L := by
  induction m with
  | zero => rw [R.firstChernCongr _ _ L.isometric_pow_zero, firstChern_trivial, zero_smul]
  | succ m ih => rw [R.firstChernCongr _ _ (L.isometric_pow_succ m), R.firstChernTensor, ih, succ_nsmul]

theorem firstChern_zpow (m : ℤ) : R.c1 (zp L m) = m • R.c1 L := by
  rw [zp, R.firstChernTensor, firstChern_dual, firstChern_pow, firstChern_pow, ← natCast_zsmul, ← natCast_zsmul, ← sub_eq_add_neg, ← sub_smul,
    Int.toNat_sub_toNat_neg]

theorem firstChern_tensor_powers (L : ι → HermLB p) (m : ι → ℤ) : R.c1 (comb L m) = ∑ i, m i • R.c1 (L i) := by
  rw [← Finset.sum_map_toList, comb]
  induction (Finset.univ : Finset ι).toList with
  | nil => exact R.firstChern_trivial
  | cons a l ih => rw [List.foldr_cons, R.firstChernTensor, firstChern_zpow, ih, List.map_cons, List.sum_cons]

theorem deg_aeval [IsIntegral X] {L : ι → HermLB p} {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L D Φ)
    (P : MvPolynomial ι ℚ) : R.deg (aeval (fun i => R.c1 (L i)) P) = Φ (map (algebraMap ℚ ℝ) P) := by
  let Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
    (basisMonomials ι ℝ).constr ℝ fun d => R.deg (aeval (fun i => R.c1 (L i)) (monomial d (1 : ℚ)))
  have h₀ (d) : Ψ (monomial d 1) = R.deg (aeval (fun i => R.c1 (L i)) (monomial d (1 : ℚ))) :=
    (basisMonomials ι ℝ).constr_basis ℝ _ d
  have h₁ (P : MvPolynomial ι ℚ) : R.deg (aeval (fun i => R.c1 (L i)) P) = Ψ (map (algebraMap ℚ ℝ) P) := by
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      rw [map_monomial, ← mul_one (algebraMap ℚ ℝ c), ← smul_eq_mul, ← smul_monomial, map_smul, h₀, algebraMap_smul,
        ← map_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
  have h₂ : Ψ - Φ = 0 := Model.eq_zero_of_pow (D + 1) _ (fun m => ?_) fun P e he hP => ?_
  · rw [h₁, sub_eq_zero.1 h₂]
  · have e : lin (fun i => (m i : ℝ)) ^ (D + 1) = map (algebraMap ℚ ℝ) ((∑ i, m i • MvPolynomial.X i) ^ (D + 1)) := by
      simp [lin]
    rw [LinearMap.sub_apply, ← R.degreeFirstChernPow _ _ (hΦ.1 m), e, ← h₁, firstChern_tensor_powers]
    simp
  · rw [LinearMap.sub_apply, hΦ.2 P e he hP, sub_zero, P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [← mul_one (coeff d P), ← smul_eq_mul, ← smul_monomial, map_smul, h₀, R.deg_eq_zero e he, smul_zero]
    rw [aeval_monomial, map_one, one_mul, ← hP (mem_support_iff.1 hd), Finsupp.weight_apply]
    exact SetLike.prod_mem_graded R.gr _ _ fun i _ => SetLike.pow_mem_graded _ (R.constant_one_mem_nonvanishing _)


end GlobalTheory.CxForm.ArRing
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

section Values

variable {n : ℕ}

def hermMat (α : Alt n) : Matrix (Fin n) (Fin n) ℂ :=
  of fun a b => -Complex.I * (bas n).repr α {a.castAdd n, b.natAdd n}

def eval₂ (α : Alt n) (ξ η : V n) : ℂ :=
  Complex.I * (HermFrame.form (hermMat α) ξ η - HermFrame.form (hermMat α) η ξ)

theorem bas_pair (a b : Fin n) : bas n {a.castAdd n, b.natAdd n} = dz a * dzb b := by
  have hlt : a.castAdd n < b.natAdd n := by
    rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
  have hc : ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))).card = 2 := Finset.card_pair hlt.ne
  have e : ⇑(({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))).orderEmbOfFin hc) = ![a.castAdd n, b.natAdd n] :=
    (Finset.orderEmbOfFin_unique hc (fun i => by fin_cases i <;> simp)
      (Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simpa using hlt)).symm
  rw [bas, ExteriorAlgebra.basis_apply_ofCard _ hc, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv, Set.powersetCard.ofCard, e, dz, dzb, -Fin.natAdd_eq_addNat]


end Values

def chPart (r j : ℕ) : symmetricSubalgebra (Fin r) ℚ := ((j.factorial : ℚ)⁻¹) • ⟨psum (Fin r) ℚ j, psum_isSymmetric _ _ j⟩

def tdPart (r j : ℕ) : symmetricSubalgebra (Fin r) ℚ :=
  ⟨homogeneousComponent j (∏ i, ∑ m ∈ Finset.range (j + 1), C (bernoulli' m / m.factorial) * X i ^ m), fun e => by
    rw [rename_homogeneousComponent, map_prod]
    congr 1
    exact Fintype.prod_equiv e _ _ fun i => by simp⟩

def rCoeff (m : ℕ) : ℝ := (2 * deriv riemannZeta (-m) + riemannZeta (-m) * (harmonic m : ℚ)).re

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

namespace ArRing

variable {B : BottChern} {h : IsRegVar p D} (R : ArRing B h) {r : ℕ} (E : HermVB p r)

def char : symmetricSubalgebra (Fin r) ℚ →ₐ[ℚ] R.CH :=
  (aeval fun i : Fin r => R.cl E (i + 1)).comp (esymmAlgEquiv (Fin r) ℚ (Fintype.card_fin r)).symm.toAlgHom

def ch : R.CH := ∑ j ∈ Finset.range (D + 2), R.char E (chPart r j)

def td : R.CH := ∑ j ∈ Finset.range (D + 2), R.char E (tdPart r j)

def rForm : h.Fld :=
  ∑ m ∈ (Finset.range (D + 1)).filter Odd, (rCoeff m : ℂ) • h.coeFld (R.om (R.char E (chPart r m)))

theorem char_esymm (j : ℕ) : R.char E ⟨esymm (Fin r) ℚ j, esymm_isSymmetric _ _ j⟩ = R.cl E j := by
  rcases j with _ | j
  · rw [R.cl_zero, ← map_one (R.char E)]
    exact congrArg _ (Subtype.ext (esymm_zero (Fin r) ℚ))
  by_cases hj : j < r
  · exact (congrArg _ (esymmAlgEquiv_symm_apply ℚ (Fintype.card_fin r) ⟨j, hj⟩)).trans (aeval_X _ _)
  · rw [R.cl_eq_zero E _ (by omega), ← map_zero (R.char E)]
    refine congrArg _ (Subtype.ext ?_)
    simp only [esymm, ZeroMemClass.coe_zero]
    rw [Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty]


theorem char_chPart_one : R.char E (chPart r 1) = R.cl E 1 := by
  rw [← char_esymm]
  exact congrArg _ (Subtype.ext (by simp [chPart, psum_one, esymm_one]))

theorem char_tdPart_zero : R.char E (tdPart r 0) = 1 := by
  rw [← map_one (R.char E)]
  exact congrArg _ (Subtype.ext (by simp [tdPart]))

theorem IsPull.char {h' : IsRegVar q D'} {R' : ArRing B h'} {π : Y ⟶ X} {hπ : π ≫ p = q} {f : R.CH →ₐ[ℚ] R'.CH}
    (H : R.IsPull R' π hπ f) (φ : symmetricSubalgebra (Fin r) ℚ) : f (R.char E φ) = R'.char (E.pull π hπ) φ := by
  simp only [ArRing.char, AlgHom.comp_apply, ← H.cl]
  exact comp_aeval_apply _ f _

end ArRing

variable (q) in

def IsGenSmooth (π : Y ⟶ X) : Prop :=
  ∃ U : Y.Opens, (∀ σ (y : CxPts q σ), y ∈ ptsIn q σ U) ∧ Smooth (U.ι ≫ π)

theorem IsGenSmooth.of_smooth (π : Y ⟶ X) [Smooth π] : IsGenSmooth q π :=
  ⟨⊤, fun _ _ => mem_ptsIn_top, inferInstance⟩

def IsRegVar.IsFibreInt (h : IsRegVar p D) (h' : IsRegVar q D') (π : Y ⟶ X) (hπ : π ≫ p = q) (η : h'.Fld) (η' : h.Fld) :
    Prop :=
  ∀ σ j φ, (h.atlas σ).IsRealForm j φ → (h.atlas σ).integral (η' σ * φ) =
    (h'.atlas σ).integral (η σ * (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map π hπ _) φ)

structure ArChow.Push {B : BottChern} (C : ArChow B k) where

  gr_zero : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D), ∀ x ∈ (C.ring h).gr 0,
    ∃ c : ℚ, x = algebraMap ℚ _ c

  push : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X), π ≫ p = q → IsGenSmooth q π → ((C.ring h').CH →ₗ[ℚ] (C.ring h).CH)

  mem : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i j : ℕ), i + D = j + D' → ∀ x ∈ (C.ring h').gr i,
    push h h' π hπ hs x ∈ (C.ring h).gr j

  eq_zero : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i : ℕ), i + D < D' → ∀ x ∈ (C.ring h').gr i,
    push h h' π hπ hs x = 0

  proj : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (x : (C.ring h).CH) (y : (C.ring h').CH),
    push h h' π hπ hs (C.pull h h' π hπ x * y) = x * push h h' π hπ hs y

  om : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (y : (C.ring h').CH),
    h.IsFibreInt h' π hπ (h'.coeFld ((C.ring h').om y)) (h.coeFld ((C.ring h).om (push h h' π hπ hs y)))

  a : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (i j : ℕ), i + D = j + D' → ∀ η, h'.IsArForm i η →
    ∃ η', h.IsArForm j η' ∧ h.IsFibreInt h' π hπ η η' ∧ push h h' π hπ hs ((C.ring h').a η) = (C.ring h).a η'

  deg : ∀ {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ} (h : IsRegVar p D) (h' : IsRegVar q D')
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (y : (C.ring h').CH),
    (C.ring h).deg (push h h' π hπ hs y) = (C.ring h').deg y

  push_id : ∀ {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D),
    push h h (𝟙 X) (Category.id_comp p) (.of_smooth _) = LinearMap.id

  push_comp : ∀ {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k} {D D' D'' : ℕ} (h : IsRegVar p D)
    (h' : IsRegVar q D') (h'' : IsRegVar t D'') (π : Y ⟶ X) (hπ : π ≫ p = q) (hs : IsGenSmooth q π) (ρ : Z ⟶ Y)
    (hρ : ρ ≫ q = t) (hs' : IsGenSmooth t ρ) (hs'' : IsGenSmooth t (ρ ≫ π)),
    push h h'' (ρ ≫ π) (by rw [Category.assoc, hπ, hρ]) hs'' = push h h' π hπ hs ∘ₗ push h' h'' ρ hρ hs'

open Limits

def relCot (π : Y ⟶ X) : Y.Modules := Conormal.conormal (pullback.diagonal π)

def dRel (π : Y ⟶ X) (W : Y.Opens) (f : Γ(Y, W)) : Γ(relCot π, W) :=
  Conormal.d (pullback.diagonal_fst π) (V := W) (W := pullback.snd π π ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, pullback.diagonal_snd]; exact le_rfl) ((pullback.snd π π).app W f)


variable (q) in

def IsRelAcyclic (π : Y ⟶ X) (L : LB Y) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (W : κ → Y.Opens),
    (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = π ⁻¹ᵁ U → ∀ n, (AbLaw.cechLB q L W).ExactAt (n + 1)

example (L : LB Y) (W : Fin 1 → Y.Opens) (n : ℕ) : (AbLaw.cechLB q L W).ExactAt (n + 1) :=
  .of_isZero (AbLaw.isZero_cechLB_X q L W (by simp))

end GlobalTheory.CxForm
end
end
