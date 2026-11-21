import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.GradedWeylDivisibility.FinalD

section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions MvPolynomial

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable instance ssFin (n : ℕ) (ν : Fin n → ℕ) : Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν) :=
  (Formalism.GradedWeylDivisibility.sSIdxFinite n n ν).fintype

def ssb (K : Type) [Field K] (n : ℕ) (ν : Fin n → ℕ) : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) K :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose

def tenP {ι K : Type} [Fintype ι] [CommRing K] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K :=
  ∏ τ, rename (Prod.mk τ) (f τ)

def nfD {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : ℂ :=
  Formalism.REAL.fockF p q / ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))

variable (D : D7)

abbrev VarT : Type := D.what₂.Tau × Fin (nW D) × Fin (nW D)

def intLat (κ : D.what₂.Tau → DomWeight (nW D)) : Submodule (𝓞 D.what₂.LL) (MvPolynomial (VarT D) D.what₂.LL) :=
  Submodule.map (mapAlgHom (Algebra.ofId (𝓞 D.what₂.LL) D.what₂.LL)).toLinearMap
    (Formalism.GradedWeylDivisibility.tensorLat (𝓞 D.what₂.LL) (𝓞 D.what₂.LL) (fun τ => Formalism.GradedWeylDivisibility.dualWeyl (𝓞 D.what₂.LL) (nW D) (nW D) (κ τ).natW))

def twistB (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL) (e : D.what₂.Tau → ℤ) : D.what₂.LL :=
  ((∏ τ, (Matrix.GeneralLinearGroup.det (B τ)) ^ (e τ) : D.what₂.LLˣ) : D.what₂.LL)

def twAct (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL) (e : D.what₂.Tau → ℤ) :
    MvPolynomial (VarT D) D.what₂.LL →ₗ[𝓞 D.what₂.LL] MvPolynomial (VarT D) D.what₂.LL :=
  (twistB D B e • (Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (B τ : Matrix (Fin (nW D)) (Fin (nW D)) D.what₂.LL))).toLinearMap).restrictScalars
    (𝓞 D.what₂.LL)

def LocEq (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (A B : Submodule (𝓞 D.what₂.LL) (Fin (nW D) → D.what₂.LL)) : Prop :=
  Formalism.HermitianLatticesTheory.locS (@Ideal.primeCompl _ _ w.asIdeal w.isPrime) A = Formalism.HermitianLatticesTheory.locS (@Ideal.primeCompl _ _ w.asIdeal w.isPrime) B

def colSpan (B : GL (Fin (nW D)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) (Fin (nW D) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) (Set.range fun t a => (B : Matrix (Fin (nW D)) (Fin (nW D)) D.what₂.LL) a t)

def FibLat (ell : D.what₂.Tau → HLat D.what₂.LL) (κ : D.what₂.Tau → DomWeight (nW D)) (c : XDef D) :
    Submodule (𝓞 D.what₂.LL) (MvPolynomial (VarT D) D.what₂.LL) :=
  ⨅ (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL)
    (_ : ∀ τ, LocEq D w (TxLat D ell c τ) (colSpan D (B τ))),
    Submodule.comap (twAct D B (fun τ => (κ τ).detShift))
      (Formalism.HermitianLatticesTheory.locS (@Ideal.primeCompl _ _ w.asIdeal w.isPrime) (intLat D κ))

abbrev NNIdx (R : Finset (XDef D)) (κ : D.what₂.Tau → DomWeight (nW D)) : Type :=
  {c // c ∈ R} × (∀ τ, Formalism.GradedWeylDivisibility.ssIdx (nW D) (nW D) (κ τ).natW)

section NN

variable (ell : D.what₂.Tau → HLat D.what₂.LL) (κ : D.what₂.Tau → DomWeight (nW D)) (R : Finset (XDef D))

def bPoly (i : NNIdx D R κ) : MvPolynomial (VarT D) D.what₂.LL :=
  tenP (fun τ => ssb D.what₂.LL (nW D) (κ τ).natW (i.2 τ))

open Classical in

def polyAt (c : {c // c ∈ R}) : (NNIdx D R κ → D.what₂.LL) →ₗ[D.what₂.LL] MvPolynomial (VarT D) D.what₂.LL where
  toFun x := ∑ i : NNIdx D R κ, if i.1 = c then x i • bPoly D κ R i else 0
  map_add' x y := by simp only [Pi.add_apply, add_smul]; rw [← Finset.sum_add_distrib]; congr 1; funext i; split_ifs <;> simp
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]; congr 1; funext i; split_ifs <;> simp [mul_smul]

def NNLat : Submodule (𝓞 D.what₂.LL) (NNIdx D R κ → D.what₂.LL) :=
  ⨅ c : {c // c ∈ R}, Submodule.comap ((polyAt D κ R c).restrictScalars (𝓞 D.what₂.LL)) (FibLat D ell κ c.1)

def atFrame (v : InfinitePlace D.what₂.LL) (c : XDef D) (F : MvPolynomial (VarT D) D.what₂.LL) :
    MvPolynomial (VarT D) ℂ :=
  Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (Tx D ell c τ).X v) (MvPolynomial.map v.embedding F)

def twAbs (v : InfinitePlace D.what₂.LL) (c : XDef D) : ℝ :=
  ∏ τ, ‖((Tx D ell c τ).X v).det‖ ^ (2 * (κ τ).detShift)

open Classical in

def gramNN (v : InfinitePlace D.what₂.LL) : Matrix (NNIdx D R κ) (NNIdx D R κ) ℂ := fun i i' =>
  if i.1 = i'.1 then
    (twAbs D ell κ v i.1.1 : ℂ) * nfD κ (atFrame D ell v i.1.1 (bPoly D κ R i')) (atFrame D ell v i.1.1 (bPoly D κ R i))
  else 0

open Classical in

def NNc : HLat D.what₂.LL where
  V := NNIdx D R κ → D.what₂.LL
  ι := NNIdx D R κ
  decι := Classical.decEq _
  b := Pi.basisFun D.what₂.LL (NNIdx D R κ)
  X := fun v => frameOf (gramNN D ell κ R v)
  L := NNLat D ell κ R

end NN

section Std

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def intStd (n : ℕ) (ν : Fin n → ℕ) : Submodule (𝓞 K) (MvPolynomial (Fin n × Fin n) K) :=
  Submodule.map (mapAlgHom (Algebra.ofId (𝓞 K) K)).toLinearMap (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν)

def polyStd (n : ℕ) (ν : Fin n → ℕ) : (Formalism.GradedWeylDivisibility.ssIdx n n ν → K) →ₗ[K] MvPolynomial (Fin n × Fin n) K where
  toFun x := ∑ i, x i • ssb K n ν i
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

def nabStd (n : ℕ) (lam : DomWeight n) : HLat K where
  V := Formalism.GradedWeylDivisibility.ssIdx n n lam.natW → K
  ι := Formalism.GradedWeylDivisibility.ssIdx n n lam.natW
  decι := Classical.decEq _
  b := Pi.basisFun K _
  X := fun v => frameOf (fun i i' =>
    nfD (fun _ : Unit => lam) (rename (Prod.mk ()) (MvPolynomial.map v.embedding (ssb K n lam.natW i')))
      (rename (Prod.mk ()) (MvPolynomial.map v.embedding (ssb K n lam.natW i))))
  L := Submodule.comap ((polyStd n lam.natW).restrictScalars (𝓞 K)) (intStd n lam.natW)

def mu0 (n : ℕ) (lam : DomWeight n) : ℝ := (nabStd (K := K) n lam).mu

end Std

end Formalism.L2.Geo.Def
end
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Def

def TensorFockProduct : Prop :=
  ∀ (T σ : Type) [Fintype T] [DecidableEq T] (p q : T → MvPolynomial σ ℂ),
    Formalism.REAL.fockF (∏ τ, rename (Prod.mk τ) (p τ)) (∏ τ, rename (Prod.mk τ) (q τ)) = ∏ τ, Formalism.REAL.fockF (p τ) (q τ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.Geo.Def
end
end

section
open Matrix MvPolynomial
open scoped Kronecker

noncomputable section

namespace Formalism.L2.Geo.Def
namespace KroneckerDeterminant

variable {R T : Type} [CommRing R] [Fintype T] [DecidableEq T] {I : T → Type} [∀ τ, Fintype (I τ)]
  [∀ τ, DecidableEq (I τ)] (A : ∀ τ, Matrix (I τ) (I τ) R)

end KroneckerDeterminant

namespace TensorFockForm

open Formalism.REAL

variable {T σ : Type} [Fintype T] [DecidableEq T]

def emb (g : T → σ →₀ ℕ) : T × σ →₀ ℕ := ∑ τ, Finsupp.mapDomain (Prod.mk τ) (g τ)

lemma prodMk_inj (τ : T) : Function.Injective (Prod.mk τ : σ → T × σ) := fun _ _ h => (Prod.mk.inj h).2

lemma emb_apply (g : T → σ →₀ ℕ) (τ : T) (k : σ) : emb g (τ, k) = g τ k := by
  unfold emb
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (prodMk_inj τ) _ _
  · intro τ' _ hτ'
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨k', hk'⟩
    exact hτ' (Prod.mk.inj hk').1
  · intro h; exact absurd (Finset.mem_univ τ) h

lemma emb_inj : Function.Injective (emb : (T → σ →₀ ℕ) → T × σ →₀ ℕ) := by
  intro g h hgh
  funext τ
  ext k
  rw [← emb_apply g τ k, ← emb_apply h τ k, hgh]

lemma fact_subset {α : Type} (u : α →₀ ℕ) (S : Finset α) (h : u.support ⊆ S) :
    ∏ k ∈ u.support, (u k).factorial = ∏ k ∈ S, (u k).factorial :=
  Finset.prod_subset h (fun k _ hk => by simp [Finsupp.notMem_support_iff.mp hk])

lemma fact_emb (g : T → σ →₀ ℕ) :
    ∏ x ∈ (emb g).support, (emb g x).factorial = ∏ τ, ∏ k ∈ (g τ).support, (g τ k).factorial := by
  classical
  set U : Finset σ := Finset.univ.biUnion fun τ => (g τ).support with hU
  have hsub : (emb g).support ⊆ (Finset.univ : Finset T) ×ˢ U := by
    rintro ⟨τ, k⟩ hx
    rw [Finsupp.mem_support_iff, emb_apply] at hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, hU, Finset.mem_biUnion]
    exact ⟨τ, Finsupp.mem_support_iff.mpr hx⟩
  rw [fact_subset _ _ hsub, Finset.prod_product]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [emb_apply]
  refine (fact_subset (g τ) U ?_).symm
  intro k hk
  simp only [hU, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨τ, hk⟩

lemma prod_rename_eq (p : T → MvPolynomial σ ℂ) :
    ∏ τ, rename (Prod.mk τ) (p τ) =
      ∑ g ∈ Fintype.piFinset (fun τ => (p τ).support), monomial (emb g) (∏ τ, coeff (g τ) (p τ)) := by
  calc ∏ τ, rename (Prod.mk τ) (p τ)
      = ∏ τ, ∑ v ∈ (p τ).support, monomial (Finsupp.mapDomain (Prod.mk τ) v) (coeff v (p τ)) := by
        refine Finset.prod_congr rfl fun τ _ => ?_
        conv_lhs => rw [as_sum (p τ)]
        rw [map_sum]
        simp only [rename_monomial]
    _ = ∑ g ∈ Fintype.piFinset (fun τ => (p τ).support),
          ∏ τ, monomial (Finsupp.mapDomain (Prod.mk τ) (g τ)) (coeff (g τ) (p τ)) :=
        Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun g _ => (monomial_sum_prod _ _ _).symm

open Classical in
lemma fock_mono (u v : σ →₀ ℕ) (a b : ℂ) :
    fockF (monomial u a) (monomial v b) =
      if u = v then a * star b * ((∏ k ∈ u.support, (u k).factorial : ℕ) : ℂ) else 0 := by
  rw [fischerInner_monomial_left, coeff_monomial]
  by_cases h : u = v
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]; simp

end TensorFockForm

open TensorFockForm Formalism.REAL in
theorem TensorFock_holds : TensorFockProduct := by
  intro T σ _ _ p q
  classical
  rw [prod_rename_eq p, prod_rename_eq q, fischerInner_sum_left]
  simp_rw [fischerInner_sum_right, fock_mono]
  have hR : ∀ τ, fockF (p τ) (q τ) = ∑ m ∈ (p τ).support, ∑ n ∈ (q τ).support,
      (if m = n then coeff m (p τ) * star (coeff n (q τ)) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) else 0) := by
    intro τ
    conv_lhs => rw [as_sum (p τ), as_sum (q τ)]
    rw [fischerInner_sum_left]
    simp_rw [fischerInner_sum_right, fock_mono]
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hgh : g = h
  · subst hgh
    simp only [if_true]
    rw [fact_emb]
    push_cast
    rw [star_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  · rw [if_neg (fun e => hgh (emb_inj e))]
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hgh
    exact (Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)).symm

end Formalism.L2.Geo.Def
end
end
