import Mathlib
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.AtTOwedS
import Formalism.LocalToGlobal.Columns.AtTLemmas
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.Columns.AtTOwedV
import Formalism.LocalToGlobal.Columns.AtTOwedC
import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.GL3MeanSquares.PrimeOrderRamificationResults
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

def lenO (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (Ow w) V) : ℕ∞ :=
  Module.length (Ow w) (A ⧸ B.comap A.subtype)

def mapO {V' : Type} [AddCommGroup V'] [Module K V'] (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V') (A : Submodule (Ow w) V) :
    Submodule (Ow w) V' :=
  A.map (f.restrictScalars (Ow w))

def piO {ι : Type} (w : HeightOneSpectrum (𝓞 K)) (A : ι → Submodule (Ow w) V) : Submodule (Ow w) (ι → V) where
  carrier := {x | ∀ i, x i ∈ A i}
  add_mem' := fun hx hy i => (A i).add_mem (hx i) (hy i)
  zero_mem' := fun i => (A i).zero_mem
  smul_mem' := fun r _ hx i => (A i).smul_mem r (hx i)

end Gen

section LemB

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end LemB

section LemC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end LemC

section T5

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def wtT {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : ℝ := 2 * lW w * (eW w : ℝ)

end T5

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

abbrev KerArg (u : Pr.Word) : Type := ∀ j : ℕ, ColV W Ch u j →ₗ[X.K] ColV W Ch u (j + 1)

variable {W Ch}

def KernelArgumentHypothesisScalar {u : Pr.Word} (kk : KerArg W Ch u) (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) : Prop :=
  ∀ j, j < R.m → ∀ P, (UOp W Ch u (j + 1) P).comp (kk j) = ((c j P : X.Kˣ) : X.K) • (kk j).comp (UOp W Ch u j P)

def cProdC (W : Wts X Pr.Word R) {u : Pr.Word} (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) (w : HeightOneSpectrum (𝓞 X.K)) (j : ℕ) : X.Kˣ :=
  ∏ P ∈ VVTc W u w, c j P

end Col

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

end Gen

section LemC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end LemC

section Det

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Det

section T5

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable [Nonempty X.Tau]

end T5

section Nab

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Nab

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

theorem list_prod_intertwines {K : Type} [Field K] {V V' ι : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (k : V →ₗ[K] V') (A : ι → Module.End K V) (A' : ι → Module.End K V') (c : ι → K)
    (h : ∀ i, (A' i).comp k = c i • k.comp (A i)) (l : List ι) :
    ((l.map A').prod).comp k = (l.map c).prod • k.comp (l.map A).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    have e1 : (A' i * (l.map A').prod).comp k = (A' i).comp (((l.map A').prod).comp k) := rfl
    rw [e1, ih, LinearMap.comp_smul, ← LinearMap.comp_assoc, h i, LinearMap.smul_comp, smul_smul, mul_comm (l.map c).prod]
    rfl

theorem KernelArgumentHypothesisScalar.prod {u : Pr.Word} {kk : KerArg W Ch u} {c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ} (h : KernelArgumentHypothesisScalar kk c) (w : HeightOneSpectrum (𝓞 X.K))
    (j : ℕ) (hj : j < R.m) :
    (UprodC W Ch u (j + 1) w).comp (kk j) = ((cProdC W c w j : X.Kˣ) : X.K) • (kk j).comp (UprodC W Ch u j w) := by
  have := list_prod_intertwines (kk j) (fun P => UOp W Ch u j P) (fun P => UOp W Ch u (j + 1) P) (fun P => ((c j P : X.Kˣ) : X.K))
    (fun P => h j hj P) (VVTc W u w).toList
  unfold UprodC cProdC
  rw [this, Units.coe_prod, Finset.prod_map_toList]

end Col

section NonDeg

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)


end NonDeg

section AutomorphicFormsHyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AutomorphicFormsHyp

section Price

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Price

section Vals

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end Vals

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end GSD

section ValsCol

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ValsCol

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host

section TBig

variable {X : Fields} {Pr : Primes X}

theorem Primes.Ok.T_modEq (hPr : Pr.Ok) (u : Pr.Word) : Pr.T u ≡ 1 [MOD Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2] := by
  obtain ⟨y, hy⟩ := hPr.piT_cong u
  have h1 : Pr.piT u = 1 + ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) * y := by
    rw [← hy]
    ring
  have h2 : X.conjO (Pr.piT u) = 1 + ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) * X.conjO y := by
    rw [h1, map_add, map_one, map_mul, map_natCast]
  have h3 : ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∣ ((((Pr.T u : ℕ) : ℤ) - 1 : ℤ) : 𝓞 X.E) := by
    refine ⟨y + X.conjO y + ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) * (y * X.conjO y), ?_⟩
    rw [Int.cast_sub, Int.cast_one, Int.cast_natCast, ← hPr.piT_norm u, h2]
    nth_rewrite 1 [h1]
    ring
  have h4 := Primes.natCast_dvd_intCast h3
  exact (Nat.modEq_iff_dvd.2 h4).symm

theorem Primes.Ok.two_lt_alt (hPr : Pr.Ok) (u : Pr.Word) : 2 < Pr.T u := by
  by_contra hcon
  have h2 : Pr.T u = 2 := le_antisymm (not_lt.mp hcon) (hPr.T_prime u).two_le
  have h3 := hPr.T_modEq u
  rw [h2] at h3
  have h4 : Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 ∣ 2 - 1 := (Nat.modEq_iff_dvd' (by norm_num)).1 h3.symm
  have h5 : Pr.g 0 ∣ 1 :=
    dvd_trans (dvd_trans (Dvd.intro _ rfl) (dvd_trans (dvd_pow_self _ (by norm_num)) (Dvd.intro_left _ rfl))) h4
  exact (hPr.g_prime 0).one_lt.ne' (Nat.dvd_one.1 h5)

end TBig

section Gen

open GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}


end Gen

section ColsRam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)








end ColsRam

section Delta

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem GSD.exists_delta (h : S.Ok) (hf : S.Free) (d0 : S.D) (v : S.V) :
    ∃ φ : S.EqFun, (φ : S.D → S.V) d0 = v ∧ ∀ d, S.cls d ≠ S.cls d0 → (φ : S.D → S.V) d = 0 := by
  classical
  let s := S.outSec
  let φ : S.EqFun := (S.resFree h s hf).symm (Pi.single (S.cls d0) (S.ρ (s.mv d0)⁻¹ v))
  have hφ : ∀ c, (φ : S.D → S.V) (s.rep c) = (Pi.single (S.cls d0) (S.ρ (s.mv d0)⁻¹ v) : S.Cl → S.V) c := by
    intro c
    rw [← S.resFree_apply h s hf φ c, LinearEquiv.apply_symm_apply]
  have hval : ∀ d, (φ : S.D → S.V) d =
      S.ρ (s.mv d) ((Pi.single (S.cls d0) (S.ρ (s.mv d0)⁻¹ v) : S.Cl → S.V) (S.cls d)) := by
    intro d
    have h1 := φ.2 (s.mv d) (s.rep (S.cls d))
    rw [s.mv_smul, hφ] at h1
    exact h1
  refine ⟨φ, ?_, ?_⟩
  · rw [hval, Pi.single_eq_same, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · intro d hd
    rw [hval, Pi.single_eq_of_ne hd, map_zero]


end Delta

section ColsUD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)






end ColsUD

section SeenEx

variable {X : Fields} {Pr : Primes X}


end SeenEx

section Pos

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def GSD.pairEmb (σ : K →+* ℂ) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)


theorem GSD.map_pair (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) :
    σ (S.pair x y) = S.pairEmb σ x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, map_mul, hσ, GSD.pairEmb, GSD.gramV, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem GSD.pairEmb_pos (σ : K →+* ℂ) (hG : (S.gramV.map σ).PosDef) {x : S.V} (hx : x ≠ 0) : 0 < S.pairEmb σ x x := by
  have hne : (fun i => σ (S.bV.repr x i)) ≠ 0 := by
    intro h0
    apply hx
    apply S.bV.repr.injective
    ext i
    have := congrFun h0 i
    simpa using this
  have h1 := hG.dotProduct_mulVec_pos hne
  have e : star (fun i => σ (S.bV.repr x i)) ⬝ᵥ (S.gramV.map σ).mulVec (fun i => σ (S.bV.repr x i)) = S.pairEmb σ x x := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, GSD.pairEmb, Finset.mul_sum,
      starRingEnd_apply, mul_assoc]
  rwa [e] at h1

theorem GSD.pairEmb_nonneg (σ : K →+* ℂ) (hG : (S.gramV.map σ).PosDef) (x : S.V) : 0 ≤ S.pairEmb σ x x := by
  by_cases hx : x = 0
  · subst hx
    simp [GSD.pairEmb]
  · exact le_of_lt (S.pairEmb_pos σ hG hx)

theorem GSD.exists_rep_ne (s : S.Sec) {φ : S.EqFun} (hφ : φ ≠ 0) : ∃ c, (φ : S.D → S.V) (s.rep c) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hφ
  apply Subtype.ext
  funext d
  have h1 := φ.2 (s.mv d) (s.rep (S.cls d))
  rw [s.mv_smul, hcon, map_zero] at h1
  exact h1

def GSD.ipEmb (h : S.Ok) (σ : K →+* ℂ) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairEmb σ (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

theorem GSD.ipAt_eq_ipEmb (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = S.ipEmb h v.embedding φ ψ := rfl

theorem GSD.ipEmb_pos (h : S.Ok) (σ : K →+* ℂ) (hG : (S.gramV.map σ).PosDef) {φ : S.EqFun} (hφ : φ ≠ 0) :
    0 < S.ipEmb h σ φ φ := by
  let _ : Fintype S.Cl := h.fintypeCl
  obtain ⟨c0, hc0⟩ := S.exists_rep_ne S.outSec hφ
  have hw : ∀ c : S.Cl, (0 : ℂ) < (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ := by
    intro c
    have h1 : 0 < (S.toCSD h).wt c := by
      rw [S.wt_eq]
      have := h.fin_stab (S.outSec.rep c)
      exact Nat.card_pos
    have h2 : (0 : ℂ) < (((S.toCSD h).wt c : ℕ) : ℂ) := by exact_mod_cast h1
    exact inv_pos.mpr h2
  unfold GSD.ipEmb
  exact Finset.sum_pos' (fun c _ => mul_nonneg (hw c).le (S.pairEmb_nonneg σ hG _))
    ⟨c0, Finset.mem_univ _, mul_pos (hw c0) (S.pairEmb_pos σ hG hc0)⟩

theorem GSD.map_ip (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (φ ψ : S.D → S.V) :
    σ (S.ip h φ ψ) = S.ipEmb h σ φ ψ := by
  let _ : Fintype S.Cl := h.fintypeCl
  unfold GSD.ip GSD.ipOf GSD.ipEmb CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  congr 1
  exact S.map_pair σ hσ _ _

theorem GSD.ip_pos (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    (hG : (S.gramV.map σ).PosDef) {φ : S.EqFun} (hφ : φ ≠ 0) : 0 < σ (S.ip h φ φ) := by
  rw [S.map_ip h σ hσ]
  exact S.ipEmb_pos h σ hG hφ

end Pos

section ColPos

open ComplexOrder

variable {X : Fields}

theorem nd_gramKd_one (n : ℕ) (τ : X.Tau) : gramKd X.emb (1 : Matrix (Fin n) (Fin n) X.E) τ = 1 := by
  unfold gramKd
  rw [Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]


theorem roundPk_gram_pos {n : ℕ} (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n))
    (σ : X.K →+* ℂ) :
    (Matrix.of fun i j : VVIdx lam => σ ((roundPk X lam L).pair (bVV X.K lam i) (bVV X.K lam j))).PosDef := by
  refine pairPos X.K X.Tau n lam (gramKd X.emb 1) σ fun τ => ?_
  rw [nd_gramKd_one, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.PosDef.one


variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)





end ColPos

section LatGen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]



end LatGen

section ColLat

variable {X : Fields}



variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)









end ColLat

section Cert

def ndPowMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | f + 1, a, e => (if e % 2 = 1 then a else 1) * ndPowMod m f (a * a % m) (e / 2) % m

theorem ndPowMod_spec (m : ℕ) : ∀ f a e : ℕ, e < 2 ^ f → ndPowMod m f a e ≡ a ^ e [MOD m] := by
  intro f
  induction f with
  | zero =>
    intro a e he
    have : e = 0 := by simpa using he
    subst this
    simp only [ndPowMod, pow_zero]
    exact Nat.ModEq.refl _
  | succ f ih =>
    intro a e he
    have he2 : e / 2 < 2 ^ f := by
      rw [pow_succ] at he
      omega
    have h1 := ih (a * a % m) (e / 2) he2
    have h2 : (a * a % m) ^ (e / 2) ≡ (a * a) ^ (e / 2) [MOD m] := (Nat.mod_modEq _ _).pow _
    have h3 : a ^ e = (if e % 2 = 1 then a else 1) * (a * a) ^ (e / 2) := by
      conv_lhs => rw [← Nat.mod_add_div e 2]
      rw [pow_add, pow_mul]
      split_ifs with h
      · simp [h, sq]
      · have h0 : e % 2 = 0 := by omega
        simp [h0, sq]
    rw [h3]
    simp only [ndPowMod]
    exact (Nat.mod_modEq _ _).trans ((h1.trans h2).mul_left _)

theorem ndPowMod_zmod (m f a e c : ℕ) (he : e < 2 ^ f) (hc : ndPowMod m f a e = c) :
    ((a : ℕ) : ZMod m) ^ e = ((c : ℕ) : ZMod m) := by
  rw [← Nat.cast_pow, ← hc]
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mpr (ndPowMod_spec m f a e he)).symm

private theorem prime_seven_hundred_trillion_example_lemma : ∀ e c : ℕ, e < 2 ^ 50 → ndPowMod 763521676554817 50 5 e = c →
    (5 : ZMod 763521676554817) ^ e = (c : ZMod 763521676554817) := by
  intro e c he hc
  have := ndPowMod_zmod 763521676554817 50 5 e c he hc
  simpa using this

private theorem prime_seven_hundred_trillion_example_lemma_2 : (5 : ZMod 763521676554817) ^ 763521676554816 = 1 :=
  (prime_seven_hundred_trillion_example_lemma 763521676554816 1 (by norm_num) (by decide)).trans Nat.cast_one

private theorem prime_seven_hundred_trillion_example_lemma_3 : (5 : ZMod 763521676554817) ^ 381760838277408 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 381760838277408 763521676554816 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 763521676554816 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

private theorem prime_seven_hundred_trillion_example_lemma_4 : (5 : ZMod 763521676554817) ^ 254507225518272 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 254507225518272 381849785353851 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 381849785353851 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

private theorem prime_seven_hundred_trillion_example_lemma_5 : (5 : ZMod 763521676554817) ^ 26328333674304 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 26328333674304 635982050010579 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 635982050010579 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

private theorem prime_seven_hundred_trillion_example_lemma_6 : (5 : ZMod 763521676554817) ^ 20635720987968 ≠ 1 := by
  rw [prime_seven_hundred_trillion_example_lemma 20635720987968 699479234267360 (by norm_num) (by decide)]
  intro h
  have h' := (ZMod.natCast_eq_natCast_iff' 699479234267360 1 763521676554817).mp (h.trans Nat.cast_one.symm)
  norm_num at h'

theorem prime_seven_hundred_trillion_example : Nat.Prime 763521676554817 := by
  refine lucas_primality 763521676554817 5 prime_seven_hundred_trillion_example_lemma_2 ?_
  intro q hq hqd
  have hq' : q = 2 ∨ q = 3 ∨ q = 29 ∨ q = 37 := by
    have hqd' : q ∣ 2 ^ 6 * 3 ^ 2 * 29 ^ 4 * 37 ^ 4 := by
      have e : (763521676554817 - 1 : ℕ) = 2 ^ 6 * 3 ^ 2 * 29 ^ 4 * 37 ^ 4 := by norm_num
      rwa [e] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd' with h | h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    · right; left
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)
    · right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
    · right; right; right
      exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
  rcases hq' with rfl | rfl | rfl | rfl
  · exact prime_seven_hundred_trillion_example_lemma_3
  · exact prime_seven_hundred_trillion_example_lemma_4
  · exact prime_seven_hundred_trillion_example_lemma_5
  · exact prime_seven_hundred_trillion_example_lemma_6

end Cert

section GaussInst

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

theorem gaussChars_of (Pr : Primes (gaussFields ι LL hE)) (hPr : Pr.Ok) {N : ℕ} (hN : 0 < N) (h1 : ∀ i, Pr.g i ∣ N)
    (h2 : ∀ i, Pr.g i - 1 ∣ N) (h3 : ∀ i, Pr.g i ≠ 2) (h4 : ∀ i, (2 : ZMod (Pr.g i)) ^ 2 ≠ 2 ^ 4) (hLL : cycQ N ≤ LL) :
    ∃ Ch : Chars (gaussFields ι LL hE) Pr 2, Ch.Ok := by
  classical
  have hi : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i := by
    intro w
    have hw := w.2
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have key : ∀ w : {w // w ∈ Pr.vGs},
      ∃ ψ : AddChar (𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal) (CoF ι LL), ψ ≠ 1 := by
    intro w
    obtain ⟨i, hw⟩ := hi w
    exact (chars_at ι LL hE w.1 hN (hPr.g_prime i) (h3 i) (hPr.vG_norm i w.1 hw) (h1 i) (h2 i) hLL).1
  have hf : ∀ i, ∃ φ : (ZMod (Pr.g i))ˣ →* (CoF ι LL)ˣ, Function.Injective φ := by
    intro i
    have : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
    have hex : Monoid.exponent (ZMod (Pr.g i))ˣ ∣ N := by
      refine dvd_trans ?_ (h2 i)
      rw [← ZMod.card_units (Pr.g i)]
      exact Group.exponent_dvd_card
    have := hasEnoughRoots ι LL hN hex hLL
    exact exists_faithful _ _
  let om : ∀ q : ℕ, (ZMod q)ˣ →* (CoF ι LL)ˣ := fun q =>
    if h : ∃ φ : (ZMod q)ˣ →* (CoF ι LL)ˣ, Function.Injective φ then h.choose else 1
  have hom : ∀ i, Function.Injective (om (Pr.g i)) := by
    intro i
    have e : om (Pr.g i) = (hf i).choose := dif_pos (hf i)
    rw [e]
    exact (hf i).choose_spec
  have keyχ : ∀ w : {w // w ∈ Pr.vGs},
      ∃ χ : Fin 2 → ((𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal)ˣ →* (CoF ι LL)ˣ), Function.Injective χ ∧
        ∀ q : ℕ, Ideal.absNorm w.1.asIdeal = q → ∀ (j : Fin 2) (a : (ZMod q)ˣ)
          (x : (𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal)ˣ),
          (x : 𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal) =
            (((a : ZMod q).val : ℕ) : 𝓞 (gaussFields ι LL hE).E ⧸ w.1.asIdeal) →
          χ j x = om q a ^ (2 * (j.1 + 1)) := by
    intro w
    obtain ⟨i, hw⟩ := hi w
    exact chi_at ι LL hE w.1 (hPr.g_prime i) (hPr.vG_norm i w.1 hw)
      ((Nat.coprime_primes Nat.prime_two (hPr.g_prime i)).2 (h3 i).symm) (h4 i) om (hom i)
  have one : ∀ (i : Fin 2) (w w' : {w // w ∈ Pr.vGs}), w.1 ∈ Pr.vG i → w'.1 ∈ Pr.vG i → w = w' := by
    intro i w w' hw hw'
    obtain ⟨P, hP⟩ := Finset.card_eq_one.1 ((hPr.vG_card i).trans (gauss_f ι LL hE))
    rw [hP, Finset.mem_singleton] at hw hw'
    exact Subtype.ext (hw.trans hw'.symm)
  choose ψ hψ using key
  choose χ hχ using keyχ
  refine ⟨{ psi0 := ψ, chi := fun j w => χ w j, muVal := fun _ _ => 1, etaVal := fun _ => 1 },
    hψ, fun w => (hχ w).1, ?_, ?_, ?_⟩
  · intro i w w' hw hw' j a x x' hx hx'
    obtain rfl : w = w' := one i w w' hw hw'
    obtain rfl : x = x' := Units.ext (hx.trans hx'.symm)
    rfl
  · intro i w w' hw hw' a
    obtain rfl : w = w' := one i w w' hw hw'
    rfl
  · intro i
    exact ⟨om _, hom i, fun w hw j a x hx => (hχ w).2 _ (hPr.vG_norm i w.1 hw) j a x hx⟩

theorem gaussCharT_of (Pr : Primes (gaussFields ι LL hE)) (hPr : Pr.Ok) {N : ℕ} (hN : 0 < N) (hd : ∀ u, Pr.T u ∣ N)
    (hLL : cycQ N ≤ LL) : ∃ Ps : CharT (gaussFields ι LL hE) Pr, Ps.Ok := by
  classical
  have key : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}),
      ∃ ψ : AddChar (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) (CoF ι LL), ψ ≠ 1 := by
    intro u P
    have hfin : Finite (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) :=
      Ideal.finiteQuotientOfFreeOfNeBot P.1.asIdeal P.1.ne_bot
    let _ : Field (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) := Ideal.Quotient.field P.1.asIdeal
    have hcard : Nat.card (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal) = Pr.T u := by
      rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hex : Monoid.exponent (Multiplicative (𝓞 (gaussFields ι LL hE).E ⧸ P.1.asIdeal)) ∣ N := by
      refine dvd_trans ?_ (hd u)
      rw [← hcard]
      exact Group.exponent_dvd_nat_card
    have := hasEnoughRoots ι LL hN hex hLL
    exact exists_addChar_ne
  choose ψ hψ using key
  refine ⟨⟨ψ⟩, hψ, ?_⟩
  intro u P P' a
  obtain ⟨Q, hQ⟩ := Finset.card_eq_one.1 ((hPr.vT_card u).trans (gauss_f ι LL hE))
  have h1 : P.1 = Q := Finset.mem_singleton.1 (hQ ▸ P.2)
  have h2 : P'.1 = Q := Finset.mem_singleton.1 (hQ ▸ P'.2)
  obtain rfl : P = P' := Subtype.ext (h1.trans h2.symm)
  rfl

def gaussianPrimesLarge : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![29, 37]
  piG := ![gz ι LL hE 5 2, gz ι LL hE 6 1]
  Word := Unit
  T := fun _ => 763521676554817
  piT := fun _ => gz ι LL hE 1 27631896

theorem gaussianPrimesLarge_ok : (gaussianPrimesLarge ι LL hE).Ok := by
  have n0 := gz_norm ι LL hE 5 2 29 (by norm_num)
  have n1 := gz_norm ι LL hE 6 1 37 (by norm_num)
  have nT := gz_norm ι LL hE 1 27631896 763521676554817 (by norm_num)
  have p0 : Nat.Prime 29 := by norm_num
  have p1 : Nat.Prime 37 := by norm_num
  have hr := gauss_rank ι LL hE
  have hf := gauss_f ι LL hE
  exact
    { g_prime := Fin.forall_fin_two.2 ⟨p0, p1⟩
      piG_Kq := fun _ => gauss_Kq ι LL hE _
      piG_norm := Fin.forall_fin_two.2 ⟨n0, n1⟩
      piG_cop := Fin.forall_fin_two.2 ⟨gz_cop ι LL hE 5 2 3 (-1) (by norm_num), gz_cop ι LL hE 6 1 (-3) 1 (by norm_num)⟩
      vG_card := Fin.forall_fin_two.2
        ⟨(card_divs_of_norm _ hr p0 (conj_norm _ n0)).trans hf.symm, (card_divs_of_norm _ hr p1 (conj_norm _ n1)).trans hf.symm⟩
      vG_norm := Fin.forall_fin_two.2
        ⟨norm_divs_of_norm _ hr p0 (conj_norm _ n0), norm_divs_of_norm _ hr p1 (conj_norm _ n1)⟩
      g_cong := Fin.forall_fin_two.2 ⟨(by decide : 29 ≡ 1 [MOD 4]), (by decide : 37 ≡ 1 [MOD 4])⟩
      g_ne := (by decide : (29 : ℕ) ≠ 37)
      T_prime := fun _ => prime_seven_hundred_trillion_example
      piT_Kq := fun _ => gauss_Kq ι LL hE _
      piT_norm := fun _ => nT
      piT_cop := fun _ => gz_cop ι LL hE 1 27631896 (-381760838277408) 1 (by norm_num)
      vT_card := fun _ => (card_divs_of_norm _ hr prime_seven_hundred_trillion_example nT).trans hf.symm
      vT_norm := fun _ => norm_divs_of_norm _ hr prime_seven_hundred_trillion_example nT
      piT_cong := fun _ => by
        have e : (gaussianPrimesLarge ι LL hE).cond * ((gaussianPrimesLarge ι LL hE).g 0 * (gaussianPrimesLarge ι LL hE).g 1) ^ 2 = 4605316 := by
          show 4 * (29 * 37) ^ 2 = 4605316
          norm_num
        rw [e]
        refine ⟨gz ι LL hE 0 6, ?_⟩
        show gz ι LL hE 1 27631896 - 1 = _
        unfold gz
        push_cast
        ring
      T_ne_g := fun _ => Fin.forall_fin_two.2
        ⟨(by norm_num : (763521676554817 : ℕ) ≠ 29), (by norm_num : (763521676554817 : ℕ) ≠ 37)⟩ }

end GaussInst

def exampleTopWeights (X : Fields) (Word : Type) : Wts X Word Examples₂.R0 where
  row := fun _ => RowPar.of Examples₂.hc0
  hc := fun _ _ => Examples₂.hc0
  tops := Finset.univ



def ndN : ℕ := 4 * 51613301813429074383

theorem ndN_pos : 0 < ndN := by
  unfold ndN
  norm_num

theorem gaussianRationals_le_cyclotomic_four_mul (M : ℕ) : KQ 1 ≤ cycQ (4 * M) := by
  unfold KQ sqQ cycQ
  apply IntermediateField.adjoin.mono
  intro z hz
  have h : z ^ 2 = -1 := by
    have h1 : z ^ 2 = ((-((1 : ℕ) : ℤ) : ℤ) : Qb) := hz
    rw [h1]; simp
  show z ^ (4 * M) = 1
  rw [show 4 * M = 2 * (2 * M) by ring, pow_mul, h, pow_mul]
  simp

theorem gaussianRationals_le_cyclotomic_level : KQ 1 ≤ cycQ ndN := by
  exact gaussianRationals_le_cyclotomic_four_mul 51613301813429074383

instance fin_cycNd : FiniteDimensional ℚ (cycQ ndN) := fin_adjoin (finite_pow_eq ndN ndN_pos 1)

instance normal_cycNd : Normal ℚ (cycQ ndN) := normal_adjoin fun s x hx => by
  show (s x) ^ ndN = 1
  rw [← map_pow, show x ^ ndN = 1 from hx, map_one]

def ndIota : Qb →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

def ndX : Fields := gaussFields ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

def ndPr : Primes ndX := gaussianPrimesLarge ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level

def ndW : Wts ndX ndPr.Word Examples₂.R0 := exampleTopWeights _ _


theorem ndPr_ok : ndPr.Ok := gaussianPrimesLarge_ok ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level






theorem ndCh_exists : ∃ Ch : Chars ndX ndPr Examples₂.R0.m, Ch.Ok :=
  gaussChars_of ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level _ ndPr_ok ndN_pos
    (Fin.forall_fin_two.2 ⟨(by unfold ndN; norm_num : 29 ∣ ndN), (by unfold ndN; norm_num : 37 ∣ ndN)⟩)
    (Fin.forall_fin_two.2 ⟨(by unfold ndN; norm_num : 29 - 1 ∣ ndN), (by unfold ndN; norm_num : 37 - 1 ∣ ndN)⟩)
    (Fin.forall_fin_two.2 ⟨(by norm_num : (29 : ℕ) ≠ 2), (by norm_num : (37 : ℕ) ≠ 2)⟩)
    (Fin.forall_fin_two.2 ⟨(by decide : (2 : ZMod 29) ^ 2 ≠ 2 ^ 4), (by decide : (2 : ZMod 37) ^ 2 ≠ 2 ^ 4)⟩) le_rfl

theorem ndPs_exists : ∃ Ps : CharT ndX ndPr, Ps.Ok :=
  gaussCharT_of ndIota (cycQ ndN) gaussianRationals_le_cyclotomic_level _ ndPr_ok ndN_pos
    (fun _ => (by unfold ndN; norm_num : 763521676554817 ∣ ndN)) le_rfl

def ndCh : Chars ndX ndPr Examples₂.R0.m := ndCh_exists.choose


def ndPs : CharT ndX ndPr := ndPs_exists.choose


section OfSizes

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)


end OfSizes

section InstThms

open ComplexOrder








end InstThms

end Formalism.L2.Col
end
end
