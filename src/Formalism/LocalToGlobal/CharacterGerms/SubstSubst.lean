import Formalism.LocalToGlobal.CharacterGerms.RowTieVal
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.FrobeniusBaseCase.BaseCaseFalseGeneral
import Formalism.IncomingBounds.FlowDegreeBounds.ThmPJet
import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def expAll (x : Fin dd) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun i : Fin dd => ∑ w : WVO I, (p w.1).u w.2.1 w.2.2 i •
    (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (un1 (Y.ex x))

def pull1 (F : PS C 1 dd) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) F

def rowOf {n : ℕ} (b : Fin n) (F : MvPowerSeries (WVO I) C) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) F

def pullN {n : ℕ} (F : PS C n dd) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) F

def toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) F

def LogCoordSt : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (Q : MvPolynomial (Fin n × WVO I) C), IsImgO (fun o => Y.raw (p o)) cp uv P Q →
    ∀ F : PS C n dd, MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) = jetAt0 Q (pullN Y p F)

def UnitSt : Prop :=
  PairsSep Y p → ∃ U : PS C 1 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p U * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow)

def GermLiftSt (H : ∀ o, (Y.raw (p o)).Hyps V) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.raw (p o)).rowData (H o)).G g))
    (t : ∀ g, I o g → MvPowerSeries (I o g) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 1 dd, IntS V G ∧ pull1 Y p G = toAllS o F

end Defs

def LeafSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (H : X.Hyps V) (n : ℕ) (Po : MvPolynomial (Fin n × WV I) C)
    (kind : Fin n → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt Po kind →
    ∀ gr : Fin n → MvPowerSeries (WV I) C,
      jetAt0 Po (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) = ValOf (X.rowData H).hL Po kind gr

def ValEqPFromCutsSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ),
    LogCoordSt Y p → UnitSt Y p → GermLiftSt Y p H → LeafSt → ValEqPSt Y p H Ls n

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section EqOn

variable {K : Type} [Field K] {σ : Type}

def EqOn (A : Set σ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ μ : σ →₀ ℕ, (↑μ.support : Set σ) ⊆ A → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G

theorem EqOn.refl (A : Set σ) (F : MvPowerSeries σ K) : EqOn A F F := fun _ _ => rfl

theorem EqOn.mul {A : Set σ} {F G F' G' : MvPowerSeries σ K} (h : EqOn A F G) (h' : EqOn A F' G') :
    EqOn A (F * F') (G * G') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hs : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have h1 : (↑p.1.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.1 ≤ μ := hs ▸ le_self_add
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  have h2 : (↑p.2.support : Set σ) ⊆ A := fun x hx => hμ (by
    have : p.2 ≤ μ := hs ▸ le_add_self
    exact Finset.mem_coe.2 (Finsupp.support_mono this (Finset.mem_coe.1 hx)))
  rw [h p.1 h1, h' p.2 h2]

theorem EqOn.pow {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (k : ℕ) : EqOn A (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem EqOn.prod {A : Set σ} {ι : Type} (s : Finset ι) {F G : ι → MvPowerSeries σ K}
    (h : ∀ i ∈ s, EqOn A (F i) (G i)) : EqOn A (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem EqOn.mvExp {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) : EqOn A (mvExp F) (mvExp G) := by
  intro μ hμ
  show ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : K) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (G ^ k) / (k.factorial : K)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem EqOn.jet {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) (P : MvPolynomial σ K)
    (hP : ∀ μ ∈ P.support, (↑μ.support : Set σ) ⊆ A) : jetAt0 P F = jetAt0 P G := by
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [h μ (hP μ hμ)]

theorem EqOn.rename {τ : Type} (e : σ ↪ τ) {A : Set τ} {F G : MvPowerSeries σ K}
    (h : ∀ μ : σ →₀ ℕ, (∀ x ∈ μ.support, e x ∈ A) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ G) :
    EqOn A (MvPowerSeries.rename e F) (MvPowerSeries.rename e G) := by
  intro ν hν
  by_cases hr : ν ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨μ, rfl⟩ := hr
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename,
      MvPowerSeries.coeff_embDomain_rename]
    refine h μ fun x hx => hν ?_
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
    exact Finset.mem_coe.2 (Finset.mem_map_of_mem e hx)
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ hr, MvPowerSeries.coeff_rename_eq_zero _ _ hr]

end EqOn

theorem leaf_holds : LeafSt := by
  intro C _ V d _ I _ κ _ X H n Po kind hk gr
  rw [rtj_valOf]
  set A : Set (Fin n × WV I) := {x | ∃ μ ∈ Po.support, μ x ≠ 0} with hA
  refine EqOn.jet (A := A) ?_ Po fun μ hμ x hx => ⟨μ, hμ, Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hx)⟩
  refine EqOn.prod _ fun ρ _ => (EqOn.refl A _).mul (EqOn.mvExp ?_)
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq]
  refine EqOn.rename (rtjR ρ) fun μ hμ => ?_
  cases hkd : kind ρ with
  | none =>
    obtain ⟨g, hg⟩ := hk.2 ρ hkd
    have h1 : ∀ w ∈ μ.support, w.1 = g := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact hg μ' hμ' w hne
    have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
      fin_cases g
      · exact Or.inl h1
      · exact Or.inr h1
    rw [H.axes μ h2]
    simp [rtjH]
  | some q =>
    obtain ⟨g, a, a'⟩ := q
    have h1 : ∀ w ∈ μ.support, X.OnLf g a a' w := fun w hw => by
      obtain ⟨μ', hμ', hne⟩ := hμ w hw
      exact (hk.1 ρ g a a' hkd).2.2 μ' hμ' w hne
    show MvPowerSeries.coeff μ X.hRow =
      (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0)
    rw [if_pos h1]

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.BaseCaseIdentities (OrdGE NoConst)

section General

variable {C : Type*} [Field C] {σ τ : Type*}

theorem ordGE_one_iff (f : MvPowerSeries τ C) : OrdGE 1 f ↔ constantCoeff f = 0 := by
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h A hA
    have hA0 : A = 0 := by
      have : A.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff A).1 this
    subst hA0
    simpa using h

theorem ordGE_zero (f : MvPowerSeries τ C) : OrdGE 0 f := fun _ h => absurd h (Nat.not_lt_zero _)

theorem ordGE_finset_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → MvPowerSeries τ C)
    (h : ∀ i ∈ s, OrdGE (n i) (f i)) : OrdGE (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using ordGE_zero (1 : MvPowerSeries τ C)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Formalism.BaseCaseIdentities.OrdGE.mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ordGE_finsupp_prod (a : σ → MvPowerSeries τ C) (ha : ∀ s, OrdGE 1 (a s)) (d : σ →₀ ℕ) :
    OrdGE d.degree (d.prod fun s n => a s ^ n) := by
  have h := ordGE_finset_prod d.support (fun s => d s) (fun s => a s ^ d s)
    (fun s _ => Formalism.BaseCaseIdentities.OrdGE.pow (ha s) (d s))
  exact h

theorem hasSubst_of_ordGE [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) :
    HasSubst a := hasSubst_of_constantCoeff_zero fun s => (ordGE_one_iff _).1 (ha s)

theorem coeff_subst_congr [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F G : MvPowerSeries σ C} {N : ℕ} (h : ∀ d : σ →₀ ℕ, d.degree ≤ N → coeff d F = coeff d G)
    (e : τ →₀ ℕ) (he : e.degree ≤ N) : coeff e (subst a F) = coeff e (subst a G) := by
  rw [coeff_subst (hasSubst_of_ordGE ha), coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree ≤ N
  · rw [h d hd]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero, smul_zero]

theorem ordGE_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE n F) : OrdGE n (subst a F) := by
  intro e he
  rw [coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d.degree < n
  · rw [hF d hd, zero_smul]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero]

def killV (P : σ → Prop) (F : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ w ∈ μ.support, P w then coeff μ F else 0



theorem dVar_eq_pderiv {C : Type} [Field C] {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = pderiv C w F := by
  ext μ
  rw [coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem ordGE_pderiv {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE (n + 1) F) (w : σ) :
    OrdGE n (pderiv C w F) := by
  intro e he
  rw [coeff_pderiv, hF _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

theorem pderiv_subst_coe [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (b : τ)
    (p : MvPolynomial σ C) :
    pderiv C b (subst a (p : MvPowerSeries σ C)) =
      ∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C)) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.coe_C]
    have : subst a (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
      rw [← substAlgHom_apply ha]
      exact (substAlgHom ha).commutes r
    rw [this, pderiv_C]
    symm
    refine Finset.sum_eq_zero fun w _ => ?_
    have h0 : subst a (0 : MvPowerSeries σ C) = 0 := by
      rw [← substAlgHom_apply ha, map_zero]
    rw [pderiv_C, h0, mul_zero]
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_add, subst_add ha, mul_add]
  | mul_X p w0 hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha, Derivation.leibniz, hp]
    have h1 : ∀ w, pderiv C b (a w) * subst a (pderiv C w ((p : MvPowerSeries σ C) * X w0)) =
        a w0 * (pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
          (if w = w0 then pderiv C b (a w0) * subst a (p : MvPowerSeries σ C) else 0) := by
      intro w
      rw [Derivation.leibniz, subst_add ha, smul_eq_mul, smul_eq_mul, subst_mul ha, subst_mul ha,
        subst_X ha]
      by_cases hw : w = w0
      · subst hw
        rw [pderiv_X_self, if_pos rfl]
        have : subst a (1 : MvPowerSeries σ C) = 1 := by
          rw [← substAlgHom_apply ha, map_one]
        rw [this]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hw), if_neg hw]
        have : subst a (0 : MvPowerSeries σ C) = 0 := by
          rw [← substAlgHom_apply ha, map_zero]
        rw [this]
        ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ w0, if_pos (Finset.mem_univ _),
      ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (b : τ)
    (H : MvPowerSeries σ C) :
    pderiv C b (subst a H) = ∑ w, pderiv C b (a w) * subst a (pderiv C w H) := by
  have hs := hasSubst_of_ordGE ha
  ext e
  obtain ⟨p, hp⟩ : ∃ p : MvPolynomial σ C, p = truncTotal (e.degree + 2) H := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : MvPowerSeries σ C, R = H - (p : MvPowerSeries σ C) := ⟨_, rfl⟩
  have hRo : OrdGE (e.degree + 2) R := by
    intro d hd
    rw [hR, map_sub, MvPolynomial.coeff_coe, hp, coeff_truncTotal _ hd, sub_self]
  have hH : H = (p : MvPowerSeries σ C) + R := by rw [hR]; ring
  have hL : coeff e (pderiv C b (subst a R)) = 0 :=
    ordGE_pderiv (n := e.degree + 1) (ordGE_subst ha hRo) b e (by omega)
  have hRr : coeff e (∑ w, pderiv C b (a w) * subst a (pderiv C w R)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have h1 : OrdGE (0 + (e.degree + 1)) (pderiv C b (a w) * subst a (pderiv C w R)) :=
      Formalism.BaseCaseIdentities.OrdGE.mul (ordGE_zero _) (ordGE_subst ha (ordGE_pderiv (n := e.degree + 1) hRo w))
    exact h1 e (by omega)
  have hsum : ∑ w, pderiv C b (a w) * subst a (pderiv C w H) =
      (∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
        ∑ w, pderiv C b (a w) * subst a (pderiv C w R) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hH, map_add, subst_add hs, mul_add]
  rw [hsum, map_add, hRr, add_zero, ← pderiv_subst_coe hs, hH, subst_add hs, map_add, map_add, hL,
    add_zero]

end General

section Lin

variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

def linS (M : τ → σ → C) : σ → MvPowerSeries τ C := fun w => ∑ c, M c w • (X c : MvPowerSeries τ C)

theorem ordGE_linS (M : τ → σ → C) (w : σ) : OrdGE 1 (linS M w) := by
  unfold linS
  refine Formalism.BaseCaseIdentities.OrdGE.sum _ fun c _ => ?_
  rw [smul_eq_C_mul]
  exact Formalism.BaseCaseIdentities.OrdGE.C_mul _ (Formalism.BaseCaseIdentities.OrdGE.X c)

theorem hasSubst_linS [Finite σ] (M : τ → σ → C) : HasSubst (linS M) :=
  hasSubst_of_ordGE (ordGE_linS M)












theorem pderiv_linS (M : τ → σ → C) (b : τ) (w : σ) :
    pderiv C b (linS M w) = MvPowerSeries.C (M b w) := by
  unfold linS
  rw [map_sum, Finset.sum_eq_single b]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, pderiv_X_of_ne hc, smul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem pderiv_subst_linS [Fintype σ] (M : τ → σ → C) (b : τ) (H : MvPowerSeries σ C) :
    pderiv C b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (pderiv C w H) := by
  rw [pderiv_subst (ordGE_linS M)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pderiv_linS, smul_eq_C_mul]



end Lin


section Rows

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem one_sub_ne (g : Fin 2) : 1 - g ≠ g := by revert g; decide

theorem finset_fin_two_eq_cases (g g' : Fin 2) : g' = g ∨ g' = 1 - g := by revert g g'; decide

theorem toW_same (g : Fin 2) (u : I g → C) (x : I g) : toW g u (⟨g, x⟩ : WV I) = u x := by
  simp [toW]

theorem toW_other (g g' : Fin 2) (h : g' ≠ g) (u : I g → C) (x : I g') :
    toW g u (⟨g', x⟩ : WV I) = 0 := by
  simp [toW, h]

def rowM (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) : ι ⊕ ι' → WV I → C :=
  Sum.elim (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))

theorem hPullW_eq (H : MvPowerSeries (WV I) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) :
    hPullW H (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = subst (linS (rowM g e v')) H := by
  unfold hPullW
  congr 1
  funext w
  unfold linS rowM
  rw [Fintype.sum_sum_type]
  rfl



theorem rename_subst_linS {σ τ τ' : Type} [Fintype σ] [Fintype τ] (f : τ ↪ τ') (M : τ → σ → C)
    (F : MvPowerSeries σ C) :
    rename f (subst (linS M) F) = subst (fun x => rename f (linS M x)) F := by
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_linS M) (HasSubst.X_comp _)]
  congr 1
  funext x
  rw [rename_eq_subst]





end Rows

section Bridge

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)

theorem Sys.al_zeroM (c k : I) : S.al c 0 k = S.tan c k := by
  unfold Sys.al
  rw [(S.curve c).2.1]
  rfl

theorem Sys.det_ne_zero : (Matrix.of fun c k : I => S.al c 0 k).det ≠ 0 := by
  intro h
  have h1 := S.unimod
  have h2 : (Matrix.of fun c k : I => S.al c 0 k) = Matrix.of S.tan := by
    ext c k
    exact S.al_zeroM c k
  rw [← h2, h, V.v.map_zero] at h1
  exact WithTop.top_ne_zero h1


theorem coeff_pow_eq_zero_of_lt {τ : Type} {f : MvPowerSeries τ C} (hf : OrdGE 1 f) {l s : ℕ}
    (hl : 1 < l) {μ : τ →₀ ℕ} (h : μ.degree < s) : coeff μ (f ^ (l ^ s)) = 0 :=
  Formalism.BaseCaseIdentities.OrdGE.pow hf _ μ (lt_trans h (Nat.lt_pow_self hl))



variable {τ : Type} [Fintype τ]





end Bridge

section Pull

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem fin_two_eq_one_sub_of_ne {g g' : Fin 2} (h : g' ≠ g) : g' = 1 - g := (finset_fin_two_eq_cases g g').resolve_left h

def rowIdx (g : Fin 2) : WV I → I g ⊕ I (1 - g) := fun w =>
  if h : w.1 = g then Sum.inl (h ▸ w.2) else Sum.inr (fin_two_eq_one_sub_of_ne h ▸ w.2)




def ttPull (t : ∀ g, I g → MvPowerSeries (I g) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : I g ⊕ I (1 - g) → MvPowerSeries (ι ⊕ ι') C :=
  Sum.elim (fun c => rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (subst (linS e) (t g c)))
    (fun c => rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (subst (linS v') (t (1 - g) c)))


theorem constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : constantCoeff F = 0) :
    constantCoeff (upG g F : MvPowerSeries (WV I) C) = 0 := by
  unfold upG
  exact (ordGE_one_iff _).1 (ordGE_subst (fun x => Formalism.BaseCaseIdentities.OrdGE.X _) ((ordGE_one_iff _).2 hF))






end Pull

section RowDataPull

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (Xr : RowData C V d I J) {ι ι' : Type} [Fintype ι]
  [Fintype ι']




end RowDataPull

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)

variable {C : Type} [Field C] {σ τ : Type}


theorem jet_smul_right (P : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 P (a • G) = a * jetAt0 P G := by
  simp only [jetAt0, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring


theorem jet_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ C)
    (G : ι → MvPowerSeries σ C) : jetAt0 P (∑ j ∈ s, G j) = ∑ j ∈ s, jetAt0 P (G j) := by
  simp only [jetAt0, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem jet_C (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a) G = a * constantCoeff G := by
  by_cases ha : a = 0
  · subst ha
    simp [jetAt0]
  · simp [jetAt0, MvPolynomial.support_C, ha, mfact, MvPowerSeries.coeff_zero_eq_constantCoeff]

theorem mfact_add_single (m : σ →₀ ℕ) (x : σ) :
    mfact (m + Finsupp.single x 1) = (m x + 1) * mfact m := by
  unfold mfact
  set s := insert x m.support with hs
  have hsub : (m + Finsupp.single x 1).support ⊆ s := by
    intro y hy
    rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
    · exact Finset.mem_insert_of_mem h
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  rw [Finsupp.prod_of_support_subset (m + Finsupp.single x 1) hsub _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset m (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)]
  have hx : x ∈ s := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase s _ hx, ← Finset.mul_prod_erase s (fun y => (m y).factorial) hx]
  have hrest : ∏ y ∈ s.erase x, ((m + Finsupp.single x 1 : σ →₀ ℕ) y).factorial = ∏ y ∈ s.erase x, (m y).factorial :=
    Finset.prod_congr rfl fun y hy => by
      rw [Finset.mem_erase] at hy
      simp [Finsupp.single_apply, Ne.symm hy.1]
  rw [hrest]
  simp [Nat.factorial_succ]
  ring

theorem jet_mul_X (p : MvPolynomial σ C) (x : σ) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.X x) G = jetAt0 p (dVar x G) := by
  unfold jetAt0
  rw [MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hd : MvPowerSeries.coeff n (dVar x G) =
      ((n x + 1 : ℕ) : C) * MvPowerSeries.coeff (n + Finsupp.single x 1) G := rfl
  simp only [addRightEmbedding_apply]
  rw [MvPolynomial.coeff_mul_X, mfact_add_single, hd]
  push_cast
  ring

theorem jet_mul_C (p : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.C a) G = a * jetAt0 p G := by
  rw [mul_comm p]
  unfold jetAt0
  rw [Finset.mul_sum]
  refine (Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl fun m _ => ?_)
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h, mul_zero]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  · rw [MvPolynomial.coeff_C_mul]
    ring

def linT [Fintype σ] (M : τ → σ → C) : MvPolynomial τ C →ₐ[C] MvPolynomial σ C :=
  MvPolynomial.aeval fun c => ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w


theorem coeff_mvExp_partial {h : MvPowerSeries σ C} (hh : OrdGE 1 h) (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) :
    coeff m (mvExp h) = coeff m (∑ k ∈ Finset.range (N + 1), ((k.factorial : C)⁻¹) • h ^ k) := by
  have hpow : ∀ k, OrdGE k (h ^ k) := by
    intro k
    have := ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)
    simpa [Finset.prod_const, Finset.card_range] using this
  show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  · intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hpow k m (by omega), zero_div]

theorem subst_mvExp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {h : MvPowerSeries σ C} (hh : OrdGE 1 h) : subst a (mvExp h) = mvExp (subst a h) := by
  ext e
  have hsh : OrdGE 1 (subst a h) := ordGE_subst ha hh
  rw [coeff_subst_congr ha (F := mvExp h)
      (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree)
      (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl,
    coeff_mvExp_partial hsh e.degree e le_rfl]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]
  simp only [map_smul, map_pow]

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace VP

section Gen

variable {C : Type} [Field C] {σ τ ρ : Type}

theorem hs [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.HasSubst a := hasSubst_of_ordGE (fun s => by
    unfold Formalism.BaseCaseIdentities.OrdGE
    intro A hA
    have h0 : A = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst h0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha s)

theorem og {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    Formalism.BaseCaseIdentities.OrdGE 1 (a s) := by
  unfold Formalism.BaseCaseIdentities.OrdGE
  intro A hA
  have h0 : A = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s

theorem cc_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have h : Formalism.BaseCaseIdentities.OrdGE 1 (MvPowerSeries.subst a f) :=
    ordGE_subst (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())
  have h0 := h 0 (by simp)
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

theorem subst_mul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f * g) = MvPowerSeries.subst a f * MvPowerSeries.subst a g := MvPowerSeries.subst_mul (hs ha) f g

theorem subst_one [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_one _

theorem subst_prod [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∏ i ∈ s, F i) = ∏ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_prod _ _ _

theorem subst_sum [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_sum _ _ _

theorem subst_smul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (c : C) (f : MvPowerSeries σ C) :
    MvPowerSeries.subst a (c • f) = c • MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_smul _ c f

theorem subst_exp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := subst_mvExp (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())

theorem subst_subst [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    MvPowerSeries.subst b (MvPowerSeries.subst a f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst b (a s)) f := MvPowerSeries.subst_comp_subst_apply (hs ha) (hs hb) f

theorem subst_X [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    MvPowerSeries.subst a (MvPowerSeries.X s : MvPowerSeries σ C) = a s := MvPowerSeries.subst_X (hs ha) s

end Gen

section Exp

variable {C : Type} [Field C] [CharZero C] {n dd : ℕ}

theorem expS_eq (f : PS C n dd) (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS C f = mvExp f := by
  have hpow : ∀ (k : ℕ) (m : Fin n × Fin dd →₀ ℕ), m.degree < k → MvPowerSeries.coeff m (f ^ k) = 0 := by
    intro k m hm
    have h1 := ordGE_finsupp_prod (fun _ : Unit => f) (fun _ => og (a := fun _ : Unit => f) (fun _ => hf) ())
      (Finsupp.single () k)
    simp only [Finsupp.prod_single_index, pow_zero, Finsupp.degree_single] at h1
    exact h1 m hm
  ext m
  rw [FB.expS, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]
  change _ = ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m.degree + 1)) ?_]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [PowerSeries.coeff_exp]
    simp only [smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hpow k m (by omega), smul_zero])

end Exp

end VP

end Formalism.L2.FormalSeriesBounds
end
end
