import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.Columns.MemWmPerp
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

section
noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX

namespace Formalism.IndefR.NX

def mulC {q : ℕ} (c : ZMod q) : Multiplicative (ZMod q) →* Multiplicative (ZMod q) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c)

@[simp] theorem mulC_ofAdd {q : ℕ} (c z : ZMod q) :
    mulC c (Multiplicative.ofAdd z) = Multiplicative.ofAdd (c * z) := rfl

theorem comp_mulC_ne_one {K : Type} [Field K] {q : ℕ} [Fact q.Prime] (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1)
    {c : ZMod q} (hc : c ≠ 0) : θ.comp (mulC c) ≠ 1 := by
  intro h
  apply hθ
  refine MonoidHom.ext fun z => ?_
  have e := DFunLike.congr_fun h (Multiplicative.ofAdd (c⁻¹ * Multiplicative.toAdd z))
  simp only [MonoidHom.comp_apply, mulC_ofAdd, MonoidHom.one_apply] at e
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, ofAdd_toAdd] at e
  simpa using e

theorem comp_mulC_zero {K : Type} [Field K] {q : ℕ} (θ : Multiplicative (ZMod q) →* Kˣ) :
    θ.comp (mulC (0 : ZMod q)) = 1 := by
  refine MonoidHom.ext fun z => ?_
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
  rw [← ofAdd_toAdd z, mulC_ofAdd, zero_mul, ofAdd_zero, map_one]

section Gen

variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)

def thXi {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) :
    ∀ x, Multiplicative (ZMod (p x)) →* Kˣ :=
  fun x => (θ x).comp (mulC (ξ x))

def psiXi {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) : Uup p r →* Kˣ :=
  psiStd p r (thXi p ξ θ)

variable {p r}

theorem psiXi_apply {K : Type} [Field K] (ξ : ∀ x, ZMod (p x)) (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (u : Uup p r) : psiXi p r ξ θ u = ∏ x, θ x (Multiplicative.ofAdd (ξ x *
      supSum r (((u : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))))) := rfl




theorem psiXi_tvAt [DecidableEq ι] {K : Type} [Field K] (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hr : 2 ≤ r) (x : ι) :
    psiXi p r ξ θ ⟨tvAt hr x, tvAt_mem hr x⟩ = θ x (Multiplicative.ofAdd (ξ x)) := by
  have hc : ∀ M : Matrix.SpecialLinearGroup (Fin r) (ZMod (p x)),
      ((Matrix.SpecialLinearGroup.toGL M : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) = M :=
    fun M => rfl
  rw [psiXi_apply, Finset.prod_eq_single x]
  · simp only [tvAt, Pi.mulSingle_eq_same]
    show θ x (Multiplicative.ofAdd (ξ x * supSum r (tv hr (1 : ZMod (p x))))) = _
    rw [supSum_tv, mul_one]
  · intro y _ hy
    simp [tvAt, Pi.mulSingle_eq_of_ne hy, supSum_one]
  · intro h
    exact absurd (Finset.mem_univ x) h


theorem xi_ne_zero_of_isStdGeneric [DecidableEq ι] {K : Type} [Field K] {S : Subgroup (GProd p r)}
    (hS : S = Uup p r) (ψ : S →* Kˣ) (hg : IsStdGeneric p r ψ) (ξ : ∀ x, ZMod (p x))
    (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (hψ : ∀ u : S, ψ u = stdVal p r (thXi p ξ θ) u)
    (hr : 2 ≤ r) (hp : ∀ x, NeZero (p x)) (x : ι) : ξ x ≠ 0 := by
  intro h0
  obtain ⟨θ', hθ', hψ'⟩ := hg
  have hm : tvAt (p := p) hr x ∈ S := by rw [hS]; exact tvAt_mem hr x
  have e := (hψ' ⟨_, hm⟩).symm.trans (hψ ⟨_, hm⟩)
  simp only [stdVal_tvAt, thXi, h0, comp_mulC_zero, MonoidHom.one_apply] at e
  exact char_one_ne (θ' x) (hθ' hr x) e

end Gen

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def U (N : NData R H what₂) : Subgroup (G0g N) :=
  Uup (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r

theorem U_eq_Uup (N : NData R H what₂) : U N = Uup (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r := rfl

theorem mem_U {N : NData R H what₂} {u : G0g N} : u ∈ U N ↔
    ∀ kv : (Σ k : Fin 2, N.PlG k), (∀ a b : Fin R.r, b < a →
      ((u kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))) a b = 0) ∧
      ∀ a : Fin R.r, ((u kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))) a a = 1 :=
  Iff.rfl


def psiUOf (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) : U N →* Kˣ :=
  psiXi (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r ξ (fun kv => θ kv.1)

theorem psiUOf_apply (N : NData R H what₂) {K : Type} [Field K] (ξ : ∀ kv : (Σ k : Fin 2, N.PlG k), ZMod (H.g kv.1))
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (H.g k)) →* Kˣ) (u : U N) :
    psiUOf N ξ θ u = ∏ kv : (Σ k : Fin 2, N.PlG k), θ kv.1 (Multiplicative.ofAdd (ξ kv *
      supSum R.r (((u : G0g N) kv : GL (Fin R.r) (ZMod (H.g kv.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g kv.1))))) :=
  rfl



def thSide {K : Type} [Field K] (g : Fin 2 → ℕ) (θ : ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ) (b : Bool) :
    ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ :=
  fun k => if b then θ k else (θ k)⁻¹

theorem thSide_ne_one {K : Type} [Field K] (g : Fin 2 → ℕ) (θ : ∀ k : Fin 2, Multiplicative (ZMod (g k)) →* Kˣ)
    (b : Bool) (k : Fin 2) (h : θ k ≠ 1) : thSide g θ b k ≠ 1 := by
  cases b <;> simp [thSide, h]

def psiUD (D : D7) (i : D.ntw.Tw) (θ : ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ)
    (b : Bool) : U D.nd →* (FractionRing (D.ntw.O i))ˣ :=
  psiUOf D.nd (xiRed D) (thSide D.host.g θ b)

theorem psiUD_side (D : D7) (i : D.ntw.Tw)
    (θ : ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ) (u : U D.nd) :
    psiUD D i θ false u = (psiUD D i θ true u)⁻¹ := by
  simp only [psiUD, psiUOf_apply, thSide, Bool.false_eq_true, if_false, if_true, MonoidHom.inv_apply,
    Finset.prod_inv_distrib]

def XiRedNZ (D : D7) : Prop := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), xiRed D kv ≠ 0

theorem tied_U_clauses (D : D7)
    (θ : ∀ i, ∀ k : Fin 2, Multiplicative (ZMod (D.host.g k)) →* (FractionRing (D.ntw.O i))ˣ)
    (hξ : 2 ≤ D.R.r → XiRedNZ D) (hθ : 2 ≤ D.R.r → ∀ i k, θ i k ≠ 1)
    (hU : D.nexp.U = U D.nd)
    (hψ : ∀ i b (u : D.nexp.U), D.nexp.psiU i b u = psiUD D i (θ i) b ⟨u.1, by rw [← hU]; exact u.2⟩) :
    D.nexp.U = Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ∧
    (∀ i b, IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r (D.nexp.psiU i b)) ∧
    (∀ i (u : D.nexp.U), D.nexp.psiU i false u = (D.nexp.psiU i true u)⁻¹) ∧
    (∀ i b, ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (FractionRing (D.ntw.O i))ˣ,
      (2 ≤ D.R.r → ∀ kk, θ kk ≠ 1) ∧ ∀ u : D.nexp.U, D.nexp.psiU i b u = ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk),
        θ kv.1 (Multiplicative.ofAdd (xiRed D kv *
          supSum D.R.r (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))))) := by
  refine ⟨hU, fun i b => ?_, fun i u => ?_, fun i b => ?_⟩
  · refine ⟨thXi _ (xiRed D) (fun kv => thSide D.host.g (θ i) b kv.1), fun hr kv => ?_, fun u => ?_⟩
    · have : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
      exact comp_mulC_ne_one _ (thSide_ne_one _ _ b _ (hθ hr i kv.1)) (hξ hr kv)
    · rw [hψ]; rfl
  · rw [hψ, hψ]; exact psiUD_side D i (θ i) _
  · exact ⟨thSide D.host.g (θ i) b, fun hr kk => thSide_ne_one _ _ b _ (hθ hr i kk), fun u => by rw [hψ]; rfl⟩

theorem NExpTied.xiRedNZ {D : D7} (T : NExpTied D) (hr : 2 ≤ D.R.r) (i : D.ntw.Tw) : XiRedNZ D := by
  classical
  intro kv
  obtain ⟨θ, -, hψ⟩ := T.psiU_xi i true
  exact xi_ne_zero_of_isStdGeneric T.U_eq _ (T.psiU_gen i true) (xiRed D) (fun kv => θ kv.1)
    (fun u => (hψ u).trans rfl) hr (fun kv => ⟨(D.host.g_prime kv.1).ne_zero⟩) kv

end Rec

section PerPlace

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def psiUPl (N : NData R H what₂) {K : Type} [Field K]
    (ψ : ∀ kv : (Σ k : Fin 2, N.PlG k), Multiplicative (ZMod (H.g kv.1)) →* Kˣ) : U N →* Kˣ :=
  psiStd (fun kv : (Σ k : Fin 2, N.PlG k) => H.g kv.1) R.r ψ


end PerPlace

end Formalism.IndefR.NX
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX

namespace Formalism.IndefR.NX

section general

variable {E : Type} [Field E] [NumberField E]

theorem natCast_not_mem_of_coprime_g {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) {g n : ℕ} (hg : ((g : ℕ) : 𝓞 E) ∈ P)
    (hc : Nat.Coprime n g) : ((n : ℕ) : 𝓞 E) ∉ P := by
  intro hn
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h := Nat.gcd_eq_gcd_ab n g
  rw [hc.gcd_eq_one] at h
  have h' : (1 : 𝓞 E) = (n : 𝓞 E) * ((Nat.gcdA n g : ℤ) : 𝓞 E) + (g : 𝓞 E) * ((Nat.gcdB n g : ℤ) : 𝓞 E) := by
    have h2 := congrArg (Int.cast : ℤ → 𝓞 E) h
    push_cast at h2
    exact h2
  rw [h']
  exact P.add_mem (P.mul_mem_right _ hn) (P.mul_mem_right _ hg)

theorem primesOver_eq_places (g : ℕ) [Fact g.Prime] :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) =
      (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' {v | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime g
  have hlo : ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P.LiesOver (Ideal.span {(g : ℤ)}) ↔ ((g : ℕ) : 𝓞 E) ∈ P := by
    intro P hP
    rw [Ideal.liesOver_iff]
    constructor
    · intro h
      have hg : (g : ℤ) ∈ P.under ℤ := h ▸ Ideal.mem_span_singleton_self _
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at hg
      exact hg
    · intro h
      have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap, map_natCast]
        exact h
      exact hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle
  have hne0 : ((g : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((g : ℕ) : E) = 0 := by
      have := congrArg (fun x : 𝓞 E => (x : E)) h
      simpa using this
    exact (Fact.out : g.Prime).ne_zero (by exact_mod_cast this)
  ext P
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hP, hl⟩
    have hg : ((g : ℕ) : 𝓞 E) ∈ P := (hlo P).mp hl
    have hne : P ≠ ⊥ := fun h => hne0 (by rw [h] at hg; exact hg)
    exact ⟨⟨P, hP, hne⟩, hg, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, (hlo v.asIdeal).mpr hv⟩

theorem card_residue_of_split (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hsplit : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).ncard = Module.finrank ℚ E)
    (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) : Nat.card (𝓞 E ⧸ w.asIdeal) = g := by
  classical
  have : Fact g.Prime := ⟨hg⟩
  set p : Ideal ℤ := Ideal.span {(g : ℤ)} with hp_def
  have : p.IsMaximal := Int.ideal_span_isMaximal_of_prime g
  have hfin : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).Finite := by
    apply Set.finite_of_ncard_pos
    rw [hsplit]; exact Module.finrank_pos
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) :=
    fun a b h => HeightOneSpectrum.ext h
  have hPO := primesOver_eq_places (E := E) g
  have hfin' : (p.primesOver (𝓞 E)).Finite := by rw [hPO]; exact hfin.image _
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin'.fintype
  have hcard : Fintype.card (p.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', hPO, Set.ncard_image_of_injective _ hinj, hsplit]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hle : ∀ q ∈ (Finset.univ : Finset (p.primesOver (𝓞 E))),
      (1 : ℕ) ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    have := q.2.1
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hones : ∑ q : p.primesOver (𝓞 E), (1 : ℕ) =
      ∑ q : p.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [hsum, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, hcard]
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hones
  have hwmem : w.asIdeal ∈ p.primesOver (𝓞 E) := by
    rw [hPO]; exact ⟨w, hw, rfl⟩
  have h1 := hall ⟨w.asIdeal, hwmem⟩ (Finset.mem_univ _)
  have hf : w.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left h1.symm
  have : w.asIdeal.LiesOver p := hwmem.2
  have hpow := Ideal.pow_inertiaDeg g w.asIdeal
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpow
  exact hpow.symm

private theorem zmod_eq_of_val_sub_mem_prime (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E)) (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {x y : ZMod g} (h : ((x.val : ℕ) : 𝓞 E) - ((y.val : ℕ) : 𝓞 E) ∈ w.asIdeal) : x = y := by
  haveI := Fact.mk hg
  have hwt : w.asIdeal ≠ ⊤ := w.isPrime.ne_top
  by_contra hne
  have hab : x.val ≠ y.val := fun h' => hne (ZMod.val_injective g h')
  have hxg := ZMod.val_lt x
  have hyg := ZMod.val_lt y
  rcases Nat.lt_or_ge x.val y.val with hlt | hle
  · have hmem : (((y.val - x.val : ℕ)) : 𝓞 E) ∈ w.asIdeal := by
      rw [Nat.cast_sub hlt.le, ← neg_sub]
      exact w.asIdeal.neg_mem h
    have hcop : Nat.Coprime (y.val - x.val) g :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm
    exact natCast_not_mem_of_coprime_g hwt hw hcop hmem
  · have hmem : (((x.val - y.val : ℕ)) : 𝓞 E) ∈ w.asIdeal := by
      rw [Nat.cast_sub hle]
      exact h
    have hcop : Nat.Coprime (x.val - y.val) g :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hg).symm
    exact natCast_not_mem_of_coprime_g hwt hw hcop hmem

theorem exists_zmod_residue (g : ℕ) (hg : g.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hsplit : ({v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}).ncard = Module.finrank ℚ E)
    (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (y : 𝓞 E ⧸ w.asIdeal) :
    ∃ x : ZMod g, Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E) = y := by
  haveI := Fact.mk hg
  have hcard := card_residue_of_split g hg w hsplit hw
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hg.ne_zero)
  let f : ZMod g → 𝓞 E ⧸ w.asIdeal := fun x => Ideal.Quotient.mk w.asIdeal ((x.val : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact zmod_eq_of_val_sub_mem_prime g hg w hw (Ideal.Quotient.eq.1 hxy)
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨x, hx⟩

end general

section record

variable (D : D7)

theorem isIntegral_sqrtMinusD : IsIntegral ℤ D.host.sqrtMinusD := by
  have h : D.host.sqrtMinusD ^ 2 = (((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) := by
    rw [Host.sqrtMinusD_sq]; push_cast; ring
  exact IsIntegral.of_pow (by norm_num : 0 < 2) (h ▸ RingOfIntegers.isIntegral_coe _)

def sqrtO : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, isIntegral_sqrtMinusD D⟩

@[simp] theorem coe_sqrtO : ((sqrtO D : 𝓞 D.host.E) : D.host.E) = D.host.sqrtMinusD :=
  rfl

theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h0
  have hsq := Host.sqrtMinusD_sq D.host
  rw [h0] at hsq
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero
  apply hd0
  have : -(D.host.d : D.host.E) = 0 := by rw [← hsq]; ring
  simpa using this

def xiDen : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) * sqrtO D

theorem imaginary_generator_mul_denominator : D.host.xi0 * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -1 := by
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact D.host.ccK_ne_bot
  have hs := sqrtMinusD_ne_zero D
  change D.host.xi0 * (((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) * D.host.sqrtMinusD) = -1
  rw [Host.xi0]
  field_simp

theorem g_mem_pG (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (pG D kv).asIdeal :=
  D.naut.plGw_over kv.1 kv.2

theorem coprime_normK_g (k : Fin 2) : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) :=
  D.host.ccK_coprime _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (D.host.g_level k))))))

theorem coprime_d_g (k : Fin 2) : Nat.Coprime D.host.d (D.host.g k) := by
  have h := D.ntypes.g_cond k
  have hdvd : D.host.d ∣ D.host.QS * D.host.q * D.host.d := Dvd.intro_left _ rfl
  have hmod : D.host.g k % D.host.d = 1 % D.host.d := by
    rw [← Nat.mod_mod_of_dvd _ hdvd, h]
  rw [Nat.Coprime, Nat.gcd_rec, hmod, ← Nat.gcd_rec]
  exact Nat.gcd_one_right _

theorem xiDen_not_mem (kv : Σ k : Fin 2, D.nd.PlG k) : xiDen D ∉ (pG D kv).asIdeal := by
  have hP : (pG D kv).asIdeal.IsPrime := (pG D kv).isPrime
  have hg := g_mem_pG D kv
  have hN := natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_normK_g D kv.1)
  have hd := natCast_not_mem_of_coprime_g hP.ne_top hg (coprime_d_g D kv.1)
  have hs : sqrtO D ∉ (pG D kv).asIdeal := by
    intro hs
    apply hd
    have h2 : sqrtO D * sqrtO D ∈ (pG D kv).asIdeal := (pG D kv).asIdeal.mul_mem_left _ hs
    have he : sqrtO D * sqrtO D = -((D.host.d : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      push_cast
      change D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E)
      rw [← sq, Host.sqrtMinusD_sq]
    rw [he] at h2
    simpa using (pG D kv).asIdeal.neg_mem_iff.mp h2
  intro hc
  rcases hP.mem_or_mem hc with h | h
  · exact hN h
  · exact hs h

theorem xiRed_cond (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ x : ZMod (D.host.g kv.1), ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
      ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal := by
  classical
  have : (pG D kv).asIdeal.IsMaximal := (pG D kv).isMaximal
  let _ : Field (𝓞 D.host.E ⧸ (pG D kv).asIdeal) := Ideal.Quotient.field _
  have hc := xiDen_not_mem D kv
  have hcq : Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨x, hx⟩ := exists_zmod_residue (D.host.g kv.1) (D.host.g_prime kv.1) (pG D kv) (D.nd.g_split kv.1)
    (g_mem_pG D kv) (Ideal.Quotient.mk (pG D kv).asIdeal (-1) * (Ideal.Quotient.mk (pG D kv).asIdeal (xiDen D))⁻¹)
  refine ⟨x, -1, xiDen D, hc, ?_, ?_⟩
  · have h1 := imaginary_generator_mul_denominator D
    push_cast
    exact h1.symm
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hx, mul_assoc, inv_mul_cancel₀ hcq, mul_one, sub_self]

theorem xiRed_ne_zero (kv : Σ k : Fin 2, D.nd.PlG k) : xiRed D kv ≠ 0 := by
  intro h0
  have hP := xiRed_cond D kv
  have hx : xiRed D kv = hP.choose := by
    unfold Formalism.L2.NX.xiRed
    rw [dif_pos hP]
  obtain ⟨a, c, hc, hac, hmem⟩ := hP.choose_spec
  rw [← hx, h0, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_sub] at hmem
  have ha : a ∈ (pG D kv).asIdeal := by simpa using (pG D kv).asIdeal.neg_mem hmem
  have h1 : a * xiDen D = -c := by
    apply NumberField.RingOfIntegers.ext
    show (a : D.host.E) * ((xiDen D : 𝓞 D.host.E) : D.host.E) = -(c : D.host.E)
    rw [hac, mul_comm D.host.xi0, mul_assoc, imaginary_generator_mul_denominator, mul_neg_one]
  apply hc
  have h2 : -c ∈ (pG D kv).asIdeal := by
    rw [← h1]
    exact (pG D kv).asIdeal.mul_mem_right _ ha
  simpa using (pG D kv).asIdeal.neg_mem h2

def IsXiRes (kv : Σ k : Fin 2, D.nd.PlG k) (x : ZMod (D.host.g kv.1)) : Prop :=
  ∃ a c : 𝓞 D.host.E, c ∉ (pG D kv).asIdeal ∧ (a : D.host.E) = D.host.xi0 * c ∧
    ((x.val : 𝓞 D.host.E) * c - a) ∈ (pG D kv).asIdeal

theorem xiRed_isXiRes (kv : Σ k : Fin 2, D.nd.PlG k) : IsXiRes D kv (xiRed D kv) := by
  have hP := xiRed_cond D kv
  have hx : xiRed D kv = hP.choose := by
    unfold Formalism.L2.NX.xiRed
    rw [dif_pos hP]
  rw [hx]
  exact hP.choose_spec

theorem xiRedNZ (D : D7) : XiRedNZ D :=
  fun kv => xiRed_ne_zero D kv

end record

end Formalism.IndefR.NX
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.NX Formalism.L2.Col
open scoped TensorProduct

namespace Formalism.IndefR.NX

section PsiU


end PsiU

section BC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {G : Type} [Group G]

def bcRep {W₀ : Type} [AddCommGroup W₀] [Module K W₀] (ρ₀ : Representation K G W₀) :
    Representation K' G (K' ⊗[K] W₀) where
  toFun γ := (ρ₀ γ).baseChange K'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_id
  map_mul' γ δ := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem toMatrix_bcRep {W₀ : Type} [AddCommGroup W₀] [Module K W₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W₀) (ρ₀ : Representation K G W₀) (γ : G) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K' b) (Algebra.TensorProduct.basis K' b) (bcRep (K' := K') ρ₀ γ) =
      (LinearMap.toMatrix b b (ρ₀ γ)).map (algebraMap K K') :=
  LinearMap.toMatrix_baseChange K' (ρ₀ γ) b b

end BC

section AdlK

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

end AdlK

section AlgBC

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] [Algebra K K']

theorem isAlgWeightF_bc {W₀ : Type} [AddCommGroup W₀] [Module K W₀]
    (ρ₀ : Representation K (GQ L n) W₀) (h : IsAlgWeightF L n K ρ₀) : IsAlgWeightF L n K' (bcRep (K' := K') ρ₀) := by
  obtain ⟨hfd, ι, hι, hdec, bs, κ, hκ, eb, P, hP⟩ := h
  have := hfd
  refine ⟨inferInstance, ι, hι, hdec, Algebra.TensorProduct.basis K' bs, κ, hκ, eb,
    fun a a' => MvPolynomial.map (algebraMap K K') (P a a'), fun γ γ₀ hγ => ?_⟩
  rw [toMatrix_bcRep, hP γ γ₀ hγ]
  ext a a'
  simp only [MvPolynomial.eval_map]
  show algebraMap K K' (MvPolynomial.eval₂ (RingHom.id K) _ (P a a')) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext p
  simp [map_ratCast]

end AlgBC

section Real

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

abbrev algKk : Algebra (FractionRing (D.ntw.O i)) (Kk D i k) := (toKk D i k).toAlgebra

attribute [local instance] algKk

end Real

section LevGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

end LevGen

section LevNX

variable (D : D7) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
  (sp : PlE D.host → SplitPlace D.host.E) (QP DP : Finset (PlE D.host))

end LevNX

section ChrG


theorem supSum_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {r : ℕ} (A : Matrix (Fin r) (Fin r) R) :
    Formalism.L2.NX.supSum r (A.map f) = f (Formalism.L2.NX.supSum r A) := by
  unfold Formalism.L2.NX.supSum
  simp only [map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

section RedGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

variable {F : Type} [CommRing F]

theorem intLift_of_mem (v : HeightOneSpectrum (𝓞 L⁺)) (y : v.adicCompletion L⁺)
    (h : y ∈ v.adicCompletionIntegers L⁺) : intLift v y = ⟨y, h⟩ := by
  unfold intLift
  rw [dif_pos h]



end RedGen

variable (D : D7) (i : D.ntw.Tw) (b : Bool) (k : ℕ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
  (sp : PlE D.host → SplitPlace D.host.E)

open Classical in

theorem psiUTot_single (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (FractionRing (D.ntw.O i))ˣ)
    (hU : D.nexp.U = U D.nd)
    (hψ : ∀ (u : D.nexp.U), D.nexp.psiU i b u = psiUD D i θ b ⟨u.1, by rw [← hU]; exact u.2⟩)
    (kv : Σ kk : Fin 2, D.nd.PlG kk) (Gm : GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (hG : IsUniTri D.R.r (Gm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) :
    psiUTot D i b (Pi.mulSingle kv Gm) = ((thSide D.host.g θ b kv.1 (Multiplicative.ofAdd (xiRed D kv *
      Formalism.L2.NX.supSum D.R.r (Gm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) :
        (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  classical
  have hmem : (Pi.mulSingle kv Gm : G0g D.nd) ∈ D.nexp.U := by
    rw [hU, mem_U]
    intro kv'
    by_cases h : kv' = kv
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact ⟨fun a c hca => hG.1 hca, hG.2⟩
    · rw [Pi.mulSingle_eq_of_ne h]
      refine ⟨fun a c hca => ?_, fun a => by simp⟩
      have hne : a ≠ c := fun e => by subst e; exact lt_irrefl _ hca
      simp [Matrix.one_apply_ne hne]
  unfold psiUTot
  rw [dif_pos hmem, hψ ⟨_, hmem⟩, psiUD, psiUOf_apply, Finset.prod_eq_single kv]
  · dsimp only
    rw [Pi.mulSingle_eq_same]
  · intro kv' _ hne
    dsimp only
    rw [Pi.mulSingle_eq_of_ne hne]
    simp [Formalism.L2.NX.supSum_one]
  · intro h
    exact absurd (Finset.mem_univ kv) h

open Classical in

theorem gVal_of (kv : Σ kk : Fin 2, D.nd.PlG kk) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (xm : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (G : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (hrn : D.R.r ≤ D.R.nV)
    (hG : redMat s.v red (topR hrn xm) = G)
    (u : (ZMod (D.host.g kv.1))ˣ) (hu : red (intLift s.v (detT D.R.r xm)) = (u : ZMod (D.host.g kv.1))) :
    gVal D i k b kv s red τ' xm = toKk D i k (psiUTot D i b (Pi.mulSingle kv (glOf G))) *
      toKk D i k ((τ' u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  have hU' : IsUnit (red (intLift s.v (detT D.R.r xm))) := by rw [hu]; exact u.isUnit
  unfold gVal
  show toKk D i k (psiUTot D i b (Pi.mulSingle kv (glOf (redMat s.v red (topR hrn xm))))) *
    (if h : IsUnit (red (intLift s.v (detT D.R.r xm))) then
      toKk D i k ((τ' h.unit : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) else 1) = _
  rw [hG, dif_pos hU', show hU'.unit = u from Units.ext (by rw [IsUnit.unit_spec, hu])]

end ChrG

section Tau

variable (D : D7)

def TauTame (i : D.ntw.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) : Prop :=
  ∃ τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ, ∀ (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E),
    (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (pG D kv).asIdeal →
    ((τ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      ringHomOfBaseOrderToFraction D i (tameVal (D.ntw.chi1 i j b) (pG D kv) 1 u).1

open Classical in

def tauNX (i : D.ntw.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) :
    (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ :=
  if h : TauTame D i j b kv then h.choose else 1


end Tau

section Assembly

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ)
  (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

attribute [local instance] algKk

end Assembly

section Pq

variable (D : D7)

open Classical in

def qpOf (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host)) :
    Finset (PlE D.host) :=
  S.filter fun P => ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S

theorem qpOf_sub (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host)) :
    qpOf D Pq S ⊆ S := by
  classical
  intro P hP
  unfold qpOf at hP
  exact (Finset.mem_filter.1 hP).1

theorem qpOf_eq (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : Finset (PlE D.host))
    {P : PlE D.host} (hP : P ∈ qpOf D Pq S) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hv : NG.OverPl P v) (hS : Pq v ∈ S) : P = Pq v := by
  classical
  unfold qpOf at hP
  exact ((Finset.mem_filter.1 hP).2 v hv).resolve_right (not_not.2 hS)

end Pq

end Formalism.IndefR.NX
end
end
