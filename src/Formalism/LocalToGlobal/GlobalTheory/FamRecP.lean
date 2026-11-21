import Formalism.LocalToGlobal.GlobalTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

theorem prBelow_plF (D : D7) (w : D.what₂.places.Pl) :
    LChain2.prBelow (plF D w) = D.what₂.places.resChar w :=
  (LChain2.prBelow_iff (plF D w) _).2
    (J.liesOver_of_mem _ (D.what₂.places.resChar_prime w) (D.plEq w) (J.resChar_mem D w))

theorem prBelow_eq (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) :
    LChain2.prBelow z = D.what₂.places.resChar (plB D z) := by
  conv_lhs => rw [← plF_plB D z]
  exact prBelow_plF D _

theorem ramE_plF (D : D7) (w : D.what₂.places.Pl) :
    LChain2.ramE (plF D w) = (D.what₂.places.ramIdx w : ℝ) := by
  rw [D.ram_eq w]; rfl


theorem ell_plF (D : D7) (w : D.what₂.places.Pl) : slopeLatticeData.ell (plF D w) = SizeData₂.lwP w := rfl

theorem lE_plF (D : D7) (w : D.what₂.places.Pl) :
    LChain2.lE (plF D w) = SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
  unfold LChain2.lE
  rw [ramE_plF, ell_plF]

theorem lE_eq (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) :
    LChain2.lE z = SizeData₂.lwP (plB D z) * (D.what₂.places.ramIdx (plB D z) : ℝ) := by
  conv_lhs => rw [← plF_plB D z]
  exact lE_plF D _


variable {D : D7} (L : SizeData₂ D)

theorem prOf_prime {p : ℕ} (hp : p ∈ prOf L) : p.Prime := by
  unfold prOf at hp
  rcases Finset.mem_union.1 hp with h | h
  · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 h
    exact D.what₂.places.resChar_prime w
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
    exact (D.mem u).A.T_prime

theorem mem_SOf (z : slopeLatticeData.FinPl D.what₂.LL) : z ∈ SOf L ↔ LChain2.prBelow z ∈ prOf L := by
  unfold SOf
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hz⟩
    rw [(LChain2.mem_plOver (prOf_prime L hp) z).1 hz]
    exact hp
  · intro h
    exact ⟨_, h, (LChain2.mem_plOver (prOf_prime L h) z).2 rfl⟩







theorem gainD_off (j : ℕ) {w : D.what₂.places.Pl} (hw : w ∉ L.supp) : L.gainD j w = 0 := by
  unfold SizeData₂.gainD
  split_ifs
  · rfl
  · exact L.gain_supp j w hw

theorem sg_off (u : D.what₂.Word) {w : D.what₂.places.Pl} (hw : w ∉ L.supp) : L.sg u w = 0 := by
  unfold SizeData₂.sg
  apply Finset.sum_eq_zero
  intro j _
  rw [gainD_off L j hw, L.F_supp j w hw, L.E_supp u j w hw]
  ring







section Proj
variable (m : ℕ) (A : Mx D)



end Proj

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.HN.DualPolygon

namespace Len

section Gen

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem locLen_tower (w : Ideal R) [w.IsPrime] (A B C : Submodule R V) (hCB : C ≤ B) (hBA : B ≤ A) :
    slopeLatticeData.locLen w (A ⧸ C.comap A.subtype) =
      slopeLatticeData.locLen w (B ⧸ C.comap B.subtype) + slopeLatticeData.locLen w (A ⧸ B.comap A.subtype) := by
  let f : (B ⧸ C.comap B.subtype) →ₗ[R] (A ⧸ C.comap A.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBA) (fun x hx => hx)
  let g : (A ⧸ C.comap A.subtype) →ₗ[R] (A ⧸ B.comap A.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hCB hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    intro h
    have h1 : (Submodule.inclusion hBA b) ∈ C.comap A.subtype := by
      have : Submodule.Quotient.mk (p := C.comap A.subtype) (Submodule.inclusion hBA b) = 0 := h
      exact (Submodule.Quotient.mk_eq_zero _).1 this
    exact (Submodule.Quotient.mk_eq_zero _).2 h1
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have H : Function.Exact f g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    constructor
    · intro h
      have h1 : a ∈ B.comap A.subtype := by
        have : Submodule.Quotient.mk (p := B.comap A.subtype) a = 0 := h
        exact (Submodule.Quotient.mk_eq_zero _).1 this
      exact ⟨Submodule.Quotient.mk ⟨a.1, h1⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← hx]
      have : Submodule.Quotient.mk (p := B.comap A.subtype) (Submodule.inclusion hBA b) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 b.2
      exact this
  exact slopeLatticeData.locLen_exact w f g hf hg H

theorem locLen_zero (w : Ideal R) [w.IsPrime] (A B : Submodule R V)
    (h : ∀ a ∈ A, ∃ s : R, s ∉ w ∧ s • a ∈ B) : slopeLatticeData.locLen w (A ⧸ B.comap A.subtype) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (A ⧸ B.comap A.subtype))).2 ?_)
  intro x
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨s, hs, hsa⟩ := h a.1 a.2
  refine ⟨s, hs, ?_⟩
  have : Submodule.Quotient.mk (p := B.comap A.subtype) (s • a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hsa
  exact this

end Gen

section NF

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem lenAt_eq (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V) :
    slopeLatticeData.lenAt w A B = (have := w.2.isPrime; slopeLatticeData.locLen w.1 (A ⧸ B.comap A.subtype)) := rfl

theorem lenAt_tower (w : slopeLatticeData.FinPl K) (A B C : Submodule (𝓞 K) V) (hCB : C ≤ B) (hBA : B ≤ A) :
    slopeLatticeData.lenAt w A C = slopeLatticeData.lenAt w B C + slopeLatticeData.lenAt w A B := by
  have := w.2.isPrime
  exact locLen_tower w.1 A B C hCB hBA

theorem lenAt_zero (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V)
    (h : ∀ a ∈ A, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • a ∈ B) : slopeLatticeData.lenAt w A B = 0 := by
  have := w.2.isPrime
  exact locLen_zero w.1 A B h

theorem index_smul (X : Submodule (𝓞 K) V) (hX : X.FG) (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup =
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set V)) := by
  let _ : StarRing K := starRingOfComm
  set m := Ideal.absNorm 𝔟 with hmdef
  have hm : m ≠ 0 := fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (m : 𝓞 K) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔠
    exact hspan0 h𝔠
  set r := finrank K (Submodule.span K (X : Set V)) with hr
  have hall := twist_int X hX m hm
  rw [twist_finrank_int X hX, h𝔠, mul_comm, Submodule.mul_smul,
    ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • X).toAddSubgroup
      (𝔟 • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)] at hall
  have ha := twist_le 𝔟 h𝔟 X hX
  have hb := twist_le 𝔠 h𝔠0 (𝔟 • X) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hX)
  rw [twist_span_smul X 𝔟 h𝔟] at hb
  have hnorm : Ideal.absNorm 𝔠 * m = m ^ finrank ℚ K := by
    rw [hmdef, ← map_mul, mul_comm, ← h𝔠, twist_absNorm_nat]
  have hB : 0 < Ideal.absNorm 𝔠 ^ r :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (finrank ℚ K * r) := by
    rw [← mul_pow, hnorm, ← pow_mul]
  by_contra hne
  have hlt := lt_of_le_of_ne ha hne
  have h1 : (𝔠 • 𝔟 • X).toAddSubgroup.relIndex (𝔟 • X).toAddSubgroup *
      (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)
  rw [hall, htot] at h1
  exact lt_irrefl _ h1

def Good (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (w : slopeLatticeData.FinPl K) (J : Ideal (𝓞 K)) (c : ℕ) : Prop :=
  J ≠ ⊥ ∧ ∀ Y : Submodule (𝓞 K) V, Y.FG → Submodule.span K (Y : Set V) = ⊤ →
    slopeLatticeData.lenAt w Y (J • Y) = ((finrank K V * c : ℕ) : ℕ∞)

theorem good_one (w : slopeLatticeData.FinPl K) : Good V w 1 0 := by
  refine ⟨one_ne_zero, fun Y _ _ => ?_⟩
  rw [Submodule.one_smul, mul_zero, Nat.cast_zero]
  exact lenAt_zero w Y Y (fun a ha => ⟨1, fun h => w.2.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩)

theorem good_mul (w : slopeLatticeData.FinPl K) {J J' : Ideal (𝓞 K)} {c c' : ℕ} (h : Good V w J c) (h' : Good V w J' c') :
    Good V w (J * J') (c + c') := by
  refine ⟨mul_ne_zero h.1 h'.1, fun Y hY hsp => ?_⟩
  rw [Submodule.mul_smul, lenAt_tower w Y (J' • Y) (J • J' • Y) Submodule.smul_le_right Submodule.smul_le_right,
    h'.2 Y hY hsp, h.2 (J' • Y) (Submodule.FG.smul (IsNoetherian.noetherian J') hY)
      (by rw [twist_span_smul Y J' h'.1, hsp])]
  push_cast
  ring

theorem good_ne (w a : slopeLatticeData.FinPl K) (h : a ≠ w) : Good V w a.1 0 := by
  refine ⟨slopeLatticeData.finPl_ne_bot a, fun Y _ _ => ?_⟩
  rw [mul_zero, Nat.cast_zero]
  have hnle : ¬ a.1 ≤ w.1 := fun hle => h (Subtype.ext (a.2.eq_of_le w.2.ne_top hle))
  obtain ⟨s, hsa, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  exact lenAt_zero w Y _ (fun y hy => ⟨s, hsw, Submodule.smul_mem_smul hsa hy⟩)

theorem good_self (w : slopeLatticeData.FinPl K) : Good V w w.1 1 := by
  classical
  refine ⟨slopeLatticeData.finPl_ne_bot w, fun Y hY hsp => ?_⟩
  have hidx := index_smul Y hY w.1 (slopeLatticeData.finPl_ne_bot w)
  rw [hsp, finrank_top] at hidx
  have hN0 : Ideal.absNorm w.1 ≠ 0 := fun h => slopeLatticeData.finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  have hN1 : Ideal.absNorm w.1 ≠ 1 := fun h => w.2.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hne : (w.1 • Y).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
    rw [hidx]; exact pow_ne_zero _ hN0
  obtain ⟨k, hk, hc⟩ := slopeLatticeData.index_finsupp Y (w.1 • Y) hne
  have hk0 : ∀ w' : slopeLatticeData.FinPl K, w' ≠ w → k w' = 0 := by
    intro w' hw'
    have h1 := (good_ne (V := V) w' w (fun h => hw' h.symm)).2 Y hY hsp
    rw [hk w', mul_zero] at h1
    exact_mod_cast h1
  have hsub : k.support ⊆ {w} := by
    intro w' hw'
    rw [Finset.mem_singleton]
    by_contra hcon
    exact (Finsupp.mem_support_iff.1 hw') (hk0 w' hcon)
  rw [Finsupp.prod_of_support_subset k hsub _ (fun _ _ => pow_zero _), Finset.prod_singleton, hidx] at hc
  have h2 : 2 ≤ Ideal.absNorm w.1 := by omega
  have := Nat.pow_right_injective h2 hc
  rw [hk w, mul_one, this]

theorem good_pow (w a : slopeLatticeData.FinPl K) (k : ℕ) : Good V w (a.1 ^ k) (if a = w then k else 0) := by
  induction k with
  | zero => simpa using good_one (V := V) w
  | succ k ih =>
    rw [pow_succ]
    by_cases h : a = w
    · subst h
      have := good_mul a ih (good_self (V := V) a)
      simpa using this
    · have := good_mul w ih (good_ne (V := V) w a h)
      simpa [h] using this

theorem good_prod (w : slopeLatticeData.FinPl K) (n : slopeLatticeData.FinPl K → ℕ) (s : Finset (slopeLatticeData.FinPl K)) :
    Good V w (∏ a ∈ s, a.1 ^ n a) (∑ a ∈ s, if a = w then n a else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one (V := V) w
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact good_mul w (good_pow w a (n a)) ih


end NF

end Len


end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters




theorem card_RR (D : D7) : Fintype.card D.div.RR.ι = D.what₂.Drows := by
  rw [← Module.finrank_eq_card_basis D.div.RR.b, D.RRV_finrank]

theorem card_all (D : D7) (h : 0 < D.what₂.Dall) :
    Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) = D.what₂.Dall := by
  have hle := D.Drows_le_Dall h
  rw [Fintype.card_sum, Fintype.card_fin, card_RR]
  omega






end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

section Alg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem mem_of_loc (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ w : slopeLatticeData.FinPl K, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • x ∈ M) : x ∈ M := by
  let I : Ideal (𝓞 K) := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : ∀ a : 𝓞 K, a ∈ I ↔ a • x ∈ M := fun a => Iff.rfl
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm⟩
    exact hs (hle ((hI s).2 hsx))
  have h2 := (hI 1).1 (by rw [htop]; trivial)
  rwa [one_smul] at h2





omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem lenAt_eq_zero (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V)
    (h : ∀ y ∈ A, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • y ∈ B) : slopeLatticeData.lenAt w A B = 0 := by
  have := w.2.isPrime
  unfold slopeLatticeData.lenAt
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.1.primeCompl
    (LocalizedModule.mkLinearMap w.1.primeCompl (A ⧸ B.comap A.subtype))).2 ?_)
  intro q
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨s, hs, hsy⟩ := h y.1 y.2
  refine ⟨s, hs, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show (s • y : A).1 ∈ B
  exact hsy


omit [IsScalarTower (𝓞 K) K V] in
theorem idealSmul_mono_left {I J : Submodule (𝓞 K) K} (h : I ≤ J) (L : Submodule (𝓞 K) V) :
    HermitianLatticesTheory.idealSmul I L ≤ HermitianLatticesTheory.idealSmul J L := by
  refine Submodule.span_mono ?_
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, h ha, x, hx, rfl⟩





end Alg

section Rec

variable {D : D7} (L : SizeData₂ D) (m : ℕ) (A : Mx D)

def itD (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (tauZ L) : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) :
    Submodule (𝓞 D.what₂.LL) D.what₂.LL) (DV.MramL D u)





theorem exists_pl_over (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ z : slopeLatticeData.FinPl K, LChain2.prBelow z = p := by
  by_contra h
  push Not at h
  have h1 := LChain2.sum_log_norm_over_prime (∅ : Finset (slopeLatticeData.FinPl K)) p hp (fun w hw => absurd hw (h w))
  simp only [Finset.filter_empty, Finset.sum_empty] at h1
  have := Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < (p : ℝ))
  linarith










theorem sat {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∈ SOf L) (z' : slopeLatticeData.FinPl D.what₂.LL)
    (h : LChain2.prBelow z' = LChain2.prBelow z) : z' ∈ SOf L :=
  (mem_SOf L z').2 (h ▸ (mem_SOf L z).1 hz)


theorem T_mem (u : D.what₂.Word) : (D.mem u).A.T ∈ (SOf L).image LChain2.prBelow := by
  obtain ⟨z, hz⟩ := exists_pl_over D.what₂.LL _ (D.mem u).A.T_prime
  refine Finset.mem_image.2 ⟨z, (mem_SOf L z).2 ?_, hz⟩
  rw [hz]
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, Finset.mem_univ _, rfl⟩)




end Rec

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

variable {D : D7} (L : SizeData₂ D)



section Sums
variable (m : ℕ) (A : Mx D)










end Sums


end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters
open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

namespace FieldEq

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top Top' : Type}
  [Fintype Top] [Fintype Top'] {m f f' : ℕ} {A : Data U0 W Top m f} {B : Data U0 W Top' m f'} {eT : Top ≃ Top'}
  {eF : Fin f ≃ Fin f'}

theorem ff (_h : FieldEq A B eT eF) : f = f' := by simpa using Fintype.card_congr eF

variable (h : FieldEq A B eT eF)
include h

theorem nT : A.nT = B.nT := by unfold Data.nT; rw [Fintype.card_congr eT]

theorem sumT (F : ℝ → ℝ) : ∑ t, F (A.aT t) = ∑ t, F (B.aT t) := by
  rw [← Equiv.sum_comp eT]; exact Finset.sum_congr rfl (fun t _ => by rw [h.aT])

theorem sumW (u0 : U0) (j : Fin m) (G : ℝ → ℝ) : ∑ ρ, G (A.w u0 j ρ) = ∑ ρ, G (B.w u0 j ρ) := by
  rw [← Equiv.sum_comp eF]; exact Finset.sum_congr rfl (fun t _ => by rw [h.w])

theorem fd : A.d = B.d := funext fun u0 => funext (h.d u0)
theorem fT : A.T = B.T := funext fun u0 => funext (h.T u0)
theorem fmuN : A.muN = B.muN := funext fun u0 => funext (h.muN u0)
theorem fmuMaxN : A.muMaxN = B.muMaxN := funext fun u0 => funext (h.muMaxN u0)
theorem fh : A.h = B.h := funext fun u0 => funext (h.h u0)
theorem fmuM : A.muM = B.muM := funext fun u0 => funext (h.muM u0)
theorem fmuMaxM : A.muMaxM = B.muMaxM := funext fun u0 => funext (h.muMaxM u0)
theorem fEeJ : A.EeJ = B.EeJ := funext fun u0 => funext fun u => funext (h.EeJ u0 u)
theorem fmuCC : A.muCC = B.muCC := funext h.muCC
theorem fmuMinCC : A.muMinCC = B.muMinCC := funext h.muMinCC
theorem fFo : A.Fo = B.Fo := funext h.Fo
theorem fGa : A.Ga = B.Ga := funext h.Ga
theorem fASK : A.ASK = B.ASK := funext h.ASK
theorem fIO : A.IO = B.IO := funext h.IO
theorem fHH : A.HH = B.HH := funext h.HH
theorem fdel : A.del = B.del := funext h.del
theorem fη : A.η = B.η := funext h.η
theorem fe : A.e = B.e := funext h.e

theorem sumA : A.sumA = B.sumA := h.sumT (fun y => y)

theorem logOm : A.logOm = B.logOm := by unfold Data.logOm; rw [h.gam, h.v, h.LpL]

theorem Ee (u0 : U0) (u : W u0) : A.Ee u0 u = B.Ee u0 u := by unfold Data.Ee; rw [h.fEeJ]

theorem s (u0 : U0) : A.s u0 = B.s u0 := by unfold Data.s; rw [h.fd, h.fmuN, h.fh]

theorem uF (u0 : U0) : A.uF u0 = B.uF u0 := by unfold Data.uF; rw [h.s, h.fmuMaxN, h.fh]

theorem LoP (C : Consts) : A.LoP C = B.LoP C := by unfold Data.LoP; rw [h.nT, h.b, h.x, h.ε]

theorem Lo5 (C : Consts) (Xpp : ℝ) (u0 : U0) (u : W u0) : Lo5 A C Xpp u0 u = Lo5 B C Xpp u0 u := by
  unfold WeightedSlopeBounds.Lo5; rw [h.fIO, h.nT, h.a, h.k, h.b', h.fT]

theorem setting (C : Consts) (hA : A.HidaSetting C) : B.HidaSetting C := by
  obtain rfl := h.ff
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hA
  rw [h.x] at a1
  rw [h.b] at a2
  rw [h.a] at a3
  rw [h.b'] at a4
  rw [h.k] at a5
  rw [h.v] at a6
  rw [h.fd] at a10
  rw [h.fT] at a11
  rw [h.fmuN, h.fmuMaxN] at a12
  rw [h.delBar] at a14
  rw [h.etaBar] at a15
  rw [h.eBar] at a16 a17
  refine ⟨a1, a2, a3, a4, a5, a6, a7, fun t => ?_, fun u0 j ρ => ?_, a10, a11, a12, a13, a14, a15, a16, a17⟩
  · have := a8 (eT.symm t); rwa [h.aT, Equiv.apply_symm_apply] at this
  · have := a9 u0 j (eF.symm ρ); rwa [h.w, Equiv.apply_symm_apply] at this

theorem div (C : Consts) (hA : A.DIV C) : B.DIV C := by
  intro u0 u
  have h1 := hA u0 u
  have e := h.sumT (fun y => (m : ℝ) * (ph y - y * B.logOm) - y * Real.log (B.T u0 u))
  rw [h.fmuCC, h.fh, h.fFo, h.logOm, h.fT, h.nT, h.a, h.La, h.B0, h.Nc, h.x, h.ε, e] at h1
  exact h1

theorem eComp5 (C : Consts) (hA : EComp5 A C) : EComp5 B C := by
  intro u0 u
  have h1 := hA u0 u
  rw [h.Ee, h.sumA, h.lg, h.B0] at h1
  exact h1

theorem hComp (C : Consts) (hA : A.HComp C) : B.HComp C := by
  intro u0 u u'
  have h1 := hA u0 u u'
  have e := h.sumT (fun y => y * Real.log (B.T u0 u))
  have e' := h.sumT (fun y => y * Real.log (B.T u0 u'))
  rw [h.fh, h.fT, h.nT, h.a, h.La, h.B0, e, e'] at h1
  exact h1

theorem count5 (C : Consts) (hA : Count5 A C) : Count5 B C := by
  obtain rfl := h.ff
  intro u0 u
  obtain ⟨h1, h2, h3⟩ := hA u0 u
  have e : ∀ j : Fin m, ∑ ρ, Real.log (A.w u0 j ρ * B.v / Real.pi) = ∑ ρ, Real.log (B.w u0 j ρ * B.v / Real.pi) :=
    fun j => h.sumW u0 j (fun y => Real.log (y * B.v / Real.pi))
  rw [h.v, h.lg, h.La, h.k, h.fT, Finset.sum_congr rfl (fun j _ => by rw [e j])] at h1
  rw [h.fT, h.L] at h2
  rw [h.fT, h.k] at h3
  exact ⟨h1, h2, h3⟩

theorem slopes (C : Consts) (hA : A.Slopes C) : B.Slopes C := by
  intro u0 u
  have h1 := hA u0 u
  rw [h.nT, h.a, h.La, h.k, h.fmuM, h.fmuMaxM] at h1
  exact h1

theorem slopes_transfer_field_eq (C : Consts) (Xpp : ℝ) (hA : QuotientSlopeBoundsWith A C Xpp) : QuotientSlopeBoundsWith B C Xpp := by
  intro u0 u
  have h1 := hA u0 u
  rw [h.fmuMaxN, h.fmuMaxM, h.fGa, h.fFo, h.Ee, h.B0, h.fmuM, h.Lo5, h.fmuN] at h1
  exact h1

theorem losses5 (C : Consts) (hA : LossBounds A C) : LossBounds B C := by
  intro u0
  have h1 := hA u0
  rw [h.fASK, h.fGa, h.LoP, h.fIO] at h1
  exact h1

theorem slopeIneq (hA : A.SlopeIneq) : B.SlopeIneq := by
  intro u0
  have h1 := hA u0
  rw [h.fdel, h.fη, h.fe, h.s, h.fmuMinCC, h.fHH, h.uF, h.fmuCC] at h1
  exact h1

theorem hhBound (C : Consts) (hA : A.HHBound C) : B.HHBound C := by
  intro u0
  have h1 := hA u0
  rw [h.s, h.fmuMinCC, h.fHH, h.x, h.b] at h1
  exact h1

theorem fParams (hA : A.FParams) : B.FParams := by
  intro u0
  have h1 := hA u0
  rw [h.fdel, h.fη, h.fe, h.delBar, h.etaBar, h.eBar] at h1
  exact h1

theorem sizeData₂ (C : Consts) (Xpp : ℝ) (hA : LChain.SizeData₂ A C Xpp) : LChain.SizeData₂ B C Xpp := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hA
  exact ⟨h.setting C a1, h.div C a2, h.eComp5 C a3, h.hComp C a4, h.count5 C a5, h.slopes C a6, h.slopes_transfer_field_eq C Xpp a7,
    h.losses5 C a8, h.slopeIneq a9, h.hhBound C a10, h.fParams a11⟩

theorem errWindows (C : Consts) (Xpp eK K : ℝ) (hA : ErrWindows A C Xpp eK K) : ErrWindows B C Xpp eK K := by
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hA
  rw [h.x] at w1 w5 w7 w8 w11 w14 w16
  rw [h.ε] at w2 w3 w7 w14 w16
  rw [h.b] at w4 w5
  rw [h.a] at w5 w12 w18 w20
  rw [h.nT] at w6
  rw [h.k] at w8 w10 w11 w12 w18 w24
  rw [h.L] at w13 w14
  rw [h.La] at w15 w16
  rw [h.b'] at w17 w18
  rw [h.B0] at w22
  rw [h.Nc] at w23
  rw [h.delBar] at w25
  rw [h.etaBar] at w26
  rw [h.eBar] at w27
  rw [h.etaBar, h.eBar, h.x, h.b, h.ε, h.nT, h.a] at wEta
  refine ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, fun t => ?_, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩
  have := w21 (eT.symm t)
  rwa [h.aT, Equiv.apply_symm_apply, h.a] at this

end FieldEq

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters
open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

theorem local_first_layer_agreement : LocalFirstLayerAgreement := by
  intro eps Fm x e m pt A G cHH Dh ell N TT T2 a w h u0
  obtain ⟨hu, h1, h2, h3, h4, h5, h6, h7⟩ := h u0
  exact ⟨fun u => hu u, h1, h2, h3, h4, h5, h6, h7⟩



section Mod

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ} (M : Lnk.Mod Fm x) (hx : Fm.x1 < x)

include hx in
theorem sc_b : (Fm.L x M.i0).sc.b = bTx x eps := by
  show Real.exp ((Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps) = _
  rw [M.s_x hx, M.s_eps]; rfl

include hx in
theorem sc_a : (Fm.L x M.i0).sc.a = aTx x eps := by
  show (Fm.L x M.i0).sc.x * (Fm.L x M.i0).sc.b = _
  rw [M.s_x hx, sc_b M hx]; rfl

include hx in
theorem sc_Xp : (Fm.L x M.i0).sc.X' = XpTx x eps := by
  show Real.exp ((Fm.L x M.i0).sc.x ^ ((Fm.L x M.i0).sc.eps / 3)) = _
  rw [M.s_x hx, M.s_eps]; rfl

include hx in
theorem sc_bp : (Fm.L x M.i0).sc.b' = bpTx x eps := by
  show (Fm.L x M.i0).sc.a / (Fm.L x M.i0).sc.X' = _
  rw [sc_a M hx, sc_Xp M hx]; rfl

include hx in
theorem sc_L : (Fm.L x M.i0).sc.L = Real.log (bTx x eps) := by
  unfold bTx
  rw [Real.log_exp]
  show (Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps = _
  rw [M.s_x hx, M.s_eps]

theorem card_n : (Fintype.card M.e.A : ℝ) = ((Fm.D x M.i0).R.n : ℝ) := by
  rw [Lnk.card_HA]; rfl

include hx in
theorem sc_Xpp (etaB eB : ℝ) :
    (Fm.L x M.i0).sc.X'' (Fm.D x M.i0).R.n = LChain2.XppH M.e.A (globM M etaB eB) := by
  show (Fm.L x M.i0).sc.a / ((Fm.L x M.i0).sc.b' / ((Fm.L x M.i0).sc.x * ((Fm.D x M.i0).R.n : ℝ))) =
    aTx x eps / (bpTx x eps / (x * (Fintype.card M.e.A : ℝ)))
  rw [sc_a M hx, sc_bp M hx, M.s_x hx, card_n]

include hx in
theorem base_bound_eq : (Fm.L x M.i0).B0 = (2 * (Fintype.card M.e.A : ℝ)) * M.m * bTx x eps * x ^ eps := by
  show (((Fm.D x M.i0).R.f : ℕ) : ℝ) * ((Fm.D x M.i0).R.m : ℝ) *
    Real.exp ((Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps) * (Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps = _
  rw [M.s_x hx, M.s_eps, card_n]
  have : (((Fm.D x M.i0).R.f : ℕ) : ℝ) = 2 * ((Fm.D x M.i0).R.n : ℝ) := by
    unfold Ranks.f; push_cast; ring
  rw [this]; rfl

include hx in
theorem Nc_eq' : (Fm.L x M.i0).Nc = (M.T2.card : ℝ) * ((Fm.D x M.i0).R.k : ℝ) * bTx x eps * x ^ eps
    / ((Fintype.card M.e.A : ℝ) * ((Fintype.card M.e.A : ℝ) * x ^ (-eps))) := by
  show ((Fm.D x M.i0).host.T2.card : ℝ) * ((Fm.D x M.i0).R.k : ℝ) *
    Real.exp ((Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps) * (Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps /
    (((Fm.D x M.i0).R.n : ℝ) * (((Fm.D x M.i0).R.n : ℝ) * (Fm.L x M.i0).sc.x ^ (-(Fm.L x M.i0).sc.eps))) = _
  rw [M.s_x hx, M.s_eps, card_n, M.card_thick_set_model_eq]; rfl

theorem modified_field_eq : ModFieldEq := by
  intro eps Fm x M A ell N CH etaB eB hx hl hT
  exact
  { x := rfl
    ε := rfl
    a := sc_a M hx
    b := sc_b M hx
    b' := sc_bp M hx
    k := rfl
    L := sc_L M hx
    La := rfl
    B0 := base_bound_eq M hx
    Nc := Nc_eq' M hx
    gam := rfl
    LpL := hl
    v := rfl
    lg := rfl
    aT := fun τ => (M.ident N CH etaB eB (etaM M A CH) (eM M A) ell hl).1 τ
    w := fun u0 j ρ => by
      show M.w u0 j (M.eP ρ).1 = M.w u0 j (LChain2.ePhi (LChain2.ePhi.symm (M.eP ρ))).1
      rw [Equiv.apply_symm_apply]
    d := fun u0 u => ((hT u0).1 u).1.symm
    T := fun u0 u => ((hT u0).1 u).2.1.symm
    muN := fun u0 u => ((hT u0).1 u).2.2.1.symm
    muMaxN := fun u0 u => ((hT u0).1 u).2.2.2.1.symm
    h := fun u0 u => ((hT u0).1 u).2.2.2.2.1.symm
    muM := fun u0 u => ((hT u0).1 u).2.2.2.2.2.1.symm
    muMaxM := fun u0 u => ((hT u0).1 u).2.2.2.2.2.2.1.symm
    EeJ := fun u0 u j => (((hT u0).1 u).2.2.2.2.2.2.2 j).symm
    muCC := fun u0 => (hT u0).2.1.symm
    muMinCC := fun u0 => (hT u0).2.2.1.symm
    Fo := fun u0 => (hT u0).2.2.2.1.symm
    Ga := fun u0 => (hT u0).2.2.2.2.1.symm
    Ta := fun u0 => (hT u0).2.2.2.2.2.1.symm
    ASK := fun _ => rfl
    IO := fun u0 => (hT u0).2.2.2.2.2.2.1.symm
    HH := fun _ => by
      show x ^ CH * (Fm.L x M.i0).sc.b = x ^ CH * bTx x eps
      rw [sc_b M hx]
    del := fun u0 => (hT u0).2.2.2.2.2.2.2.symm
    η := fun _ => rfl
    e := fun _ => rfl
    delBar := rfl
    etaBar := rfl
    eBar := rfl }

theorem card_f (u0 : M.e.A) : (Fm.D x (M.pt u0)).R.f = (PhiSet (H := M.e.A)).card := by
  rw [M.hf u0, Lnk.card_PhiSet]; rfl


end Mod


end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters
open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

set_option maxHeartbeats 1600000 in
theorem second_chain_record_tied : ChainRecordCompatible := by
  intro eps Fm eD eL K cHH eK CL x hx hTie
  rintro ⟨M, A, ell, C, cT, N, η, θ, etaB, eB, h1, h2, h3, hAr, hl, hη, hI⟩
  have hT : ∀ u0, LocalTie (Fm.L x (M.pt u0)) M.m (famM M A u0) := fun u0 => hTie (M.pt u0) M.m (A u0) (M.hm u0)
  have hE := modified_field_eq M A ell N C.cHH etaB eB hx hl hT
  obtain ⟨hB, hLoss⟩ := hI
  obtain ⟨l1, l7, l9, l10, l11⟩ := LChain2.sizeConditions_of_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB
  obtain ⟨-, -, -, -, -, -, hDIV, hEC, hHC, hCnt, hSl, -, -, hWin, hRest, hCost, hSize⟩ := hB
  refine ⟨M.i0, M.m, (PhiSet (H := M.e.A)).card, M.pt, M.av, M.bv, ↥M.TT,
    inferInstance, { dataK M A ell N C.cHH etaB eB with logGam := Real.log (GamL (Fm.L x M.i0)) }, C,
    LChain2.XppH M.e.A (globM M etaB eB), ell, N, M.TT, M.T2, M.a, M.w, Equiv.refl _, LChain2.ePhi, η, XpTx x eps, θ,
    ?_, ?_, ?_, hAr, rfl, rfl, h1, h2, h3, ?_, ?_, hWin, ?_,
    hRest, hCost, hSize⟩
  · intro u0
    obtain ⟨t1, t2, -, t4, t5, t6, t7⟩ := M.tiePts u0
    exact ⟨t1, t2, card_f M u0, t4, t5, t6, t7⟩
  · intro u0
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩ :=
      M.tieGlobal hx N C.cHH etaB eB (etaM M A C.cHH) (eM M A) u0
    exact ⟨hE.a.symm.trans g1, hE.b.symm.trans g2, hE.b'.symm.trans g3, hE.k.symm.trans g4, hE.L.symm.trans g5,
      hE.La.symm.trans g6, hE.B0.symm.trans g7, hE.Nc.symm.trans g8, rfl, hE.LpL.symm.trans g10, hE.v.symm.trans g11,
      hE.lg.symm.trans g12, g13, (sc_Xpp M hx etaB eB).symm.trans g14, hη.trans g15, (sc_Xp M hx).symm.trans g16⟩
  · exact local_first_layer_agreement Fm x M.e M.m M.pt A (globM M etaB eB) C.cHH M.AD ell N M.TT M.T2 M.a M.w hT
  · exact ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, rfl, fun _ => rfl⟩
  · exact ⟨l1, hDIV, hEC, hHC, hCnt, hSl, l7, hLoss, l9, l10, l11⟩
  · exact ⟨le_refl _, le_refl _⟩

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

variable {D : D7} (L : SizeData₂ D) (m : ℕ) (A : Mx D)







theorem lam_le (hLen : ∀ u w, (famOf L m A).lenR u (plF D w) = (L.lenMN u w : ℝ))
    (hcard : ∀ u, Fintype.card ((D.fm u).lat 0).ι = D.duS u) (u : D.what₂.Word) (hd : 0 < D.duS u) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * c) :
    (famOf L m A).lam u ≤ c := by
  show lamOf L m A u ≤ c
  unfold lamOf
  refine Finset.fold_max_le _ |>.2 ⟨hc, fun z hz => ?_⟩
  have hzT0 : LChain2.prBelow z = (D.mem u).A.T := (Finset.mem_filter.1 hz).2
  have hzT : D.what₂.places.resChar (plB D z) = (D.mem u).A.T := (prBelow_eq D z).symm.trans hzT0
  have h1 := h (plB D z) hzT
  have h2 := hLen u (plB D z)
  have h3 : (fam0 L m A).lenR u z = (L.lenMN u (plB D z) : ℝ) :=
    (congrArg (fun y => (famOf L m A).lenR u y) (plF_plB D z)).symm.trans h2
  have hdM : (fam0 L m A).dM u = (D.duS u : ℝ) := by
    show (Fintype.card ((D.fm u).lat 0).ι : ℝ) = _
    rw [hcard u]
  have hpos : (0 : ℝ) < (D.duS u : ℝ) := by exact_mod_cast hd
  rw [hdM, div_le_iff₀ hpos, h3, mul_comm]
  exact h1

end Formalism.L2.GlobalTheoryTheory.FamRec

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec




end Formalism.L2.GlobalTheoryTheory.FamRec

end
