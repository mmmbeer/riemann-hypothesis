import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS

section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section IntP

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def IntP (x : D.host.E) : Prop :=
  ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = o

theorem one_not_mem_P : (1 : 𝓞 D.host.E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem mul_not_mem_P {s t : 𝓞 D.host.E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem intP_O (o : 𝓞 D.host.E) : IntP P (o : D.host.E) := ⟨1, one_not_mem_P P, o, by simp⟩

theorem intP_add {x y : D.host.E} (hx : IntP P x) (hy : IntP P y) : IntP P (x + y) := by
  obtain ⟨s1, hs1, o1, h1⟩ := hx
  obtain ⟨s2, hs2, o2, h2⟩ := hy
  refine ⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * s2 + o2 * s1, ?_⟩
  push_cast
  linear_combination (s2 : D.host.E) * h1 + (s1 : D.host.E) * h2

theorem intP_sum {ι : Type*} (s : Finset ι) (f : ι → D.host.E) (h : ∀ i ∈ s, IntP P (f i)) :
    IntP P (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intP_O P 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact intP_add P (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem valuation_le_one_of_isIntegralAt {x : D.host.E} (hx : IntP P x) : P.valuation D.host.E x ≤ 1 := by
  obtain ⟨s, hs, o, h⟩ := hx
  have e1 : algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  have := congrArg (P.valuation D.host.E) h
  rw [map_mul, ← e1, ← e2, P.valuation_of_algebraMap, P.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, one_mul] at this
  rw [this]
  exact P.intValuation_le_one o

end IntP

section Loc

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def LP (L : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L

theorem mem_LP {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ LP P L ↔ ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x ∈ L := by
  unfold LP Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  rfl

theorem smul_eq_E (o : 𝓞 D.host.E) (v : (VS D).V) : o • v = (o : D.host.E) • v :=
  (algebraMap_smul D.host.E o v).symm

theorem mem_localization_of_mem₃ {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ L) : x ∈ LP P L :=
  (mem_LP P).mpr ⟨1, one_not_mem_P P, by rw [one_smul]; exact hx⟩

theorem localization_mono₃ {L L' : Submodule (𝓞 D.host.E) (VS D).V} (hle : L ≤ L') {x : (VS D).V} (hx : x ∈ LP P L) :
    x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  exact (mem_LP P).mpr ⟨s, hs, hle h⟩


theorem sub_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {x y : (VS D).V} (hx : x ∈ LP P L) (hy : y ∈ LP P L) :
    x - y ∈ LP P L := sub_mem hx hy

theorem smul_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E} (hc : IntP P c) {x : (VS D).V}
    (hx : x ∈ LP P L) : c • x ∈ LP P L := by
  obtain ⟨s, hs, o, ho⟩ := hc
  obtain ⟨t, ht, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s * t, mul_not_mem_P P hs ht, ?_⟩
  have : (s * t) • (c • x) = o • (t • x) := by
    rw [smul_eq_E, smul_eq_E o, smul_eq_E t, smul_smul, smul_smul, ← ho]
    push_cast
    ring_nf
  rw [this]
  exact L.smul_mem o h

theorem LP_sum {L : Submodule (𝓞 D.host.E) (VS D).V} {ι : Type*} (s : Finset ι) (f : ι → (VS D).V)
    (h : ∀ i ∈ s, f i ∈ LP P L) : ∑ i ∈ s, f i ∈ LP P L := Submodule.sum_mem _ h

theorem LP_map {L L' : Submodule (𝓞 D.host.E) (VS D).V} (f : (VS D).V →ₗ[D.host.E] (VS D).V)
    (hf : ∀ v ∈ L, f v ∈ L') {x : (VS D).V} (hx : x ∈ LP P L) : f x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s, hs, ?_⟩
  rw [smul_eq_E, ← f.map_smul, ← smul_eq_E]
  exact hf _ h

theorem mem_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : ℕ} {x : (VS D).V} :
    x ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ ↔ ∃ l ∈ Λ, ((g : ℕ) : D.host.E) • l = x := by
  have hc : (((g : ℕ) : 𝓞 D.host.E) : D.host.E) = ((g : ℕ) : D.host.E) :=
    map_natCast (algebraMap (𝓞 D.host.E) D.host.E) g
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩

theorem nlam_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ G) (g : ℕ) :
    ∀ v ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ, (n : (VS D).V →ₗ[D.host.E] (VS D).V) v ∈
      Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := mem_gLam.mp hv
  exact mem_gLam.mpr ⟨n l, nlam_mem hn hl, by simp⟩

end Loc

section Coef

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_of_mem_spanO (F : FlagG S r T) {u : S.V} (hu : u ∈ Submodule.span (𝓞 E) (Set.range F.e)) :
    u ∈ F.X ∧ ∀ a, F.coefX u a ∈ (algebraMap (𝓞 E) E).range := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', rfl⟩ := hy
    refine ⟨e_mem_X F a', fun a => ?_⟩
    rw [coefX_e]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  | zero => exact ⟨zero_mem _, fun a => by rw [coefX_zero]; exact Subring.zero_mem _⟩
  | add v w _ _ hv hw =>
    exact ⟨add_mem hv.1 hw.1, fun a => by rw [coefX_add _ hv.1 hw.1]; exact Subring.add_mem _ (hv.2 a) (hw.2 a)⟩
  | smul o v _ hv =>
    have e : o • v = (algebraMap (𝓞 E) E o) • v := (algebraMap_smul E o v).symm
    refine ⟨by rw [e]; exact Submodule.smul_mem _ _ hv.1, fun a => ?_⟩
    rw [e, coefX_smul _ hv.1]
    exact Subring.mul_mem _ ⟨o, rfl⟩ (hv.2 a)

end Coef

section FixedConv

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

theorem fixedConv_at {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    LP P (XLam Λ G) = LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) := by
  obtain ⟨c, _, hc1, hloc⟩ := hC.1 P
  have hc : (fun a => c a • G.fl.e a) = G.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
  rw [hc] at hloc
  exact hloc

theorem e_mem_LP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : Fin D.R.rS) :
    G.fl.e a ∈ LP P Λ := by
  have h : G.fl.e a ∈ LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) :=
    mem_localization_of_mem₃ P (Submodule.subset_span ⟨a, rfl⟩)
  rw [← fixedConv_at P hC hP] at h
  exact localization_mono₃ P (fun v hv => by rw [XLam, Submodule.mem_inf] at hv; exact hv.1) h

theorem coef_intP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {w : (VS D).V}
    (hw : w ∈ LP P Λ) (hwX : w ∈ G.fl.X) (a : Fin D.R.rS) : IntP P (G.fl.coefX w a) := by
  obtain ⟨s, hs, hsw⟩ := (mem_LP P).mp hw
  have hsX : s • w ∈ G.fl.X := by rw [smul_eq_E]; exact Submodule.smul_mem _ _ hwX
  have h1 : s • w ∈ LP P (XLam Λ G) := mem_localization_of_mem₃ P (by rw [XLam, Submodule.mem_inf]; exact ⟨hsw, hsX⟩)
  rw [fixedConv_at P hC hP] at h1
  obtain ⟨t, ht, h2⟩ := (mem_LP P).mp h1
  obtain ⟨-, h3⟩ := coefX_of_mem_spanO G.fl h2
  obtain ⟨o, ho⟩ := h3 a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [smul_eq_E, smul_eq_E, coefX_smul _ (Submodule.smul_mem _ _ hwX), coefX_smul _ hwX] at ho
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  rw [← e2, ho]
  push_cast
  ring

theorem coef_intP_g {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) {Y : (VS D).V}
    (hY : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) (hYX : Y ∈ G.fl.X) (a : Fin D.R.rS) :
    IntP P (G.fl.coefX Y a / (gS D : D.host.E)) := by
  obtain ⟨s, hs, hsY⟩ := (mem_LP P).mp hY
  obtain ⟨l, hl, hlY⟩ := mem_gLam.mp hsY
  have hl' : l = ((s : D.host.E) / (gS D : D.host.E)) • Y := by
    rw [smul_eq_E] at hlY
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hlY, smul_smul, inv_mul_cancel₀ hg, one_smul]
  have hlX : l ∈ G.fl.X := by rw [hl']; exact Submodule.smul_mem _ _ hYX
  obtain ⟨t, ht, o, ho⟩ := coef_intP P hC hP (mem_localization_of_mem₃ P hl) hlX a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [hl', coefX_smul _ hYX] at ho
  rw [← ho]
  push_cast
  ring

end FixedConv

end PI.NRCW
end
end

section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem sgUp_eq_sum {K : Type} [Field K] [NumberField K] (U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    sgUp U = ∑ a : Fin r, U a.castSucc a.succ := by
  unfold sgUp
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [dif_pos (by simp)]
  rfl

theorem frame_d_mem {Λ : Submodule (𝓞 E) S.V} (G : LFlag S r T) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G)
    (b : Fin (r + 1)) : n (frame G b) - frame G b ∈ G.fl.X := by
  obtain ⟨he, hz⟩ := nlam_frame_mem G hn
  induction b using Fin.lastCases with
  | last => rw [frame_last]; exact hz
  | cast i => rw [frame_castSucc]; exact Xa_le_X _ _ (he i)

theorem coefX_finset_sum (F : FlagG S r T) {ι : Type*} (s : Finset ι) (v : ι → S.V) (hv : ∀ i, v i ∈ F.X)
    (a : Fin r) : F.coefX (∑ i ∈ s, v i) a = ∑ i ∈ s, F.coefX (v i) a := by
  induction s using Finset.induction_on with
  | empty => simp [coefX_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coefX_add _ (hv i) (Submodule.sum_mem _ fun j _ => hv j), ih]

theorem frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) :
    frameAct f (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) b = f b := by
  unfold frameAct
  simp [Matrix.one_apply]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fmat_sup (D : D7) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (a : Fin D.R.rS) :
    fmat D G n a.castSucc a.succ = G.fl.coefX (n (frame G a.succ) - frame G a.succ) a := by
  unfold fmat
  rw [if_neg (fun h => by have := congrArg Fin.val h; simp at this), zero_add, dif_pos (by simp)]
  rfl

theorem loc_entry (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (G₁ G₂ : LFlag (VS D) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (hfr : ∀ a, frame G₂ a = n (m (frame G₁ a))) (hC : IsFixedConv Λ (gS D) G)
    (hC₁ : IsFixedConv Λ (gS D) G₁) (hA1 : AdmWit Λ (gS D) G G₁ 1) (hA2 : AdmWit Λ (gS D) G G₂ 1)
    (hz₁ : G₁.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) (a : Fin D.R.rS) :
    IntP P ((fmat D G n a.castSucc a.succ + fmat D G₁ m a.castSucc a.succ) / (gS D : D.host.E)) := by
  set b := a.succ with hb
  have hw : ∀ c, frame G₁ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA1.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hw2 : ∀ c, frame G₂ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA2.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hwe : ∀ c : Fin D.R.rS, G₁.fl.e c - G.fl.e c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hw c.castSucc
    rw [frame_castSucc, frame_castSucc] at this
    exact this
  have hf1LP : ∀ c, frame G₁ c ∈ LP P Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => rw [frame_last]; exact mem_localization_of_mem₃ P hz₁
    | cast i => rw [frame_castSucc]; exact e_mem_LP P hC₁ hP i
  have hd'X := frame_d_mem G₁ hm b
  have hmLP : m (frame G₁ b) - frame G₁ b ∈ LP P Λ :=
    sub_mem_localization P (LP_map P (m : (VS D).V →ₗ[D.host.E] (VS D).V) (fun v hv => nlam_mem hm hv) (hf1LP b)) (hf1LP b)
  have hM'int : ∀ c, IntP P (G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c) :=
    fun c => coef_intP P hC₁ hP hmLP hd'X c
  have hd'sum : m (frame G₁ b) = frame G₁ b + ∑ c, G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c • G₁.fl.e c := by
    rw [coefX_sum _ hd'X]; abel
  have hM'zero : ∀ c : Fin D.R.rS, a.val < c.val → G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c = 0 := by
    intro c hac
    have hr : a.val + 1 < D.R.rS := by have := c.isLt; omega
    have hbi : b = (⟨a.val + 1, hr⟩ : Fin D.R.rS).castSucc := Fin.ext rfl
    rw [hbi, frame_castSucc]
    exact coefX_eq_zero _ ((nlam_frame_mem G₁ hm).1 _) c (by simp; omega)
  set M' := fun c => G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c with hM'
  set Y := (n (frame G b) - frame G b) + ∑ c, M' c • G.fl.e c + ∑ c, M' c • (n (G.fl.e c) - G.fl.e c) with hY
  have hYeq : Y = (frame G₂ b - frame G b) - (frame G₁ b - frame G b) + (frame G₁ b - frame G b) -
      n (frame G₁ b - frame G b) - n (∑ c, M' c • (G₁.fl.e c - G.fl.e c)) := by
    rw [hY, hfr b, hd'sum]
    simp only [map_add, map_sub, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  have hYLg : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    rw [hYeq]
    refine sub_mem (sub_mem (add_mem (sub_mem (hw2 b) (hw b)) (hw b)) ?_) ?_
    · exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _) (hw b)
    · exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _)
        (LP_sum P _ _ fun c _ => smul_mem_localization P (hM'int c) (hwe c))
  have hdX : ∀ c : Fin D.R.rS, n (G.fl.e c) - G.fl.e c ∈ G.fl.X := fun c => Xa_le_X _ _ ((nlam_frame_mem G hn).1 c)
  have hYX : Y ∈ G.fl.X := by
    refine add_mem (add_mem (frame_d_mem G hn b) (Submodule.sum_mem _ fun c _ => ?_))
      (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hdX c))
    exact Submodule.smul_mem _ _ (e_mem_X _ c)
  have hcoef := coef_intP_g P hC hP hg hYLg hYX a
  have hYa : G.fl.coefX Y a = fmat D G n a.castSucc a.succ + fmat D G₁ m a.castSucc a.succ := by
    rw [fmat_sup, fmat_sup, hY]
    rw [coefX_add _ (add_mem (frame_d_mem G hn b) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X _ c)))
      (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hdX c)),
      coefX_add _ (frame_d_mem G hn b) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X _ c)),
      coefX_finset_sum _ _ _ (fun c => Submodule.smul_mem _ _ (e_mem_X _ c)),
      coefX_finset_sum _ _ _ (fun c => Submodule.smul_mem _ _ (hdX c))]
    have h3 : ∑ c, G.fl.coefX (M' c • (n (G.fl.e c) - G.fl.e c)) a = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [coefX_smul _ (hdX c)]
      by_cases hac : a.val < c.val
      · rw [show M' c = 0 from hM'zero c hac, zero_mul]
      · rw [coefX_eq_zero _ ((nlam_frame_mem G hn).1 c) a (by omega), mul_zero]
    rw [h3, add_zero]
    simp only [coefX_smul_e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  rw [← hYa]
  exact hcoef

theorem stepLoc (D : D7) : StepLoc D := by
  intro Λ T T' G G₁ G₂ n m hn hm hfr hC hC₁ hA1 hA2 _ hz₁ P hP
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (by
    unfold gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  rw [sgUp_eq_sum (fmat D G n), sgUp_eq_sum (fmat D G₁ m), ← Finset.sum_add_distrib, Finset.sum_div]
  exact valuation_le_one_of_isIntegralAt P (intP_sum P _ _ fun a _ =>
    loc_entry D Λ G G₁ G₂ n m hn hm hfr hC hC₁ hA1 hA2 hz₁ P hP hg a)

end PI.NRCW
end
end
