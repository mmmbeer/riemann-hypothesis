import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.CupCastRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TorsOfForall

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace CrystallineSemistableComparison.AdicCoh

section Heq
variable {q : ℕ} {E : Spc}

theorem eq_cast_of_heq {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n' i'} {y : Ht q E n i} (h : HEq x y) :
    x = y.cast h1 h2 := by
  exact eq_of_heq (h.trans (cast_heq h1 h2 y).symm)

theorem heq_zero {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') {x : Ht q E n i} (h : HEq x (0 : Ht q E n' i')) : x = 0 := by
  subst h1 h2
  exact eq_of_heq h

theorem cup_heq {n m i j n' m' i' j' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : m = m') (h4 : j = j')
    {a : Ht q E n i} {a' : Ht q E n' i'} {b : Ht q E m j} {b' : Ht q E m' j'} (ha : HEq a a') (hb : HEq b b') :
    HEq (cup q a b) (cup q a' b') := by
  subst h1 h2 h3 h4
  cases ha
  cases hb
  exact HEq.rfl

end Heq

section Root
variable (q : ℕ) [NeZero q] {E : Spc} (hR : GlobalTheory.EtC.DivisorRingCompatibility) (hinv : Inv q E) {e : ℤ} (u : Ht q E 0 e) (v : Ht q E 0 (-e))
include hR hinv

theorem cup_one_right {n i : ℤ} (b : Ht q E n i) : HEq (cup q b (one q E)) b := by
  obtain ⟨h1, -, h3⟩ := hR q E
  rw [h3 b (one q E), h1 hinv b]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _)

theorem root_left (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b v) u) b := by
  obtain ⟨-, h2, -⟩ := hR q E
  rw [h2 b v u, hvu, cup_cast_right]
  exact (cast_heq _ _ _).trans ((cast_heq _ _ _).trans (cup_one_right q hR hinv b))

theorem root_right (hvu : cup q v u = (one q E).cast (by ring) (by ring)) {n i : ℤ} (b : Ht q E n i) :
    HEq (cup q (cup q b u) v) b := by
  obtain ⟨-, h2, h3⟩ := hR q E
  rw [h2 b u v, h3 u v, hvu]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, cast_cast, cup_cast_right]
  exact (cast_heq _ _ _).trans (cup_one_right q hR hinv b)

end Root

section PD
variable {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Spec (CommRingCat.of k)) [IsProper p]
  (d : ℕ) [SmoothOfRelativeDimension d p] (q : ℕ) [NeZero q] (hq : IsUnit (q : k))
include p hq

theorem vanish (hI : ZIn) (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Ht q (sch.obj Y) n 0) := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  haveI : Subsingleton (Ht q (sch.obj Y) (2 * d - n) (d - 0)) :=
    (hI.a9 (ZMod q) (tw q ((d : ℤ) - 0))).1 _ _ (by omega)
  obtain ⟨c, -, hc⟩ := htr n 0 0
  refine ⟨fun a b => (hc a fun y => ?_).trans (hc b fun y => ?_).symm⟩ <;>
    simp [Subsingleton.elim y 0, cast_zero]

theorem nondeg (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) (i j : ℤ) (hij : i + j = 2 * d)
    (a : Ht q (sch.obj Y) i 0) (h : ∀ b : Ht q (sch.obj Y) j 0, cup q a b = 0) : a = 0 := by
  obtain ⟨tr, htr⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  have key : ∀ b' : Ht q (sch.obj Y) (2 * d - i) (d - 0), cup q a b' = 0 := by
    intro b'
    have hc := h ((cup q b' v).cast (by omega) (by omega))
    have s1 : cup q a (cup q b' v) = 0 :=
      heq_zero (by omega) (by omega)
        ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (cast_heq _ _ _).symm).trans (heq_of_eq hc))
    have s3 : cup q (cup q a (cup q b' v)) u = 0 := by rw [s1, map_zero, AddMonoidHom.zero_apply]
    have s4 : HEq (cup q a (cup q (cup q b' v) u)) (cup q (cup q a (cup q b' v)) u) := by
      rw [(hI.ring q _).2.1 a (cup q b' v) u]
      exact (cast_heq _ _ _).symm
    exact heq_zero (by omega) (by omega)
      ((cup_heq rfl rfl (by omega) (by omega) HEq.rfl (root_left q hI.ring hinv u v hvu b').symm).trans
        (s4.trans (heq_of_eq s3)))
  obtain ⟨c, -, hc⟩ := htr i 0 0
  have ha : a = c := hc a (fun b => by simp [key b, cast_zero])
  have h0 : (0 : Ht q (sch.obj Y) i 0) = c := hc 0 (fun b => by simp [cast_zero])
  exact ha.trans h0.symm

theorem top_cyclic (hI : ZIn) (hprim : Nonempty (Prim q Γ(Y, ⊤))) (hinv : Inv q (sch.obj Y)) :
    ∃ g : Ht q (sch.obj Y) (2 * d) 0, ∀ x, ∃ n : ℤ, x = n • g := by
  obtain ⟨tr, -⟩ := hI.e8 q k hq p d
  obtain ⟨u, v, hvu⟩ := hI.root q Y hprim (d : ℤ)
  refine ⟨(cup q (tr.symm 1) v).cast (by ring) (by ring), fun x => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      ((cup q x u).cast (by ring) (by ring) : Ht q (sch.obj Y) (2 * d) d) = m • tr.symm 1 := by
    refine ⟨((tr ((cup q x u).cast (by ring) (by ring))).val : ℤ), tr.injective ?_⟩
    rw [map_zsmul, AddEquiv.apply_symm_apply, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨m, ?_⟩
  have hc : cup q (m • tr.symm 1) v = m • cup q (tr.symm 1) v := by
    rw [map_zsmul]
    rfl
  rw [← cast_smul]
  refine eq_cast_of_heq _ _ ?_
  refine (root_right q hI.ring hinv u v hvu x).symm.trans ?_
  rw [← hc, ← hm]
  exact cup_heq (by ring) (by ring) rfl rfl (cast_heq _ _ _).symm HEq.rfl

end PD

end CrystallineSemistableComparison.AdicCoh
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable (l : ℕ) [Fact l.Prime]

theorem castH_apply {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i) :
    castH h1 h2 x = x.cast h1 h2 := rfl

section Cup
variable {E : Spc} {n m i j n' i' : ℤ} (hI : ZIn) (h1 : n + m = n') (h2 : i + j = i')

def cupL (x : Hl l E n i) (y : Hl l E m j) : Hl l E n' i' := ⟨_, cup_mem l hI E h1 h2 x y⟩

theorem pull_cupL {E' : Spc} (f : E' ⟶ E) (x : Hl l E n i) (y : Hl l E m j) :
    pullHl l f n' i' (cupL l hI h1 h2 x y) = cupL l hI h1 h2 (pullHl l f n i x) (pullHl l f m j y) := by
  apply Subtype.ext
  funext k
  have := neZero_pow l k
  change pull _ f _ n' ((cup _ _ _).cast h1 h2) = (cup _ (pull _ f _ n _) (pull _ f _ m _)).cast h1 h2
  rw [pull_cast, (hI.nat (l ^ k)).1 f]

theorem cupL_zero_right (x : Hl l E n i) : cupL l hI h1 h2 x (0 : Hl l E m j) = 0 := by
  apply Subtype.ext
  funext k
  change (cup _ _ 0).cast h1 h2 = 0
  rw [map_zero, cast_zero]

theorem cupL_add_left (x x' : Hl l E n i) (y : Hl l E m j) :
    cupL l hI h1 h2 (x + x') y = cupL l hI h1 h2 x y + cupL l hI h1 h2 x' y := by
  apply Subtype.ext
  funext k
  change (cup _ (x.1 k + x'.1 k) (y.1 k)).cast h1 h2 = (cup _ _ _).cast h1 h2 + (cup _ _ _).cast h1 h2
  rw [map_add, AddMonoidHom.add_apply, cast_add]

theorem cupL_smul_left (r : ℤ_[l]) (x : Hl l E n i) (y : Hl l E m j) :
    cupL l hI h1 h2 (r • x) y = r • cupL l hI h1 h2 x y := by
  apply Subtype.ext
  funext k
  change (cup _ (r • x.1 k) (y.1 k)).cast h1 h2 = r • (show HtL l k E n' i' from (cup _ (x.1 k) (y.1 k)).cast h1 h2)
  rw [HtL.smul_eq l k k le_rfl E n i r (x.1 k), HtL.smul_eq l k k le_rfl E n' i' r]
  erw [map_nsmul, AddMonoidHom.nsmul_apply, cast_nsmul]

def cupR (y : Hl l E m j) : Hl l E n i →ₗ[ℤ_[l]] Hl l E n' i' where
  toFun x := cupL l hI h1 h2 x y
  map_add' x x' := cupL_add_left l hI h1 h2 x x' y
  map_smul' r x := cupL_smul_left l hI h1 h2 r x y

end Cup

section Sum
variable (hI : ZIn) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) (n i : ℤ)
include hI hj

theorem sum_eq (x x' : Hl l (sch.obj X) n i) (h : ∀ s, pullHl l (sch.map (j s)) n i x = pullHl l (sch.map (j s)) n i x') :
    x = x' :=
  sub_eq_zero.1 (sum_inj l hI j hj n i _ fun s => by rw [map_sub, h, sub_self])

def extS (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) : Hl l (sch.obj X) n i :=
  (sum_ext l hI j hj n i (Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y)).choose

theorem extS_spec (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) (t : Fin r) :
    pullHl l (sch.map (j t)) n i (extS l hI j hj n i s y) = Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y t :=
  (sum_ext l hI j hj n i (Pi.single (M := fun t => Hl l (sch.obj (Y t)) n i) s y)).choose_spec t

theorem extS_self (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) :
    pullHl l (sch.map (j s)) n i (extS l hI j hj n i s y) = y := by
  rw [extS_spec]; exact Pi.single_eq_same _ _

theorem extS_ne (s : Fin r) (y : Hl l (sch.obj (Y s)) n i) {t : Fin r} (ht : t ≠ s) :
    pullHl l (sch.map (j t)) n i (extS l hI j hj n i s y) = 0 := by
  rw [extS_spec]; exact Pi.single_eq_of_ne ht _

theorem tors_of_restr (x : Hl l (sch.obj X) n i) (h : ∀ s, ∃ e : ℕ, (l : ℤ_[l]) ^ e • pullHl l (sch.map (j s)) n i x = 0) :
    ∃ e : ℕ, (l : ℤ_[l]) ^ e • x = 0 := by
  choose e he using h
  refine ⟨∑ s, e s, sum_inj l hI j hj n i _ fun s => ?_⟩
  rw [map_smul, ← Finset.add_sum_erase _ _ (Finset.mem_univ s), pow_add, mul_comm, mul_smul, he, smul_zero]

end Sum

theorem unitQ (k : ℕ) : IsUnit (((l ^ k : ℕ) : ℕ) : PadicAlgCl l) :=
  isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (pow_ne_zero k (Fact.out : l.Prime).ne_zero))

section Y
variable (hI : ZIn) {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of (PadicAlgCl l))) [IsProper p]
include hI p

theorem ysys (n i : ℤ) : Adic.IsSys l (fun k => HtL l k (sch.obj Y) n i) (fun m m' => red (l ^ m) (l ^ m') (sch.obj Y) n i) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine isSys l hI Y (AdicGeo.unit_of_over p l) n i fun k => ?_
  have := neZero_pow l k
  exact hI.e4 (l ^ k) (PadicAlgCl l) (unitQ l k) p n i

variable [IsIntegral Y] (d : ℕ) [SmoothOfRelativeDimension d p]

theorem hl_vanish (n : ℤ) (hn : 2 * (d : ℤ) < n) : Subsingleton (Hl l (sch.obj Y) n 0) := by
  refine ⟨fun x y => Subtype.ext (funext fun k => ?_)⟩
  have := neZero_pow l k
  exact (vanish p d (l ^ k) (unitQ l k) hI n hn).elim _ _

theorem hl_cyclic (N : ℤ) (hN : N = 2 * d) : ∃ g : Hl l (sch.obj Y) N 0, ∀ x, ∃ c : ℤ_[l], x = c • g := by
  subst hN
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have := neZero_pow l 1
  obtain ⟨g, hg, hc⟩ := (ysys l hI p _ 0).cyclic (S := HlSub l (sch.obj Y) _ 0) (fun _ => Iff.rfl)
    (top_cyclic p d (l ^ 1) (unitQ l 1) hI (AdicGeo.prim_of_over p _) (AdicGeo.inv_sch _ (AdicGeo.unit_of_over p _)))
  refine ⟨⟨g, hg⟩, fun x => ?_⟩
  obtain ⟨c, e⟩ := hc x.1 x.2
  exact ⟨c, Subtype.ext e⟩

theorem hl_nondeg (i j N : ℤ) (hij : i + j = N) (hN : N = 2 * d) (x : Hl l (sch.obj Y) i 0)
    (h : ∀ y : Hl l (sch.obj Y) j 0, ∃ e : ℕ, (l : ℤ_[l]) ^ e • cupL l hI hij (add_zero 0) x y = 0) :
    ∃ e : ℕ, (l : ℤ_[l]) ^ e • x = 0 := by
  obtain ⟨g, hg⟩ := hl_cyclic l hI p d N hN
  have hnd : ∀ k (a : HtL l k (sch.obj Y) i 0),
      (∀ b : HtL l k (sch.obj Y) j 0, ((cup (l ^ k)).compr₂ (castH hij (add_zero (0 : ℤ)))) a b = 0) → a = 0 := by
    intro k a hb
    have := neZero_pow l k
    exact nondeg p d (l ^ k) (unitQ l k) hI (AdicGeo.prim_of_over p _) (AdicGeo.inv_sch _ (AdicGeo.unit_of_over p _))
      i j (hij.trans hN) a fun b => (cast_eq_zero _ _ _).1 (by simpa only [AddMonoidHom.compr₂_apply, castH_apply] using hb b)
  obtain ⟨e, he⟩ := Adic.pair_tors (ysys l hI p i 0) (ysys l hI p j 0) (ysys l hI p N 0)
    (SA := HlSub l (sch.obj Y) i 0) (SB := HlSub l (sch.obj Y) j 0) (SC := HlSub l (sch.obj Y) N 0)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (fun k => (cup (l ^ k)).compr₂ (castH hij (add_zero (0 : ℤ))))
    (fun m n a b hmn => by
      have := neZero_pow l m
      simp only [AddMonoidHom.compr₂_apply]
      show red (l ^ m) (l ^ n) (sch.obj Y) N 0 (Ht.cast hij (add_zero 0) (cup (l ^ m) a b)) =
        Ht.cast hij (add_zero 0) (cup (l ^ n) (red (l ^ m) (l ^ n) _ i 0 a) (red (l ^ m) (l ^ n) _ j 0 b))
      rw [red_cast, (hI.a11 (l ^ m) (l ^ n) (pow_dvd_pow l hmn) _).1])
    hnd ⟨g.1, g.2, fun z hz => by obtain ⟨c, e⟩ := hg ⟨z, hz⟩; exact ⟨c, congrArg Subtype.val e⟩⟩ x.2
    (fun y hy => by
      obtain ⟨e, he⟩ := h ⟨y, hy⟩
      exact ⟨e, congrArg Subtype.val he⟩)
  exact ⟨e, Subtype.ext he⟩

end Y

end CrystallineSemistableComparison.AdicCoh
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem pow_mono_tors {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (y : N) {m n : ℕ} (h : m ≤ n)
    (hy : (l : ℤ_[l]) ^ m • y = 0) : (l : ℤ_[l]) ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]

theorem tors_of_tmul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (hc : c ≠ 0) (y : N)
    (h : c ⊗ₜ[ℤ_[l]] y = 0) : ∃ n : ℕ, (l : ℤ_[l]) ^ n • y = 0 := by
  refine (Adic.tmul_eq_zero y).1 ?_
  have e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = c⁻¹ • (c ⊗ₜ[ℤ_[l]] y) := by
    rw [smul_tmul', smul_eq_mul, inv_mul_cancel₀ hc]
  rw [e, h, smul_zero]

theorem tmul_zero_of {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) {n : ℕ}
    (h : (l : ℤ_[l]) ^ n • y = 0) : c ⊗ₜ[ℤ_[l]] y = 0 := by
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y = 0 := (Adic.tmul_eq_zero y).2 ⟨_, h⟩
  rw [← mul_one c, ← smul_eq_mul, ← smul_tmul', h1, smul_zero]

theorem unit_geom (M : Model l K) : IsUnit ((l : ℕ) : Γ(GlobalTheory.Et.geom (PadicAlgCl l) M.q, ⊤)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact AdicGeo.unit_of_over (AdicGeo.str M) l

theorem fin_levels (hI : ZIn) (M : Model l K) (h : M.Good) (n i : ℤ) (k : ℕ) :
    Finite (Ht (l ^ k) (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n i) := by
  have := AdicGeo.proper_str h
  have := neZero_pow l k
  have hu : IsUnit ((l ^ k : ℕ) : PadicAlgCl l) := (Nat.cast_ne_zero.2 (NeZero.ne _)).isUnit
  exact hI.e4 (l ^ k) (PadicAlgCl l) hu (AdicGeo.str M) n i

theorem fin_of (hI : ZIn) (M : Model l K) (h : M.Good) (j : ℕ) : FiniteDimensional ℚ_[l] (M.V j) := by
  have hS := isSys l hI _ (unit_geom M) (j : ℤ) 0 (fin_levels hI M h _ _)
  have : Module.Finite ℤ_[l] (Hl l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) (j : ℤ) 0) :=
    hS.finite (fun _ => Iff.rfl)
  exact Adic.fd

theorem comp_of (hI : ZIn) (G : Model l K → Prop) (hG : ∀ M, G M → M.Good) (hC : CompM G) (M : Model l K) (hM : G M) :
    ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p), (∀ a, G (P a) ∧ (P a).Conn (d a)) ∧
    ∀ (j : ℕ) (v : M.V j), (∀ a, Model.pullV (u a) (hu a) j v = 0) → v = 0 := by
  obtain ⟨r, P, d, u, hu, hsum, hP⟩ := hC M hM
  refine ⟨r, P, d, u, hu, hP, fun j v hv => ?_⟩
  have hs := AdicGeo.isSum_geom u hu hsum
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  by_cases hc : c = 0
  · rw [hc, zero_tmul]
  have ht : ∀ a, ∃ n : ℕ, (l : ℤ_[l]) ^ n • pullHl l (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q
      (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))) j 0 x = 0 := fun a =>
    tors_of_tmul c hc _ ((LinearMap.baseChange_tmul _ _ _).symm.trans (hv a))
  choose n hn using ht
  refine tmul_zero_of c x (n := ∑ a, n a) (sum_inj l hI _ hs j 0 _ fun a => ?_)
  refine ((pullHl l _ j 0).map_smul _ x).trans ?_
  exact pow_mono_tors _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (hn a)

end CrystallineSemistableComparison.AdicCoh
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gen_tmul_smul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) (y : N) :
    (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (a • y) = algebraMap ℤ_[l] ℚ_[l] a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [tmul_smul, algebraMap_smul]

theorem gen_tmul_eq {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (y : N) :
    c ⊗ₜ[ℤ_[l]] y = c • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [smul_tmul', smul_eq_mul, mul_one]

theorem toV_smul (M : Model l K) (n : ℕ) (a : ℤ_[l]) (x : M.T n) :
    M.toV n (a • x) = algebraMap ℤ_[l] ℚ_[l] a • M.toV n x :=
  gen_tmul_smul (N := Hl l M.spc n 0) a x

theorem tmul_eq_smul_toV (M : Model l K) (n : ℕ) (c : ℚ_[l]) (x : M.T n) :
    (c ⊗ₜ[ℤ_[l]] (show Hl l M.spc n 0 from x) : M.V n) = c • M.toV n x :=
  gen_tmul_eq (N := Hl l M.spc n 0) c x

theorem pull_gal_inj (M : Model l K) (n : ℤ) (τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (x : Hl l M.spc n 0)
    (h : pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ)) n 0 x = 0) : x = 0 := by
  have e := congrArg (pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ⁻¹)) n 0) h
  rw [← LinearMap.comp_apply, ← pullHl_comp, ← Functor.map_comp, ← galMap_mul, inv_mul_cancel, galMap_one,
    CategoryTheory.Functor.map_id, pullHl_id, map_zero] at e
  exact e

theorem pull_comp_apply {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) (x : Hl l E'' n i) :
    pullHl l (f ≫ g) n i x = pullHl l f n i (pullHl l g n i x) := by
  rw [pullHl_comp]; rfl

end CrystallineSemistableComparison.AdicCoh
end
end
