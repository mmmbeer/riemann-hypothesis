import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange

section
namespace Formalism.HermitianLattices.Ext.L3.SecondPropositionFree

open NormLifting

variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

theorem card_lift_pred [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n : A} (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) (p : (Fin M → B) → Prop)
    (hsurj : ∀ y : Fin M → A, p (fun i => π (y i)) → ∀ w ∈ fixSub σ (RingHom.ker π),
      w ∈ (linPart σ (RingHom.ker π) y).range) :
    Nat.card {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n} := by
  classical
  have hIσ : ∀ a ∈ RingHom.ker π, σ a ∈ RingHom.ker π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [hστ, ha, map_zero]
  haveI : Finite B := Finite.of_surjective π hπ

  have hker : Nat.card (RingHom.ker π) = q ^ 2 := by
    have h1 : Nat.card A = Nat.card (RingHom.ker π) * Nat.card B := by
      refine card_eq_mul_of_fibers π _ (fun b => ?_)
      obtain ⟨a0, ha0⟩ := hπ b
      exact Nat.card_congr
        { toFun := fun a => ⟨a.1 - a0, by rw [RingHom.mem_ker, map_sub, a.2, ha0, sub_self]⟩
          invFun := fun k => ⟨k.1 + a0, by rw [map_add, RingHom.mem_ker.mp k.2, ha0, zero_add]⟩
          left_inv := fun a => Subtype.ext (sub_add_cancel a.1 a0)
          right_inv := fun k => Subtype.ext (add_sub_cancel_right k.1 a0) }
    have hB : 0 < Nat.card B := Nat.card_pos
    rw [hq] at h1
    exact (Nat.eq_of_mul_eq_mul_right hB h1).symm
  have hq0 : 0 < q := by
    have hk : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hker] at hk
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at hk)

  have hfix : Nat.card (fixSub σ (RingHom.ker π)) = q := by
    have h := card_fixSub_sq hσ hIσ he
    rw [hker] at h
    exact Nat.pow_left_injective two_ne_zero h

  have hrange : ∀ x0 : Fin M → A, p (fun i => π (x0 i)) →
      Nat.card (linPart σ (RingHom.ker π) x0).range = q := by
    intro x0 hp
    have hR : (linPart σ (RingHom.ker π) x0).range = fixSub σ (RingHom.ker π) := by
      ext w
      rw [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨δ, rfl⟩
        show linPart σ (RingHom.ker π) x0 δ ∈ RingHom.ker π ∧
          σ (linPart σ (RingHom.ker π) x0 δ) = linPart σ (RingHom.ker π) x0 δ
        refine ⟨?_, ?_⟩
        · rw [linPart_apply]
          refine Ideal.sum_mem _ fun i _ => Ideal.add_mem _ ?_ ?_
          · exact Ideal.mul_mem_left _ _ (δ i).2
          · exact Ideal.mul_mem_right _ _ (hIσ _ (δ i).2)
        · rw [linPart_apply, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_add, map_mul, hσ]
          ring
      · intro hw
        exact AddMonoidHom.mem_range.mp (hsurj x0 hp w hw)
    rw [hR, hfix]

  have hnorm : ∀ x : Fin M → A, ∑ i, σ (x i) * x i = n → ∑ i, τ (π (x i)) * π (x i) = π n := by
    intro x hx
    rw [← hx, map_sum]
    simp only [map_mul, hστ]
  refine card_eq_mul_of_fibers
    (fun x : {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =>
      (⟨fun i => π (x.1 i), x.2.1, hnorm x.1 x.2.2⟩ :
        {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n})) _ ?_
  intro y
  choose x0 hx0 using fun i => hπ (y.1 i)
  have hpx0 : p (fun i => π (x0 i)) := by
    have h : (fun i => π (x0 i)) = y.1 := funext hx0
    rw [h]
    exact y.2.1
  have hNx0 : π (∑ i, σ (x0 i) * x0 i) = π n := by
    rw [map_sum]
    simp only [map_mul, hστ, hx0]
    exact y.2.2
  have ht : n - ∑ i, σ (x0 i) * x0 i ∈ fixSub σ (RingHom.ker π) := by
    show n - ∑ i, σ (x0 i) * x0 i ∈ RingHom.ker π ∧
      σ (n - ∑ i, σ (x0 i) * x0 i) = n - ∑ i, σ (x0 i) * x0 i
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, map_sub, hNx0, sub_self]
    · rw [map_sub, hn, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, hσ]
      ring

  have key : Nat.card {δ : Fin M → RingHom.ker π //
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i} = q ^ (2 * M - 1) := by
    have hfib := card_fiber_mul_card_range (linPart σ (RingHom.ker π) x0) _ (hsurj x0 hpx0 _ ht)
    rw [hrange x0 hpx0, Nat.card_fun, hker, Nat.card_eq_fintype_card (α := Fin M), Fintype.card_fin,
      ← pow_mul] at hfib
    have hpow : q ^ (2 * M) = q ^ (2 * M - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hfib
    exact Nat.eq_of_mul_eq_mul_right hq0 hfib

  have hfwd : ∀ x : Fin M → A, (∀ i, π (x i) = y.1 i) → ∀ i, x i - x0 i ∈ RingHom.ker π := by
    intro x hx i
    rw [RingHom.mem_ker, map_sub, hx, hx0, sub_self]
  have hexp : ∀ (x : Fin M → A) (hd : ∀ i, x i - x0 i ∈ RingHom.ker π),
      ∑ i, σ (x i) * x i = ∑ i, σ (x0 i) * x0 i +
        linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hd i⟩) := by
    intro x hd
    rw [linPart_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : σ (x i - x0 i) * (x i - x0 i) = 0 :=
      hsq _ _ (RingHom.mem_ker.mp (hIσ _ (hd i))) (RingHom.mem_ker.mp (hd i))
    dsimp only
    rw [map_sub] at h0 ⊢
    linear_combination h0
  have hLfwd : ∀ (x : Fin M → A) (hx : ∀ i, π (x i) = y.1 i), ∑ i, σ (x i) * x i = n →
      linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hfwd x hx i⟩) =
        n - ∑ i, σ (x0 i) * x0 i := by
    intro x hx hN
    have h := hexp x (hfwd x hx)
    rw [hN] at h
    rw [h]
    ring
  have hdmem : ∀ (δ : Fin M → RingHom.ker π) i, (x0 i + δ i) - x0 i ∈ RingHom.ker π := by
    intro δ i
    rw [add_sub_cancel_left]
    exact (δ i).2
  have hbinv : ∀ (δ : Fin M → RingHom.ker π) i, π (x0 i + δ i) = y.1 i := by
    intro δ i
    rw [map_add, RingHom.mem_ker.mp (δ i).2, add_zero, hx0]
  have hpinv : ∀ δ : Fin M → RingHom.ker π, p (fun i => π (x0 i + δ i)) := by
    intro δ
    have h : (fun i => π (x0 i + δ i)) = y.1 := funext (hbinv δ)
    rw [h]
    exact y.2.1
  have hNinv : ∀ δ : Fin M → RingHom.ker π,
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i →
        ∑ i, σ (x0 i + δ i) * (x0 i + δ i) = n := by
    intro δ hδ
    have h := hexp (fun i => x0 i + δ i) (hdmem δ)
    have hδ' : (fun i => (⟨(x0 i + δ i) - x0 i, hdmem δ i⟩ : RingHom.ker π)) = δ := by
      funext i
      exact Subtype.ext (add_sub_cancel_left (x0 i) (δ i : A))
    rw [hδ', hδ] at h
    rw [h]
    ring
  rw [← key]
  exact Nat.card_congr
    { toFun := fun x => ⟨fun i => ⟨x.1.1 i - x0 i,
          hfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) i⟩,
        hLfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) x.1.2.2⟩
      invFun := fun δ => ⟨⟨fun i => x0 i + δ.1 i, hpinv δ.1, hNinv δ.1 δ.2⟩,
        Subtype.ext (funext fun i => hbinv δ.1 i)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (funext fun i =>
        show x0 i + (x.1.1 i - x0 i) = x.1.1 i by ring))
      right_inv := fun δ => Subtype.ext (funext fun i => Subtype.ext
        (show x0 i + (δ.1 i : A) - x0 i = (δ.1 i : A) by ring)) }

theorem mem_range_linPart (I : Ideal A) {M : ℕ} (y : Fin M → A) (i₀ : Fin M)
    {b : A} (hb : σ (y i₀) * b + σ b * y i₀ = 1) {w : A} (hw : w ∈ fixSub σ I) :
    w ∈ (linPart σ I y).range := by
  have hw' : w ∈ I ∧ σ w = w := hw
  obtain ⟨hwI, hσw⟩ := hw'
  classical
  refine ⟨fun i => if i = i₀ then ⟨b * w, I.mul_mem_left b hwI⟩ else 0, ?_⟩
  rw [linPart_apply, Finset.sum_eq_single i₀]
  · rw [if_pos rfl]
    show σ (y i₀) * (b * w) + σ (b * w) * y i₀ = w
    rw [map_mul, hσw]
    linear_combination w * hb
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

open NormLifting

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

abbrev AQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  𝓞 K ⧸ extP K 𝔭 ^ k

def sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : AQ K 𝔭 k →+* AQ K 𝔭 k :=
  conjQ (extP K 𝔭 ^ k) (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k)

theorem sg_mk (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    sg hF 𝔭 k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (conjO K a) := conjQ_mk _ _ a

theorem sg_sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) :
    sg hF 𝔭 k (sg hF 𝔭 k a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [sg_mk, sg_mk, conjO_conjO]

def InQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) : Prop :=
  ∃ z ∈ extP K 𝔭, Ideal.Quotient.mk (extP K 𝔭 ^ k) z = a

theorem inQ_mk (𝔭 : Ideal (𝓞 F)) {k : ℕ} (hk : 1 ≤ k) (y : 𝓞 K) :
    InQ 𝔭 k (Ideal.Quotient.mk (extP K 𝔭 ^ k) y) ↔ y ∈ extP K 𝔭 := by
  unfold InQ
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hd : z - y ∈ extP K 𝔭 ^ k := Ideal.Quotient.eq.mp hzy
    have hd' : z - y ∈ extP K 𝔭 := Ideal.pow_le_self (by omega) hd
    have hy := sub_mem hz hd'
    simpa using hy
  · intro hy
    exact ⟨y, hy, rfl⟩

def cnt (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

def cntP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (¬ ∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

def cntI (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

theorem cnt_eq_normRepCount (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = normRepCount K (extP K 𝔭 ^ k) M n :=
  (normRepCount_eq _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k) M n).symm

theorem finite_AQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (AQ K 𝔭 k) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ (idealPowerSpanBounds.map_ne_bot_of_isMaximal h𝔭))

theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  unfold extP
  rw [Ideal.absNorm_algebraMap, ← MeanB.finrank_eq_two hK hF]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm

theorem card_AQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Nat.card (AQ K 𝔭 k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, absNorm_extP hK hF, ← pow_mul]

theorem card_split {X : Type*} [Finite X] (p r : X → Prop) :
    Nat.card {x // r x} = Nat.card {x // ¬ p x ∧ r x} + Nat.card {x // p x ∧ r x} := by
  classical
  haveI := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact h1.1 h2.1

theorem cnt_eq_add (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = cntP hF 𝔭 k M n + cntI hF 𝔭 k M n := by
  haveI := finite_AQ (K := K) h𝔭 k
  unfold cnt cntP cntI
  exact card_split (fun x : Fin M → AQ K 𝔭 k => ∀ i, InQ 𝔭 k (x i)) _

theorem exists_tr_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 K} (ha : a ∉ extP K 𝔭) (N : ℕ) :
    ∃ b : 𝓞 K, conjO K a * b + conjO K b * a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  have h1 : ∃ b : 𝓞 K, conjO K a * b + conjO K b * a ∉ extP K 𝔭 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon 1
    have e2 := hcon θ
    apply ha
    have e3 : (θ - conjO K θ) * a ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one]
      have := (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left θ e1) e2
      have e : θ * (conjO K a * 1 + conjO K 1 * a) - (conjO K a * θ + conjO K θ * a) =
          (θ - conjO K θ) * a := by rw [map_one]; ring
      rwa [e] at this
    have := idealPowerSpanBounds.mem_of_unit_mul_mem hθ e3
    rwa [pow_one] at this
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := idealPowerSpanBounds.exists_tr hF (conjO K a * b)
  rw [map_mul, conjO_conjO, mul_comm a] at hc
  have hc𝔭 : c ∉ 𝔭 := by
    intro h
    apply hb
    rw [← hc]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 hc𝔭 N
  refine ⟨ι u * b, ?_⟩
  have e : conjO K a * (ι u * b) + conjO K (ι u * b) * a - 1 = ι (u * c - 1) := by
    rw [map_mul (conjO K), idealPowerSpanBounds.conjO_map hF, map_sub, map_mul, map_one, hc]
    ring
  rw [e, idealPowerSpanBounds.mem_pow_iff]
  exact hu

theorem cntP_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (k + 1) M n = Ideal.absNorm 𝔭 ^ (2 * M - 1) * cntP hF 𝔭 k M n := by
  have hle : extP K 𝔭 ^ (k + 1) ≤ extP K 𝔭 ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have := finite_AQ (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta hθ (k + 1)
  have hIn : ∀ a : AQ K 𝔭 (k + 1), InQ 𝔭 k (Ideal.Quotient.factor hle a) ↔ InQ 𝔭 (k + 1) a := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk, inQ_mk 𝔭 (by omega)]
  have h := SecondPropositionFree.card_lift_pred (σ := sg hF 𝔭 (k + 1)) (τ := sg hF 𝔭 k)
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [sg_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, sg_mk])
    (sg_sg hF 𝔭 (k + 1))
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by
      rw [sg_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact he)
    (n := Ideal.Quotient.mk _ n) (by rw [sg_mk, hn]) (Ideal.absNorm 𝔭)
    (by rw [card_AQ hK hF, card_AQ hK hF]; ring) M hM
    (fun x => ¬ ∀ i, InQ 𝔭 k (x i))
    (by
      intro y hy w hw
      push Not at hy
      obtain ⟨i₀, hi₀⟩ := hy
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i₀)
      rw [← ha, Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk] at hi₀
      obtain ⟨b, hb⟩ := exists_tr_one hK hF h𝔭 hi₀ (k + 1)
      refine SecondPropositionFree.mem_range_linPart _ y i₀ (b := Ideal.Quotient.mk _ b) ?_ hw
      rw [← ha, sg_mk, sg_mk, ← map_mul, ← map_mul, ← map_add, ← map_one (Ideal.Quotient.mk _),
        Ideal.Quotient.eq]
      exact hb)
  rw [Ideal.Quotient.factor_mk] at h
  unfold cntP
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [hIn])

theorem cntP_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (j : ℕ) {M : ℕ} (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (j + 1) M n = Ideal.absNorm 𝔭 ^ ((2 * M - 1) * j) * cntP hF 𝔭 1 M n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [cntP_succ hK hF h𝔭 (by omega) hM hn, ih, ← mul_assoc, ← pow_add]
    congr 2
    ring

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

open NormLifting

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def mulW (𝔭 : Ideal (𝓞 F)) {w : 𝓞 K} (hw : w ∈ extP K 𝔭) (j : ℕ) : AQ K 𝔭 (j + 1) →+ AQ K 𝔭 (j + 2) :=
  (Submodule.mapQ (extP K 𝔭 ^ (j + 1)) (extP K 𝔭 ^ (j + 2)) (LinearMap.mulLeft (𝓞 K) w) (by
    intro z hz
    show w * z ∈ extP K 𝔭 ^ (j + 2)
    rw [pow_succ' _ (j + 1)]
    exact Ideal.mul_mem_mul hw hz)).toAddMonoidHom

theorem mulW_mk (𝔭 : Ideal (𝓞 F)) {w : 𝓞 K} (hw : w ∈ extP K 𝔭) (j : ℕ) (z : 𝓞 K) :
    mulW 𝔭 hw j (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (w * z) := rfl

theorem map_mem {𝔭 : Ideal (𝓞 F)} {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) : ι ϖ ∈ extP K 𝔭 :=
  Ideal.mem_map_of_mem _ h1

theorem mulW_injective {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) : Function.Injective (mulW (K := K) 𝔭 (map_mem h1) j) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mulW_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 1) (j := j + 1) h2 (by rwa [show 1 + (j + 1) = j + 2 by ring])

theorem inQ_iff_range {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2)
    (j : ℕ) (a : AQ K 𝔭 (j + 2)) : InQ 𝔭 (j + 2) a ↔ ∃ b, mulW (K := K) 𝔭 (map_mem h1) j b = a := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h3 := idealPowerSpanBounds.map_pow_le_span_sup (K := K) h𝔭 (c := 1) h2 (j + 2) (by rwa [pow_one])
    obtain ⟨u, hu, e, he, hue⟩ := Submodule.mem_sup.1 h3
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [mulW_mk, Ideal.Quotient.eq, ← hue]
    have : ι ϖ * r - (r * ι ϖ + e) = -e := by ring
    rw [this]
    exact neg_mem he
  · rintro ⟨b, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, Ideal.mul_mem_right _ _ (map_mem h1), (mulW_mk 𝔭 _ j z).symm⟩

theorem norm_iff (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭)
    (h2 : ϖ ∉ 𝔭 ^ 2) (j : ℕ) {M : ℕ} {n n' : 𝓞 K} (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2))
    (y : Fin M → AQ K 𝔭 (j + 1)) :
    ∑ i, sg hF 𝔭 (j + 2) (mulW 𝔭 (map_mem h1) j (y i)) * mulW 𝔭 (map_mem h1) j (y i) =
        Ideal.Quotient.mk _ n ↔
      ∑ i, sg hF 𝔭 j (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)) *
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i) =
        Ideal.Quotient.mk _ n' := by
  choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
  obtain rfl : (fun i => Ideal.Quotient.mk _ (z i)) = y := funext hz
  simp only [mulW_mk, Ideal.Quotient.factor_mk, sg_mk, ← map_mul, ← map_sum]
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]
  have e1 : ∑ i, conjO K (ι ϖ * z i) * (ι ϖ * z i) = ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, idealPowerSpanBounds.conjO_map hF]
    ring
  rw [e1]
  have h3 : ϖ * ϖ ∉ 𝔭 ^ (1 + 1 + 1) := idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) h2 h2
  constructor
  · intro h
    have h4 := add_mem h hn
    have e2 : ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i - n + (n - ι ϖ ^ 2 * n') =
        ι (ϖ * ϖ) * (∑ i, conjO K (z i) * z i - n') := by rw [map_mul]; ring
    rw [e2] at h4
    exact idealPowerSpanBounds.mem_of_mul_mem h𝔭 (v := 2) (j := j) h3 (by rwa [show 2 + j = j + 2 by ring])
  · intro h
    have h4 : ι ϖ ^ 2 * (∑ i, conjO K (z i) * z i - n') ∈ extP K 𝔭 ^ (j + 2) := by
      rw [show j + 2 = 2 + j by ring, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (map_mem h1) 2) h
    have h5 := sub_mem h4 hn
    have e2 : ι ϖ ^ 2 * (∑ i, conjO K (z i) * z i - n') - (n - ι ϖ ^ 2 * n') =
        ι ϖ ^ 2 * ∑ i, conjO K (z i) * z i - n := by ring
    rwa [e2] at h5

theorem card_red (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (j M : ℕ) (T : (Fin M → AQ K 𝔭 j) → Prop) :
    Nat.card {y : Fin M → AQ K 𝔭 (j + 1) //
        T fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ j)) (y i)} =
      Ideal.absNorm 𝔭 ^ (2 * M) * Nat.card {y // T y} := by
  have := finite_AQ (K := K) h𝔭 (j + 1)
  have := finite_AQ (K := K) h𝔭 j
  have hle : extP K 𝔭 ^ (j + 1) ≤ extP K 𝔭 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j)
  let f : (Fin M → AQ K 𝔭 (j + 1)) →+ (Fin M → AQ K 𝔭 j) :=
    AddMonoidHom.compLeft (Ideal.Quotient.factor hle).toAddMonoidHom (Fin M)
  have hf : Function.Surjective f := by
    intro b
    choose a ha using fun i => Ideal.Quotient.factor_surjective hle (b i)
    exact ⟨a, funext ha⟩
  have hq : 0 < Ideal.absNorm 𝔭 :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (idealPowerSpanBounds.ne_bot h𝔭))
  have hker : Nat.card f.ker = Ideal.absNorm 𝔭 ^ (2 * M) := by
    have h0 := HermitianSublattices.card_preimage f hf (fun _ => True)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_fun, Nat.card_fun,
      Nat.card_fin, card_AQ hK hF, card_AQ hK hF] at h0
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (pow_pos hq (2 * j)) M)
    rw [← h0, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [← hker]
  exact HermitianSublattices.card_preimage f hf T

theorem cntI_add_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2) (j M : ℕ) {n n' : 𝓞 K}
    (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2)) :
    cntI hF 𝔭 (j + 2) M n = Ideal.absNorm 𝔭 ^ (2 * M) * cnt hF 𝔭 j M n' := by
  unfold cntI cnt
  rw [← card_red hK hF h𝔭 j M
    (fun y => ∑ i, sg hF 𝔭 j (y i) * y i = Ideal.Quotient.mk _ n')]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨fun i => mulW 𝔭 (map_mem h1) j (y.1 i),
    fun i => (inQ_iff_range h𝔭 h1 h2 j _).2 ⟨_, rfl⟩,
    (norm_iff hF h𝔭 h1 h2 j hn y.1).2 y.2⟩) ⟨?_, ?_⟩)
  · intro y y' h
    apply Subtype.ext
    funext i
    exact mulW_injective h𝔭 h1 h2 j (congrFun (congrArg Subtype.val h) i)
  · rintro ⟨x, hx1, hx2⟩
    choose y hy using fun i => (inQ_iff_range h𝔭 h1 h2 j _).1 (hx1 i)
    obtain rfl : (fun i => mulW 𝔭 (map_mem h1) j (y i)) = x := funext hy
    exact ⟨⟨y, (norm_iff hF h𝔭 h1 h2 j hn y).1 hx2⟩, rfl⟩

theorem cntI_eq_zero (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j M : ℕ) {n : 𝓞 K}
    (hn : n ∉ extP K 𝔭 ^ 2) : cntI hF 𝔭 (j + 2) M n = 0 := by
  unfold cntI
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx1, hx2⟩
  choose z hz hzx using hx1
  obtain rfl : (fun i => Ideal.Quotient.mk _ (z i)) = x := funext hzx
  simp only [sg_mk, ← map_mul, ← map_sum] at hx2
  rw [Ideal.Quotient.eq] at hx2
  have h1 : ∑ i, conjO K (z i) * z i - n ∈ extP K 𝔭 ^ 2 := Ideal.pow_le_pow_right (by omega) hx2
  have h2 : ∑ i, conjO K (z i) * z i ∈ extP K 𝔭 ^ 2 := by
    refine sum_mem fun i _ => ?_
    rw [sq]
    refine Ideal.mul_mem_mul ?_ (hz i)
    have := idealPowerSpanBounds.conjO_mem_pow hF 𝔭 1 (z i) (by rw [pow_one]; exact hz i)
    rwa [pow_one] at this
  apply hn
  have := sub_mem h2 h1
  rwa [sub_sub_cancel] at this

theorem eq_zero_of_inQ_one {𝔭 : Ideal (𝓞 F)} {a : AQ K 𝔭 1} (ha : InQ 𝔭 1 a) : a = 0 := by
  obtain ⟨z, hz, rfl⟩ := ha
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hz

theorem cntI_one_of_mem (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (M : ℕ) {n : 𝓞 K}
    (hn : n ∈ extP K 𝔭) : cntI hF 𝔭 1 M n = 1 := by
  unfold cntI
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨⟨0, fun i => ⟨0, zero_mem _, map_zero _⟩, ?_⟩⟩⟩
  · apply Subtype.ext
    funext i
    rw [eq_zero_of_inQ_one (x.2.1 i), eq_zero_of_inQ_one (y.2.1 i)]
  · symm
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hn


end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

private lemma coe_conjO_eq_star (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

private lemma conjO_conjO_unimodular_class_representatives (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star, coe_conjO_eq_star, star_star]

private lemma mem_conjIdeal_iff' (P : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ conjO K r ∈ P := by
  have hS : {r : 𝓞 K | ∃ s ∈ P, algebraMap (𝓞 K) K r = star (algebraMap (𝓞 K) K s)} =
      ((P.comap (conjO K) : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    ext r
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_comap]
    constructor
    · rintro ⟨s, hs, h⟩
      have : conjO K r = s := by
        apply RingOfIntegers.ext
        rw [coe_conjO_eq_star]
        change star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K s
        rw [h, star_star]
      rwa [this]
    · intro h
      refine ⟨conjO K r, h, ?_⟩
      change (r : K) = star ((conjO K r : 𝓞 K) : K)
      rw [coe_conjO_eq_star, star_star]
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  rw [hS, Ideal.span_eq, Ideal.mem_comap]

private lemma conjO_algebraMap_of_fixed_field (hF : IsFixF K F) (x : 𝓞 F) :
    conjO K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star]
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (algebraMap (𝓞 F) F x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x)) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x)
  rw [h1]
  exact (hF _).mpr ⟨_, rfl⟩

private lemma exists_algebraMap_eq_of_conjO_eq (hF : IsFixF K F) (y : 𝓞 K) (hy : conjO K y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) a = y := by
  have h1 : star (y : K) = y := by rw [← coe_conjO_eq_star, hy]
  obtain ⟨f, hf⟩ := (hF _).mp h1
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (algebraMap F K).injective, hf]
    exact RingOfIntegers.isIntegral_coe y
  let a : 𝓞 F := ⟨f, (mem_integralClosure_iff ℤ F).mpr hint⟩
  refine ⟨a, RingOfIntegers.ext ?_⟩
  have h2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (algebraMap (𝓞 F) F a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = (y : K)
  rw [h2, ← hf]
  rfl

private lemma extP_comap_eq_inf_conjIdeal_of_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P ⊓ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply le_antisymm
  · unfold extP
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_comap, Ideal.mem_inf, mem_conjIdeal_iff', conjO_algebraMap_of_fixed_field hF]
    exact ⟨hx, hx⟩
  · intro x hx
    rw [Ideal.mem_inf, mem_conjIdeal_iff'] at hx
    obtain ⟨hxP, hxc⟩ := hx
    have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
    have htc : t = conjO K θ := RingOfIntegers.ext (by rw [coe_conjO_eq_star]; exact ht)
    subst htc
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_conjO_eq hF (x + conjO K x) (by rw [map_add, conjO_conjO_unimodular_class_representatives, add_comm])
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_conjO_eq hF (conjO K θ * x + θ * conjO K x)
      (by rw [map_add, map_mul, map_mul, conjO_conjO_unimodular_class_representatives, conjO_conjO_unimodular_class_representatives, add_comm])
    obtain ⟨g, hg⟩ := exists_algebraMap_eq_of_conjO_eq hF ((θ - conjO K θ) * (θ - conjO K θ))
      (by rw [map_mul, map_sub, conjO_conjO_unimodular_class_representatives]; ring)
    have ha𝔭 : a ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, ha]; exact P.add_mem hxP hxc
    have hb𝔭 : b ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, hb]; exact P.add_mem (P.mul_mem_left _ hxP) (P.mul_mem_left _ hxc)
    have hg𝔭 : g ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, hg]
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h <;> exact hθ h
    obtain ⟨e, i, hi, hei⟩ := h𝔭.exists_inv hg𝔭
    have hEI : algebraMap (𝓞 F) (𝓞 K) e * ((θ - conjO K θ) * (θ - conjO K θ)) +
        algebraMap (𝓞 F) (𝓞 K) i = 1 := by
      rw [← hg, ← map_mul, ← map_add, hei, map_one]
    have hx_eq : x = algebraMap (𝓞 F) (𝓞 K) e * (θ - conjO K θ) * θ * algebraMap (𝓞 F) (𝓞 K) a -
        algebraMap (𝓞 F) (𝓞 K) e * (θ - conjO K θ) * algebraMap (𝓞 F) (𝓞 K) b +
        algebraMap (𝓞 F) (𝓞 K) i * x := by
      rw [ha, hb]
      linear_combination (-x) * hEI
    have hmem : ∀ z ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)), algebraMap (𝓞 F) (𝓞 K) z ∈
        extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) := fun z hz => Ideal.mem_map_of_mem _ hz
    rw [hx_eq]
    exact Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hmem _ ha𝔭))
      (Ideal.mul_mem_left _ _ (hmem _ hb𝔭))) (Ideal.mul_mem_right _ _ (hmem _ hi))

theorem map_comap_eq_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  rw [extP_comap_eq_inf_conjIdeal_of_isMaximal hK hF hP, hc, inf_idem]

theorem extP_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hle : ¬ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P := by
    intro h
    apply hc
    apply le_antisymm h
    intro r hr
    rw [mem_conjIdeal_iff']
    apply h
    rw [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
    exact hr
  have htop : P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = ⊤ := by
    by_contra h
    exact hle (le_sup_right.trans (hP.eq_of_le h le_sup_left).ge)
  rw [extP_comap_eq_inf_conjIdeal_of_isMaximal hK hF hP, Ideal.mul_eq_inf_of_coprime htop]

theorem etaF_eq (𝔭 : Ideal (𝓞 F)) : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
  unfold etaF
  split_ifs <;> simp

theorem one_lt_q {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
  have h0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  have h1 : Ideal.absNorm 𝔭 ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have : 1 < Ideal.absNorm 𝔭 := by omega
  exact_mod_cast this

theorem beta_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    0 < 1 - etaF K F 𝔭 ^ M * (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) := by
  have hq := one_lt_q h𝔭
  have hlt : (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ)) := zpow_pos (by linarith) _
  rcases etaF_eq (K := K) 𝔭 with h | h <;> rw [h]
  · rw [one_pow, one_mul]; linarith
  · rcases neg_one_pow_eq_or ℝ M with h' | h' <;> rw [h'] <;> linarith

theorem cnt_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    (cnt hF 𝔭 k M (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * M - 1) * k) *
      (1 - etaF K F 𝔭 ^ M * (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ))) := by
  classical
  have hinj : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h2 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx, map_zero]
    rw [map_eq_zero_iff _ (algebraMap F K).injective] at h2
    have : x = 0 := RingOfIntegers.ext (h2.trans (map_zero (algebraMap (𝓞 F) F)).symm)
    rw [this]
    exact 𝔭.zero_mem
  haveI := h𝔭
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hinj
  subst hPc
  have hq := one_lt_q h𝔭
  have hnP : ι n ∉ P := by rwa [Ideal.mem_comap] at hn
  have hfix : conjO K (ι n) = ι n := conjO_algebraMap_of_fixed_field hF n
  rw [cnt_eq_normRepCount]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hin := map_comap_eq_of_inert hK hF hP hc
    rw [hin, normRepCount_eq_eulerFac_inert hK hP hc M k hM hk _ hfix hnP]
    have hN := absNorm_comap_inert hK hF hP hc
    have hpr : ((P.comap ι).map ι).IsPrime := by
      have h3 := hin
      unfold extP at h3
      rw [h3]
      exact hP.isPrime
    have heta : etaF K F (P.comap ι) = -1 := by
      unfold etaF
      rw [if_pos hpr]
    unfold Formalism.HermitianLatticesTheory.eulerFac
    rw [if_pos hc, inv_inv, heta, ← hN]
    push_cast
    rw [Real.sqrt_sq (by positivity)]
  · have hsplit := extP_split hK hF hP hc
    rw [hsplit, normRepCount_eq_eulerFac_split hK hP hc M k hM hk _ hfix hnP]
    have hN := absNorm_comap_split hK hF hP hc
    have hcc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
      ext r
      rw [mem_conjIdeal_iff', mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
    have hc2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠
        Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      rw [hcc]
      exact Ne.symm hc
    have hNc := absNorm_conjIdeal hK P
    have hpr : ¬ ((P.comap ι).map ι).IsPrime := by
      intro hpr
      have h3 := hsplit
      unfold extP at h3
      rw [h3] at hpr
      rcases (hpr.mul_le).mp le_rfl with h | h
      · have h1 : P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := h.trans Ideal.mul_le_right
        apply hc
        refine le_antisymm ?_ h1
        intro r hr
        rw [mem_conjIdeal_iff'] at hr
        have h4 := h1 hr
        rwa [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives] at h4
      · have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P := h.trans Ideal.mul_le_left
        apply hc
        refine le_antisymm h1 ?_
        intro r hr
        rw [mem_conjIdeal_iff']
        apply h1
        rw [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
        exact hr
    have heta : etaF K F (P.comap ι) = 1 := by
      unfold etaF
      rw [if_neg hpr]
    have hx : 0 < 1 - (Ideal.absNorm (P.comap ι) : ℝ) ^ (-(M : ℤ)) := by
      have hlt : (Ideal.absNorm (P.comap ι) : ℝ) ^ (-(M : ℤ)) < 1 := by
        rw [zpow_neg, zpow_natCast]
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
      linarith
    have hh : (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 := by norm_num
    unfold Formalism.HermitianLatticesTheory.eulerFac
    rw [if_neg hc, if_neg hc2, hNc, ← hN, heta, ← Real.rpow_add hx, hh, Real.rpow_neg_one, inv_inv,
      one_pow, one_mul]

theorem exists_norm (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {u : 𝓞 F} (hu : u ∉ 𝔭) :
    ∃ c : 𝓞 K, conjO K c * c - ι u ∈ extP K 𝔭 ^ k := by
  have hq := one_lt_q h𝔭
  have h1 := cnt_unit hK hF h𝔭 (M := 1) le_rfl hk hu
  have h2 := beta_pos (K := K) h𝔭 (M := 1) le_rfl
  have hpos : (0 : ℝ) < (cnt hF 𝔭 k 1 (ι u) : ℝ) := by
    rw [h1]
    exact mul_pos (pow_pos (by linarith) _) h2
  have hpos' : 0 < normRepCount K (extP K 𝔭 ^ k) 1 (ι u) := by
    rw [← cnt_eq_normRepCount hF]
    exact_mod_cast hpos
  unfold normRepCount at hpos'
  obtain ⟨⟨x, y, hy, hsum⟩⟩ := (Nat.card_pos_iff.mp hpos').1
  refine ⟨y 0, ?_⟩
  rw [Fin.sum_univ_one] at hsum
  exact Ideal.Quotient.eq.mp hsum

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_frame (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (z : Fin (finrank K V) → ↥L) (g : Fin (finrank K V) → 𝓞 K),
      (∀ i j, i ≠ j → h (z i : V) (z j : V) = 0) ∧
      (∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) ∧ ∀ i, g i - 1 ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hPp := hP.isPrime
  have hda := LocF.aniso_of_totPosDef hd
  have hu := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  obtain ⟨x, hxM, hxo, hxu⟩ := LocF.exists_orth_unit_frame (WA.isHermSemilocal_locRing hK hP)
    (LocF.locRing_local hPp) hs hda (WA.isSelfDualMod_loc hL hPp hu)
  choose s hs' hsx using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
    (show x i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hxM i)
  choose u hu' using fun i => MeanB.exists_val hF hs hLi ⟨s i • x i, hsx i⟩
  have hunit : ∀ i, u i ∉ P.comap ι := by
    intro i
    have h1 : WA.IsUnitIn (WA.locRing P) (algebraMap (𝓞 K) K (ι (u i))) := by
      rw [MeanB.algebraMap_comp, ← hu' i]
      show WA.IsUnitIn (WA.locRing P) (h (s i • x i) (s i • x i))
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
      refine LocF.isUnitIn_mul ?_ (LocF.isUnitIn_mul ?_ (hxu i))
      · rw [← WA.algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact WA.conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    exact ((WA.mem_hcompl_iff hPp _).mp ((LocF.isUnitIn_algebraMap_iff hPp _).mp h1)).1
  choose u' hu'' using fun i => MeanA.exists_mul_sub_one_mem_pow h𝔭 (hunit i) k
  have hunit' : ∀ i, u' i ∉ P.comap ι := by
    intro i hmem
    have h1 : u' i * u i - 1 ∈ P.comap ι := Ideal.pow_le_self (by omega) (hu'' i)
    have h2 := sub_mem (Ideal.mul_mem_right (u i) _ hmem) h1
    rw [sub_sub_cancel] at h2
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  choose c hc using fun i => exists_norm hK hF h𝔭 hk (hunit' i)
  refine ⟨fun i => ⟨c i • s i • x i, L.smul_mem _ (hsx i)⟩, fun i => conjO K (c i) * c i * ι (u i),
    ?_, ?_, ?_⟩
  · intro i j hij
    show h (c i • s i • x i) (c j • s j • x j) = 0
    simp only [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hxo i j hij, mul_zero]
  · intro i
    show h (c i • s i • x i) (c i • s i • x i) = _
    have := hu' i
    simp only at this
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, this, map_mul, map_mul,
      WA.algebraMap_conjO, MeanB.algebraMap_comp]
    ring
  · intro i
    have e : conjO K (c i) * c i * ι (u i) - 1 =
        (conjO K (c i) * c i - ι (u' i)) * ι (u i) + ι (u' i * u i - 1) := by
      rw [map_sub, map_mul, map_one]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ (hc i)) ((idealPowerSpanBounds.mem_pow_iff _ _ _).2 (hu'' i))

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem exists_mem_ideal_form_eq_of_mem_ideal_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (I : Ideal (𝓞 K)) (w x : ↥L)
    (hx : x ∈ (I • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ I, h (w : V) (x : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (w : V) w.2 (m : V) m.2)
    refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by rw [Submodule.coe_add, map_add, hu', hv', map_add]⟩

private theorem exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (w x : ↥L)
    (hx : x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ extP K 𝔭 ^ k, h (x : V) (w : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (m : V) m.2 (w : V) w.2)
    refine ⟨conjO K r * o, Ideal.mul_mem_right _ _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k r hr), ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ho]
    congr 1 <;> simp [conjO]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by
      rw [Submodule.coe_add, map_add, LinearMap.add_apply, hu', hv', map_add]⟩


section Frame

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)

def lin (a : Fin m → 𝓞 K) : ↥L := ∑ i, a i • z i

theorem lin_sub (a b : Fin m → 𝓞 K) : lin z a - lin z b = lin z (a - b) := by
  simp only [lin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_smul]

theorem coe_lin (a : Fin m → 𝓞 K) : ((lin z a : ↥L) : V) = ∑ i, a i • (z i : V) := by
  simp [lin]

variable {z g}

theorem form_right (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (j : Fin m) (c : Fin m → 𝓞 K) :
    h (z j : V) (lin z c : V) = algebraMap (𝓞 K) K (c j * g j) := by
  rw [coe_lin, map_sum, Finset.sum_eq_single j]
  · rw [← algebraMap_smul K (c j) (z j : V), map_smul, hzg, smul_eq_mul, map_mul]
  · intro i _ hij
    rw [← algebraMap_smul K (c i) (z i : V), map_smul, hzo j i (Ne.symm hij), smul_zero]
  · simp

theorem form_lin (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (c : Fin m → 𝓞 K) :
    h (lin z c : V) (lin z c : V) = algebraMap (𝓞 K) K (∑ i, conjO K (c i) * c i * g i) := by
  nth_rewrite 1 [coe_lin]
  rw [map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul K (c i) (z i : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    form_right hzo hzg, smul_eq_mul, map_mul, map_mul, map_mul, ← mul_assoc]
  congr 2 <;> simp [conjO]

theorem mk_lin_eq_iff (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i))
    (hg1 : ∀ i, g i - 1 ∈ extP K 𝔭 ^ k) (a b : Fin m → 𝓞 K) :
    (Submodule.Quotient.mk (lin z a) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk (lin z b) ↔ ∀ i, a i - b i ∈ extP K 𝔭 ^ k := by
  rw [Submodule.Quotient.eq, lin_sub]
  constructor
  · intro hmem i
    have key : ∀ x : ↥L, x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) →
        ∃ y ∈ extP K 𝔭 ^ k, h (z i : V) (x : V) = algebraMap (𝓞 K) K y := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
      · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (z i : V) (z i).2 (m : V) m.2)
        refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
        rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
      · obtain ⟨u, hu, hu'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨u + w, Ideal.add_mem _ hu hw, by rw [Submodule.coe_add, map_add, hu', hw', map_add]⟩
    obtain ⟨y, hy, hyeq⟩ := key _ hmem
    rw [form_right hzo hzg] at hyeq
    have h1 : (a - b) i * g i ∈ extP K 𝔭 ^ k := by
      rw [IsFractionRing.injective (𝓞 K) K hyeq]
      exact hy
    have h2 : (a - b) i * (g i - 1) ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ _ (hg1 i)
    have h3 : a i - b i = (a - b) i * g i - (a - b) i * (g i - 1) := by
      simp only [Pi.sub_apply]
      ring
    rw [h3]
    exact Ideal.sub_mem _ h1 h2
  · intro hab
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hab i) Submodule.mem_top

end Frame

private theorem quotient_norm_congr_of_quotient_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (y y₀ : ↥L)
    (hy : (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk y₀)
    (o o₀ : 𝓞 K) (ho : h (y : V) (y : V) = algebraMap (𝓞 K) K o)
    (ho₀ : h (y₀ : V) (y₀ : V) = algebraMap (𝓞 K) K o₀) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ := by
  rw [Submodule.Quotient.eq] at hy
  obtain ⟨u1, hu1, he1⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy
  obtain ⟨u2, hu2, he2⟩ := exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy
  obtain ⟨u3, hu3, he3⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy
  have hyx : y = y₀ + (y - y₀) := by abel
  have hsum : o = o₀ + u1 + u2 + u3 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [← ho, hyx]
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
    rw [he1, he2, he3, ← ho₀]
    ring
  rw [Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]
  exact Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3

theorem nkCount_eq_cnt (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) (n : 𝓞 F) :
    nkCount h L 𝔭 k n = cnt hF 𝔭 k (finrank K V) (ι n) := by
  obtain ⟨z, g, hzo, hzg, hg1⟩ := exists_frame hK hF hs hd hL hLi h𝔭 hv hk
  have hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o := fun y =>
    let ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)
    ⟨o, ho.symm⟩
  have hn : algebraMap F K (n : F) = algebraMap (𝓞 K) K (ι n) := rfl
  let lift : (Fin (finrank K V) → AQ K 𝔭 k) → Fin (finrank K V) → 𝓞 K :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose
  have hlift : ∀ x i, Ideal.Quotient.mk (extP K 𝔭 ^ k) (lift x i) = x i :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose_spec
  let Φ : (Fin (finrank K V) → AQ K 𝔭 k) → ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    fun x => Submodule.Quotient.mk (lin z (lift x))
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have hd := (mk_lin_eq_iff hLi 𝔭 k hzo hzg hg1 (lift x) (lift x')).mp hxx
    funext i
    rw [← hlift x i, ← hlift x' i, Ideal.Quotient.eq]
    exact hd i
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  haveI : Finite (Fin (finrank K V) → AQ K 𝔭 k) := vectorCountBounds.finite_vec h𝔭 k
  have hcard : Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Nat.card (Fin (finrank K V) → AQ K 𝔭 k) := by
    rw [MeanB.card_quot_extP hK hF hL h𝔭 k, vectorCountBounds.card_vec hK h𝔭 k, Fintype.card_fin]
    ring_nf
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  have hsum : ∀ x, Ideal.Quotient.mk (extP K 𝔭 ^ k) (∑ i, conjO K (lift x i) * lift x i * g i) =
      ∑ i, sg hF 𝔭 k (x i) * x i := by
    intro x
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : Ideal.Quotient.mk (extP K 𝔭 ^ k) (g i) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
      exact hg1 i
    rw [map_mul, map_mul, hg, mul_one]
    conv_rhs => rw [← hlift x i]
    unfold sg
    rw [NormLifting.conjQ_mk]
  unfold nkCount cnt
  refine (Nat.card_congr ((Equiv.ofBijective Φ hbij).subtypeEquiv (fun x => ?_))).symm
  show _ ↔ ∃ y : ↥L, Submodule.Quotient.mk y = Φ x ∧ _
  constructor
  · intro hx
    refine ⟨lin z (lift x), rfl, ?_⟩
    rw [form_lin hzo hzg, hn, integralBasisSpans.congrP_int h𝔭, hsum x, hx]
  · rintro ⟨y, hy, hc⟩
    obtain ⟨o, ho⟩ := hint y
    have hcg := quotient_norm_congr_of_quotient_eq hF hLi 𝔭 k y (lin z (lift x)) hy o _ ho (form_lin hzo hzg (lift x))
    rw [ho, hn, integralBasisSpans.congrP_int h𝔭, hcg, hsum x] at hc
    exact hc

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem mem_pow_iff_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hbdd : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hn
    have hI := Ideal.iInf_pow_eq_bot_of_isDomain (I := 𝔭) h𝔭.ne_top
    rw [← Ideal.mem_bot, ← hI, Ideal.mem_iInf]
    intro i
    obtain ⟨e', he', hie'⟩ := hnb i
    exact Ideal.pow_le_pow_right hie'.le he'
  have hne : {e : ℕ | n ∈ 𝔭 ^ e}.Nonempty := ⟨0, by simp⟩
  unfold vF
  constructor
  · intro he
    exact le_csSup hbdd he
  · intro he
    have hmem : sSup {e : ℕ | n ∈ 𝔭 ^ e} ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem hne hbdd
    exact Ideal.pow_le_pow_right he hmem

theorem cnt_congr (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) {n n' : 𝓞 K}
    (h : n - n' ∈ extP K 𝔭 ^ k) : cnt hF 𝔭 k M n = cnt hF 𝔭 k M n' := by
  unfold cnt
  rw [Ideal.Quotient.eq.mpr h]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem cnt_one_of_mem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∈ 𝔭) :
    (cnt hF 𝔭 1 (finrank K V) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V - 1) *
        (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))) := by
  classical
  have h0 := sum_nkCount hK hF hs hd hL hLi h𝔭 1
  have := MeanC.finite_quot_pow h𝔭 1
  have := Fintype.ofFinite (𝓞 F ⧸ 𝔭 ^ 1)
  rw [finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun n' _ => nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv le_rfl _,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : 𝓞 F ⧸ 𝔭 ^ 1))] at h0
  have h1 : (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out (0 : 𝓞 F ⧸ 𝔭 ^ 1))) : ℝ) +
      ∑ n' ∈ Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1),
        (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out n')) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V * 1) := by exact_mod_cast h0
  have h2 : cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out (0 : 𝓞 F ⧸ 𝔭 ^ 1))) =
      cnt hF 𝔭 1 (finrank K V) (ι n) := by
    apply cnt_congr
    rw [← map_sub, idealPowerSpanBounds.mem_pow_iff]
    refine sub_mem ?_ (by rwa [pow_one])
    rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
  have h3 : ∀ n' ∈ Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1),
      (cnt hF 𝔭 1 (finrank K V) (ι (Quotient.out n')) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V - 1) *
        (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) := by
    intro n' hn'
    have hne : Quotient.out n' ∉ 𝔭 := by
      intro hmem
      apply Finset.ne_of_mem_erase hn'
      rw [← Ideal.Quotient.mk_out n', Ideal.Quotient.eq_zero_iff_mem]
      exact (pow_one 𝔭).ge hmem
    rw [cnt_unit hK hF h𝔭 hm le_rfl hne, mul_one]
  have hcard : ((Finset.univ.erase (0 : 𝓞 F ⧸ 𝔭 ^ 1)).card : ℝ) = (Ideal.absNorm 𝔭 : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
      MeanC.card_quot_pow, pow_one, Nat.cast_sub (MeanC.one_lt_absNorm h𝔭).le, Nat.cast_one]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hcard, mul_one] at h1
  linarith

theorem real_step (q T ε β c1 cI : ℝ) (j t : ℕ) (hq : 0 < q) (hT : T = q ^ t) (hε : ε ^ 2 = 1)
    (hβ : β = 1 - ε * (q ^ (t + 1))⁻¹)
    (hc1 : c1 = q ^ (2 * (t + 1)) - (q - 1) * (q ^ (2 * (t + 1) - 1) * β)) :
    (q ^ ((2 * (t + 1) - 1) * (j + 1)) * (c1 - 1) + cI) / q ^ ((j + 2) * (2 * (t + 1) - 1)) =
      β * (1 + ε * T⁻¹) + cI / q ^ ((j + 2) * (2 * (t + 1) - 1)) := by
  subst hT hβ hc1
  have e : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hq' : q ≠ 0 := hq.ne'
  have h1 : (j + 2) * (2 * t + 1) = (2 * t + 1) * (j + 1) + (2 * t + 1) := by ring
  rw [e, h1, pow_add q ((2 * t + 1) * (j + 1)) (2 * t + 1), add_div,
    mul_div_mul_left _ _ (pow_ne_zero _ hq')]
  congr 1
  have hε2 : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
  rcases hε2 with rfl | rfl
  · field_simp
    ring
  · field_simp
    ring

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem eta_pow_sq (𝔭 : Ideal (𝓞 F)) (M : ℕ) : (etaF K F 𝔭 ^ M) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  rcases etaF_eq (K := K) 𝔭 with h | h <;> simp [h]

theorem alphaN_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n =
      1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by have := one_lt_q h𝔭; linarith
  rw [alphaN]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv hk n, cnt_unit hK hF h𝔭 hm hk hn,
    show k * (2 * finrank K V - 1) = (2 * finrank K V - 1) * k from mul_comm _ _,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

private theorem exists_uniformizer_sq_mul_congr_of_two_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0)
    (h2 : 2 ≤ vF 𝔭 n) {N : ℕ} (hN : vF 𝔭 n + 1 ≤ N) :
    ∃ ϖ ∈ 𝔭, ϖ ∉ 𝔭 ^ 2 ∧ ∃ n' : 𝓞 F, n' ≠ 0 ∧ vF 𝔭 n' + 2 = vF 𝔭 n ∧ n - ϖ ^ 2 * n' ∈ 𝔭 ^ N := by
  have h0 : 𝔭 ≠ ⊥ := idealPowerSpanBounds.ne_bot h𝔭
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ ∈ 𝔭, ϖ ∉ 𝔭 ^ 2 := by
    by_contra hcon
    push Not at hcon
    have heq : 𝔭 ^ 2 = 𝔭 := le_antisymm (Ideal.pow_le_self two_ne_zero) (fun x hx => hcon x hx)
    have hmul : 𝔭 * 𝔭 = 𝔭 * 1 := by rw [mul_one, ← pow_two, heq]
    have h1 : 𝔭 = 1 := mul_left_cancel₀ h0 hmul
    exact h𝔭.ne_top (by rw [h1, Ideal.one_eq_top])
  have hg : ϖ ^ 2 ∉ 𝔭 ^ (2 + 1) := by
    have := idealPowerSpanBounds.mul_notMem h𝔭.isPrime h0 (i := 1) (j := 1) hϖ2 hϖ2
    rwa [← pow_two] at this
  have hmem : ∀ e, n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := mem_pow_iff_le_vF h𝔭 hn
  have hsup := idealPowerSpanBounds.pow_le_span_sup h𝔭.isPrime h0 hg N ((hmem 2).mpr h2)
  obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.mp hsup
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hdiff : n - ϖ ^ 2 * r = e := by rw [← hae]; ring
  have heN : ∀ t, t ≤ N → e ∈ 𝔭 ^ t := fun t ht => Ideal.pow_le_pow_right ht he
  refine ⟨ϖ, hϖ1, hϖ2, r, ?_, ?_, by rw [hdiff]; exact he⟩
  · rintro rfl
    have : n ∈ 𝔭 ^ N := by rw [← hae]; simpa using he
    have := (hmem N).mp this
    omega
  · have hr0 : r ≠ 0 := by
      rintro rfl
      have : n ∈ 𝔭 ^ N := by rw [← hae]; simpa using he
      have := (hmem N).mp this
      omega
    have hmemr : ∀ t, r ∈ 𝔭 ^ t ↔ t ≤ vF 𝔭 r := mem_pow_iff_le_vF h𝔭 hr0
    have hup : ¬ (vF 𝔭 n - 1 ≤ vF 𝔭 r) := by
      intro hle
      have hr := (hmemr (vF 𝔭 n - 1)).mpr hle
      have h3 : ϖ ^ 2 * r ∈ 𝔭 ^ (vF 𝔭 n + 1) := by
        have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖ1 2) hr
        rwa [← pow_add, show 2 + (vF 𝔭 n - 1) = vF 𝔭 n + 1 by omega] at this
      have h4 : n ∈ 𝔭 ^ (vF 𝔭 n + 1) := by
        have h3' : r * ϖ ^ 2 ∈ 𝔭 ^ (vF 𝔭 n + 1) := by rw [mul_comm]; exact h3
        have := Ideal.add_mem _ h3' (heN _ hN)
        rwa [hae] at this
      have := (hmem _).mp h4
      omega
    have hlow : vF 𝔭 n - 2 ≤ vF 𝔭 r := by
      rcases Nat.eq_zero_or_pos (vF 𝔭 n - 2) with h | h
      · omega
      · by_contra hlt
        have hr : r ∉ 𝔭 ^ ((vF 𝔭 n - 3) + 1) := by
          rw [hmemr]; omega
        have h5 := idealPowerSpanBounds.mul_notMem h𝔭.isPrime h0 hg hr
        have h6 : ϖ ^ 2 * r ∈ 𝔭 ^ vF 𝔭 n := by
          rw [show ϖ ^ 2 * r = n - e by rw [← hdiff]; ring]
          exact Ideal.sub_mem _ ((hmem _).mpr le_rfl) (heN _ (by omega))
        rw [show 2 + (vF 𝔭 n - 3) + 1 = vF 𝔭 n by omega] at h5
        exact h5 h6
    omega

private theorem pow_mul_div_pow_eq_inv_sq_mul (q c' : ℝ) (j m : ℕ) (hq : 0 < q) :
    (q ^ (2 * (m + 1)) * c') / q ^ ((j + 2) * (2 * (m + 1) - 1)) =
      ((q ^ m)⁻¹) ^ 2 * (c' / q ^ (j * (2 * (m + 1) - 1))) := by
  have hq0 : q ≠ 0 := hq.ne'
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
    show (j + 2) * (2 * m + 1) = j * (2 * m + 1) + (2 * m + 2) + 2 * m by ring,
    show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, pow_add]
  field_simp
  ring

private theorem sub_single_one_add_single_one_of_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {m : ℕ} {n : 𝓞 F} (hn : n ∈ 𝔭)
    (hc1 : (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1)) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1) - 1) * (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹))) (j : ℕ) :
    (cnt hF 𝔭 (j + 2) (m + 1) (ι n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ ((j + 2) * (2 * (m + 1) - 1)) =
      (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹) * (1 + etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) +
      (cntI hF 𝔭 (j + 2) (m + 1) (ι n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ ((j + 2) * (2 * (m + 1) - 1)) := by
  have hιn : ι n ∈ extP K 𝔭 := by
    have := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 n).mpr (by rwa [pow_one])
    rwa [pow_one] at this
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by have := one_lt_q h𝔭; linarith
  have hadd := cnt_eq_add hF h𝔭 (j + 2) (m + 1) (ι n)
  have hP := cntP_eq hK hF h𝔭 (j + 1) (Nat.le_add_left 1 m) (idealPowerSpanBounds.conjO_map hF n)
  have hadd1 := cnt_eq_add hF h𝔭 1 (m + 1) (ι n)
  have hI1 := cntI_one_of_mem hF 𝔭 (m + 1) hιn
  have hP1 : (cntP hF 𝔭 1 (m + 1) (ι n) : ℝ) = (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) - 1 := by
    rw [hadd1, hI1]; push_cast; ring
  rw [hadd, hP]
  push_cast
  rw [hP1]
  exact real_step _ _ _ _ _ _ j m hq rfl (eta_pow_sq (K := K) 𝔭 (m + 1)) rfl hc1

private theorem stab_lemma (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {m : ℕ}
    (hc1 : ∀ n : 𝓞 F, n ∈ 𝔭 → (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1)) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1) - 1) * (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹))) :
    ∀ v : ℕ, ∀ n : 𝓞 F, n ≠ 0 → vF 𝔭 n = v → ∀ k : ℕ, 2 * v + 1 ≤ k →
      (cnt hF 𝔭 k (m + 1) (ι n) : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * (m + 1) - 1)) =
        (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹) * ∑ l ∈ Finset.range (v + 1), (etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) ^ l := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by have := one_lt_q h𝔭; linarith
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro n hn0 hnv k hk
    have hmem : ∀ e, n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := mem_pow_iff_le_vF h𝔭 hn0
    rcases v with _ | _ | w
    · have hn𝔭 : n ∉ 𝔭 := by
        intro h
        have := (hmem 1).mp (by rwa [pow_one])
        omega
      rw [cnt_unit hK hF h𝔭 (Nat.le_add_left 1 m) (by omega) hn𝔭,
        show k * (2 * (m + 1) - 1) = (2 * (m + 1) - 1) * k from mul_comm _ _,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne'), zpow_neg, zpow_natCast]
      simp
    · have hn𝔭 : n ∈ 𝔭 := by rw [← pow_one 𝔭]; exact (hmem 1).mpr (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [sub_single_one_add_single_one_of_ne_zero hK hF h𝔭 hn𝔭 (hc1 n hn𝔭) j]
      have hn2 : ι n ∉ extP K 𝔭 ^ 2 := by
        rw [idealPowerSpanBounds.mem_pow_iff, hmem]; omega
      rw [cntI_eq_zero hF 𝔭 j (m + 1) hn2]
      simp [Finset.sum_range_succ]
    · have hn𝔭 : n ∈ 𝔭 := by rw [← pow_one 𝔭]; exact (hmem 1).mpr (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [sub_single_one_add_single_one_of_ne_zero hK hF h𝔭 hn𝔭 (hc1 n hn𝔭) j]
      obtain ⟨ϖ, h1, h2, n', hn'0, hn'v, hdiv⟩ := exists_uniformizer_sq_mul_congr_of_two_le_vF h𝔭 hn0 (by omega) (N := j + 2) (by omega)
      have hdivK : ι n - ι ϖ ^ 2 * ι n' ∈ extP K 𝔭 ^ (j + 2) := by
        rw [← map_pow, ← map_mul, ← map_sub, idealPowerSpanBounds.mem_pow_iff]
        exact hdiv
      rw [cntI_add_two hK hF h𝔭 h1 h2 j (m + 1) hdivK]
      have hih := ih w (by omega) n' hn'0 (by omega) j (by omega)
      push_cast
      rw [pow_mul_div_pow_eq_inv_sq_mul _ _ j m hq, hih]
      set x := (etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹) with hx
      have hx2 : x ^ 2 = ((Ideal.absNorm 𝔭 : ℝ) ^ m)⁻¹ ^ 2 := by
        rw [hx, mul_pow, eta_pow_sq (K := K) 𝔭 (m + 1), one_mul]
      have hgeo : ∑ l ∈ Finset.range (w + 1 + 1 + 1), x ^ l =
          1 + x + x ^ 2 * ∑ l ∈ Finset.range (w + 1), x ^ l := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum,
          Finset.sum_congr rfl (fun i _ => (show x ^ (i + 1 + 1) = x ^ 2 * x ^ i by ring))]
        simp only [pow_zero, zero_add, pow_one]
        ring
      rw [hgeo, ← hx2]
      ring



theorem alphaN_closed (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) :
    ∀ (v : ℕ) (n : 𝓞 F), n ≠ 0 → vF 𝔭 n = v → alphaN h L 𝔭 n =
      (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) *
        ∑ l ∈ Finset.range (v + 1),
          (etaF K F 𝔭 ^ finrank K V * ((Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V - 1))⁻¹) ^ l := by
  intro v n hn hnv
  obtain ⟨m, hm'⟩ : ∃ m, finrank K V = m + 1 := ⟨finrank K V - 1, by omega⟩
  have hc1 : ∀ n : 𝓞 F, n ∈ 𝔭 → (cnt hF 𝔭 1 (m + 1) (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1)) -
      ((Ideal.absNorm 𝔭 : ℝ) - 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (2 * (m + 1) - 1) * (1 - etaF K F 𝔭 ^ (m + 1) * ((Ideal.absNorm 𝔭 : ℝ) ^ (m + 1))⁻¹)) := by
    intro n' hn'
    have h := cnt_one_of_mem hK hF hs hd hL hLi h𝔭 hv hm hn'
    rw [hm'] at h
    rw [h, zpow_neg, zpow_natCast]
  rw [alphaN]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 * v + 1)] with k hk
  rw [nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv (by omega) n, hm',
    stab_lemma hK hF h𝔭 hc1 v n hn hnv k hk]
  simp only [zpow_neg, zpow_natCast, Nat.add_sub_cancel]

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace unitaryAbsoluteValueBounds

theorem abs_eta_pow (𝔭 : Ideal (𝓞 F)) (M : ℕ) : |etaF K F 𝔭 ^ M| = 1 := by
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h] <;> simp

theorem geom_bound {x : ℝ} (hx : |x| ≤ 1 / 2) (N : ℕ) :
    0 ≤ ∑ l ∈ Finset.range N, x ^ l ∧ ∑ l ∈ Finset.range N, x ^ l ≤ 4 := by
  have hxa := abs_le.mp hx
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hxa
    linarith [hxa.2]
  have hxN : |x ^ N| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (by linarith)
  have hxN' := abs_le.mp hxN
  rw [geom_sum_eq hx1 N]
  constructor
  · exact div_nonneg_of_nonpos (by linarith [hxN'.2]) (by linarith [hxa.2])
  · rw [div_le_iff_of_neg (by linarith [hxa.2])]
    linarith [hxa.2, hxN'.1]

theorem abs_x_eq (𝔭 : Ideal (𝓞 F)) (m : ℕ) :
    |etaF K F 𝔭 ^ m * ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹| = ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹ := by
  rw [abs_mul, abs_eta_pow, one_mul, abs_of_nonneg (by positivity)]


theorem alphaN_rank_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hm : finrank K V = 0) {n : 𝓞 F} (hn : n ≠ 0) : alphaN h L 𝔭 n = 0 := by
  have hsub : Subsingleton V := finrank_zero_iff.1 hm
  rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn le_rfl]
  have h0 : nkCount h L 𝔭 (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) n = 0 := by
    unfold nkCount
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, y, -, hc⟩
    have hy : h (y : V) (y : V) = algebraMap F K ((0 : 𝓞 F) : F) := by
      rw [Subsingleton.elim (y : V) 0]
      simp
    rw [hy, MeanB.congrP_algebraMap_iff_sub_mem h𝔭, zero_sub, neg_mem_iff, mem_pow_iff_le_vF h𝔭 hn] at hc
    omega
  rw [h0]
  simp

end unitaryAbsoluteValueBounds

theorem alphaN_of_vd_zero_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n = (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) :=
  unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd hL hLi h𝔭 hv hm hn

theorem alphaN_eq_of_vF_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0) (hvv : vF 𝔭 n = vF 𝔭 n') :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  rcases Nat.eq_zero_or_pos (finrank K V) with hm | hm
  · rw [unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL hLi h𝔭 hm hn,
      unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL hLi h𝔭 hm hn']
  · rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv hm _ n hn rfl, unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv hm _ n' hn' rfl, hvv]


theorem alphaN_rho_diff_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hvv : vF 𝔭 n = vF 𝔭 n' + 1) :
    |alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) - alphaN h L 𝔭 n' / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))| ≤
      8 * ((vF 𝔭 n : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(((finrank K V - 1) * ((vF 𝔭 n + 1) / 2) : ℕ) : ℤ)) := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := unitaryAbsoluteValueBounds.one_lt_q h𝔭
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n hn rfl,
    unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n' hn' rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne',
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne', hvv,
    Finset.sum_range_succ _ (vF 𝔭 n' + 1), add_sub_cancel_left, abs_pow, unitaryAbsoluteValueBounds.abs_x_eq, zpow_neg,
    zpow_natCast, inv_pow, ← pow_mul]
  have h1 : ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n' + 1)))⁻¹ ≤
      ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le (Nat.mul_le_mul_left _ (by omega)))
  have h2 : (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ := by
    positivity
  have h3 : (1 : ℝ) ≤ 8 * (((vF 𝔭 n' + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((vF 𝔭 n' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc _ ≤ _ := h1
    _ = 1 * _ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 h2

end Formalism.HermitianLattices.Ext.L3
end
end
