import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CreAnnApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithTotalBoundary
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreApply
import BuildAid.ForwardExisting

section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.TorC

open CompanionTheory.D.LK (Pos)

section Abstract

variable {R ι : Type*} [Ring R] [Algebra ℂ R] [Fintype ι] [DecidableEq ι]

def br (x y : R) : R := x * y - y * x

theorem br_mul (x y z : R) : br x (y * z) = br x y * z + y * br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_sub, sub_mul, mul_assoc]
  abel

theorem br_add_right (x y z : R) : br x (y + z) = br x y + br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_add_left (x y z : R) : br (x + y) z = br x z + br y z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_smul_right (r : ℂ) (x y : R) : br x (r • y) = r • br x y := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem br_sum_right {κ : Type*} (s : Finset κ) (x : R) (f : κ → R) : br x (∑ i ∈ s, f i) = ∑ i ∈ s, br x (f i) := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

theorem br_anti (x y : R) : br x y = -br y x := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, neg_sub]

theorem swap3 {M : Type*} [AddCommMonoid M] (g : ι → ι → ι → M) :
    ∑ j, ∑ k, ∑ b, g j k b = ∑ b, ∑ k, ∑ j, g j k b := by
  calc ∑ j, ∑ k, ∑ b, g j k b = ∑ j, ∑ b, ∑ k, g j k b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, g j k b := Finset.sum_comm
    _ = ∑ b, ∑ k, ∑ j, g j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem swap4 {M : Type*} [AddCommMonoid M] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b := by
  calc ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ i, ∑ j, ∑ b, ∑ k, f i j k b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ j, ∑ k, f i j k b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ j, ∑ k, f i j k b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ i, ∑ k, f i j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

def Dm (a c : ι → R) (A : ι → ι → ℂ) : R := ∑ i, ∑ k, A i k • (c k * a i)

theorem reindex (W : ι → ι → ι → R) (S : ι → ι → ι → ℂ) (A : ι → ι → ℂ) :
    ∑ i, ∑ j, ∑ k, S i j k • ((∑ l, A k l • W i j l) - (∑ b, A b j • W i b k) - ∑ b, A b i • W b j k) =
      ∑ i, ∑ j, ∑ k, ((∑ m, S i j m * A m k) - (∑ m, S i m k * A j m) - ∑ m, S m j k * A i m) • W i j k := by
  simp only [smul_sub, sub_smul, Finset.smul_sum, Finset.sum_smul, smul_smul, Finset.sum_sub_distrib]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  · exact Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.RealMult.TorC.swap3 _
  · exact GlobalTheory.CompanionTheory.RealMult.TorC.swap4 _

variable {a c : ι → R}

theorem term_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (a m) = -(if m = k then a i else 0) := by
  have h₁ : a i * a m = -(a m * a i) := eq_neg_of_add_eq_zero_left (haa i m)
  have h₂ : a m * c k = (if m = k then 1 else 0) - c k * a m := eq_sub_of_add_eq (hac m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (a m), h₂]
  split_ifs <;> simp only [sub_mul, mul_neg, mul_assoc, one_mul, zero_mul] <;> abel

theorem term_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (c m) = if i = m then c k else 0 := by
  have h₁ : a i * c m = (if i = m then 1 else 0) - c m * a i := eq_sub_of_add_eq (hac i m)
  have h₂ : c m * c k = -(c k * c m) := eq_neg_of_add_eq_zero_left (hcc m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (c m), h₂]
  split_ifs <;> simp only [mul_sub, neg_mul, mul_assoc, mul_one, mul_zero] <;> abel

theorem dm_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (a m) = -∑ i, A i m • a i := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (a m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (a m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • -(if m = k then a i else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_a haa hac]
    _ = -∑ i, A i m • a i := by
          simp [smul_ite, Finset.sum_neg_distrib]

theorem dm_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (c m) = ∑ k, A m k • c k := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (c m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (c m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • (if i = m then c k else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_c hcc hac]
    _ = ∑ k, A m k • c k := by
          rw [Finset.sum_comm]
          simp [smul_ite]

theorem bracket_wedge_formula (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (i j k : ι) :
    br (Dm a c A) (c k * a j * a i) =
      (∑ l, A k l • (c l * a j * a i)) - (∑ b, A b j • (c k * a b * a i)) - ∑ b, A b i • (c k * a j * a b) := by
  rw [GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_c hcc hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac]
  simp only [add_mul, mul_neg, neg_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, mul_assoc]
  abel

theorem br_lift_dm {L : R} (hLa : ∀ i, br L (a i) = 0) (hLc : ∀ i, br L (c i) = 0) (A : ι → ι → ℂ) :
    br L (Dm a c A) = 0 := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br_sum_right,
    GlobalTheory.CompanionTheory.RealMult.TorC.br_smul_right, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, hLa, hLc, zero_mul, mul_zero,
    add_zero, smul_zero, Finset.sum_const_zero]

end Abstract

section Car

variable {n : ℕ}

theorem key_lt (p : Pos n) : CompanionTheory.D.LK.key p < n * n := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  nlinarith

theorem keyR_inj {i j : Ix n} (h : keyR i = keyR j) : i = j := by
  obtain ⟨b, p⟩ := i
  obtain ⟨b', q⟩ := j
  have hp := key_lt p
  have hq := key_lt q
  cases b <;> cases b' <;> simp only [keyR, if_true, Bool.false_eq_true, if_false] at h
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]

def tw (i j : Ix n) : ℂ := if keyR j < keyR i then -1 else 1

theorem tw_self (i : Ix n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Ix n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Ix n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyR i ≠ keyR j := fun e => h (keyR_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem liftR_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cr n V)
    (A : Finset (Ix n)) : liftR n T x A = T (x A) := rfl

theorem br_lift_lift (T S : Module.End ℂ V) :
    br (liftR n T : Module.End ℂ (Cr n V)) (liftR n S) = liftR n (br T S) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [br, liftR_apply]

end Car

section Coefficients

variable {n : ℕ}

end Coefficients

section Units

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V}

end Units

end GlobalTheory.CompanionTheory.RealMult.TorC
end
end

section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.LeviQ

open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)

variable {n : ℕ}

theorem key_lt' (p : Pos n) : CompanionTheory.D.LK.key p < (n + 1) * (n + 1) := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  nlinarith

theorem keyL_inj {i j : Lt n} (h : keyL i = keyL j) : i = j := by
  obtain ⟨a, i⟩ := i
  obtain ⟨b, j⟩ := j
  have hi := key_lt' i
  have hj := key_lt' j
  cases a <;> cases b <;> simp only [keyL, Bool.false_eq_true, if_false, if_true, zero_add] at h
  · rw [CompanionTheory.D.LK.Car.key_inj (Nat.add_left_cancel h)]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj h]

def tw (i j : Lt n) : ℂ := if keyL j < keyL i then -1 else 1

theorem tw_self (i : Lt n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Lt n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Lt n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyL i ≠ keyL j := fun e => h (keyL_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sg_mul_self (i : Lt n) (A : Finset (Lt n)) : sgL i A * sgL i A = 1 := by
  unfold sgL
  rw [← mul_pow]; simp

theorem sg_insert (i : Lt n) {j : Lt n} {A : Finset (Lt n)} (h : j ∉ A) :
    sgL i (insert j A) = tw i j * sgL i A := by
  unfold sgL tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sg_erase (i : Lt n) {j : Lt n} {A : Finset (Lt n)} (h : j ∈ A) :
    sgL i (A.erase j) = tw i j * sgL i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annq_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annq i x A = if i ∈ A then 0 else sgL i A • x (insert i A) := rfl

theorem creq_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creq i x A = if i ∈ A then sgL i A • x (A.erase i) else 0 := rfl

theorem liftq_apply (T : Module.End ℂ V) (x : Cq n V) (A : Finset (Lt n)) :
    liftq n T x A = T (x A) := rfl

theorem annq_annq (i j : Lt n) : (annq i * annq j + annq j * annq i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    annq_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem creq_creq (i j : Lt n) : (creq i * creq j + creq j * creq i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    creq_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem annq_creq (i j : Lt n) :
    (annq i * creq j + creq j * annq i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annq_apply, creq_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem liftq_sum_smul {κ : Type*} [Fintype κ] (d : κ → ℂ) (T : κ → Module.End ℂ V) :
    (liftq n (∑ k, d k • T k) : Module.End ℂ (Cq n V)) = ∑ k, d k • (liftq n (T k) : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [liftq_apply, LinearMap.sum_apply, Finset.sum_apply]

open GlobalTheory.CompanionTheory.RealMult.TorC (br Dm br_mul br_add_left br_add_right br_smul_right br_sum_right br_anti dm_a dm_c bracket_wedge_formula
  br_lift_dm)

theorem br_lift_annq (T : Module.End ℂ V) (i : Lt n) :
    br (liftq n T : Module.End ℂ (Cq n V)) (annq i) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, LinearMap.zero_apply, Pi.zero_apply,
    annq_apply, liftq_apply]
  by_cases hi : i ∈ A <;> simp [hi]

theorem br_lift_creq (T : Module.End ℂ V) (i : Lt n) :
    br (liftq n T : Module.End ℂ (Cq n V)) (creq i) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, LinearMap.zero_apply, Pi.zero_apply,
    creq_apply, liftq_apply]
  by_cases hi : i ∈ A <;> simp [hi]

theorem br_lift_lift (T S : Module.End ℂ V) :
    br (liftq n T : Module.End ℂ (Cq n V)) (liftq n S) = liftq n (br T S) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [br, liftq_apply]

def Mt (s : Bool) (p q : Fin n) (l m : Lt n) : ℂ := if m.1 = (s == l.1) then adC p q l.2 m.2 else 0

def Sq (l1 l2 l3 : Lt n) : ℂ :=
  if l3.1 = (l1.1 == l2.1) then GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc l1.2 l2.2 l3.2 else 0

theorem sum_Mt {M : Type*} [AddCommMonoid M] [Module ℂ M] (s : Bool) (p q : Fin n) (l : Lt n) (f : Lt n → M) :
    ∑ m, Mt s p q l m • f m = ∑ k : Pos n, adC p q l.2 k • f ((s == l.1), k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (s == l.1)]
  · simp [Mt]
  · intro b _ hb
    exact Finset.sum_eq_zero fun k _ => by simp [Mt, hb]
  · simp

theorem sum_Sq {M : Type*} [AddCommMonoid M] [Module ℂ M] (l1 l2 : Lt n) (f : Lt n → M) :
    ∑ m, Sq l1 l2 m • f m = ∑ k : Pos n, GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc l1.2 l2.2 k • f ((l1.1 == l2.1), k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (l1.1 == l2.1)]
  · simp [Sq]
  · intro b _ hb
    exact Finset.sum_eq_zero fun k _ => by simp [Sq, hb]
  · simp

theorem adLq_eq (s : Bool) (p q : Fin n) :
    (adLq s p q : Module.End ℂ (Cq n V)) = Dm annq creq (Mt s p q) := by
  unfold adLq Dm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Mt]

def cubicBoundaryPart (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module.End ℂ (Cq n V) :=
  ∑ l1 : Lt n, ∑ l2 : Lt n, ∑ l3 : Lt n, Sq l1 l2 l3 • (creq l3 * annq l2 * annq l1)

def moduleBoundaryPart (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  ∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l

theorem bdq_eq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : bdq E1 E2 = moduleBoundaryPart E1 E2 + cubicBoundaryPart n V := by
  unfold bdq moduleBoundaryPart cubicBoundaryPart
  congr 1
  simp only [sum_Sq]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  by_cases h : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
  · simp [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc, h]
  · simp [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc, h]

section Ops

variable (E1 E2 : Fin n → Fin n → Module.End ℂ V)

theorem aa (i j : Lt n) : (annq i * annq j + annq j * annq i : Module.End ℂ (Cq n V)) = 0 := annq_annq i j
theorem cc (i j : Lt n) : (creq i * creq j + creq j * creq i : Module.End ℂ (Cq n V)) = 0 := creq_creq i j
theorem ac (i j : Lt n) : (annq i * creq j + creq j * annq i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 :=
  annq_creq i j

theorem lFq_eq (s : Bool) (p q : Fin n) :
    lFq E1 E2 s p q = liftq n (Ts E1 E2 s p q) + Dm annq creq (Mt s p q) := by
  rw [lFq, adLq_eq]

theorem br_L_ann (s : Bool) (p q : Fin n) (m : Lt n) :
    br (lFq E1 E2 s p q) (annq m) = -∑ i, Mt s p q i m • annq i := by
  rw [lFq_eq, br_add_left, br_lift_annq, zero_add, dm_a aa ac]

theorem br_dm_lift (A : Lt n → Lt n → ℂ) (T : Module.End ℂ V) :
    br (Dm annq creq A) (liftq n T : Module.End ℂ (Cq n V)) = 0 := by
  rw [br_anti, br_lift_dm (fun i => br_lift_annq T i) (fun i => br_lift_creq T i), neg_zero]

theorem br_L_lift (s : Bool) (p q : Fin n) (T : Module.End ℂ V) :
    br (lFq E1 E2 s p q) (liftq n T) = liftq n (br (Ts E1 E2 s p q) T) := by
  rw [lFq_eq, br_add_left, br_lift_lift, br_dm_lift, add_zero]

theorem bracket_levi_moduleBoundaryPart (s : Bool) (p q : Fin n) :
    br (lFq E1 E2 s p q) (moduleBoundaryPart E1 E2) =
      ∑ l : Lt n, (liftq n (br (Ts E1 E2 s p q) (Tl E1 E2 l) - ∑ m, Mt s p q l m • Tl E1 E2 m) :
        Module.End ℂ (Cq n V)) * annq l := by
  have hsub : ∀ S T : Module.End ℂ V, (liftq n (S - T) : Module.End ℂ (Cq n V)) = liftq n S - liftq n T := fun S T => by
    refine LinearMap.ext fun x => funext fun A => ?_
    simp [liftq_apply]
  unfold moduleBoundaryPart
  simp only [br_sum_right, br_mul, br_L_lift, br_L_ann, hsub, liftq_sum_smul, sub_mul, Finset.sum_mul, mul_neg,
    Finset.mul_sum, mul_smul_comm, smul_mul_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 2
  exact Finset.sum_comm

theorem bracket_levi_cubicBoundaryPart (s : Bool) (p q : Fin n) :
    br (lFq E1 E2 s p q) (cubicBoundaryPart n V) =
      ∑ l1 : Lt n, ∑ l2 : Lt n, ∑ l3 : Lt n,
        ((∑ m, Sq l1 l2 m * Mt s p q m l3) - (∑ m, Sq l1 m l3 * Mt s p q l2 m) - ∑ m, Sq m l2 l3 * Mt s p q l1 m) •
          (creq l3 * annq l2 * annq l1) := by
  rw [lFq_eq, br_add_left]
  have h0 : br (liftq n (Ts E1 E2 s p q) : Module.End ℂ (Cq n V)) (cubicBoundaryPart n V) = 0 := by
    simp only [cubicBoundaryPart, br_sum_right, br_smul_right, br_mul, br_lift_annq, br_lift_creq, zero_mul, mul_zero, add_zero,
      smul_zero, Finset.sum_const_zero]
  rw [h0, zero_add]
  unfold cubicBoundaryPart
  have hW := fun l1 l2 l3 => bracket_wedge_formula (R := Module.End ℂ (Cq n V)) (ι := Lt n) (a := annq) (c := creq) aa cc ac (Mt s p q) l1 l2 l3
  simp only [br_sum_right, br_smul_right, hW]
  exact GlobalTheory.CompanionTheory.RealMult.TorC.reindex (R := Module.End ℂ (Cq n V)) (fun i j k => creq k * annq j * annq i) Sq (Mt s p q)

end Ops

theorem coef_zero {lev : Fin n → ℕ} (hm : Monotone lev) {s : Bool} {p q : Fin n} (hpq : lev p = lev q) {l1 l2 : Lt n}
    (h1 : inUL lev l1) (h2 : inUL lev l2) (l3 : Lt n) :
    (∑ m, Sq l1 l2 m * Mt s p q m l3) - (∑ m, Sq l1 m l3 * Mt s p q l2 m) - ∑ m, Sq m l2 l3 * Mt s p q l1 m = 0 := by
  obtain ⟨a, i⟩ := l1
  obtain ⟨b, j⟩ := l2
  obtain ⟨c, k⟩ := l3
  have e1 : ∑ m, Sq (a, i) (b, j) m * Mt s p q m (c, k) =
      ∑ m : Pos n, GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc i j m * Mt s p q ((a == b), m) (c, k) := by
    simpa only [smul_eq_mul] using sum_Sq (a, i) (b, j) (fun m => Mt s p q m (c, k))
  have e2 : ∑ m, Sq (a, i) m (c, k) * Mt s p q (b, j) m =
      ∑ m : Pos n, adC p q j m * Sq (a, i) ((s == b), m) (c, k) := by
    simpa only [smul_eq_mul, mul_comm] using sum_Mt s p q (b, j) (fun m => Sq (a, i) m (c, k))
  have e3 : ∑ m, Sq m (b, j) (c, k) * Mt s p q (a, i) m =
      ∑ m : Pos n, adC p q i m * Sq ((s == a), m) (b, j) (c, k) := by
    simpa only [smul_eq_mul, mul_comm] using sum_Mt s p q (a, i) (fun m => Sq m (b, j) (c, k))
  rw [e1, e2, e3]
  have hD := GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.Dc_eq_zero (p := p) (q := q) hm hpq (a := i) (b := j) h1 h2 k
  unfold GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.Dc at hD
  by_cases hc : c = (s == (a == b))
  · have i1 : c = (s == (a == b)) := hc
    have i2 : c = (a == (s == b)) := by rw [hc]; cases s <;> cases a <;> cases b <;> rfl
    have i3 : c = ((s == a) == b) := by rw [hc]; cases s <;> cases a <;> cases b <;> rfl
    simp only [Mt, Sq, i1.symm, i2.symm, i3.symm, if_true]
    simp only [mul_comm (adC p q j _), mul_comm (adC p q i _)]
    exact hD
  · have i2 : ¬c = (a == (s == b)) := fun e => hc (by rw [e]; cases s <;> cases a <;> cases b <;> rfl)
    have i3 : ¬c = ((s == a) == b) := fun e => hc (by rw [e]; cases s <;> cases a <;> cases b <;> rfl)
    simp [Mt, Sq, hc, i2, i3]

section Abs

variable {R ι : Type*} [Ring R] [Algebra ℂ R] [Fintype ι] [DecidableEq ι] {a c : ι → R}

open GlobalTheory.CompanionTheory.RealMult.TorC (swap3)

theorem br_dm_gen (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A B : ι → ι → ℂ) :
    br (Dm a c A) (Dm a c B) =
      ∑ i, ∑ l, ((∑ m, B i m * A m l) - ∑ m, A i m * B m l) • (c l * a i) := by
  have h1 : ∑ m, ∑ l, B m l • ((∑ x, A l x • c x) * a m) = ∑ m, ∑ x, (∑ l, B m l * A l x) • (c x * a m) :=
    sum_congr rfl fun m _ => by
      simp only [sum_mul, smul_mul_assoc, smul_sum, smul_smul, sum_smul]; exact sum_comm
  have h2 : ∑ m, ∑ l, B m l • (c l * ∑ i, A i m • a i) = ∑ i, ∑ l, (∑ m, A i m * B m l) • (c l * a i) := by
    simp only [mul_sum, mul_smul_comm, smul_sum, smul_smul, sum_smul]
    rw [swap3 (fun m l i => (B m l * A i m) • (c l * a i))]
    exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => sum_congr rfl fun m _ => by rw [mul_comm]
  have h3 : br (Dm a c A) (Dm a c B) =
      (∑ m, ∑ l, B m l • ((∑ x, A l x • c x) * a m)) - ∑ m, ∑ l, B m l • (c l * ∑ i, A i m • a i) := by
    conv_lhs => rw [Dm.eq_1 a c B]
    simp only [br_sum_right, br_smul_right, br_mul, dm_a haa hac, dm_c hcc hac, mul_neg, smul_add, smul_neg,
      sum_add_distrib, sum_neg_distrib, sub_eq_add_neg]
  rw [h3, h1, h2]
  simp only [sub_smul, sum_sub_distrib]

end Abs

def eps (s : Bool) : ℂ := if s then 1 else -1

theorem eps_mul (s t : Bool) : eps s * eps t = eps (s == t) := by
  cases s <;> cases t <;> simp [eps]

section Rel

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V}

theorem Ts_eq (s : Bool) (p q : Fin n) : Ts E1 E2 s p q = E1 p q + eps s • E2 p q := by
  cases s <;> simp [Ts, eps, sub_eq_add_neg]

theorem ts_rel (h : PairRel E1 E2) (s t : Bool) (p q r v : Fin n) :
    br (Ts E1 E2 s p q) (Ts E1 E2 t r v) =
      (if q = r then Ts E1 E2 (s == t) p v else 0) - (if v = p then Ts E1 E2 (s == t) r q else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  have g1 := h1 p q r v
  have g2 := h2 p q r v
  have c1 : E1 p q * E2 r v = E2 r v * E1 p q := h3 p q r v
  have c2 : E1 r v * E2 p q = E2 p q * E1 r v := h3 r v p q
  have e : br (E1 p q + eps s • E2 p q) (E1 r v + eps t • E2 r v) =
      (E1 p q * E1 r v - E1 r v * E1 p q) + (eps s * eps t) • (E2 p q * E2 r v - E2 r v * E2 p q) := by
    simp only [br, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, c1, c2]
    module
  rw [Ts_eq, Ts_eq, e, g1, g2, eps_mul]
  simp only [Ts_eq]
  split_ifs <;> module

theorem lin_q (hP : PairRel E1 E2) {lev : Fin n → ℕ} (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q)
    (s : Bool) {l : Lt n} (hl : inUL lev l) :
    br (Ts E1 E2 s p q) (Tl E1 E2 l) - ∑ m, Mt s p q l m • Tl E1 E2 m = 0 := by
  obtain ⟨u, i⟩ := l
  have hi : lev i.1.1 < lev i.1.2 := hl
  rw [sum_Mt]
  have hX : ∀ k : Pos n, Tl E1 E2 ((s == u), k) = Ts E1 E2 (s == u) k.1.1 k.1.2 := fun _ => rfl
  simp only [hX]
  set X := Ts E1 E2 (s == u) with hXd
  have h1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1.1 = p ∧ k.1.2 = i.1.2 then (1 : ℂ) else 0) • X k.1.1 k.1.2 =
      if q = i.1.1 then X p i.1.2 else 0 := by
    by_cases h : q = i.1.1
    · have hlt : p < i.1.2 := GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.lt_of_lev hm (by rw [hpq, h]; exact hi)
      simp only [h, true_and, if_true]
      exact GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.sum_ind hlt fun k => X k.1.1 k.1.2
    · simp [h]
  have h2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1.1 = i.1.1 ∧ k.1.2 = q then (1 : ℂ) else 0) • X k.1.1 k.1.2 =
      if i.1.2 = p then X i.1.1 q else 0 := by
    by_cases h : i.1.2 = p
    · have hlt : i.1.1 < q := GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.lt_of_lev hm (by rw [← hpq, ← h]; exact hi)
      simp only [h, true_and, if_true]
      exact GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.sum_ind hlt fun k => X k.1.1 k.1.2
    · simp [h]
  simp only [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.adC_eq, sub_smul, Finset.sum_sub_distrib]
  rw [h1, h2]
  have := ts_rel hP s u p q i.1.1 i.1.2
  show br (Ts E1 E2 s p q) (Ts E1 E2 u i.1.1 i.1.2) - _ = 0
  rw [this, sub_eq_zero]

theorem annq_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annq i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annq_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · refine ⟨hi, fun h0 => h ?_⟩
    simp [hi, h0]

theorem annq_eq_zero {P : Lt n → Prop} {x : Cq n V} (hx : SuppQ P x) {i : Lt n} (hi : ¬P i) : annq i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (annq_ne h).2 i (mem_insert_self _ _))

theorem annq_supp {P : Lt n → Prop} {x : Cq n V} (hx : SuppQ P x) (i : Lt n) : SuppQ P (annq i x) := by
  intro A h j hj
  exact hx _ (annq_ne h).2 j (mem_insert_of_mem hj)

theorem lFq_bd (hP : PairRel E1 E2) {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cq n V} (hx : SuppQ (inUL lev) x)
    (s : Bool) {p q : Fin n} (hpq : lev p = lev q) :
    lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x) := by
  have h1 : br (lFq E1 E2 s p q) (moduleBoundaryPart E1 E2) x = 0 := by
    rw [bracket_levi_moduleBoundaryPart, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : inUL lev l
    · rw [lin_q hP hm hpq s hl]
      refine funext fun A => ?_
      simp [liftq_apply]
    · rw [Module.End.mul_apply, annq_eq_zero hx hl, map_zero]
  have h2 : br (lFq E1 E2 s p q) (cubicBoundaryPart n V) x = 0 := by
    rw [bracket_levi_cubicBoundaryPart]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun m _ => ?_
    by_cases ha : inUL lev a
    · by_cases hb : inUL lev b
      · rw [coef_zero hm hpq ha hb, zero_smul]
      · simp only [Module.End.mul_apply]
        rw [annq_eq_zero (annq_supp hx a) hb, map_zero, smul_zero]
    · simp only [Module.End.mul_apply]
      rw [annq_eq_zero hx ha, map_zero, map_zero, smul_zero]
  rw [bdq_eq]
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
  simp only [LinearMap.add_apply, map_add]
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2]

theorem mt_id {lev : Fin n → ℕ} (hm : Monotone lev) {s t : Bool} {p q r v : Fin n} (hpq : lev p = lev q)
    (hrv : lev r = lev v) {i : Lt n} (hi : inUL lev i) (l : Lt n) :
    (∑ m, Mt t r v i m * Mt s p q m l) - ∑ m, Mt s p q i m * Mt t r v m l =
      (if q = r then Mt (s == t) p v i l else 0) - (if v = p then Mt (s == t) r q i l else 0) := by
  obtain ⟨u, i⟩ := i
  obtain ⟨w, l⟩ := l
  have e1 : ∑ m, Mt t r v (u, i) m * Mt s p q m (w, l) = ∑ k : Pos n, adC r v i k * Mt s p q ((t == u), k) (w, l) := by
    simpa only [smul_eq_mul] using sum_Mt t r v (u, i) (fun m => Mt s p q m (w, l))
  have e2 : ∑ m, Mt s p q (u, i) m * Mt t r v m (w, l) = ∑ k : Pos n, adC p q i k * Mt t r v ((s == u), k) (w, l) := by
    simpa only [smul_eq_mul] using sum_Mt s p q (u, i) (fun m => Mt t r v m (w, l))
  rw [e1, e2]
  have hM := GlobalTheory.CompanionTheory.RgCOBlock.LetterGl.mat_id hm hpq hrv (i := i) hi l
  rw [Finset.sum_sub_distrib] at hM
  by_cases hc : w = ((s == t) == u)
  · have i1 : w = (s == (t == u)) := by rw [hc]; cases s <;> cases t <;> cases u <;> rfl
    have i2 : w = (t == (s == u)) := by rw [hc]; cases s <;> cases t <;> cases u <;> rfl
    simp only [Mt, i1.symm, i2.symm, hc.symm, if_true]
    exact hM
  · have i1 : ¬w = (s == (t == u)) := fun e => hc (by rw [e]; cases s <;> cases t <;> cases u <;> rfl)
    have i2 : ¬w = (t == (s == u)) := fun e => hc (by rw [e]; cases s <;> cases t <;> cases u <;> rfl)
    simp [Mt, hc, i1, i2]

theorem dm_apply (A : Lt n → Lt n → ℂ) (x : Cq n V) :
    (Dm annq creq A : Module.End ℂ (Cq n V)) x = ∑ i, ∑ l, A i l • creq l (annq i x) := by
  simp [Dm, LinearMap.sum_apply, Module.End.mul_apply]

theorem dm_comm_apply {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cq n V} (hx : SuppQ (inUL lev) x)
    {s t : Bool} {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    br (Dm annq creq (Mt s p q)) (Dm annq creq (Mt t r v) : Module.End ℂ (Cq n V)) x =
      (if q = r then Dm annq creq (Mt (s == t) p v) x else 0) -
        (if v = p then (Dm annq creq (Mt (s == t) r q) : Module.End ℂ (Cq n V)) x else 0) := by
  rw [br_dm_gen (R := Module.End ℂ (Cq n V)) aa cc ac]
  have t1 : ∀ i l : Lt n,
      ((∑ m, Mt t r v i m * Mt s p q m l) - ∑ m, Mt s p q i m * Mt t r v m l) • creq l (annq i x) =
      ((if q = r then Mt (s == t) p v i l else 0) - (if v = p then Mt (s == t) r q i l else 0)) • creq l (annq i x) := by
    intro i l
    by_cases hi : inUL lev i
    · rw [mt_id hm hpq hrv hi]
    · rw [annq_eq_zero hx hi, map_zero, smul_zero, smul_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [t1]
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs
    · rw [dm_apply]
    · simp
  · split_ifs
    · rw [dm_apply]
    · simp

theorem lFq_rel (hP : PairRel E1 E2) {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cq n V} (hx : SuppQ (inUL lev) x)
    (s t : Bool) {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    lFq E1 E2 s p q (lFq E1 E2 t r v x) - lFq E1 E2 t r v (lFq E1 E2 s p q x) =
      (if q = r then lFq E1 E2 (s == t) p v x else 0) - (if v = p then lFq E1 E2 (s == t) r q x else 0) := by
  have hb : br (lFq E1 E2 s p q) (lFq E1 E2 t r v) =
      liftq n (br (Ts E1 E2 s p q) (Ts E1 E2 t r v)) + br (Dm annq creq (Mt s p q)) (Dm annq creq (Mt t r v)) := by
    rw [lFq_eq E1 E2 t r v, br_add_right, br_L_lift, lFq_eq E1 E2 s p q, br_add_left,
      br_lift_dm (fun i => br_lift_annq _ i) (fun i => br_lift_creq _ i), zero_add]
  have h := LinearMap.congr_fun hb x
  rw [LinearMap.add_apply, dm_comm_apply hm hx hpq hrv, ts_rel hP] at h
  have hsub : ∀ S T : Module.End ℂ V, (liftq n (S - T) : Module.End ℂ (Cq n V)) x = liftq n S x - liftq n T x :=
    fun S T => by
      funext A
      simp [liftq_apply]
  rw [hsub] at h
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  simp only [lFq_eq, LinearMap.add_apply]
  have h0 : (liftq n (0 : Module.End ℂ V) : Module.End ℂ (Cq n V)) x = 0 := by
    funext A
    simp [liftq_apply]
  split_ifs <;> (try simp only [h0]) <;> abel

theorem cre_ann_ne (i k : Lt n) (x : Cq n V) (A : Finset (Lt n))
    (h : (creq k * annq i : Module.End ℂ (Cq n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  have e : (creq k * annq i : Module.End ℂ (Cq n V)) x A =
      if k ∈ A then sgL k A • (if i ∈ A.erase k then (0 : V) else
        sgL i (A.erase k) • x (insert i (A.erase k))) else 0 := rfl
  rw [e] at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · simp [hk, hi] at h
    · refine ⟨hk, hi, fun h0 => h ?_⟩
      simp [hk, hi, h0]
  · simp [hk] at h

theorem lFq_ne (s : Bool) (p q : Fin n) (x : Cq n V) (A : Finset (Lt n)) (h : lFq E1 E2 s p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ (t : Bool) (i k : Pos n), adC p q i k ≠ 0 ∧
      (creq ((s == t), k) * annq (t, i) : Module.End ℂ (Cq n V)) x A ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨h0, h1⟩ := hc
  apply h
  have hs : adLq s p q x A = 0 := by
    unfold adLq
    simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hz : adC p q i k = 0
    · simp [hz]
    · rw [h1 t i k hz, smul_zero]
  have e : lFq E1 E2 s p q x A = Ts E1 E2 s p q (x A) + adLq s p q x A := rfl
  rw [e, hs, h0, map_zero, add_zero]

theorem lFq_supp_deg {lev : Fin n → ℕ} {x : Cq n V} (hx : SuppQ (inUL lev) x) (s : Bool) {p q : Fin n}
    (hpq : lev p = lev q) :
    SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ ∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x) := by
  constructor
  · intro A hA m hm
    rcases lFq_ne s p q x A hA with h | ⟨t, i, k, hc, h⟩
    · exact hx A h m hm
    · obtain ⟨-, -, h3⟩ := cre_ann_ne (t, i) ((s == t), k) x A h
      by_cases hmk : m = ((s == t), k)
      · subst hmk
        exact GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.inU_of_adC hpq hc (hx _ h3 (t, i) (Finset.mem_insert_self _ _))
      · exact hx _ h3 m (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hmk, hm⟩))
  · intro j hj A hA
    rcases lFq_ne s p q x A hA with h | ⟨t, i, k, -, h⟩
    · exact hj A h
    · obtain ⟨h1, h2, h3⟩ := cre_ann_ne (t, i) ((s == t), k) x A h
      have hc := hj _ h3
      rw [Finset.card_insert_of_notMem h2, Finset.card_erase_of_mem h1] at hc
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨_, h1⟩
      omega

end Rel

end GlobalTheory.CompanionTheory.PairMult.LeviQ

namespace GlobalTheory.CompanionTheory.PairMult

open GlobalTheory.CompanionTheory.PairMult.LeviQ

theorem leviRel : LeviRel := by
  intro n lev V _ _ E1 E2 hm hP x hx
  refine ⟨fun s p q hpq => ?_, fun p q r v hpq hrv => ?_⟩
  · obtain ⟨a, b⟩ := lFq_supp_deg (E1 := E1) (E2 := E2) hx s hpq
    exact ⟨a, b, lFq_bd hP hm hx s hpq⟩
  · have R := fun s t => lFq_rel hP hm hx s t hpq hrv
    have tt := R true true
    have tf := R true false
    have ft := R false true
    have ff := R false false
    simp only [beq_self_eq_true, Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false,
      beq_iff_eq] at tt tf ft ff
    simp only [c1, c2, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, map_smul, map_add, map_sub]
    refine ⟨?_, ?_, ?_⟩
    · split_ifs at tt tf ft ff ⊢ <;>
        linear_combination (norm := module) (1 / 4 : ℂ) • tt + (1 / 4 : ℂ) • tf + (1 / 4 : ℂ) • ft + (1 / 4 : ℂ) • ff
    · split_ifs at tt tf ft ff ⊢ <;>
        linear_combination (norm := module) (1 / 4 : ℂ) • tt - (1 / 4 : ℂ) • tf - (1 / 4 : ℂ) • ft + (1 / 4 : ℂ) • ff
    · split_ifs at tt tf ft ff <;>
        linear_combination (norm := module) (1 / 4 : ℂ) • tt - (1 / 4 : ℂ) • tf + (1 / 4 : ℂ) • ft - (1 / 4 : ℂ) • ff

end GlobalTheory.CompanionTheory.PairMult
end
end

section
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.COU

open GlobalTheory.CompanionTheory.PairMult
open CompanionTheory.D.LK (Pos key)
open Formalism.REAL (GlRel)

variable {n : ℕ}
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

structure MorQ (T : V →ₗ[ℂ] W) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (F1 F2 : Fin n → Fin n → Module.End ℂ W) : Prop where
  h1 : ∀ a b y, T (E1 a b y) = F1 a b (T y)
  h2 : ∀ a b y, T (E2 a b y) = F2 a b (T y)

theorem adLq_apply (s : Bool) (p q : Fin n) (x : Cq n V) :
    adLq s p q x = ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n,
      CompanionTheory.RgExh.U.adC p q i k • creq ((s == t), k) (annq (t, i) x) := by
  simp [adLq, Module.End.mul_apply, LinearMap.sum_apply]

theorem lift_adLq (T : V →ₗ[ℂ] W) (s : Bool) (p q : Fin n) (x : Cq n V) :
    liftq n T (adLq s p q x) = adLq s p q (liftq n T x) := by
  simp only [adLq_apply, map_sum, map_smul, lift_cre', lift_ann']

section MorLemmas

variable {T : V →ₗ[ℂ] W} {E1 E2 : Fin n → Fin n → Module.End ℂ V} {F1 F2 : Fin n → Fin n → Module.End ℂ W}

theorem MorQ.Ts_eq (h : MorQ T E1 E2 F1 F2) (s : Bool) (p q : Fin n) (y : V) :
    T (Ts E1 E2 s p q y) = Ts F1 F2 s p q (T y) := by
  cases s <;> simp [Ts, h.h1, h.h2]

theorem MorQ.lift_Ts (h : MorQ T E1 E2 F1 F2) (s : Bool) (p q : Fin n) (y : Cq n V) :
    liftq n T (liftq n (Ts E1 E2 s p q) y) = liftq n (Ts F1 F2 s p q) (liftq n T y) := by
  funext A
  exact h.Ts_eq s p q (y A)

theorem MorQ.lift_Tl (h : MorQ T E1 E2 F1 F2) (i : Lt n) (y : Cq n V) :
    liftq n T (liftq n (Tl E1 E2 i) y) = liftq n (Tl F1 F2 i) (liftq n T y) :=
  h.lift_Ts _ _ _ y

theorem MorQ.bd (h : MorQ T E1 E2 F1 F2) (x : Cq n V) :
    liftq n T (bdq E1 E2 x) = bdq F1 F2 (liftq n T x) := by
  rw [bd_apply, bd_apply]
  simp only [map_add, map_smul, map_sum, lift_cre', lift_ann', h.lift_Tl]

theorem MorQ.lF (h : MorQ T E1 E2 F1 F2) (s : Bool) (p q : Fin n) (x : Cq n V) :
    liftq n T (lFq E1 E2 s p q x) = lFq F1 F2 s p q (liftq n T x) := by
  simp only [lFq, LinearMap.add_apply, map_add, h.lift_Ts, lift_adLq]

theorem MorQ.cc1 (h : MorQ T E1 E2 F1 F2) (p q : Fin n) (x : Cq n V) :
    liftq n T (c1 E1 E2 p q x) = c1 F1 F2 p q (liftq n T x) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c1, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, h.lF]

theorem MorQ.cc2 (h : MorQ T E1 E2 F1 F2) (p q : Fin n) (x : Cq n V) :
    liftq n T (c2 E1 E2 p q x) = c2 F1 F2 p q (liftq n T x) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c2, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub, h.lF]

theorem MorQ.evC (h : MorQ T E1 E2 F1 F2) (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ x : Cq n V, liftq n T (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 F1 F2) (c2 F1 F2) b (liftq n T x) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun b => ∀ x : Cq n V,
    liftq n T (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 F1 F2) (c2 F1 F2) b (liftq n T x)) ?_ ?_ ?_ ?_ b
  · intro r x
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  · intro p x
    simp only [evB, FreeAlgebra.lift_ι_apply]
    split_ifs
    · exact h.cc1 _ _ x
    · exact h.cc2 _ _ x
    · simp
  · intro a b ha hb x
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  · intro a b ha hb x
    simp only [map_add, LinearMap.add_apply, ha, hb]

theorem MorQ.ev (h : MorQ T E1 E2 F1 F2) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ y : V, T (ev2 E1 E2 a y) = ev2 F1 F2 a (T y) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun a => ∀ y : V, T (ev2 E1 E2 a y) = ev2 F1 F2 a (T y)) ?_ ?_ ?_ ?_ a
  · intro r y
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  · intro p y
    simp only [ev2, FreeAlgebra.lift_ι_apply]
    by_cases hp : p.1 = true
    · simp [hp, h.h1]
    · simp [hp, h.h2]
  · intro a b ha hb y
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  · intro a b ha hb y
    simp only [map_add, LinearMap.add_apply, map_add, ha, hb]

theorem MorQ.lift_ev (h : MorQ T E1 E2 F1 F2) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (x : Cq n V) :
    liftq n T (liftq n (ev2 E1 E2 a) x) = liftq n (ev2 F1 F2 a) (liftq n T x) := by
  funext A
  exact h.ev a (x A)

end MorLemmas

theorem evC_facts (hR : LeviRel) {lev : Fin n → ℕ} (hlev : Monotone lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hE : PairRel E1 E2) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ x : Cq n V, SuppQ (inUL lev) x → SuppQ (inUL lev) (evB lev (c1 E1 E2) (c2 E1 E2) b x) ∧
      (∀ j, DegQ j x → DegQ j (evB lev (c1 E1 E2) (c2 E1 E2) b x)) ∧
      bdq E1 E2 (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 E1 E2) (c2 E1 E2) b (bdq E1 E2 x) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun b => ∀ x : Cq n V, SuppQ (inUL lev) x →
    SuppQ (inUL lev) (evB lev (c1 E1 E2) (c2 E1 E2) b x) ∧
      (∀ j, DegQ j x → DegQ j (evB lev (c1 E1 E2) (c2 E1 E2) b x)) ∧
      bdq E1 E2 (evB lev (c1 E1 E2) (c2 E1 E2) b x) = evB lev (c1 E1 E2) (c2 E1 E2) b (bdq E1 E2 x)) ?_ ?_ ?_ ?_ b
  · intro r x hx
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
    exact ⟨Submodule.smul_mem (supSub V _) r hx, fun j hj => Submodule.smul_mem (supSub V _) r hj, trivial⟩
  · intro c x hx
    have hs := (hR n lev V E1 E2 hlev hE x hx).1
    simp only [evB, FreeAlgebra.lift_ι_apply]
    by_cases hc : lev c.2.1 = lev c.2.2
    · obtain ⟨t1, t2, t3⟩ := hs true _ _ hc
      obtain ⟨f1, f2, f3⟩ := hs false _ _ hc
      rw [if_pos hc]
      by_cases h1 : c.1 = true
      · simp only [h1, if_true, GlobalTheory.CompanionTheory.PairMult.c1, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add]
        refine ⟨Submodule.smul_mem (supSub V _) _ (Submodule.add_mem (supSub V _) t1 f1), fun j hj =>
          Submodule.smul_mem (supSub V _) _ (Submodule.add_mem (supSub V _) (t2 j hj) (f2 j hj)), ?_⟩
        rw [t3, f3]
      · simp only [h1, Bool.false_eq_true, if_false, GlobalTheory.CompanionTheory.PairMult.c2, LinearMap.smul_apply, LinearMap.sub_apply, map_smul,
          map_sub]
        refine ⟨Submodule.smul_mem (supSub V _) _ (Submodule.sub_mem (supSub V _) t1 f1), fun j hj =>
          Submodule.smul_mem (supSub V _) _ (Submodule.sub_mem (supSub V _) (t2 j hj) (f2 j hj)), ?_⟩
        rw [t3, f3]
    · rw [if_neg hc]
      simp only [LinearMap.zero_apply, map_zero]
      exact ⟨Submodule.zero_mem (supSub V _), fun j _ => Submodule.zero_mem (supSub V _), trivial⟩
  · intro a b ha hb x hx
    obtain ⟨h1, h2, h3⟩ := hb x hx
    obtain ⟨h4, h5, h6⟩ := ha _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h4, fun j hj => h5 j (h2 j hj), by rw [h6, h3]⟩
  · intro a b ha hb x hx
    obtain ⟨h1, h2, h3⟩ := ha x hx
    obtain ⟨h4, h5, h6⟩ := hb x hx
    simp only [map_add, LinearMap.add_apply]
    exact ⟨Submodule.add_mem (supSub V _) h1 h4, fun j hj => Submodule.add_mem (supSub V _) (h2 j hj) (h5 j hj),
      by rw [h3, h6]⟩

theorem lift_bd_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} {S : Lt n → Prop} {T : Module.End ℂ V}
    (hT : ∀ i, S i → Commute (Tl E1 E2 i) T) {x : Cq n V} (hx : SuppQ S x) :
    liftq n T (bdq E1 E2 x) = bdq E1 E2 (liftq n T x) := by
  rw [bd_apply, bd_apply]
  have hk : ∀ i : Lt n, liftq n T (liftq n (Tl E1 E2 i) (annq i x)) =
      liftq n (Tl E1 E2 i) (annq i (liftq n T x)) := by
    intro i
    by_cases hi : S i
    · funext A
      rw [← lift_ann']
      simp only [lift_apply]
      exact (LinearMap.congr_fun (hT i hi).eq _).symm
    · rw [← lift_ann', ann_zero hx hi]
      simp
  simp only [map_add, map_smul, map_sum, lift_cre', lift_ann' T, hk]

theorem single_degree_zero (v : V) : DegQ 0 (Pi.single ∅ v : Cq n V) := by
  intro A hA
  by_contra h
  have : A ≠ ∅ := fun h0 => h (by simp [h0])
  exact hA (by simp [Pi.single_apply, this])

theorem eq_single {x : Cq n V} (hx : DegQ 0 x) : x = Pi.single ∅ (x ∅) := by
  funext A
  by_cases h : A = ∅
  · subst h
    simp
  · rw [Pi.single_apply, if_neg h]
    by_contra h0
    exact h (card_eq_zero.mp (hx A h0))

theorem lift_single (T : V →ₗ[ℂ] W) (v : V) :
    liftq n T (Pi.single ∅ v : Cq n V) = Pi.single ∅ (T v) := by
  funext A
  by_cases h : A = ∅
  · subst h
    simp [lift_apply]
  · simp [lift_apply, Pi.single_apply, h]

theorem lF_single (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) (v : V) :
    lFq E1 E2 s p q (Pi.single ∅ v : Cq n V) = Pi.single ∅ (Ts E1 E2 s p q v) := by
  rw [lFq, LinearMap.add_apply, lift_single, adLq_apply]
  simp [ann_eq_zero_of_degree_zero _ (single_degree_zero (n := n) v)]

theorem chainOp_apply_single_empty (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (v : V) :
    c1 E1 E2 p q (Pi.single ∅ v : Cq n V) = Pi.single ∅ (E1 p q v) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c1, LinearMap.smul_apply, LinearMap.add_apply, lF_single, ← Pi.single_add, ← Pi.single_smul]
  congr 1
  simp only [Ts, if_true, Bool.false_eq_true, if_false, LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem second_operator_single (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (v : V) :
    c2 E1 E2 p q (Pi.single ∅ v : Cq n V) = Pi.single ∅ (E2 p q v) := by
  simp only [GlobalTheory.CompanionTheory.PairMult.c2, LinearMap.smul_apply, LinearMap.sub_apply, lF_single, ← Pi.single_sub, ← Pi.single_smul]
  congr 1
  simp only [Ts, if_true, Bool.false_eq_true, if_false, LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem evC_single (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∀ v : V, evB lev (c1 E1 E2) (c2 E1 E2) b (Pi.single ∅ v : Cq n V) = Pi.single ∅ (evB lev E1 E2 b v) := by
  refine FreeAlgebra.induction ℂ _ (motive := fun b => ∀ v : V,
    evB lev (c1 E1 E2) (c2 E1 E2) b (Pi.single ∅ v : Cq n V) = Pi.single ∅ (evB lev E1 E2 b v)) ?_ ?_ ?_ ?_ b
  · intro r v
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [Pi.single_smul]
  · intro p v
    simp only [evB, FreeAlgebra.lift_ι_apply]
    split_ifs
    · exact chainOp_apply_single_empty E1 E2 _ _ v
    · exact second_operator_single E1 E2 _ _ v
    · simp
  · intro a b ha hb v
    simp only [map_mul, Module.End.mul_apply, ha, hb]
  · intro a b ha hb v
    simp only [map_add, LinearMap.add_apply, ha, hb, Pi.single_add]

theorem single_one_deg (i : Lt n) (y : V) : DegQ 1 (Pi.single {i} y : Cq n V) := by
  intro A hA
  by_contra h
  have : A ≠ {i} := fun h0 => h (by simp [h0])
  exact hA (by simp [Pi.single_apply, this])

theorem ann_single (k i : Lt n) (y : V) :
    annq k (Pi.single {i} y : Cq n V) = if k = i then Pi.single ∅ y else 0 := by
  funext A
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl, ann_apply]
    by_cases hA : k ∈ A
    · have : A ≠ ∅ := fun h0 => by simp [h0] at hA
      simp [hA, Pi.single_apply, this]
    · by_cases h0 : A = ∅
      · subst h0
        simp [sgL]
      · have : insert k A ≠ {k} := by
          intro h
          obtain ⟨l, hl⟩ := nonempty_iff_ne_empty.mpr h0
          have := h ▸ mem_insert_of_mem hl
          rw [mem_singleton] at this
          exact hA (this ▸ hl)
        simp [hA, Pi.single_apply, this, h0]
  · rw [if_neg hk, ann_apply]
    by_cases hA : k ∈ A
    · simp [hA]
    · have : insert k A ≠ {i} := by
        intro h
        have := h ▸ mem_insert_self k A
        exact hk (mem_singleton.mp this)
      simp [hA, Pi.single_apply, this]

theorem bd_single (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Lt n) (y : V) :
    bdq E1 E2 (Pi.single {i} y : Cq n V) = Pi.single ∅ (Tl E1 E2 i y) := by
  rw [bd_apply]
  have h2 : ∀ i' j k : Lt n, cq i' j k • creq k (annq j (annq i' (Pi.single {i} y : Cq n V))) = 0 := by
    intro i' j k
    rw [ann_eq_zero_of_degree_zero j (ann_deg i' (single_one_deg i y))]
    simp
  simp only [h2, sum_const_zero, smul_zero, add_zero]
  simp only [ann_single]
  rw [Finset.sum_eq_single i]
  · simp [lift_single]
  · intro k _ hk
    simp [hk]
  · simp

theorem single_one_supp {P : Lt n → Prop} {i : Lt n} (hi : P i) (y : V) : SuppQ P (Pi.single {i} y : Cq n V) := by
  intro A hA l hl
  by_cases h : A = {i}
  · subst h
    rw [mem_singleton.1 hl]
    exact hi
  · exact absurd (by simp [Pi.single_apply, h]) hA

theorem gl_of_inj {T : V →ₗ[ℂ] W} (hT : Function.Injective T) {E : Fin n → Fin n → Module.End ℂ V}
    {F : Fin n → Fin n → Module.End ℂ W} (h : ∀ a b y, T (E a b y) = F a b (T y)) (hF : GlRel F) : GlRel E := by
  intro a b c d
  refine LinearMap.ext fun y => hT ?_
  have key := LinearMap.congr_fun (hF a b c d) (T y)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, h, h, h, h, key]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, h]

theorem pair_of_inj {T : V →ₗ[ℂ] W} (hT : Function.Injective T) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    {F1 F2 : Fin n → Fin n → Module.End ℂ W} (h : MorQ T E1 E2 F1 F2) (hF : PairRel F1 F2) : PairRel E1 E2 := by
  refine ⟨gl_of_inj hT h.h1 hF.1, gl_of_inj hT h.h2 hF.2.1, fun a b c d => ?_⟩
  show _ * _ = _ * _
  refine LinearMap.ext fun y => hT ?_
  have key := LinearMap.congr_fun (hF.2.2 a b c d).eq (T y)
  simp only [Module.End.mul_apply] at key ⊢
  rw [h.h1, h.h2, h.h2, h.h1, key]

def ShiftAt (n : ℕ) (lev : Fin n → ℕ) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (S : Lt n → Prop) (j : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ x : Cq n V, SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
      ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
        liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def HypAB (n : ℕ) (lev : Fin n → ℕ) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) (S : Lt n → Prop) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
    ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

theorem shift_zero {lev : Fin n → ℕ} {a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} {S : Lt n → Prop}
    (hA : HypAB n lev a b S) : ShiftAt n lev a b S 0 := by
  intro V _ _ E1 E2 hE x _ hx _
  obtain ⟨w, hw⟩ := (hA V E1 E2 hE).2 (x ∅)
  let t : Cq n V := ∑ l : Lt n, if inUL lev l then Pi.single {l} (w l) else 0
  refine ⟨t, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem (supSub V _) fun l _ => ?_
    split_ifs with h
    · exact single_one_supp h _
    · exact Submodule.zero_mem (supSub V _)
  · refine Submodule.sum_mem (supSub V _) fun l _ => ?_
    split_ifs
    · exact single_one_deg l _
    · exact Submodule.zero_mem (supSub V _)
  · have e : bdq E1 E2 t = Pi.single ∅ (∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) := by
      have h1 : ∀ l : Lt n, bdq E1 E2 (if inUL lev l then (Pi.single {l} (w l) : Cq n V) else 0) =
          Pi.single ∅ (if inUL lev l then Tl E1 E2 l (w l) else 0) := by
        intro l
        split_ifs
        · exact bd_single E1 E2 l _
        · simp
      simp only [t, map_sum, h1]
      exact (map_sum (AddMonoidHom.single (fun _ : Finset (Lt n) => V) ∅) _ _).symm
    rw [e, ← hw, eq_single hx, lift_single, evC_single, ← Pi.single_sub]
    simp

theorem shift_step (hR : LeviRel) {lev : Fin n → ℕ} (hlev : Monotone lev) {a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {S : Lt n → Prop} (hS : IsSubL lev S) (hA : HypAB n lev a b S) {j : ℕ} (IH : ShiftAt n lev a b S j) :
    ShiftAt n lev a b S (j + 1) := by
  classical
  intro V _ _ E1 E2 hE x hxS hx hxb
  obtain ⟨Y, _, _, F1, F2, π, hF, hπ, h1, h2, hY⟩ := coverQ lev E1 E2 hE
  have hm : MorQ π F1 F2 E1 E2 := ⟨h1, h2⟩

  let x' : Cq n Y := fun A => if x A = 0 then 0 else Function.surjInv hπ (x A)
  have hx'π : liftq n π x' = x := by
    funext A
    by_cases h : x A = 0
    · simp [lift_apply, x', h]
    · simp [lift_apply, x', h, Function.surjInv_eq hπ]
  have hne : ∀ A, x' A ≠ 0 → x A ≠ 0 := by
    intro A hA0 h0
    exact hA0 (by simp [x', h0])
  have hx'D : DegQ (j + 1) x' := fun A h => hx A (hne A h)
  have hx'S : SuppQ S x' := fun A h => hxS A (hne A h)
  have hz0 : liftq n π (bdq F1 F2 x') = 0 := by rw [hm.bd, hx'π, hxb]

  have hk1 : ∀ a b, ∀ y ∈ LinearMap.ker π, F1 a b y ∈ LinearMap.ker π := by
    intro a b y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [h1, hy, map_zero]
  have hk2 : ∀ a b, ∀ y ∈ LinearMap.ker π, F2 a b y ∈ LinearMap.ker π := by
    intro a b y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [h2, hy, map_zero]
  let G1 : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (F1 a b).restrict (hk1 a b)
  let G2 : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (F2 a b).restrict (hk2 a b)
  have hι : MorQ (LinearMap.ker π).subtype G1 G2 F1 F2 := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  have hinj : Function.Injective (LinearMap.ker π).subtype := Submodule.injective_subtype _
  have hG : PairRel G1 G2 := pair_of_inj hinj hι hF

  let z' : Cq n (LinearMap.ker π) := fun A => ⟨bdq F1 F2 x' A, congrFun hz0 A⟩
  have hz' : liftq n (LinearMap.ker π).subtype z' = bdq F1 F2 x' := rfl
  have hne' : ∀ A, z' A ≠ 0 → bdq F1 F2 x' A ≠ 0 := by
    intro A hA0 h0
    exact hA0 (Subtype.ext h0)
  have hzD : DegQ j z' := fun A h => bd_deg F1 F2 hx'D A (hne' A h)
  have hzS : SuppQ S z' := fun A h => bd_supp F1 F2 (cq_closed hS) hx'S A (hne' A h)
  have hzc : bdq G1 G2 z' = 0 := by
    funext A
    apply hinj
    have e := congrFun (hι.bd z') A
    rw [hz'] at e
    have e2 : bdq F1 F2 (bdq F1 F2 x') = 0 := LinearMap.congr_fun (bdq_sq hF) x'
    rw [e2] at e
    simpa [lift_apply] using e
  obtain ⟨w', hw'S, hw'D, hw'⟩ := IH (LinearMap.ker π) G1 G2 hG z' hzS hzD hzc
  have e1 : liftq n (ev2 F1 F2 a) (bdq F1 F2 x') - evB lev (c1 F1 F2) (c2 F1 F2) b (bdq F1 F2 x') =
      bdq F1 F2 (liftq n (LinearMap.ker π).subtype w') := by
    have := congrArg (liftq n (LinearMap.ker π).subtype) hw'
    rwa [map_sub, hι.lift_ev, hι.evC lev, hι.bd, hz'] at this

  let u : Cq n Y := liftq n (ev2 F1 F2 a) x' - evB lev (c1 F1 F2) (c2 F1 F2) b x' - liftq n (LinearMap.ker π).subtype w'
  have hx'U : SuppQ (inUL lev) x' := fun A h l hl => hS.1 l (hx'S A h l hl)
  obtain ⟨f1, f2, f3⟩ := evC_facts hR hlev hF b x' hx'U
  have hub : bdq F1 F2 u = 0 := by
    have cc := lift_bd_comm (hA Y F1 F2 hF).1 hx'S
    simp only [u, map_sub]
    rw [← cc, f3, e1, sub_self]
  have huD : DegQ (j + 1) u := by
    have d1 : liftq n (ev2 F1 F2 a) x' ∈ supSub Y (fun A => A.card = j + 1) := lift_mem _ hx'D
    have d2 : evB lev (c1 F1 F2) (c2 F1 F2) b x' ∈ supSub Y (fun A => A.card = j + 1) := f2 _ hx'D
    have d3 : liftq n (LinearMap.ker π).subtype w' ∈ supSub Y (fun A => A.card = j + 1) := lift_mem _ hw'D
    exact Submodule.sub_mem _ (Submodule.sub_mem _ d1 d2) d3
  have huS : SuppQ (inUL lev) u := by
    have d1 : liftq n (ev2 F1 F2 a) x' ∈ supSub Y (fun A => ∀ i ∈ A, inUL lev i) := lift_mem _ hx'U
    have d2 : evB lev (c1 F1 F2) (c2 F1 F2) b x' ∈ supSub Y (fun A => ∀ i ∈ A, inUL lev i) := f1
    have d3 : liftq n (LinearMap.ker π).subtype w' ∈ supSub Y (fun A => ∀ i ∈ A, inUL lev i) := lift_mem _ hw'S
    exact Submodule.sub_mem _ (Submodule.sub_mem _ d1 d2) d3
  obtain ⟨t, htS, htD, ht⟩ := hY j u huS huD hub
  refine ⟨liftq n π t, lift_mem π htS, lift_mem π htD, ?_⟩
  rw [← hm.bd, ht]
  have e0 : liftq n π (liftq n (LinearMap.ker π).subtype w') = 0 := by
    funext A
    exact (w' A).2
  simp only [u, map_sub, e0, sub_zero]
  rw [hm.lift_ev, hm.evC lev, hx'π]

theorem genCOU2_of (hR : LeviRel) : GenCOU2 := by
  intro n lev S a b hlev hS hA V _ _ E1 E2 hE j
  have key : ∀ j, ShiftAt n lev a b S j := by
    intro j
    induction j with
    | zero => exact shift_zero hA
    | succ j ih => exact shift_step hR hlev hS hA ih
  exact key j V E1 E2 hE

theorem genCOU2 : GenCOU2 := genCOU2_of GlobalTheory.CompanionTheory.PairMult.leviRel

end GlobalTheory.CompanionTheory.PairMult.COU
end
end

open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_multiplicity_generic_unitary : GlobalTheory.CompanionTheory.PairMult.GenCOU2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PairMult.COU.genCOU2
end
