import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapMemNonZeroDivisorsAdicCompletion

section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

section Lim

variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}

def ulim (s : ℕ → K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff n (s n)

theorem ulim_sub_dvd {s : ℕ → K⟦X⟧} (h : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ s (n + 1) - s n) (n : ℕ) :
    (X : K⟦X⟧) ^ (n + 1) ∣ ulim s - s n := by
  have key (m k : ℕ) : (X : K⟦X⟧) ^ (m + 1) ∣ s (m + k) - s m := by
    induction k with
    | zero => simp
    | succ k ih =>
      have := dvd_add ((pow_dvd_pow _ (by omega : m + 1 ≤ m + k + 1)).trans (h (m + k))) ih
      rwa [sub_add_sub_cancel] at this
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 hm)
  have := X_pow_dvd_iff.1 (key m k) m (Nat.lt_succ_self m)
  rw [map_sub] at this ⊢
  rw [ulim, coeff_mk, ← neg_sub, this, neg_zero]

variable (K a ι) in

def uPow (m : ℕ) : Submodule K⟦X⟧ (Vec K a ι) where
  carrier := {v | ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i}
  add_mem' hv hw τ i := dvd_add (hv τ i) (hw τ i)
  zero_mem' _ _ := dvd_zero _
  smul_mem' c _ hv τ i := (hv τ i).mul_left c

theorem mem_uPow {m : ℕ} {v : Vec K a ι} : v ∈ uPow K a ι m ↔ ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i :=
  Iff.rfl

theorem uPow_anti {m n : ℕ} (h : m ≤ n) : uPow K a ι n ≤ uPow K a ι m :=
  fun _ hv τ i => (pow_dvd_pow _ h).trans (hv τ i)

theorem eq_zero_of_mem_uPow {v : Vec K a ι} (h : ∀ m, v ∈ uPow K a ι (m + 1)) : v = 0 := by
  ext τ i n
  simpa using X_pow_dvd_iff.1 (h n τ i) n (Nat.lt_succ_self n)

theorem mem_uPow_one {v : Vec K a ι} : v ∈ uPow K a ι 1 ↔ red v = 0 := by
  simp [mem_uPow, X_dvd_iff, funext_iff]

theorem mem_uPow_iff_exists {m : ℕ} {v : Vec K a ι} :
    v ∈ uPow K a ι m ↔ ∃ w : Vec K a ι, v = (X : K⟦X⟧) ^ m • w := by
  constructor
  · intro h
    choose w hw using h
    exact ⟨w, funext fun τ => funext fun i => hw τ i⟩
  · rintro ⟨w, rfl⟩ τ i
    exact Dvd.intro _ rfl

theorem X_smul_mem_uPow (w : Vec K a ι) : (X : K⟦X⟧) • w ∈ uPow K a ι 1 :=
  mem_uPow_iff_exists.2 ⟨w, by simp⟩

theorem dvd_mulVec [Fintype ι] {c : K⟦X⟧} (Y : Matrix κ ι K⟦X⟧) {v : ι → K⟦X⟧} (hv : ∀ i, c ∣ v i)
    (j : κ) : c ∣ (Y *ᵥ v) j := Finset.dvd_sum fun i _ => (hv i).mul_left _

theorem X_pow_dvd_frob (l : ℕ) [Fact l.Prime] {m : ℕ} {f : K⟦X⟧} (h : (X : K⟦X⟧) ^ (m + 1) ∣ f) :
    (X : K⟦X⟧) ^ (m + 2) ∣ frob K l f := by
  have h1 := map_dvd (frob K l) h
  rw [map_pow, frob_X, ← pow_mul] at h1
  have := (Fact.out : l.Prime).two_le
  exact (pow_dvd_pow _ (by nlinarith)).trans h1

def geom (T : Module.End K (Vec K a ι)) : Module.End K (Vec K a ι) where
  toFun w τ i := ulim fun n => (∑ j ∈ Finset.range (n + 1), T ^ j) w τ i
  map_add' v w := by ext τ i n; simp [ulim, Finset.sum_add_distrib]
  map_smul' c w := by ext τ i n; simp [ulim, Finset.mul_sum]

def Raises (T : Module.End K (Vec K a ι)) : Prop :=
  ∀ m, ∀ v ∈ uPow K a ι (m + 1), T v ∈ uPow K a ι (m + 2)

theorem Raises.pow_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) : (T ^ n) w ∈ uPow K a ι (n + 1) := by
  induction n with
  | zero => exact hw
  | succ n ih => rw [pow_succ']; exact hT n _ ih

theorem geom_sub_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) :
    geom T w - (∑ j ∈ Finset.range n, T ^ j) w ∈ uPow K a ι (n + 1) := by
  have h : geom T w - (∑ j ∈ Finset.range (n + 1), T ^ j) w ∈ uPow K a ι (n + 1) := fun τ i =>
    ulim_sub_dvd (s := fun n => (∑ j ∈ Finset.range (n + 1), T ^ j) w τ i) (fun n => by
      rw [Finset.sum_range_succ _ (n + 1), LinearMap.add_apply, Pi.add_apply, Pi.add_apply,
        add_sub_cancel_left]
      exact uPow_anti n.succ.le_succ (hT.pow_mem hw (n + 1)) τ i) n
  have := add_mem h (hT.pow_mem hw n)
  rwa [Finset.sum_range_succ, LinearMap.add_apply, ← sub_sub, sub_add_cancel] at this

theorem geom_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) : geom T w ∈ uPow K a ι 1 := by
  simpa using geom_sub_mem hT hw 0

theorem geom_eq {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) : geom T w = w + T (geom T w) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_uPow fun m => uPow_anti (Nat.le_succ _) ?_
  have := sub_mem (geom_sub_mem hT hw (m + 1)) (hT m _ (geom_sub_mem hT hw m))
  convert this using 1
  simp only [Finset.sum_range_succ', pow_succ', ← Finset.mul_sum, LinearMap.add_apply,
    Module.End.mul_apply, map_sub, pow_zero, Module.End.one_apply]
  abel

def cst : (ZMod a → ι → K) →ₗ[K] Vec K a ι where
  toFun d τ i := C (d τ i)
  map_add' d d' := by ext τ i : 2; simp
  map_smul' c d := by ext τ i : 2; simp [smul_eq_C_mul]

@[simp] theorem cst_apply (d : ZMod a → ι → K) (τ : ZMod a) (i : ι) : cst d τ i = C (d τ i) := rfl

@[simp] theorem red_cst (d : ZMod a → ι → K) : red (cst d) = d := by ext τ i; simp

def derV : Module.End K (Vec K a ι) where
  toFun v τ i := PowerSeries.derivative K (v τ i)
  map_add' v w := by ext τ i : 2; simp
  map_smul' c v := by ext τ i : 2; simp

@[simp] theorem derV_apply (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    derV v τ i = PowerSeries.derivative K (v τ i) := rfl

def derTot (f : ZMod a → K⟦X⟧) : ZMod a → K⟦X⟧ := fun τ => PowerSeries.derivative K (f τ)

def NTot (f : ZMod a → K⟦X⟧) : ZMod a → K⟦X⟧ := fun τ => N K (f τ)

def bas [DecidableEq ι] (i : ι) : Vec K a ι := fun _ => Pi.single i 1

theorem eq_sum_bas [Fintype ι] [DecidableEq ι] (v : Vec K a ι) :
    v = ∑ i, (fun τ => v τ i) • (bas i : Vec K a ι) := by
  ext1 τ
  ext1 j
  simp [bas, Finset.sum_apply, Pi.single_apply]

theorem cst_single [DecidableEq ι] (i : ι) :
    cst (fun _ : ZMod a => (Pi.single i 1 : ι → K)) = bas i := by
  ext1 τ
  ext1 j
  simp only [bas, cst_apply, Pi.single_apply]
  split_ifs <;> simp

end Lim

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

namespace PhiMod

variable (P : PhiMod O K l e a ι)

theorem raises_phi : Raises P.phi := fun _ _ hv τ =>
  dvd_mulVec _ fun i => X_pow_dvd_frob l (hv (τ - 1) i)

theorem raises_smul_phi (c : K) : Raises (c • P.phi) := fun m v hv => by
  have := (uPow K a ι (m + 2)).smul_mem (C c) (P.raises_phi m v hv)
  convert this using 1
  ext τ i : 2
  simp [smul_eq_C_mul]

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in

theorem _root_.GlobalTheory.BK.Raises.eq_zero {T : Module.End K (Vec K a ι)} (hT : Raises T) {α : Type}
    {σ : α → α} (hσ : Function.Surjective σ) {δ : α → Vec K a ι} (h1 : ∀ x, δ x ∈ uPow K a ι 1)
    (h : ∀ x, δ (σ x) = T (δ x)) (x : α) : δ x = 0 := by
  refine eq_zero_of_mem_uPow fun m => ?_
  induction m generalizing x with
  | zero => exact h1 x
  | succ m ih =>
    obtain ⟨y, rfl⟩ := hσ x
    rw [h]
    exact hT m _ (ih y)

def xiSeq (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun Y τ => P.mx τ * (Y (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C)^[n]
    fun _ => 1

theorem xiSeq_zero (τ : ZMod a) : P.xiSeq 0 τ = 1 := rfl

theorem xiSeq_succ (n : ℕ) (τ : ZMod a) : P.xiSeq (n + 1) τ =
    P.mx τ * (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
  rw [xiSeq, Function.iterate_succ_apply']
  rfl

theorem xiSeq_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 1) ∣ P.xiSeq (n + 1) τ i j - P.xiSeq n τ i j := by
  induction n generalizing τ i j with
  | zero =>
    have h := congrFun (congrFun (P.matrix_mul_inv_const_eq_one τ) i) j
    rw [zero_add, pow_one, X_dvd_iff]
    simp only [xiSeq_succ, xiSeq_zero, Matrix.map_one _ (map_zero (frob K l)) (map_one _), Matrix.mul_one, map_sub]
    rw [Matrix.mul_apply] at h ⊢
    simp only [map_sum, map_mul, Matrix.map_apply, constantCoeff_C, mx0] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [← Matrix.sub_apply, xiSeq_succ P (n + 1), xiSeq_succ P n τ, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
    rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
    rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub]
    exact X_pow_dvd_frob l (ih (τ - 1) m k)

def xiMat (τ : ZMod a) : Matrix ι ι K⟦X⟧ := Matrix.of fun i j => ulim fun n => P.xiSeq n τ i j

theorem xiMat_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 1) ∣ P.xiMat τ i j - P.xiSeq n τ i j :=
  ulim_sub_dvd (s := fun n => P.xiSeq n τ i j) (fun n => P.xiSeq_dvd n τ i j) n

theorem xiMat_map_constantCoeff (τ : ZMod a) : (P.xiMat τ).map constantCoeff = 1 := by
  ext i j
  have := P.xiMat_sub_dvd 0 τ i j
  rw [zero_add, pow_one, X_dvd_iff, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, xiSeq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mx_mul_xiMat (τ : ZMod a) :
    P.mx τ * (P.xiMat (τ - 1)).map (frob K l) = P.xiMat τ * (P.mx0 τ).map C := by
  have h : P.mx τ * (P.xiMat (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C =
      P.xiMat τ := by
    ext i j n
    have h1 : (X : K⟦X⟧) ^ (n + 2) ∣ (P.mx τ * (P.xiMat (τ - 1)).map (frob K l) *
        ((P.mxInv τ).map constantCoeff).map C) i j - P.xiSeq (n + 1) τ i j := by
      rw [← Matrix.sub_apply, xiSeq_succ, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_apply]
      refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
      rw [Matrix.mul_apply]
      refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
      rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact X_pow_dvd_frob l (P.xiMat_sub_dvd n (τ - 1) m k)
    have h2 := X_pow_dvd_iff.1 (dvd_sub h1 (P.xiMat_sub_dvd (n + 1) τ i j)) n (by omega)
    rwa [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h2
  rw [← h, Matrix.mul_assoc _ _ ((P.mx0 τ).map C), ← Matrix.map_mul, inv_const_mul_matrix_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

theorem isUnit_det_xiMat (τ : ZMod a) : IsUnit (P.xiMat τ).det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, xiMat_map_constantCoeff]
  simp

def xiExt : Vec K a ι ≃ₗ[K] Vec K a ι where
  toFun w τ := P.xiMat τ *ᵥ w τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]
  invFun v τ := (P.xiMat τ)⁻¹ *ᵥ v τ
  left_inv w := by ext1 τ; simp [Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  right_inv w := by ext1 τ; simp [Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)]

theorem xiExt_apply (w : Vec K a ι) (τ : ZMod a) : P.xiExt w τ = P.xiMat τ *ᵥ w τ := rfl

theorem xiExt_smul_tot (f : ZMod a → K⟦X⟧) (w : Vec K a ι) : P.xiExt (f • w) = f • P.xiExt w :=
  funext fun τ => Matrix.mulVec_smul _ (f τ) (w τ)

def xi : P.D →ₗ[K] Vec K a ι := P.xiExt.toLinearMap ∘ₗ cst

theorem xi_apply (d : P.D) : P.xi d = P.xiExt (cst d) := rfl

theorem red_xiExt (w : Vec K a ι) : red (P.xiExt w) = red w := by
  ext1 τ
  rw [red_apply, xiExt_apply, powerSeriesVecReduceModU_mulVec, xiMat_map_constantCoeff, Matrix.one_mulVec, red_apply]

@[simp] theorem red_xi (d : P.D) : red (P.xi d) = d := by rw [xi_apply, red_xiExt, red_cst]

theorem phi_xiExt (w : Vec K a ι) :
    P.phi (P.xiExt w) = P.xiExt fun τ => (P.mx0 τ).map C *ᵥ frobV l (w (τ - 1)) := by
  ext1 τ
  rw [phi_apply, xiExt_apply, xiExt_apply, Matrix.mulVec_mulVec, ← mx_mul_xiMat,
    ← Matrix.mulVec_mulVec]
  congr 1
  ext1 i
  exact RingHom.map_mulVec (frob K l).toRingHom _ _ i

theorem phi_xi (d : P.D) : P.phi (P.xi d) = P.xi (P.phiD d) := by
  rw [xi_apply, phi_xiExt, xi_apply]
  congr 1
  ext τ i : 2
  simp [phiD_apply, Matrix.mulVec, dotProduct]

variable {P} in

theorem map_xi {Q : PhiMod O K l e a κ} {g : Vec K a ι → Vec K a κ}
    (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (d : P.D) : g (P.xi d) = Q.xi (red (g (P.xi d))) := by
  rw [← sub_eq_zero]
  refine Q.raises_phi.eq_zero (σ := P.phiD) P.phiD.surjective
    (δ := fun d => g (P.xi d) - Q.xi (red (g (P.xi d)))) (fun d => ?_) (fun d => ?_) d
  · rw [mem_uPow_one, map_sub, red_xi, sub_self]
  · simp only [← phi_xi, hg, red_phi, map_sub]

theorem xi_unique {s : P.D → Vec K a ι} (h0 : ∀ d, red (s d) = d)
    (h : ∀ d, P.phi (s d) = s (P.phiD d)) (d : P.D) : s d = P.xi d := by
  rw [← sub_eq_zero]
  refine P.raises_phi.eq_zero (σ := P.phiD) P.phiD.surjective
    (δ := fun d => s d - P.xi d) (fun d => ?_) (fun d => ?_) d
  · rw [mem_uPow_one, map_sub, red_xi, h0, sub_self]
  · simp only [← phi_xi, ← h, map_sub]

def nabla : Module.End K (Vec K a ι) := P.xiExt.conj derV

def conn : Module.End K (Vec K a ι) where
  toFun v := (X : K⟦X⟧) • P.nabla v
  map_add' v w := by rw [map_add, smul_add]
  map_smul' c v := by rw [map_smul, smul_comm]; rfl

theorem conn_apply (v : Vec K a ι) : P.conn v = (X : K⟦X⟧) • P.nabla v := rfl

theorem nabla_xiExt (w : Vec K a ι) : P.nabla (P.xiExt w) = P.xiExt (derV w) := by
  simp [nabla, LinearEquiv.conj_apply]

theorem conn_xiExt (w : Vec K a ι) : P.conn (P.xiExt w) = P.xiExt fun τ i => N K (w τ i) := by
  rw [conn_apply, nabla_xiExt]
  exact (P.xiExt_smul_tot (fun _ => X) _).symm

@[simp] theorem nabla_xi (d : P.D) : P.nabla (P.xi d) = 0 := by
  rw [xi_apply, nabla_xiExt, ← map_zero P.xiExt]
  congr 1
  ext τ i : 2
  simp

@[simp] theorem conn_xi (d : P.D) : P.conn (P.xi d) = 0 := by rw [conn_apply, nabla_xi, smul_zero]

theorem nabla_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.nabla (f • v) = derTot f • v + f • P.nabla v := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [← xiExt_smul_tot, nabla_xiExt, nabla_xiExt, ← xiExt_smul_tot, ← xiExt_smul_tot, ← map_add]
  congr 1
  ext τ i : 2
  simp [derTot, add_comm, mul_comm]

theorem conn_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.conn (f • v) = NTot f • v + f • P.conn v := by
  rw [conn_apply, nabla_smul_tot, conn_apply]
  ext τ i : 2
  simp only [derTot, NTot, N_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', smul_eq_mul]
  ring

theorem conn_smul (f : K⟦X⟧) (v : Vec K a ι) : P.conn (f • v) = N K f • v + f • P.conn v :=
  P.conn_smul_tot (fun _ => f) v

theorem conn_mem_uPow (v : Vec K a ι) : P.conn v ∈ uPow K a ι 1 := X_smul_mem_uPow _

theorem conn_phi (v : Vec K a ι) : P.conn (P.phi v) = (l : K) • P.phi (P.conn v) := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [phi_xiExt, conn_xiExt, conn_xiExt, phi_xiExt, ← map_smul]
  congr 1
  ext τ i : 2
  simp only [Matrix.mulVec, dotProduct, map_sum, Pi.smul_apply, Finset.smul_sum, frobV_apply,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, N_frob, smul_comm, smul_eq_C_mul (a := (l : K)),
    map_natCast]

variable {P} in

theorem map_conn {Q : PhiMod O K l e a κ} (g : Vec K a ι →+ Vec K a κ)
    (σ : (ZMod a → K⟦X⟧) → ZMod a → K⟦X⟧) (hσ : ∀ f, σ (NTot f) = NTot (σ f))
    (hs : ∀ f v, g (f • v) = σ f • g v) (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (v : Vec K a ι) :
    g (P.conn v) = Q.conn (g v) := by
  obtain ⟨w, rfl⟩ := P.xiExt.surjective v
  rw [eq_sum_bas w]
  simp only [map_sum, xiExt_smul_tot, ← cst_single, ← xi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conn_smul_tot, conn_xi, smul_zero, add_zero, hs, hs, conn_smul_tot, map_xi hg, conn_xi,
    smul_zero, add_zero, hσ]

end PhiMod

namespace PhiMod

variable (P : PhiMod O K l e a ι)

omit [Fact l.Prime] in
theorem bas_mem_M (i : ι) : bas i ∈ P.M := mem_tot.2 fun _ j => by
  simp only [bas, Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem phi_bas (i : ι) (τ : ZMod a) : P.phi (bas i) τ = (P.mx τ).col i := by
  have : frobV l (Pi.single i (1 : K⟦X⟧)) = Pi.single i 1 := by
    ext1 j
    rw [frobV_apply, Pi.single_apply]
    split_ifs <;> simp
  simp [phi_apply, bas, this]

theorem eq_sum_phi_bas (v : Vec K a ι) :
    v = ∑ i, (fun τ => (P.mxInv τ *ᵥ v τ) i) • P.phi (bas i) := by
  ext1 τ
  conv_lhs => rw [← Matrix.one_mulVec (v τ), ← P.mx_mul_mxInv τ, ← Matrix.mulVec_mulVec]
  ext1 j
  simp only [Finset.sum_apply, Pi.smul_apply', phi_bas, Pi.smul_apply, Matrix.col_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fact l.Prime] in
theorem smul_tot_mem_Mext {B : Subalgebra O K⟦X⟧} {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B)
    {v : Vec K a ι} (hv : v ∈ P.Mext B) : f • v ∈ P.Mext B :=
  mem_tot.2 fun τ i => B.mul_mem (hf τ) (mem_tot.1 hv τ i)

omit [Fact l.Prime] in
theorem smul_tot_mem_ext {B : Subalgebra O K⟦X⟧} {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B)
    {v : Vec K a ι} (hv : v ∈ P.ext B) : f • v ∈ P.ext B :=
  mem_tot.2 fun τ => (P.extc B τ).smul_mem ⟨f τ, hf τ⟩ (mem_tot.1 hv τ)

omit [Fact l.Prime] in
theorem Mext_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.Mext B) :
    v ∈ P.Mext B' := mem_tot.2 fun τ i => h (mem_tot.1 hv τ i)

omit [Fact l.Prime] in
theorem ext_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.ext B) :
    v ∈ P.ext B' := mem_tot.2 fun τ => P.mem_extc_iff.2 fun i =>
      h (P.mem_extc_iff.1 (mem_tot.1 hv τ) i)

def lphi : Module.End K (Vec K a ι) := (l : K) • P.phi

theorem lphi_apply (v : Vec K a ι) : P.lphi v = (l : K) • P.phi v := rfl

theorem raises_lphi : Raises P.lphi := P.raises_smul_phi l

def zeta : Module.End K (Vec K a ι) := -(geom P.lphi * P.lphi * P.conn)

theorem lphi_conn_mem (y : Vec K a ι) : P.lphi (P.conn y) ∈ uPow K a ι 1 :=
  uPow_anti one_le_two (P.raises_lphi 0 _ (P.conn_mem_uPow y))

theorem zeta_mem_uPow (y : Vec K a ι) : P.zeta y ∈ uPow K a ι 1 :=
  neg_mem (geom_mem P.raises_lphi (P.lphi_conn_mem y))

theorem zeta_eq (y : Vec K a ι) : P.zeta y = P.lphi (P.zeta y - P.conn y) := by
  have h := geom_eq P.raises_lphi (P.lphi_conn_mem y)
  have h' : P.zeta y = -geom P.lphi (P.lphi (P.conn y)) := rfl
  rw [map_sub, h', map_neg]
  linear_combination (exp := 1) -h

theorem zeta_unique {y z : Vec K a ι} (h1 : z ∈ uPow K a ι 1) (h : z = P.lphi (z - P.conn y)) :
    z = P.zeta y := by
  rw [← sub_eq_zero]
  refine P.raises_lphi.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ => z - P.zeta y) (fun _ => sub_mem h1 (P.zeta_mem_uPow y)) (fun _ => ?_) ()
  conv_lhs => rw [h, zeta_eq, ← map_sub, sub_sub_sub_cancel_right]

theorem zeta_add_sum_mem (y : Vec K a ι) (m : ℕ) :
    P.zeta y + ∑ n ∈ Finset.range m, (P.lphi ^ (n + 1)) (P.conn y) ∈ uPow K a ι (m + 1) := by
  have h := neg_mem (geom_sub_mem P.raises_lphi (P.lphi_conn_mem y) m)
  rw [neg_sub, sub_eq_neg_add, LinearMap.sum_apply] at h
  exact h

theorem zeta_phi_sub (m : Vec K a ι) : P.zeta (P.phi m - m) = P.conn (P.phi m) :=
  (P.zeta_unique (P.conn_mem_uPow _) (by
    rw [map_sub P.conn, sub_sub_cancel, lphi_apply, conn_phi])).symm

variable {P} in

theorem map_zeta {Q : PhiMod O K l e a κ} (g : Vec K a ι →ₗ[K] Vec K a κ)
    (h1 : ∀ v ∈ uPow K a ι 1, g v ∈ uPow K a κ 1) (hg : ∀ v, g (P.phi v) = Q.phi (g v))
    (hN : ∀ v, g (P.conn v) = Q.conn (g v)) (y : Vec K a ι) : g (P.zeta y) = Q.zeta (g y) :=
  Q.zeta_unique (h1 _ (P.zeta_mem_uPow y)) (by
    conv_lhs => rw [zeta_eq, lphi_apply, map_smul, hg, map_sub, hN]
    rfl)

end PhiMod

namespace Hom

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)

theorem app_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : F.app (f • v) = f • F.app v :=
  funext fun τ => Matrix.mulVec_smul _ (f τ) (v τ)

theorem app_mem_uPow {m : ℕ} {v : Vec K a ι} (hv : v ∈ uPow K a ι m) : F.app v ∈ uPow K a κ m :=
  fun τ => dvd_mulVec _ (hv τ)

theorem app_xi (d : P.D) : F.app (P.xi d) = Q.xi (F.onD d) := by
  rw [PhiMod.map_xi F.app_phi, red_app, PhiMod.red_xi]

theorem app_conn (v : Vec K a ι) : F.app (P.conn v) = Q.conn (F.app v) :=
  PhiMod.map_conn F.app.toAddMonoidHom id (fun _ => rfl) F.app_smul_tot F.app_phi v

theorem app_nabla (v : Vec K a ι) : F.app (P.nabla v) = Q.nabla (F.app v) := by
  have h := F.app_conn v
  rw [PhiMod.conn_apply, PhiMod.conn_apply, map_smul] at h
  exact smul_right_injective _ X_ne_zero h

theorem app_zeta (y : Vec K a ι) : F.app (P.zeta y) = Q.zeta (F.app y) :=
  PhiMod.map_zeta (F.app.restrictScalars K) (fun _ => F.app_mem_uPow) F.app_phi F.app_conn y

end Hom

section Plus

def join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) : Vec K a (ι ⊕ Unit) :=
  fun τ => Sum.elim (v τ) fun _ => f τ

def xVec : Vec K a (ι ⊕ Unit) := join 0 1

namespace PhiMod

variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))

omit [Fact l.Prime] in

def plus : PhiMod O K l e a (ι ⊕ Unit) :=
  ofMatrix (fun τ => Matrix.fromBlocks (P.mx τ) (Matrix.replicateCol Unit (y τ)) 0 1)
    (fun τ => Matrix.fromBlocks (P.mxInv τ) (Matrix.replicateCol Unit (-(P.mxInv τ *ᵥ y τ))) 0 1)
    (by
      rintro τ (i | i) (j | j)
      exacts [P.mx_mem τ i j, mem_tot.1 hy τ i, zero_mem _, one_mem _])
    (by
      rintro τ (i | i) (j | j)
      exacts [P.mxInv_mem τ i j, neg_mem (Subalgebra.sum_mem _ fun k _ =>
        mul_mem (P.mxInv_mem τ i k) (mem_tot.1 hy τ k)), zero_mem _, one_mem _])
    fun τ => by
      rw [Matrix.fromBlocks_multiply, ← Matrix.replicateCol_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, mx_mul_mxInv]
      simp [← Matrix.replicateCol_add]

theorem plus_phi_join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plus hy).phi (join v f) = join (P.phi v + frobTot K a l f • y) (frobTot K a l f) := by
  ext1 τ
  rw [phi_apply, plus, mx_ofMatrix]
  ext1 i
  rcases i with i | i <;>
    simp [join, Matrix.mulVec, dotProduct, phi_apply, Fintype.sum_sum_type, mul_comm]

def plusInl : Hom P (P.plus hy) where
  mat _ := Matrix.fromRows 1 0
  mem := by
    rintro τ (i | i) j
    · rw [Matrix.fromRows_apply_inl, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · exact zero_mem _
  comm τ := by
    rw [plus, mx_ofMatrix, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    simp

theorem plusInl_app (v : Vec K a ι) : (P.plusInl hy).app v = join v 0 := by
  ext1 τ
  rw [Hom.app_apply, plusInl]
  ext1 i
  rcases i with i | i <;> simp [join]

theorem phi_extension_generator_eq_add : (P.plus hy).phi xVec = xVec + (P.plusInl hy).app y := by
  rw [xVec, plus_phi_join, plusInl_app]
  ext1 τ
  ext1 i
  rcases i with i | i <;> simp [join]

theorem conn_phi_extension_generator_eq_zeta : (P.plus hy).conn ((P.plus hy).phi xVec) = (P.plusInl hy).app (P.zeta y) := by
  rw [Hom.app_zeta, ← zeta_phi_sub, phi_extension_generator_eq_add, add_sub_cancel_left]

theorem plus_conn_xVec_eq : (P.plus hy).conn xVec = (P.plusInl hy).app (P.zeta y - P.conn y) := by
  rw [map_sub, ← conn_phi_extension_generator_eq_zeta, phi_extension_generator_eq_add, map_add, Hom.app_conn, add_sub_cancel_right]

variable [NormedAlgebra ℚ_[l] K] [NeZero e]

def plusProj : Hom (P.plus hy) (rankOne O K l e fun _ => 0) where
  mat _ := Matrix.fromCols 0 1
  mem := by
    rintro τ i (j | j)
    exacts [zero_mem _, one_mem _]
  comm τ := by
    have h : (rankOne O K l e fun _ : ZMod a => 0).mx τ = 1 := by
      ext1 i j
      exact (mx_rankOne (n := 0) rfl).trans (pow_zero _)
    rw [h, plus, mx_ofMatrix, Matrix.fromCols_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.fromCols_mul_fromBlocks]
    simp

theorem plusProj_app (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plusProj hy).app (join v f) = fun τ _ => f τ := by
  ext1 τ
  rw [Hom.app_apply, plusProj]
  ext1 i
  simp [join]

end PhiMod

end Plus

end GlobalTheory.BK
end
end

section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

class TameDescentExponentData (K : Type) [NormedField K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] :
    Prop where
  succ_eq : e + 1 = l ^ a
  not_dvd : ¬ l ∣ a
  finite : FiniteDimensional ℚ_[l] K
  prim : ∃ ζ : K, IsPrimitiveRoot ζ e

instance instTameDescentExponentDataPadicThree : TameDescentExponentData ℚ_[3] 3 2 1 where
  succ_eq := rfl
  not_dvd := by decide
  finite := inferInstance
  prim := ⟨-1, IsPrimitiveRoot.neg_one 0 (by decide)⟩

section Group

variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]

omit [NeZero a] in
theorem pow_pow_mod (ζ : rootsOfUnity e K) (n : ℕ) : ζ ^ l ^ (n % a) = ζ ^ l ^ n := by
  have h1 : ζ ^ e = 1 := Subtype.ext ζ.2
  have h2 (k : ℕ) : ζ ^ (l ^ a) ^ k = ζ := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, ← TameDescentExponentData.succ_eq (K := K) (e := e), pow_succ, h1, one_mul]
  conv_rhs => rw [← Nat.div_add_mod n a, pow_add, pow_mul l, pow_mul, h2]

def powL (s : ZMod a) : rootsOfUnity e K →* rootsOfUnity e K := powMonoidHom (l ^ s.val)

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] in
theorem powL_apply (s : ZMod a) (ζ : rootsOfUnity e K) : powL l s ζ = ζ ^ l ^ s.val := rfl

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] in
@[simp] theorem powL_zero (ζ : rootsOfUnity e K) : powL l (0 : ZMod a) ζ = ζ := by simp [powL_apply]

theorem powL_add (s t : ZMod a) (ζ : rootsOfUnity e K) :
    powL l (s + t) ζ = powL l s (powL l t ζ) := by
  rw [powL_apply, powL_apply, powL_apply, ZMod.val_add, pow_pow_mod l, ← pow_mul, ← pow_add, add_comm]

omit [NeZero a] in
theorem powL_one (ζ : rootsOfUnity e K) : powL l (1 : ZMod a) ζ = ζ ^ l := by
  rw [powL_apply, ZMod.val_one_eq_one_mod, pow_pow_mod l, pow_one]

variable (K e a) in

def frobAut : Multiplicative (ZMod a) →* MulAut (rootsOfUnity e K) where
  toFun s :=
    { powL l s.toAdd with
      invFun := powL l (-s.toAdd)
      left_inv := fun ζ => ((powL_add l _ _ ζ).symm.trans (by simp))
      right_inv := fun ζ => ((powL_add l _ _ ζ).symm.trans (by simp)) }
  map_one' := MulEquiv.ext fun ζ => powL_zero l ζ
  map_mul' s t := MulEquiv.ext fun ζ => powL_add l _ _ ζ

variable (K e a) in

abbrev TameGal : Type := rootsOfUnity e K ⋊[frobAut K l e a] Multiplicative (ZMod a)

namespace TameGal

variable {l}

abbrev inertia : rootsOfUnity e K →* TameGal K l e a := SemidirectProduct.inl

abbrev fr : TameGal K l e a := SemidirectProduct.inr (Multiplicative.ofAdd 1)

def shift (g : TameGal K l e a) : ZMod a := g.right.toAdd

def root (g : TameGal K l e a) (τ : ZMod a) : K := ((powL l (-τ) g.left : rootsOfUnity e K) : Kˣ)

@[simp] theorem shift_one : shift (1 : TameGal K l e a) = 0 := rfl

theorem shift_mul (g h : TameGal K l e a) : shift (g * h) = shift g + shift h := rfl

@[simp] theorem shift_inertia (ζ : rootsOfUnity e K) : shift (inertia ζ : TameGal K l e a) = 0 := rfl

@[simp] theorem shift_fr : shift (fr : TameGal K l e a) = 1 := rfl

@[simp] theorem root_one (τ : ZMod a) : root (1 : TameGal K l e a) τ = 1 := by simp [root]

@[simp] theorem root_fr (τ : ZMod a) : root (fr : TameGal K l e a) τ = 1 := by simp [root]

@[simp] theorem root_inertia_zero (ζ : rootsOfUnity e K) :
    root (inertia ζ : TameGal K l e a) 0 = (ζ : Kˣ) := by simp [root]

theorem root_mul (g h : TameGal K l e a) (τ : ZMod a) :
    root (g * h) τ = root g τ * root h (τ - shift g) := by
  have : powL l (-τ) (g * h).left = powL l (-τ) g.left * powL l (-(τ - shift g)) h.left := by
    rw [SemidirectProduct.mul_left, map_mul, neg_sub', sub_neg_eq_add, powL_add]
    rfl
  rw [root, this]
  simp [root]

theorem root_sub_one (g : TameGal K l e a) (τ : ZMod a) : root g (τ - 1) = root g τ ^ l := by
  rw [root, neg_sub, sub_eq_add_neg, powL_add, powL_one]
  simp [root]

theorem root_pow (g : TameGal K l e a) (τ : ZMod a) : root g τ ^ e = 1 :=
  (mem_rootsOfUnity' _ _).1 (powL l (-τ) g.left).2

theorem fr_mul_inertia (ζ : rootsOfUnity e K) :
    (fr : TameGal K l e a) * inertia ζ = inertia (ζ ^ l) * fr := by
  ext1
  · simpa [-map_pow, frobAut] using powL_one (a := a) l ζ
  · simp [-map_pow]

theorem root_ne_zero (g : TameGal K l e a) (τ : ZMod a) : root g τ ≠ 0 := Units.ne_zero _

variable [NeZero e]

theorem norm_root (g : TameGal K l e a) (τ : ZMod a) : ‖root g τ‖ = 1 := by
  have h := congrArg norm (g.root_pow τ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h

instance : Finite (TameGal K l e a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem card : Nat.card (TameGal K l e a) = e * a := by
  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := K) (l := l) (e := e) (a := a)
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    hζ.card_rootsOfUnity, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem not_dvd_card : ¬ l ∣ Nat.card (TameGal K l e a) := by
  rw [card, (Fact.out : l.Prime).dvd_mul, not_or]
  refine ⟨fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ?_), TameDescentExponentData.not_dvd K e⟩
  refine (Nat.dvd_add_right h).1 ?_
  rw [TameDescentExponentData.succ_eq (K := K) (l := l) (a := a)]
  exact dvd_pow_self l (NeZero.ne a)

end TameGal

variable {l}

def ringAct : TameGal K l e a →* ((ZMod a → K⟦X⟧) →ₐ[K] (ZMod a → K⟦X⟧)) where
  toFun g :=
    { toFun := fun f τ => rescale (g.root τ) (f (τ - g.shift))
      map_one' := by ext1; simp
      map_mul' := fun f f' => by ext1; simp
      map_zero' := by ext1; simp
      map_add' := fun f f' => by ext1; simp
      commutes' := fun c => by
        ext τ n
        simp only [Pi.algebraMap_apply, PowerSeries.algebraMap_apply, coeff_rescale, coeff_C]
        split_ifs with h <;> simp [h] }
  map_one' := by ext f τ : 2; simp
  map_mul' g h := by
    ext f τ : 2
    simp [TameGal.root_mul, TameGal.shift_mul, rescale_rescale, sub_sub, mul_comm]

theorem ringAct_apply (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) (τ : ZMod a) :
    ringAct g f τ = rescale (g.root τ) (f (τ - g.shift)) := rfl

theorem ringAct_frobTot (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) :
    ringAct g (frobTot K a l f) = frobTot K a l (ringAct g f) := by
  ext τ n
  rw [ringAct_apply, frobTot_apply, frobTot_apply, ringAct_apply, coeff_rescale, coeff_frob,
    coeff_frob, coeff_rescale, TameGal.root_sub_one, sub_right_comm]
  split_ifs with h
  · rw [← pow_mul, Nat.mul_div_cancel' h]
  · simp

theorem ringAct_NTot (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) :
    ringAct g (NTot f) = NTot (ringAct g f) := by
  ext τ n
  simp only [ringAct_apply, NTot, coeff_rescale, coeff_N]
  ring

theorem ringAct_X (g : TameGal K l e a) :
    ringAct g (fun _ => X) = fun τ => C (g.root τ) * X := funext fun _ => rescale_X _

theorem ringAct_X_pow (g : TameGal K l e a) : ringAct g (fun _ => X ^ e) = fun _ => X ^ e := by
  ext1 τ
  rw [ringAct_apply, map_pow, rescale_X, mul_pow, ← map_pow, g.root_pow, map_one, one_mul]

theorem ringAct_E (g : TameGal K l e a) : ringAct g (fun _ => E K l e) = fun _ => E K l e := by
  ext1 τ
  have := congrFun (ringAct_X_pow g) τ
  rw [ringAct_apply] at this ⊢
  rw [E, map_add, this, map_natCast]

end Group

section Join

variable {K : Type} [NormedField K] {a : ℕ} {ι : Type}

omit [NormedField K] in
theorem join_eta (w : Vec K a (ι ⊕ Unit)) :
    join (fun τ i => w τ (.inl i)) (fun τ => w τ (.inr ())) = w := by
  ext τ (i | i) : 2 <;> rfl

theorem join_add (v v' : Vec K a ι) (f f' : ZMod a → K⟦X⟧) :
    join (v + v') (f + f') = join v f + join v' f' := by
  ext τ (i | i) : 2 <;> rfl

theorem join_smul (c : K) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    join (c • v) (c • f) = c • join v f := by
  ext τ (i | i) : 2 <;> rfl

theorem join_smul_tot (c : ZMod a → K⟦X⟧) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    join (c • v) (c * f) = c • join v f := by
  ext τ (i | i) : 2 <;> rfl

theorem PhiMod.join_mem_Mext {O : Type} [CommRing O] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) {B : Subalgebra O K⟦X⟧} {v : Vec K a ι}
    {f : ZMod a → K⟦X⟧} : join v f ∈ (P.plus hy).Mext B ↔ v ∈ P.Mext B ∧ ∀ τ, f τ ∈ B :=
  ⟨fun h => ⟨mem_tot.2 fun τ i => mem_tot.1 h τ (.inl i), fun τ => mem_tot.1 h τ (.inr ())⟩,
    fun h => mem_tot.2 fun τ i => by
      rcases i with i | i
      exacts [mem_tot.1 h.1 τ i, h.2 τ]⟩

end Join

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Rot

def Rot (e : ℕ) (B : Subalgebra O K⟦X⟧) : Prop :=
  ∀ c : K, c ^ e = 1 → ∀ f ∈ B, rescale c f ∈ B

omit [IsUltrametricDist K] in
theorem norm_coeff_rescale [NeZero e] {c : K} (hc : c ^ e = 1) (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (rescale c f)‖ = ‖coeff n f‖ := by
  have h := congrArg norm hc
  rw [norm_pow, norm_one] at h
  rw [coeff_rescale, norm_mul, norm_pow,
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h, one_pow, one_mul]

theorem rot_A [NeZero e] : Rot e (A O K) := fun _ hc f hf n =>
  (norm_coeff_rescale hc f n).trans_le (hf n)

theorem rot_S [NeZero e] : Rot e (S O K e) := fun _ hc f hf => by
  simpa only [mem_S, norm_coeff_rescale hc] using hf

theorem rot_R [NeZero e] (k : ℝ) : Rot e (R O K l k) := fun _ hc f hf => by
  simpa only [mem_R, norm_coeff_rescale hc] using hf

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem Rot.invL {B : Subalgebra O K⟦X⟧} (h : Rot e B) : Rot e (invL l B) := by
  rintro c hc f ⟨n, hn⟩
  exact ⟨n, by simpa using h c hc _ hn⟩

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem Rot.invE {B : Subalgebra O K⟦X⟧} [HasU B] (h : Rot e B) : Rot e (invE l e B) := by
  rintro c hc f ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have := h c hc _ hn
  rwa [map_mul, map_pow, coe_EIn, E, map_add, map_pow, rescale_X, mul_pow, ← map_pow, hc, map_one,
    one_mul, map_natCast] at this

end Rot

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

omit [IsUltrametricDist K] [IsUnitBall O K] in
theorem Rot.ringAct_mem {B : Subalgebra O K⟦X⟧} (h : Rot e B) (g : TameGal K l e a)
    {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B) (τ : ZMod a) : ringAct g f τ ∈ B :=
  h _ (g.root_pow τ) _ (hf _)

structure Descent (P : PhiMod O K l e a ι) where

  act : Representation K (TameGal K l e a) (Vec K a ι)
  act_smul_tot : ∀ g (f : ZMod a → K⟦X⟧) v, act g (f • v) = ringAct g f • act g v
  act_mem_M : ∀ g, ∀ v ∈ P.M, act g v ∈ P.M
  act_phi : ∀ g v, act g (P.phi v) = P.phi (act g v)

namespace Descent

def matAct (g : TameGal K l e a) (G : ZMod a → Matrix ι ι K⟦X⟧) : Module.End K (Vec K a ι) where
  toFun v τ := G τ *ᵥ fun i => rescale (g.root τ) (v (τ - g.shift) i)
  map_add' v w := by
    ext1 τ
    refine Eq.trans ?_ (Matrix.mulVec_add _ _ _)
    congr 1
    ext1 i
    simp
  map_smul' c v := by
    ext1 τ
    refine Eq.trans ?_
      (Matrix.mulVec_smul (G τ) c fun i => rescale (g.root τ) (v (τ - g.shift) i))
    congr 1
    ext1 i
    exact congrFun (map_smul (ringAct g) c fun σ => v σ i) τ

omit [IsUltrametricDist K] [DecidableEq ι] in
theorem matAct_apply (g : TameGal K l e a) (G : ZMod a → Matrix ι ι K⟦X⟧) (v : Vec K a ι)
    (τ : ZMod a) :
    matAct g G v τ = G τ *ᵥ fun i => rescale (g.root τ) (v (τ - g.shift) i) := rfl

def ofMatrix (P : PhiMod O K l e a ι) (G : TameGal K l e a → ZMod a → Matrix ι ι K⟦X⟧)
    (mem : ∀ g τ i j, G g τ i j ∈ A O K) (one : ∀ τ, G 1 τ = 1)
    (mul : ∀ g h τ, G (g * h) τ = G g τ * (G h (τ - g.shift)).map (rescale (g.root τ)))
    (comm : ∀ g τ, G g τ * (P.mx (τ - g.shift)).map (rescale (g.root τ)) =
      P.mx τ * (G g (τ - 1)).map (frob K l)) [NeZero e] : Descent P where
  act :=
    { toFun := fun g => matAct g (G g)
      map_one' := by
        refine LinearMap.ext fun v => funext fun τ => ?_
        simp [one, matAct_apply]
      map_mul' := fun g h => by
        refine LinearMap.ext fun v => funext fun τ => ?_
        rw [Module.End.mul_apply, matAct_apply, matAct_apply, matAct_apply, mul,
          ← Matrix.mulVec_mulVec]
        congr 1
        ext1 i
        refine Eq.trans ?_ (RingHom.map_mulVec (rescale (g.root τ)) _ _ i).symm
        congr 1
        ext1 j
        simp [TameGal.root_mul, TameGal.shift_mul, rescale_rescale, sub_sub, mul_comm] }
  act_smul_tot g f v := by
    ext1 τ
    change matAct g (G g) (f • v) τ = ringAct g f τ • matAct g (G g) v τ
    rw [matAct_apply, matAct_apply, ← Matrix.mulVec_smul]
    congr 1
    ext1 i
    simp [ringAct_apply]
  act_mem_M g v hv := mem_tot.2 fun τ i => by
    change (matAct g (G g) v τ) i ∈ A O K
    rw [matAct_apply]
    exact Subalgebra.sum_mem _ fun j _ =>
      mul_mem (mem g τ i j) (rot_A _ (g.root_pow τ) _ (mem_tot.1 hv _ j))
  act_phi g v := by
    ext1 τ
    have h1 : (fun i => rescale (g.root τ) (P.phi v (τ - g.shift) i)) =
        (P.mx (τ - g.shift)).map (rescale (g.root τ)) *ᵥ
          fun i => frob K l (ringAct g (fun σ => v σ i) (τ - 1)) := funext fun i => by
      refine (RingHom.map_mulVec (rescale (g.root τ)) _ _ i).trans ?_
      congr 1
      ext1 j
      exact congrFun (ringAct_frobTot g fun σ => v σ j) τ
    change matAct g (G g) (P.phi v) τ = P.phi (matAct g (G g) v) τ
    rw [matAct_apply, h1, Matrix.mulVec_mulVec, comm, ← Matrix.mulVec_mulVec, P.phi_apply,
      matAct_apply]
    congr 1
    ext1 i
    exact (RingHom.map_mulVec (frob K l).toRingHom _ _ i).symm

variable {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)

theorem act_E_pow_smul (n : ℕ) (v : Vec K a ι) :
    Δ.act g (E K l e ^ n • v) = E K l e ^ n • Δ.act g v := by
  have h := Δ.act_smul_tot g ((fun _ => E K l e) ^ n) v
  rwa [map_pow, ringAct_E] at h

theorem act_E_smul (v : Vec K a ι) : Δ.act g (E K l e • v) = E K l e • Δ.act g v := by
  simpa using Δ.act_E_pow_smul g 1 v

theorem act_X_pow_smul (v : Vec K a ι) :
    Δ.act g ((X : K⟦X⟧) ^ e • v) = (X : K⟦X⟧) ^ e • Δ.act g v := by
  have h := Δ.act_smul_tot g (fun _ => X ^ e) v
  rwa [ringAct_X_pow] at h

theorem act_mem_uPow {m : ℕ} {v : Vec K a ι} (hv : v ∈ uPow K a ι m) :
    Δ.act g v ∈ uPow K a ι m := by
  obtain ⟨w, rfl⟩ := mem_uPow_iff_exists.1 hv
  have h := Δ.act_smul_tot g ((fun _ => X) ^ m) w
  rw [map_pow, ringAct_X] at h
  intro τ i
  rw [show Δ.act g ((X : K⟦X⟧) ^ m • w) = _ from h]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (Dvd.intro_left _ rfl) m) _

theorem act_mem_Mext {B : Subalgebra O K⟦X⟧} (hA : A O K ≤ B) (hB : Rot e B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : Δ.act g v ∈ P.Mext B := by
  rw [eq_sum_bas v, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [act_smul_tot]
  exact P.smul_tot_mem_Mext (hB.ringAct_mem g fun τ => mem_tot.1 hv τ i)
    (P.Mext_mono hA (Δ.act_mem_M g _ (P.bas_mem_M i)))

theorem act_mem_ext {B : Subalgebra O K⟦X⟧} (hA : A O K ≤ B) (hB : Rot e B) {v : Vec K a ι}
    (hv : v ∈ P.ext B) : Δ.act g v ∈ P.ext B := by
  rw [P.eq_sum_phi_bas v, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [act_smul_tot, act_phi]
  exact P.smul_tot_mem_ext (hB.ringAct_mem g fun τ => P.mem_extc_iff.1 (mem_tot.1 hv τ) i)
    (P.ext_mono hA (P.phi_mem_L (Δ.act_mem_M g _ (P.bas_mem_M i))))

theorem act_conn (v : Vec K a ι) : Δ.act g (P.conn v) = P.conn (Δ.act g v) :=
  PhiMod.map_conn (Δ.act g).toAddMonoidHom (ringAct g) (ringAct_NTot g) (Δ.act_smul_tot g)
    (Δ.act_phi g) v

theorem act_zeta (y : Vec K a ι) : Δ.act g (P.zeta y) = P.zeta (Δ.act g y) :=
  PhiMod.map_zeta (Δ.act g) (fun _ => Δ.act_mem_uPow g) (Δ.act_phi g) (Δ.act_conn g) y

theorem red_act_cst_red (v : Vec K a ι) : red (Δ.act g (cst (red v))) = red (Δ.act g v) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, ← mem_uPow_one]
  exact Δ.act_mem_uPow g (by rw [mem_uPow_one, map_sub, red_cst, sub_self])

def actD : Representation K (TameGal K l e a) P.D where
  toFun g := red ∘ₗ Δ.act g ∘ₗ cst
  map_one' := LinearMap.ext fun d => by simp
  map_mul' g h := LinearMap.ext fun d => by
    simp only [map_mul, LinearMap.comp_apply, Module.End.mul_apply, red_act_cst_red]

theorem red_act (v : Vec K a ι) : red (Δ.act g v) = Δ.actD g (red v) :=
  (Δ.red_act_cst_red g v).symm

theorem actD_phiD (d : P.D) : Δ.actD g (P.phiD d) = P.phiD (Δ.actD g d) := by
  conv_lhs => rw [← red_cst d, ← P.red_phi, ← red_act, act_phi, P.red_phi, red_act, red_cst]

theorem act_xi (d : P.D) : Δ.act g (P.xi d) = P.xi (Δ.actD g d) := by
  rw [PhiMod.map_xi (Δ.act_phi g), red_act, PhiMod.red_xi]

abbrev inv : Submodule K (Vec K a ι) := Δ.act.invariants

def isotypic (c : ZMod e) : Submodule K (Vec K a ι) where
  carrier := {v | ∀ ζ τ, Δ.act (TameGal.inertia ζ) v τ =
    (TameGal.inertia ζ : TameGal K l e a).root τ ^ c.val • v τ}
  add_mem' hv hw ζ τ := by rw [map_add, Pi.add_apply, hv, hw, Pi.add_apply, smul_add]
  zero_mem' ζ τ := by simp
  smul_mem' r v hv ζ τ := by rw [map_smul, Pi.smul_apply, hv, Pi.smul_apply, smul_comm]

def chars (τ : ZMod a) : Set (ZMod e) :=
  {c | ∃ d : P.D, d τ ≠ 0 ∧ ∀ ζ, Δ.actD (TameGal.inertia ζ) d τ =
    (TameGal.inertia ζ : TameGal K l e a).root τ ^ c.val • d τ}

def plusAct : Module.End K (Vec K a (ι ⊕ Unit)) where
  toFun w := join (Δ.act g fun τ i => w τ (.inl i)) (ringAct g fun τ => w τ (.inr ()))
  map_add' v w := by
    rw [← join_add, ← map_add, ← map_add]
    rfl
  map_smul' c v := by
    rw [RingHom.id_apply, ← join_smul, ← map_smul, ← map_smul]
    rfl

theorem plusAct_join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    Δ.plusAct g (join v f) = join (Δ.act g v) (ringAct g f) := rfl

def plus [NeZero e] {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv) :
    Descent (P.plus hy) where
  act :=
    { toFun := Δ.plusAct
      map_one' := LinearMap.ext fun w => by
        rw [← join_eta w, plusAct_join]
        simp
      map_mul' := fun g h => LinearMap.ext fun w => by
        rw [← join_eta w, Module.End.mul_apply, plusAct_join, plusAct_join, plusAct_join, map_mul,
          map_mul]
        rfl }
  act_smul_tot g f w := by
    change Δ.plusAct g _ = _ • Δ.plusAct g _
    rw [← join_eta w, ← join_smul_tot, plusAct_join, plusAct_join, ← join_smul_tot, act_smul_tot,
      map_mul]
  act_mem_M g w hw := by
    change Δ.plusAct g w ∈ (P.plus hy).Mext (A O K)
    rw [← join_eta w, plusAct_join, P.join_mem_Mext hy]
    exact ⟨Δ.act_mem_M g _ (mem_tot.2 fun τ i => mem_tot.1 hw τ (.inl i)),
      rot_A.ringAct_mem g fun τ => mem_tot.1 hw τ (.inr ())⟩
  act_phi g w := by
    change Δ.plusAct g _ = (P.plus hy).phi (Δ.plusAct g _)
    rw [← join_eta w, P.plus_phi_join, plusAct_join, plusAct_join, P.plus_phi_join, map_add, act_phi,
      act_smul_tot, hinv g, ringAct_frobTot]

theorem plus_act_join [NeZero e] {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
    (hinv : y ∈ Δ.inv) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (Δ.plus hy hinv).act g (join v f) = join (Δ.act g v) (ringAct g f) := rfl

end Descent

def frobPeriod (l : ℕ) {e : ℕ} (c : ZMod e) : ℕ := Function.minimalPeriod (fun x => (l : ZMod e) * x) c

def maxPeriod (l : ℕ) {e : ℕ} (T : Finset (ZMod e)) : ℕ :=
  (T ×ˢ T).sup fun p => frobPeriod l (p.1 - p.2)

example : frobPeriod 3 (1 : ZMod 8) = 2 :=
  Function.minimalPeriod_eq_prime (p := 2) (by decide) (by decide)

example : ringAct (TameGal.inertia (rootsOfUnity.mkOfPowEq (-1 : ℚ_[3]) (n := 2) (by norm_num)) :
    TameGal ℚ_[3] 3 2 1) (fun _ => X) 0 = -X := by
  rw [ringAct_X]
  simp

end GlobalTheory.BK
end
end

section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Scalars

variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]

theorem mem_A_of_E_mul_mem {h : K⟦X⟧} (hh : h ∈ Rpi O K l e) (hE : E K l e * h ∈ A O K) :
    h ∈ A O K := by
  obtain ⟨b, hb⟩ := (mem_invL_A_iff l).1 (mem_invL_A_of_E_mul l e hh (le_away _ _ hE))
  have hbdd : BddAbove (Set.range fun n => ‖coeff n h‖) := ⟨b, by rintro _ ⟨n, rfl⟩; exact hb n⟩
  have hle (n : ℕ) : ‖coeff n h‖ ≤ ⨆ n, ‖coeff n h‖ := le_ciSup hbdd n
  have h1 : ⨆ n, ‖coeff n h‖ ≤ max 1 (‖(l : K)‖ * ⨆ n, ‖coeff n h‖) := ciSup_le fun n => by
    have : coeff n h = coeff (n + e) (E K l e * h) + -(l * coeff (n + e) h) := by
      rw [coeff_E_mul]; ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hE _) ?_)
    rw [norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
  intro n
  refine (hle n).trans ?_
  rcases le_max_iff.1 h1 with h2 | h2
  · exact h2
  · nlinarith [norm_l_lt_one (K := K) l]

theorem mem_A_of_E_pow_mul_mem (m : ℕ) {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e ^ m * h ∈ A O K) : h ∈ A O K := by
  induction m with
  | zero => simpa using hE
  | succ m ih =>
    refine ih (mem_A_of_E_mul_mem l e (mul_mem (pow_mem (E_mem l e _) m) hh) ?_)
    rwa [← mul_assoc, ← pow_succ']

theorem algebraMap_AhatE_injective :
    Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 (Ehat_mem_nonZeroDivisors O K l e))

theorem hat_E_pow_mul (n : ℕ) {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    hat O l e (E K l e ^ n * f) = algebraMap _ _ (Ehat O K l e ^ n) * hat O l e f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, hat_mul l e (E_mem l e _) (mul_mem (pow_mem (E_mem l e _) n) hf), ih,
      hat_E, pow_succ', map_mul, mul_assoc]

theorem hat_sub {f g : K⟦X⟧} (hf : f ∈ RpiE O K l e) (hg : g ∈ RpiE O K l e) :
    hat O l e (f - g) = hat O l e f - hat O l e g := by
  rw [eq_sub_iff_add_eq, ← hat_add l e (sub_mem hf hg) hg, sub_add_cancel]

theorem hat_mem_range_iff {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    (∃ x : Ahat O K l e, algebraMap _ _ x = hat O l e f) ↔ f ∈ Rpi O K l e := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => ⟨_, (hat_coe_Rpi l e ⟨f, h⟩).symm⟩⟩
  obtain ⟨n, hn⟩ := id hf
  have h1 : toHat O K l e ⟨_, hn⟩ = Ehat O K l e ^ n * x := algebraMap_AhatE_injective l e (by
    rw [← hat_coe_Rpi, map_mul, hx]
    exact hat_E_pow_mul l e n hf)
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) =
      Ideal.Quotient.mk _ (EIn l e _) := AlgHom.commutes _ _
  obtain ⟨h, hh, H⟩ := (evalₐ_toHat_eq_iff l e n ⟨_, hn⟩ 0).1 (by
    rw [h1, map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul, map_zero])
  have H' : E K l e ^ n * f = E K l e ^ n * h := by simpa using H
  rwa [((isUnit_E l e).pow n).mul_left_cancel H']

theorem exists_eq_algebraMap_add_pow_mul {B : Type} [CommRing B] (s : B) (n : ℕ)
    (x : AdicCompletion (Ideal.span {s}) B) :
    ∃ (g : B) (x' : AdicCompletion (Ideal.span {s}) B),
      x = algebraMap B _ g + algebraMap B _ s ^ n * x' := by
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {s}) B n x)
  have h : x - AdicCompletion.of (Ideal.span {s}) B g ∈
      Ideal.span {s} ^ n • (⊤ : Submodule B (AdicCompletion (Ideal.span {s}) B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
      map_sub, ← hg, sub_eq_zero]
    rfl
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨x', -, hx'⟩ := h
  refine ⟨g, x', ?_⟩
  rw [Algebra.smul_def, map_pow, eq_sub_iff_add_eq'] at hx'
  exact hx'.symm

theorem toHat_derivative (f : Rpi O K l e) :
    toHat O K l e ⟨_, derivative_mem_R l f.2⟩ = dHat O K l e (toHat O K l e f) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) (toHat O K l e f))
  rw [dHat, evalₐ_complDer _ _ hg.symm, evalₐ_toHat_eq_iff]
  obtain ⟨h, hh, H⟩ := (evalₐ_toHat_eq_iff l e (n + 1) f g).1 hg.symm
  refine ⟨E K l e * PowerSeries.derivative K h +
    h * (((n + 1 : ℕ) : K⟦X⟧) * PowerSeries.derivative K (E K l e)), add_mem
      (mul_mem (E_mem l e _) (derivative_mem_R l hh)) (mul_mem hh (mul_mem (natCast_mem _ _)
        (derivative_mem_R l (E_mem l e _)))), ?_⟩
  rw [coe_derAl, ← map_sub, H, Derivation.leibniz, derivative_pow]
  simp only [smul_eq_mul, Nat.add_sub_cancel]
  ring

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] in
theorem N_mem_RpiE {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) : N K f ∈ RpiE O K l e :=
  N_mem (derivative_mem_away _ (fun _ => derivative_mem_R l) hf)

theorem hat_N_of_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    hat O l e (N K f) = NHatE O K l e (hat O l e f) := by
  have hu : hat O l e (X : K⟦X⟧) = algebraMap _ _ (uhat O K l e) :=
    (hat_coe_Rpi l e (uIn _)).trans (congrArg _ (toHat_eq_ofAl l e rfl))
  rw [N_apply, hat_mul l e HasU.X_mem (le_away _ _ (derivative_mem_R l hf)), hu,
    hat_coe_Rpi l e ⟨f, hf⟩, hat_coe_Rpi l e ⟨_, derivative_mem_R l hf⟩, toHat_derivative l e ⟨f, hf⟩,
    NHatE, Derivation.smul_apply, dHatE_algebraMap, smul_eq_mul]

theorem hat_N {f : K⟦X⟧} (hf : f ∈ RpiE O K l e) :
    hat O l e (N K f) = NHatE O K l e (hat O l e f) := by
  obtain ⟨n, hn⟩ := id hf
  have hE : E K l e ^ n ∈ Rpi O K l e := pow_mem (E_mem l e _) n
  have hE' : E K l e ^ n ∈ RpiE O K l e := le_away _ _ hE
  have h1 := hat_N_of_mem_Rpi l e hn
  rw [coe_EIn, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    hat_add l e (mul_mem hE' (N_mem_RpiE l e hf)) (mul_mem hf (N_mem_RpiE l e hE')),
    hat_mul l e hf (N_mem_RpiE l e hE'), hat_N_of_mem_Rpi l e hE, hat_mul l e hE' hf,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_left_inj, hat_E_pow_mul l e n (N_mem_RpiE l e hf),
    ← mul_one (E K l e ^ n), hat_E_pow_mul l e n (one_mem _),
    show hat O l e (1 : K⟦X⟧) = 1 from (hat_coe l e 1).trans (map_one _), mul_one, map_pow] at h1
  exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow n).mul_left_cancel h1

variable (K) in

def Ezpow (i : ℤ) : K⟦X⟧ := (((isUnit_E (K := K) l e).unit ^ i : K⟦X⟧ˣ) : K⟦X⟧)

omit [IsUltrametricDist K] [CompleteSpace K]

@[simp] theorem Ezpow_natCast (n : ℕ) : Ezpow K l e n = E K l e ^ n := by simp [Ezpow]

theorem Ezpow_add (i j : ℤ) : Ezpow K l e (i + j) = Ezpow K l e i * Ezpow K l e j := by
  simp [Ezpow, _root_.zpow_add]

theorem E_pow_mul_Ezpow_neg (n : ℕ) : E K l e ^ n * Ezpow K l e (-n) = 1 := by
  rw [← Ezpow_natCast, ← Ezpow_add]
  simp [Ezpow]

end Scalars

section DivE

variable {R : Type} [Semiring R] [Module R (Vec K a ι)] [SMulCommClass R K⟦X⟧ (Vec K a ι)]

variable (l e) in

def divE (n : ℕ) (W : Submodule R (Vec K a ι)) : Submodule R (Vec K a ι) where
  carrier := {y | E K l e ^ n • y ∈ W}
  add_mem' hv hw := by simpa only [Set.mem_ofPred_eq, smul_add] using W.add_mem hv hw
  zero_mem' := by simp
  smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, smul_comm c] using W.smul_mem c hy

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
theorem mem_divE {n : ℕ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ divE l e n W ↔ E K l e ^ n • y ∈ W := Iff.rfl

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

variable (l e) in

def shiftE (i : ℤ) (W : Submodule R (Vec K a ι)) : Submodule R (Vec K a ι) where
  carrier := {y | Ezpow K l e (-i) • y ∈ W}
  add_mem' hv hw := by simpa only [Set.mem_ofPred_eq, smul_add] using W.add_mem hv hw
  zero_mem' := by simp
  smul_mem' c y hy := by simpa only [Set.mem_ofPred_eq, smul_comm c] using W.smul_mem c hy

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
theorem mem_shiftE {i : ℤ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ shiftE l e i W ↔ Ezpow K l e (-i) • y ∈ W := Iff.rfl

end DivE

variable (K a ι) in

def mulV (f : K⟦X⟧) : Module.End K (Vec K a ι) where
  toFun v := f • v
  map_add' := smul_add f
  map_smul' c v := smul_comm f c v

omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
@[simp] theorem mulV_apply (f : K⟦X⟧) (v : Vec K a ι) : mulV K a ι f v = f • v := rfl

namespace PhiMod

variable (P : PhiMod O K l e a ι)

abbrev EM (η : ℕ) : Submodule (A O K) (Vec K a ι) := divE l e η P.M

theorem mem_Mext_invE_of_mem_divE {B : Subalgebra O K⟦X⟧} [HasU B] {n : ℕ} {y : Vec K a ι}
    (hy : E K l e ^ n • y ∈ P.Mext B) : y ∈ P.Mext (invE l e B) :=
  mem_tot.2 fun τ i => ⟨n, mem_tot.1 hy τ i⟩

def Man : Submodule K (Vec K a ι) := (P.Mext (Rpi O K l e)).restrictScalars K

theorem mem_Man {v : Vec K a ι} : v ∈ P.Man ↔ v ∈ P.Mext (Rpi O K l e) := Iff.rfl

theorem smul_mem_Man {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {v : Vec K a ι} (hv : v ∈ P.Man) :
    f • v ∈ P.Man := P.smul_tot_mem_Mext (f := fun _ => f) (fun _ => hf) hv

abbrev Pol : Type := Vec K a ι ⧸ P.Man

abbrev cls : Vec K a ι →ₗ[K] P.Pol := P.Man.mkQ

theorem cls_eq_zero_iff {v : Vec K a ι} : P.cls v = 0 ↔ v ∈ P.Man := Submodule.Quotient.mk_eq_zero _

def PolEta (η : ℕ) : Submodule K P.Pol := (divE l e η P.Man).map P.cls

def mulPol (f : Rpi O K l e) : Module.End K P.Pol :=
  P.Man.mapQ P.Man (mulV K a ι f) fun _ => P.smul_mem_Man f.2

@[simp] theorem mulPol_cls (f : Rpi O K l e) (v : Vec K a ι) :
    P.mulPol f (P.cls v) = P.cls ((f : K⟦X⟧) • v) := rfl

def vPol : Module.End K P.Pol := P.mulPol (uIn _ ^ e)

@[simp] theorem vPol_cls (v : Vec K a ι) : P.vPol (P.cls v) = P.cls ((X : K⟦X⟧) ^ e • v) := rfl

variable [Fact l.Prime]

def EN : Module.End K (Vec K a ι) := mulV K a ι (E K l e) * P.conn

theorem EN_apply (v : Vec K a ι) : P.EN v = E K l e • P.conn v := rfl

def Mon : Vec K a ι →ₗ[K] P.Pol := P.cls ∘ₗ (P.EN - mulV K a ι (E K l e) * P.zeta)

theorem Mon_apply (y : Vec K a ι) : P.Mon y = P.cls (P.EN y - E K l e • P.zeta y) := rfl

theorem eisenstein_x_eq_neg {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    (P.plus hy).EN xVec = -(P.plusInl hy).app (P.EN y - E K l e • P.zeta y) := by
  rw [EN_apply, plus_conn_xVec_eq, EN_apply, ← smul_sub, ← map_smul, ← map_neg, ← smul_neg, neg_sub]

theorem Mon_eq_zero_iff {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    P.Mon y = 0 ↔ (P.plus hy).EN xVec ∈ (P.plus hy).Man := by
  rw [eisenstein_x_eq_neg, neg_mem_iff, plusInl_app, mem_Man, P.join_mem_Mext hy, Mon_apply, cls_eq_zero_iff]
  exact ⟨fun h => ⟨h, fun _ => zero_mem _⟩, fun h => h.1⟩

theorem Mon_phi_sub (m : Vec K a ι) : P.Mon (P.phi m - m) = -P.cls (P.EN m) := by
  rw [Mon_apply, zeta_phi_sub, map_sub P.EN, ← EN_apply, sub_sub_cancel_left, map_neg]

theorem E_pow_smul_EN (n : ℕ) (y : Vec K a ι) : E K l e ^ n • P.EN y =
    P.EN (E K l e ^ n • y) - ((n : K⟦X⟧) * N K (E K l e)) • E K l e ^ n • y := by
  rw [EN_apply, EN_apply, conn_smul, Derivation.leibniz_pow]
  cases n with
  | zero => simp
  | succ n =>
    ext τ i : 2
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, Pi.smul_apply, Pi.sub_apply,
      Pi.add_apply]
    ring

variable [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem M_le_Man {v : Vec K a ι} (hv : v ∈ P.M) : v ∈ P.Man := P.Mext_mono (A_le_Rpi l e) hv

theorem cls_mem_PolEta {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) : P.cls y ∈ P.PolEta η :=
  ⟨y, P.M_le_Man hy, rfl⟩

def filL (i : ℤ) : Submodule (invL l (A O K)) (Vec K a ι) :=
  (P.ext (invL l (A O K)) ⊓ shiftE l e i (P.Mext (invL l (A O K)))) ⊔
    shiftE l e 1 (P.ext (invL l (A O K)))

def jumps : Set ℤ := {i | P.filL (i + 1) ≠ P.filL i}

variable [CompleteSpace K]

theorem mem_M_of_mem_Man {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) (h : y ∈ P.Man) : y ∈ P.M :=
  mem_tot.2 fun τ i => mem_A_of_E_pow_mul_mem l e η (mem_tot.1 h τ i) (mem_tot.1 hy τ i)

theorem mem_Mhat {w : ZMod a → ι → AhatE O K l e} :
    w ∈ P.Mhat ↔ ∀ τ i, ∃ x : Ahat O K l e, algebraMap _ _ x = w τ i := by
  simp only [Mhat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, mem_Mhatc]

theorem hatTot_mem_Mhat_iff {v : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e)) :
    P.hatTot v ∈ P.Mhat ↔ v ∈ P.Man :=
  P.mem_Mhat.trans <| Iff.trans (forall₂_congr fun τ i => hat_mem_range_iff l e (mem_tot.1 hv τ i))
    (mem_tot (P := fun _ => vecs ι (Rpi O K l e))).symm

theorem hatTot_sub_mem_Mhat_iff {v w : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e))
    (hw : w ∈ P.Mext (RpiE O K l e)) : P.hatTot v - P.hatTot w ∈ P.Mhat ↔ P.cls v = P.cls w := by
  have : P.hatTot v - P.hatTot w = P.hatTot (v - w) := funext fun τ => funext fun i =>
    (hat_sub l e (mem_tot.1 hv τ i) (mem_tot.1 hw τ i)).symm
  rw [this, P.hatTot_mem_Mhat_iff (sub_mem hv hw)]
  exact (Submodule.Quotient.eq _).symm

theorem smul_hatTot_mem_Mhat_iff (η : ℕ) {v : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e)) :
    Ehat O K l e ^ η • P.hatTot v ∈ P.Mhat ↔ v ∈ divE l e η P.Man := by
  have : Ehat O K l e ^ η • P.hatTot v = P.hatTot (E K l e ^ η • v) := funext fun τ => funext fun i =>
    (Algebra.smul_def _ _).trans (hat_E_pow_mul l e η (mem_tot.1 hv τ i)).symm
  rw [this, mem_divE]
  exact P.hatTot_mem_Mhat_iff
    (P.smul_tot_mem_Mext (f := fun _ => E K l e ^ η) (fun _ => pow_mem (E_mem l e _) η) hv)

theorem exists_sub_hatTot_mem_Mhat (η : ℕ) {w : ZMod a → ι → AhatE O K l e}
    (hw : Ehat O K l e ^ η • w ∈ P.Mhat) :
    ∃ v ∈ divE l e η (P.Mext (invL l (A O K))), w - P.hatTot v ∈ P.Mhat := by
  choose x hx using P.mem_Mhat.1 hw
  choose g x' hg using fun τ i =>
    exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) η (x τ i)
  have hE (τ i) : E K l e ^ η * (Ezpow K l e (-η) * g τ i) = g τ i := by
    rw [← mul_assoc, E_pow_mul_Ezpow_neg, one_mul]
  refine ⟨fun τ i => Ezpow K l e (-η) * g τ i, mem_tot.2 fun τ i => ?_,
    P.mem_Mhat.2 fun τ i => ⟨x' τ i, ?_⟩⟩
  · change E K l e ^ η * (Ezpow K l e (-η) * g τ i) ∈ invL l (A O K)
    rw [hE]
    exact (g τ i).2
  · have hg' := invL_A_le_Rpi l e (g τ i).2
    have h0 : Ezpow K l e (-η) * (g τ i : K⟦X⟧) ∈ RpiE O K l e := ⟨η, by rw [coe_EIn, hE]; exact hg'⟩
    have h1 := hat_E_pow_mul l e η h0
    rw [hE, hat_coe_Rpi l e ⟨_, hg'⟩, toHat_eq_ofAl l e (g := g τ i) rfl] at h1
    have h2 : algebraMap _ _ (x τ i) = algebraMap _ _ (Ehat O K l e ^ η) * w τ i :=
      (hx τ i).trans (Algebra.smul_def (Ehat O K l e ^ η) (w τ i))
    have h3 : x τ i = ofAl O K l e (g τ i) + Ehat O K l e ^ η * x' τ i := hg τ i
    rw [h3, map_add, map_mul, h1, add_comm, ← eq_sub_iff_add_eq, ← mul_sub, map_pow] at h2
    exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow η).mul_left_cancel h2

def connHat (w : ZMod a → ι → AhatE O K l e) : ZMod a → ι → AhatE O K l e :=
  fun τ i => NHatE O K l e (w τ i) + ∑ j, w τ j * P.hatTot (P.conn (bas j)) τ i

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] in
theorem conn_apply_eq (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    P.conn v τ i = N K (v τ i) + ∑ j, v τ j * P.conn (bas j) τ i := by
  conv_lhs => rw [eq_sum_bas v]
  simp [conn_smul_tot, Finset.sum_apply, Finset.sum_add_distrib, bas, NTot, Pi.single_apply]

theorem hatTot_conn (hN : ∀ j, P.conn (bas j) ∈ P.Mext (RpiE O K l e)) {v : Vec K a ι}
    (hv : v ∈ P.Mext (RpiE O K l e)) : P.hatTot (P.conn v) = P.connHat (P.hatTot v) := by
  ext τ i
  have h1 (j) : v τ j ∈ RpiE O K l e := mem_tot.1 hv τ j
  have h2 (j) : P.conn (bas j) τ i ∈ RpiE O K l e := mem_tot.1 (hN j) τ i
  have h3 : ∑ j, v τ j * P.conn (bas j) τ i =
      ((∑ j, ⟨_, h1 j⟩ * ⟨_, h2 j⟩ : RpiE O K l e) : K⟦X⟧) := by simp
  change hat O l e (P.conn v τ i) = NHatE O K l e (hat O l e _) + ∑ j, hat O l e _ * hat O l e _
  rw [conn_apply_eq, hat_add l e (N_mem_RpiE l e (h1 i))
    (sum_mem fun j _ => mul_mem (h1 j) (h2 j)), hat_N l e (h1 i), h3, hat_coe, map_sum]
  simp only [map_mul, hat_of_mem l e (h1 _), hat_of_mem l e (h2 _)]

end PhiMod

namespace Hom

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)

def onPol : P.Pol →ₗ[K] Q.Pol :=
  P.Man.mapQ Q.Man (F.app.restrictScalars K) fun _ => F.app_mem_Mext (A_le_Rpi l e)

@[simp] theorem onPol_cls (v : Vec K a ι) : F.onPol (P.cls v) = Q.cls (F.app v) := rfl

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem app_EN (v : Vec K a ι) : F.app (P.EN v) = Q.EN (F.app v) := by
  rw [PhiMod.EN_apply, map_smul, app_conn, PhiMod.EN_apply]

theorem onPol_Mon (y : Vec K a ι) : F.onPol (P.Mon y) = Q.Mon (F.app y) := by
  rw [PhiMod.Mon_apply, onPol_cls, map_sub, app_EN, map_smul, app_zeta, PhiMod.Mon_apply]

omit [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem app_mem_EM {η : ℕ} {y : Vec K a ι} (hy : y ∈ P.EM η) : F.app y ∈ Q.EM η := by
  rw [mem_divE, ← map_smul]
  exact F.app_mem_M hy


omit [NormedAlgebra ℚ_[l] K] [NeZero e]

def imM : Submodule (A O K) (Vec K a κ) := P.M.map (F.app.restrictScalars (A O K))

def imL : Submodule (A O K) (Vec K a κ) := P.L.map (F.app.restrictScalars (A O K))

abbrev coker : Type := Q.M ⧸ F.imM.submoduleOf Q.M

end Hom

end GlobalTheory.BK
end
end
