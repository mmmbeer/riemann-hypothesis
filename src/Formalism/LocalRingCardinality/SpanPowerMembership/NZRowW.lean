import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialColumnsRamifiedTop
import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
import Formalism.LocalRingCardinality.Lemmas

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem inj_of_iso {μ} (hiso : ∀ x y, inner ℂ (S.iota μ x) (S.iota μ y) = inner ℂ x y) :
    Function.Injective (S.iota μ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have := hiso x x
  rw [LinearMap.mem_ker.mp hx, inner_zero_left] at this
  exact inner_self_eq_zero.mp this.symm


theorem iotaQ_adj {μ} (he : S.eOp μ = LinearMap.id)
    (hiso : ∀ x y, inner ℂ (S.iota μ x) (S.iota μ y) = inner ℂ x y)
    (hs : Function.Surjective (S.iota μ)) : S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ) = LinearMap.id := by
  have hi := inj_of_iso S hiso
  ext x
  refine ext_inner_right ℂ fun y => ?_
  obtain ⟨z, rfl⟩ := hs y
  have hz : z ∈ S.Qsp μ := by rw [Qsp_top S he hi]; trivial
  show inner ℂ (S.iota μ (LinearMap.adjoint (S.iotaQ μ) x : S.Amb μ)) (S.iota μ z) = inner ℂ x (S.iota μ z)
  rw [hiso]
  have h1 : inner ℂ (LinearMap.adjoint (S.iotaQ μ) x) (⟨z, hz⟩ : S.Qsp μ) =
      inner ℂ x (S.iotaQ μ ⟨z, hz⟩) := LinearMap.adjoint_inner_left _ _ _
  exact h1


end Gen

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)











omit kb ks in

theorem row_kapDef : ∃ kb ks, DV.KapDef (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) := by
  obtain ⟨kb, ks, h⟩ := DV.exists_blocks (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G (fun _ _ _ => 0) (fun _ _ _ => 0) tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)
  exact ⟨kb, ks, fun j _ _ τ => h j τ⟩

end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem unipotentSpace_le_baseSubspace (μ) : S.Usp μ ≤ S.V0 μ := inf_le_left

theorem sub_projQ_mem (μ) {x : S.Amb μ} (hx : x ∈ S.V0 μ) : x - (S.Qsp μ).starProjection x ∈ S.Usp μ := by
  set u := (S.Usp μ).starProjection x with hu
  have huU : u ∈ S.Usp μ := Submodule.starProjection_apply_mem _ _
  have hq : x - u ∈ S.Qsp μ :=
    ⟨Submodule.sub_mem _ hx (unipotentSpace_le_baseSubspace S μ huU), Submodule.sub_starProjection_mem_orthogonal x⟩
  have hp : (S.Qsp μ).starProjection x = x - u := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hq fun w hw => ?_
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal huU hw.2
  rw [hp, sub_sub_cancel]
  exact huU

theorem RRset_gen (μ) : S.RRset μ = S.iota μ '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ))) := by
  unfold RowSide.RRset RowSide.LamSet
  rw [Set.image_image]
  refine Set.image_congr fun x hx => ?_
  have h : S.iota μ (x - (S.Qsp μ).starProjection x) = 0 := (sub_projQ_mem S μ hx.2).2
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

variable {μ : D.what₂.Tup} (s : EE →ₗ[ℂ] S.Amb μ) (hs : ∀ y, S.iota μ (s y) = y)
  (hV : ∀ y, s y ∈ S.V0 μ) (hU : ∀ y, ∀ u ∈ S.Usp μ, inner ℂ u (s y) = 0)
  (hiso : ∀ y z, inner ℂ (s y) (s z) = inner ℂ y z)

include hs hV hU in

theorem mem_Qsp_iff (x : S.Amb μ) : x ∈ S.Qsp μ ↔ x = s (S.iota μ x) := by
  have hsQ : ∀ y, s y ∈ S.Qsp μ := fun y => ⟨hV y, (Submodule.mem_orthogonal _ _).mpr (hU y)⟩
  constructor
  · intro hx
    have h1 : x - s (S.iota μ x) ∈ S.Usp μ :=
      ⟨Submodule.sub_mem _ hx.1 (hV _),
        (show S.iota μ (x - s (S.iota μ x)) = 0 by rw [map_sub, hs, sub_self])⟩
    have h2 : x - s (S.iota μ x) ∈ (S.Usp μ)ᗮ := Submodule.sub_mem _ hx.2 (hsQ _).2
    have h3 := Submodule.inner_right_of_mem_orthogonal h1 h2
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)
  · intro hx
    rw [hx]; exact hsQ _

include hs hV hU in
theorem iotaQ_bij' : Function.Bijective (S.iotaQ μ) := by
  refine ⟨fun a b h => Subtype.ext ?_, fun y => ⟨⟨s y, (mem_Qsp_iff S s hs hV hU _).mpr (by rw [hs])⟩, hs y⟩⟩
  rw [(mem_Qsp_iff S s hs hV hU _).mp a.2, (mem_Qsp_iff S s hs hV hU _).mp b.2]
  exact congrArg s h

include hs hV hU hiso in
theorem iotaQ_adj' : S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ) = LinearMap.id := by
  ext x
  refine ext_inner_right ℂ fun y => ?_
  have hz : s y ∈ S.Qsp μ := (mem_Qsp_iff S s hs hV hU _).mpr (by rw [hs])
  set q := LinearMap.adjoint (S.iotaQ μ) x with hq
  have h1 : inner ℂ q (⟨s y, hz⟩ : S.Qsp μ) = inner ℂ x (S.iotaQ μ ⟨s y, hz⟩) :=
    LinearMap.adjoint_inner_left _ _ _
  have h2 : S.iotaQ μ ⟨s y, hz⟩ = y := hs y
  rw [h2] at h1
  show inner ℂ (S.iota μ (q : S.Amb μ)) y = inner ℂ x y
  rw [← h1, ← hiso, ← (mem_Qsp_iff S s hs hV hU _).mp q.2]
  rfl

end Gen

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section TwoChar

variable {Z V : Type} [CommSemiring Z] [Algebra ℂ Z] [AddCommGroup V] [Module ℂ V]

def twoChar (χ1 χ0 : Z →ₐ[ℂ] ℂ) (E : Module.End ℂ V) (hE : E * E = E) : Z →ₐ[ℂ] Module.End ℂ V :=
  AlgHom.ofLinearMap (χ1.toLinearMap.smulRight E + χ0.toLinearMap.smulRight (1 - E))
    (by simp)
    (fun x y => by
      have hEF : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
      have hFE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
      have hFF : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, hFE, sub_zero]
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, AlgHom.toLinearMap_apply, map_mul, add_mul,
        mul_add, smul_mul_smul_comm, hE, hEF, hFE, hFF, smul_zero, add_zero, zero_add])

theorem twoChar_apply (χ1 χ0 : Z →ₐ[ℂ] ℂ) (E : Module.End ℂ V) (hE : E * E = E) (z : Z) :
    twoChar χ1 χ0 E hE z = χ1 z • E + χ0 z • (1 - E) := rfl

end TwoChar

def MultT (EE A : Type) : ℕ → Type
  | 0 => EE
  | _ + 1 => A

section MultT

variable (EE A : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]

instance MultT.nacg : ∀ j, NormedAddCommGroup (MultT EE A j)
  | 0 => inferInstanceAs (NormedAddCommGroup EE)
  | _ + 1 => inferInstanceAs (NormedAddCommGroup A)

instance MultT.ips : ∀ j, InnerProductSpace ℂ (MultT EE A j)
  | 0 => inferInstanceAs (InnerProductSpace ℂ EE)
  | _ + 1 => inferInstanceAs (InnerProductSpace ℂ A)

instance MultT.fd : ∀ j, FiniteDimensional ℂ (MultT EE A j)
  | 0 => inferInstanceAs (FiniteDimensional ℂ EE)
  | _ + 1 => inferInstanceAs (FiniteDimensional ℂ A)

def castTop : ∀ j, j ≠ 0 → MultT EE A j ≃ₗᵢ[ℂ] A
  | 0, h => absurd rfl h
  | _ + 1, _ => LinearIsometryEquiv.refl ℂ A

variable {EE A}

def ioT (pr : A →ₗ[ℂ] EE) : ∀ j, MultT EE A (j + 1) →ₗ[ℂ] MultT EE A j
  | 0 => pr
  | _ + 1 => LinearMap.id

end MultT

section Coord

variable {n : ℕ} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  (b : OrthonormalBasis (Fin n) ℂ EE) (a n1 : ℕ) (hn : n ≤ n1) (h1 : n1 ≤ a)

def eP : En a →ₗ[ℂ] En a where
  toFun x := WithLp.toLp 2 fun i => if (i : ℕ) < n1 then x i else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < n1 <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < n1 <;> simp [hi]

theorem eP_apply (x : En a) (i : Fin a) : eP a n1 x i = if (i : ℕ) < n1 then x i else 0 := rfl

theorem projection_idem : eP a n1 ∘ₗ eP a n1 = eP a n1 := by
  ext x i
  simp only [LinearMap.comp_apply, eP_apply]
  split_ifs <;> rfl

theorem projection_isSelfAdjoint : (eP a n1).IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eP_apply, eP_apply]
  split_ifs <;> simp

include hn h1 in
theorem le_a : n ≤ a := hn.trans h1

def prB (h : n ≤ a) : En a →ₗ[ℂ] EE where
  toFun x := ∑ k : Fin n, x (Fin.castLE h k) • b k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

def secB : EE →ₗ[ℂ] En a where
  toFun y := WithLp.toLp 2 fun i => if hi : (i : ℕ) < n then b.repr y ⟨i, hi⟩ else 0
  map_add' x y := by
    ext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]

theorem secB_apply (y : EE) (i : Fin a) : secB b a y i = if hi : (i : ℕ) < n then b.repr y ⟨i, hi⟩ else 0 := rfl

theorem prB_secB (h : n ≤ a) (y : EE) : prB b a h (secB b a y) = y := by
  show ∑ k : Fin n, secB b a y (Fin.castLE h k) • b k = y
  conv_rhs => rw [← b.sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [secB_apply, dif_pos (show ((Fin.castLE h k : Fin a) : ℕ) < n from k.2)]
  rfl

theorem eP_secB (hn : n ≤ n1) (y : EE) : eP a n1 (secB b a y) = secB b a y := by
  ext i
  rw [eP_apply, secB_apply]
  by_cases hi : (i : ℕ) < n
  · rw [if_pos (lt_of_lt_of_le hi hn)]
  · rw [dif_neg hi]; simp




theorem sum_smul_eb (z : Fin a → ℂ) : ∑ i, z i • eb a i = WithLp.toLp 2 z := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

end Coord

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (D : D7) (c : CentralCharacterOne D)
  (χ0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] ℂ) (h0 : χ0 ⟨D.ntypes.e0, c.cen⟩ = 0)
  (hm : D.R.m ≠ 0) {n : ℕ} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (b : OrthonormalBasis (Fin n) ℂ EE) (a n1 : ℕ) (hn : n ≤ n1) (h1 : n1 ≤ a)

def projSide : RowSide D EE where
  Amb := fun _ => En a
  Mult := fun _ j => MultT EE (En a) j
  instMult := fun _ j => MultT.nacg EE (En a) j
  instMulti := fun _ j => MultT.ips EE (En a) j
  instMultf := fun _ j => MultT.fd EE (En a) j
  multZero := fun _ => LinearIsometryEquiv.refl ℂ EE
  multTop := fun _ => castTop EE (En a) D.R.m hm
  io := fun _ j => ioT (prB b a (hn.trans h1)) j
  Mtilde := fun _ => oB (eb a) _
  cen := fun _ => twoChar c.χ χ0 (eP a n1) (projection_idem a n1)
  eOp := fun _ => eP a n1
  eOp_idem := fun _ => projection_idem a n1
  eOp_sa := fun _ => projection_isSelfAdjoint a n1
  eOp_tie := fun _ => by
    rw [dif_pos c.cen, twoChar_apply, c.one, h0, one_smul, zero_smul, add_zero]
  RR := stdH D.what₂.LL n
  RR_frames := stdH_frames _ n
  jEE := jB D.what₂.embLL b
  jEE_basis := jB_basis _ b
  jEE_norm := jB_norm _ b

local notation "PS" => (projSide D c χ0 h0 hm b a n1 hn h1)

theorem projSide_downTo (μ) (k : ℕ) : (PS).downTo μ (k + 1) = prB b a (hn.trans h1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((PS).downTo μ (k + 1)).comp (LinearMap.id : En a →ₗ[ℂ] En a) = _
    rw [ih]; rfl

theorem projSide_down_cast (μ) : ∀ (j : ℕ) (h : j ≠ 0),
    (PS).downTo μ j ∘ₗ (castTop EE (En a) j h).symm.toLinearEquiv.toLinearMap = prB b a (hn.trans h1)
  | 0, h => absurd rfl h
  | k + 1, _ => by
    rw [projSide_downTo]; rfl

theorem projSide_iota (μ) : (PS).iota μ = prB b a (hn.trans h1) :=
  LinearMap.ext fun x => LinearMap.congr_fun (projSide_down_cast D c χ0 h0 hm b a n1 hn h1 μ D.R.m hm) x

theorem projectionSide_mem_iff (μ) (x : En a) : x ∈ (PS).V0 μ ↔ eP a n1 x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (projection_idem a n1) y
  · intro h
    exact ⟨x, h⟩




variable (hO : OFull D)

omit [FiniteDimensional ℂ EE] in

theorem img_lemma {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    {O : Type} [CommRing O] (f : O →+* K) (hf : ∀ z : K, (∃ y, f y = z) ↔ ∃ c : 𝓞 K, z = (c : K))
    (h : n ≤ a) (Vs : Set (En a)) (hV : ∀ y, secB b a y ∈ Vs) (y : Fin n → K) :
    jB σ b y ∈ prB b a h '' ((oB (eb a) (σ.comp f)).carrier ∩ Vs) ↔ y ∈ (stdH K n).L := by
  rw [mem_stdL]
  constructor
  · rintro ⟨x, ⟨hx, -⟩, e⟩ k
    obtain ⟨cx, rfl⟩ := (mem_oB (eb a) _ x).mp hx
    refine (hf (y k)).mp ⟨cx (Fin.castLE h k), σ.injective ?_⟩
    have h2 := congrArg (fun z => b.repr z k) e
    rw [sum_smul_eb] at h2
    have h3 : prB b a h (WithLp.toLp 2 fun i => (σ.comp f) (cx i)) =
        jB σ b (fun k => f (cx (Fin.castLE h k))) := rfl
    simp only [h3, repr_jB] at h2
    exact h2
  · intro hy
    have h' := fun k => (hf (y k)).mpr (hy k)
    choose cy hcy using h'
    refine ⟨secB b a (jB σ b y), ⟨(mem_oB (eb a) _ _).mpr
      ⟨fun i => if hi : (i : ℕ) < n then cy ⟨i, hi⟩ else 0, ?_⟩, hV _⟩, prB_secB b a _ _⟩
    rw [sum_smul_eb]
    ext i
    rw [secB_apply]
    by_cases hi : (i : ℕ) < n
    · simp only [dif_pos hi, repr_jB, RingHom.comp_apply, hcy]
    · simp [dif_neg hi]

include hO in

theorem projSide_rrDef : (PS).RRDef := by
  refine rrDef_of _ (stdH D.what₂.LL n).L (fun w y => ?_) rfl
  rw [RRset_gen, projSide_iota]
  exact img_lemma b a D.what₂.embLL D.what₂.OtoLL hO (hn.trans h1) _
    (fun z => (projectionSide_mem_iff D c χ0 h0 hm b a n1 hn h1 _ _).mpr (eP_secB b a n1 hn z)) y


end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rows

variable (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R0.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

end Rows

section Div

variable (K : Type) [Field K] [NumberField K] [StarRing K]

abbrev div1 : DivData K Unit :=
  { toyZeroLatticeDatum K with
    Nu := fun _ => oneHLat K
    Bk := fun _ => 0
    h := fun _ => 0
    HH := sFrame (fun _ : Unit => oneHLat K) (fun _ => 0) + (zeroHLat K).muMax
    HH_ge := le_refl _ }


end Div

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E) {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

end S

section G

open Formalism.MainNotions.G

def gLevel1 (p : ℕ) : Level (emptyPlaces p) where
  Γ := Unit
  act := fun v => v.elim0
  χ := 1



def trivialLocalData (p : ℕ) : GAtP p where
  O := ℤ_[3]
  Kf := ℚ_[3]
  P := emptyPlaces p
  comp := Unit
  lev := fun _ => gLevel1 p
  e := 0


end G

end Formalism.BasicNotions.Examples₂.ND
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (Tau : Type) [Fintype Tau]

abbrev period2 : PeriodMap R0 (chain1 Tau) where
  Mt := ℂ
  Wz := ℂ
  evz := cst.symm.toLinearMap
  Wrow := ℂ
  lowerMap := LinearMap.id
  period := LinearMap.mul ℂ ℂ




def oneOLat {O : Type} [CommRing O] (φ : O →+* ℂ) : Rows.OLat O φ ℂ :=
  ⟨{1}, by rw [Finset.coe_singleton]; exact span_one_C⟩

section Rows

variable (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (hTau : Fintype.card Tau = R0.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (eo : ℂ) (heo : eo = 0 ∨ eo = 1)

def slL : LL →ₛₗ[embLL] ℂ where
  toFun x := embLL x
  map_add' x y := map_add _ _ _
  map_smul' c x := by simp

include heo in
theorem smul_id_idem : (eo • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) ∘ₗ (eo • LinearMap.id) = eo • LinearMap.id := by
  rcases heo with rfl | rfl <;> simp

include heo in
theorem smul_id_sa : (eo • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).IsSymmetric := by
  intro x y
  rcases heo with rfl | rfl <;> simp

end Rows

section Div

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def bk2 : (Fin 1 → K) →ₗ[K] Module.Dual K (Fin 1 → K) :=
  LinearMap.mk₂ K (fun φ x => φ 0 * x 0) (by intros; simp [add_mul]) (by intros; simp [mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp; ring)

abbrev div2 : DivData K Unit :=
  { toyZeroLatticeDatum K with
    RR := oneHLat K
    Nu := fun _ => oneHLat K
    Bk := fun _ => bk2 K
    h := fun _ => 0
    HH := sFrame (fun _ : Unit => oneHLat K) (fun _ => 0) + (oneHLat K).muMax
    HH_ge := le_refl _
    Dall := 1 }


end Div

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E) {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

end S

section Forms

variable (Tau : Type) [Fintype Tau] (T : ℕ) [hT : Fact T.Prime]
  {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) (hTau : Fintype.card Tau = R0.f) (Dst : ℝ) (hD : 0 < Dst)

def forms2 : MemberForms LL embLL Pl Tau (fun _ => hc0) (chain1 Tau) (baseColumnsAt Tau T Dst hD)
    (period2 Tau) :=
  { forms1 Tau T embLL Pl hTau Dst hD with }


end Forms

open Polynomial in
theorem not_isGood_const {N g : ℕ} [Fact g.Prime] {PP J : Type} (f : (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) : ¬ Formalism.CyclotomicNorms.IsGood N g (fun _ : PP => f) χ := by
  rintro ⟨h1, -, -, -, h4, v, q, -, ⟨s, hs'⟩, -, hN, hN3⟩
  have hs : f = q * s := hs'
  have hf0 : f ≠ 0 := (h1 v).1.ne_zero
  have hfN : f.natDegree = N := (h1 v).2.1
  have hq0 : q ≠ 0 := fun h => hf0 (by rw [hs, h, zero_mul])
  have hs0 : s ≠ 0 := fun h => hf0 (by rw [hs, h, mul_zero])
  have hdeg : f.natDegree = q.natDegree + s.natDegree := by
    conv_lhs => rw [hs]
    exact natDegree_mul hq0 hs0
  obtain ⟨_, hv'⟩ := h4 s.natDegree (by omega) (by omega)
  exact hv' ⟨s, ⟨q, by rw [mul_comm]; exact hs⟩, rfl⟩

end Formalism.BasicNotions.Examples₂.ND
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

theorem labelIdempotent_ne_one (ht : THyp H) : e0L H Lb what₂ h ℂ ≠ 1 := by
  intro e1
  let b : ∀ kv : Ix (ndG H Lb what₂ h), Fin R.r → ZMod (H.g kv.1) := fun kv => fun i => (Lb.fA kv.1).coeff i
  have hm : ∀ k, Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (Lb.fA k).coeff i) = Lb.fA k := fun k =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (Lb.okA k).1 (Lb.okA k).2.1
  have hS : ¬ GoodT (ndG H Lb what₂ h) (fun k v => Formalism.CyclotomicNorms.monicOf (b ⟨k, v⟩)) := by
    intro hg
    have := (hg 0).1
    simp only [b, hm] at this
    exact ND.not_isGood_const _ _ this
  have hmul := eSum_mul_tens (I := Ix (ndG H Lb what₂ h)) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf a))
    (fun a => GoodT (ndG H Lb what₂ h) fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
    (fun kv l => esZ_idem _) (fun kv l l' hl => esZ_orth _ _ (monicOf_injective.ne hl)) b
  rw [if_neg hS] at hmul
  have hne : tens (fun kv : Ix (ndG H Lb what₂ h) => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) ≠ 0 :=
    tens_ne_zero _ fun kv => by
      show esZ ℂ _ (Lb.fA kv.1) (Lb.fB kv.1) (Formalism.CyclotomicNorms.monicOf fun i : Fin R.r => (Lb.fA kv.1).coeff i) ≠ 0
      rw [hm]
      unfold esZ
      rw [if_pos rfl]
      exact one_sub_eT_ne_zero (zL H kv.1) (zL_ne_one H ht kv.1)
  apply hne
  have : e0L H Lb what₂ h ℂ = eSum (I := Ix (ndG H Lb what₂ h)) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
      (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf a))
      (fun a => GoodT (ndG H Lb what₂ h) fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := rfl
  rw [← this, e1, one_mul] at hmul
  exact hmul

theorem one_sub_e0L_mem_center :
    1 - e0L H Lb what₂ h ℂ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) :=
  Subalgebra.sub_mem _ (Subalgebra.one_mem _) (labelIdempotent_mem_center H Lb what₂ h)

def labelComplementCharacter (ht : THyp H) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) →ₐ[ℂ] ℂ :=
  (exists_char _ (one_sub_e0L_mem_center H Lb what₂ h)
    (by rw [sub_mul, mul_sub, mul_sub, labelIdempotent_idem, one_mul, one_mul, mul_one, sub_self, sub_zero])
    (sub_ne_zero.mpr (labelIdempotent_ne_one H Lb what₂ h ht).symm)).choose

theorem labelComplementCharacter_idempotent_zero (ht : THyp H) : labelComplementCharacter H Lb what₂ h ht ⟨e0L H Lb what₂ h ℂ, labelIdempotent_mem_center H Lb what₂ h⟩ = 0 := by
  have h1 : labelComplementCharacter H Lb what₂ h ht ⟨1 - e0L H Lb what₂ h ℂ, one_sub_e0L_mem_center H Lb what₂ h⟩ = 1 :=
    (exists_char _ (one_sub_e0L_mem_center H Lb what₂ h)
      (by rw [sub_mul, mul_sub, mul_sub, labelIdempotent_idem, one_mul, one_mul, mul_one, sub_self, sub_zero])
      (sub_ne_zero.mpr (labelIdempotent_ne_one H Lb what₂ h ht).symm)).choose_spec
  have e : (⟨1 - e0L H Lb what₂ h ℂ, one_sub_e0L_mem_center H Lb what₂ h⟩ :
      Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h)))) = 1 - ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ := rfl
  rw [e, map_sub, map_one] at h1
  linear_combination -h1

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)

theorem row_m_ne : (DR).R.m ≠ 0 := by
  have := R.two_le_m
  show R.m ≠ 0
  omega

def levelRecordCentralCharacter : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (DR).nd)) →ₐ[ℂ] ℂ :=
  labelComplementCharacter H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ht

theorem rowCharacter_idempotent : levelRecordCentralCharacter H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat ⟨(DR).ntypes.e0, (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).cen⟩ = 0 := by
  have key : (⟨(DR).ntypes.e0, (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).cen⟩ :
      Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg))))) =
      ⟨_, labelIdempotent_mem_center H Lb _ _⟩ := Subtype.ext (labelNewtypes_idempotent_eq H Lb _ _ ht G.tame)
  exact (congrArg _ key).trans (labelComplementCharacter_idempotent_zero H Lb _ _ ht)

variable (a n1 : ℕ) (hn : d0 ≤ n1) (h1 : n1 ≤ a)

def levelRecordBaseSideAtDistinguishedPrime : BaseLevelRowSide DR :=
  ⟨projSide DR (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) (levelRecordCentralCharacter H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) (rowCharacter_idempotent H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) (row_m_ne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) (eb d0) a n1 hn h1⟩



end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)

def levelRecordTwistForms : TwForms DR where
  A := fun u _ => haveI := hT u; atTN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG
  A_T := fun _ _ => rfl
  fm := fun u μ => haveI := hT u; formsN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u μ) H.φ₀ (placesOf H.E)
    (card_realPlaces_eq_degree R)
  e0 := fun _ _ => LinearEquiv.refl _ _
  twist_preserves_base_lattice := fun _ _ _ => Iff.rfl
  embed_mul_block_embedding := fun _ _ _ => rfl
  eMu0 := fun _ _ _ => LinearEquiv.refl _ _
  eMu0_lat := fun _ _ _ _ => Iff.rfl
  eMu0_emb := fun _ _ _ _ => HEq.rfl

end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions MvPolynomial

section Det

theorem det_ind {p N : ℕ} (I : Fin p ↪o Fin N) {C : Type} [CommRing C] :
    (Matrix.of fun i k : Fin p => if (i : ℕ) = (I k : ℕ) then (1 : C) else 0).det =
      if ∀ k, (I k : ℕ) = k then 1 else 0 := by
  split_ifs with h
  · have : (Matrix.of fun i k : Fin p => if (i : ℕ) = (I k : ℕ) then (1 : C) else 0) = 1 := by
      ext i k
      simp only [Matrix.of_apply, Matrix.one_apply, h k, Fin.val_inj]
    rw [this, Matrix.det_one]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    have hge : ∀ j : Fin p, (j : ℕ) ≤ (I j : ℕ) := fun j => by
      have := StrictMono.id_le (f := fun n : ℕ => if hn : n < p then (I ⟨n, hn⟩ : ℕ) + 0 else n + N) (by
        intro a b hab
        by_cases hb : b < p
        · have ha : a < p := lt_trans hab hb
          simp only [dif_pos ha, dif_pos hb, add_zero]
          exact I.strictMono (show (⟨a, ha⟩ : Fin p) < ⟨b, hb⟩ from hab)
        · simp only [dif_neg hb]
          by_cases ha : a < p
          · simp only [dif_pos ha, add_zero]
            have := (I ⟨a, ha⟩).2
            omega
          · simp only [dif_neg ha]; omega) j
      simpa [j.2] using this
    have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) k.2
    let last : Fin p := ⟨p - 1, by omega⟩
    have hlast : p ≤ (I last : ℕ) := by
      have h1 : (k : ℕ) < (I k : ℕ) := lt_of_le_of_ne (hge k) (Ne.symm hk)
      have h2 : ∀ n : ℕ, ∀ hn : (k : ℕ) + n < p, (I k : ℕ) + n ≤ (I ⟨k + n, hn⟩ : ℕ) := by
        intro n
        induction n with
        | zero => intro hn; simp
        | succ n ih =>
          intro hn
          have h3 := ih (by omega)
          have hlt : (I ⟨k + n, by omega⟩ : ℕ) < (I ⟨k + (n + 1), hn⟩ : ℕ) :=
            I.strictMono (show (⟨k + n, by omega⟩ : Fin p) < ⟨k + (n + 1), hn⟩ from by
              rw [Fin.lt_iff_val_lt_val]; simp)
          omega
      have h4 := h2 (p - 1 - k) (by omega)
      have e : (⟨k + (p - 1 - k), by omega⟩ : Fin p) = last := Fin.ext (by simp [last]; omega)
      rw [e] at h4
      omega
    refine Matrix.det_eq_zero_of_column_eq_zero last fun i => ?_
    simp only [Matrix.of_apply]
    rw [if_neg]
    have := i.2
    omega

end Det

section Eval

variable {Lt : Type} (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime]

def xS : Lt × ℕ × Fin N0 → ℂ_[l] := fun k => if k.2.1 = (k.2.2 : ℕ) then 1 else 0

def zS : Lt × Fin N0 × Fin N1 → ℂ_[l] := fun k => if (k.2.1 : ℕ) = (k.2.2 : ℕ) then 1 else 0

open Classical in

def ThE : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l] := fun μ =>
  if ∀ k ∈ μ.support, zS N0 N1 l k = 1 then (μ.prod fun _ n => (n.factorial : ℂ_[l]))⁻¹ else 0

open Classical in
theorem prod_ind {σ : Type} (t : σ → ℂ_[l]) (ht : ∀ k, t k = 0 ∨ t k = 1) (μ : σ →₀ ℕ) :
    (μ.prod fun k e => t k ^ e) = if ∀ k ∈ μ.support, t k = 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun k hk => by show t k ^ μ k = 1; rw [h k hk, one_pow]
  · push Not at h
    obtain ⟨k, hk, hne⟩ := h
    have h0 : t k = 0 := (ht k).resolve_right hne
    exact Finset.prod_eq_zero hk (by show t k ^ μ k = 0; rw [h0, zero_pow (Finsupp.mem_support_iff.mp hk)])

theorem fac_ne (μ : (Lt × Fin N0 × Fin N1) →₀ ℕ) : (μ.prod fun _ n => (n.factorial : ℂ_[l])) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

open Classical in
theorem fac_ThE (μ : (Lt × Fin N0 × Fin N1) →₀ ℕ) :
    (μ.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff μ (ThE N0 N1 l) =
      μ.prod fun k e => zS N0 N1 l k ^ e := by
  rw [prod_ind l (zS N0 N1 l) (fun k => by unfold zS; split_ifs <;> simp) μ]
  show _ * ThE N0 N1 l μ = _
  unfold ThE
  split_ifs
  · exact mul_inv_cancel₀ (fac_ne N0 N1 l μ)
  · exact mul_zero _

theorem eval_applyAt0 (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    MvPolynomial.eval (xS N0 l) (KM.applyAt0 N0 N1 l (ThE N0 N1 l) P) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l)) P := by
  unfold KM.applyAt0
  rw [map_sum, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  set e := Finsupp.sumFinsuppEquivProdFinsupp μ with he
  have hμ : μ = Finsupp.sumElim e.1 e.2 := by
    rw [he]
    ext k
    cases k <;> rfl
  have hprod : (∏ i ∈ μ.support, Sum.elim (xS N0 l) (zS N0 N1 l) i ^ μ i) =
      (e.1.prod fun k n => xS N0 l k ^ n) * (e.2.prod fun k n => zS N0 N1 l k ^ n) := by
    show μ.prod (fun i n => Sum.elim (xS N0 l) (zS N0 N1 l) i ^ n) = _
    conv_lhs => rw [hμ]
    rw [Finsupp.prod_sumElim]
    rfl
  rw [hprod, ← fac_ThE N0 N1 l e.2]
  simp only [eq_intCast, Int.cast_id]
  ring

theorem sum_xz {p : ℕ} (hp : p ≤ N0) (s : Lt) (i : Fin p) (b : Fin N1) :
    (∑ a : Fin N0, xS N0 l (s, (i : ℕ), a) * zS N0 N1 l (s, a, b)) = if (i : ℕ) = (b : ℕ) then 1 else 0 := by
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hp⟩]
  · simp [xS, zS]
  · intro a _ ha
    have : (i : ℕ) ≠ (a : ℕ) := fun h => ha (Fin.ext h.symm)
    simp [xS, this]
  · simp

variable [Fintype Lt] [DecidableEq Lt]

open Classical in
theorem eval_Gxz (nu : Lt → YoungDiagram) (hnu : ∀ s c, (nu s).colLen c ≤ N0) (I : KM.ColChoice N1 nu) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l)) (KM.Gxz N0 N1 nu I) =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (I s c k : ℕ) = k then 1 else 0 := by
  unfold KM.Gxz
  rw [← MvPolynomial.coe_eval₂Hom, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold KM.minorXZ
  have hM : (MvPolynomial.eval₂Hom (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l))).mapMatrix
      (Matrix.of fun i k : Fin ((nu s).colLen c) => ∑ a : Fin N0,
        MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I s c k))) =
      Matrix.of fun i k : Fin ((nu s).colLen c) => if (i : ℕ) = (I s c k : ℕ) then (1 : ℂ_[l]) else 0 := by
    ext i k
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, map_sum]
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    exact sum_xz N0 N1 l (hnu s c) s i (I s c k)
  rw [RingHom.map_det, hM, det_ind]

open Classical in
theorem eval_nablaX (nu : Lt → YoungDiagram) (J : KM.ColChoice N0 nu) :
    MvPolynomial.eval (xS N0 l) (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N0 nu J)) =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (J s c k : ℕ) = k then 1 else 0 := by
  rw [MvPolynomial.eval_map]
  unfold KM.nablaX
  rw [← MvPolynomial.coe_eval₂Hom, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, ← det_ind (C := ℂ_[l]) (J s c)]
  congr 1
  ext i k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, xS]

end Eval

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable (D : D7)

theorem intW_int (w : D.what₂.places.Pl) (r : 𝓞 D.what₂.LL) : (r : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)

theorem mem_locW_std (w : D.what₂.places.Pl) {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → D.what₂.LL) :
    x ∈ locW D.what₂.places w (stdHLat D.what₂.LL ι).L ↔ ∀ c, x c ∈ intW D.what₂.places w := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨k, rfl⟩ := hz
        intro c
        by_cases h : c = k
        · subst h; simp
        · simp [Pi.basisFun_apply, Pi.single_apply, h]
      | zero => intro c; simp
      | add a b _ _ ha hb => intro c; exact add_mem (ha c) (hb c)
      | smul r a _ ha => intro c; exact mul_mem (intW_int D w r) (ha c)
    | zero => intro c; simp
    | add a b _ _ ha hb => intro c; exact add_mem (ha c) (hb c)
    | smul r a _ ha => intro c; exact mul_mem r.2 (ha c)
  · intro h
    have hx : x = ∑ c, (⟨x c, h c⟩ : intW D.what₂.places w) • (Pi.basisFun D.what₂.LL ι c) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
      exact (mul_one _).symm
    rw [hx]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨c, rfl⟩))

end Gen

section Ind

open Classical in

def indC {Lt : Type} [Fintype Lt] {N : ℕ} (nu : Lt → YoungDiagram) (I : KM.ColChoice N nu) (C : Type) [CommRing C] : C :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (I s c k : ℕ) = k then 1 else 0

theorem indC_01 {Lt : Type} [Fintype Lt] {N : ℕ} (nu : Lt → YoungDiagram) (I : KM.ColChoice N nu) (C : Type) [CommRing C] :
    indC nu I C = 0 ∨ indC nu I C = 1 := by
  classical
  unfold indC
  refine Finset.prod_induction _ (fun x : C => x = 0 ∨ x = 1) (fun a b ha hb => ?_) (Or.inr rfl) fun s _ =>
    Finset.prod_induction _ (fun x : C => x = 0 ∨ x = 1) (fun a b ha hb => ?_) (Or.inr rfl) fun c _ => ?_
  · rcases ha with rfl | rfl <;> simp [hb]
  · rcases ha with rfl | rfl <;> simp [hb]
  · split_ifs <;> simp

def initC {Lt : Type} {N : ℕ} (nu : Lt → YoungDiagram) (h : ∀ s c, (nu s).colLen c ≤ N) : KM.ColChoice N nu :=
  fun s c => Fin.castLEOrderEmb (h s c)

theorem indC_init {Lt : Type} [Fintype Lt] {N : ℕ} (nu : Lt → YoungDiagram) (h : ∀ s c, (nu s).colLen c ≤ N)
    (C : Type) [CommRing C] : indC nu (initC nu h) C = 1 := by
  classical
  unfold indC
  refine Finset.prod_eq_one fun s _ => Finset.prod_eq_one fun c _ => ?_
  rw [if_pos fun k => by simp [initC]]

end Ind

theorem chainN_Kmap {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (i : ℕ)
    (c : K.cls i) (c' : K.cls (i + 1)) (φ : Unit → ℂ) : (chainN hc K).Kmap i c c' φ = φ := by
  funext y
  simp [ColumnChain.Kmap, ColumnChain.divDe, ColumnChain.sharp, mulFun]

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)

theorem row_nu_le (u : W) (i : ℕ) (j : ℕ) (hj : i ≤ j) :
    ∀ s c, (nuD DR u i s).colLen c ≤ R.N j := fun s c =>
  ((nuD DR u i s).colLen_anti 0 c (Nat.zero_le _)).trans ((nuD_rows DR u i s).trans
    (by show R.k + i * (R.t + 1) ≤ R.k + j * (R.t + 1); have := Nat.mul_le_mul_right (R.t + 1) hj; omega))

def levelRecordTwistEntries (P : EntPl DR) : KerEnt DR (levelRecordDivisor H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) (levelRecordTwistForms H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) where
  lam := P.lam
  iL := P.iL
  iL_lam := P.iL_lam
  iL_int := P.iL_int
  Th := fun _ _ w i _ _ => ThE (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w)
  VQ := fun _ _ _ _ => (DR).what₂.LL
  ev := fun _ _ _ _ =>
    { toFun := fun v _ => (DR).what₂.embLL v
      map_add' := fun a b => by funext _; simp
      map_smul' := fun a b => by funext _; simp }
  ev_inj := fun _ _ _ _ a b h => (DR).what₂.embLL.injective (congrFun h ())
  prS := fun _ _ w i _ =>
    { toFun := fun v => P.iL w v • (MvPolynomial.aeval (xS (R.N i) ((DR).what₂.places.resChar w))).toLinearMap
      map_add' := fun a b => by rw [map_add, add_smul]; rfl
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, mul_smul]; rfl }
  prT := fun u _ w i _ =>
    { toFun := fun v I => P.iL w v * indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w]
      map_add' := fun a b => by funext I; simp [add_mul]
      map_smul' := fun a b => by
        funext I
        show P.iL w (a * b) * _ = P.iL w a * (P.iL w b * _)
        rw [map_mul, mul_assoc] }
  prT_val := fun u _ w _ i _ _ v' I => by
    rcases indC_01 (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨v', by simp [h]⟩
  lat_S := by
    intro u μ w _ i _ φ
    have key : ∀ v : (DR).what₂.LL, (∀ J : KM.ColChoice (R.N i) (nuD DR u i),
        ‖P.iL w v * MvPolynomial.eval (xS (R.N i) ((DR).what₂.places.resChar w))
          (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (R.N i) (nuD DR u i) J))‖ ≤ 1) ↔
        v ∈ intW (DR).what₂.places w := fun v => by
      rw [P.iL_int]
      simp only [eval_nablaX]
      constructor
      · intro h
        have := h (initC (nuD DR u i) (row_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat u i i le_rfl))
        rwa [show (∏ s, ∏ c : Fin ((nuD DR u i s).rowLen 0), if ∀ k,
            ((initC (nuD DR u i) (row_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat u i i le_rfl)) s c k : ℕ) = k then (1 : ℂ_[(DR).what₂.places.resChar w])
            else 0) = 1 from indC_init (nuD DR u i) _ _, mul_one] at this
      · intro h J
        rcases indC_01 (nuD DR u i) J ℂ_[(DR).what₂.places.resChar w] with h0 | h0 <;>
          · unfold indC at h0
            rw [h0]
            simpa using h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_locW_std DR w (ι := (K u).cls i) x).mp hx
      refine ⟨trivial, fun c => ⟨x c, rfl, fun J => ?_⟩⟩
      have := (key (x c)).mpr (hx' c) J
      rwa [← MvPolynomial.coe_aeval_eq_eval] at this
    · rintro ⟨-, h⟩
      choose v hv1 hv2 using h
      refine ⟨v, (mem_locW_std DR w (ι := (K u).cls i) v).mpr fun c => (key (v c)).mp fun J => ?_, ?_⟩
      · have := hv2 c J
        rwa [← MvPolynomial.coe_aeval_eq_eval]
      · funext c y
        exact congrFun (hv1 c) y
  levelFree_lattice_condition := by
    intro u μ w _ i _ φ
    have key : ∀ v : (DR).what₂.LL, (∀ I : KM.ColChoice (R.N (i + 1)) (nuD DR u i),
        ‖P.iL w v * indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w]‖ ≤ 1) ↔
        v ∈ intW (DR).what₂.places w := fun v => by
      rw [P.iL_int]
      constructor
      · intro h
        have := h (initC (nuD DR u i) (row_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat u i (i + 1) (Nat.le_succ i)))
        rwa [indC_init, mul_one] at this
      · intro h I
        rcases indC_01 (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] with h0 | h0 <;>
          · rw [h0]
            simpa using h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_locW_std DR w (ι := (K u).cls (i + 1)) x).mp hx
      exact ⟨trivial, fun c => ⟨x c, rfl, (key (x c)).mpr (hx' c)⟩⟩
    · rintro ⟨-, h⟩
      choose v hv1 hv2 using h
      refine ⟨v, (mem_locW_std DR w (ι := (K u).cls (i + 1)) v).mpr fun c => (key (v c)).mp (hv2 c), ?_⟩
      funext c y
      exact congrFun (hv1 c) y
  un := fun _ _ _ _ _ _ => 1
  un_ne := fun _ _ _ _ _ _ => one_ne_zero
  kform := by
    intro u μ w _ i _ c c' v v' hvv I
    have h3 : ((DR).chTw u μ).Kmap i c c' (fun _ => (DR).what₂.embLL v) = fun _ => (DR).what₂.embLL v :=
      chainN_Kmap (hcW u) (K u) i c c' _
    have h4 : (DR).what₂.embLL v' = ((DR).chTw u μ).Kmap i c c' (fun _ => (DR).what₂.embLL v) () := congrFun hvv ()
    have h2 : (DR).what₂.embLL v' = (DR).what₂.embLL v := by rw [h4, h3]
    have hv' : v' = v := (DR).what₂.embLL.injective h2
    subst hv'
    have e1 : MvPolynomial.aeval (xS (R.N i) ((DR).what₂.places.resChar w))
        (KM.applyAt0 (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w) (ThE (R.N i) (R.N (i + 1)) _)
          (KM.Gxz (R.N i) (R.N (i + 1)) (nuD DR u i) I)) = indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] := by
      change MvPolynomial.eval (xS (R.N i) ((DR).what₂.places.resChar w)) _ = _
      rw [eval_applyAt0]
      erw [eval_Gxz _ _ _ _ (row_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat u i i le_rfl)]
      rfl
    show P.iL w v' * indC (nuD DR u i) I _ = 1 * (P.iL w v' * MvPolynomial.aeval (xS (R.N i)
      ((DR).what₂.places.resChar w)) (KM.applyAt0 (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w)
        (ThE (R.N i) (R.N (i + 1)) _) (KM.Gxz (R.N i) (R.N (i + 1)) (nuD DR u i) I)))
    rw [e1, one_mul]


end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end
