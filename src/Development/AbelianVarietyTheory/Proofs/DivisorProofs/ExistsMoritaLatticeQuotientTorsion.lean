import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff

section
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.MatRed

theorem approx {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ) (x : M ⊗[ℤ] ℤ_[p]) :
    ∃ (b : M) (y : M ⊗[ℤ] ℤ_[p]), x = b ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul o z =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec r z)
    refine ⟨(z.appr r) • o, o ⊗ₜ w, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    congr 1
    rw [nsmul_eq_mul, nsmul_eq_mul, _root_.mul_one]
    push_cast
    linear_combination hw
  | add x y hx hy =>
    obtain ⟨a, u, ha⟩ := hx
    obtain ⟨b, v, hb⟩ := hy
    exact ⟨a + b, u + v, by rw [ha, hb, TensorProduct.add_tmul, smul_add]; abel⟩

theorem dvd_of_tmul {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (r : ℕ) (u : M) (z : M ⊗[ℤ] ℤ_[p]) (h : u ⊗ₜ (1 : ℤ_[p]) = (p ^ r) • z) :
    ∃ v : M, u = (p ^ r) • v := by
  let bs := Module.Free.chooseBasis ℤ M
  have hd : ∀ i, ((p ^ r : ℕ) : ℤ) ∣ bs.repr u i := by
    intro i
    let φ : M ⊗[ℤ] ℤ_[p] →ₗ[ℤ] ℤ_[p] :=
      (TensorProduct.lid ℤ ℤ_[p]).toLinearMap ∘ₗ TensorProduct.map (bs.coord i) LinearMap.id
    have h1 : φ (u ⊗ₜ (1 : ℤ_[p])) = ((bs.repr u i : ℤ) : ℤ_[p]) := by
      show (TensorProduct.lid ℤ ℤ_[p]) (TensorProduct.map (bs.coord i) LinearMap.id (u ⊗ₜ[ℤ] (1 : ℤ_[p]))) = _
      rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
      simp [zsmul_eq_mul]
    rw [h, map_nsmul] at h1
    have h2 := congrArg (PadicInt.toZModPow (p := p) r) h1
    rw [map_nsmul, map_intCast] at h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← h2, nsmul_eq_mul]
    simp
  choose k hk using hd
  refine ⟨∑ i, k i • bs i, ?_⟩
  conv_lhs => rw [← bs.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk i, mul_smul, natCast_zsmul]

theorem mem_smul_top_map {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) (f : X →ₗ[R] Y) {x : X} (hx : x ∈ I • (⊤ : Submodule R X)) :
    f x ∈ I • (⊤ : Submodule R Y) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem exists_matRed : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  intro p _ D w0 r _ hp
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e⟩ := D.splitP
  have hpr : (p : 𝓞 D.F) ^ r ∈ w0 ^ r := Ideal.pow_mem_pow hp r
  have hA : ((p ^ r : ℕ) : 𝓞 D.F ⧸ w0 ^ r) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.2 hpr
    simpa using h
  let ψ₀ : ℤ_[p] →+* 𝓞 D.F ⧸ w0 ^ r :=
    (ZMod.castHom (ringChar.dvd hA) (𝓞 D.F ⧸ w0 ^ r)).comp (PadicInt.toZModPow r)
  let ψ : 𝓞 D.F ⊗[ℤ] ℤ_[p] →ₐ[𝓞 D.F] 𝓞 D.F ⧸ w0 ^ r :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ (𝓞 D.F) (w0 ^ r)) ψ₀.toIntAlgHom
      (fun _ _ => Commute.all _ _)
  have hψ : ∀ c, ψ (c ⊗ₜ (1 : ℤ_[p])) = Ideal.Quotient.mk _ c := by
    intro c; simp [ψ, Algebra.TensorProduct.lift_tmul]
  have hψk : ∀ y, ψ y = 0 → y ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    intro y hy
    obtain ⟨c, z, rfl⟩ := approx r y
    rw [map_add, map_nsmul, hψ, nsmul_eq_mul, hA, zero_mul, add_zero] at hy
    have hc : c ∈ w0 ^ r := Ideal.Quotient.eq_zero_iff_mem.1 hy
    have h1 : c ⊗ₜ[ℤ] (1 : ℤ_[p]) = c • (1 : 𝓞 D.F ⊗[ℤ] ℤ_[p]) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (p ^ r) • z = ((p : 𝓞 D.F) ^ r) • z := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [h1, h2]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc trivial) (Submodule.smul_mem_smul hpr trivial)
  let incl : D.O →ₐ[𝓞 D.F] D.O ⊗[ℤ] ℤ_[p] := Algebra.TensorProduct.includeLeft
  have hincl : ∀ b, incl b = b ⊗ₜ (1 : ℤ_[p]) := fun b => rfl
  refine ⟨ψ.mapMatrix.comp (e.toAlgHom.comp incl), ?_, ?_⟩
  · intro N
    choose c hc using fun i j => Ideal.Quotient.mk_surjective (N i j)
    obtain ⟨b, y, hby⟩ := approx (M := D.O) r (e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])))
    refine ⟨b, ?_⟩
    have hb : incl b = e.symm (Matrix.of fun i j => c i j ⊗ₜ (1 : ℤ_[p])) - (p ^ r) • y := by
      rw [hby, hincl]; abel
    show ψ.mapMatrix (e (incl b)) = N
    rw [hb, map_sub, map_sub, map_nsmul, map_nsmul, e.apply_symm_apply]
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, nsmul_eq_mul, hA, zero_mul, sub_zero]
    simp [AlgHom.mapMatrix_apply, hψ, hc]
  · intro b hb
    have hb' : ∀ i j, ψ (e (incl b) i j) = 0 := fun i j => by
      have h := congrFun (congrFun hb i) j
      simpa [AlgHom.mapMatrix_apply] using h
    have hM : e (incl b) ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]))) := by
      rw [Matrix.matrix_eq_sum_single (e (incl b))]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      exact mem_smul_top_map _ (Matrix.singleLinearMap (𝓞 D.F) i j) (hψk _ (hb' i j))
    have hO : incl b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])) := by
      have h := mem_smul_top_map _ e.symm.toLinearEquiv.toLinearMap hM
      simpa using h
    have claim : ∀ x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p])),
        ∃ b' ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O), ∃ z : D.O ⊗[ℤ] ℤ_[p],
          x = b' ⊗ₜ (1 : ℤ_[p]) + (p ^ r) • z := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro c hc x _
        obtain ⟨bx, y, rfl⟩ := approx r x
        refine ⟨c • bx, Submodule.smul_mem_smul hc trivial, c • y, ?_⟩
        rw [smul_add, TensorProduct.smul_tmul', smul_comm]
      · rintro x y ⟨a, ha, u, rfl⟩ ⟨a', ha', v, rfl⟩
        exact ⟨a + a', add_mem ha ha', u + v, by rw [TensorProduct.add_tmul, smul_add]; abel⟩
    obtain ⟨b', hb'', z, hz⟩ := claim _ hO
    rw [hincl] at hz
    have h3 : (b - b') ⊗ₜ[ℤ] (1 : ℤ_[p]) = (p ^ r) • z := by
      rw [TensorProduct.sub_tmul, hz]; abel
    obtain ⟨v, hv⟩ := dvd_of_tmul r (b - b') z h3
    have h4 : b = b' + ((p : 𝓞 D.F) ^ r) • v := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← hv]; abel
    rw [h4]
    exact add_mem hb'' (Submodule.smul_mem_smul hpr trivial)

end GlobalTheory.UPel.HT.MatRed
end
end

section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.MatRed.exists_matRed) | (exact GlobalTheory.UPel.HT.MatRed.exists_matRed) | (intros; apply GlobalTheory.UPel.HT.MatRed.exists_matRed <;> assumption)
end

section
namespace GlobalTheory.Morita

structure MatrixUnits (R : Type*) [CommRing R] (N : Type*) [AddCommGroup N] [Module R N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where

  E : ι → ι → Module.End R N
  mul_eq : ∀ i j k l, E i j * E k l = if j = k then E i l else 0
  sum_diag : ∑ i, E i i = 1

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MatrixUnits

variable (U : MatrixUnits R N ι)

theorem apply_apply (i j k l : ι) (x : N) : U.E i j (U.E k l x) = if j = k then U.E i l x else 0 := by
  have h := LinearMap.congr_fun (U.mul_eq i j k l) x
  rw [Module.End.mul_apply] at h
  rw [h]; split_ifs <;> simp

theorem sum_apply (x : N) : ∑ i, U.E i i x = x := by
  have h := LinearMap.congr_fun U.sum_diag x
  simpa [LinearMap.sum_apply] using h

def corner (a : ι) : Submodule R N := LinearMap.range (U.E a a)

theorem mem_corner_iff (a : ι) (x : N) : x ∈ U.corner a ↔ U.E a a x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [U.apply_apply]; simp
  · intro h; exact ⟨x, h⟩

theorem apply_mem_corner (a i : ι) (x : N) : U.E a i x ∈ U.corner a := ⟨U.E a i x, by rw [U.apply_apply]; simp⟩

def toPi (a : ι) : N ≃ₗ[R] (ι → U.corner a) where
  toFun x i := ⟨U.E a i x, U.apply_mem_corner a i x⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  invFun v := ∑ i, U.E i a (v i)
  left_inv x := by
    simp only
    conv_rhs => rw [← U.sum_apply x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U.apply_apply]; simp
  right_inv v := by
    ext j
    simp only [map_sum, U.apply_apply]
    simp [(U.mem_corner_iff a _).1 (v j).2]

theorem toPi_apply (a : ι) (x : N) (i : ι) : ((U.toPi a x) i : N) = U.E a i x := rfl

theorem toPi_symm_apply (a : ι) (v : ι → U.corner a) : (U.toPi a).symm v = ∑ i, U.E i a (v i) := rfl

theorem toPi_E (a i j : ι) (x : N) : U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j) := by
  ext k
  rw [toPi_apply, U.apply_apply]
  by_cases h : k = i
  · subst h; simp [toPi_apply]
  · simp [h, Pi.single_apply]

end MatrixUnits

def stdUnits (M : Type*) [AddCommGroup M] [Module R M] : MatrixUnits R (ι → M) ι where
  E i j := LinearMap.single R (fun _ => M) i ∘ₗ LinearMap.proj j
  mul_eq i j k l := by
    ext x m
    by_cases h : j = k
    · subst h; simp [Pi.single_apply]
    · simp [h, Pi.single_apply]
  sum_diag := by
    ext x m
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def ofModule [Module (Matrix ι ι R) N] [IsScalarTower R (Matrix ι ι R) N] : MatrixUnits R N ι where
  E i j := Algebra.lsmul R R N (Matrix.single i j (1 : R))
  mul_eq i j k l := by
    rw [← map_mul]
    by_cases h : j = k
    · subst h; rw [Matrix.single_mul_single_same]; simp
    · rw [Matrix.single_mul_single_of_ne (h := h)]; simp [h]
  sum_diag := by
    rw [← map_sum, Matrix.sum_single_one, map_one]

end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem toPi_corner (a : ι) (y : U.corner a) : U.toPi a y = Pi.single a y := by
  ext i
  rw [toPi_apply, ← (U.mem_corner_iff a _).1 y.2, U.apply_apply]
  by_cases h : i = a
  · subst h; simp [(U.mem_corner_iff i _).1 y.2]
  · simp [h, Pi.single_apply, Ne.symm h]

def IsStable (L : Submodule R N) : Prop := ∀ i j, ∀ x ∈ L, U.E i j x ∈ L

def cornerPart (a : ι) (L : Submodule R N) : Submodule R (U.corner a) := L.comap (U.corner a).subtype

def spread (a : ι) (L₀ : Submodule R (U.corner a)) : Submodule R N :=
  (Submodule.pi Set.univ fun _ => L₀).comap (U.toPi a).toLinearMap

theorem mem_cornerPart {a : ι} {L : Submodule R N} {y : U.corner a} : y ∈ U.cornerPart a L ↔ (y : N) ∈ L :=
  Iff.rfl

theorem mem_spread {a : ι} {L₀ : Submodule R (U.corner a)} {x : N} :
    x ∈ U.spread a L₀ ↔ ∀ i, U.toPi a x i ∈ L₀ := by
  simp [spread, Submodule.mem_pi]

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem mem_of_forall {L : Submodule R N} (hL : U.IsStable L) (a : ι) {x : N} (h : ∀ i, U.E a i x ∈ L) : x ∈ L := by
  rw [← (U.toPi a).symm_apply_apply x, toPi_symm_apply]
  exact L.sum_mem fun i _ => hL i a _ (h i)

theorem spread_isStable (a : ι) (L₀ : Submodule R (U.corner a)) : U.IsStable (U.spread a L₀) := by
  intro i j x hx
  rw [mem_spread] at hx ⊢
  intro k
  rw [toPi_E]
  by_cases h : k = i
  · subst h; simpa using hx j
  · simp [Pi.single_apply, h, L₀.zero_mem]

theorem cornerPart_spread (a : ι) (L₀ : Submodule R (U.corner a)) : U.cornerPart a (U.spread a L₀) = L₀ := by
  ext y
  rw [mem_cornerPart, mem_spread, toPi_corner]
  constructor
  · intro h; simpa using h a
  · intro h i
    by_cases hi : i = a
    · subst hi; simpa using h
    · simp [Pi.single_apply, hi, L₀.zero_mem]

theorem spread_cornerPart {L : Submodule R N} (hL : U.IsStable L) (a : ι) : U.spread a (U.cornerPart a L) = L := by
  ext x
  rw [mem_spread]
  constructor
  · intro h; exact U.mem_of_forall hL a fun i => h i
  · intro h i; exact hL a i x h

def latIso (a : ι) : {L : Submodule R N // U.IsStable L} ≃o Submodule R (U.corner a) where
  toFun L := U.cornerPart a L.1
  invFun L₀ := ⟨U.spread a L₀, U.spread_isStable a L₀⟩
  left_inv L := Subtype.ext (U.spread_cornerPart L.2 a)
  right_inv L₀ := U.cornerPart_spread a L₀
  map_rel_iff' {L L'} := by
    constructor
    · intro h
      show L.1 ≤ L'.1
      rw [← U.spread_cornerPart L.2 a, ← U.spread_cornerPart L'.2 a]
      intro x hx
      rw [mem_spread] at hx ⊢
      exact fun i => h (hx i)
    · intro h y hy; exact h hy



theorem map_toPi {L : Submodule R N} (hL : U.IsStable L) (a : ι) :
    L.map (U.toPi a).toLinearMap = Submodule.pi Set.univ fun _ => U.cornerPart a L := by
  conv_lhs => rw [← U.spread_cornerPart hL a]
  rw [spread, Submodule.map_comap_eq_of_surjective (U.toPi a).surjective]

def partEquiv {L : Submodule R N} (hL : U.IsStable L) (a : ι) : L ≃ₗ[R] (ι → U.cornerPart a L) where
  toFun x i := ⟨U.toPi a x i, hL a i x x.2⟩
  map_add' x y := by ext i; simp [toPi_apply]
  map_smul' r x := by ext i; simp [toPi_apply]
  invFun v := ⟨(U.toPi a).symm fun i => (v i : U.corner a), by
    rw [toPi_symm_apply]; exact L.sum_mem fun i _ => hL i a _ (v i).2⟩
  left_inv x := by ext1; simp
  right_inv v := by ext i; simp

theorem smul_mem_iff {L L' : Submodule R N} (hL : U.IsStable L) (hL' : U.IsStable L') (a : ι) (r : R) :
    (∀ x ∈ L, r • x ∈ L') ↔ ∀ y ∈ U.cornerPart a L, r • y ∈ U.cornerPart a L' := by
  constructor
  · intro h y hy; exact h _ hy
  · intro h x hx
    refine U.mem_of_forall hL' a fun i => ?_
    rw [map_smul]
    exact h ⟨U.E a i x, U.apply_mem_corner a i x⟩ (hL a i x hx)

section semilinear

variable {σ : R →+* R} (F : N →ₛₗ[σ] N)

def cornerMap (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) : U.corner a →ₛₗ[σ] U.corner a :=
  (F.domRestrict (U.corner a)).codRestrict (U.corner a) fun y => by
    rw [U.mem_corner_iff]
    simp only [LinearMap.domRestrict_apply]
    rw [← hF, (U.mem_corner_iff a _).1 y.2]

theorem cornerMap_apply (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) (y : U.corner a) :
    (U.cornerMap F a hF y : N) = F y := rfl

theorem toPi_map (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) (x : N) :
    U.toPi a (F x) = fun i => U.cornerMap F a hF (U.toPi a x i) := by
  ext i; simp [toPi_apply, cornerMap_apply, hF]

theorem map_mem_iff (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) {L : Submodule R N} (hL : U.IsStable L) :
    (∀ x ∈ L, F x ∈ L) ↔ ∀ y ∈ U.cornerPart a L, U.cornerMap F a hF y ∈ U.cornerPart a L := by
  constructor
  · intro h y hy; exact h _ hy
  · intro h x hx
    refine U.mem_of_forall hL a fun i => ?_
    rw [← hF]
    exact h ⟨U.E a i x, U.apply_mem_corner a i x⟩ (hL a i x hx)

theorem isStable_span_image (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) {L : Submodule R N} (hL : U.IsStable L) :
    U.IsStable (Submodule.span R (F '' L)) := by
  intro i j
  have : Submodule.span R (F '' L) ≤ (Submodule.span R (F '' L)).comap (U.E i j) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [← hF]
    exact Submodule.subset_span ⟨_, hL i j x hx, rfl⟩
  exact fun x hx => this hx

theorem cornerPart_span_image (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) {L : Submodule R N}
    (hL : U.IsStable L) :
    U.cornerPart a (Submodule.span R (F '' L)) =
      Submodule.span R (U.cornerMap F a hF '' U.cornerPart a L) := by
  apply le_antisymm
  · intro y hy
    have key : (Submodule.span R (F '' L)).map (U.E a a) ≤
        (Submodule.span R (U.cornerMap F a hF '' U.cornerPart a L)).map (U.corner a).subtype := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨U.cornerMap F a hF ⟨U.E a a x, U.apply_mem_corner a a x⟩,
        Submodule.subset_span ⟨_, hL a a x hx, rfl⟩, ?_⟩
      simp [cornerMap_apply, hF]
    obtain ⟨z, hz, hzy⟩ := key ⟨(y : N), hy, (U.mem_corner_iff a _).1 y.2⟩
    have : z = y := Subtype.ext hzy
    rwa [← this]
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end semilinear

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem map_partEquiv_comap {L L' : Submodule R N} (hL : U.IsStable L) (hL' : U.IsStable L') (a : ι) :
    (L'.comap L.subtype).map (U.partEquiv hL a).toLinearMap =
      Submodule.pi Set.univ fun _ => (U.cornerPart a L').comap (U.cornerPart a L).subtype := by
  ext v
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
    Submodule.subtype_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact hL' a i x hx
  · intro h
    refine ⟨(U.partEquiv hL a).symm v, ?_, by simp⟩
    refine U.mem_of_forall hL' a fun i => ?_
    have := h i
    have e : ((U.partEquiv hL a) ((U.partEquiv hL a).symm v) i : N) = U.E a i ((U.partEquiv hL a).symm v : N) := rfl
    rw [LinearEquiv.apply_symm_apply] at e
    rw [← e]; exact this

theorem length_quotient {L L' : Submodule R N} (hL : U.IsStable L) (hL' : U.IsStable L') (a : ι) :
    Module.length R (L ⧸ L'.comap L.subtype) =
      Fintype.card ι * Module.length R (U.cornerPart a L ⧸ (U.cornerPart a L').comap (U.cornerPart a L).subtype) := by
  rw [(Submodule.Quotient.equiv _ _ (U.partEquiv hL a) (U.map_partEquiv_comap hL hL' a)).length_eq,
    (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem fg_iff {L : Submodule R N} (hL : U.IsStable L) (a : ι) :
    L.FG ↔ (U.cornerPart a L).FG := by
  rw [← Module.Finite.iff_fg, ← Module.Finite.iff_fg]
  constructor
  · intro h
    have : Module.Finite R (ι → U.cornerPart a L) := Module.Finite.equiv (U.partEquiv hL a)
    exact Module.Finite.of_surjective (LinearMap.proj a : (ι → U.cornerPart a L) →ₗ[R] _)
      (fun y => ⟨Pi.single a y, by simp⟩)
  · intro h
    exact Module.Finite.equiv (U.partEquiv hL a).symm

theorem dense_iff {L : Submodule R N} (hL : U.IsStable L) (a : ι) :
    (∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L) ↔
      ∀ y : U.corner a, ∃ r ∈ nonZeroDivisors R, r • y ∈ U.cornerPart a L := by
  constructor
  · intro h y
    obtain ⟨r, hr, hx⟩ := h y
    exact ⟨r, hr, hx⟩
  · intro h x
    choose r hr hrx using fun i => h (U.toPi a x i)
    refine ⟨∏ i, r i, prod_mem fun i _ => hr i, U.mem_of_forall hL a fun i => ?_⟩
    rw [map_smul]
    have e : (∏ j, r j) = (∏ j ∈ Finset.univ.erase i, r j) * r i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [e, mul_smul]
    exact L.smul_mem _ (hrx i)

theorem toPi_E_std (a i j : ι) (x : N) :
    U.toPi a (U.E i j x) = (stdUnits (R := R) (U.corner a)).E i j (U.toPi a x) := by
  rw [toPi_E]; ext k; simp [stdUnits, Pi.single_apply]

section extend

variable {σ : R →+* R}

def extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) : N →ₛₗ[σ] N where
  toFun x := ∑ i, U.E i a (F₀ (U.toPi a x i))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

theorem toPi_extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) (x : N) :
    U.toPi a (U.extend a F₀ x) = fun i => F₀ (U.toPi a x i) := by
  rw [show U.extend a F₀ x = (U.toPi a).symm (fun i => F₀ (U.toPi a x i)) from rfl,
    LinearEquiv.apply_symm_apply]

theorem extend_comm (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) :
    ∀ i j x, U.extend a F₀ (U.E i j x) = U.E i j (U.extend a F₀ x) := by
  intro i j x
  apply (U.toPi a).injective
  rw [toPi_extend, toPi_E, toPi_E, toPi_extend]
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem cornerMap_extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) :
    U.cornerMap (U.extend a F₀) a (U.extend_comm a F₀) = F₀ := by
  ext y
  rw [cornerMap_apply]
  apply (U.toPi a).injective
  rw [toPi_extend, toPi_corner, toPi_corner]
  funext k
  by_cases h : k = a
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem extend_cornerMap (a : ι) (F : N →ₛₗ[σ] N) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) :
    U.extend a (U.cornerMap F a hF) = F := by
  ext x
  apply (U.toPi a).injective
  rw [toPi_extend, U.toPi_map F a hF]

def semilinearEquiv (a : ι) :
    {F : N →ₛₗ[σ] N // ∀ i j x, F (U.E i j x) = U.E i j (F x)} ≃ (U.corner a →ₛₗ[σ] U.corner a) where
  toFun F := U.cornerMap F.1 a F.2
  invFun F₀ := ⟨U.extend a F₀, U.extend_comm a F₀⟩
  left_inv F := Subtype.ext (U.extend_cornerMap a F.1 F.2)
  right_inv F₀ := U.cornerMap_extend a F₀

end extend

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def stdCornerEquiv (M : Type*) [AddCommGroup M] [Module R M] (a : ι) :
    (stdUnits (R := R) (ι := ι) M).corner a ≃ₗ[R] M where
  toFun v := (v : ι → M) a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨Pi.single a m, (MatrixUnits.mem_corner_iff _ _ _).2 (by ext i; simp [stdUnits, Pi.single_apply])⟩
  left_inv v := by
    have h := ((stdUnits (R := R) (ι := ι) M).mem_corner_iff a v).1 v.2
    apply Subtype.ext
    conv_rhs => rw [← h]
    ext i; simp [stdUnits]
  right_inv m := by simp

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

theorem span_eq_top_iff_dense (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Module K N]
    [IsScalarTower R K N] (L : Submodule R N) :
    Submodule.span K (L : Set N) = ⊤ ↔ ∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L := by
  haveI : Nontrivial R := nontrivial_of_ne 0 1 fun h => by
    have := congrArg (algebraMap R K) h; simp at this
  constructor
  · intro h x
    have hx : x ∈ Submodule.span K (L : Set N) := h ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨r, hr, hry⟩ := hy
      obtain ⟨s, hs, hsz⟩ := hz
      refine ⟨r * s, mul_mem hr hs, ?_⟩
      rw [smul_add]
      refine L.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact L.smul_mem _ hry
      · rw [mul_smul]; exact L.smul_mem _ hsz
    | smul k y _ hy =>
      obtain ⟨r, hr, hry⟩ := hy
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hB : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
        field_simp
      have e : (b * r) • ((algebraMap R K a / algebraMap R K b) • y) = a • (r • y) := by
        rw [mul_comm b r, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul, smul_comm]
      exact ⟨b * r, mul_mem hb hr, e ▸ L.smul_mem a hry⟩
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hr, hx⟩ := h x
    have hB : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
    have e : x = (algebraMap R K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hB, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

end GlobalTheory.Morita

universe w

namespace GlobalTheory.Morita

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

open MatrixUnits in

theorem morita_lattices (U : MatrixUnits R N ι) (a : ι) {σ : R →+* R} (F : N →ₛₗ[σ] N)
    (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) :
    (∀ i j x, U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j)) ∧
    (∀ L : Submodule R N, U.IsStable L → U.spread a (U.cornerPart a L) = L) ∧
    (∀ L₀ : Submodule R (U.corner a), U.IsStable (U.spread a L₀) ∧ U.cornerPart a (U.spread a L₀) = L₀) ∧
    (∀ L : Submodule R N, U.IsStable L →
      Nonempty (L ≃ₗ[R] (ι → U.cornerPart a L)) ∧
      L.map (U.toPi a).toLinearMap = Submodule.pi Set.univ fun _ => U.cornerPart a L) ∧
    (∀ x, U.toPi a (F x) = fun i => U.cornerMap F a hF (U.toPi a x i)) ∧
    (∀ L : Submodule R N, U.IsStable L →
      ((∀ x ∈ L, F x ∈ L) ↔ ∀ y ∈ U.cornerPart a L, U.cornerMap F a hF y ∈ U.cornerPart a L) ∧
      U.IsStable (Submodule.span R (F '' L)) ∧
      U.cornerPart a (Submodule.span R (F '' L)) = Submodule.span R (U.cornerMap F a hF '' U.cornerPart a L)) ∧
    (∀ L L' : Submodule R N, U.IsStable L → U.IsStable L' →
      (∀ r : R, (∀ x ∈ L, r • x ∈ L') ↔ ∀ y ∈ U.cornerPart a L, r • y ∈ U.cornerPart a L') ∧
      Module.length R (L ⧸ L'.comap L.subtype) =
        Fintype.card ι * Module.length R (U.cornerPart a L ⧸ (U.cornerPart a L').comap (U.cornerPart a L).subtype)) ∧
    (∀ i j x, U.toPi a (U.E i j x) = (stdUnits (R := R) (U.corner a)).E i j (U.toPi a x)) ∧
    (∀ L : Submodule R N, U.IsStable L →
      (L.FG ↔ (U.cornerPart a L).FG) ∧
      ((∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L) ↔
        ∀ y : U.corner a, ∃ r ∈ nonZeroDivisors R, r • y ∈ U.cornerPart a L)) ∧
    (∀ (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K] [Module K N] [IsScalarTower R K N]
      (L : Submodule R N), Submodule.span K (L : Set N) = ⊤ ↔ ∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L) ∧
    (∃ e : {G : N →ₛₗ[σ] N // ∀ i j x, G (U.E i j x) = U.E i j (G x)} ≃ (U.corner a →ₛₗ[σ] U.corner a),
      ∀ G, e G = U.cornerMap G.1 a G.2) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module R M],
      ∃ e : (stdUnits (R := R) (ι := ι) M).corner a ≃ₗ[R] M, ∀ v, e v = (v : ι → M) a) :=
  ⟨fun i j x => U.toPi_E a i j x, fun _ hL => U.spread_cornerPart hL a,
    fun L₀ => ⟨U.spread_isStable a L₀, U.cornerPart_spread a L₀⟩,
    fun _ hL => ⟨⟨U.partEquiv hL a⟩, U.map_toPi hL a⟩, fun x => U.toPi_map F a hF x,
    fun _ hL => ⟨U.map_mem_iff F a hF hL, U.isStable_span_image F hF hL, U.cornerPart_span_image F a hF hL⟩,
    fun _ _ hL hL' => ⟨fun r => U.smul_mem_iff hL hL' a r, U.length_quotient hL hL' a⟩,
    fun i j x => U.toPi_E_std a i j x, fun _ hL => ⟨U.fg_iff hL a, U.dense_iff hL a⟩,
    fun K _ _ _ _ _ L => span_eq_top_iff_dense K L, ⟨U.semilinearEquiv a, fun _ => rfl⟩,
    fun M _ _ => ⟨stdCornerEquiv M a, fun _ => rfl⟩⟩

example : (Pi.single 0 1 : Fin 2 → ℤ) ∈ (stdUnits (R := ℤ) (ι := Fin 2) ℤ).corner 0 ∧ (Pi.single 0 1 : Fin 2 → ℤ) ≠ 0 := by
  refine ⟨(MatrixUnits.mem_corner_iff _ _ _).2 ?_, ?_⟩
  · ext i; fin_cases i <;> simp [stdUnits]
  · intro h; have := congrFun h 0; simp at this

end GlobalTheory.Morita
end

section
namespace GlobalTheory.MoritaLocal

open GlobalTheory.Morita

theorem smul_eq_zero_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (e : M ≃ₗ[R] (Fin n → R ⧸ I)) {c : R} (hc : c ∈ I) (x : M) : c • x = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  funext i
  simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hc]

theorem corner_equiv {R : Type} [CommRing R] (I : Ideal R) (hI : IsLocalRing (R ⧸ I)) {m k : ℕ} (hm : 0 < m)
    (C : Type) [AddCommGroup C] [Module R C] (e : (Fin m → C) ≃ₗ[R] (Fin (m * k) → R ⧸ I)) :
    Nonempty (C ≃ₗ[R] (Fin k → R ⧸ I)) := by
  have hC : Module.IsTorsionBySet R C I := by
    intro x a
    have h := congrFun (smul_eq_zero_of_equiv I e a.2 (Pi.single (⟨0, hm⟩ : Fin m) x)) ⟨0, hm⟩
    simpa using h
  letI : Module (R ⧸ I) C := hC.module
  haveI : IsScalarTower R (R ⧸ I) C := hC.isScalarTower
  let e' : (Fin m → C) ≃ₗ[R ⧸ I] (Fin (m * k) → R ⧸ I) :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e
  haveI : Module.Finite (R ⧸ I) (Fin m → C) := Module.Finite.equiv e'.symm
  haveI : Module.Free (R ⧸ I) (Fin m → C) := Module.Free.of_equiv e'.symm
  let i0 : C →ₗ[R ⧸ I] (Fin m → C) := LinearMap.single (R ⧸ I) (fun _ => C) ⟨0, hm⟩
  let p0 : (Fin m → C) →ₗ[R ⧸ I] C := LinearMap.proj ⟨0, hm⟩
  haveI : Module.Projective (R ⧸ I) C := Module.Projective.of_split i0 p0 (by ext x; simp [i0, p0])
  haveI : Module.Finite (R ⧸ I) C := Module.Finite.of_surjective p0 (fun x => ⟨Pi.single ⟨0, hm⟩ x, by simp [p0]⟩)
  haveI : Module.Free (R ⧸ I) C := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank (R ⧸ I) (Fin m → C) = m * k := by
    rw [e'.finrank_eq, Module.finrank_fin_fun]
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 : Module.finrank (R ⧸ I) C = k := Nat.eq_of_mul_eq_mul_left hm h1
  exact ⟨(LinearEquiv.ofFinrankEq C (Fin k → R ⧸ I) (by rw [h2, Module.finrank_fin_fun])).restrictScalars R⟩

section
variable {R : Type} [CommRing R] {I : Ideal R} {m : ℕ} {O : Type} [Ring O] [Algebra R O]
  {φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)}
  {P : Type} [AddCommGroup P] [Module O P] [Module R P] [IsScalarTower R O P]

theorem act_congr (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    {b b' : O} (h : φ b = φ b') (x : P) : b • x = b' • x := by
  have hb : b - b' ∈ I • (⊤ : Submodule R O) := hker _ (by rw [map_sub, h, sub_self])
  have key : ∀ y ∈ I • (⊤ : Submodule R O), y • x = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro c hc o _
      rw [smul_assoc, hP c hc]
    · intro y z hy hz
      rw [add_smul, hy, hz, zero_add]
  have := key _ hb
  rwa [sub_smul, sub_eq_zero] at this

def units (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    (E : Fin m → Fin m → O) (hE : ∀ i j, φ (E i j) = Matrix.single i j 1) : MatrixUnits R P (Fin m) where
  E i j := Algebra.lsmul R R P (E i j)
  mul_eq i j k l := by
    by_cases h : j = k
    · subst h
      rw [if_pos rfl, ← map_mul]
      refine LinearMap.ext fun x => ?_
      show (E i j * E j l) • x = E i l • x
      exact act_congr hker hP (by rw [map_mul, hE, hE, hE, Matrix.single_mul_single_same, mul_one]) x
    · rw [if_neg h, ← map_mul]
      refine LinearMap.ext fun x => ?_
      show (E i j * E k l) • x = 0
      have := act_congr hker hP (b := E i j * E k l) (b' := 0)
        (by rw [map_mul, hE, hE, Matrix.single_mul_single_of_ne (h := h), map_zero]) x
      rwa [zero_smul] at this
  sum_diag := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply]
    show ∑ i, E i i • x = x
    rw [← Finset.sum_smul]
    have := act_congr hker hP (b := ∑ i, E i i) (b' := 1)
      (by rw [map_sum, map_one]; simp only [hE]; exact Matrix.sum_single_one) x
    rwa [one_smul] at this

theorem units_E (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    (E : Fin m → Fin m → O) (hE : ∀ i j, φ (E i j) = Matrix.single i j 1) (i j : Fin m) (x : P) :
    (units hker hP E hE).E i j x = E i j • x := rfl

end

end GlobalTheory.MoritaLocal

namespace GlobalTheory.MoritaLocal

open GlobalTheory.Morita

theorem morita_local : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  intro R _ I hI m k hm O _ _ φ hφ hker M N _ _ _ _ _ _ _ _ eM eN
  have hM : ∀ c ∈ I, ∀ x : M, c • x = 0 := fun c hc x => smul_eq_zero_of_equiv I eM hc x
  have hN : ∀ c ∈ I, ∀ x : N, c • x = 0 := fun c hc x => smul_eq_zero_of_equiv I eN hc x
  choose E hE using fun i j : Fin m => hφ (Matrix.single i j (1 : R ⧸ I))
  let UM := units hker hM E hE
  let UN := units hker hN E hE
  let a : Fin m := ⟨0, hm⟩
  obtain ⟨gM⟩ := corner_equiv I hI hm (UM.corner a) ((UM.toPi a).symm.trans eM)
  obtain ⟨gN⟩ := corner_equiv I hI hm (UN.corner a) ((UN.toPi a).symm.trans eN)
  let g := gM.trans gN.symm
  let Φ : M ≃ₗ[R] N := (UM.toPi a).trans ((LinearEquiv.piCongrRight fun _ => g).trans (UN.toPi a).symm)
  have hΦ : ∀ y, UN.toPi a (Φ y) = fun l => g (UM.toPi a y l) := by
    intro y
    simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hΦE : ∀ i j (x : M), Φ (E i j • x) = E i j • Φ x := by
    intro i j x
    apply (UN.toPi a).injective
    have h1 := UM.toPi_E a i j x
    have h2 := UN.toPi_E a i j (Φ x)
    rw [units_E] at h1 h2
    rw [h2, hΦ, hΦ, h1]
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hΦO : ∀ (o : O) (x : M), Φ (o • x) = o • Φ x := by
    intro o x
    choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (φ o i j)
    have hφo : φ (∑ i, ∑ j, r i j • E i j) = φ o := by
      rw [map_sum]
      simp only [map_sum, map_smul, hE]
      refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
        (Matrix.matrix_eq_sum_single (φ o)).symm
      rw [Matrix.smul_single, ← hr i j, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    rw [act_congr hker hM hφo.symm x, act_congr hker hN hφo.symm (Φ x)]
    simp only [Finset.sum_smul, smul_assoc, map_sum, map_smul, hΦE]
  exact ⟨{ Φ with map_smul' := fun o x => hΦO o x }⟩

end GlobalTheory.MoritaLocal
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  first | (exact @GlobalTheory.MoritaLocal.morita_local) | (exact GlobalTheory.MoritaLocal.morita_local) | (intros; apply GlobalTheory.MoritaLocal.morita_local  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

theorem projective_La_int (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.Projective (𝓞 D.F) D.La := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  have htor : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : (a : 𝓞 D.F) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) ha0 (Ideal.mem_span_singleton_self (a : 𝓞 D.F))
      (Algebra.IsIntegral.isIntegral (R := ℤ) (a : 𝓞 D.F))
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
    obtain ⟨d, hd⟩ := he
    have h1 : e • x = 0 := by
      have : (algebraMap ℤ (𝓞 D.F) e) • x = e • x := by
        rw [algebraMap_smul]
      rw [← this, ← hd, mul_smul]
      change d • (a • x) = 0
      rw [hax, smul_zero]
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h he0
    · exact (Submodule.mem_bot _).2 h
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have : Module.Flat (𝓞 D.F) D.La := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have := Module.finitePresentation_of_finite (𝓞 D.F) D.La
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.UPel.HT.EtLev
end

section
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_surj_pi_quot_pow_ker_eq {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A) :
    P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d →
      ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧
        ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  intro hP r d hd
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨0, ?_, ?_⟩
    · intro y
      refine ⟨0, ?_⟩
      funext i
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i)
      rw [← ha]
      exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simp)).symm
    · intro x
      simp
  haveI : P.IsPrime := hP.isPrime
  have hPr : P ^ r ≠ ⊤ := by
    intro h
    exact hP.ne_top (eq_top_iff.mpr (h ▸ Ideal.pow_le_self hr.ne'))
  haveI : Nontrivial (A ⧸ P ^ r) := Ideal.Quotient.nontrivial_iff.2 hPr
  let Ap := Localization.AtPrime P
  let φ : Ap →ₐ[A] A ⧸ P ^ r := IsLocalization.liftAlgHom (M := P.primeCompl)
    (f := Ideal.Quotient.mkₐ A (P ^ r)) fun u ↦
      Ideal.Quotient.isUnit_mk_pow_of_notMem _ (Ideal.mem_primeCompl_iff.mp u.prop)
  letI : Algebra Ap (A ⧸ P ^ r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A Ap (A ⧸ P ^ r) := IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm

  haveI : Module.Free Ap (Ap ⊗[A] M) := Module.free_of_flat_of_isLocalRing
  have hle := Ideal.primeCompl_le_nonZeroDivisors P
  have hAp : Module.finrank Ap (Ap ⊗[A] M) = d := by
    rw [IsLocalization.finrank_eq Ap P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl (TensorProduct.mk A Ap M 1) hle, hd]
  let e0 := TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap (A ⧸ P ^ r) (A ⧸ P ^ r) M
  haveI : Module.Free (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := Module.Free.of_equiv e0
  haveI : Module.Finite (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := inferInstance
  have hB : Module.finrank (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) = d := by
    rw [← e0.finrank_eq, Module.finrank_baseChange, hAp]
  let e : (A ⧸ P ^ r) ⊗[A] M ≃ₗ[A ⧸ P ^ r] (Fin d → A ⧸ P ^ r) :=
    (Module.finBasisOfFinrankEq _ _ hB).equivFun
  let g : M →ₗ[A] (Fin d → A ⧸ P ^ r) :=
    (e.restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A (A ⧸ P ^ r) M 1
  refine ⟨g, ?_, ?_⟩
  · exact e.surjective.comp (TensorProduct.mk_surjective A M (A ⧸ P ^ r) Ideal.Quotient.mk_surjective)
  · intro x
    have h1 : g x = 0 ↔ (1 : A ⧸ P ^ r) ⊗ₜ[A] x = 0 := by
      simp [g, e.map_eq_zero_iff]
    rw [h1, ← (quotTensorEquivQuotSMul M (P ^ r)).map_eq_zero_iff]
    have h2 : (1 : A ⧸ P ^ r) = Ideal.Quotient.mk (P ^ r) 1 := rfl
    rw [h2, quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

end GlobalTheory
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq : ∀ {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A), P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d → ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧ ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  first | (exact @GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (exact GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (intros; apply GlobalTheory.exists_surj_pi_quot_pow_ker_eq  <;> assumption)
end

section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.VF : Type := D.VQ

instance Datum.acgVF : AddCommGroup D.VF := inferInstanceAs (AddCommGroup D.VQ)

instance Datum.modQVF : Module ℚ D.VF := inferInstanceAs (Module ℚ D.VQ)

instance Datum.modFVF : Module D.F D.VF :=
  Module.compHom D.VQ ((D.endO.val : D.endO →ₐ[ℚ] Module.End ℚ D.VQ).toRingHom.comp D.actF.toRingHom)

theorem Datum.smul_VF (x : D.F) (v : D.VF) :
    x • v = (((D.actF x : D.endO) : Module.End ℚ D.VQ) (v : D.VQ) : D.VF) := rfl

instance Datum.towerVF : IsScalarTower ℚ D.F D.VF :=
  ⟨fun q x v => by
    show ((D.actF (q • x) : D.endO) : Module.End ℚ D.VQ) v = q • ((D.actF x : D.endO) : Module.End ℚ D.VQ) v
    rw [map_smul]; rfl⟩

def Datum.endFL (g : D.endO) : Module.End D.F D.VF where
  toFun v := ((g : Module.End ℚ D.VQ) v : D.VQ)
  map_add' v w := map_add (g : Module.End ℚ D.VQ) v w
  map_smul' x v := by
    show (g : Module.End ℚ D.VQ) (((D.actF x : D.endO) : Module.End ℚ D.VQ) v) =
      ((D.actF x : D.endO) : Module.End ℚ D.VQ) ((g : Module.End ℚ D.VQ) v)
    have := congrArg (fun k : D.endO => (k : Module.End ℚ D.VQ) v) (D.actF_comm x g)
    exact this.symm

def Datum.endF : D.endO →+* Module.End D.F D.VF where
  toFun := D.endFL
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def Datum.actOFL (b : D.O) : Module.End D.F D.VF where
  toFun v := (D.actQ b (v : D.VQ) : D.VQ)
  map_add' v w := map_add (D.actQ b) v w
  map_smul' x v := by
    show D.actQ b (((D.actF x : D.endO) : Module.End ℚ D.VQ) v) =
      ((D.actF x : D.endO) : Module.End ℚ D.VQ) (D.actQ b v)
    have := (D.mem_endO.1 (D.actF x).2) b
    exact congrArg (fun k : Module.End ℚ D.VQ => k v) this

def Datum.actOF : D.O →+* Module.End D.F D.VF where
  toFun := D.actOFL
  map_one' := by ext v; show D.actQ 1 v = v; rw [map_one]; rfl
  map_mul' a b := by ext v; show D.actQ (a * b) v = D.actQ a (D.actQ b v); rw [map_mul]; rfl
  map_zero' := by ext v; show D.actQ 0 v = 0; rw [map_zero]; rfl
  map_add' a b := by ext v; show D.actQ (a + b) v = D.actQ a v + D.actQ b v; rw [map_add]; rfl

instance Datum.algFw (τ : D.F →+* PadicAlgCl p) : Algebra D.F (GlobalTheory.LKTrip.FwOf τ) := (GlobalTheory.LKTrip.embOf τ).toAlgebra

abbrev Datum.VL (τ : D.F →+* PadicAlgCl p) : Type := GlobalTheory.LKTrip.FwOf τ ⊗[D.F] D.VF

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem Datum.finrank_VF : Module.finrank D.F D.VF = D.m * D.n := by
  have h1 : Module.finrank ℚ D.VF = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa; haveI := D.finLa
    show Module.finrank ℚ (ℚ ⊗[ℤ] D.La) = _
    rw [Module.finrank_baseChange, D.rankLa]
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  haveI : FiniteDimensional D.F D.VF := Module.Finite.of_restrictScalars_finite ℚ D.F D.VF
  rw [← Module.finrank_mul_finrank ℚ D.F D.VF, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

instance Datum.finVF : FiniteDimensional D.F D.VF :=
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  Module.Finite.of_restrictScalars_finite ℚ D.F D.VF

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MatUnit

open Module

variable {L U R : Type} [Field L] [AddCommGroup U] [Module L U] [Ring R] {m : ℕ}
  (σ : Matrix (Fin m) (Fin m) R →+* Module.End L U)

theorem sum_single_one : (∑ j : Fin m, Matrix.single j j (1 : R)) = 1 := by
  ext a b
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp [Matrix.single_apply]
  · rw [if_neg h]; refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply]; split_ifs with h'
    · exact absurd (h'.1.symm.trans h'.2) h
    · rfl

theorem E_mul (i j k : Fin m) :
    σ (Matrix.single i j 1) * σ (Matrix.single j k 1) = σ (Matrix.single i k 1) := by
  rw [← map_mul, Matrix.single_mul_single_same, mul_one]

theorem E_mul_ne (i j k l : Fin m) (h : j ≠ k) :
    σ (Matrix.single i j 1) * σ (Matrix.single k l 1) = 0 := by
  rw [← map_mul, Matrix.single_mul_single_of_ne _ _ _ _ h, map_zero]

def corner (i0 : Fin m) : Submodule L U := LinearMap.range (σ (Matrix.single i0 i0 1))

theorem mem_corner {i0 : Fin m} {w : U} : w ∈ corner σ i0 ↔ σ (Matrix.single i0 i0 1) w = w :=
  ⟨fun ⟨u, hu⟩ => by rw [← hu, ← Module.End.mul_apply, E_mul], fun h => ⟨w, h⟩⟩

def cornerEquiv (i0 : Fin m) : U ≃ₗ[L] (Fin m → corner σ i0) where
  toFun u i := ⟨σ (Matrix.single i0 i 1) u, by rw [mem_corner, ← Module.End.mul_apply, E_mul]⟩
  map_add' u v := by ext i; simp
  map_smul' c u := by ext i; simp
  invFun w := ∑ i, σ (Matrix.single i i0 1) (w i)
  left_inv u := by
    show ∑ i, σ (Matrix.single i i0 1) (σ (Matrix.single i0 i 1) u) = u
    rw [show ∑ i, σ (Matrix.single i i0 1) (σ (Matrix.single i0 i 1) u) = ∑ i, σ (Matrix.single i i 1) u from
      Finset.sum_congr rfl fun i _ => by rw [← Module.End.mul_apply, E_mul]]
    rw [← LinearMap.sum_apply, ← map_sum, sum_single_one, map_one, Module.End.one_apply]
  right_inv w := by
    funext j; apply Subtype.ext
    show σ (Matrix.single i0 j 1) (∑ i, σ (Matrix.single i i0 1) (w i)) = w j
    rw [map_sum, Finset.sum_eq_single j]
    · rw [← Module.End.mul_apply, E_mul, (mem_corner σ).1 (w j).2]
    · intro i _ hij
      rw [← Module.End.mul_apply, E_mul_ne _ _ _ _ _ (Ne.symm hij), LinearMap.zero_apply]
    · intro h; exact absurd (Finset.mem_univ j) h

variable {A : Type} [Ring A] (α : A →+* Module.End L U)

theorem mapsTo_corner (hc : ∀ a M, α a * σ M = σ M * α a) (i0 : Fin m) (a : A) :
    ∀ w ∈ corner σ i0, α a w ∈ corner σ i0 := by
  intro w hw
  rw [mem_corner] at hw ⊢
  rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, hw]

def cornerHom (hc : ∀ a M, α a * σ M = σ M * α a) (i0 : Fin m) : A →+* Module.End L (corner σ i0) where
  toFun a := (α a).restrict (p := corner σ i0) (q := corner σ i0) (by intro w hw; exact mapsTo_corner σ α hc i0 a w hw)
  map_one' := by ext w; simp [LinearMap.restrict_apply]
  map_mul' a b := by ext w; simp [LinearMap.restrict_apply]
  map_zero' := by ext w; simp [LinearMap.restrict_apply]
  map_add' a b := by ext w; simp [LinearMap.restrict_apply]

end GlobalTheory.UPel.HT.MatUnit

section Main

open NumberField Matrix

end Main
end
end

section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

theorem Datum.finrank_La_ringOfIntegers :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O);
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  letI iV : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
  haveI : IsScalarTower (𝓞 D.F) D.F D.VF :=
    ⟨fun c x v => by
      show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
      rw [mul_smul]⟩
  let f : D.La →ₗ[𝓞 D.F] D.VF :=
    { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
      map_add' := fun z w => TensorProduct.tmul_add _ _ _
      map_smul' := fun c z => by
        rw [RingHom.id_apply]
        show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
          algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
        rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
        rfl }
  have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

  have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
    intro n v
    show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : (c : D.F) ≠ 0 := by
        intro h
        exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
      rw [Module.End.isUnit_iff]
      constructor
      · intro v w h
        have h' : (c : D.F) • v = (c : D.F) • w := h
        exact smul_right_injective D.VF hc0 h'
      · intro v
        refine ⟨(c : D.F)⁻¹ • v, ?_⟩
        show (c : D.F) • ((c : D.F)⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    · intro y
      obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
      have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
        mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
      refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
      show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
      rw [hnat, hf, hy]
      show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
      rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_one]
    · intro z w h
      rw [hf, hf] at h
      obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
        (TensorProduct.mk ℤ ℚ D.La 1)).1 h
      have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
        exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
      refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
      rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact hcz
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
  have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
  rw [← h1, ← h2, D.finrank_VF]

end GlobalTheory.UPel.HT
end
end

section
open NumberField GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_La_ringOfIntegers' : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p), letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O); Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  first | (exact @GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers) | (exact GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers) | (intros; apply GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers <;> assumption)
end

section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem mem_smul_top_iff_wSub {p : ℕ} [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (x : D.La) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) ↔ x ∈ wSub D w0 r := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun c hc z _ => ?_) (fun u v hu hv => add_mem hu hv)
    exact Submodule.subset_span ⟨c, hc, z, rfl⟩
  · intro hx
    suffices H : ∀ b : D.O, b • x ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.La) by simpa using H 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [smul_smul, ← Algebra.commutes, ← smul_smul]
      exact Submodule.smul_mem_smul (M := D.La) hc Submodule.mem_top
    | zero => intro b; rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => intro b; rw [smul_add]; exact add_mem (hu b) (hv b)
    | smul a u _ hu => intro b; rw [smul_smul]; exact hu (b * a)

theorem latQuot_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ),
    w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  intro p _ D w0 r hw
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := projective_La_int D
  haveI := D.finLa
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  obtain ⟨g, hs, hk⟩ := GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq w0 hw r _ (GlobalTheory.T.finrank_La_ringOfIntegers' D)
  refine ⟨g.toAddMonoidHom, hs, fun c x => ?_, fun x => ?_⟩
  · show g (c • x) = _
    rw [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rfl
  · show g x = 0 ↔ _
    rw [hk]
    exact mem_smul_top_iff_wSub D w0 r x

end GlobalTheory.UPel.HT.EtLev
end

section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_quotient_module_surjection : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.latQuot_free) | (exact GlobalTheory.UPel.HT.EtLev.latQuot_free) | (intros; apply GlobalTheory.UPel.HT.EtLev.latQuot_free <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.EtLevMorita

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

section Act

variable {O : Type} [Ring O] {G : Type} [CommGroup G] (act : O → G → G)
  (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
  (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)

include hmul in
theorem act_one_eq (b : O) : act b 1 = 1 := by
  have h := hmul b 1 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.1 h

include hadd in
theorem act_zero_eq (g : G) : act 0 g = 1 := by
  have h := hadd 0 0 g
  rw [add_zero] at h
  exact left_eq_mul.1 h

def actModule : Module O (Additive G) where
  smul b x := Additive.ofMul (act b x.toMul)
  one_smul x := by show Additive.ofMul (act 1 x.toMul) = x; rw [hone]; rfl
  mul_smul b c x := congrArg Additive.ofMul (hcomp b c x.toMul)
  smul_zero b := congrArg Additive.ofMul (act_one_eq act hmul b)
  smul_add b x y := congrArg Additive.ofMul (hmul b x.toMul y.toMul)
  add_smul b c x := congrArg Additive.ofMul (hadd b c x.toMul)
  zero_smul x := congrArg Additive.ofMul (act_zero_eq act hadd x.toMul)

end Act

end GlobalTheory.EtLevMorita

open GlobalTheory.EtLevMorita in

theorem GlobalTheory.EtLevMorita.exists_lev : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  intro p _ D w0 r hw hp G _ act hmul hone hcomp hadd f hfadd hfsm hfinj hfonto
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨fun _ => 1, fun _ _ => (_root_.mul_one 1).symm, fun b _ => (act_one_eq act hmul b).symm,
      fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
    · simp only [true_iff]
      have hx : x = algebraMap (𝓞 D.F) D.O 1 • x := by simp
      rw [hx]
      exact Submodule.subset_span ⟨1, by simp, x, rfl⟩
    · have h1 := hg 1 (by simp)
      rw [map_one, hone] at h1
      exact h1.symm
  · haveI := isLocalRing_quot_pow w0 r hr.ne'
    letI : Module D.O (Additive G) := actModule act hmul hone hcomp hadd
    letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    have hsm : ∀ (b : D.O) (x : Additive G), b • x = Additive.ofMul (act b x.toMul) := fun _ _ => rfl
    let T : Submodule D.O (Additive G) :=
      { carrier := {x | ∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) x.toMul = 1}
        add_mem' := fun {x y} hx hy c hc => by
          show act _ (x.toMul * y.toMul) = 1
          rw [hmul, hx c hc, hy c hc, _root_.mul_one]
        zero_mem' := fun c _ => act_one_eq act hmul _
        smul_mem' := fun b x hx c hc => by
          show act _ (act b x.toMul) = 1
          rw [← hcomp, Algebra.commutes, hcomp, hx c hc, act_one_eq act hmul] }
    have hf0 : f 0 = 1 := by
      have h := hfadd 0 0
      rw [add_zero] at h
      exact left_eq_mul.1 h
    have hfT : ∀ a, Additive.ofMul (f a) ∈ T := fun a c hc => by
      show act _ (f a) = 1
      rw [← hfsm, Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_smul, hf0]
    let fl : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) →ₗ[𝓞 D.F] T :=
      { toFun := fun a => ⟨Additive.ofMul (f a), hfT a⟩
        map_add' := fun a a' => Subtype.ext (by
          show Additive.ofMul (f (a + a')) = Additive.ofMul (f a) + Additive.ofMul (f a')
          rw [hfadd]; rfl)
        map_smul' := fun c a => Subtype.ext (by
          show Additive.ofMul (f (c • a)) = algebraMap (𝓞 D.F) D.O c • Additive.ofMul (f a)
          rw [← algebraMap_smul (𝓞 D.F ⧸ w0 ^ r) c a, Ideal.Quotient.algebraMap_eq, hfsm]
          rfl) }
    have hfl : Function.Bijective fl := by
      refine ⟨fun a a' h => hfinj (congrArg (fun t : T => (t : Additive G).toMul) h), fun t => ?_⟩
      obtain ⟨a, ha⟩ := hfonto (t : Additive G).toMul t.2
      exact ⟨a, Subtype.ext (by show Additive.ofMul (f a) = _; rw [ha]; rfl)⟩
    let eT : T ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) := (LinearEquiv.ofBijective fl hfl).symm
    obtain ⟨g, hgs, hgsm, hgker⟩ := GlobalTheory.T.level_quotient_module_surjection p D w0 r hw
    let gl : D.La →ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c x => by
          show g (algebraMap (𝓞 D.F) D.O c • x) = c • g x
          rw [hgsm, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
    have hker : LinearMap.ker gl = (wSub D w0 r).restrictScalars (𝓞 D.F) := by
      ext x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact hgker x
    let eL : (D.La ⧸ wSub D w0 r) ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      (Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D w0 r)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ gl.quotKerEquivOfSurjective hgs
    obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power p D w0 r hw hp
    obtain ⟨e⟩ := GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix (𝓞 D.F) (w0 ^ r) inferInstance D.m D.n D.m_pos D.O φ hφs hφk
      (D.La ⧸ wSub D w0 r) T eL eT
    refine ⟨fun x => ((e (Submodule.Quotient.mk x) : T) : Additive G).toMul, fun x y => ?_, fun b x => ?_,
      fun x => ?_, fun g hg => ?_⟩
    · simp only [Submodule.Quotient.mk_add, map_add, Submodule.coe_add, toMul_add]
    · simp only [Submodule.Quotient.mk_smul, map_smul, Submodule.coe_smul, hsm, toMul_ofMul]
    · rw [toMul_eq_one, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm ⟨Additive.ofMul g, hg⟩)
      refine ⟨y, ?_⟩
      simp only [hy, LinearEquiv.apply_symm_apply, toMul_ofMul]
end
end
