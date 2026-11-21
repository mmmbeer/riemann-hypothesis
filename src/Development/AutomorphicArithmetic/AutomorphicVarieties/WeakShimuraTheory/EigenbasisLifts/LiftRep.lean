import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DLiftIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmaDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyHamiltonSymmetric
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TrPlus
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Topology.Instances.TrivSqZeroExt

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem matUnits_pair {A E k : Type} [CommRing A] [Ring E] [Algebra A E] [Field k] [Algebra A k] [IsLocalHom (algebraMap A k)] {n : ℕ} (π : E →ₐ[A] Matrix (Fin n) (Fin n) k) (e : Fin n → E)
    (hs : Function.Surjective π) (hid : ∀ i, e i * e i = e i)
    (hπ : ∀ i, π (e i) = Matrix.single i i 1) (hc : ∀ i x, ∃ a : A, e i * x * e i = a • e i)
    (hf : ∀ i (a : A), a • e i = 0 → a = 0) (o j : Fin n) :
    ∃ P Q : E, e o * P = P ∧ P * e j = P ∧ e j * Q = Q ∧ Q * e o = Q ∧ P * Q = e o ∧ Q * P = e j ∧
      π P = Matrix.single o j 1 ∧ π Q = Matrix.single j o 1 := by
  obtain ⟨p, hp⟩ := hs (Matrix.single o j 1)
  obtain ⟨q, hq⟩ := hs (Matrix.single j o 1)
  obtain ⟨P, hP⟩ : ∃ P, P = e o * p * e j := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = e j * q * e o := ⟨_, rfl⟩
  have h1 : e o * P = P := by rw [hP, ← mul_assoc, ← mul_assoc, hid]
  have h2 : P * e j = P := by rw [hP, mul_assoc _ (e j), hid]
  have h3 : e j * Q = Q := by rw [hQ, ← mul_assoc, ← mul_assoc, hid]
  have h4 : Q * e o = Q := by rw [hQ, mul_assoc _ (e o), hid]
  have hπP : π P = Matrix.single o j 1 := by
    rw [hP, map_mul, map_mul, hπ, hπ, hp, Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp
  have hπQ : π Q = Matrix.single j o 1 := by
    rw [hQ, map_mul, map_mul, hπ, hπ, hq, Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp
  obtain ⟨c, hc1⟩ := hc j (Q * P)
  obtain ⟨d, hd1⟩ := hc o (P * Q)
  have hc2 : Q * P = c • e j := by
    rw [← hc1, ← mul_assoc, h3, mul_assoc, h2]
  have hd2 : P * Q = d • e o := by
    rw [← hd1, ← mul_assoc, h1, mul_assoc, h4]
  have hone : ∀ (i : Fin n) (a : A) (x : E), π x = Matrix.single i i 1 → x = a • e i → algebraMap A k a = 1 := by
    intro i a x hx hxa
    rw [hxa, map_smul, hπ] at hx
    have := congrFun (congrFun hx i) i
    simpa [Algebra.smul_def] using this
  have hck : algebraMap A k c = 1 := hone j c _ (by
    rw [map_mul, hπP, hπQ, Matrix.single_mul_single_same, mul_one]) hc2
  have hdk : algebraMap A k d = 1 := hone o d _ (by
    rw [map_mul, hπP, hπQ, Matrix.single_mul_single_same, mul_one]) hd2
  have hcu : IsUnit c := (isUnit_map_iff (algebraMap A k) c).1 (hck ▸ isUnit_one)
  have hdu : IsUnit d := (isUnit_map_iff (algebraMap A k) d).1 (hdk ▸ isUnit_one)
  have hcd : c = d := by
    have a1 : P * Q * (P * Q) = (d * d) • e o := by
      rw [hd2, smul_mul_smul_comm, hid]
    have a2 : P * Q * (P * Q) = (c * d) • e o := by
      rw [mul_assoc, ← mul_assoc Q, hc2, smul_mul_assoc, h3, mul_smul_comm, hd2, smul_smul]
    have a3 : (c * d - d * d) • e o = 0 := by rw [sub_smul, ← a1, ← a2, sub_self]
    exact hdu.mul_right_cancel (sub_eq_zero.1 (hf o _ a3))
  obtain ⟨b, hb⟩ := hcu.exists_left_inv
  have hbk : algebraMap A k b = 1 := by
    have := congrArg (algebraMap A k) hb
    rwa [map_mul, hck, mul_one, map_one] at this
  refine ⟨P, b • Q, h1, h2, ?_, ?_, ?_, ?_, hπP, ?_⟩
  · rw [mul_smul_comm, h3]
  · rw [smul_mul_assoc, h4]
  · rw [mul_smul_comm, hd2, smul_smul, ← hcd, hb, one_smul]
  · rw [smul_mul_assoc, hc2, smul_smul, hb, one_smul]
  · rw [map_smul, hπQ, ← algebraMap_smul k b, hbk, one_smul]

theorem UpperTheory.V.Ws.Eb.matUnits :
    ∀ {A E k : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] [Field k] [Algebra A k] [IsLocalHom (algebraMap A k)] {n : ℕ} (π : E →ₐ[A] Matrix (Fin n) (Fin n) k) (e : Fin n → E), Function.Surjective π → CompleteOrthogonalIdempotents e → (∀ i, π (e i) = Matrix.single i i 1) → (∀ i x, ∃ a : A, e i * x * e i = a • e i) → (∀ i (a : A), a • e i = 0 → a = 0) →
        ∃ φ : E →ₐ[A] Matrix (Fin n) (Fin n) A, (∀ i, φ (e i) = Matrix.single i i 1) ∧ ∀ x, (φ x).map (algebraMap A k) = π x := by
  intro A E k _ _ _ _ _ _ _ n π e hs he hπ hc hf
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  let o : Fin n := ⟨0, hn⟩
  have hid : ∀ i, e i * e i = e i := fun i => (he.idem i).eq
  choose P Q h1 h2 h3 h4 h5 h6 hP hQ using matUnits_pair π e hs hid hπ hc hf o
  choose c hcc using hc o
  have inj : ∀ a b : A, a • e o = b • e o → a = b := fun a b h =>
    sub_eq_zero.1 (hf o _ (by rw [sub_smul, h, sub_self]))
  obtain ⟨m, hm⟩ : ∃ m : E → Matrix (Fin n) (Fin n) A, ∀ x i j, m x i j • e o = P i * x * Q j := by
    refine ⟨fun x => Matrix.of fun i j => c (P i * x * Q j), fun x i j => ?_⟩
    change c (P i * x * Q j) • e o = _
    rw [← hcc, ← mul_assoc, ← mul_assoc, h1, mul_assoc _ (Q j), h4]
  have hPQ : ∀ i j, P i * Q j = (1 : Matrix (Fin n) (Fin n) A) i j • e o := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [h5, Matrix.one_apply_eq, one_smul]
    · rw [Matrix.one_apply_ne hij, zero_smul, ← h2 i, ← h3 j, mul_assoc, ← mul_assoc (e i),
        he.ortho hij, zero_mul, mul_zero]
  have m1 : m 1 = 1 := by
    ext i j
    apply inj
    rw [hm, mul_one, hPQ]
  have mmul : ∀ x y, m (x * y) = m x * m y := by
    intro x y
    ext i j
    apply inj
    rw [hm, Matrix.mul_apply, Finset.sum_smul]
    have : ∀ l, (m x i l * m y l j) • e o = P i * x * e l * (y * Q j) := by
      intro l
      rw [← hid o, ← smul_mul_smul_comm, hm, hm, ← h6 l]
      simp only [mul_assoc]
    simp only [this]
    rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete]
    simp only [mul_assoc, one_mul]
  have madd : ∀ x y, m (x + y) = m x + m y := by
    intro x y
    ext i j
    apply inj
    rw [Matrix.add_apply, add_smul, hm, hm, hm, mul_add, add_mul]
  have msmul : ∀ (a : A) x, m (a • x) = a • m x := by
    intro a x
    ext i j
    apply inj
    rw [Matrix.smul_apply, smul_eq_mul, mul_smul, hm, hm, mul_smul_comm, smul_mul_assoc]
  let L : E →ₗ[A] Matrix (Fin n) (Fin n) A := ⟨⟨m, madd⟩, msmul⟩
  refine ⟨AlgHom.ofLinearMap L m1 mmul, fun l => ?_, fun x => ?_⟩
  · change m (e l) = _
    ext i j
    apply inj
    rw [hm]
    by_cases hi : l = i
    · subst hi
      rw [h2, hPQ]
      congr 1
      simp [Matrix.one_apply, Matrix.single_apply]
    · rw [← h2 i, mul_assoc _ (e i), he.ortho (Ne.symm hi), mul_zero, zero_mul,
        Matrix.single_apply_of_row_ne hi, zero_smul]
  · change (m x).map _ = _
    ext i j
    have h := congrArg π (hm x i j)
    rw [map_smul, map_mul, map_mul, hπ, hP, hQ, Matrix.single_mul_mul_single] at h
    have := congrFun (congrFun h o) o
    simpa [Algebra.smul_def] using this
end

section
section

open TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.CA

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp



theorem UpperTheory.V.Ws.Eb.detRep :
    ∀ {A k G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Field k] (f : A →+* k) [IsLocalHom f] [Group G] {n : ℕ} (D : W.GDet n A G) (ρ : G →* GL (Fin n) k), 1 ≤ n → Function.Surjective f → Full ρ → D.map f = W.GDet.ofRep (W.mat ρ) →
        ∃ ρ' : G →* GL (Fin n) A, D = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep f ρ' = ρ ∧ Full ρ' :=
  _root_.UpperTheory.Reformulated.B.CayleyHamiltonSymmetric.detRep
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def ebS {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd

private theorem ebS_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    ebS (X * Y) = X.map (dF K) * ebS Y + ebS X * Y.map (dF K) := by
  ext i j
  simp only [ebS, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [dF, smul_eq_mul, MulOpposite.smul_eq_mul_unop, mul_comm]

theorem UpperTheory.V.Ws.Eb.tanOf :
    ∀ {K G : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ' : G →* GL (Fin n) (DualNumber K)), Continuous ρ' →
        Continuous (W.pushRep (dF K) ρ') ∧ ∃ y ∈ Z1 (Loc.adGL (W.pushRep (dF K) ρ')), IsTan (W.pushRep (dF K) ρ') y ρ' := by
  intro K G _ _ _ _ _ _ n ρ' hρ'
  set ρ := W.pushRep (dF K) ρ' with hρ
  have hdF : Continuous (dF K) := TrivSqZeroExt.continuous_fst
  have hv : Continuous fun g => (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_val.comp hρ'
  have hi : Continuous fun g => (↑((ρ' g)⁻¹) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_coe_inv.comp hρ'
  have hc : Continuous ρ := by
    rw [Units.continuous_iff]
    exact ⟨hv.matrix_map hdF, hi.matrix_map hdF⟩
  have hci : Continuous fun g => (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv.comp hc
  have e : ∀ g, (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) = (↑(ρ g) : Matrix (Fin n) (Fin n) K) :=
    fun g => rfl
  have hS : Continuous fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    continuous_matrix fun i j => TrivSqZeroExt.continuous_snd.comp (hv.matrix_elem i j)
  refine ⟨hc, fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K),
    ⟨hS.matrix_mul hci, ?_⟩, ?_⟩
  · intro g h
    show ebS (↑(ρ' (g * h)) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ (g * h))⁻¹) : Matrix (Fin n) (Fin n) K) =
      ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) +
        (↑(ρ g) : Matrix (Fin n) (Fin n) K) * (ebS (↑(ρ' h) : Matrix (Fin n) (Fin n) (DualNumber K)) *
          (↑((ρ h)⁻¹) : Matrix (Fin n) (Fin n) K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K)
    rw [map_mul, map_mul, Units.val_mul, ebS_mul, e, e, _root_.mul_inv_rev, Units.val_mul, add_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    exact add_comm _ _
  · intro g i j
    show _ = (_, (ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) *
      (↑(ρ g) : Matrix (Fin n) (Fin n) K)) i j)
    rw [Units.inv_mul_cancel_right]
    rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem lr_cont {Γ R E : Type} [TopologicalSpace Γ] [CommRing R] [NormedAddCommGroup E] (I : Ideal R) (f : Γ → R)
    (hf : AdicCont I f) (y : R →+ E) (hy : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ ε) :
    Continuous fun g => y (f g) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hy (ε / 2) (half_pos hε)
  filter_upwards [(hf n).eventually_eq g₀] with g hg
  have h1 := hn _ (Ideal.Quotient.eq.1 hg)
  rw [map_sub] at h1
  rw [dist_eq_norm]
  exact h1.trans_lt (half_lt_self hε)

private theorem lr_cont2 {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (f : Γ → R) (hf : AdicCont (maximalIdeal R) f) (x : R →ₐ[c.O] DualNumber (PadicAlgCl l)) :
    Continuous fun g => x (f g) := by
  obtain ⟨-, a, ha1, ha0, ha⟩ := (coPt c R).1 ((TrivSqZeroExt.fstHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp x)
  have h1 : Continuous fun g => (x (f g)).fst := by
    refine lr_cont _ f hf
      ((TrivSqZeroExt.fstHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp x).toRingHom.toAddMonoidHom fun ε hε => ?_
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).eventually (gt_mem_nhds hε)).exists
    exact ⟨k, fun z hz => (ha k z hz).trans hk.le⟩
  have h2 : Continuous fun g => (x (f g)).snd :=
    lr_cont _ f hf ((TrivSqZeroExt.sndHom (PadicAlgCl l) (PadicAlgCl l)).toAddMonoidHom.comp x.toRingHom.toAddMonoidHom)
      ((coPt c R).2 x).2
  exact h1.prodMk h2

theorem UpperTheory.V.Ws.Eb.liftRep :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), 1 ≤ n → Full ρ → B.u.D.map ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) = W.GDet.ofRep (W.mat ρ) →
        ∃ (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep (dF _) ρ' = ρ ∧ Full ρ' ∧ Continuous ρ ∧ y ∈ Z1 (Loc.adGL ρ) ∧ IsTan ρ y ρ' := by
  intro l _ F c n r B x' ρ hn hρ hD
  haveI : Module.Finite (PadicAlgCl l) (DualNumber (PadicAlgCl l)) :=
    inferInstanceAs (Module.Finite (PadicAlgCl l) (PadicAlgCl l × PadicAlgCl l))
  haveI : IsArtinianRing (DualNumber (PadicAlgCl l)) := IsArtinianRing.of_finite (PadicAlgCl l) _
  haveI : IsAdicComplete (maximalIdeal (DualNumber (PadicAlgCl l))) (DualNumber (PadicAlgCl l)) := inferInstance
  haveI : IsLocalHom (dF (PadicAlgCl l)) := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  obtain ⟨ρ', h1, h2, h3⟩ := detRep (dF (PadicAlgCl l)) (B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l))) ρ hn
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) hρ (((AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1 _).trans hD)
  have htr : ∀ g, (W.mat ρ' g).trace = x' (B.u.D.lam 1 (MonoidAlgebra.single g 1)) := fun g => by
    have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 1 g
    have e2 := (AlgebraTools.Det.repApi (W.mat ρ')).2.2.1 hn (MonoidAlgebra.single g 1)
    have e3 : W.GDet.repAlg (W.mat ρ') _ (MonoidAlgebra.single g 1) = W.mat ρ' g := by
      refine Matrix.ext fun i j => ?_
      simp [W.GDet.repAlg]
    rw [h1] at e1
    rw [e3] at e2
    exact e2.symm.trans e1
  have hc : Continuous ρ' := (trPlus ρ' h3).2 (by
    simp only [htr]
    exact lr_cont2 c _ (B.u.cont 1) x')
  obtain ⟨h4, y, h5, h6⟩ := tanOf ρ' hc
  rw [h2] at h4 h5 h6
  exact ⟨ρ', y, h1, h2, h3, h4, h5, h6⟩
end
