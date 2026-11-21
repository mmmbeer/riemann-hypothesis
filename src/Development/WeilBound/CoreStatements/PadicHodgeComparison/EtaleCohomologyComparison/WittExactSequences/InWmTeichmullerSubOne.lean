import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesUnOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForD

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

open PAlg

variable {l : ℕ} [Fact l.Prime]

theorem dxi_zero' (A : PAlg l) (n : ℕ) : A.dxi n 0 = 1 := by
  show A.mkAcr n (A.dxi0 0) = 1
  rw [← map_one (A.mkAcr n)]
  congr 1
  apply Subtype.ext
  simp [PAlg.dxi0, dpw]

theorem fil_zero' (A : PAlg l) (n : ℕ) : A.Fil n 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (dxi_zero' A n ▸ Ideal.subset_span ⟨0, le_rfl, rfl⟩)

theorem fil_succ_le' (A : PAlg l) (n r : ℕ) : A.Fil n (r + 1) ≤ A.Fil n r :=
  Ideal.span_mono fun _ ⟨k, hk, hz⟩ => ⟨k, by omega, hz⟩

theorem dxi_mem_fil' (A : PAlg l) (n r : ℕ) : A.dxi n r ∈ A.Fil n r := Ideal.subset_span ⟨r, le_rfl, rfl⟩

def gr (h : RGr l) (A : PAlg l) (n r : ℕ) (z : A.Acr n) (hz : z ∈ A.Fil n r) : A.Un n :=
  Ideal.Quotient.mk _ (A.th (Classical.choose ((h A n r).1 z hz)))

theorem gr_eq (h : RGr l) (A : PAlg l) {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) (x : A.W)
    (hx : z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) : gr h A n r z hz = Ideal.Quotient.mk _ (A.th x) := by
  have h0 := Classical.choose_spec ((h A n r).1 z hz)
  show Ideal.Quotient.mk _ (A.th (Classical.choose ((h A n r).1 z hz))) = _
  rw [Ideal.Quotient.eq, ← map_sub]
  apply ((h A n r).2 _).1
  have e : A.toAcr n (Classical.choose ((h A n r).1 z hz) - x) * A.dxi n r =
      (z - A.toAcr n x * A.dxi n r) - (z - A.toAcr n (Classical.choose ((h A n r).1 z hz)) * A.dxi n r) := by
    rw [map_sub]; ring
  rw [e]; exact sub_mem hx h0

theorem gr_spec (h : RGr l) (A : PAlg l) {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) :
    ∃ x : A.W, z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1) ∧ gr h A n r z hz = Ideal.Quotient.mk _ (A.th x) :=
  ⟨_, Classical.choose_spec ((h A n r).1 z hz), rfl⟩

def fv {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) : A.Acr n := z.1

theorem fv_mem {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) : fv z ∈ A.Fil n r := z.2

theorem fv_add {A : PAlg l} {n r : ℕ} (z z' : (FilF l n r).obj A) : fv (z + z') = fv z + fv z' := rfl

theorem fv_zero {A : PAlg l} {n r : ℕ} : fv (0 : (FilF l n r).obj A) = 0 := rfl

theorem gr_zero (h : RGr l) (A : PAlg l) (n r : ℕ) : gr h A n r (fv (0 : (FilF l n r).obj A)) (fv_mem _) = 0 := by
  rw [gr_eq h A _ _ 0 (by rw [fv_zero, map_zero, zero_mul, sub_zero]; exact zero_mem _), map_zero, map_zero]

theorem gr_add (h : RGr l) (A : PAlg l) (n r : ℕ) (z z' : (FilF l n r).obj A) :
    gr h A n r (fv (z + z')) (fv_mem _) = gr h A n r (fv z) (fv_mem z) + gr h A n r (fv z') (fv_mem z') := by
  obtain ⟨x, hx, e⟩ := gr_spec h A (fv z) (fv_mem z)
  obtain ⟨x', hx', e'⟩ := gr_spec h A (fv z') (fv_mem z')
  have hs : fv (z + z') - A.toAcr n (x + x') * A.dxi n r =
      (fv z - A.toAcr n x * A.dxi n r) + (fv z' - A.toAcr n x' * A.dxi n r) := by rw [fv_add, map_add]; ring
  rw [gr_eq h A _ _ (x + x') (by rw [hs]; exact add_mem hx hx'), e, e', map_add, map_add]

def grF (h : RGr l) (A : PAlg l) (n r : ℕ) : (FilF l n r).obj A →+ (UnF l n).obj A where
  toFun z := gr h A n r (fv z) (fv_mem z)
  map_zero' := gr_zero h A n r
  map_add' := gr_add h A n r

theorem grF_apply (h : RGr l) (A : PAlg l) {n r : ℕ} (z : (FilF l n r).obj A) (x : A.W)
    (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) : grF h A n r z = Ideal.Quotient.mk _ (A.th x) :=
  gr_eq h A _ (fv_mem z) x hx

theorem fv_inj {A : PAlg l} {n r : ℕ} {z z' : (FilF l n r).obj A} (e : fv z = fv z') : z = z' := Subtype.ext e

def mkF {A : PAlg l} {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) : (FilF l n r).obj A := ⟨z, hz⟩

theorem fv_mkF {A : PAlg l} {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) : fv (mkF (l := l) z hz) = z := rfl

theorem fv_smul {A : PAlg l} {n r : ℕ} (a : Acris l) (z : (FilF l n r).obj A) : fv (a • z) = A.cris n a * fv z := rfl

theorem fv_map {A B : PAlg l} (f : A ⟶ B) {n r : ℕ} (z : (FilF l n r).obj A) :
    fv (((FilF l n r).map f).hom z) = mapAcr f n (fv z) := rfl

theorem un_smul (A : PAlg l) (n : ℕ) (a : Ainf l) (x : A.W) :
    (a • (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th x))) =
      (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th (A.sW a * x))) := rfl

theorem un_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    ((UnF l n).map f).hom (Ideal.Quotient.mk _ (A.th x)) = Ideal.Quotient.mk _ (B.th (mapW f x)) := rfl

def grx (h : RGr l) {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) : A.W := Classical.choose ((h A n r).1 (fv z) (fv_mem z))

theorem grx_spec (h : RGr l) {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) :
    fv z - A.toAcr n (grx h z) * A.dxi n r ∈ A.Fil n (r + 1) := Classical.choose_spec ((h A n r).1 (fv z) (fv_mem z))

theorem un_smul' (A : PAlg l) (n : ℕ) (a : Ainf l) (x : A.W) :
    (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th (A.sW a * x))) = RingHom.id (Ainf l) a • (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th x)) := by
  rw [RingHom.id_apply]; exact (un_smul A n a x).symm

theorem grF_algebraMap_smul (h : RGr l) (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n r).obj A) (x : A.W) (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1))
    (hm : fv (algebraMap (Ainf l) (Acris l) a • z) - A.toAcr n (A.sW a * x) * A.dxi n r ∈ A.Fil n (r + 1)) :
    grF h A n r (algebraMap (Ainf l) (Acris l) a • z) = RingHom.id (Ainf l) a • grF h A n r z := by
  rw [grF_apply h A _ _ hm, grF_apply h A z x hx]
  exact un_smul' A n a x

theorem smul_mem_filtration_graded (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n r).obj A) (x : A.W) (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) :
    fv (algebraMap (Ainf l) (Acris l) a • z) - A.toAcr n (A.sW a * x) * A.dxi n r ∈ A.Fil n (r + 1) := by
  have : fv (algebraMap (Ainf l) (Acris l) a • z) - A.toAcr n (A.sW a * x) * A.dxi n r =
      A.toAcr n (A.sW a) * (fv z - A.toAcr n x * A.dxi n r) := by
    rw [fv_smul, cris_algebraMap, map_mul]; ring
  rw [this]; exact Ideal.mul_mem_left _ _ hx

theorem grF_smul (h : RGr l) (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n r).obj A) :
    grF h A n r (algebraMap (Ainf l) (Acris l) a • z) = RingHom.id (Ainf l) a • grF h A n r z :=
  grF_algebraMap_smul h A n r a z _ (grx_spec h z) (smul_mem_filtration_graded A n r a z _ (grx_spec h z))

def incF (A : PAlg l) (n r : ℕ) : (FilF l n (r + 1)).obj A →+ (FilF l n r).obj A where
  toFun z := mkF (fv z) (fil_succ_le' A n r (fv_mem z))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fv_incF (A : PAlg l) (n r : ℕ) (z : (FilF l n (r + 1)).obj A) : fv (incF A n r z) = fv z := rfl

theorem incF_inj (A : PAlg l) (n r : ℕ) : Function.Injective (incF A n r) := fun z z' e => fv_inj (by
  have := congrArg (fv (l := l) (A := A) (n := n) (r := r)) e
  rwa [fv_incF, fv_incF] at this)

theorem incF_smul (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n (r + 1)).obj A) :
    incF A n r (algebraMap (Ainf l) (Acris l) a • z) = algebraMap (Ainf l) (Acris l) a • incF A n r z := rfl

theorem incF_nat {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n (r + 1)).obj A) :
    incF B n r (((FilF l n (r + 1)).map f).hom z) = ((FilF l n r).map f).hom (incF A n r z) := rfl

theorem ex_mem (h : RGr l) (A : PAlg l) (n r : ℕ) (y : (FilF l n r).obj A) (x : A.W)
    (hx : fv y - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) (h0 : (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ n}) (A.th x) : A.Un n) = 0) :
    fv y ∈ A.Fil n (r + 1) := by
  have hm := ((h A n r).2 x).2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have : fv y = (fv y - A.toAcr n x * A.dxi n r) + A.toAcr n x * A.dxi n r := by ring
  rw [this]; exact add_mem hx hm

theorem ex1 (h : RGr l) (A : PAlg l) (n r : ℕ) (y : (FilF l n r).obj A) (x : A.W)
    (hx : fv y - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) (hy : grF h A n r y = 0) : y ∈ Set.range (incF A n r) :=
  ⟨mkF (fv y) (ex_mem h A n r y x hx ((grF_apply h A y x hx).symm.trans hy)), fv_inj (fv_incF A n r _)⟩

theorem ex2 (h : RGr l) (A : PAlg l) (n r : ℕ) (w : (FilF l n (r + 1)).obj A) : grF h A n r (incF A n r w) = 0 := by
  rw [grF_apply h A _ 0 (by rw [fv_incF, map_zero, zero_mul, sub_zero]; exact fv_mem w), map_zero, map_zero]

theorem ex3 (h : RGr l) (A : PAlg l) (n r : ℕ) (y : (FilF l n r).obj A) : grF h A n r y = 0 ↔ y ∈ Set.range (incF A n r) := by
  constructor
  · exact ex1 h A n r y _ (grx_spec h y)
  · rintro ⟨w, rfl⟩
    exact ex2 h A n r w

theorem grF_exact (h : RGr l) (A : PAlg l) (n r : ℕ) : Function.Exact (incF A n r) (grF h A n r) := by
  intro y
  exact ex3 h A n r y

theorem grF_surj (h : RGr l) (A : PAlg l) (n r : ℕ) : Function.Surjective (grF h A n r) := by
  intro u
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(l : A.U) ^ n}) u
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {A.xi}) u'
  refine ⟨mkF (A.toAcr n x * A.dxi n r) (Ideal.mul_mem_left _ _ (dxi_mem_fil' A n r)), ?_⟩
  exact grF_apply h A _ x (by rw [fv_mkF, sub_self]; exact zero_mem _)

theorem nat_mem {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n r).obj A) (x : A.W)
    (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) :
    fv (((FilF l n r).map f).hom z) - B.toAcr n (mapW f x) * B.dxi n r ∈ B.Fil n (r + 1) := by
  rw [fv_map, ← mapAcr_toAcr, ← mapAcr_dxi f n r, ← map_mul, ← map_sub]
  exact mapAcr_fil f n (r + 1) hx

theorem graded_naturality (h : RGr l) {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n r).obj A) (x : A.W)
    (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) :
    grF h B n r (((FilF l n r).map f).hom z) = ((UnF l n).map f).hom (grF h A n r z) := by
  rw [grF_apply h B _ _ (nat_mem f n r z x hx), grF_apply h A z x hx]
  exact (un_map f n x).symm

theorem grF_nat (h : RGr l) {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n r).obj A) :
    grF h B n r (((FilF l n r).map f).hom z) = ((UnF l n).map f).hom (grF h A n r z) :=
  graded_naturality h f n r z _ (grx_spec h z)

def fil0Inclusion (A : PAlg l) (n : ℕ) : (FilF l n 0).obj A →+ (AcrF l n).obj A where
  toFun z := fv z
  map_zero' := rfl
  map_add' _ _ := rfl

theorem filtration_zero_inclusion_bijective (A : PAlg l) (n : ℕ) : Function.Bijective (fil0Inclusion A n) :=
  ⟨fun _ _ e => fv_inj e, fun y => ⟨mkF (r := 0) y (by rw [fil_zero']; trivial), rfl⟩⟩

theorem filtration_zero_inclusion_smul (A : PAlg l) (n : ℕ) (a : Acris l) (z : (FilF l n 0).obj A) :
    fil0Inclusion A n (a • z) = RingHom.id (Acris l) a • fil0Inclusion A n z := rfl

theorem fil0Inclusion_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (z : (FilF l n 0).obj A) :
    fil0Inclusion B n (((FilF l n 0).map f).hom z) = ((AcrF l n).map f).hom (fil0Inclusion A n z) := rfl

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

open PAlg

variable (l : ℕ) [Fact l.Prime]

theorem des_Fil_zero (hA : ∀ n k, Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k))) (n k : ℕ) :
    Des (FilF l n 0) (algebraMap (Ainf l) (Acris l) (rtW l k)) :=
  (des_semi (RingHom.id (Acris l)) (testι l) (FilF l n 0) (AcrF l n) (fun A => fil0Inclusion A n)
    (fun A a x => filtration_zero_inclusion_smul A n a x) (fun A => filtration_zero_inclusion_bijective A n) (fun f x => fil0Inclusion_map f n x) _).2 (hA n k)

theorem des_Fil_succ (h : RIn l) (n r k : ℕ) (ih : Des (FilF l n r) (algebraMap (Ainf l) (Acris l) (rtW l (k + 2)))) :
    Des (FilF l n (r + 1)) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  have hs := (des_ses (algebraMap (Ainf l) (Acris l)) (algebraMap (Ainf l) (Acris l)) (RingHom.id (Ainf l)) (testι l)
    (FilF l n (r + 1)) (FilF l n r) (UnF l n) (fun A => incF A n r) (fun A => grF h.2.2.2.2 A n r)
    (fun A a x => incF_smul A n r a x) (fun A a x => grF_smul h.2.2.2.2 A n r a x)
    (fun f x => incF_nat f n r x) (fun f x => grF_nat h.2.2.2.2 f n r x)
    (fun A => incF_inj A n r) (fun A => grF_exact h.2.2.2.2 A n r) (fun A => grF_surj h.2.2.2.2 A n r) (rtW l (k + 2))).2 ih
    (des_Un l h.1 h.2.2.2.1 n (k + 2))
  exact des_span (testι l) (FilF l n (r + 1)) {algebraMap (Ainf l) (Acris l) (rtW l (k + 2) ^ 3)} (by
    rintro a rfl; exact Or.inl hs) _ (Ideal.mem_span_singleton.2 (map_dvd _ (rtW_dvd l k).1))

theorem des_Fil_of (h : RIn l) (hA : ∀ n k, Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k))) (n r k : ℕ) :
    Des (FilF l n r) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  induction r generalizing k with
  | zero => exact des_Fil_zero l hA n k
  | succ r ih => exact des_Fil_succ l h n r k (ih (k + 2))

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem acr_zero_eq (A : PAlg l) (x : A.Acr 0) : x = 0 := by
  have h1 : (1 : A.Acr 0) = 0 := by simpa using A.pow_l_acr 0
  rw [← mul_one x, h1, mul_zero]

theorem des_Acr_zero (s : Acris l) : Des (AcrF l 0) s :=
  des_span (testι l) (AcrF l 0) {s} (fun _ _ => Or.inr fun A x => by
    have hx : x = 0 := acr_zero_eq l A x
    rw [hx, smul_zero]) s (Ideal.subset_span rfl)

theorem des_Acr_one (h : ObFacts l) (h1 : RAcr1 l) (k : ℕ) :
    Des (AcrF l 1) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  obtain ⟨N, _, _, M, τ, hN, hτ, hn⟩ := h1
  have h0 := des_tens l h N M hN k
  let σ : Ainf l →+* Ob l := WittVector.constantCoeff
  have e1 : Des (toPf l ⋙ tensF l (Ob l) N ⋙ ModuleCat.restrictScalars σ) (rtW l k) := by
    refine (des_semi σ (testι l) (toPf l ⋙ tensF l (Ob l) N ⋙ ModuleCat.restrictScalars σ) (toPf l ⋙ tensF l (Ob l) N)
      (fun A => AddMonoidHom.id _) (fun A a x => rfl) (fun A => Function.bijective_id) (fun f x => rfl) (rtW l k)).2 ?_
    have hc : σ (rtW l k) = rt l k := (rtW_dvd l k).2
    rw [hc]; exact h0
  refine (des_semi (algebraMap (Ainf l) (Acris l)) (testι l) (toPf l ⋙ tensF l (Ob l) N ⋙ ModuleCat.restrictScalars σ)
    (AcrF l 1) (fun A => (τ A).toAddMonoidHom) (fun A a x => ?_) (fun A => (τ A).bijective) (fun f x => hn _ _ f x) (rtW l k)).1 e1
  refine (hτ A a x).trans ?_
  change _ = A.cris 1 (algebraMap (Ainf l) (Acris l) a) * τ A x
  rw [A.cris_algebraMap]; rfl

theorem mkAcr_surj (A : PAlg l) (m : ℕ) : Function.Surjective (A.mkAcr m) := Ideal.Quotient.mk_surjective

theorem acr_smul_eq (A : PAlg l) (m : ℕ) (a : Ainf l) (z : A.Acr m) :
    (algebraMap (Ainf l) (Acris l) a) • z = A.mkAcr m (algebraMap A.W A.Acr0 (A.sW a)) * z := by
  rw [Algebra.smul_def]; exact congrArg (· * z) (A.cris_algebraMap m a)

theorem des_span_dvd {R : Type} [CommRing R] (F : PAlg l ⥤ ModuleCat.{0} R) (a b : R) (hab : a ∣ b) (ha : Des F a) : Des F b :=
  des_span (testι l) F {a} (fun c hc => Or.inl (by rw [Set.mem_singleton_iff.1 hc]; exact ha)) b
    (Ideal.mem_span_singleton.2 hab)

theorem seq_smul (n : ℕ) (A : PAlg l) (α : A.Acr 1 →+ A.Acr (n + 1))
    (hmk : ∀ y : A.Acr0, α (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y)) (a : Ainf l) (x : A.Acr 1) :
    α (algebraMap (Ainf l) (Acris l) a • x) = algebraMap (Ainf l) (Acris l) a • α x := by
  obtain ⟨y, rfl⟩ := mkAcr_surj l A 1 x
  rw [acr_smul_eq, acr_smul_eq, ← map_mul, hmk, hmk, ← map_mul, mul_left_comm]

theorem seq_nat (n : ℕ) {A B : PAlg l} (f : A ⟶ B) (α : A.Acr 1 →+ A.Acr (n + 1)) (α' : B.Acr 1 →+ B.Acr (n + 1))
    (hmk : ∀ y : A.Acr0, α (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y))
    (hmk' : ∀ y : B.Acr0, α' (B.mkAcr 1 y) = B.mkAcr (n + 1) ((l : B.Acr0) ^ n * y)) (x : A.Acr 1) :
    α' (PAlg.mapAcr f 1 x) = PAlg.mapAcr f (n + 1) (α x) := by
  obtain ⟨y, rfl⟩ := mkAcr_surj l A 1 x
  change α' ((PAlg.pdOk_hom f).acr 1 (A.mkAcr 1 y)) = (PAlg.pdOk_hom f).acr (n + 1) (α (A.mkAcr 1 y))
  rw [hmk, PAlg.PdOk.acr_mk, PAlg.PdOk.acr_mk, hmk']
  simp only [map_mul, map_pow, map_natCast]

theorem red_surj (A : PAlg l) (n : ℕ) : Function.Surjective (A.red (Nat.le_succ n)) := fun x => by
  obtain ⟨y, rfl⟩ := mkAcr_surj l A n x
  exact ⟨A.mkAcr (n + 1) y, rfl⟩

theorem des_Acr_succ (h2 : RAcrSeq l) (n : ℕ)
    (h1k : ∀ k, Des (AcrF l 1) (algebraMap (Ainf l) (Acris l) (rtW l k)))
    (hnk : ∀ k, Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k))) (k : ℕ) :
    Des (AcrF l (n + 1)) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  obtain ⟨α, hαmk, hαe⟩ := h2 n
  let σ := algebraMap (Ainf l) (Acris l)
  have := (des_ses σ σ σ (testι l) (AcrF l 1) (AcrF l (n + 1)) (AcrF l n) (fun A => α A)
    (fun A => ((redF l (Nat.le_succ n)).app A).hom.toAddMonoidHom)
    (fun A a x => seq_smul l n A (α A) (hαmk A) a x)
    (fun A a x => ((redF l (Nat.le_succ n)).app A).hom.map_smul (σ a) x)
    (fun {A B} f x => seq_nat l n f (α A) (α B) (hαmk A) (hαmk B) x)
    (fun {A B} f x => congrArg (fun g => ModuleCat.Hom.hom g x) ((redF l (Nat.le_succ n)).naturality f))
    (fun A => (hαe A).1) (fun A => (hαe A).2)
    (fun A => red_surj l A n) (rtW l (k + 2))).1 (h1k _) (hnk _)
  exact des_span_dvd l _ _ _ (map_dvd σ (rtW_dvd l k).1) this

theorem un_kill (A : PAlg l) (n : ℕ) (x : (UnF l n).obj A) : ((l : Ainf l) ^ n) • x = 0 := by
  have h0 : (l : A.Un n) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ n})), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  refine (Algebra.smul_def (A := A.Un n) _ x).trans ?_
  rw [map_pow, map_natCast, h0, zero_mul]

theorem acr_kill (A : PAlg l) (n : ℕ) (x : A.Acr n) : algebraMap (Ainf l) (Acris l) ((l : Ainf l) ^ n) • x = 0 := by
  rw [acr_smul_eq]
  simp only [map_pow, map_natCast]
  rw [A.pow_l_acr, zero_mul]

theorem fil_kill (A : PAlg l) (n r : ℕ) (x : (FilF l n r).obj A) :
    algebraMap (Ainf l) (Acris l) ((l : Ainf l) ^ n) • x = 0 :=
  Subtype.ext (acr_kill l A n x.1)

theorem des_of_map {R : Type} [CommRing R] (F : PAlg l ⥤ ModuleCat.{0} R) (σ : Ainf l →+* R) (n : ℕ)
    (hk : ∀ (A : PAlg l) (x : F.obj A), σ ((l : Ainf l) ^ n) • x = 0) (hr : ∀ k, Des F (σ (rtW l k)))
    (s : Ainf l) (hs : s ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l)))) : Des F (σ s) := by
  have hm := Ideal.mem_map_of_mem σ hs
  rw [Ideal.map_span] at hm
  refine des_span (testι l) F _ ?_ _ hm
  rintro _ ⟨b, hb, rfl⟩
  rcases hb with rfl | ⟨k, rfl⟩
  · exact Or.inr hk
  · exact Or.inl (hr k)

theorem des_Acr (h : ObFacts l) (h1 : RAcr1 l) (h2 : RAcrSeq l) (n k : ℕ) :
    Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  induction n generalizing k with
  | zero => exact des_Acr_zero l _
  | succ n ih => exact des_Acr_succ l h2 n (des_Acr_one l h h1) ih k

theorem des_Fil (h : RIn l) (n r k : ℕ) : Des (FilF l n r) (algebraMap (Ainf l) (Acris l) (rtW l k)) :=
  des_Fil_of l h (fun n k => des_Acr l h.1 h.2.1 h.2.2.1 n k) n r k

theorem out_of_rin (h : RIn l) : Out l := fun s hs n => by
  have hw := wm_span l h.1 s hs n
  refine ⟨?_, ?_, fun r => ?_⟩
  · exact des_of_map l (UnF l n) (RingHom.id _) n (fun A x => un_kill l A n x) (des_Un l h.1 h.2.2.2.1 n) s hw
  · exact des_of_map l (AcrF l n) (algebraMap _ _) n (fun A x => acr_kill l A n x) (des_Acr l h.1 h.2.1 h.2.2.1 n) s hw
  · exact des_of_map l (FilF l n r) (algebraMap _ _) n (fun A x => fil_kill l A n r x) (des_Fil l h n r) s hw

end CrystallineSemistableComparison.D
end
end

section
set_option backward.isDefEq.respectTransparency false

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem out : Out l := out_of_rin l (CrystallineSemistableComparison.R.forD l)



theorem inWm_iff [IsLocalRing (Ob l)] (s : Ainf l) : InWm l s ↔ WittVector.map (IsLocalRing.residue (Ob l)) s = 0 := by
  rw [WittVector.ext_iff]
  refine forall_congr' fun i => ?_
  rw [WittVector.map_coeff, WittVector.zero_coeff, IsLocalRing.residue_eq_zero_iff]
  rfl

theorem isLocalRing_Ob (h : ObFacts l) : IsLocalRing (Ob l) := by
  obtain ⟨_, _, _⟩ := h
  infer_instance


end CrystallineSemistableComparison.D
end
