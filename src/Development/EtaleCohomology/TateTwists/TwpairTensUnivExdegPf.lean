import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.EtaleCohomology.TateTwists.EtaleTateTwistCupPairingOfTensorAndResolutionPro
import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

def SecSep : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U),
    (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b

lemma res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op).symm

lemma res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

lemma res_usmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (x : Sec F U) :
    Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Units.smul_def]; exact map_zsmul _ _ x

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

lemma leib_lift {R : Type} [CommRing R] {I J K T M L : Cx R} (τ : Pair I J T) (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U)
    (heq : ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c))
    (V : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (x : Tens I J V s) (b : Sec (K.X t) V) :
    Sec.map (L.d w (w + 1)) (m V s t w h (τ.lift V s x) b) = m V (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) (τ.lift V s x)) b +
          s.negOnePow • m V s (t + 1) (w + 1) (by omega) (τ.lift V s x) (Sec.map (K.d t (t + 1)) b) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
    rw [hx, hy]; abel
  | of p z =>
    obtain ⟨⟨s1, t1⟩, hp⟩ := p
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
      rw [hx, hy]; abel
    | tmul a1 b1 =>
      have hl : τ.lift V s (DirectSum.of _ ⟨(s1, t1), hp⟩ (a1 ⊗ₜ b1)) = τ.mul V s1 t1 s hp a1 b1 := by
        unfold Pair.lift
        rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof, TensorProduct.lift.tmul]
      simp only at hp
      rw [hl, τ.leibniz V s1 t1 s hp a1 b1]
      rw [heq V s1 t1 t s (t1 + t) w hp h (by omega) (by omega)]
      rw [ν'.leibniz V s1 (t1 + t) w (by omega), μ'.leibniz V t1 t (t1 + t) rfl]
      simp only [map_add, LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [heq V (s1 + 1) t1 t (s + 1) (t1 + t) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 (t1 + 1) t (s + 1) (t1 + t + 1) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 t1 (t + 1) s (t1 + t + 1) (w + 1) hp (by omega) (by omega) (by omega)]
      have hs : ((s.negOnePow : ℤˣ) : ℤ) = (s1.negOnePow : ℤ) * (t1.negOnePow : ℤ) := by
        rw [← Units.val_mul, ← Int.negOnePow_add, hp]
      rw [hs, mul_smul, smul_add]
      abel

end LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

open LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_leibniz_of_separated (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) :
    LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz := by
  intro R _ I J K T τ hτ M L μ' ν' m hnat heq U s t w h a b
  apply hsep R (L.X (w + 1)) U
  refine loc_mono (hτ.1 U s a) ?_
  rintro V g ⟨x, hx⟩
  rw [res_map, hnat, res_add, res_usmul, hnat, hnat, res_map, res_map, ← hx, leib_lift τ μ' ν' m heq]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensLocbij

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P)
    (h2 : Loc U Q) : Loc U (fun V g => P V g ∧ Q V g) := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem map_comp_apply' (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V W : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (p : P.obj (op U)) :
    (P.map (k ≫ g).op).hom p = (P.map k.op).hom ((P.map g.op).hom p) := by
  simp [op_comp, Functor.map_comp]

end LateralTheory.EtaleFoundations.TensLocbij
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem secmap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem secmap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun k => k.hom x) (φ.hom.naturality g.op)
  exact this.symm

noncomputable def pairPost {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact secmap_res (u.f w) g _
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) =
        Sec.map (u.f (w + 1)) (Sec.map (K.d w (w + 1)) (μ.mul U s t w h a b)) := by
      rw [secmap_comp, secmap_comp, u.comm]
    show Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz U s t w h a b]
    show Sec.map (u.f (w + 1)) _ = Sec.map (u.f (w + 1)) _ + _ • Sec.map (u.f (w + 1)) _
    rw [Sec.map, map_add, map_zsmul_unit]

def twpair_tens_univ_uniq : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K'), τ.Compat ν f g u → τ.Compat ν f g u' → u = u'

def twpair_tens_univ_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃ u : K ⟶ K', τ.Compat ν f g u

def twpair_tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0

theorem pairPost_compat {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') :
    μ.Compat (pairPost μ u) (𝟙 I) (𝟙 J) u := by
  intro U s t w h a b
  rfl

theorem lift_comp_eq {R : Type} [CommRing R] {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K')
    (hu : τ.Compat ν f g u) (hu' : τ.Compat ν f g u') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) :
    Sec.map (u.f w) (τ.lift V w x) = Sec.map (u'.f w) (τ.lift V w x) := by
  classical
  have key : ((u.f w).hom.app (op V)).hom ∘ₗ τ.lift V w = ((u'.f w).hom.app (op V)).hom ∘ₗ τ.lift V w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (hu V _ _ _ p.2 a b).trans (hu' V _ _ _ p.2 a b).symm
  exact congrArg (fun k => k x) key

theorem tens_univ_uniq_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_uniq := by
  intro R _ I J K τ hτ I' J' K' ν f g u u' hu hu'
  ext w U y
  apply hsep R (K'.X w) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop w y) ?_
  rintro V r ⟨x, hx⟩
  rw [secmap_res, secmap_res, ← hx]
  exact lift_comp_eq τ ν f g u u' hu hu' V w x

theorem sec_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [h]
  exact this

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact (h U.unop y).trans (h U.unop _).symm

theorem tens_univ_ge_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_ge := by
  intro R _ I J K τ hτ hI hJ
  have hK : ∀ w : ℤ, w < 0 → IsZero (K.X w) := by
    intro w hw
    apply isZero_of_sec
    intro U y
    apply hsep R (K.X w) U
    refine TensLocbij.loc_mono (hτ.1 U w y) ?_
    rintro V r ⟨x, hx⟩
    rw [← hx]
    classical
    have hl : τ.lift V w = 0 := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.zero_apply]
      rcases lt_or_ge p.1.1 0 with hs | hs
      · rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE I 0 p.1.1 hs) a, map_zero, LinearMap.zero_apply]
      · have ht : p.1.2 < 0 := by have := p.2; omega
        rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE J 0 p.1.2 ht) b, map_zero]
    rw [hl, LinearMap.zero_apply]
    exact (map_zero _).symm
  exact ⟨fun i hi => hK i ((ComplexShape.notMem_range_embeddingUpIntGE_iff (p := 0) i).1 hi)⟩

theorem etale_sheaf_sections_separated_holds : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep := by
  intro R _ F U a b hab
  obtain ⟨S, hS, hP⟩ := hab
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  exact (h2 S hS).isSeparatedFor.ext fun V g hg => hP V g hg

def twpair_tens_univ_exdeg : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ), ∃ φ : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map φ (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem tens_univ_ex_of (hdeg : twpair_tens_univ_exdeg) : twpair_tens_univ_ex := by
  intro R _ I J K τ hτ I' J' K' ν f g
  choose φ hφ using hdeg R τ hτ ν f g
  have hsep := etale_sheaf_sections_separated_holds
  refine ⟨⟨φ, ?_⟩, fun U s t w h a b => hφ w U s t h a b⟩
  rintro i j (hij : i + 1 = j)
  subst hij
  ext U y
  apply hsep R (K'.X (i + 1)) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop i y) ?_
  rintro V r ⟨x, hx⟩
  show Sec.res r (Sec.map (φ i ≫ K'.d i (i + 1)) y) = Sec.res r (Sec.map (K.d i (i + 1) ≫ φ (i + 1)) y)
  rw [secmap_res, secmap_res, ← hx]
  classical
  have key : ((K.d i (i + 1) ≫ φ (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i =
      ((φ i ≫ K'.d i (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e1 : Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (φ (i + 1)) (Sec.map (K.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    have e2 : Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (K'.d i (i + 1)) (Sec.map (φ i) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    change Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) = Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)
    have h1 := hφ (i + 1) V (p.1.1 + 1) p.1.2 (by have := p.2; omega) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
    have h2 := hφ (i + 1) V p.1.1 (p.1.2 + 1) (by have := p.2; omega) a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
    have hf : Sec.map (I'.d p.1.1 (p.1.1 + 1)) (Sec.map (f.f p.1.1) a) = Sec.map (f.f (p.1.1 + 1)) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) := by
      rw [secmap_comp, secmap_comp, f.comm]
    have hg : Sec.map (J'.d p.1.2 (p.1.2 + 1)) (Sec.map (g.f p.1.2) b) = Sec.map (g.f (p.1.2 + 1)) (Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
      rw [secmap_comp, secmap_comp, g.comm]
    rw [e1, e2, τ.leibniz, hφ i, ν.leibniz, hf, hg]
    simp only [Sec.map, map_add, map_zsmul_unit] at h1 h2 ⊢
    rw [h1, h2]
  exact (congrArg (fun k => k x) key).symm

theorem twpair_tens_univ_of (hdeg : twpair_tens_univ_exdeg) :
    LateralTheory.EtaleFoundations.twpair_tens_univ := by
  have hsep := etale_sheaf_sections_separated_holds
  have hex := tens_univ_ex_of hdeg
  intro R _ I J K τ hτ
  refine ⟨?_, tens_univ_ge_of hsep R τ hτ, fun u => ⟨pairPost τ u, pairPost_compat τ u⟩⟩
  intro I' J' K' ν f g
  obtain ⟨u, hu⟩ := hex R τ hτ ν f g
  exact ⟨u, hu, fun u' hu' => tens_univ_uniq_of hsep R τ hτ ν f g u' u hu' hu⟩

end LateralTheory.EtaleFoundations
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExDeg

variable {R : Type} [CommRing R]

noncomputable def tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) :
    Tens I J V w →ₗ[ULift.{1} R] Tens I' J' V w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op V)).hom ((g.f p.1.2).hom.app (op V)).hom

theorem lift_res {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res k w x) = Sec.res k (τ.lift U w x) := by
  classical
  have key : τ.lift V w ∘ₗ Tens.res k w = ((K.X w).obj.map k.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (τ.nat k p.1.1 p.1.2 w p.2 a b).symm
  exact congrArg (fun m => m x) key

theorem lam_res {I J I' J' K : Cx R} (ν : Pair I' J' K) (f : I ⟶ I') (g : J ⟶ J') {V U : Scheme.{0}} (k : V ⟶ U)
    (w : ℤ) (x : Tens I J U w) :
    ν.lift V w (tmap f g V w (Tens.res k w x)) = Sec.res k (ν.lift U w (tmap f g U w x)) := by
  classical
  have key : (ν.lift V w ∘ₗ tmap f g V w) ∘ₗ Tens.res k w =
      ((K.X w).obj.map k.op).hom ∘ₗ (ν.lift U w ∘ₗ tmap f g U w) := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Tens.res, tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift,
      DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e := ν.nat k p.1.1 p.1.2 w p.2 (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b)
    rw [secmap_res, secmap_res] at e
    exact e.symm
  exact congrArg (fun m => m x) key

theorem lam_zero {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) (hx : τ.lift V w x = 0) :
    ν.lift V w (tmap f g V w x) = 0 := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) V
  refine TensLocbij.loc_mono (hτ.2 V w x hx) ?_
  intro W k hk
  rw [← lam_res, hk, map_zero, map_zero]
  exact (map_zero _).symm

theorem lam_eq {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (V : Scheme.{0}) (w : ℤ) (x x' : Tens I J V w) (hx : τ.lift V w x = τ.lift V w x') :
    ν.lift V w (tmap f g V w x) = ν.lift V w (tmap f g V w x') := by
  have := lam_zero τ hτ ν f g V w (x - x') (by rw [map_sub, hx, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sheafT (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y :=
  (TensLocbij.map_comp_apply' R F.obj k g y).symm

def sv {I J K : Cx R} (τ : Pair I J K) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sieve U where
  arrows V g := ∃ x, τ.lift V w x = Sec.res g y
  downward_closed := by
    rintro V W g ⟨x, hx⟩ k
    exact ⟨Tens.res k w x, by rw [lift_res, hx, res_comp]⟩

theorem sv_cov {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    sv τ w y ∈ Scheme.etaleTopology.{0} U := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  exact Scheme.etaleTopology.superset_covering (fun V g hg => hP V g hg) hS

noncomputable def fam {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Presieve.FamilyOfElements ((K'.X w).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (sv τ w y).arrows :=
  fun V _ hk => (ν.lift V w (tmap f g V w hk.choose) : Sec (K'.X w) V)

theorem fam_compat {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    (fam τ ν f g w y).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ heq
  show Sec.res g₁ (ν.lift Y₁ w (tmap f g Y₁ w h₁.choose)) = Sec.res g₂ (ν.lift Y₂ w (tmap f g Y₂ w h₂.choose))
  rw [← lam_res, ← lam_res]
  apply lam_eq τ hτ
  rw [lift_res, lift_res, h₁.choose_spec, h₂.choose_spec, res_comp, res_comp, heq]

noncomputable def glue {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) : Sec (K'.X w) U :=
  (sheafT (K'.X w) _ (sv_cov τ hτ w y)).amalgamate _ (fam_compat τ hτ ν f g w y)

theorem glue_spec {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) {V : Scheme.{0}} (k : V ⟶ U)
    (x : Tens I J V w) (hx : τ.lift V w x = Sec.res k y) :
    Sec.res k (glue τ hτ ν f g w y) = ν.lift V w (tmap f g V w x) := by
  have hk : (sv τ w y).arrows k := ⟨x, hx⟩
  have := (sheafT (K'.X w) _ (sv_cov τ hτ w y)).valid_glue (fam_compat τ hτ ν f g w y) k hk
  refine this.trans ?_
  show ν.lift V w (tmap f g V w hk.choose) = _
  exact lam_eq τ hτ ν f g V w _ _ (hk.choose_spec.trans hx.symm)

end LateralTheory.EtaleFoundations.ExDeg

namespace LateralTheory.EtaleFoundations.ExDeg
variable {R : Type} [CommRing R]

theorem sv_loc {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {U : Scheme.{0}} (w : ℤ) (y : Sec (K.X w) U) :
    Loc U fun V k => (sv τ w y).arrows k :=
  ⟨sv τ w y, sv_cov τ hτ w y, fun _ _ h => h⟩

theorem glue_add {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (y₁ y₂ : Sec (K.X w) U) :
    glue τ hτ ν f g w (y₁ + y₂) = glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂ := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (TensLocbij.loc_and (sv_loc τ hτ w y₁) (sv_loc τ hτ w y₂)) ?_
  rintro V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  rw [glue_spec τ hτ ν f g w _ k (x₁ + x₂) (by rw [map_add, hx₁, hx₂]; exact (map_add _ _ _).symm)]
  have e : Sec.res k (glue τ hτ ν f g w y₁ + glue τ hτ ν f g w y₂) =
      Sec.res k (glue τ hτ ν f g w y₁) + Sec.res k (glue τ hτ ν f g w y₂) := map_add _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x₁ hx₁, glue_spec τ hτ ν f g w _ k x₂ hx₂, map_add, map_add]

theorem glue_smul {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U : Scheme.{0}} (w : ℤ) (c : ULift.{1} R) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (c • y) = c • glue τ hτ ν f g w y := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U
  refine TensLocbij.loc_mono (sv_loc τ hτ w y) ?_
  rintro V k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k (c • x) (by rw [map_smul, hx]; exact (map_smul _ _ _).symm)]
  have e : Sec.res k (c • glue τ hτ ν f g w y) = c • Sec.res k (glue τ hτ ν f g w y) := map_smul _ _ _
  rw [e, glue_spec τ hτ ν f g w _ k x hx, map_smul, map_smul]

theorem glue_res {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') {U U' : Scheme.{0}} (w : ℤ) (h : U' ⟶ U) (y : Sec (K.X w) U) :
    glue τ hτ ν f g w (Sec.res h y) = Sec.res h (glue τ hτ ν f g w y) := by
  apply etale_sheaf_sections_separated_holds R (K'.X w) U'
  refine TensLocbij.loc_mono (sv_loc τ hτ w (Sec.res h y)) ?_
  rintro _ k ⟨x, hx⟩
  rw [glue_spec τ hτ ν f g w _ k x hx, res_comp]
  rw [res_comp] at hx
  rw [glue_spec τ hτ ν f g w _ (k ≫ h) x hx]

noncomputable def phi {I J K I' J' K' : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) : K.X w ⟶ K'.X w :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun y => glue τ hτ ν f g w (U := U.unop) y
          map_add' := fun y₁ y₂ => glue_add τ hτ ν f g w y₁ y₂
          map_smul' := fun c y => glue_smul τ hτ ν f g w c y }
     naturality := by
       intro U U' h
       ext y
       exact glue_res τ hτ ν f g w h.unop y }⟩

theorem res_id {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.res (𝟙 U) y = y := by
  simp [Sec.res]

end LateralTheory.EtaleFoundations.ExDeg

open LateralTheory.EtaleFoundations.ExDeg in
theorem LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg_of : LateralTheory.EtaleFoundations.twpair_tens_univ_exdeg := by
  intro R _ I J K τ hτ I' J' K' ν f g w
  refine ⟨phi τ hτ ν f g w, ?_⟩
  intro U s t h a b
  classical
  have hx : τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      Sec.res (𝟙 U) (τ.mul U s t w h a b) := by
    rw [res_id]
    simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  have e := glue_spec τ hτ ν f g w _ (𝟙 U) _ hx
  rw [res_id] at e
  refine e.trans ?_
  simp only [tmap, DirectSum.lmap_lof, TensorProduct.map_tmul, Pair.lift, DirectSum.toModule_lof,
    TensorProduct.lift.tmul]
end
