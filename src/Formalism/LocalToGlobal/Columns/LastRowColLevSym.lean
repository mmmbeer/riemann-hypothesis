import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.Columns.RecLevelSym

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TopG

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure TopNum (R : Ranks) (i : ℕ) : Prop where
  a_eq : R.r + (i + 1 - 1) * R.t = R.N i
  a_le : R.r + (i + 1 - 1) * R.t ≤ (R.N (i + 1) - 1) + 0
  c0 : cOf R i = 0

theorem topNum_of {m2 : ℕ} (hm : R.m = m2 + 2) : TopNum R (m2 + 1) where
  a_eq := by
    have h := xt_a_eq (R := R) hm
    have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
    rwa [e] at h
  a_le := by
    have h := xt_a_eq (R := R) hm
    have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
    rw [e] at h
    rw [h]
    unfold Ranks.N
    have e2 : (m2 + 1 + 1) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
    omega
  c0 := xt_cOf hm

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xtPhiTopG_congr (hX : X.Ok) (hPr : Pr.Ok) {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hD : ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x' = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTopG
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [if_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')

theorem xtPhiTopG_int {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0)) (h : PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x ≠ 0) :
    ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i →
      IntAt P (LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  unfold PhiTopG at h
  rw [if_pos hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, if_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (hn.a_eq.symm ▸ hp')
  · simp only [if_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (hn.a_eq.symm ▸ hp')

def topDat (i : ℕ) (P : rowSG Pr sel mu) (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y) y''

theorem XiTop_eq {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x *
      ∏ P : rowSG Pr sel mu, topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem xt_last_lt (R : Ranks) (j : ℕ) : R.N j - 1 < R.N j := by have := R.N_pos j; omega

theorem xt_atNL (j : ℕ) (a : Sp X.E (R.N j)) : atNL X.E (R.N j) (R.N j - 1) a = a ⟨R.N j - 1, xt_last_lt R j⟩ := by
  unfold atNL
  rw [dif_pos (xt_last_lt R j)]
  rfl

theorem xt_split {P : HeightOneSpectrum (𝓞 X.E)} (j : ℕ) (a : Sp X.E (R.N j)) :
    (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prXpG X.E (R.N j) a i)) ∧ IntAt P (atNL X.E (R.N j) (R.N j - 1) a) := by
  rw [xt_atNL]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.1 < R.N j - 1
    · exact h1 ⟨i.1, by omega⟩
    · have : i = ⟨R.N j - 1, xt_last_lt R j⟩ := Fin.ext (by show i.1 = R.N j - 1; have := i.2; omega)
      rw [this]
      exact h2

theorem topDat_congr (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y y₁ : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (hy : ∀ j, IntAt P.1 ((qOf P.1 : X.E) * y'' j))
    (H : ∀ j : Fin (R.N i), ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) ↔ ∀ l, IntAt P.1 (y₁ (Pi.single j 1) l)) ∧
      ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) → ∀ l, redP P.1 (y (Pi.single j 1) l) = redP P.1 (y₁ (Pi.single j 1) l))) :
    topDat Ch sel mu cst i P y y'' = topDat Ch sel mu cst i P y₁ y'' := by
  classical
  have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R i)
    (n' := R.N i) (n := R.N (i + 1) - 1) (N := R.N (i + 1)) hn.c0 (PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1)
    (fun x x' h => xtPhiTopG_congr Ch mu hX hPr hn cst.sharp hP x x' h) (fun x h => xtPhiTopG_int Ch mu hn cst.sharp hP x h)
    (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXpG X.E (R.N (i + 1))) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1))
    (fun a => xt_split (i + 1) a) y (prXpG X.E (R.N (i + 1)) ∘ₗ y₁) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y₁)
    (fun j => ⟨(H j).1.trans (xt_split (i + 1) _), fun hall => ⟨fun l => (H j).2 hall _, by
      show redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _) = redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _)
      rw [xt_atNL, xt_atNL]
      exact (H j).2 hall _⟩⟩) y'' hy
  unfold topDat ftY
  rw [if_pos hP, if_pos hP]
  exact key

theorem topDat_int {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (h : topDat Ch sel mu cst i P y y'' ≠ 0) (j : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 (y (Pi.single j 1) l) := by
  classical
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  refine (xt_split (i + 1) (y (Pi.single j 1))).2 ⟨fun l => ?_, ?_⟩ l
  · have := xtPhiTopG_int Ch mu hn cst.sharp hP _ h1 l.1 j.1 l.2 j.2
    rwa [xtEntB hn.c0 _ (by have := l.2; omega) j.2, LinearMap.comp_apply, LinearMap.comp_apply, xtRes j.2] at this
  · unfold ftY at h2
    rw [if_pos hP] at h2
    by_contra h3
    exact h2 (if_neg fun hh => h3 (hh j))

end TopG

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Std

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem xt_sum_single {a b : ℕ} (z : HomE E a b) (v : Sp E a) : z v = ∑ j, v j • z (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (v j) : Sp E a) = v j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul]

theorem xt_map_std {a b : ℕ} (z : HomE E a b) (hz : ∀ j l, IntAt P (z (Pi.single j 1) l)) {v : Sp E a} (hv : v ∈ stdAt E a P) :
    z v ∈ stdAt E b P := by
  rw [ciMem_stdAt] at hv ⊢
  intro l
  rw [xt_sum_single z v, Finset.sum_apply]
  exact ciIntAt_sum _ _ fun j _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hv j).mul (hz j l)

end Std

section Law

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def TopLawG (m2 : ℕ) (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)),
    (∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x)) →
    ∀ y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)), (∀ j l, IntAt w.1 (y (Pi.single j 1) l)) →
      rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ
            (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))

def LastRow {j : ℕ} (Λm : LevFam X.E X.K (R.N j) Pr.vGs) : Prop :=
  ∀ (w : Pr.vGs), ∀ h' ∈ (Λm w).H, ∀ l : Fin (R.N j),
    (h'.1 : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) ⟨R.N j - 1, xt_last_lt R j⟩ l = if l.1 = R.N j - 1 then 1 else 0

variable {Ch sel mu cst L}

theorem topDat_law (hc : cst.Ok) {m2 : ℕ} (hn : TopNum R (m2 + 1)) {Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs} {b : L.β (m2 + 1)}
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm)
    (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1))
    (hκ : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x))
    (hκ' : ∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x))
    (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))) (hδ : κ.1 y₁ - y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1)
    (hq : ((qOf w.1 : ℕ) : X.E) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1) :
    rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
        topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ =
      (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
        topDat Ch sel mu cst (m2 + 1) w y y₂ := by
  have hk : ∀ v, κ.1 v ∈ stdAt X.E (R.N (m2 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1)) w.1 := κ.2
  have hk' : ∀ v, κ'.1 v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := κ'.2
  by_cases hint : ∀ j l, IntAt w.1 (y (Pi.single j 1) l)
  ·
    have hF : ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap)) y₁ =
        ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₂ := by
      have e1 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) =
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y) ∘ₗ κ.1.toLinearMap := rfl
      rw [e1, ftY_move2 sel mu cst hc w hw κ _ y₂ y₁ hδ hq]
      set ζ : Sp X.E (R.N (m2 + 1)) →ₗ[X.E] X.E :=
        atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y - atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y with hζdef
      have e2 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y =
          atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y + ζ := by rw [hζdef]; abel

      have hζq : ∀ i, IntAt w.1 (ζ (Pi.single i 1) / (qOf w.1 : X.E)) := by
        intro i
        set v := y (Pi.single i 1) with hv
        have hvs : v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (ciMem_stdAt _ _).2 (hint i)
        have hvs' : κ'.1.symm v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (hk' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hvs)
        have h1 := hκ' _ hvs'
        rw [LinearEquiv.apply_symm_apply] at h1
        have h2 : redV w.1 (κ'.1.symm v) = h'.1.1.mulVec (redV w.1 v) := by
          rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        have h3 : redP w.1 (κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) = redP w.1 (v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) := by
          have h20 := congrFun h2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
          have e : (h'.1.1.mulVec (redV w.1 v)) ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ = redV w.1 v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
            show ∑ l, h'.1.1 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ l * redV w.1 v l = _
            rw [Finset.sum_eq_single (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1)))]
            · rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩, if_pos rfl, one_mul]
            · intro l _ hl
              rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 l, if_neg (fun hh => hl (Fin.ext hh)), zero_mul]
            · intro hh
              exact absurd (Finset.mem_univ _) hh
          exact h20.trans e
        have ha := (ciMem_stdAt _ _).1 hvs' ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have hb := (ciMem_stdAt _ _).1 hvs ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have e3 : ζ (Pi.single i 1) = κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ - v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
          rw [hζdef, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, xt_atNL, xt_atNL]
          rfl
        rw [e3]
        exact ciIntAt_div (ciQ_mem w.1) hu (ciIntAt_sub ha hb) (by rw [redP_sub ha hb, h3, sub_self])
      have hq0 : (qOf w.1 : X.E) ≠ 0 := ciQ_ne_zero hu
      have hζ : ∀ i, IntAt w.1 (ζ (Pi.single i 1)) := fun i => by
        have := (ciIntAt_q (q := qOf w.1)).mul (hζq i)
        rwa [mul_div_cancel₀ _ hq0] at this
      have hζy : IntAt w.1 (ζ y₂) := by
        have e4 : ζ y₂ = ∑ j, y₂ j * ζ (Pi.single j 1) := by
          conv_lhs => rw [← Finset.univ_sum_single y₂]
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have : (Pi.single j (y₂ j) : Sp X.E (R.N (m2 + 1))) = y₂ j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [this, map_smul, smul_eq_mul]
        rw [e4]
        refine ciIntAt_sum _ _ fun j _ => ?_
        have h1 := (ciMem_stdAt _ _).1 hq j
        rw [Pi.smul_apply, smul_eq_mul] at h1
        have h2 := h1.mul (hζq j)
        have e5 : ((qOf w.1 : ℕ) : X.E) * y₂ j * (ζ (Pi.single j 1) / (qOf w.1 : X.E)) = y₂ j * ζ (Pi.single j 1) := by
          field_simp
        rwa [e5] at h2
      rw [e2]
      exact fourierTwist_add_integral sel mu cst hc w hw _ ζ y₂ hζ hζy hq
    unfold topDat
    rw [hF, ← mul_assoc, hLaw w hw h h' κ κ' hκ hκ' y hint, mul_assoc]
  ·
    have r0 : topDat Ch sel mu cst (m2 + 1) w y y₂ = 0 := by
      by_contra hne
      exact hint fun j l => topDat_int Ch sel mu cst hn w hw y y₂ hne j l
    have l0 : topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ = 0 := by
      by_contra hne
      have hz := fun j l => topDat_int Ch sel mu cst hn w hw _ y₁ hne j l
      refine hint fun j l => ?_
      have h1 : κ.1.symm (Pi.single j 1) ∈ stdAt X.E (R.N (m2 + 1)) w.1 :=
        (hk _).1 (by rw [LinearEquiv.apply_symm_apply]; exact ciSingle_mem j)
      have h2 := xt_map_std _ hz h1
      have h3 : (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) (κ.1.symm (Pi.single j 1)) = κ'.1.symm (y (Pi.single j 1)) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [h3] at h2
      have h4 := (hk' _).2 h2
      rw [LinearEquiv.apply_symm_apply] at h4
      exact (ciMem_stdAt _ _).1 h4 l
    rw [r0, l0, mul_zero, mul_zero]

end Law

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Inv

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word}

open Classical in

theorem xiTop_inv (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {i : ℕ} (hn : TopNum R i)
    (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x z : HomE X.E (R.N i) (R.N (i + 1))) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiTop Ch sel mu cst i p Y p' (x + z) = XiTop Ch sel mu cst i p Y p' x := by
  obtain ⟨w0, hw0, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  have hphi : phiT X.K p.deco.1 p'.deco.1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) = phiT X.K p.deco.1 p'.deco.1 x := by
    refine phiT_add_mul X.K p.deco p'.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_
    · have h1 : Pr.piT u ∈ P.1.asIdeal := mem_asIdeal_of_mem_divs P.2
      rw [← hPr.piT_norm u]
      exact P.1.asIdeal.mul_mem_right _ h1
    · refine (mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w0,
        Submodule.smul_mem _ _ hw0, ?_⟩
      rw [smul_smul]
      unfold cBof
      push_cast
      rfl
  rw [XiTop_eq, XiTop_eq, hphi]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := hG w
  have hu := ciQ_notMem_sq hX hPr hw
  have hq0 : ((qOf w.1 : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have ef : frsF sel mu p w = p.deco.1.liftFr ⟨w.1, hw⟩ := by
    unfold frsF
    rw [dif_pos hw]
  obtain ⟨k, hk⟩ : ∃ k, cst.B = k + 1 := ⟨cst.B - 1, by have := hc.B_pos; omega⟩
  refine topDat_congr Ch sel mu cst hX hPr hc hn w hw _ _ _ (fun j => by rw [ef]; exact xtRepY_int sel mu cst p.deco Y hYm w hw j) fun j => ?_

  have h1 : frsF sel mu p w (Pi.single j 1) ∈ p.deco.1.at w.1 := (frame_mem_lattice_iff_std' sel mu p w hw _).2 (ciSingle_mem j)
  have h2 : w0 (frsF sel mu p w (Pi.single j 1)) ∈ localization₂ w.1.asIdeal p'.deco.1.N := hw0 w.1 (Finset.mem_union_right _ w.2) _ h1
  have h3 : (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) ∈ stdAt X.E (R.N (i + 1)) w.1 :=
    (frame_mem_lattice_iff_std' sel mu p' w hw _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h2)
  have e : ∀ l, inFr (frsF sel mu p w) (frsF sel mu p' w) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) (Pi.single j 1) l =
      inFr (frsF sel mu p w) (frsF sel mu p' w) x (Pi.single j 1) l + (qOf w.1 : X.E) *
        ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
          (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l) := by
    intro l
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smul_apply, map_add, Pi.add_apply]
    rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast, hk]
    congr 1
    field_simp
    ring
  have hd : ∀ l, IntAt w.1 ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
      (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l) := fun l =>
    ((xtIntAt_qpow (qOf w.1) k).mul (intAt_inv_qOf_pow_mul_cBof sel mu cst w)).mul ((ciMem_stdAt _ _).1 h3 l)
  refine ⟨forall_congr' fun l => ?_, fun _ l => ?_⟩
  · rw [e l]
    exact ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul (hd l))
  · rw [e l]
    exact redP_add_natCast_mul (ciQ_mem w.1) (hd l)

end Inv

section Thm

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word} {m2 : ℕ}

def CpTopEquivOn (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (Θm : LevQFam X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  CplEq2On (S := midGSD W sel mu L u m2 b) (S₁ := frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm) (ybCpl W sel mu cst L u m2 b hY)
    (fun p Y p' => cpTopK W Ch sel mu cst T (m2 + 1) p Y p')

variable {W Ch sel mu cst L}

set_option maxHeartbeats 1600000 in

theorem cpTopEquivOn_of (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hn : TopNum R (m2 + 1))
    (T : ChTh W sel mu u m2)
    (hOk : ThDist.Ok (T.th (m2 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
      (colValF W sel mu u (m2 + 1 + 1)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1)))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (Θm : LevQFam X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K)))
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm) :
    CpTopEquivOn W Ch sel mu cst L T b hY Λm Θm := by
  classical
  intro g g' p (Y : Set (Sp X.E (R.N (m2 + 1)))) p' hYm
  change Y ∈ ybSet sel mu cst p.deco.1.N at hYm
  have hT : 0 < Pr.T u := (hPr.T_prime u).pos
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  choose κ hκ hκr using fun w : rowSG Pr sel mu => frsF_smul sel mu p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w (hG w)
  choose κ' hκ' hκr' using fun w : rowSG Pr sel mu => frsF_smul sel mu p' Λm Θm g' w (hG w)
  have hfr : frsF sel mu (g • p) = fun w => g.1.1 * frsF sel mu p w * (κ w).1 := funext hκ
  have hfr' : frsF sel mu (g' • p') = fun w => g'.1.1 * frsF sel mu p' w * (κ' w).1 := funext hκ'
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hN' : IsSdLat p'.deco.1.N := ⟨p'.deco.2.lat, p'.deco.2.uni⟩
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hdeco' : (g' • p').deco = (g'.1, (g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs)) • p'.deco := rfl
  have hYm1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (gmap g.1.1 p.deco.1.N) := (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm
  have hcc : (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (((Λm ⟨w.1, hG w⟩).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
          ((((L.levG (m2 + 1) b ⟨w.1, hG w⟩).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K) := by
    rw [prod_rowSG_eq_prod_vGs_of_QE_empty sel mu hQ (fun w =>
      (((Λm w).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) w, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
        ((((L.levG (m2 + 1) b w).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, levFam_chr_apply_coe, levFam_chr_apply_coe, Finset.prod_mul_distrib]
    simp only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
  show cpTopK W Ch sel mu cst T (m2 + 1) (g • p) ((fun v => g.1.1 v) '' (Y : Set (Sp X.E (R.N (m2 + 1))))) (g' • p') =
    (frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm).ρ g' ∘ₗ cpTopK W Ch sel mu cst T (m2 + 1) p Y p' ∘ₗ (midGSD W sel mu L u m2 b).ρ g⁻¹
  unfold cpTopK
  rw [if_pos (show (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N from hYm1), if_pos hYm, hfr, hfr']
  refine (kerOf_move hOk (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsF sel mu p') g.1 g'.1 κ κ'
    _ _ (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K)
    (fun x z hz => xiTop_inv Ch sel mu cst hX hPr hc hQ hn p Y p' x z hYm hz) ?_).trans ?_
  · intro x
    rw [XiTop_eq, XiTop_eq, hdeco, hdeco', phiT_smul]
    simp only [hfr, hfr', inFr_move]
    rw [hcc]
    refine prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ _ fun w => ?_
    have hw := hG w
    obtain ⟨hne, hdiff, hqm⟩ := ybSet_props2 sel mu cst hYm w hw
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frame_mem_lattice_iff_std' sel mu p w hw _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    obtain ⟨a, ha, hra⟩ : repY ((fun v => g.1.1 v) '' Y) ∈ (fun v => g.1.1 v) '' Y := representative_mem (hne.image _)
    have hr0 := representative_mem hne
    have e2 : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (g.1.1 a)) = (frsF sel mu p w).symm a := by
      rw [LinearEquiv.eq_symm_apply]
      apply g.1.1.injective
      have := LinearEquiv.apply_symm_apply (g.1.1 * frsF sel mu p w * (κ w).1) (g.1.1 a)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
      exact this
    have hδ : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (repY ((fun v => g.1.1 v) '' Y))) - (frsF sel mu p w).symm (repY Y) ∈
        stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← hra, e2, ← map_sub]
      exact hFst _ (hdiff _ ha _ hr0)
    have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← LinearEquiv.map_smul]
      exact hFst _ (hqm _ hr0)
    exact topDat_law hc hn hLaw hRow w hw ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩
      ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ (κ w) (κ' w) (hκr w) (hκr' w)
      (ciQ_notMem_sq hX hPr hw) _ _ _ hδ hq
  · show _ = (frmRho (colValF W sel mu u (m2 + 1 + 1)) Λm Θm g') ∘ₗ _ ∘ₗ
      (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g⁻¹)
    simp only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, levQFam_chr_eq_one_of_QE_empty sel mu hQ, mul_one, Prod.fst_inv, Prod.snd_inv, map_inv,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end Thm

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Top

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {Am : Amb X} {u : Pr.Word}

end Eq

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TI

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))



end TI

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section LR

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem xt_N_top {m2 : ℕ} (hm : R.m = m2 + 2) : R.N (m2 + 1 + 1) - 1 = R.r + R.m * R.t := by
  unfold Ranks.N Ranks.r
  rw [hm]
  have e : (m2 + 1 + 1) * (R.t + 1) = (m2 + 2) * R.t + (m2 + 2) := by ring
  omega

theorem lastRow_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : LastRow (colLevSym Ch (m2 + 1 + 1)) := by
  intro w h' hh' l
  rw [colLevSym_top_H Ch (by omega) w] at hh'
  have hN := xt_N_top (R := R) hm
  have hbt := HPar_le _ _ _ hh'.1
  by_cases hl : l.1 = R.N (m2 + 1 + 1) - 1
  · rw [if_pos hl, hh'.2 _ l (by rw [hl, hN])]
    have : (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1))) = l := Fin.ext hl.symm
    rw [this, Matrix.one_apply_eq]
  · rw [if_neg hl]
    refine mem_btG.1 hbt _ l ?_
    have hl2 : l.1 < R.r + R.m * R.t := by have := l.2; omega
    show coarse R.r (List.replicate R.m R.t) l.1 < coarse R.r (List.replicate R.m R.t) (R.N (m2 + 1 + 1) - 1)
    rw [hN]
    have e1 : coarse R.r (List.replicate R.m R.t) (R.r + R.m * R.t) = R.m + 1 := by
      unfold coarse blkIdx
      rw [if_neg (by omega), Nat.add_sub_cancel_left, blkIdx_replicate_of_le _ _ _ le_rfl]
    rw [e1]
    unfold coarse blkIdx
    split_ifs with h0
    · omega
    · have := blkIdx_replicate_lt R.t R.m (l.1 - R.r) (by omega)
      omega

end LR

end Formalism.L2.Col
end
end
