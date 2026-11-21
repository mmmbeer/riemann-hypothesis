import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.SharpRestriction.FamCore
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

def TNorm {R : Ranks} (H : Host R) (T : ℕ) : Prop :=
  ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
    (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}

structure Fits (lb : Bool) (D : D7) {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (u0 : (Rt s).A)
    (T Lw β : ℕ) (Tstar Gam : ℝ) : Prop where
  host_eq : (⟨D.R, D.host⟩ : Σ R : Ranks, Host R) = ⟨Rt s, hostOf A u0 T Lw⟩
  word : ∀ u : D.what₂.Word, u = D.u₀
  letter : ∀ u l, D.s.letter u l = lb
  eta : ∀ j w, D.what₂.etaJ j w = 0
  Aj_eq : ∀ j w, D.what₂.Aj j w = 0
  T_eq : ∀ u, (D.mem u).A.T = T
  Tstar_eq : ∀ u, (D.mem u).A.Tstar = Tstar
  Gam_eq : ∀ u, (D.mem u).A.GamP = Gam
  Del_eq : (D.s.Del : ℝ) = 1
  hv : ∀ τ (i : Fin (D.R.k - 1)), (D.hc τ).v i = 24 - 4 * ((i : ℕ) : ℚ)
  hu0 : ∀ τ (h : 0 < D.R.k), (D.hc τ).u ⟨0, h⟩ = 113 / 2
  hu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k → (D.hcW u τ).u i = 55 / 2 - 4 * ((i : ℕ) : ℚ)
  hb : ∀ τ (j : Fin D.R.m), (D.hc τ).b j = β + 2 * ((s : ℚ) + 9) * ((j : ℕ) : ℚ)
  he : ∀ τ (j : Fin D.R.m), (D.hc τ).e j = β + ((s : ℚ) + 9) + 2 * ((s : ℚ) + 9) * ((j : ℕ) : ℚ)

def SizeDataAt : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x1 : ℝ, 1 < x1 ∧ ∀ x, x1 < x → ∃ (s B Lw β : ℕ) (Gam : ℝ), 1 ≤ β ∧ 1 < Gam ∧
    ∀ (lb : Bool) (D : D7) (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (u0 : (Rt s).A) (T : ℕ) (Tstar : ℝ),
      Real.exp (x ^ eps) ≤ T → Fits lb D A u0 T Lw β Tstar Gam →
      ∃ L : SizeData₂ D, L.sc.x = x ∧ L.sc.eps = eps ∧ L.CGam = 1 ∧ L.Cc = 2 ∧ L.Ct = eps ∧ L.LaG = x ^ eps ∧
        L.supp = ∅

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

section Norm

variable {R : Ranks} (H : Host R)

theorem conj_bE : H.conj (H.sqd) = - H.sqd := by
  have h1 := H.gal_sqd H.conj
  have h2 : H.gal H.conj = R.cc := H.galE_conjE
  rw [h2] at h1
  simpa [Formalism.HC.Frame.cc, c0] using h1

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem bE_integral : IsIntegral ℤ (H.sqd) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination bE_sq H

def bO : 𝓞 H.E := ⟨H.sqd, bE_integral H⟩

theorem tnorm_of (x y : ℤ) (T M : ℕ) (hT : (T : ℤ) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2)
    (hM : M = H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2) : TNorm H T := by
  have hbc : ((bO H : 𝓞 H.E) : H.E) = H.sqd := rfl
  have hco : (((1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H) : 𝓞 H.E)) : H.E) =
      1 + (M : H.E) * ((x : H.E) + (y : H.E) * H.sqd) := by
    rw [← hbc]; push_cast; rfl
  refine ⟨1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H), ?_, ?_, ?_⟩
  · rw [hco]
    have hb : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ _
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hb)))
  · rw [hco]
    have hT' : (T : H.E) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2 := by exact_mod_cast congrArg (Int.cast : ℤ → H.E) hT
    simp only [map_add, map_mul, map_one, map_natCast, map_intCast, conj_bE]
    rw [hT']
    linear_combination (-(M : H.E) ^ 2 * (y : H.E) ^ 2) * bE_sq H
  · rw [← hM, Ideal.mem_span_singleton]
    exact ⟨(x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H, by ring⟩

end Norm

theorem scale_w''_bounds (sc : Scale) (n : ℕ) (hn : 1 ≤ n) : 0 ≤ sc.w'' n ∧ sc.w'' n ≤ sc.b := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX : 1 ≤ sc.X' := Real.one_le_exp (by positivity)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : sc.w'' n = sc.b / (n * sc.X') := by
    simp only [Scale.w'', Scale.b', Scale.a]
    field_simp
  rw [e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ n * sc.X' := one_le_mul_of_one_le_of_one_le hn' hX
  nlinarith

def sizeDataOfAjZero (D : D7) (sc : Scale)
    (hTT : D.host.TT = ∅)
    (hAj : ∀ j w, D.what₂.Aj j w = 0)
    (hTu : ∀ u, sc.b ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ))
    (hb : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2)
    (hsplit : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound)
    (ho : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100))
    (hQS : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100))
    (j0 : ℕ) (hj0 : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0)
    (hLw : 10 * j0 + 20 ≤ D.host.Lw)
    (η Cc : ℝ) (hη : 0 < η)
    (hthick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
      sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + η + 1)
    (hthin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
      sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + η)
    (hcg : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
      (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
      (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ))))
    (hcv : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
      (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hcu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hbe : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η)
    (hSc : 0 < (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (Ct : ℝ) (htw : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ sc.x ^ Ct)
    (CGam : ℝ) (hCG : 0 < CGam)
    (hGam : ∀ u, Real.log (D.mem u).A.GamP = CGam * (D.R.m : ℝ) ^ 5 * D.R.f * sc.L)
    (LaG : ℝ) (hT2 : D.host.T2.card = 1) : SizeData₂ D where
  sc := sc
  aT := fun _ => 0
  aT_win := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  bT := fun _ => 0
  bT_ge := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_u := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_b := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  supp := ∅
  gain := fun _ _ => 0
  F := fun _ _ => 0
  E := fun _ _ _ => 0
  tau := fun _ => 0
  io := fun _ => 0
  gain_supp := fun _ _ _ => rfl
  F_supp := fun _ _ _ => rfl
  E_supp := fun _ _ _ _ => rfl
  tau_supp := fun _ _ => rfl
  io_supp := fun _ _ => rfl
  gain_g := fun _ _ _ => rfl
  b_le := hb
  untwisted := fun w _ j _ _ => ⟨hAj j w, rfl⟩
  not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
  drop := ∅
  drop_alt := fun _ => Set.notMem_empty _
  F_conj := fun _ _ => rfl
  F_above := by intros; rfl
  j0 := j0
  logFiveDepth_le := hj0
  weightLength_ge_depth := hLw
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := hsplit
  o_tie := ho
  QS_tie := hQS
  NuLat := fun _ => ⊤
  de2 := (D.host.T2.card : ℝ) / D.R.n
  thickDensity_pos := by
    have : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.toFrame.ord_pos
    rw [hT2]; positivity
  thickDensity_le_one := by
    have : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.toFrame.ord_pos
    rw [hT2, div_le_one (by linarith)]; simpa using this
  typeDensity_eq_card_div := rfl
  LaG := LaG
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := η
  Cc := Cc
  win_thick := hthick
  win_top := fun _ _ _ _ t _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  win_thin := hthin
  cloud_gap := hcg
  cloud_v := hcv
  cloud_u := hcu
  be_close := hbe
  Sc_pos := hSc
  Sc_eq := rfl
  etaSz_pos := hη
  TTw := fun _ => Finset.univ
  TTw_full := fun _ _ => rfl
  Ct := Ct
  t_win := htw
  CGam := CGam
  CGam_pos := hCG
  Gam_eq := hGam
  wPart := fun _ _ _ _ => 1
  wPart_ge := fun _ _ _ _ => le_rfl
  lenMN := fun _ _ => 0

theorem exists_odd (L : ℝ) (hL : 20 < L) : ∃ s : ℕ, L ≤ ((2 * s + 15 : ℕ) : ℝ) ∧ ((2 * s + 15 : ℕ) : ℝ) < L + 2 := by
  refine ⟨⌈(L - 15) / 2⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil ((L - 15) / 2)
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (L - 15) / 2)
    push_cast
    linarith


end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField



variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))



end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

def dlogQ (d : ℕ) (hd : d.Prime) : ℝ :=
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d) 1).re


structure QDGood (x eps : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  q_lo : Real.exp (x ^ (eps / 5) / 2) < q
  q_hi : (q : ℝ) ≤ Real.exp (x ^ (eps / 5))
  d_lo : Real.exp (x ^ (eps / 5) * Real.log x ^ 2 / 2) < d
  d_hi : (d : ℝ) ≤ Real.exp (x ^ (eps / 5) * Real.log x ^ 2)
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ x ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1
  dlog : |dlogQ d hyp.2.1| ≤ x ^ eps

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

section General

variable {R : Ranks} (H : Host R)

theorem norm_form (u v : ℤ) (T M : ℕ) (hT : (T : ℤ) = (1 + M * u) ^ 2 + H.d * (M * v) ^ 2) :
    ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
      (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)} := by
  have hbc : ((bO H : 𝓞 H.E) : H.E) = H.sqd := rfl
  have hco : (((1 + (M : 𝓞 H.E) * ((u : 𝓞 H.E) + (v : 𝓞 H.E) * bO H) : 𝓞 H.E)) : H.E) =
      1 + (M : H.E) * ((u : H.E) + (v : H.E) * H.sqd) := by
    rw [← hbc]; push_cast; rfl
  refine ⟨1 + (M : 𝓞 H.E) * ((u : 𝓞 H.E) + (v : 𝓞 H.E) * bO H), ?_, ?_, ?_⟩
  · rw [hco]
    have hb : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ _
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hb)))
  · rw [hco]
    have hT' : (T : H.E) = (1 + M * u) ^ 2 + H.d * (M * v) ^ 2 := by exact_mod_cast congrArg (Int.cast : ℤ → H.E) hT
    simp only [map_add, map_mul, map_one, map_natCast, map_intCast, conj_bE]
    rw [hT']
    linear_combination (-(M : H.E) ^ 2 * (v : H.E) ^ 2) * bE_sq H
  · rw [Ideal.mem_span_singleton]
    exact ⟨(u : 𝓞 H.E) + (v : 𝓞 H.E) * bO H, by ring⟩



theorem primesOver_ncard (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have himg : (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' placesOver E p =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      have hmem : ((p : ℕ) : 𝓞 E) ∈ I := by
        have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
        simpa using this
      have hne : I ≠ ⊥ := by
        rintro rfl
        have h0 : ((p : ℕ) : 𝓞 E) = 0 := by simpa using hmem
        exact hp.ne_zero (by exact_mod_cast h0)
      exact ⟨⟨I, hI, hne⟩, hmem, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

end General


theorem form_mod {T M d : ℕ} {u v : ℤ} (hT : (T : ℤ) = (1 + M * u) ^ 2 + d * (M * v) ^ 2) : T ≡ 1 [MOD M] := by
  rw [← Int.natCast_modEq_iff]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨2 * u + M * u ^ 2 + d * M * v ^ 2, by rw [hT]; push_cast; ring⟩

def Yof (R : Ranks) (x eps : ℝ) : ℝ := ((R.k : ℝ) * Real.exp (x ^ eps)) ^ 8

structure Fld (R : Ranks) (x eps : ℝ) extends Formalism.HC.HostAx R.toFrame where
  flPS : toHostRaw.PsQ
  sqq : E
  sqq_sq : sqq ^ 2 = -(q : E)
  gal_sqq : ∀ σ : E ≃ₐ[ℚ] E, σ sqq = ((((gal σ).1.1 : ℤˣ) : ℤ) : E) * sqq
  QS_exact : toHostRaw.Exact
  QS_le : QS ≤ R.n ^ 2
  o_pow : R.toFrame.o ^ 64 ≤ 2 ^ R.e
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → 4 * l ≤ ⌊x ^ (eps / 5)⌋₊
  good : QDGood x eps q d
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)

structure Base (R : Ranks) (x eps Cp CT : ℝ) extends Fld R x eps where
  q_big : 4 * R.t * R.r + 1 < q
  d_big : 4 * R.t * R.r + 1 < d
  g0 : ℕ
  g1 : ℕ
  first_prime_isPrime : g0.Prime
  second_prime_isPrime : g1.Prime
  g_ne : g0 ≠ g1
  first_prime_in_window : Yof R x eps ≤ g0 ∧ (g0 : ℝ) ≤ 2 * Yof R x eps
  second_prime_in_window : Yof R x eps ≤ g1 ∧ (g1 : ℝ) ≤ 2 * Yof R x eps
  first_prime_norm_form : ∃ u v : ℤ, (g0 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  second_prime_norm_form : ∃ u v : ℤ, (g1 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  bb : Disjoint (Formalism.CyclotomicNorms.BB R.r g0) (Formalism.CyclotomicNorms.BB R.r g1)
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_mod : pde ≡ 1 [MOD 15 * (QS * q * d)]
  pde'_mod : pde' ≡ 1 [MOD 15 * (QS * q * d)]
  pde_ne_g : pde ≠ g0 ∧ pde ≠ g1 ∧ pde' ≠ g0 ∧ pde' ≠ g1
  pde_log : Real.log pde < x ^ (eps / 3) ∧ Real.log pde' < x ^ (eps / 3)
  Cp_pos : 0 < Cp
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  T2 : Finset ℕ
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0
  second_set_no_relation : NoRel T2 Lw
  T2_card : (R.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card
  TT : Finset (R.A)

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

theorem cm_nonempty : B.cmType.Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [B.der.cmType.2.1]
  positivity

theorem bb_ex : ∃ 𝔟 : Ideal (𝓞 B.E),
    differentIdeal (𝓞 B.K) (𝓞 B.E) = 𝔟 * (B.conj • 𝔟) ∧ 𝔟 ⊔ B.conj • 𝔟 = ⊤ ∧
    ∀ σ : B.E ≃ₐ[ℚ] B.E, B.gal σ ∈ R.Psi → σ • 𝔟 = 𝔟 :=
  B.der.principal

theorem coprime_QS_of_mod {p : ℕ} (h : p ≡ 1 [MOD B.QS * B.q * B.d]) : Nat.Coprime p B.QS := by
  have h1 : p ≡ 1 [MOD B.QS] := h.of_dvd ⟨B.q * B.d, by ring⟩
  rw [Nat.Coprime, h1.gcd_eq, Nat.gcd_one_left]


end Base

def host2 (u0 : R.A) (ex : Finset ℕ) : Host R where
  toHostAx := B.toHostAx
  flPS := B.flPS
  sqq := B.sqq
  sqq_sq := B.sqq_sq
  gal_sqq := B.gal_sqq
  QS_exact := B.QS_exact
  QS_le := B.QS_le
  o_pow := B.o_pow
  small_le := B.small_le
  q_ne_three := by
    have h := B.q_big
    have ht : 1 ≤ R.t := by have := R.rank_add_five_le; omega
    have hr : 1 ≤ R.r := by have := R.two_le_m; unfold Ranks.r; omega
    have h1 : 1 ≤ R.t * R.r := Nat.mul_pos ht hr
    have e : 4 * R.t * R.r = 4 * (R.t * R.r) := by ring
    omega
  qd_big := ⟨B.q_big, B.d_big⟩
  splitBound := ⌊x ^ (eps / 5)⌋₊
  split_small := fun p hp h2 hB => B.good.split p hp h2 (by
    rcases Nat.eq_zero_or_pos ⌊x ^ (eps / 5)⌋₊ with h0 | h0
    · rw [h0] at hB; exact absurd hp.pos (by omega)
    · exact (Nat.cast_le.2 hB).trans (Nat.floor_le (Nat.pos_of_floor_pos h0).le))
  φ₀ := B.cm_nonempty.some
  φ₀_mem := B.cm_nonempty.some_mem
  𝔟 := B.bb_ex.choose
  𝔟_spec := ⟨B.bb_ex.choose_spec.1, B.bb_ex.choose_spec.2.1⟩
  𝔟_stable := B.bb_ex.choose_spec.2.2
  levelPrimes := {B.g0, B.g1, B.pde, B.pde'} ∪ ex.filter (fun p => Nat.Coprime p B.QS)
  g := ![B.g0, B.g1]
  g_prime := by intro i; fin_cases i; exacts [B.first_prime_isPrime, B.second_prime_isPrime]
  g_ne := by simpa using B.g_ne
  g_level := by intro i; fin_cases i <;> simp
  pde := B.pde
  pde' := B.pde'
  pde_prime := B.pde_prime
  pde'_prime := B.pde'_prime
  pde_ne := B.pde_ne
  pde_level := by simp
  pde_mod := ⟨B.pde_mod.of_mul_right _, B.pde'_mod.of_mul_right _⟩
  pde_ne_g := by
    obtain ⟨h1, h2, h3, h4⟩ := B.pde_ne_g
    intro i; fin_cases i
    · exact ⟨h1, h3⟩
    · exact ⟨h2, h4⟩
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  level_coprimeS := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | h
    · obtain ⟨u, v, h⟩ := B.first_prime_norm_form; exact B.coprime_QS_of_mod (form_mod h)
    · obtain ⟨u, v, h⟩ := B.second_prime_norm_form; exact B.coprime_QS_of_mod (form_mod h)
    · exact B.coprime_QS_of_mod (B.pde_mod.of_mul_left _)
    · exact B.coprime_QS_of_mod (B.pde'_mod.of_mul_left _)
    · exact h.2
  TT := B.TT
  T2 := B.T2
  u0 := u0
  Lw := B.Lw
  two_le_Lw := B.two_le_Lw
  second_set_range := B.second_set_range
  second_set_no_relation := B.second_set_no_relation
  CT2 := CT





end Formalism.MainNotions.Inhab

end
end
