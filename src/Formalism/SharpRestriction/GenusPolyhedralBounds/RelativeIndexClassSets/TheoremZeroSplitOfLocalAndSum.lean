import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VEtNonnegOfTied
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsLatticeOfAdmissible
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem concl_of_nat {j : ℕ} (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hnu : ∀ la, 0 ≤ nus la) (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la))
    (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
        X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
        ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
            (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la) :
    Concl X S ka wL wF T nus β := by
  unfold Concl
  refine ⟨r, hr0, hrs, hrb, ?_⟩
  intro la e he V' hV'
  have hT : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hnu la)
  have he0 : (0 : ℤ) ≤ e := by
    have h := hT.trans he
    exact_mod_cast h
  lift e to ℕ using he0 with n
  have h := hloc la n (by exact_mod_cast he) V' hV'
  simpa only [Int.cast_natCast] using h


end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem lw_nonneg' (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K la := by
  simp only [lw]
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem sum_mul_lw (B : WeightFamilies.Prov D) (nn : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ) (s : Finset (HeightOneSpectrum (𝓞 B.KO)))
    (hs : nn.support ⊆ s) :
    ∑ la ∈ s, nn la * lw B.KO la = (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B := by
  rw [Finsupp.sum_of_support_subset nn hs (fun la v => v * WeightFamilies.lnN B la) (fun _ _ => zero_mul _),
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun la _ => ?_)
  simp only [lw, WeightFamilies.lnN, WeightFamilies.degO]
  ring

theorem quotCoreE (large₂ : SizeData₂ D) {CRm Ch Ah Cq Aq : ℝ} (ka : WeightFamilies.Wt D j) (T c : ℝ)
    (hE : ∃ be : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ, (∀ la, 0 ≤ be la) ∧
      (be.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cq Aq * ka.size ∧
      ∀ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
        Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
          WeightFamilies.MggK B CRm T c j ka = ⊤ →
        (∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) →
      ∃ nn : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ,
        (∀ la, ∃ ℓ : ℕ,
          WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
            (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) = ℓ ∧
          (ℓ : ℝ) ≤ nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) ∧
        (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤
          (WeightFamilies.rhoP B CRm T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size)
    (rq : ℕ) (hrq : rq = WeightFamilies.rhoP B CRm T c j ka) (th : Fin rq → B.Mlat j ka)
    (hspan : Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      WeightFamilies.MggK B CRm T c j ka = ⊤)
    (hsup : ∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    (∀ la, WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) ≠ ⊤) ∧
    Summable (fun la => ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ) *
        lw B.KO la) ∧
    (∑' la, ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ) *
        lw B.KO la) ≤ 2 * (rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  classical
  subst hrq
  obtain ⟨be, -, hbeS, hall⟩ := hE
  obtain ⟨nn, hnn, hnnS⟩ := hall th hspan hsup
  choose ℓ hℓeq hℓle using hnn
  have hlw : ∀ la, 0 ≤ lw B.KO la := fun la => lw_nonneg' B.KO la
  have hρ0 : 0 ≤ (WeightFamilies.rhoP B CRm T c j ka : ℝ) := Nat.cast_nonneg _
  have hg0 : ∀ la ∉ nn.support ∪ be.support, (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la = 0 := by
    intro la hla
    have h1 : nn la = 0 := by
      by_contra hne
      exact hla (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne))
    have h2 : be la = 0 := by
      by_contra hne
      exact hla (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne))
    rw [h1, h2]
    ring
  have hsg : Summable fun la => (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la :=
    summable_of_ne_finset_zero hg0
  have hle : ∀ la, (ℓ la : ℝ) * lw B.KO la ≤ (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la :=
    fun la => mul_le_mul_of_nonneg_right (hℓle la) (hlw la)
  have hsf : Summable fun la => (ℓ la : ℝ) * lw B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (hlw la)) hle hsg
  refine ⟨fun la => ?_, ?_, ?_⟩
  · rw [hℓeq la]
    exact ENat.coe_ne_top _
  · simp only [hℓeq, ENat.toNat_coe]
    exact hsf
  · simp only [hℓeq, ENat.toNat_coe]
    have hsub1 : nn.support ⊆ nn.support ∪ be.support := fun x hx => Finset.mem_union_left _ hx
    have hsub2 : be.support ⊆ nn.support ∪ be.support := fun x hx => Finset.mem_union_right _ hx
    calc ∑' la, (ℓ la : ℝ) * lw B.KO la
        ≤ ∑' la, (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la := Summable.tsum_le_tsum hle hsf hsg
      _ = ∑ la ∈ nn.support ∪ be.support, (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la := tsum_eq_sum hg0
      _ = ∑ la ∈ nn.support ∪ be.support, nn la * lw B.KO la +
            (WeightFamilies.rhoP B CRm T c j ka : ℝ) * ∑ la ∈ nn.support ∪ be.support, be la * lw B.KO la := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun la _ => by ring)
      _ = (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B +
            (WeightFamilies.rhoP B CRm T c j ka : ℝ) * ((be.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B) := by
        rw [sum_mul_lw B nn _ hsub1, sum_mul_lw B be _ hsub2]
      _ ≤ (WeightFamilies.rhoP B CRm T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * (WeightFamilies.PPv D large₂ Cq Aq * ka.size) :=
        add_le_add hnnS (mul_le_mul_of_nonneg_left hbeS hρ0)
      _ = 2 * (WeightFamilies.rhoP B CRm T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by ring

theorem two_T_sq_le_last {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1)
    (hi : i.1 + 1 = (D.R.sigW j).1) : 2 * T ^ 2 ≤ ka.aP τ i := by
  simp only [SetC] at h
  obtain ⟨-, -, -, h4, -, h6, -⟩ := h
  have h6' := h6 τ i hi
  have key : 2 * (T : ℝ) ^ 2 ≤ (ka.aP τ i : ℝ) := by linarith
  exact_mod_cast key

theorem lastPos_of_SetC {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : ka.LastPos := by
  have hT : 0 < T := by
    have h' := h
    simp only [SetC] at h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := h'
    exact hT
  simp only [WeightFamilies.Wt.LastPos]
  intro τ i hi
  have h2 := two_T_sq_le_last h τ i hi
  have h3 : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ hT
  linarith

theorem DF_pos_of_SetC {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : 0 < DF wL := by
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have hp : 0 < (D.R.sigW j).1 := by
    have := D.R.m_add_three_le_k
    show 0 < D.R.k + j - 1
    omega
  have hτ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    unfold Ranks.f Ranks.n
    positivity
  obtain ⟨τ⟩ := hτ
  set i : Fin (D.R.sigW j).1 := ⟨(D.R.sigW j).1 - 1, by omega⟩ with hi
  have hi1 : i.1 + 1 = (D.R.sigW j).1 := by simp only [hi]; omega
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold gapZ at h3
  rw [dif_neg hn] at h3
  have hTp : (0 : ℤ) < (Tp D j T : ℤ) := by unfold Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp, one_mul]
    unfold Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    push_cast
    nlinarith
  have h5 : 1 ≤ wL.aP τ i := by
    rw [← h3] at h4; exact_mod_cast h4
  unfold DF degP
  calc 0 < wL.aP τ i := h5
    _ ≤ ∑ i, wL.aP τ i := Finset.single_le_sum (f := fun i => wL.aP τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i := Nat.le_add_right _ _
    _ ≤ _ := Finset.single_le_sum (f := fun τ => (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

theorem RRv_pos' (D : D7) (CR : ℝ) : 0 < WeightFamilies.RRv D CR := by
  simp only [WeightFamilies.RRv]
  apply Real.rpow_pos_of_pos
  simp only [Formalism.BasicNotions.Host.rdE]
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (Int.cast_ne_zero.mpr h)

theorem PPv_pos_of_PolyDom {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka : WeightFamilies.Wt D j}
    (h : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) : 0 < WeightFamilies.PPv D large₂ C2 A2 := by
  simp only [PolyDom] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -, -, h18⟩ := h
  linarith

theorem modulus_pos_of_third_hypothesis {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR Bx : ℝ} {wL : WeightFamilies.Wt D j} {T : ℕ}
    (h : H3 large₂ H C2 A2 CR Bx wL T) : (0 : ℝ) < qq D := by
  simp only [qq]
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  exact Nat.cast_pos.mpr (lt_min h0 h1)

theorem cc_pos_of {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp}
    {C2 A2 CR Bx Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (hS : SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0) (h3 : H3 large₂ H C2 A2 CR Bx wL T)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) : 0 < cc D large₂ C2 A2 CR wL := by
  have hDF := DF_pos_of_SetC hS
  have hRR := RRv_pos' D CR
  have hPP := PPv_pos_of_PolyDom hP
  have hq := modulus_pos_of_third_hypothesis h3
  have hD : (0 : ℝ) < (DF wL : ℝ) := by exact_mod_cast hDF
  simp only [cc]
  exact div_pos (mul_pos (mul_pos hRR hPP) (pow_pos hD 2)) hq

theorem T_mul_cc_le_one {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp}
    {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka wL : WeightFamilies.Wt D j} {T : ℕ}
    (h3 : H3 large₂ H C2 A2 CR 0 wL T)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    (T : ℝ) * cc D large₂ C2 A2 CR wL ≤ 1 := by
  have hg : (1 : ℝ) ≤ g0 D := by
    simp only [g0]
    have hm := D.R.two_le_m
    have hr : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      omega
    have h5 : (2 : ℕ) * 5 ^ 4 = 1250 := by norm_num
    have hr' : 1 ≤ 2 * 5 ^ 4 * D.R.r := by
      rw [h5]
      omega
    exact_mod_cast hr'
  have hq := modulus_pos_of_third_hypothesis h3
  have hRR := RRv_pos' D CR
  have hPP := PPv_pos_of_PolyDom hP
  simp only [H3] at h3
  obtain ⟨-, h2, -⟩ := h3
  simp only [pow_zero, Real.rpow_zero, one_mul] at h2
  have hA : 0 ≤ (T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hRR.le) hPP.le) (sq_nonneg _)
  have key : (T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 ≤ (qq D : ℝ) := by
    calc (T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2
        ≤ ((T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2) * (g0 D : ℝ) :=
          le_mul_of_one_le_right hA hg
      _ = (T : ℝ) * (g0 D : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 := by ring
      _ ≤ (qq D : ℝ) := h2
  simp only [cc]
  calc (T : ℝ) * (WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 / (qq D : ℝ))
      = ((T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    _ ≤ 1 := (div_le_one hq).mpr key

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

section J

variable {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}







variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem vEt_nonneg_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (Q : LocalPointData G la) (ζ : PtsG G la) : 0 ≤ vEt Q ζ := by
  unfold vEt
  split_ifs with hj
  · exact div_nonneg (EReal.toReal_nonneg ((hB la (Q.y ζ)).1 hj).1) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · exact le_rfl

theorem nu_le_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) : Q.nu S ζ ≤ nus la + max 0 c * vEt Q ζ := by
  have hv := vEt_nonneg_comb hB Q ζ
  have hm : c * vEt Q ζ ≤ max 0 c * vEt Q ζ := mul_le_mul_of_nonneg_right (le_max_right _ _) hv
  by_cases hj : j < D.R.m
  · have h1 := ((hB la (Q.y ζ)).1 hj).2 ((hTie ζ).2.2.1 hj)
    rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
    have h2 : c / (2 * (G.iet : ℝ)) * (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal = c * vEt Q ζ := by
      unfold vEt
      rw [if_pos hj]
      ring
    rw [h2] at h1
    unfold LocalPointData.nu
    linarith
  · have h1 := (hB la (Q.y ζ)).2 (not_lt.1 hj)
    rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
    have h2 : 0 ≤ max 0 c * vEt Q ζ := mul_nonneg (le_max_left _ _) hv
    unfold LocalPointData.nu
    linarith

theorem Net_nonneg_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (hj : j < D.R.m) (Q : LocalPointData G la) : 0 ≤ Q.Net := by
  unfold LocalPointData.Net
  exact finsum_nonneg fun ζ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (EReal.toReal_nonneg ((hB la (Q.y ζ)).1 hj).1)

theorem rLa_nonneg_comb {S : Scal B} {c' : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c' nus)
    (Q : LocalPointData G la) (CRm : ℝ) (T : ℕ) (c : ℝ) : 0 ≤ rLa Q CRm T c := by
  unfold rLa
  have h1 : (0 : ℝ) ≤ (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0) := by
    split_ifs with hj
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (le_max_left _ _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) (Net_nonneg_comb hB hj Q)
    · exact le_rfl
  have h2 : (0 : ℝ) ≤ (Q.Ila.toNat : ℝ) := Nat.cast_nonneg _
  exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg h2 h1)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem theta_le_msup_of_hypC {large₂ : SizeData₂ D} (X : PJ D B P j) {H : KHyp} {C2 A2 CR Bx CT : ℝ} (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (h : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) : X.Theta S ka wL wF T ≤ X.Msup ka :=
  Formalism.MainNotions.Gaps.T0.theta_le_msup_of_setC X S h.2.2.2.2.1 h.2.1

theorem span_Thc_of_hypC {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR Bx CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) :
    Submodule.span B.KO (X.Thc S.sF wF : Set (B.Cusp j wF)) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.s0 (X.wF0 wL wF) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤ := by
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PLam, -, -, hF, h0', hK⟩, -⟩ := hH
  exact ⟨span_eq_top_of_shortG hF, span_eq_top_of_shortG h0', span_eq_top_of_shortG hK⟩

end J

def LocalC (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la),
    InBasis G la → Q.InCurve → Q.InTie S → Q.InLift T → InContainZ G la S T → InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL) →
    Q.Ila ≠ ⊤ →
    ∀ e : ℕ, (T : ℝ) * nus la ≤ (e : ℝ) →
    ∀ V' : Submodule ((X j h1 h2).Kl la) ((X j h1 h2).Vl la), V' ≤ (X j h1 h2).locK la ((X j h1 h2).Msup ka) →
      (X j h1 h2).qlen la ((X j h1 h2).loc la ((X j h1 h2).Msup ka) ⊓ (X j h1 h2).ofK la V')
        ((X j h1 h2).loc la ((X j h1 h2).Theta S ka wL wF T) ⊓ (X j h1 h2).ofK la V') ≠ ⊤ ∧
      (((X j h1 h2).qlen la ((X j h1 h2).loc la ((X j h1 h2).Msup ka) ⊓ (X j h1 h2).ofK la V')
          ((X j h1 h2).loc la ((X j h1 h2).Theta S ka wL wF T) ⊓ (X j h1 h2).ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (Module.finrank ((X j h1 h2).Kl la) V' : ℝ) + rLa Q K.CRm T (cc D large₂ C2 A2 CR wL)

def SumC (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    ∀ Qf : ∀ la, LocalPointData G la, Heights Qf Gc PH Prw Pet →
    Summable (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ∧
    (∑' la, rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ≤
      (X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2

theorem theorem_zero_split_of_local_and_sum (hL : LocalC D B P) (hS : SumC D B P) : Conclusion1OfComb (D := D) (B := B) (P := P) := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd Qf
    tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP iB iC iT iLf iZ iM hB hHt
  obtain ⟨hrs, hrb⟩ := hS large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA
    G Gc PH Prw Pet Pd tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB Qf hHt
  exact concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
    hH.2.2.2.1.1 (fun la => rLa_nonneg_comb hB (Qf la) _ _ _) hrs hrb
    (fun la e he V' hV => hL large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA
      G Gc PH Prw Pet Pd tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB la (Qf la) (iB la) (iC la) (iT la)
      (iLf la tW (iC la) (iT la)) (iZ la) (iM la) (hHt.1 la) e he V' hV)

def LiftAll (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ), Q.Ok S CRm T c → Q.InLift T


end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end
