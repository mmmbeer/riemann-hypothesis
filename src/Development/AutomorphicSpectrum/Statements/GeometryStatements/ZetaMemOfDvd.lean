import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj

noncomputable section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

abbrev thLevel (l : Level H) {R : ℕ} (hR : R ^ 2 ∣ l.M) : Level H :=
  { l with A := R ^ 2, A_pos := Nat.pos_of_dvd_of_pos hR (lt_of_lt_of_le (by norm_num) l.three_le) }

theorem zeta_mem_of_dvd (c : Coeff l) {d : ℕ} (hd : d ∣ l.M) : zeta d ∈ c.F := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  obtain ⟨k, hk⟩ : d ∣ l.M' := hd.trans (Nat.dvd_lcm_left _ _)
  have hd0 : (d : ℂ) ≠ 0 := by
    rintro h
    have : d = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hk; omega
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h
    have : k = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hk; omega
  have : zeta d = zeta l.M' ^ k := by
    unfold zeta
    rw [← Complex.exp_nat_mul, hk]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem c.zeta_mem k

abbrev thCoeff (c : Coeff l) {R : ℕ} (hR : R ^ 2 ∣ l.M) : Coeff (thLevel l hR) :=
  ⟨c.F, c.fin, c.conj, zeta_mem_of_dvd c (Nat.lcm_dvd dvd_rfl hR), by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro z (rfl | rfl)
    · exact c.le (IntermediateField.subset_adjoin _ _ (by simp))
    · exact zeta_mem_of_dvd c hR⟩

namespace TauTest

variable {Xo : Moduli Dw l} {c : Coeff l}

open HostModel in

def sqLevel (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Level H where
  M := (H.d + 4) ^ 2
  three_le := by nlinarith [H.d_prime.two_le]
  odd := (level H 1 one_pos).odd.pow
  Mb := Ideal.span {(2 - H.rt) ^ 2}
  fromK := by
    apply le_antisymm
    · apply Ideal.span_mono
      rintro a rfl
      exact ⟨Ideal.mem_span_singleton_self _, pow_mem (sub_mem (ofNat_mem _ 2) (rt_mem_adjoin H)) 2⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [← Ideal.span_singleton_pow, Ideal.map_pow, map_bar_span_two_sub_rt, ← mul_pow,
      Ideal.span_singleton_mul_span_singleton, two_sub_rt_mul_two_add_rt, Ideal.span_singleton_pow, Nat.cast_pow]
  coprime := by
    rw [← Ideal.span_singleton_pow, Ideal.map_pow, map_bar_span_two_sub_rt, ← Ideal.isCoprime_iff_sup_eq]
    exact ((Ideal.isCoprime_span_singleton_iff _ _).2 (isCoprime_two_sub_rt_two_add_rt H)).pow
  A := 1
  A_pos := one_pos

end TauTest

end GlobalTheory.CompanionTheory.Ar.Rec
