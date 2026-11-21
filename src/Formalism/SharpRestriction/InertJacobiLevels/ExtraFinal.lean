import Formalism.SharpRestriction.InertJacobiLevels.TrivialDatumMultiplicitySpaceSubsingleton
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.InertJacobiLevels.AsmLed
import Formalism.SharpRestriction.InertJacobiLevels.EtaSz
import Formalism.SharpRestriction.InertJacobiLevels.GaugeExists
import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section

variable {R : Ranks} (H : Host R) (hc : Tau2 R → HCParam R) (etaF : ℝ) (Dn : ℕ) (hDel : (0 : ℚ) < (Dn : ℚ))
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * (Dn : ℚ))
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (hu : ∀ τ, FdegUniq R (hc τ))
  (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

def d7F : D7 := twistRecord H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw









set_option maxHeartbeats 2000000 in
theorem trivialFamily_heightValue_eq (hv' : ℝ) (sc : Scale) (aT : H.TT → ℤ) (η Sc dl C : ℝ) (u) :
    hVal (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) sc aT η Sc dl C u = hVal (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) sc aT η Sc dl C u := rfl



end

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def ej (R : Ranks) (p : HCParam R) (j : ℕ) : ℝ := if h : j - 1 < R.m then ((p.e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0



structure CoreLed (R : Ranks) (H : Host R) (hc : ↥(R.Psi) → HCParam R) (sc : Scale) (a b : ℕ → ℤ)
    (η Cc Ct : ℝ) (j0 : ℕ) (Del : ℝ) : Prop where
  aT_win : ∀ t ∈ H.TT, sc.a ≤ (a t.val : ℝ) ∧ (a t.val : ℝ) ≤ sc.a + sc.a / ((R.k : ℝ) * sc.x ^ (Scale.A / 2))
  bT_ge : ∀ t ∈ H.TT, sc.b' ≤ (b t.val : ℝ)
  top_u : ∀ g : ↥(R.Psi), ∀ t ∈ H.TT, ∀ h0 : 0 < R.k, (g : R.GG) = R.tau1 t →
    (((hc g).u ⟨0, h0⟩ : ℚ) : ℝ) = a t.val + ((R.k : ℝ) - 1) / 2 ∧
    (((hc g).u ⟨R.k - 1, by omega⟩ : ℚ) : ℝ) = -(b t.val : ℝ) - ((R.k : ℝ) - 1) / 2
  top_b : ∀ g : ↥(R.Psi), ∀ t ∈ H.TT, ∀ hm : 0 < R.m, (g : R.GG) = R.tau1 t →
    (((hc g).b ⟨0, hm⟩ : ℚ) : ℝ) - (b t.val : ℝ) > ((R.k : ℝ) - 1) / 2 + 3
  b_le : ∀ g j, (((hc g).b j : ℚ) : ℝ) ≤ sc.b ^ 2
  logFiveDepth_le : Real.logb 5 ((R.n : ℝ) * R.N R.m / R.m) ≤ j0
  weightLength_ge_depth : 10 * j0 + 20 ≤ H.Lw
  split_tie : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ H.splitBound
  secondTorsion_card_pos : 0 < H.T2.card
  secondTorsion_card_le : H.T2.card ≤ R.n
  win_thick : ∀ j, 1 ≤ j → j ≤ R.m → ∀ g : ↥(R.Psi), (g : R.GG) ∈ H.thickPlaces →
    sc.b ≤ ej R (hc g) j ∧ ej R (hc g) j ≤ sc.b + η + 1
  win_top : ∀ j, 1 ≤ j → j ≤ R.m → ∀ g : ↥(R.Psi), ∀ t ∈ H.TT, (g : R.GG) = R.tau1 t →
    (b t.val : ℝ) + sc.b' / sc.x ≤ ej R (hc g) j ∧ ej R (hc g) j ≤ (b t.val : ℝ) + sc.b' / sc.x + η
  win_thin : ∀ j, 1 ≤ j → j ≤ R.m → ∀ g : ↥(R.Psi), H.IsThin (g : R.GG) →
    sc.w'' R.n ≤ ej R (hc g) j ∧ ej R (hc g) j ≤ sc.w'' R.n + η
  cloud_gap : ∀ (g : ↥(R.Psi)) (h0 : 0 < R.k - 1), (g : R.GG) ∉ H.topPlaces →
    (R.k : ℝ) * (4 * Del) ≤ (((hc g).u ⟨0, by omega⟩ - (hc g).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
    (((hc g).u ⟨0, by omega⟩ - (hc g).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((R.k : ℝ) * (4 * Del))
  cloud_v : ∀ g (i : Fin (R.k - 1)), 0 ≤ (((hc g).v i : ℚ) : ℝ) ∧ (((hc g).v i : ℚ) : ℝ) ≤ (R.k : ℝ) * (4 * Del)
  cloud_u : ∀ g (i : Fin R.k), 1 ≤ i.1 → i.1 + 1 < R.k →
    0 ≤ (((hc g).u i : ℚ) : ℝ) ∧ (((hc g).u i : ℚ) : ℝ) ≤ (R.k : ℝ) * (4 * Del)
  be_close : ∀ g (i j : Fin R.m), |(((hc g).b i - (hc g).e j : ℚ) : ℝ)| ≤ η
  eta_pos : 0 < η
  Del_pos : 0 < Del
  t_win : 1 ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ sc.x ^ Ct

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def errPrimes (D : D7) : Finset ℕ :=
  haveI := D.wordFin
  ({D.host.g 0, D.host.g 1, D.host.d} : Finset ℕ) ∪ Finset.univ.image (fun u : D.what₂.Word => (D.mem u).A.T) ∪
    Finset.univ.biUnion (fun u : D.what₂.Word => (D.mem u).C.DGam.primeFactors)

open Classical in

def errSupp (D : D7) (sc : Scale) : Finset D.what₂.places.Pl :=
  (finite_resChar_le D (sc.X'' D.R.n)).toFinset ∪ (finite_resChar_mem D (errPrimes D)).toFinset

theorem Eval_off {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hw : w ∉ errSupp D L.sc) : Eval L X K c u j w = 0 := by
  classical
  let _ := D.wordFin
  rw [errSupp, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hw
  have h1 : ¬ ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n := hw.1
  have h2 : D.what₂.places.resChar w ∉ errPrimes D := hw.2
  refine Eval_above L X K c u j w (not_le.1 h1) ?_ ?_ ?_ ?_
  · intro h
    exact h2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨u, Finset.mem_univ _, h.symm⟩)))
  · intro h
    refine h2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h <;> simp [h]
  · intro h
    refine h2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    simp [h]
  · intro h
    refine h2 (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _, ?_⟩))
    exact Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, (D.mem u).C.DGam_pos.ne'⟩

variable {D : D7} {sc : Scale} {aT bT : D.host.TT → ℤ} {η Cc Ct CGam : ℝ} {j0 : ℕ}

def baseZ (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : SizeData₂ D :=
  baseL h Nu ∅ (fun _ _ _ => 0) (fun _ _ _ _ => rfl)

open Classical in

def baseE (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) : SizeData₂ D :=
  baseL h Nu (errSupp D sc ∪ S1) (Eval (baseZ h Nu) X K c)
    (fun u j w hw => Eval_off (baseZ h Nu) X K c u j w (fun h' => hw (Finset.mem_union_left _ h')))

open Classical in

theorem subset_supp_baseE (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) : S1 ⊆ (baseE h Nu S1 X K c).supp :=
  fun _ hw => Finset.mem_union_right _ hw


end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

def gdOf (R : Ranks) : GC.GD := ⟨R, ⟨∅, ∅, 0, fun _ => PrimeClass.splitK⟩, fun _ => 0⟩

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure CoreTie (R : Ranks) (H : Host R) (hc : ↥(R.Psi) → HCParam R) (sc : Scale) (Del : ℝ) (c : ℕ) : Prop where
  hw : 1 ≤ sc.w'' R.n
  c_le : (c : ℝ) ≤ 4 * ((R.k : ℝ) * (4 * Del))
  hcl : (R.k : ℝ) * (4 * Del) + ((R.k : ℝ) - 1) / 2 ≤ c
  hoff : ∀ g : ↥(R.Psi), (g : R.GG) ∉ H.topPlaces → ∀ i : Fin R.k,
    |(((hc g).u i : ℚ) : ℝ) - (((R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c
  hw1 : ∀ g, (c : ℝ) ≤ ej R (hc g) 1 - ((R.k : ℝ) + (2 * ((1 : ℕ) : ℝ) - 1) * ((R.t : ℝ) + 1)) / 2
  g_cls : ∀ i, H.cls (H.g i) = .splitK

def Core.Comparison₂ (X : Core) (sc : Scale) (Del : ℝ) (c : ℕ) : Prop := CoreTie X.1 X.2.1 X.2.2 sc Del c

structure RecMore (D : D7) (gatT : GatTies D) (sc : Scale) where

  mu_tw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ L : SizeData₂ D, L.sc = sc → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L j w = 0

  Aj0 : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0

  S0 : Finset D.what₂.places.Pl

  mu_0 : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ sc.X'' D.R.n ∨
    D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨ w ∈ S0

  pos : ∀ (L : SizeData₂ D) (X : G.Inst D L), X.bs = bsA → L.sc = sc → PosHyp gatT X

theorem fval_zero_of_tw {D : D7} {sc : Scale}
    (h : ∀ w, (((D.what₂.places.resChar w : ℕ) : ℝ) ≤ sc.X'' D.R.n ∨
      D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ)) → D.what₂.muAt w ≠ D.what₂.mu0)
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w = D.what₂.mu0) (L : SizeData₂ D) (hL : L.sc = sc) (j : ℕ) : Fval L j w = 0 := by
  subst hL
  have h1 : ¬ (((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n ∨
      D.what₂.places.resChar w ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ)) := fun h' => h w h' hw
  rw [not_or] at h1
  refine FvalP_above _ j (not_le.1 h1.1) (fun h' => h1.2 ?_) (fun h' => h1.2 ?_)
  · have h2 : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := h'
    rw [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 <;> simp [h2]
  · simp [h']

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev wtOf (D : D7) (a : ℕ → ℤ) : D.host.TT → ℤ := fun t => a (t : D.R.A).val

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure RecExtra (D : D7) (ep : ℕ → ℕ) where
  shape : Shape D
  ties : Ties D
  X : DivX D
  mjH : ∀ j, Subsingleton (X.MjH j).V
  kapR : X.kapR D.what₂.embLL = 1
  ep_tie : ∀ u w hg, (D.gat u w hg).e = ep (D.what₂.places.resChar w)
  kap_def : DV.KapDef D
  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u
  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D
  cover : NTw.TwCover D.ntw
  le : LevErr D
  served : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h
  gauge : GaugeExists D.host D.sp


end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.BasicNotions.Examples₂

section Base

variable {N : ℕ} [NeZero N]




end Base

section BaseA

variable {φ : Formalism.HC.Frame}

theorem bsA_add_nsmul (h t : φ.A) (i : ℕ) : bsA h (t + i • h) = bsA h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, bsA_step, ih]

theorem bsA_idem (h t : φ.A) : bsA h (bsA h t) = bsA h t := by
  obtain ⟨i, hi⟩ := bsA_eq h t
  rw [hi, bsA_add_nsmul, ← hi]

theorem bsA_unique (h x x' : φ.A) (i : ℕ) (e : bsA h x' = bsA h x + i • h) : bsA h x' = bsA h x := by
  rw [← bsA_idem h x', e, bsA_add_nsmul, bsA_idem]

end BaseA

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (sc : Scale) (eOf : ℕ → ℕ)

def baseB : D.what₂.Word → ℕ → Set (G.HH D) := fun _ p => {t | ∃ x, bsA (G.stepP D p) x = t}

def rOfB : D.what₂.Word → ℕ → ℕ := fun _ p => if (p : ℝ) < sc.p0 D.R.k then G.rG sc else 1

def recB : D7 := withGatCB D h0 (rOfB D sc) eOf (baseB D)

def tiesB : GatTies (recB D h0 sc eOf) := gatTiesCB D h0 (rOfB D sc) eOf (baseB D)

theorem stepP_of_gidx {T p : ℕ} (hg : GIdx D.host T p) : G.stepP D p = G.hP D p := by
  unfold G.stepP
  rw [if_neg]
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  have h2 : D.host.cls p = PrimeClass.signal := h
  rw [h1] at h2
  exact PrimeClass.noConfusion h2

theorem baseB_sep (u : D.what₂.Word) {T p : ℕ} (hg : GIdx D.host T p) :
    ∀ t ∈ baseB D u p, ∀ t' ∈ baseB D u p, ∀ i : ℕ, t' = t + i • G.hP D p → t' = t := by
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ i e
  rw [stepP_of_gidx D hg] at e ⊢
  exact bsA_unique _ _ _ i e

def posHypB {L : SizeData₂ (recB D h0 sc eOf)} (X : G.Inst (recB D h0 sc eOf) L) (hbs : X.bs = bsA) (hsc : L.sc = sc) :
    PosHyp (tiesB D h0 sc eOf) X where
  vOf := vOfCB D h0 (rOfB D sc) eOf (baseB D)
  inj := fun u w hg => by
    have h := vOfCB_injOn D h0 (rOfB D sc) eOf (baseB D) u w hg (baseB_sep D u hg)
    intro t ht t' ht' e
    have m : ∀ y, y ∈ G.reps X (D.what₂.places.resChar w) → y ∈ baseB D u (D.what₂.places.resChar w) := by
      intro y hy
      unfold G.reps at hy
      rw [hbs] at hy
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hy
      exact ⟨x, hx⟩
    exact h (m t ht) (m t' ht') e
  n_eq := fun u w hg t0 _ => withGatCB_n' D h0 (rOfB D sc) eOf (baseB D) u w hg _
  pos := fun u w hg t0 ht0 s => by
    have m : t0 ∈ baseB D u (D.what₂.places.resChar w) := by
      unfold G.reps at ht0
      rw [hbs] at ht0
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 ht0
      exact ⟨x, hx⟩
    exact gatTiesCB_pos D h0 (rOfB D sc) eOf (baseB D) u w hg (baseB_sep D u hg) m s
  r_eq := fun u w hg => by
    rw [hsc]
    rfl




end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section RecF

variable (D1 : D7) (W : TwGap D1) (large₂ : LevGapD D1) (h0 : ∀ u, Module.finrank ℂ (D1.mem u).A.Mu0 = 0)
  (sc : Scale) (eOf : ℕ → ℕ)

def recF : D7 := recX D1 W large₂ h0 (rOfB (large₂.withTw W).recS sc) eOf (baseB (large₂.withTw W).recS)

def recF_gatT : GatTies (recF D1 W large₂ h0 sc eOf) :=
  recX_gatT D1 W large₂ h0 (rOfB (large₂.withTw W).recS sc) eOf (baseB (large₂.withTw W).recS)

def recF_more
    (hmt : ∀ w, (((D1.what₂.places.resChar w : ℕ) : ℝ) ≤ sc.X'' D1.R.n ∨
      D1.what₂.places.resChar w ∈ ({D1.host.d, D1.host.g 0, D1.host.g 1} : Finset ℕ)) ↔ D1.what₂.muAt w ≠ D1.what₂.mu0)
    (hA : ∀ j w, D1.what₂.Aj j w = 0) :
    RecMore (recF D1 W large₂ h0 sc eOf) (recF_gatT D1 W large₂ h0 sc eOf) sc where
  mu_tw := fun w hw L hL j _ _ =>
    fval_zero_of_tw (D := recF D1 W large₂ h0 sc eOf) (fun w => (hmt w).1) w hw L hL j
  Aj0 := fun w _ j _ _ => hA j w
  S0 := ∅
  mu_0 := fun w hw => ((hmt w).2 hw).elim Or.inl (fun h => Or.inr (Or.inl h))
  pos := fun _ X hbs hsc => posHypB (large₂.withTw W).recS h0 sc eOf X hbs hsc

def recF_ex (hS : ServedGap) (hGa : GaugeGap) (S : Shape0 D1)
    (hV : ∀ i j b k Q ψ, Subsingleton (W.nexp.MtV i j b k Q ψ)) (hF : ∀ i j b, Subsingleton (W.nexp.Fm i j b))
    (t : Ties (withTw D1 W)) (hb : Function.Bijective D1.embE) (hk : DV.KapDef D1)
    (hdu : ∀ u, ((D1.mem u).A.duStar : ℝ) = StandardLattice.duStarU D1 u) (hDs : D1.what₂.Dstar = StandardLattice.DstarD D1) :
    RecExtra (recF D1 W large₂ h0 sc eOf) eOf where
  shape := recX_shape D1 W large₂ h0 _ eOf _ S hV hF
  ties := recX_ties D1 W large₂ h0 _ eOf _ t
  X := recX_X D1 W large₂ h0 _ eOf _ S
  mjH := recX_mjH D1 W large₂ h0 _ eOf _ S
  kapR := rfl
  ep_tie := fun _ _ _ => rfl
  kap_def := hk
  duStar_def := hdu
  Dstar_def := hDs
  cover := W.cover
  le := recX_le D1 W large₂ h0 _ eOf _
  served := recX_served D1 W large₂ h0 _ eOf _ hS hb
  gauge := hGa _ _ _

end RecF

open Classical in

def twOf {R : Ranks} (H : Host R) (sc : Scale) : (@placesOf H.E _ _ H.cmStar).Pl → Bool :=
  fun w => decide ((((@placesOf H.E _ _ H.cmStar).resChar w : ℕ) : ℝ) ≤ sc.X'' R.n ∨
    (@placesOf H.E _ _ H.cmStar).resChar w ∈ ({H.d, H.g 0, H.g 1} : Finset ℕ))



end Formalism.MainNotions.Inhab

end
end
