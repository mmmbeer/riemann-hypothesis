import ReciprocityTheory.GroupCohomology.ContinuousContractNth

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

def BasicStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (φ : Hom A B) (ψ : Hom B C) (n : ℕ),
  (Hom.id A).H n = LinearMap.id ∧ (ψ.comp φ).H n = (ψ.H n).comp (φ.H n) ∧
  (∀ h : A.H n, ∃ x hx, h = A.cls n x hx) ∧ (∀ x hx, A.cls n x hx = 0 ↔ x ∈ A.B n) ∧
  ∀ x hx, ∃ hy, φ.H n (A.cls n x hx) = B.cls n (φ.f n x) hy

def LESStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (i : Hom A B) (p : Hom B C), SES i p →
  (∃ δ, IsConn i p δ ∧ LES i p δ) ∧ ∀ δ δ', IsConn i p δ → IsConn i p δ' → δ = δ'

def ConnNatStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C A' B' C' : Cx R) (i : Hom A B) (p : Hom B C)
  (i' : Hom A' B') (p' : Hom B' C') (α : Hom A A') (β : Hom B B') (γ : Hom C C') δ δ', SES i p → SES i' p' →
  (∀ n x, β.f n (i.f n x) = i'.f n (α.f n x)) → (∀ n x, γ.f n (p.f n x) = p'.f n (β.f n x)) →
  IsConn i p δ → IsConn i' p' δ' → ∀ n x, δ' n (γ.H n x) = α.H (n + 1) (δ n x)

def TowerStatement : Prop := ∀ (R : Type u) [CommRing R] (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m))
  (L : Cx R) (π : ∀ m, Hom L (A m)), IsTowerLim A τ L π → ∀ n,
  (∀ y : ∀ m, (A m).H n, (∀ m, (τ m).H n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).H n x = y m) ∧
  ((∀ k, n = k + 1 → ∀ m, IsArtinian R ((A m).H k)) → ∀ x : L.H n, (∀ m, (π m).H n x = 0) → x = 0)

def LowStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ n, ∃ e : M.H n ≃ₗ[R] Hn M.rho n, ∀ x hx, ∃ hz : x.1 ∈ Zn M.rho n,
    e (M.coch.cls n x hx) = Submodule.Quotient.mk ⟨x.1, hz⟩) ∧
  (∃ e : M.H 0 ≃ₗ[R] H0 M.rho, ∀ x hx, (e (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∃ e : M.H 1 ≃ₗ[R] H1 M.rho, ∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho,
    e (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∃ e : M.H 2 ≃ₗ[R] H2 M.rho, ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩

def AdmStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C : TRep R G) (i : Pair A B) (p : Pair B C),
  admitted i p → SES i.hom p.hom

def SectionStatement : Prop := ∀ (B C : Type u) [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C] (p : B →+ C), Continuous p → Surjective p →
  (DiscreteTopology C ∨ (CompactSpace B ∧ T2Space B ∧ TotallyDisconnectedSpace B ∧ T2Space C)) →
  ∃ s : C → B, Continuous s ∧ ∀ c, p (s c) = c

def GroupSectionStatement : Prop := ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G), IsClosed (U : Set G) →
  ∃ r : G → U, Continuous r ∧ r 1 = 1 ∧ ∀ (x : U) g, r (x * g) = x * r g

def InnerStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (P : Pair M M) (s : G),
  (∀ g, P.φ g = s⁻¹ * g * s) → (∀ m, P.u m = M.rho s m) → ∀ n, P.hom.H n = LinearMap.id

def InvRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal],
  ∃ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P

def InfResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal]
  (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
  Injective (P.hom.H 1) ∧ Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) ∧
  ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) → (∀ m, c.u m = M.rho s m) →
    ∀ n x, c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x

def FiveTermStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2, (∀ x : I, tg x = 0 ↔
      x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧ Exact tg (P.hom.H 2)

def CorStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
  ∃ cor, IsCor M U cor ∧ ∀ n x,
    cor.H n ((Pair.res M U.subtype continuous_subtype_val).hom.H n x) = U.index • x

def ResInjStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
  IsUnit (U.index : R) → ∀ n, Injective ((Pair.res M U.subtype continuous_subtype_val).hom.H n)

def ResNormalStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal] [N.FiniteIndex],
  IsOpen (N : Set G) → IsUnit (N.index : R) → ∀ n (x : (M.resSub N).H n),
  (∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H n x = x) →
  x ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H n)

def CupStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (b : Pairing M N P),
  (∀ p q f f' (g : Fin (p + q + 1) → G), dn P.rho (p + q) (cupFun b p q f f') g =
    cupFun b (p + 1) q (dn M.rho p f) f' (fun i => g (i.cast (by omega))) +
      (-1 : R) ^ p • cupFun b p (q + 1) f (dn N.rho q f') g) ∧
  (∃ cup, IsCup b cup) ∧ ∀ cup cup', IsCup b cup → IsCup b cup' → cup = cup'

def CupConnRightStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N₁ N₂ N₃ P₁ P₂ P₃ : TRep R G) (i : Pair N₁ N₂) (p : Pair N₂ N₃)
  (i' : Pair P₁ P₂) (p' : Pair P₂ P₃) (b₁ : Pairing M N₁ P₁) (b₂ : Pairing M N₂ P₂) (b₃ : Pairing M N₃ P₃)
  δ δ' c₁ c₃, admitted i p → admitted i' p' → (∀ m n, i'.u (b₁.β m n) = b₂.β m (i.u n)) →
  (∀ m n, p'.u (b₂.β m n) = b₃.β m (p.u n)) → IsConn i.hom p.hom δ → IsConn i'.hom p'.hom δ' →
  IsCup b₁ c₁ → IsCup b₃ c₃ → ∀ r q x y, δ' (r + q) (c₃ r q x y) = (-1 : R) ^ r • c₁ r (q + 1) x (δ q y)

def CupCorStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (U : Subgroup G) [U.FiniteIndex] (b : Pairing M N P)
  (bU : Pairing (M.resSub U) (N.resSub U) (P.resSub U)) cup cupU corM corP, IsOpen (U : Set G) →
  bU.β = b.β → IsCup b cup → IsCup bU cupU → IsCor M U corM → IsCor P U corP → ∀ p q x y,
    corP.H (p + q) (cupU p q x ((Pair.res N U.subtype continuous_subtype_val).hom.H q y)) =
      cup p q (corM.H p x) y

def CoindStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : Subgroup G) (M : TRep R U),
  ∃ (C : TRep R G) (ev : Pair C M), IsCoind U M C ev

def ShapiroStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : Subgroup G) (M : TRep R U) (C : TRep R G)
  (ev : Pair C M), IsCoind U M C ev → (∃ r : G → U, Continuous r ∧ ∀ (x : U) g, r (x * g) = x * r g) →
  ev.hom.QuasiIso

def LimRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : ℕ → TRep R G) [∀ m, DiscreteTopology (A m).V]
  (τ : ∀ m, Pair (A (m + 1)) (A m)) (L : TRep R G) (π : ∀ m, Pair L (A m)),
  (∀ m, (τ m).φ = MonoidHom.id G ∧ (π m).φ = MonoidHom.id G ∧ Surjective (τ m).u ∧
    ∀ x, (τ m).u ((π (m + 1)).u x) = (π m).u x) →
  Topology.IsEmbedding (fun (x : L.V) m => (π m).u x) →
  (∀ y : ∀ m, (A m).V, (∀ m, (τ m).u (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).u x = y m) →
  IsTowerLim (fun m => (A m).coch) (fun m => (τ m).hom) L.coch fun m => (π m).hom

def ColimStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (ι : Type u) [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  (A : ι → TRep R G) (L : TRep R G) [DiscreteTopology L.V] [∀ a, DiscreteTopology (A a).V]
  (j : ∀ a, Pair (A a) L) (t : ∀ a b, a ≤ b → Pair (A a) (A b)),
  (∀ a, (j a).φ = MonoidHom.id G ∧ Injective (j a).u) →
  (∀ a b h, (t a b h).φ = MonoidHom.id G ∧ ∀ x, (j b).u ((t a b h).u x) = (j a).u x) →
  (∀ x, ∃ a, x ∈ LinearMap.range (j a).u) → ∀ n,
  (∀ x : L.H n, ∃ a y, (j a).hom.H n y = x) ∧
  ∀ a (y : (A a).H n), (j a).hom.H n y = 0 → ∃ b h, (t a b h).hom.H n y = 0

def FiniteLevelStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (n : ℕ) (x : M.H n),
  (∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n)) ∧ (0 < n → ∃ k : ℕ, 0 < k ∧ k • x = 0)

def ModTStatement : Prop := ∀ (R : Type u) [CommRing R] (A C : Cx R) (i : Hom A A) (p : Hom A C) (t : R) δ,
  (∀ n x, i.f n x = t • x) → SES i p → IsConn i p δ → ∀ n,
  (∀ x, p.H n x = 0 ↔ ∃ y, x = t • y) ∧ Exact (p.H n) (δ n) ∧ ∀ x, x ∈ LinearMap.range (δ n) ↔ t • x = 0

def FinGenStatement : Prop := ∀ (R : Type u) [CommRing R] (t : R) [IsAdicComplete (Ideal.span {t}) R]
  (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)),
  IsTowerLim A τ L π → (∀ n (x : L.X n), t • x = 0 → x = 0) →
  (∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y) →
  (∀ n, IsFiniteLength R ((A 0).H n)) → ∀ n, Module.Finite R (L.H n) ∧ ∀ m, IsFiniteLength R ((A m).H n)

end ReciprocityTheory.Coh
