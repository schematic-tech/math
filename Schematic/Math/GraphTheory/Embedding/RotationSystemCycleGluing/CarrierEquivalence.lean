import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.NodeReachability

/-! Equivalence between the left-biased carrier and the union graph darts. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- The canonical map from the left-biased dart decomposition to the darts of
the graph union. -/
def leftBiasedSupMap
    {V : Type u} {G₁ G₂ C : SimpleGraph V} :
    LeftBiasedDart G₁ G₂ C → OrientedEdge (G₁ ⊔ G₂)
  | Sum.inl e =>
      ⟨(e.tail, e.head),
        (SimpleGraph.sup_adj G₁ G₂ e.tail e.head).mpr (Or.inl e.adj)⟩
  | Sum.inr e =>
      ⟨(e.1.tail, e.1.head),
        (SimpleGraph.sup_adj G₁ G₂ e.1.tail e.1.head).mpr
          (Or.inr e.1.adj)⟩

theorem leftBiasedSupMap_bijective
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y) :
    Function.Bijective
      (leftBiasedSupMap :
        LeftBiasedDart G₁ G₂ C → OrientedEdge (G₁ ⊔ G₂)) := by
  constructor
  · intro e f hef
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            have hp : e.1 = f.1 :=
              congrArg
                (fun z : OrientedEdge (G₁ ⊔ G₂) => z.1) hef
            apply congrArg Sum.inl
            apply Subtype.ext
            exact hp
        | inr f =>
            rcases e with ⟨⟨x, y⟩, h₁⟩
            rcases f with ⟨⟨⟨x', y'⟩, h₂⟩, hnC⟩
            have hp : (x, y) = (x', y') :=
              congrArg Subtype.val hef
            cases hp
            exact False.elim (hnC (hcommon h₁ h₂))
    | inr e =>
        cases f with
        | inl f =>
            rcases e with ⟨⟨⟨x, y⟩, h₂⟩, hnC⟩
            rcases f with ⟨⟨x', y'⟩, h₁⟩
            have hp : (x, y) = (x', y') :=
              congrArg Subtype.val hef
            cases hp
            exact False.elim (hnC (hcommon h₁ h₂))
        | inr f =>
            have hp : e.1.1 = f.1.1 :=
              congrArg
                (fun z : OrientedEdge (G₁ ⊔ G₂) => z.1) hef
            apply congrArg Sum.inr
            apply Subtype.ext
            apply Subtype.ext
            exact hp
  · intro e
    rcases (SimpleGraph.sup_adj G₁ G₂ e.tail e.head).mp e.adj with h₁ | h₂
    · refine ⟨Sum.inl ⟨(e.tail, e.head), h₁⟩, ?_⟩
      apply Subtype.ext
      rfl
    · by_cases h₁ : G₁.Adj e.tail e.head
      · refine ⟨Sum.inl ⟨(e.tail, e.head), h₁⟩, ?_⟩
        apply Subtype.ext
        rfl
      · refine
          ⟨Sum.inr
              ⟨⟨(e.tail, e.head), h₂⟩, fun hC => h₁ (hC₁ hC)⟩,
            ?_⟩
        apply Subtype.ext
        rfl

/-- The left-biased dart decomposition is exactly the oriented-edge type of
the graph union when `C` contains every common edge. -/
noncomputable def leftBiasedSupEquiv
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y) :
    LeftBiasedDart G₁ G₂ C ≃ OrientedEdge (G₁ ⊔ G₂) :=
  Equiv.ofBijective leftBiasedSupMap
    (leftBiasedSupMap_bijective hC₁ hcommon)

@[simp]
theorem leftBiasedSupEquiv_inl
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (e : OrientedEdge G₁) :
    leftBiasedSupEquiv hC₁ hcommon (Sum.inl e) =
      ⟨(e.tail, e.head),
        (SimpleGraph.sup_adj G₁ G₂ e.tail e.head).mpr (Or.inl e.adj)⟩ :=
  rfl

@[simp]
theorem leftBiasedSupEquiv_inr
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (e : {e : OrientedEdge G₂ // ¬ C.Adj e.tail e.head}) :
    leftBiasedSupEquiv hC₁ hcommon (Sum.inr e) =
      ⟨(e.1.tail, e.1.head),
        (SimpleGraph.sup_adj G₁ G₂ e.1.tail e.1.head).mpr
          (Or.inr e.1.adj)⟩ :=
  rfl

@[simp]
theorem leftBiasedSupEquiv_tail
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (e : LeftBiasedDart G₁ G₂ C) :
    (leftBiasedSupEquiv hC₁ hcommon e).tail =
      e.elim OrientedEdge.tail (fun z => z.1.tail) := by
  cases e <;> rfl

@[simp]
theorem leftBiasedSupEquiv_head
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (e : LeftBiasedDart G₁ G₂ C) :
    (leftBiasedSupEquiv hC₁ hcommon e).head =
      e.elim OrientedEdge.head (fun z => z.1.head) := by
  cases e <;> rfl

/-- Reverse a dart in the left-biased decomposition. -/
def leftBiasedSymm
    {V : Type u} {G₁ G₂ C : SimpleGraph V} :
    LeftBiasedDart G₁ G₂ C → LeftBiasedDart G₁ G₂ C
  | Sum.inl e => Sum.inl e.symm
  | Sum.inr e =>
      Sum.inr
        ⟨e.1.symm, fun hC => e.2 (C.symm hC)⟩

@[simp]
theorem leftBiasedSymm_symm
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (e : LeftBiasedDart G₁ G₂ C) :
    leftBiasedSymm (leftBiasedSymm e) = e := by
  cases e with
  | inl e => simp [leftBiasedSymm]
  | inr e =>
      apply congrArg Sum.inr
      apply Subtype.ext
      simp

@[simp]
theorem leftBiasedSupEquiv_symm
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (e : LeftBiasedDart G₁ G₂ C) :
    leftBiasedSupEquiv hC₁ hcommon (leftBiasedSymm e) =
      (leftBiasedSupEquiv hC₁ hcommon e).symm := by
  cases e <;> rfl

/-- Conjugate a permutation through an equivalence of its carrier. -/
def transportPerm
    {α β : Type u}
    (E : α ≃ β) (σ : Equiv.Perm α) :
    Equiv.Perm β :=
  E.symm.trans (σ.trans E)

@[simp]
theorem transportPerm_apply
    {α β : Type u}
    (E : α ≃ β) (σ : Equiv.Perm α) (x : α) :
    transportPerm E σ (E x) = E (σ x) := by
  simp [transportPerm]

theorem transportPerm_reachable
    {α β : Type u}
    (E : α ≃ β) (σ : Equiv.Perm α)
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable (transportPerm E σ) (E x) (E y) := by
  exact permReachable_of_forward_simulation σ (transportPerm E σ) E
    (fun z => by
      simpa using
        PermReachable.forward (transportPerm E σ) (E z))
    hxy


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
