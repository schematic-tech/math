import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.CarrierEquivalence

/-! Construction and elementary permutation equations of the cycle-sum hypermap. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- Glue two rotation systems along a common cycle that is facial in opposite
orientations. -/
noncomputable def cycleSum
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (hmeet :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support →
        v ∈ c.support) :
    RotationSystem (G₁ ⊔ G₂) := by
  let E := leftBiasedSupEquiv hC₁ hcommon
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  exact
    { node := transportPerm E N
      node_tail := by
        intro e
        let x := E.symm e
        have hEx : E x = e := E.apply_symm_apply e
        calc
          (transportPerm E N e).tail =
              (E (N x)).tail := by rw [← hEx, transportPerm_apply]
          _ = leftBiasedTail (N x) := by
            exact leftBiasedSupEquiv_tail hC₁ hcommon (N x)
          _ = leftBiasedTail x :=
            cycleSplicedNode_tail
              R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ x
          _ = (E x).tail := by
            exact (leftBiasedSupEquiv_tail hC₁ hcommon x).symm
          _ = e.tail := by rw [hEx]
      node_orbit_of_same_tail := by
        intro e f hef
        let x := E.symm e
        let y := E.symm f
        have hEx : E x = e := E.apply_symm_apply e
        have hEy : E y = f := E.apply_symm_apply f
        have hxyTail : leftBiasedTail x = leftBiasedTail y := by
          calc
            leftBiasedTail x = (E x).tail :=
              (leftBiasedSupEquiv_tail hC₁ hcommon x).symm
            _ = e.tail := by rw [hEx]
            _ = f.tail := hef
            _ = (E y).tail := by rw [hEy]
            _ = leftBiasedTail y :=
              leftBiasedSupEquiv_tail hC₁ hcommon y
        have hxy :=
          cycleSplicedNode_reachable_of_same_tail
            R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hmeet
            x y hxyTail
        have hmapped := transportPerm_reachable E N hxy
        simpa [hEx, hEy] using hmapped }

/-- Edge reversal on the duplicate-free common-cycle carrier. -/
def leftBiasedEdgePerm
    {V : Type u} {G₁ G₂ C : SimpleGraph V} :
    Equiv.Perm (LeftBiasedDart G₁ G₂ C) where
  toFun := leftBiasedSymm
  invFun := leftBiasedSymm
  left_inv := leftBiasedSymm_symm
  right_inv := leftBiasedSymm_symm

/-- Hypermap on the duplicate-free carrier underlying `cycleSum`. -/
noncomputable def cycleSplicedHypermap
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse) :
    Hypermap.{u} := by
  classical
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  exact
    { Dart := LeftBiasedDart G₁ G₂ C
      edge := leftBiasedEdgePerm
      node := N
      face := leftBiasedEdgePerm.trans N.symm
      node_face_edge := by
        intro e
        simp [leftBiasedEdgePerm, N] }

@[simp]
theorem cycleSplicedHypermap_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : LeftBiasedDart G₁ G₂ C) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).edge e = leftBiasedSymm e :=
  rfl

@[simp]
theorem cycleSplicedHypermap_node
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : LeftBiasedDart G₁ G₂ C) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).node e =
        cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂ e :=
  rfl

@[simp]
theorem cycleSplicedHypermap_face
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : LeftBiasedDart G₁ G₂ C) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).face e =
        cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c
          (leftBiasedSymm e) :=
  rfl

theorem cycleSplicedHypermap_face_inl_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : OrientedEdge G₁)
    (he : CycleForwardDart (c.mapLe hC₁) e) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).face (Sum.inl e) =
        rightDartCode hC₁
          ((R₂.toHypermap).face
            (transferCommonDart hC₂ e
              (common_adj_of_cycleForwardDart hC₁ he))) := by
  classical
  rw [cycleSplicedHypermap_face]
  have hbackward :
      CycleBackwardDart (c.mapLe hC₁) e.symm := by
    simpa [CycleBackwardDart] using he
  change
    cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c (Sum.inl e.symm) =
      rightDartCode hC₁
        ((R₂.toHypermap).face
          (transferCommonDart hC₂ e
            (common_adj_of_cycleForwardDart hC₁ he)))
  rw [cycleSplicedNodeInvFun_inl_backward
    R₁ R₂ hC₁ hC₂ c e.symm hbackward]
  change
    rightDartCode hC₁
        (R₂.node.symm
          (transferCommonDart hC₂ e.symm
            (common_adj_of_cycleBackwardDart hC₁ hbackward))) =
      rightDartCode hC₁
        (R₂.node.symm
          (transferCommonDart hC₂ e
            (common_adj_of_cycleForwardDart hC₁ he)).symm)
  apply congrArg (rightDartCode hC₁)
  apply congrArg R₂.node.symm
  apply Subtype.ext
  rfl

theorem cycleSplicedHypermap_face_inl_not_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : OrientedEdge G₁)
    (he : ¬ CycleForwardDart (c.mapLe hC₁) e) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).face (Sum.inl e) =
        Sum.inl ((R₁.toHypermap).face e) := by
  classical
  rw [cycleSplicedHypermap_face]
  have hnotBackward :
      ¬ CycleBackwardDart (c.mapLe hC₁) e.symm := by
    simpa [CycleBackwardDart] using he
  change
    cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c (Sum.inl e.symm) =
      Sum.inl ((R₁.toHypermap).face e)
  rw [cycleSplicedNodeInvFun_inl_not_backward
    R₁ R₂ hC₁ hC₂ c e.symm hnotBackward]
  rfl

theorem cycleSplicedHypermap_face_inr
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : {e : OrientedEdge G₂ // ¬ C.Adj e.tail e.head}) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).face (Sum.inr e) =
        rightDartCode hC₁ ((R₂.toHypermap).face e.1) := by
  rw [cycleSplicedHypermap_face]
  simp only [leftBiasedSymm]
  rw [
    cycleSplicedNodeInvFun_inr]
  rfl


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
