import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.GraphTransport

/-! The duplicate-free left-biased carrier and its spliced node permutation. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- Darts of a graph union, represented with all darts of the first summand
and only the darts outside the common graph from the second summand.  Common
cycle darts therefore occur exactly once. -/
abbrev LeftBiasedDart
    {V : Type u}
    (G₁ G₂ C : SimpleGraph V) :=
  Sum (OrientedEdge G₁)
    {e : OrientedEdge G₂ // ¬ C.Adj e.tail e.head}

/-- Encode a dart of the second summand in the left-biased carrier, using the
first summand's copy exactly when the dart belongs to the common graph. -/
noncomputable def rightDartCode
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) (e : OrientedEdge G₂) :
    LeftBiasedDart G₁ G₂ C := by
  classical
  exact if heC : C.Adj e.tail e.head then
    Sum.inl (transferCommonDart hC₁ e heC)
  else
    Sum.inr ⟨e, heC⟩

@[simp]
theorem rightDartCode_of_common
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) (e : OrientedEdge G₂)
    (heC : C.Adj e.tail e.head) :
    rightDartCode hC₁ e =
      Sum.inl (transferCommonDart hC₁ e heC) := by
  classical
  simp [rightDartCode, heC]

@[simp]
theorem rightDartCode_of_not_common
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) (e : OrientedEdge G₂)
    (heC : ¬ C.Adj e.tail e.head) :
    rightDartCode hC₁ e = Sum.inr ⟨e, heC⟩ := by
  classical
  simp [rightDartCode, heC]

theorem rightDartCode_injective
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) :
    Function.Injective (rightDartCode hC₁ :
      OrientedEdge G₂ → LeftBiasedDart G₁ G₂ C) := by
  classical
  intro e f hef
  by_cases heC : C.Adj e.tail e.head
  · by_cases hfC : C.Adj f.tail f.head
    · rw [rightDartCode_of_common hC₁ e heC,
        rightDartCode_of_common hC₁ f hfC] at hef
      exact transferCommonDart_injective hC₁ heC hfC
        (Sum.inl.inj hef)
    · simp [rightDartCode, heC, hfC] at hef
  · by_cases hfC : C.Adj f.tail f.head
    · simp [rightDartCode, heC, hfC] at hef
    · rw [rightDartCode_of_not_common hC₁ e heC,
        rightDartCode_of_not_common hC₁ f hfC] at hef
      exact congrArg Subtype.val (Sum.inr.inj hef)

@[simp]
theorem rightDartCode_transferCommonDart
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (e : OrientedEdge G₁)
    (heC : C.Adj e.tail e.head) :
    rightDartCode hC₁ (transferCommonDart hC₂ e heC) =
      Sum.inl e := by
  rw [rightDartCode_of_common hC₁ _ (by simpa using heC)]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

@[simp]
theorem rightDartCode_liftOrientedEdge
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (e : OrientedEdge C) :
    rightDartCode hC₁ (liftOrientedEdge hC₂ e) =
      Sum.inl (liftOrientedEdge hC₁ e) := by
  rw [rightDartCode_of_common hC₁ _ (by simp)]
  apply congrArg Sum.inl
  apply Subtype.ext
  rfl

def leftBiasedTail
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (e : LeftBiasedDart G₁ G₂ C) : V :=
  e.elim OrientedEdge.tail (fun z => z.1.tail)

@[simp]
theorem rightDartCode_tail
    {V : Type u} {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁) (e : OrientedEdge G₂) :
    leftBiasedTail (rightDartCode hC₁ e) = e.tail := by
  classical
  by_cases heC : C.Adj e.tail e.head
  · rw [rightDartCode_of_common hC₁ e heC]
    rfl
  · rw [rightDartCode_of_not_common hC₁ e heC]
    rfl

/-- Node successor for gluing two rotations along an oppositely oriented
common facial cycle.  The first rotation is retained except at its forward
cycle darts; there the successor follows the second rotation until it returns
through the backward cycle dart. -/
noncomputable def cycleSplicedNodeFun
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) :
    LeftBiasedDart G₁ G₂ C → LeftBiasedDart G₁ G₂ C := by
  classical
  intro e
  cases e with
  | inl e =>
      exact if he : CycleForwardDart (c.mapLe hC₁) e then
        rightDartCode hC₁
          (R₂.node
            (transferCommonDart hC₂ e
              (common_adj_of_cycleForwardDart hC₁ he)))
      else
        Sum.inl (R₁.node e)
  | inr e =>
      exact rightDartCode hC₁ (R₂.node e.1)

/-- Candidate inverse of `cycleSplicedNodeFun`.  It switches to the second
inverse rotation precisely at backward cycle darts. -/
noncomputable def cycleSplicedNodeInvFun
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) :
    LeftBiasedDart G₁ G₂ C → LeftBiasedDart G₁ G₂ C := by
  classical
  intro e
  cases e with
  | inl e =>
      exact if he : CycleBackwardDart (c.mapLe hC₁) e then
        rightDartCode hC₁
          (R₂.node.symm
            (transferCommonDart hC₂ e
              (common_adj_of_cycleBackwardDart hC₁ he)))
      else
        Sum.inl (R₁.node.symm e)
  | inr e =>
      exact rightDartCode hC₁ (R₂.node.symm e.1)

@[simp]
theorem cycleSplicedNodeFun_inl_forward
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (e : OrientedEdge G₁)
    (he : CycleForwardDart (c.mapLe hC₁) e) :
    cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) =
      rightDartCode hC₁
        (R₂.node
          (transferCommonDart hC₂ e
            (common_adj_of_cycleForwardDart hC₁ he))) := by
  classical
  simp [cycleSplicedNodeFun, he]

@[simp]
theorem cycleSplicedNodeFun_inl_not_forward
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (e : OrientedEdge G₁)
    (he : ¬ CycleForwardDart (c.mapLe hC₁) e) :
    cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) =
      Sum.inl (R₁.node e) := by
  classical
  simp [cycleSplicedNodeFun, he]

@[simp]
theorem cycleSplicedNodeFun_inr
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u)
    (e : {e : OrientedEdge G₂ // ¬ C.Adj e.tail e.head}) :
    cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inr e) =
      rightDartCode hC₁ (R₂.node e.1) := by
  rfl

@[simp]
theorem cycleSplicedNodeInvFun_inl_backward
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (e : OrientedEdge G₁)
    (he : CycleBackwardDart (c.mapLe hC₁) e) :
    cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) =
      rightDartCode hC₁
        (R₂.node.symm
          (transferCommonDart hC₂ e
            (common_adj_of_cycleBackwardDart hC₁ he))) := by
  classical
  simp [cycleSplicedNodeInvFun, he]

@[simp]
theorem cycleSplicedNodeInvFun_inl_not_backward
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (e : OrientedEdge G₁)
    (he : ¬ CycleBackwardDart (c.mapLe hC₁) e) :
    cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) =
      Sum.inl (R₁.node.symm e) := by
  classical
  simp [cycleSplicedNodeInvFun, he]

@[simp]
theorem cycleSplicedNodeInvFun_inr
    {V : Type u} {G₁ G₂ C : SimpleGraph V} {u : V}
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u)
    (e : {e : OrientedEdge G₂ // ¬ C.Adj e.tail e.head}) :
    cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c (Sum.inr e) =
      rightDartCode hC₁ (R₂.node.symm e.1) := by
  rfl

/-- The proposed inverse cancels the common-cycle splice on the left. -/
theorem cycleSplicedNode_leftInverse
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
    Function.LeftInverse
      (cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c)
      (cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c) := by
  classical
  intro z
  cases z with
  | inl e =>
      by_cases heForward : CycleForwardDart (c.mapLe hC₁) e
      · rw [cycleSplicedNodeFun_inl_forward
          R₁ R₂ hC₁ hC₂ c e heForward]
        let e₂ : OrientedEdge G₂ :=
          transferCommonDart hC₂ e
            (common_adj_of_cycleForwardDart hC₁ heForward)
        have he₂Forward :
            CycleForwardDart (c.mapLe hC₂) e₂ := by
          exact cycleForwardDart_transferCommonDart
            hC₁ hC₂ heForward
        let r : OrientedEdge G₂ := R₂.node e₂
        by_cases hrC : C.Adj r.tail r.head
        · rw [rightDartCode_of_common hC₁ r hrC]
          have hrOrient :=
            cycleForward_or_backward_of_common hC₂ hspan r hrC
          have hrBackward :
              CycleBackwardDart (c.mapLe hC₂) r := by
            rcases hrOrient with hrForward | hrBackward
            · have he₂BackwardReverse :
                  CycleBackwardDart (c.mapLe hC₂).reverse e₂ :=
                (cycleBackwardDart_reverse_iff_forward
                  (c.mapLe hC₂) e₂).mpr he₂Forward
              have hpredForwardReverse :=
                hfac₂.node_symm_backward_forward
                  ((cycleBackwardDart_reverse_iff_forward
                    (c.mapLe hC₂) r).mpr hrForward)
              have hpred : R₂.node.symm r = e₂ := by
                dsimp [r]
                simp
              rw [hpred] at hpredForwardReverse
              exact False.elim
                (cycleBackwardDart_not_forward
                  (hc.mapLe hC₂).reverse
                  he₂BackwardReverse hpredForwardReverse)
            · exact hrBackward
          have hrBackward₁ :
              CycleBackwardDart (c.mapLe hC₁)
                (transferCommonDart hC₁ r hrC) :=
            cycleBackwardDart_transferCommonDart
              hC₂ hC₁ hrBackward
          rw [cycleSplicedNodeInvFun_inl_backward
            R₁ R₂ hC₁ hC₂ c
            (transferCommonDart hC₁ r hrC) hrBackward₁]
          have htransferBack :
              transferCommonDart hC₂
                  (transferCommonDart hC₁ r hrC)
                  (common_adj_of_cycleBackwardDart hC₁ hrBackward₁) =
                r := by
            apply Subtype.ext
            rfl
          rw [htransferBack]
          change rightDartCode hC₁ (R₂.node.symm (R₂.node e₂)) =
            Sum.inl e
          rw [R₂.node.symm_apply_apply]
          exact rightDartCode_transferCommonDart hC₁ hC₂ e
            (common_adj_of_cycleForwardDart hC₁ heForward)
        · rw [rightDartCode_of_not_common hC₁ r hrC,
            cycleSplicedNodeInvFun_inr]
          change rightDartCode hC₁ (R₂.node.symm (R₂.node e₂)) =
            Sum.inl e
          rw [R₂.node.symm_apply_apply]
          exact rightDartCode_transferCommonDart hC₁ hC₂ e
            (common_adj_of_cycleForwardDart hC₁ heForward)
      · rw [cycleSplicedNodeFun_inl_not_forward
          R₁ R₂ hC₁ hC₂ c e heForward]
        have hnodeNotBackward :
            ¬ CycleBackwardDart (c.mapLe hC₁) (R₁.node e) := by
          intro hbackward
          have hpredForward :=
            hfac₁.node_symm_backward_forward hbackward
          have hpred : R₁.node.symm (R₁.node e) = e := by simp
          rw [hpred] at hpredForward
          exact heForward hpredForward
        rw [cycleSplicedNodeInvFun_inl_not_backward
          R₁ R₂ hC₁ hC₂ c (R₁.node e) hnodeNotBackward]
        simp
  | inr e =>
      rw [cycleSplicedNodeFun_inr]
      let r : OrientedEdge G₂ := R₂.node e.1
      by_cases hrC : C.Adj r.tail r.head
      · rw [rightDartCode_of_common hC₁ r hrC]
        have hrOrient :=
          cycleForward_or_backward_of_common hC₂ hspan r hrC
        have hrBackward :
            CycleBackwardDart (c.mapLe hC₂) r := by
          rcases hrOrient with hrForward | hrBackward
          · have hpredBackward :=
              hfac₂.node_symm_forward_backward_of_reverse
                (hc := hc.mapLe hC₂) hrForward
            have hpred : R₂.node.symm r = e.1 := by
              dsimp [r]
              simp
            rw [hpred] at hpredBackward
            exact False.elim
              (e.2 (common_adj_of_cycleBackwardDart hC₂ hpredBackward))
          · exact hrBackward
        have hrBackward₁ :
            CycleBackwardDart (c.mapLe hC₁)
              (transferCommonDart hC₁ r hrC) :=
          cycleBackwardDart_transferCommonDart
            hC₂ hC₁ hrBackward
        rw [cycleSplicedNodeInvFun_inl_backward
          R₁ R₂ hC₁ hC₂ c
          (transferCommonDart hC₁ r hrC) hrBackward₁]
        have htransferBack :
            transferCommonDart hC₂
                (transferCommonDart hC₁ r hrC)
                (common_adj_of_cycleBackwardDart hC₁ hrBackward₁) =
              r := by
          apply Subtype.ext
          rfl
        rw [htransferBack]
        change rightDartCode hC₁ (R₂.node.symm (R₂.node e.1)) =
          Sum.inr e
        rw [R₂.node.symm_apply_apply]
        exact rightDartCode_of_not_common hC₁ e.1 e.2
      · rw [rightDartCode_of_not_common hC₁ r hrC,
          cycleSplicedNodeInvFun_inr]
        change rightDartCode hC₁ (R₂.node.symm (R₂.node e.1)) =
          Sum.inr e
        rw [R₂.node.symm_apply_apply]
        exact rightDartCode_of_not_common hC₁ e.1 e.2

/-- The common-cycle splice also cancels its proposed inverse on the right. -/
theorem cycleSplicedNode_rightInverse
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
    Function.RightInverse
      (cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c)
      (cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c) := by
  classical
  intro z
  cases z with
  | inl e =>
      by_cases heBackward : CycleBackwardDart (c.mapLe hC₁) e
      · rw [cycleSplicedNodeInvFun_inl_backward
          R₁ R₂ hC₁ hC₂ c e heBackward]
        let e₂ : OrientedEdge G₂ :=
          transferCommonDart hC₂ e
            (common_adj_of_cycleBackwardDart hC₁ heBackward)
        have he₂Backward :
            CycleBackwardDart (c.mapLe hC₂) e₂ :=
          cycleBackwardDart_transferCommonDart
            hC₁ hC₂ heBackward
        let r : OrientedEdge G₂ := R₂.node.symm e₂
        by_cases hrC : C.Adj r.tail r.head
        · rw [rightDartCode_of_common hC₁ r hrC]
          have hrOrient :=
            cycleForward_or_backward_of_common hC₂ hspan r hrC
          have hrForward :
              CycleForwardDart (c.mapLe hC₂) r := by
            rcases hrOrient with hrForward | hrBackward
            · exact hrForward
            · have hnextForward :=
                hfac₂.node_backward_forward_of_reverse
                  (hc := hc.mapLe hC₂) hrBackward
              have hnext : R₂.node r = e₂ := by
                dsimp [r]
                simp
              rw [hnext] at hnextForward
              exact False.elim
                (cycleBackwardDart_not_forward
                  (hc.mapLe hC₂) he₂Backward hnextForward)
          have hrForward₁ :
              CycleForwardDart (c.mapLe hC₁)
                (transferCommonDart hC₁ r hrC) :=
            cycleForwardDart_transferCommonDart
              hC₂ hC₁ hrForward
          rw [cycleSplicedNodeFun_inl_forward
            R₁ R₂ hC₁ hC₂ c
            (transferCommonDart hC₁ r hrC) hrForward₁]
          have htransferBack :
              transferCommonDart hC₂
                  (transferCommonDart hC₁ r hrC)
                  (common_adj_of_cycleForwardDart hC₁ hrForward₁) =
                r := by
            apply Subtype.ext
            rfl
          rw [htransferBack]
          change rightDartCode hC₁ (R₂.node (R₂.node.symm e₂)) =
            Sum.inl e
          rw [R₂.node.apply_symm_apply]
          exact rightDartCode_transferCommonDart hC₁ hC₂ e
            (common_adj_of_cycleBackwardDart hC₁ heBackward)
        · rw [rightDartCode_of_not_common hC₁ r hrC,
            cycleSplicedNodeFun_inr]
          change rightDartCode hC₁ (R₂.node (R₂.node.symm e₂)) =
            Sum.inl e
          rw [R₂.node.apply_symm_apply]
          exact rightDartCode_transferCommonDart hC₁ hC₂ e
            (common_adj_of_cycleBackwardDart hC₁ heBackward)
      · rw [cycleSplicedNodeInvFun_inl_not_backward
          R₁ R₂ hC₁ hC₂ c e heBackward]
        have hpredNotForward :
            ¬ CycleForwardDart (c.mapLe hC₁)
              (R₁.node.symm e) := by
          intro hforward
          have hnextBackward :=
            hfac₁.node_forward_backward hforward
          have hnext : R₁.node (R₁.node.symm e) = e := by simp
          rw [hnext] at hnextBackward
          exact heBackward hnextBackward
        rw [cycleSplicedNodeFun_inl_not_forward
          R₁ R₂ hC₁ hC₂ c (R₁.node.symm e)
          hpredNotForward]
        simp
  | inr e =>
      rw [cycleSplicedNodeInvFun_inr]
      let r : OrientedEdge G₂ := R₂.node.symm e.1
      by_cases hrC : C.Adj r.tail r.head
      · rw [rightDartCode_of_common hC₁ r hrC]
        have hrOrient :=
          cycleForward_or_backward_of_common hC₂ hspan r hrC
        have hrForward :
            CycleForwardDart (c.mapLe hC₂) r := by
          rcases hrOrient with hrForward | hrBackward
          · exact hrForward
          · have hnextForward :=
              hfac₂.node_backward_forward_of_reverse
                (hc := hc.mapLe hC₂) hrBackward
            have hnext : R₂.node r = e.1 := by
              dsimp [r]
              simp
            rw [hnext] at hnextForward
            exact False.elim
              (e.2 (common_adj_of_cycleForwardDart hC₂ hnextForward))
        have hrForward₁ :
            CycleForwardDart (c.mapLe hC₁)
              (transferCommonDart hC₁ r hrC) :=
          cycleForwardDart_transferCommonDart
            hC₂ hC₁ hrForward
        rw [cycleSplicedNodeFun_inl_forward
          R₁ R₂ hC₁ hC₂ c
          (transferCommonDart hC₁ r hrC) hrForward₁]
        have htransferBack :
            transferCommonDart hC₂
                (transferCommonDart hC₁ r hrC)
                (common_adj_of_cycleForwardDart hC₁ hrForward₁) =
              r := by
          apply Subtype.ext
          rfl
        rw [htransferBack]
        change rightDartCode hC₁ (R₂.node (R₂.node.symm e.1)) =
          Sum.inr e
        rw [R₂.node.apply_symm_apply]
        exact rightDartCode_of_not_common hC₁ e.1 e.2
      · rw [rightDartCode_of_not_common hC₁ r hrC,
          cycleSplicedNodeFun_inr]
        change rightDartCode hC₁ (R₂.node (R₂.node.symm e.1)) =
          Sum.inr e
        rw [R₂.node.apply_symm_apply]
        exact rightDartCode_of_not_common hC₁ e.1 e.2

/-- The node successor obtained by gluing along opposite facial cycles is a
permutation of the duplicate-free union dart carrier. -/
noncomputable def cycleSplicedNode
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
    Equiv.Perm (LeftBiasedDart G₁ G₂ C) where
  toFun := cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c
  invFun := cycleSplicedNodeInvFun R₁ R₂ hC₁ hC₂ c
  left_inv :=
    cycleSplicedNode_leftInverse R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂
  right_inv :=
    cycleSplicedNode_rightInverse R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂

theorem cycleSplicedNode_tail
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
    leftBiasedTail
        (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂ e) =
      leftBiasedTail e := by
  classical
  cases e with
  | inl e =>
      by_cases he : CycleForwardDart (c.mapLe hC₁) e
      · rw [show
          cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
              (Sum.inl e) =
            cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) from
          rfl,
          cycleSplicedNodeFun_inl_forward
            R₁ R₂ hC₁ hC₂ c e he,
          rightDartCode_tail, R₂.node_tail]
        rfl
      · rw [show
          cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
              (Sum.inl e) =
            cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) from
          rfl,
          cycleSplicedNodeFun_inl_not_forward
            R₁ R₂ hC₁ hC₂ c e he]
        exact R₁.node_tail e
  | inr e =>
      rw [show
        cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
            (Sum.inr e) =
          cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inr e) from
        rfl,
        cycleSplicedNodeFun_inr, rightDartCode_tail,
        R₂.node_tail]
      rfl


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
