import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.LeftBiasedCarrier

/-! Node-orbit reachability in the cycle splice. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- The second rotation supplies the inserted arc from a forward boundary dart
to the matching backward boundary dart of the first rotation. -/
theorem cycleSplicedNode_forward_reachable_backward
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
    (heForward : CycleForwardDart (c.mapLe hC₁) e) :
    PermReachable
      (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
      (Sum.inl e) (Sum.inl (R₁.node e)) := by
  classical
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  let b₁ : OrientedEdge G₁ := R₁.node e
  have hb₁Backward :
      CycleBackwardDart (c.mapLe hC₁) b₁ := by
    exact hfac₁.node_forward_backward heForward
  let e₂ : OrientedEdge G₂ :=
    transferCommonDart hC₂ e
      (common_adj_of_cycleForwardDart hC₁ heForward)
  let b₂ : OrientedEdge G₂ :=
    transferCommonDart hC₂ b₁
      (common_adj_of_cycleBackwardDart hC₁ hb₁Backward)
  have he₂Forward :
      CycleForwardDart (c.mapLe hC₂) e₂ :=
    cycleForwardDart_transferCommonDart hC₁ hC₂ heForward
  have hb₂Backward :
      CycleBackwardDart (c.mapLe hC₂) b₂ :=
    cycleBackwardDart_transferCommonDart hC₁ hC₂ hb₁Backward
  have htails : b₂.tail = e₂.tail := by
    dsimp [b₂, e₂, b₁]
    exact R₁.node_tail e
  have horbit : PermReachable R₂.node e₂ b₂ :=
    R₂.node_orbit_of_same_tail e₂ b₂ htails.symm
  have hexists :
      ∃ n : Nat, (R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[n] e₂ =
        b₂ :=
    permReachable_exists_iterate R₂.node horbit
  let n := Nat.find hexists
  have hn :
      (R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[n] e₂ = b₂ :=
    Nat.find_spec hexists
  have hiterTail :
      ∀ k : Nat,
        ((R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[k] e₂).tail =
          e₂.tail := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (R₂.node_tail _).trans ih
  have hstep :
      ∀ x : OrientedEdge G₂,
        x.tail = e₂.tail →
        x ≠ b₂ →
        N (rightDartCode hC₁ x) =
          rightDartCode hC₁ (R₂.node x) := by
    intro x hxtail hxne
    by_cases hxC : C.Adj x.tail x.head
    · rcases cycleForward_or_backward_of_common hC₂ hspan x hxC with
        hxForward | hxBackward
      · have hxe₂ : x = e₂ :=
          cycleForwardDart_eq_of_tail_eq (hc.mapLe hC₂)
            hxForward he₂Forward hxtail
        subst x
        rw [rightDartCode_transferCommonDart hC₁ hC₂ e
          (common_adj_of_cycleForwardDart hC₁ heForward)]
        change
          cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) =
            rightDartCode hC₁ (R₂.node e₂)
        exact cycleSplicedNodeFun_inl_forward
          R₁ R₂ hC₁ hC₂ c e heForward
      · have hxb₂ : x = b₂ :=
          cycleBackwardDart_eq_of_tail_eq (hc.mapLe hC₂)
            hxBackward hb₂Backward (hxtail.trans htails.symm)
        exact False.elim (hxne hxb₂)
    · rw [rightDartCode_of_not_common hC₁ x hxC]
      change
        cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c
            (Sum.inr ⟨x, hxC⟩) =
          rightDartCode hC₁ (R₂.node x)
      rfl
  have hwalk :
      ∀ k : Nat, k ≤ n →
        PermReachable N
          (rightDartCode hC₁ e₂)
          (rightDartCode hC₁
            ((R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[k] e₂)) := by
    intro k hk
    induction k with
    | zero =>
        exact PermReachable.refl N (rightDartCode hC₁ e₂)
    | succ k ih =>
        have hklt : k < n := by omega
        have hxne :
            (R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[k] e₂ ≠
              b₂ := by
          intro heq
          exact Nat.find_min hexists hklt heq
        have hstepEq :=
          hstep
            ((R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[k] e₂)
            (hiterTail k) hxne
        exact PermReachable.trans N (ih (by omega)) (by
          rw [Function.iterate_succ_apply', ← hstepEq]
          exact PermReachable.forward N
            (rightDartCode hC₁
              ((R₂.node : OrientedEdge G₂ → OrientedEdge G₂)^[k] e₂)))
  have hresult := hwalk n le_rfl
  rw [hn] at hresult
  rw [rightDartCode_transferCommonDart hC₁ hC₂ e
      (common_adj_of_cycleForwardDart hC₁ heForward),
    rightDartCode_transferCommonDart hC₁ hC₂ b₁
      (common_adj_of_cycleBackwardDart hC₁ hb₁Backward)] at hresult
  exact hresult

/-- A pointwise simulation of old successor steps lifts every old orbit
reachability relation. -/
theorem permReachable_of_forward_simulation
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (code : α → β)
    (hstep : ∀ x : α, PermReachable τ (code x) (code (σ x)))
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable τ (code x) (code y) :=
  PermReachable.map_of_forward_simulation σ τ code hstep hxy

theorem cycleSplicedNode_left_forward_reachable
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
    (e : OrientedEdge G₁) :
    PermReachable
      (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
      (Sum.inl e) (Sum.inl (R₁.node e)) := by
  classical
  by_cases heForward : CycleForwardDart (c.mapLe hC₁) e
  · exact cycleSplicedNode_forward_reachable_backward
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e heForward
  · have heq :
        cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
            (Sum.inl e) =
          Sum.inl (R₁.node e) := by
      change
        cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e) =
          Sum.inl (R₁.node e)
      exact cycleSplicedNodeFun_inl_not_forward
        R₁ R₂ hC₁ hC₂ c e heForward
    simpa [heq] using
      PermReachable.forward
        (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
        (Sum.inl e)

theorem cycleSplicedNode_right_forward_reachable
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
    (e : OrientedEdge G₂) :
    PermReachable
      (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
      (rightDartCode hC₁ e)
      (rightDartCode hC₁ (R₂.node e)) := by
  classical
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  by_cases heC : C.Adj e.tail e.head
  · rcases cycleForward_or_backward_of_common hC₂ hspan e heC with
      heForward | heBackward
    · let e₁ : OrientedEdge G₁ :=
        transferCommonDart hC₁ e heC
      have heForward₁ :
          CycleForwardDart (c.mapLe hC₁) e₁ :=
        cycleForwardDart_transferCommonDart hC₂ hC₁ heForward
      have hcode : rightDartCode hC₁ e = Sum.inl e₁ :=
        rightDartCode_of_common hC₁ e heC
      have hstep :
          N (Sum.inl e₁) = rightDartCode hC₁ (R₂.node e) := by
        change
          cycleSplicedNodeFun R₁ R₂ hC₁ hC₂ c (Sum.inl e₁) =
            rightDartCode hC₁ (R₂.node e)
        rw [cycleSplicedNodeFun_inl_forward
          R₁ R₂ hC₁ hC₂ c e₁ heForward₁]
        congr 2
      rw [hcode]
      simpa [hstep] using PermReachable.forward N (Sum.inl e₁)
    · let b₁ : OrientedEdge G₁ :=
        transferCommonDart hC₁ e heC
      have hb₁Backward :
          CycleBackwardDart (c.mapLe hC₁) b₁ :=
        cycleBackwardDart_transferCommonDart hC₂ hC₁ heBackward
      have hnextForward :
          CycleForwardDart (c.mapLe hC₂) (R₂.node e) :=
        hfac₂.node_backward_forward_of_reverse
          (hc := hc.mapLe hC₂) heBackward
      have hnextC :
          C.Adj (R₂.node e).tail (R₂.node e).head :=
        common_adj_of_cycleForwardDart hC₂ hnextForward
      let a₁ : OrientedEdge G₁ :=
        transferCommonDart hC₁ (R₂.node e) hnextC
      have ha₁Forward :
          CycleForwardDart (c.mapLe hC₁) a₁ :=
        cycleForwardDart_transferCommonDart hC₂ hC₁ hnextForward
      have hnodeEq : R₁.node a₁ = b₁ := by
        apply cycleBackwardDart_eq_of_tail_eq (hc.mapLe hC₁)
        · exact hfac₁.node_forward_backward ha₁Forward
        · exact hb₁Backward
        · dsimp [a₁, b₁]
          exact (R₁.node_tail _).trans
            ((R₂.node_tail e).trans rfl)
      have harc :=
        cycleSplicedNode_forward_reachable_backward
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ a₁ ha₁Forward
      rw [hnodeEq] at harc
      have hcodeE : rightDartCode hC₁ e = Sum.inl b₁ :=
        rightDartCode_of_common hC₁ e heC
      have hcodeNext :
          rightDartCode hC₁ (R₂.node e) = Sum.inl a₁ :=
        rightDartCode_of_common hC₁ (R₂.node e) hnextC
      rw [hcodeE, hcodeNext]
      exact PermReachable.symm N harc
  · have hcode : rightDartCode hC₁ e = Sum.inr ⟨e, heC⟩ :=
      rightDartCode_of_not_common hC₁ e heC
    have hstep :
        N (Sum.inr ⟨e, heC⟩) =
          rightDartCode hC₁ (R₂.node e) := by
      rfl
    rw [hcode]
    simpa [hstep] using PermReachable.forward N (Sum.inr ⟨e, heC⟩)

theorem cycleSplicedNode_left_reachable_of_old
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
    {e f : OrientedEdge G₁}
    (hef : PermReachable R₁.node e f) :
    PermReachable
      (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
      (Sum.inl e) (Sum.inl f) := by
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  exact permReachable_of_forward_simulation R₁.node N Sum.inl
    (cycleSplicedNode_left_forward_reachable
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂) hef

theorem cycleSplicedNode_right_reachable_of_old
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
    {e f : OrientedEdge G₂}
    (hef : PermReachable R₂.node e f) :
    PermReachable
      (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
      (rightDartCode hC₁ e) (rightDartCode hC₁ f) := by
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  exact permReachable_of_forward_simulation R₂.node N
    (rightDartCode hC₁)
    (cycleSplicedNode_right_forward_reachable
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂) hef

/-- The spliced node permutation has exactly one orbit on every nonempty tail
fibre, provided the two summands meet only on cycle vertices. -/
theorem cycleSplicedNode_reachable_of_same_tail
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
    (hmeet :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support →
        v ∈ c.support)
    (e f : LeftBiasedDart G₁ G₂ C)
    (hef : leftBiasedTail e = leftBiasedTail f) :
    PermReachable
      (cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)
      e f := by
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  have hcross :
      ∀ (e₁ : OrientedEdge G₁)
        (e₂ : {e : OrientedEdge G₂ // ¬ C.Adj e.tail e.head}),
        e₁.tail = e₂.1.tail →
        PermReachable N (Sum.inl e₁) (Sum.inr e₂) := by
    intro e₁ e₂ htail
    have hcycle : e₁.tail ∈ c.support :=
      hmeet e₁.adj.left_mem_support
        (htail ▸ e₂.1.adj.left_mem_support)
    rcases exists_cycleForwardDart_of_mem_support hc hcycle with
      ⟨a, haForward, hatail⟩
    let a₁ : OrientedEdge G₁ := liftOrientedEdge hC₁ a
    let a₂ : OrientedEdge G₂ := liftOrientedEdge hC₂ a
    have haForward₁ :
        CycleForwardDart (c.mapLe hC₁) a₁ :=
      (cycleForwardDart_liftOrientedEdge_iff hC₁ c a).mpr
        haForward
    have haForward₂ :
        CycleForwardDart (c.mapLe hC₂) a₂ :=
      (cycleForwardDart_liftOrientedEdge_iff hC₂ c a).mpr
        haForward
    have hleftOld : PermReachable R₁.node e₁ a₁ :=
      R₁.node_orbit_of_same_tail e₁ a₁ (by
        dsimp [a₁]
        simpa using hatail.symm)
    have hrightOld : PermReachable R₂.node e₂.1 a₂ :=
      R₂.node_orbit_of_same_tail e₂.1 a₂ (by
        dsimp [a₂]
        exact htail.symm.trans (by simpa using hatail.symm))
    have hleft :=
      cycleSplicedNode_left_reachable_of_old
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hleftOld
    have hright :=
      cycleSplicedNode_right_reachable_of_old
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hrightOld
    rw [rightDartCode_of_not_common hC₁ e₂.1 e₂.2,
      rightDartCode_liftOrientedEdge hC₁ hC₂ a] at hright
    exact PermReachable.trans N hleft
      (PermReachable.symm N hright)
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          exact cycleSplicedNode_left_reachable_of_old
            R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
            (R₁.node_orbit_of_same_tail e f hef)
      | inr f =>
          exact hcross e f hef
  | inr e =>
      cases f with
      | inl f =>
          exact PermReachable.symm N (hcross f e hef.symm)
      | inr f =>
          have hright :=
            cycleSplicedNode_right_reachable_of_old
              R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
              (R₂.node_orbit_of_same_tail e.1 f.1 hef)
          simpa [rightDartCode_of_not_common hC₁ e.1 e.2,
            rightDartCode_of_not_common hC₁ f.1 f.2] using hright


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
