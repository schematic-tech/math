import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_two_bridge_splice
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {wExit vHit wPrev vNext wHit vEnter : V}
    (hwExit : wExit ∈ (L.path 0).support)
    (hvHit : vHit ∈ (L.path 0).support)
    (hwPrev : wPrev ∈ (L.path 0).support)
    (hvNext : vNext ∈ (L.path 0).support)
    (hwHit : wHit ∈ (L.path 0).support)
    (hvEnter : vEnter ∈ (L.path 0).support)
    (hExitBefore : (L.path 0).support.idxOf wExit <
      (L.path 0).support.idxOf vHit)
    (hHitPrev : (L.path 0).support.idxOf vHit <=
      (L.path 0).support.idxOf wPrev)
    (hPrevNext : (L.path 0).support.idxOf wPrev <
      (L.path 0).support.idxOf vNext)
    (hNextHit : (L.path 0).support.idxOf vNext <=
      (L.path 0).support.idxOf wHit)
    (hHitEnter : (L.path 0).support.idxOf wHit <
      (L.path 0).support.idxOf vEnter)
    (pIn : G.Walk (left iNew) vHit)
    (pBridge : G.Walk wExit vNext)
    (pBridgeLast : G.Walk wPrev vEnter)
    (pOut : G.Walk wHit (right jNew))
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (hBridgeAvoid :
      forall x : V, x ∈ pBridge.support ->
        x ∉ L.usedVertices ∨ x = wExit ∨ x = vNext)
    (hBridgeLastAvoid :
      forall x : V, x ∈ pBridgeLast.support ->
        x ∉ L.usedVertices ∨ x = wPrev ∨ x = vEnter)
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit)
    (hInBridge :
      Disjoint {x : V | x ∈ pIn.support}
        {x : V | x ∈ pBridge.support})
    (hBridgeBridge :
      Disjoint {x : V | x ∈ pBridge.support}
        {x : V | x ∈ pBridgeLast.support})
    (hBridgeLastOut :
      Disjoint {x : V | x ∈ pBridgeLast.support}
        {x : V | x ∈ pOut.support})
    (hInOut :
      Disjoint {x : V | x ∈ pIn.support}
        {x : V | x ∈ pOut.support}) :
    HasPartialThreeVertexLinkage G left right 2 := by
  classical
  let q : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)) :=
    L.path 0
  have hqpath : q.IsPath := by
    simpa [q] using L.isPath 0
  have hwExitq : wExit ∈ q.support := by
    simpa [q] using hwExit
  have hvHitq : vHit ∈ q.support := by
    simpa [q] using hvHit
  have hwPrevq : wPrev ∈ q.support := by
    simpa [q] using hwPrev
  have hvNextq : vNext ∈ q.support := by
    simpa [q] using hvNext
  have hwHitq : wHit ∈ q.support := by
    simpa [q] using hwHit
  have hvEnterq : vEnter ∈ q.support := by
    simpa [q] using hvEnter
  have hExitBefore_q :
      q.support.idxOf wExit < q.support.idxOf vHit := by
    simpa [q] using hExitBefore
  have hHitPrev_q :
      q.support.idxOf vHit <= q.support.idxOf wPrev := by
    simpa [q] using hHitPrev
  have hPrevNext_q :
      q.support.idxOf wPrev < q.support.idxOf vNext := by
    simpa [q] using hPrevNext
  have hNextHit_q :
      q.support.idxOf vNext <= q.support.idxOf wHit := by
    simpa [q] using hNextHit
  have hHitEnter_q :
      q.support.idxOf wHit < q.support.idxOf vEnter := by
    simpa [q] using hHitEnter
  let pTake : G.Walk (left (L.leftIndex 0)) wExit :=
    q.takeUntil wExit hwExitq
  let pSegA : G.Walk vNext wHit :=
    Walk.segment (G := G) q hvNextq hwHitq hNextHit_q
  let pSegB : G.Walk vHit wPrev :=
    Walk.segment (G := G) q hvHitq hwPrevq hHitPrev_q
  let pDrop : G.Walk vEnter (right (L.rightIndex 0)) :=
    q.dropUntil vEnter hvEnterq
  have htake_used :
      forall x : V, x ∈ pTake.support -> x ∈ L.usedVertices := by
    intro x hx
    exact ⟨0, by
      simpa [q, pTake] using
        SimpleGraph.Walk.support_takeUntil_subset q hwExitq hx⟩
  have hsegA_used :
      forall x : V, x ∈ pSegA.support -> x ∈ L.usedVertices := by
    intro x hx
    exact ⟨0, by
      simpa [q, pSegA] using
        Walk.segment_support_subset (G := G) q hvNextq hwHitq hNextHit_q hx⟩
  have hsegB_used :
      forall x : V, x ∈ pSegB.support -> x ∈ L.usedVertices := by
    intro x hx
    exact ⟨0, by
      simpa [q, pSegB] using
        Walk.segment_support_subset (G := G) q hvHitq hwPrevq hHitPrev_q hx⟩
  have hdrop_used :
      forall x : V, x ∈ pDrop.support -> x ∈ L.usedVertices := by
    intro x hx
    exact ⟨0, by
      simpa [q, pDrop] using
        SimpleGraph.Walk.support_dropUntil_subset q hvEnterq hx⟩
  have hvHit_not_take : vHit ∉ pTake.support := by
    dsimp [pTake]
    exact Walk.not_mem_takeUntil_of_idxOf_lt
      (G := G) hwExitq hExitBefore_q
  have hwPrev_not_take : wPrev ∉ pTake.support := by
    dsimp [pTake]
    exact Walk.not_mem_takeUntil_of_idxOf_lt
      (G := G) hwExitq (by omega)
  have hwHit_not_take : wHit ∉ pTake.support := by
    dsimp [pTake]
    exact Walk.not_mem_takeUntil_of_idxOf_lt
      (G := G) hwExitq (by omega)
  have hvEnter_not_take : vEnter ∉ pTake.support := by
    dsimp [pTake]
    exact Walk.not_mem_takeUntil_of_idxOf_lt
      (G := G) hwExitq (by omega)
  have hwExit_not_segB : wExit ∉ pSegB.support := by
    intro hx
    have hv_le :
        q.support.idxOf vHit <= q.support.idxOf wExit :=
      Walk.IsPath.idxOf_left_le_of_mem_segment
        (G := G) hqpath hvHitq hwPrevq hHitPrev_q hx
    omega
  have hvNext_not_segB : vNext ∉ pSegB.support := by
    dsimp [pSegB]
    exact
      Walk.IsPath.not_mem_segment_of_idxOf_right_lt
        (G := G) hqpath hvHitq hwPrevq hHitPrev_q hPrevNext_q
  have vHit_not_segA : vHit ∉ pSegA.support := by
    intro hx
    have hnext_le :
        q.support.idxOf vNext <= q.support.idxOf vHit :=
      Walk.IsPath.idxOf_left_le_of_mem_segment
        (G := G) hqpath hvNextq hwHitq hNextHit_q hx
    omega
  have hwPrev_not_segA : wPrev ∉ pSegA.support := by
    intro hx
    have hnext_le :
        q.support.idxOf vNext <= q.support.idxOf wPrev :=
      Walk.IsPath.idxOf_left_le_of_mem_segment
        (G := G) hqpath hvNextq hwHitq hNextHit_q hx
    omega
  have hvEnter_not_segA : vEnter ∉ pSegA.support := by
    dsimp [pSegA]
    exact
      Walk.IsPath.not_mem_segment_of_idxOf_right_lt
        (G := G) hqpath hvNextq hwHitq hNextHit_q hHitEnter_q
  have hwExit_not_drop : wExit ∉ pDrop.support := by
    dsimp [pDrop]
    exact Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
      (G := G) hqpath hvEnterq hwExitq (by omega)
  have hvNext_not_drop : vNext ∉ pDrop.support := by
    dsimp [pDrop]
    exact Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
      (G := G) hqpath hvEnterq hvNextq (by omega)
  have hwHit_not_drop : wHit ∉ pDrop.support := by
    dsimp [pDrop]
    exact Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
      (G := G) hqpath hvEnterq hwHitq hHitEnter_q
  have hTakeIn :
      Disjoint {x : V | x ∈ pTake.support}
        {x : V | x ∈ pIn.support} := by
    rw [disjoint_comm]
    exact L.walk_support_disjoint_of_avoids_usedVertices
      hInAvoid htake_used hvHit_not_take
  have hTakeSegB :
      Disjoint {x : V | x ∈ pTake.support}
        {x : V | x ∈ pSegB.support} := by
    exact
      Walk.IsPath.takeUntil_support_disjoint_segment_of_idxOf_lt
        (G := G) hqpath hwExitq hvHitq hwPrevq hHitPrev_q
        hExitBefore_q
  have hTakeBridgeLast :
      Disjoint {x : V | x ∈ pTake.support}
        {x : V | x ∈ pBridgeLast.support} := by
    rw [disjoint_comm]
    exact L.walk_support_disjoint_of_avoids_usedVertices_two
      hBridgeLastAvoid htake_used hwPrev_not_take hvEnter_not_take
  have hTakeDrop :
      Disjoint {x : V | x ∈ pTake.support}
        {x : V | x ∈ pDrop.support} := by
    dsimp [pTake, pDrop]
    exact Walk.IsPath.takeUntil_support_disjoint_dropUntil_of_idxOf_lt
      (G := G) hqpath hwExitq hvEnterq (by omega)
  have hBridgeIn :
      Disjoint {x : V | x ∈ pBridge.support}
        {x : V | x ∈ pIn.support} := by
    rw [disjoint_comm]
    exact hInBridge
  have hBridgeSegB :
      Disjoint {x : V | x ∈ pBridge.support}
        {x : V | x ∈ pSegB.support} := by
    exact L.walk_support_disjoint_of_avoids_usedVertices_two
      hBridgeAvoid hsegB_used hwExit_not_segB hvNext_not_segB
  have hBridgeDrop :
      Disjoint {x : V | x ∈ pBridge.support}
        {x : V | x ∈ pDrop.support} := by
    exact L.walk_support_disjoint_of_avoids_usedVertices_two
      hBridgeAvoid hdrop_used hwExit_not_drop hvNext_not_drop
  have hSegAIn :
      Disjoint {x : V | x ∈ pSegA.support}
        {x : V | x ∈ pIn.support} := by
    rw [disjoint_comm]
    exact L.walk_support_disjoint_of_avoids_usedVertices
      hInAvoid hsegA_used vHit_not_segA
  have hSegASegB :
      Disjoint {x : V | x ∈ pSegA.support}
        {x : V | x ∈ pSegB.support} := by
    rw [disjoint_comm]
    exact
      Walk.IsPath.segment_support_disjoint_of_right_lt_left
        (G := G) hqpath hvHitq hwPrevq hvNextq hwHitq
        hHitPrev_q hNextHit_q hPrevNext_q
  have hSegABridgeLast :
      Disjoint {x : V | x ∈ pSegA.support}
        {x : V | x ∈ pBridgeLast.support} := by
    rw [disjoint_comm]
    exact L.walk_support_disjoint_of_avoids_usedVertices_two
      hBridgeLastAvoid hsegA_used hwPrev_not_segA hvEnter_not_segA
  have hSegADrop :
      Disjoint {x : V | x ∈ pSegA.support}
        {x : V | x ∈ pDrop.support} := by
    dsimp [pSegA, pDrop]
    exact
      Walk.IsPath.segment_support_disjoint_dropUntil_of_idxOf_lt
        (G := G) hqpath hvNextq hwHitq hvEnterq hNextHit_q
        hHitEnter_q
  have hOutSegB :
      Disjoint {x : V | x ∈ pOut.support}
        {x : V | x ∈ pSegB.support} := by
    have hwHit_not_segB : wHit ∉ pSegB.support := by
      dsimp [pSegB]
      exact
        Walk.IsPath.not_mem_segment_of_idxOf_right_lt
          (G := G) hqpath hvHitq hwPrevq hHitPrev_q
          (by omega)
    exact L.walk_support_disjoint_of_avoids_usedVertices
      hOutAvoid hsegB_used hwHit_not_segB
  have hOutDrop :
      Disjoint {x : V | x ∈ pOut.support}
        {x : V | x ∈ pDrop.support} := by
    exact L.walk_support_disjoint_of_avoids_usedVertices
      hOutAvoid hdrop_used hwHit_not_drop
  let pOldHead : G.Walk (left (L.leftIndex 0)) vNext :=
    pTake.append pBridge
  let pOldTail : G.Walk vNext (right jNew) :=
    pSegA.append pOut
  let pNewHead : G.Walk (left iNew) wPrev :=
    pIn.append pSegB
  let pNewTail : G.Walk wPrev (right (L.rightIndex 0)) :=
    pBridgeLast.append pDrop
  have hHeadHead :
      Disjoint {x : V | x ∈ pOldHead.support}
        {x : V | x ∈ pNewHead.support} := by
    exact
      Walk.support_append_disjoint_append
        (G := G) hTakeIn hTakeSegB hBridgeIn hBridgeSegB
  have hHeadTail :
      Disjoint {x : V | x ∈ pOldHead.support}
        {x : V | x ∈ pNewTail.support} := by
    exact
      Walk.support_append_disjoint_append
        (G := G) hTakeBridgeLast hTakeDrop hBridgeBridge
        hBridgeDrop
  have hTailHead :
      Disjoint {x : V | x ∈ pOldTail.support}
        {x : V | x ∈ pNewHead.support} := by
    exact
      Walk.support_append_disjoint_append
        (G := G) hSegAIn hSegASegB (by
          rw [disjoint_comm]
          exact hInOut) hOutSegB
  have hTailTail :
      Disjoint {x : V | x ∈ pOldTail.support}
        {x : V | x ∈ pNewTail.support} := by
    exact
      Walk.support_append_disjoint_append
        (G := G) hSegABridgeLast hSegADrop (by
          rw [disjoint_comm]
          exact hBridgeLastOut) hOutDrop
  have hdisj :
      Disjoint {x : V | x ∈ (pOldHead.append pOldTail).support}
        {x : V | x ∈ (pNewHead.append pNewTail).support} := by
    exact
      Walk.support_append_disjoint_append
        (G := G) hHeadHead hHeadTail hTailHead hTailTail
  exact
    L.hasPartial_two_of_one_path_splice_walks hiNew hjNew
      (pOldHead.append pOldTail) (pNewHead.append pNewTail) hdisj

theorem PartialThreeVertexLinkage.mem_path_zero_of_usedVertices_one
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {v : V} (hv : v ∈ L.usedVertices) :
    v ∈ (L.path 0).support := by
  rcases hv with ⟨k, hk⟩
  have hk0 : k = 0 := Subsingleton.elim k 0
  rw [hk0] at hk
  simpa using hk

theorem PartialThreeVertexLinkage.mem_path_zero_or_one_of_usedVertices_two
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {v : V} (hv : v ∈ L.usedVertices) :
    v ∈ (L.path 0).support ∨ v ∈ (L.path 1).support := by
  rcases hv with ⟨k, hk⟩
  fin_cases k
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa using hk)

theorem PartialThreeVertexLinkage.not_mem_path_one_of_mem_path_zero_two
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {v : V} (hv0 : v ∈ (L.path 0).support) :
    v ∉ (L.path 1).support := by
  intro hv1
  exact Set.disjoint_left.mp
    (L.pairwise_vertex_disjoint 0 1 (by decide)) hv0 hv1

theorem PartialThreeVertexLinkage.not_mem_path_zero_of_mem_path_one_two
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {v : V} (hv1 : v ∈ (L.path 1).support) :
    v ∉ (L.path 0).support := by
  intro hv0
  exact Set.disjoint_left.mp
    (L.pairwise_vertex_disjoint 1 0 (by decide)) hv1 hv0

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_ordered_splice
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {vHit wHit : V}
    (hvHit : vHit ∈ L.usedVertices)
    (hwHit : wHit ∈ L.usedVertices)
    (horder :
      (L.path 0).support.idxOf wHit < (L.path 0).support.idxOf vHit)
    (pIn : G.Walk (left iNew) vHit)
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (pOut : G.Walk wHit (right jNew))
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit)
    (hOutIn : Disjoint {x : V | x ∈ pOut.support}
      {x : V | x ∈ pIn.support}) :
    HasPartialThreeVertexLinkage G left right 2 := by
  let q := L.path 0
  have hqpath : q.IsPath := by simpa [q] using L.isPath 0
  have hvq : vHit ∈ q.support := by
    simpa [q] using L.mem_path_zero_of_usedVertices_one hvHit
  have hwq : wHit ∈ q.support := by
    simpa [q] using L.mem_path_zero_of_usedVertices_one hwHit
  let oldToW : G.Walk (left (L.leftIndex 0)) wHit := q.takeUntil wHit hwq
  let vToOld : G.Walk vHit (right (L.rightIndex 0)) := q.dropUntil vHit hvq
  have htake_used :
      forall x : V, x ∈ oldToW.support -> x ∈ L.usedVertices := by
    intro x hx
    exact ⟨0, by
      simpa [q, oldToW] using
        SimpleGraph.Walk.support_takeUntil_subset q hwq hx⟩
  have hdrop_used :
      forall x : V, x ∈ vToOld.support -> x ∈ L.usedVertices := by
    intro x hx
    exact ⟨0, by
      simpa [q, vToOld] using
        SimpleGraph.Walk.support_dropUntil_subset q hvq hx⟩
  have hv_not_oldToW : vHit ∉ oldToW.support := by
    dsimp [oldToW]
    exact Walk.not_mem_takeUntil_of_idxOf_lt (G := G) hwq horder
  have hw_not_vToOld : wHit ∉ vToOld.support := by
    dsimp [vToOld]
    exact Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
      (G := G) hqpath hvq hwq horder
  have h_old_in :
      Disjoint {x : V | x ∈ oldToW.support}
        {x : V | x ∈ pIn.support} := by
    rw [disjoint_comm]
    exact
      L.walk_support_disjoint_of_avoids_usedVertices
        hInAvoid htake_used hv_not_oldToW
  have h_old_drop :
      Disjoint {x : V | x ∈ oldToW.support}
        {x : V | x ∈ vToOld.support} := by
    dsimp [oldToW, vToOld]
    exact Walk.IsPath.takeUntil_support_disjoint_dropUntil_of_idxOf_lt
      (G := G) hqpath hwq hvq horder
  have h_out_drop :
      Disjoint {x : V | x ∈ pOut.support}
        {x : V | x ∈ vToOld.support} := by
    exact
      L.walk_support_disjoint_of_avoids_usedVertices
        hOutAvoid hdrop_used hw_not_vToOld
  have hconcat :
      Disjoint {x : V | x ∈ ((oldToW.append pOut).support)}
        {x : V | x ∈ ((pIn.append vToOld).support)} := by
    exact Walk.support_append_disjoint_append
      (G := G) h_old_in h_old_drop hOutIn h_out_drop
  exact L.hasPartial_two_of_one_path_splice_walks hiNew hjNew
    (oldToW.append pOut) (pIn.append vToOld) hconcat

theorem PartialThreeVertexLinkage.hasPartial_two_of_one_path_ordered_splice_or_direct
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {vHit wHit : V}
    (hvHit : vHit ∈ L.usedVertices)
    (hwHit : wHit ∈ L.usedVertices)
    (horder :
      (L.path 0).support.idxOf wHit < (L.path 0).support.idxOf vHit)
    (pIn : G.Walk (left iNew) vHit)
    (hpIn : pIn.IsPath)
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (pOut : G.Walk wHit (right jNew))
    (hpOut : pOut.IsPath)
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit) :
    HasPartialThreeVertexLinkage G left right 2 := by
  by_cases hOutIn :
      Disjoint {x : V | x ∈ pOut.support}
        {x : V | x ∈ pIn.support}
  · exact L.hasPartial_two_of_one_path_ordered_splice
      hiNew hjNew hvHit hwHit horder pIn hInAvoid pOut hOutAvoid hOutIn
  · rw [Set.not_disjoint_iff] at hOutIn
    rcases hOutIn with ⟨x, hxOut, hxIn⟩
    simp only [Set.mem_setOf_eq] at hxOut hxIn
    have hx_not_used : x ∉ L.usedVertices := by
      rcases hInAvoid x hxIn with hx_not | hxv
      · exact hx_not
      rcases hOutAvoid x hxOut with hx_not | hxw
      · exact hx_not
      have hvw : vHit = wHit := hxv.symm.trans hxw
      have hbad :
          (L.path 0).support.idxOf wHit <
            (L.path 0).support.idxOf wHit := by
        rw [hvw] at horder
        exact horder
      exact False.elim (Nat.lt_irrefl _ hbad)
    have hx_ne_v : x ≠ vHit := by
      intro hxv
      exact hx_not_used (by simpa [hxv] using hvHit)
    have hx_ne_w : x ≠ wHit := by
      intro hxw
      exact hx_not_used (by simpa [hxw] using hwHit)
    let pDirect : G.Walk (left iNew) (right jNew) :=
      (pIn.takeUntil x hxIn).append (pOut.dropUntil x hxOut)
    have hdirect_avoid :
        forall y : V, y ∈ pDirect.support -> y ∉ L.usedVertices := by
      intro y hy
      dsimp [pDirect] at hy
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy
      rcases hy with hyIn | hyOut
      · have hyIn_full : y ∈ pIn.support :=
          SimpleGraph.Walk.support_takeUntil_subset pIn hxIn hyIn
        rcases hInAvoid y hyIn_full with hy_not | hyv
        · exact hy_not
        · subst y
          exact False.elim
            ((SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              hpIn hxIn hx_ne_v.symm) hyIn)
      · have hyOut_full : y ∈ pOut.support :=
          SimpleGraph.Walk.support_dropUntil_subset pOut hxOut hyOut
        rcases hOutAvoid y hyOut_full with hy_not | hyw
        · exact hy_not
        · subst y
          exact False.elim
            ((Walk.IsPath.start_not_mem_dropUntil_support_of_ne
              hpOut hxOut hx_ne_w) hyOut)
    exact L.hasPartial_succ_of_path_avoids_usedVertices
      hiNew hjNew (pDirect.toPath : G.Walk (left iNew) (right jNew))
      pDirect.toPath.property (by
        intro y hy
        exact hdirect_avoid y
          (SimpleGraph.Walk.support_toPath_subset pDirect hy))

noncomputable def PartialThreeVertexLinkage.spliceFirstOfTwoPaths
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOldToNew : G.Walk (left (L.leftIndex 0)) (right jNew))
    (hpOldToNew : pOldToNew.IsPath)
    (pNewToOld : G.Walk (left iNew) (right (L.rightIndex 0)))
    (hpNewToOld : pNewToOld.IsPath)
    (hdisjNew : Disjoint {v : V | v ∈ pOldToNew.support}
      {v : V | v ∈ pNewToOld.support})
    (hdisjOldToOther : Disjoint {v : V | v ∈ (L.path 1).support}
      {v : V | v ∈ pOldToNew.support})
    (hdisjNewToOther : Disjoint {v : V | v ∈ (L.path 1).support}
      {v : V | v ∈ pNewToOld.support}) :
    PartialThreeVertexLinkage G left right 3 := by
  let Lother : PartialThreeVertexLinkage G left right 1 :=
    PartialThreeVertexLinkage.ofOnePath (G := G)
      (left := left) (right := right) (i := L.leftIndex 1)
      (j := L.rightIndex 1) (L.path 1) (L.isPath 1)
  have hiOld : L.leftIndex 0 ∉ Set.range Lother.leftIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    have heq : L.leftIndex 0 = L.leftIndex 1 := by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk.symm
    have h01 : (0 : Fin 2) = 1 := L.leftIndex_injective heq
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have hjNewOther : jNew ∉ Set.range Lother.rightIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    exact hjNew ⟨1, by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk⟩
  let Ltwo : PartialThreeVertexLinkage G left right 2 :=
    Lother.snocPath hiOld hjNewOther pOldToNew hpOldToNew (by
      intro k
      have hk0 : k = 0 := Subsingleton.elim k 0
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0]
        using hdisjOldToOther)
  have hiNewTwo : iNew ∉ Set.range Ltwo.leftIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hiNew ⟨0, by simpa [Ltwo, Fin.snoc_last] using hk⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        exact hiNew ⟨1, by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk⟩
  have hjOldTwo : L.rightIndex 0 ∉ Set.range Ltwo.rightIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hjNew ⟨0, by simpa [Ltwo, Fin.snoc_last] using hk.symm⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        have heq : L.rightIndex 0 = L.rightIndex 1 := by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk.symm
        have h01 : (0 : Fin 2) = 1 := L.rightIndex_injective heq
        exact (by decide : (0 : Fin 2) ≠ 1) h01
  exact Ltwo.snocPath hiNewTwo hjOldTwo pNewToOld hpNewToOld (by
    intro k
    cases k using Fin.lastCases with
    | last =>
        simpa [Ltwo, PartialThreeVertexLinkage.snocPath, Fin.snoc_last]
          using hdisjNew
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
          PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
          using hdisjNewToOther)

noncomputable def PartialThreeVertexLinkage.spliceSecondOfTwoPaths
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOldToNew : G.Walk (left (L.leftIndex 1)) (right jNew))
    (hpOldToNew : pOldToNew.IsPath)
    (pNewToOld : G.Walk (left iNew) (right (L.rightIndex 1)))
    (hpNewToOld : pNewToOld.IsPath)
    (hdisjNew : Disjoint {v : V | v ∈ pOldToNew.support}
      {v : V | v ∈ pNewToOld.support})
    (hdisjOldToOther : Disjoint {v : V | v ∈ (L.path 0).support}
      {v : V | v ∈ pOldToNew.support})
    (hdisjNewToOther : Disjoint {v : V | v ∈ (L.path 0).support}
      {v : V | v ∈ pNewToOld.support}) :
    PartialThreeVertexLinkage G left right 3 := by
  let Lother : PartialThreeVertexLinkage G left right 1 :=
    PartialThreeVertexLinkage.ofOnePath (G := G)
      (left := left) (right := right) (i := L.leftIndex 0)
      (j := L.rightIndex 0) (L.path 0) (L.isPath 0)
  have hiOld : L.leftIndex 1 ∉ Set.range Lother.leftIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    have heq : L.leftIndex 1 = L.leftIndex 0 := by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk.symm
    have h10 : (1 : Fin 2) = 0 := L.leftIndex_injective heq
    exact (by decide : (1 : Fin 2) ≠ 0) h10
  have hjNewOther : jNew ∉ Set.range Lother.rightIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    exact hjNew ⟨0, by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk⟩
  let Ltwo : PartialThreeVertexLinkage G left right 2 :=
    Lother.snocPath hiOld hjNewOther pOldToNew hpOldToNew (by
      intro k
      have hk0 : k = 0 := Subsingleton.elim k 0
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0]
        using hdisjOldToOther)
  have hiNewTwo : iNew ∉ Set.range Ltwo.leftIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hiNew ⟨1, by simpa [Ltwo, Fin.snoc_last] using hk⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        exact hiNew ⟨0, by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk⟩
  have hjOldTwo : L.rightIndex 1 ∉ Set.range Ltwo.rightIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hjNew ⟨1, by simpa [Ltwo, Fin.snoc_last] using hk.symm⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        have heq : L.rightIndex 1 = L.rightIndex 0 := by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk.symm
        have h10 : (1 : Fin 2) = 0 := L.rightIndex_injective heq
        exact (by decide : (1 : Fin 2) ≠ 0) h10
  exact Ltwo.snocPath hiNewTwo hjOldTwo pNewToOld hpNewToOld (by
    intro k
    cases k using Fin.lastCases with
    | last =>
        simpa [Ltwo, PartialThreeVertexLinkage.snocPath, Fin.snoc_last]
          using hdisjNew
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
          PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
          using hdisjNewToOther)


end Schematic.Math.GraphTheory
