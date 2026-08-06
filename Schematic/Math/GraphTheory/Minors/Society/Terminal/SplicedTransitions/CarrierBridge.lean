import Schematic.Math.GraphTheory.Minors.Society.Terminal.SplicedTransitions.Dispatch

/-!
Carrier-clean bridge forms of the outer-arm residual argument.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Carrier-clean bridge form of the outer-left-arm fourth-route argument.
If the bridge meets the prefixed escape away from the old left endpoint, its
last contact with the original clean tail gives the checked spliced-transition
tripod; otherwise `liftAllNilOfOuterLeftArmResidualAndCleanBridge` applies. -/
theorem Tripod.liftAllNilOfOuterLeftArmResidualAndCarrierCleanBridge
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left) :
    Nonempty S.Tripod := by
  let hgraph :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  let qLeft : S.graph.Walk T.left a := T.leftArmPrefixTail hgraph hx_arm q
  by_cases hbridge_q : forall z : V, z ∈ bridge.support ->
      z ∈ qLeft.support -> z = T.left
  · exact
      GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndCleanBridge
        P hno_cross T hij hik hjk hr hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q hx_arm hx_ne_attach hx_internal ha hq_path hq_outside
        hq_clean bridge hbridge_path hbridge_outside hbridge_clean
        (by simpa [qLeft, hgraph] using hbridge_q)
  · push Not at hbridge_q
    rcases hbridge_q with ⟨c, hcBridge, hcQLeft, hc_ne_left⟩
    have hcQ : c ∈ q.support := by
      have hcCases :
          c ∈ (((T.leftToAttach r).takeUntil x hx_arm).mapLe hgraph).support ∨
            c ∈ q.support := by
        simpa [qLeft, Tripod.leftArmPrefixTail,
          SimpleGraph.Walk.mem_support_append_iff] using hcQLeft
      rcases hcCases with hcPrefixMap | hcQ
      · have hcPrefix :
            c ∈ ((T.leftToAttach r).takeUntil x hx_arm).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hcPrefixMap
        have hcArm : c ∈ (T.leftToAttach r).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.leftToAttach r) hx_arm hcPrefix
        rcases hbridge_clean c hcBridge
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim r hcArm)) with hcRight | hcLeft
        · exact False.elim
            (T.right_not_mem_leftToAttach r (by simpa [hcRight] using hcArm))
        · exact False.elim (hc_ne_left hcLeft)
      · exact hcQ
    have hc_ne_x : c ≠ x := by
      intro hcx
      rcases hbridge_clean c hcBridge (by
          rw [hcx]
          exact T.rim_mem_vertexSet hx_internal.1) with hcRight | hcLeft
      · exact hx_internal.2.2 (hcx.symm.trans hcRight)
      · exact hx_internal.2.1 (hcx.symm.trans hcLeft)
    let afterC : S.graph.Walk c a := q.dropUntil c hcQ
    have hafterC_path : afterC.IsPath := by
      simpa [afterC] using hq_path.dropUntil hcQ
    obtain ⟨d, hdAfter, hdBridge, htail_path, hlast, htail_subset,
        _htail_covers, _hd_index⟩ :=
      Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
        (G := S.graph) hafterC_path {z : V | z ∈ bridge.support} hcBridge
    let tail : S.graph.Walk d a := afterC.dropUntil d hdAfter
    have htail_outside : forall z : V,
        z ∈ tail.support -> z ∈ P.outside := by
      intro z hz
      apply hq_outside z
      apply SimpleGraph.Walk.support_dropUntil_subset q hcQ
      apply htail_subset z
      simpa [tail] using hz
    have hx_not_afterC : x ∉ afterC.support := by
      simpa [afterC] using
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne hq_path hcQ hc_ne_x
    have htail_clean : forall z : V, z ∈ tail.support ->
        z ∈ T.vertexSet -> False := by
      intro z hz hzT
      have hzAfter : z ∈ afterC.support :=
        htail_subset z (by simpa [tail] using hz)
      have hzQ : z ∈ q.support :=
        SimpleGraph.Walk.support_dropUntil_subset q hcQ hzAfter
      have hzx : z = x := hq_clean z hzQ hzT
      exact hx_not_afterC (by simpa [hzx] using hzAfter)
    have hbridge_tail : forall z : V, z ∈ bridge.support ->
        z ∈ tail.support -> z = d := by
      intro z hzBridge hzTail
      exact hlast z (by simpa [tail] using hzTail) hzBridge
    exact
      GMIX24SourceProof.Tripod.liftAllNilOfSplicedRightEndpointTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts ha bridge hbridge_path hbridge_outside hbridge_clean
        tail (by simpa [tail] using htail_path) htail_outside htail_clean
        hdBridge hbridge_tail

/-- Right-arm symmetric form of
`liftAllNilOfOuterLeftArmResidualAndCarrierCleanBridge`. -/
theorem Tripod.liftAllNilOfOuterRightArmResidualAndCarrierCleanBridge
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.attachToRight r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (bridge : S.graph.Walk T.left T.right)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.left ∨ z = T.right) :
    Nonempty S.Tripod := by
  let U := T.flip
  have hx_U_arm : x ∈ (U.leftToAttach r).support := by
    apply GMIX24SourceProof.Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T
    simpa [Tripod.rightToAttach,
      SimpleGraph.Walk.support_reverse] using hx_arm
  have hx_U_internal : x ∈ Walk.InternalVertices (U.rim r) := by
    simpa [U, Tripod.flip, Walk.internalVertices_reverse] using hx_internal
  have hpath_contacts_U : forall z : V,
      z ∈ P.pathSet -> z ∈ U.vertexSet ->
        Exists fun m : Fin 3 => z = U.boundary m := by
    simpa [U] using T.pathContacts_flip hpath_contacts
  exact
    GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndCarrierCleanBridge
      P hno_cross U hij hik hjk hr
      (by intro s; simpa [U] using hlegs_nil s)
      (by simpa [U] using hi) (by simpa [U] using hj)
      (by simpa [U] using hk) (by simpa [U] using hij_order)
      (by simpa [U] using hjk_order) hpath_contacts_U q hx_U_arm
      (by simpa [U] using hx_ne_attach) hx_U_internal ha hq_path hq_outside
      (by
        intro z hzq hzU
        exact hq_clean z hzq (by simpa [U] using hzU))
      bridge hbridge_path hbridge_outside
      (by
        intro z hzBridge hzU
        simpa [U] using hbridge_clean z hzBridge (by simpa [U] using hzU))


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
