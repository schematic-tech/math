import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.TailAvoidance

/-!
Tripod lifts for internal outer-rim residual contacts.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Assemble the nontrivial-middle double-collapse tripod from the two exact
tail conditions needed by the construction: contact with the middle old left
arm only at `T.left`, and avoidance of the rebuilt theta. -/
theorem Tripod.liftOuterNilMiddleNonNilCommonLeftOfTailAvoids
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_leftArm_clean :
      forall z : V, z ∈ q.support -> z ∈ (T.leftToAttach j).support ->
        z = T.left)
    (hq_avoids : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  apply GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilCommonLeftOfLegData
    P T hgraph hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
    hi hj hk hij_order hjk_order ha q hq_outside hpath_contacts
  · exact
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_isPath_of_leftArm_clean
        P T hgraph hleg_i_nil hleg_k_nil hi hk q hq_path hq_leftArm_clean
  · intro r s z hzLeg hzRim
    fin_cases r
    · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
        P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
        hij_order hjk_order q hpath_contacts s z hzLeg hzRim
    · exact
        GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_one_meets_rims_of_tail_avoids
        P T hgraph hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
        hi hj hk hij_order hjk_order q hq_avoids hpath_contacts
        s z hzLeg hzRim
    · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
        P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
        hij_order hjk_order q hpath_contacts s z hzLeg hzRim

/-- Direct source constructor for a collapsed outer-rim residual on an old
left arm, when the ordered middle leg is nontrivial. -/
theorem Tripod.liftOuterNilMiddleNonNilLeftArmResidual
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
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
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  let hgraph :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hrj : r ≠ j := by
    rcases hr with rfl | rfl
    · exact hij
    · exact fun h => hjk h.symm
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  have hqLeft_outside : forall z : V, z ∈ qLeft.support -> z ∈ P.outside := by
    simpa [qLeft, hgraph] using
      GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach q hq_outside
  have hqLeft_arm_clean : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.leftToAttach j).support -> z = T.left := by
    simpa [qLeft] using qLeftData.inter_distinct_leftToAttach_eq_left hrj
  have hqLeft_avoids : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False := by
    simpa [qLeft] using
      GMIX24SourceProof.Tripod.leftArmPrefixTail_avoids_outerNilMiddleNonNilCommonLeftRims
        P T hgraph hi hj hk hij_order hjk_order
        hx_arm hx_ne_attach hx_internal q hq_clean hqLeft_outside
  exact GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilCommonLeftOfTailAvoids
    P T hgraph hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
    hi hj hk hij_order hjk_order ha qLeft hqLeft_path hqLeft_outside
    hqLeft_arm_clean hqLeft_avoids hpath_contacts

/-- Right-arm counterpart of `liftOuterNilMiddleNonNilLeftArmResidual`. -/
theorem Tripod.liftOuterNilMiddleNonNilRightArmResidual
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
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
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  let Tflip := T.flip
  have hx_flip_arm : x ∈ (Tflip.leftToAttach r).support := by
    apply GMIX24SourceProof.Tripod.mem_flip_leftToAttach_of_mem_rightToAttach T
    simpa [Tripod.rightToAttach,
      SimpleGraph.Walk.support_reverse] using hx_arm
  have hx_flip_internal : x ∈ Walk.InternalVertices (Tflip.rim r) := by
    simpa [Tflip, Tripod.flip, Walk.internalVertices_reverse] using hx_internal
  have hpath_contacts_flip :
      forall z : V, z ∈ P.pathSet -> z ∈ Tflip.vertexSet ->
        Exists fun m : Fin 3 => z = Tflip.boundary m := by
    simpa [Tflip] using T.pathContacts_flip hpath_contacts
  exact GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilLeftArmResidual
    P hno_cross Tflip hij hik hjk hr
    (by simpa [Tflip] using hleg_i_nil)
    (by simpa [Tflip] using hleg_j_not_nil)
    (by simpa [Tflip] using hleg_k_nil)
    (by simpa [Tflip] using hi) (by simpa [Tflip] using hj)
    (by simpa [Tflip] using hk)
    (by simpa [Tflip] using hij_order)
    (by simpa [Tflip] using hjk_order)
    hpath_contacts_flip q hx_flip_arm (by simpa [Tflip] using hx_ne_attach)
    hx_flip_internal ha hq_path hq_outside
    (by
      intro z hzq hzT
      exact hq_clean z hzq (by simpa [Tflip] using hzT))


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
