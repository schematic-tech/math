import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameFirstTransition

/-!
Tripod reconstruction from clean common-end bridges.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Rebuilt rims for the all-collapsed common-end construction with a clean
outside bridge from the old right end to the old left end. -/
def Tripod.allNilCleanBridgeRim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_j_nil : (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (bridge : S.graph.Walk T.right T.left) :
    Fin 3 -> S.graph.Walk T.right (T.boundary j)
  | 0 =>
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim P T hgraph
        hi hj hk hij_order hjk_order 0
  | 1 =>
      (bridge.append ((T.leftToAttach j).mapLe hgraph)).copy rfl
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil).symm
  | 2 =>
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim P T hgraph
        hi hj hk hij_order hjk_order 2

/-- Simplicity of the three clean-bridge rebuilt rims. -/
theorem Tripod.allNilCleanBridgeRim_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
        hleg_j_nil
        hi hj hk hij_order hjk_order bridge r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.allNilCleanBridgeRim] using
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
        P T hgraph hij hik hjk
        hi hj hk hij_order hjk_order hpath_contacts 0
  · have happ :
        (bridge.append ((T.leftToAttach j).mapLe hgraph)).IsPath := by
      refine Walk.IsPath.append_of_support_inter_eq_endpoint hbridge_path
        (SimpleGraph.Walk.IsPath.mapLe hgraph (T.leftToAttach_isPath j)) ?_
      intro z hzBridge hzArm
      have hzArmOld : z ∈ (T.leftToAttach j).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
      rcases hbridge_clean z hzBridge
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzArmOld)) with
        hzRight | hzLeft
      · exact False.elim
          (T.right_not_mem_leftToAttach j (by simpa [hzRight] using hzArmOld))
      · exact hzLeft
    simpa [Tripod.allNilCleanBridgeRim] using
      (SimpleGraph.Walk.isPath_copy
        (bridge.append ((T.leftToAttach j).mapLe hgraph)) rfl
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil).symm).mpr happ
  · simpa [Tripod.allNilCleanBridgeRim] using
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
        P T hgraph hij hik hjk
        hi hj hk hij_order hjk_order hpath_contacts 2

/-- Each selected attachment lies internally on its clean-bridge rebuilt
rim. -/
theorem Tripod.allNilCleanBridgeAttach_mem_rim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
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
    (bridge : S.graph.Walk T.right T.left) :
    forall r : Fin 3,
      GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k r ∈
        Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil
          hi hj hk hij_order hjk_order bridge r) := by
  intro r
  fin_cases r
  · refine ⟨?_, (T.attach_mem_rim i).2.2, ?_⟩
    · change T.attach i ∈
        (T.rightToBoundaryViaLegTail hgraph i
          (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order))).support
      rw [Tripod.rightToBoundaryViaLegTail,
        SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl (by
        simp [SimpleGraph.Walk.support_mapLe_eq_support])
    · intro hai_j
      have hbi := (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil
      exact hij (T.boundary_injective (hbi.trans hai_j))
  · refine ⟨?_, ?_, ?_⟩
    simp [Tripod.allNilCleanBridgeAttach, Tripod.allNilCleanBridgeRim,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_append_iff]
    · simpa [Tripod.allNilCleanBridgeAttach] using T.left_ne_right
    · simpa [Tripod.allNilCleanBridgeAttach] using T.left_ne_boundary j
  · refine ⟨?_, (T.attach_mem_rim k).2.2, ?_⟩
    · change T.attach k ∈
        (T.rightToBoundaryViaLegTail hgraph k
          (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).reverse).support
      rw [Tripod.rightToBoundaryViaLegTail,
        SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl (by
        simp [SimpleGraph.Walk.support_mapLe_eq_support])
    · intro hak_j
      have hbk := (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil
      exact hjk (T.boundary_injective (hbk.trans hak_j).symm)

/-- Support decomposition of the middle clean-bridge rim. -/
theorem Tripod.allNilCleanBridgeRim_one_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_j_nil : (T.leg j).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (bridge : S.graph.Walk T.right T.left)
    {z : V}
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
        hleg_j_nil hi hj hk
        hij_order hjk_order bridge 1).support) :
    z ∈ bridge.support ∨ z ∈ (T.leftToAttach j).support := by
  change z ∈
    ((bridge.append ((T.leftToAttach j).mapLe hgraph)).copy rfl
      ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil).symm).support at hz
  rw [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzBridge | hzArm
  · exact Or.inl hzBridge
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)

/-- The middle clean-bridge rim is internally disjoint from the first outer
rim. -/
theorem Tripod.allNilCleanBridgeRim_one_zero_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge 1))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge 0)) := by
  rw [Set.disjoint_left]
  intro z hzMiddle hzOuter
  rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
      P T hgraph hleg_j_nil hi hj hk
      hij_order hjk_order bridge hzMiddle.1 with hzBridge | hzLeftArm
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
        (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1) with
      hzRightArm | hzRest
    · rcases hbridge_clean z hzBridge
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzRightArm)) with
        hzRight | hzLeft
      · exact hzMiddle.2.1 hzRight
      · exact T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightArm)
    · rcases hzRest with hzLeg | hzSegment
      · rcases hbridge_clean z hzBridge (T.leg_mem_vertexSet hzLeg) with
          hzRight | hzLeft
        · exact hzMiddle.2.1 hzRight
        · exact T.left_not_mem_leg i (by simpa [hzLeft] using hzLeg)
      · exact (hbridge_outside z hzBridge).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment)
  · have hzRimJ : z ∈ (T.rim j).support :=
      T.leftToAttach_support_subset_rim j hzLeftArm
    rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
        (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1) with
      hzRightArm | hzRest
    · have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left (fun h => hij h.symm)
          hzLeftArm (T.rightToAttach_support_subset_rim i hzRightArm)
      exact T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightArm)
    · rcases hzRest with hzLeg | hzSegment
      · have hzAttach : z = T.attach i :=
          T.legs_meet_rims_only_at_attach i j z hzLeg hzRimJ
        exact T.attach_not_mem_rim_of_ne hij (by simpa [hzAttach] using hzRimJ)
      · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order hpath_contacts
            hzSegment (T.rim_mem_vertexSet hzRimJ) with hzi | hzj
        · exact T.boundary_not_mem_rim_of_ne_index hij
            (by simpa [hzi] using hzRimJ)
        · exact hzMiddle.2.2 hzj

/-- The middle clean-bridge rim is internally disjoint from the last outer
rim. -/
theorem Tripod.allNilCleanBridgeRim_one_two_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge 1))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge 2)) := by
  rw [Set.disjoint_left]
  intro z hzMiddle hzOuter
  rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
      P T hgraph hleg_j_nil hi hj hk
      hij_order hjk_order bridge hzMiddle.1 with hzBridge | hzLeftArm
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
        (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1) with
      hzRightArm | hzRest
    · rcases hbridge_clean z hzBridge
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim k hzRightArm)) with
        hzRight | hzLeft
      · exact hzMiddle.2.1 hzRight
      · exact T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzRightArm)
    · rcases hzRest with hzLeg | hzSegmentRev
      · rcases hbridge_clean z hzBridge (T.leg_mem_vertexSet hzLeg) with
          hzRight | hzLeft
        · exact hzMiddle.2.1 hzRight
        · exact T.left_not_mem_leg k (by simpa [hzLeft] using hzLeg)
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact (hbridge_outside z hzBridge).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment)
  · have hzRimJ : z ∈ (T.rim j).support :=
      T.leftToAttach_support_subset_rim j hzLeftArm
    rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
        (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1) with
      hzRightArm | hzRest
    · have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left hjk hzLeftArm
          (T.rightToAttach_support_subset_rim k hzRightArm)
      exact T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzRightArm)
    · rcases hzRest with hzLeg | hzSegmentRev
      · have hzAttach : z = T.attach k :=
          T.legs_meet_rims_only_at_attach k j z hzLeg hzRimJ
        exact T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
          (by simpa [hzAttach] using hzRimJ)
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegment (T.rim_mem_vertexSet hzRimJ) with hzj | hzk
        · exact hzMiddle.2.2 hzj
        · exact T.boundary_not_mem_rim_of_ne_index
            (i := k) (s := j) (fun h => hjk h.symm)
            (by simpa [hzk] using hzRimJ)

/-- Pairwise internal disjointness of all three clean-bridge rebuilt rims. -/
theorem Tripod.allNilCleanBridgeRims_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge r))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact (GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_zero_internal_disjoint
      P T hgraph hij hik hjk hleg_j_nil
      hi hj hk hij_order hjk_order hpath_contacts bridge
      hbridge_outside hbridge_clean).symm
  · simpa [Tripod.allNilCleanBridgeRim] using
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts
  · exact GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_zero_internal_disjoint
      P T hgraph hij hik hjk hleg_j_nil
      hi hj hk hij_order hjk_order hpath_contacts bridge
      hbridge_outside hbridge_clean
  · exact False.elim (hrs rfl)
  · exact GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_j_nil
      hi hj hk hij_order hjk_order hpath_contacts bridge
      hbridge_outside hbridge_clean
  · simpa [Tripod.allNilCleanBridgeRim] using
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts).symm
  · exact (GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_j_nil
      hi hj hk hij_order hjk_order hpath_contacts bridge
      hbridge_outside hbridge_clean).symm
  · exact False.elim (hrs rfl)

/-- The clean-bridge theta construction only needs carrier cleanliness to
prove that the inserted bridge meets each outer rebuilt rim at the common
right endpoint.  Exposing that exact condition lets structured carrier
transitions reuse the same construction. -/
theorem Tripod.allNilCleanBridgeRims_internal_disjoint_of_outer_contacts
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_zero : forall z : V, z ∈ bridge.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 0).support -> z = T.right)
    (hbridge_two : forall z : V, z ∈ bridge.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 2).support -> z = T.right) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge r))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge s)) := by
  have hone_zero :
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge 1))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge 0)) := by
    rw [Set.disjoint_left]
    intro z hzMiddle hzOuter
    rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzMiddle.1 with hzBridge | hzLeftArm
    · exact hzMiddle.2.1 (hbridge_zero z hzBridge
        (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1))
    · have hzRimJ : z ∈ (T.rim j).support :=
        T.leftToAttach_support_subset_rim j hzLeftArm
      rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
          (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1) with
        hzRightArm | hzRest
      · have hzLeft : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left (fun h => hij h.symm)
            hzLeftArm (T.rightToAttach_support_subset_rim i hzRightArm)
        exact T.left_not_mem_rightToAttach i
          (by simpa [hzLeft] using hzRightArm)
      · rcases hzRest with hzLeg | hzSegment
        · have hzAttach : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i j z hzLeg hzRimJ
          exact T.attach_not_mem_rim_of_ne hij
            (by simpa [hzAttach] using hzRimJ)
        · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
              T hij hik hjk hi hj hij_order hjk_order hpath_contacts
              hzSegment (T.rim_mem_vertexSet hzRimJ) with hzi | hzj
          · exact T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzi] using hzRimJ)
          · exact hzMiddle.2.2 hzj
  have hone_two :
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge 1))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            hleg_j_nil hi hj hk
            hij_order hjk_order bridge 2)) := by
    rw [Set.disjoint_left]
    intro z hzMiddle hzOuter
    rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzMiddle.1 with hzBridge | hzLeftArm
    · exact hzMiddle.2.1 (hbridge_two z hzBridge
        (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1))
    · have hzRimJ : z ∈ (T.rim j).support :=
        T.leftToAttach_support_subset_rim j hzLeftArm
      rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
          (by simpa [Tripod.allNilCleanBridgeRim] using hzOuter.1) with
        hzRightArm | hzRest
      · have hzLeft : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left hjk hzLeftArm
            (T.rightToAttach_support_subset_rim k hzRightArm)
        exact T.left_not_mem_rightToAttach k
          (by simpa [hzLeft] using hzRightArm)
      · rcases hzRest with hzLeg | hzSegmentRev
        · have hzAttach : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k j z hzLeg hzRimJ
          exact T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
            (by simpa [hzAttach] using hzRimJ)
        · have hzSegment : z ∈
              (P.pathSegmentBetween hj hk
                (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
              T hij hik hjk hj hk hij_order hjk_order hpath_contacts
              hzSegment (T.rim_mem_vertexSet hzRimJ) with hzj | hzk
          · exact hzMiddle.2.2 hzj
          · exact T.boundary_not_mem_rim_of_ne_index
              (i := k) (s := j) (fun h => hjk h.symm)
              (by simpa [hzk] using hzRimJ)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact hone_zero.symm
  · simpa [Tripod.allNilCleanBridgeRim] using
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts
  · exact hone_zero
  · exact False.elim (hrs rfl)
  · exact hone_two
  · simpa [Tripod.allNilCleanBridgeRim] using
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts).symm
  · exact hone_two.symm
  · exact False.elim (hrs rfl)

/-- Every clean-bridge boundary leg meets every rebuilt rim only at its own
selected attachment. -/
theorem Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
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
    {a : V} (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_q : forall z : V, z ∈ bridge.support ->
      z ∈ q.support -> z = T.left) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
          hleg_i_nil hleg_k_nil hi hk q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge s).support ->
      z = GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k r := by
  intro r s z hzLeg hzRim
  fin_cases r <;> fin_cases s
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 0 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzRim with hzBridge | hzArm
    · exact False.elim ((hbridge_outside z hzBridge).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail))
    · have hzi : z = T.boundary i :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzArm))
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 2 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
        (by simpa [Tripod.allNilCleanBridgeRim] using hzRim) with
      hzArm | hzRest
    · have hzLeft := hq_clean z (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzArm))
      exact False.elim (T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzArm))
    · rcases hzRest with hzOldLeg | hzSegment
      · have hzLeft := hq_clean z (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
            (T.leg_mem_vertexSet hzOldLeg)
        exact False.elim (T.left_not_mem_leg i (by simpa [hzLeft] using hzOldLeg))
      · exact False.elim ((hq_outside z (by
          simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)).2
            (P.pathSegmentBetween_support_subset_pathSet hi hj
              (Nat.le_of_lt hij_order) z hzSegment))
  · rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzRim with hzBridge | hzArm
    · exact hbridge_q z hzBridge
        (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
    · exact hq_clean z (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
        (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim j hzArm))
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
        (by simpa [Tripod.allNilCleanBridgeRim] using hzRim) with
      hzArm | hzRest
    · have hzLeft := hq_clean z (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim k hzArm))
      exact False.elim (T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzArm))
    · rcases hzRest with hzOldLeg | hzSegmentRev
      · have hzLeft := hq_clean z (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
            (T.leg_mem_vertexSet hzOldLeg)
        exact False.elim (T.left_not_mem_leg k (by simpa [hzLeft] using hzOldLeg))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact False.elim ((hq_outside z (by
          simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)).2
            (P.pathSegmentBetween_support_subset_pathSet hj hk
              (Nat.le_of_lt hjk_order) z hzSegment))
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 0 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzRim with hzBridge | hzArm
    · exact False.elim ((hbridge_outside z hzBridge).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail))
    · have hzk : z = T.boundary k :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzArm))
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 2 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)

/-- Variant of `allNilCleanBridgeLegs_meet_rims_only_at_attach` in which the
middle boundary leg is assumed clean only against the three rebuilt rims.
This is the exact interface needed when the middle leg begins with an old rim
arm before following a clean outside tail. -/
theorem Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach_of_middle_rim_clean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
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
    {a : V} (q : S.graph.Walk T.left a)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hq_rim_clean : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge s).support ->
      z = T.left) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
          hleg_i_nil hleg_k_nil hi hk q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          hleg_j_nil hi hj hk
          hij_order hjk_order bridge s).support ->
      z = GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k r := by
  intro r s z hzLeg hzRim
  fin_cases r <;> fin_cases s
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 0 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzRim with hzBridge | hzArm
    · exact False.elim ((hbridge_outside z hzBridge).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail))
    · have hzi : z = T.boundary i :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzArm))
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 2 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)
  · exact hq_rim_clean 0 z
      (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg) hzRim
  · exact hq_rim_clean 1 z
      (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg) hzRim
  · exact hq_rim_clean 2 z
      (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg) hzRim
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 0 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order bridge hzRim with hzBridge | hzArm
    · exact False.elim ((hbridge_outside z hzBridge).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail))
    · have hzk : z = T.boundary k :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzArm))
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts 2 z
      (by simpa [Tripod.allNilCleanBridgeLeg,
        Tripod.outerNilMiddleNonNilCommonLeftLeg,
        SimpleGraph.Walk.support_copy] using hzLeg)
      (by simpa [Tripod.allNilCleanBridgeRim] using hzRim)

/-- Clean-bridge all-nil lift with a middle boundary leg that is clean only
against the rebuilt rims. -/
theorem Tripod.liftAllNilOfCleanRightToLeftBridgeOfMiddleRimClean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    {a : V} (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left)
    (hq_rim_clean : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          (hlegs_nil j)
          hi hj hk hij_order hjk_order bridge s).support ->
      z = T.left) :
    Nonempty S.Tripod := by
  refine ⟨{
    left := T.right
    right := T.boundary j
    left_ne_right := T.right_ne_boundary j
    rim := GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
      (hlegs_nil j)
      hi hj hk hij_order hjk_order bridge
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeRim_isPath P T hgraph
        hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts bridge
        hbridge_path hbridge_clean
    attach := GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeAttach_mem_rim P T hgraph
        hij hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order bridge
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
      (hlegs_nil i) (hlegs_nil k) hi hk q
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLeg_isPath P T
        (hlegs_nil i) (hlegs_nil k) hi hk q hq_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts bridge
        hbridge_outside hbridge_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order q hq_outside
    legs_meet_rims_only_at_attach :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach_of_middle_rim_clean
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts q bridge
        hbridge_outside hq_rim_clean
  }⟩

/-- The fourth-route construction for an all-collapsed residual on an outer
left arm.  The old left-arm prefix is absorbed into the middle boundary leg;
a clean right-to-left bridge supplies the missing middle rim. -/
theorem Tripod.liftAllNilOfOuterLeftArmResidualAndCleanBridge
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
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left)
    (hbridge_q : forall z : V, z ∈ bridge.support ->
      z ∈ (T.leftArmPrefixTail
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
        hx_arm q).support -> z = T.left) :
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
  have hqLeft_outside : forall z : V,
      z ∈ qLeft.support -> z ∈ P.outside := by
    simpa [qLeft, hgraph] using
      GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach q hq_outside
  have hqLeft_middle_arm : forall z : V,
      z ∈ qLeft.support -> z ∈ (T.leftToAttach j).support ->
        z = T.left := by
    simpa [qLeft] using qLeftData.inter_distinct_leftToAttach_eq_left hrj
  have hqLeft_outer_avoid : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False := by
    simpa [qLeft] using
      GMIX24SourceProof.Tripod.leftArmPrefixTail_avoids_outerNilMiddleNonNilCommonLeftRims
        P T hgraph hi hj hk
        hij_order hjk_order hx_arm hx_ne_attach hx_internal q hq_clean
        hqLeft_outside
  have hqLeft_rim_clean : forall s : Fin 3, forall z : V,
      z ∈ qLeft.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
          (hlegs_nil j)
          hi hj hk hij_order hjk_order bridge s).support ->
      z = T.left := by
    intro s z hzq hzRim
    fin_cases s
    · exact False.elim (hqLeft_outer_avoid 0 z hzq (by
        simpa [Tripod.allNilCleanBridgeRim] using hzRim))
    · rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
          P T hgraph (hlegs_nil j)
          hi hj hk hij_order hjk_order bridge hzRim with hzBridge | hzArm
      · exact hbridge_q z hzBridge (by simpa [qLeft] using hzq)
      · exact hqLeft_middle_arm z hzq hzArm
    · exact False.elim (hqLeft_outer_avoid 2 z hzq (by
        simpa [Tripod.allNilCleanBridgeRim] using hzRim))
  exact
    GMIX24SourceProof.Tripod.liftAllNilOfCleanRightToLeftBridgeOfMiddleRimClean
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts qLeft ha hqLeft_path hqLeft_outside bridge
      hbridge_path hbridge_outside hbridge_clean hqLeft_rim_clean

/-- The direct ambient tripod suppressed by the final common-end sentence of
GM IX `(2.4)`.

The old three attachment paths have collapsed to ordered vertices of the cut
path.  A carrier-clean right-to-left bridge in the caught component supplies
the third rebuilt rim, and a carrier-clean left escape supplies its boundary
leg.  The two extreme cut-path tails supply the other two boundary legs. -/
theorem Tripod.liftAllNilOfCleanRightToLeftBridge
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    {a : V} (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left)
    (hbridge_q : forall z : V, z ∈ bridge.support ->
      z ∈ q.support -> z = T.left) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfCleanRightToLeftBridgeOfMiddleRimClean
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q ha hq_path hq_outside bridge hbridge_path
      hbridge_outside hbridge_clean
  intro s z hzq hzRim
  simpa [Tripod.allNilCleanBridgeLeg, Tripod.allNilCleanBridgeAttach] using
    (GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts q hq_outside hq_clean
      bridge hbridge_outside hbridge_q 1 s z
      (by simpa [Tripod.allNilCleanBridgeLeg] using hzq) hzRim)

/-- Right-end symmetric form of the clean common-end bridge constructor. -/
theorem Tripod.liftAllNilOfCleanLeftToRightBridge
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    {a : V} (q : S.graph.Walk T.right a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.right)
    (bridge : S.graph.Walk T.left T.right)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V, z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.left ∨ z = T.right)
    (hbridge_q : forall z : V, z ∈ bridge.support ->
      z ∈ q.support -> z = T.right) :
    Nonempty S.Tripod := by
  let U : H.Tripod := T.flip
  have hlegsU : forall r : Fin 3, (U.leg r).Nil := by
    simpa [U] using T.legsNil_flip hlegs_nil
  have hcontactsU : forall z : V,
      z ∈ P.pathSet -> z ∈ U.vertexSet ->
        Exists fun m : Fin 3 => z = U.boundary m := by
    simpa [U] using T.pathContacts_flip hpath_contacts
  exact GMIX24SourceProof.Tripod.liftAllNilOfCleanRightToLeftBridge
    P U hgraph hij hik hjk hlegsU
    (by simpa [U] using hi) (by simpa [U] using hj)
    (by simpa [U] using hk) (by simpa [U] using hij_order)
    (by simpa [U] using hjk_order) hcontactsU q ha hq_path hq_outside
    (by
      intro z hzq hzU
      exact hq_clean z hzq (by simpa [U] using hzU))
    bridge hbridge_path hbridge_outside
    (by
      intro z hzBridge hzU
      rcases hbridge_clean z hzBridge (by simpa [U] using hzU) with
        hzLeft | hzRight
      · exact Or.inl (by simpa [U] using hzLeft)
      · exact Or.inr (by simpa [U] using hzRight))
    (by
      intro z hzBridge hzq
      simpa [U] using hbridge_q z hzBridge hzq)

/-- Source-path form of `liftAllNilOfCleanRightToLeftBridge`.

Split one simple caught-component escape from the old right end at its last
old-carrier contact `T.left`.  Its prefix is the clean right-to-left bridge,
its suffix is the clean left-to-boundary leg, and path simplicity gives their
exact intersection at the split vertex. -/
theorem Tripod.liftAllNilOfRightEscapeThroughCleanLeft
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    {a : V} (raw : S.graph.Walk T.right a)
    (ha : a ∈ P.leftBoundaryArc)
    (hraw_path : raw.IsPath)
    (hraw_outside : forall z : V, z ∈ raw.support -> z ∈ P.outside)
    (hleft : T.left ∈ raw.support)
    (hprefix_clean : forall z : V,
      z ∈ (raw.takeUntil T.left hleft).support ->
        z ∈ T.vertexSet -> z = T.right ∨ z = T.left)
    (hsuffix_clean : forall z : V,
      z ∈ (raw.dropUntil T.left hleft).support ->
        z ∈ T.vertexSet -> z = T.left) :
    Nonempty S.Tripod := by
  let bridge : S.graph.Walk T.right T.left := raw.takeUntil T.left hleft
  let q : S.graph.Walk T.left a := raw.dropUntil T.left hleft
  have hbridge_path : bridge.IsPath := by
    simpa [bridge] using hraw_path.takeUntil hleft
  have hq_path : q.IsPath := by
    simpa [q] using hraw_path.dropUntil hleft
  have hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside := by
    intro z hz
    exact hraw_outside z
      (SimpleGraph.Walk.support_takeUntil_subset raw hleft
        (by simpa [bridge] using hz))
  have hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside := by
    intro z hz
    exact hraw_outside z
      (SimpleGraph.Walk.support_dropUntil_subset raw hleft
        (by simpa [q] using hz))
  have hbridge_q : forall z : V,
      z ∈ bridge.support -> z ∈ q.support -> z = T.left := by
    intro z hzBridge hzq
    exact Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hraw_path hleft (by simpa [bridge] using hzBridge)
        (by simpa [q] using hzq)
  exact GMIX24SourceProof.Tripod.liftAllNilOfCleanRightToLeftBridge
    P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
    hpath_contacts q ha hq_path hq_outside
    (by simpa [q] using hsuffix_clean) bridge hbridge_path hbridge_outside
    (by simpa [bridge] using hprefix_clean) hbridge_q


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
