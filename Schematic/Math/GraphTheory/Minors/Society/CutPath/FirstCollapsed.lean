import Schematic.Math.GraphTheory.Minors.Society.CutPath.CommonEndpoint

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Attachments for the first-collapsed-leg residual constructor.

The new rim endpoints are the second and third ordered old attachments.  The
leg-segment rim is attached at the third old foot, and the two old common ends
are the attachments on the left and right old-rim routes. -/
def firstNilResidualAttach {S : GeneralSociety V}
    (T : S.Tripod) (k : Fin 3) : Fin 3 -> V
  | 0 => T.boundary k
  | 1 => T.left
  | 2 => T.right

/-- Rims for the first-collapsed-leg residual constructor. -/
def firstNilResidualRim {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {j k : Fin 3}
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    Fin 3 -> S.graph.Walk (T.attach j) (T.attach k)
  | 0 =>
      T.liftAttachToAttachViaLegSegment hgraph j k
        (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order))
  | 1 => (T.attachToAttachViaLeft j k).mapLe hgraph
  | 2 => (T.attachToAttachViaRight j k).mapLe hgraph

/-- Legs for the first-collapsed-leg residual constructor when the clean tail
starts on the old left arm of the collapsed first branch. -/
def firstNilResidualLeftArmLeg {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i k : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk (T.firstNilResidualAttach k r)
        (P.boundaryTripleReverseEnds a r)
  | 0 => P.pathTailToEnd hk
  | 1 => q
  | 2 => T.rightToBoundaryViaLegTail hgraph i (P.pathTailToStart hi)

/-- Core ambient tripod for the first ordered collapsed-leg residual.

This is the direct source construction for the subcase where the clean path
from the side tripod starts on the old left arm of the first ordered branch.
The large disjointness checks are exposed as hypotheses so they can be proved
locally without rebuilding the record. -/
def liftFirstNilResidualLeftArmCore {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hrim_disjoint :
      forall r s : Fin 3, r ≠ s ->
        Disjoint
          (Walk.InternalVertices
            (T.firstNilResidualRim P hgraph hj hk hjk_order r))
          (Walk.InternalVertices
            (T.firstNilResidualRim P hgraph hj hk hjk_order s)))
    (hlegs_disjoint :
      forall r s : Fin 3, r ≠ s ->
        Disjoint
          {z : V | z ∈
            (T.firstNilResidualLeftArmLeg P hgraph hi hk q r).support}
          {z : V | z ∈
            (T.firstNilResidualLeftArmLeg P hgraph hi hk q s).support})
    (hlegs_meet_rims :
      forall r s : Fin 3, forall z : V,
        z ∈ (T.firstNilResidualLeftArmLeg P hgraph hi hk q r).support ->
          z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
            z = T.firstNilResidualAttach k r) :
    S.Tripod where
  left := T.attach j
  right := T.attach k
  left_ne_right := T.attach_ne_of_ne hjk
  rim := T.firstNilResidualRim P hgraph hj hk hjk_order
  rim_isPath := by
    intro r
    fin_cases r
    ·
      have hmiddle_clean :
          forall z : V,
            z ∈ (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order)).support ->
              z ∈ T.vertexSet ->
                z = T.boundary j ∨ z = T.boundary k := by
        intro z hz hzT
        exact
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts hz hzT
      simpa [Tripod.firstNilResidualRim] using
        T.liftAttachToAttachViaLegSegment_isPath hgraph hjk
          (P.pathSegmentBetween_isPath hj hk (Nat.le_of_lt hjk_order))
          hmiddle_clean
    ·
      simpa [Tripod.firstNilResidualRim] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          (T.attachToAttachViaLeft_isPath hjk)
    ·
      simpa [Tripod.firstNilResidualRim] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          (T.attachToAttachViaRight_isPath hjk)
  attach := T.firstNilResidualAttach k
  attach_mem_rim := by
    intro r
    fin_cases r
    ·
      have hbk_ne_aj : T.boundary k ≠ T.attach j := by
        intro h
        exact
          T.boundary_not_mem_rim_of_ne_index (fun hkj => hjk hkj.symm)
            (by simpa [h] using (T.attach_mem_rim j).1)
      have hbk_ne_ak : T.boundary k ≠ T.attach k := by
        intro h
        exact hleg_k_not_nil
          ((T.boundary_eq_attach_iff_leg_nil k).mp h)
      simpa [Tripod.firstNilResidualRim, Tripod.firstNilResidualAttach]
        using
          T.boundary_right_mem_internal_liftAttachToAttachViaLegSegment
            hgraph
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order))
            hbk_ne_aj hbk_ne_ak
    ·
      simpa [Tripod.firstNilResidualRim, Tripod.firstNilResidualAttach,
        Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.left_mem_internal_attachToAttachViaLeft j k
    ·
      simpa [Tripod.firstNilResidualRim, Tripod.firstNilResidualAttach,
        Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.right_mem_internal_attachToAttachViaRight j k
  boundary := P.boundaryTripleReverseEnds a
  boundary_mem := P.boundaryTripleReverseEnds_mem_of_leftArc ha
  boundary_injective := P.boundaryTripleReverseEnds_injective_of_leftArc ha
  leg := T.firstNilResidualLeftArmLeg P hgraph hi hk q
  leg_isPath := by
    intro r
    fin_cases r
    · simpa [Tripod.firstNilResidualLeftArmLeg] using P.pathTailToEnd_isPath hk
    · simpa [Tripod.firstNilResidualLeftArmLeg] using hq_path
    ·
      have htail_clean :
          forall z : V, z ∈ (P.pathTailToStart hi).support ->
            z ∈ T.vertexSet -> z = T.boundary i := by
        intro z hz hzT
        exact
          P.pathTailToStart_clean_first_foot_of_path_contacts
            T hij hik hjk hi hij_order hjk_order hpath_contacts hz hzT
      simpa [Tripod.firstNilResidualLeftArmLeg] using
        T.rightToBoundaryViaLegTail_isPath hgraph i
          (P.pathTailToStart hi) (P.pathTailToStart_isPath hi) htail_clean
  rim_internals_disjoint := hrim_disjoint
  legs_pairwise_disjoint := hlegs_disjoint
  legs_meet_rims_only_at_attach := hlegs_meet_rims

/-- Internal disjointness of the three rims in the first-collapsed-leg
residual constructor. -/
theorem firstNilResidualRims_internal_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order r))
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order s)) := by
  have hmiddle_clean :
      forall z : V,
        z ∈ (P.pathSegmentBetween hj hk
          (Nat.le_of_lt hjk_order)).support ->
        z ∈ T.vertexSet ->
          z = T.boundary j ∨ z = T.boundary k := by
    intro z hz hzT
    exact
      P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
        T hij hik hjk hj hk hij_order hjk_order hpath_contacts hz hzT
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  ·
    simpa [Tripod.firstNilResidualRim] using
      T.liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean
        hgraph hjk hmiddle_clean
  ·
    simpa [Tripod.firstNilResidualRim] using
      T.liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean
        hgraph hjk hmiddle_clean
  ·
    simpa [Tripod.firstNilResidualRim] using
      (T.liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean
        hgraph hjk hmiddle_clean).symm
  · exact False.elim (hrs rfl)
  ·
    simpa [Tripod.firstNilResidualRim, Tripod.commonLeftEndpointRim] using
      T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hjk hj hk hjk_order
  ·
    simpa [Tripod.firstNilResidualRim] using
      (T.liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean
        hgraph hjk hmiddle_clean).symm
  ·
    simpa [Tripod.firstNilResidualRim, Tripod.commonLeftEndpointRim] using
      (T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hjk hj hk hjk_order).symm
  · exact False.elim (hrs rfl)

/-- Internal disjointness of the first-collapsed residual rims when only the
last ordered old leg is known to be nontrivial.

This is the exact degenerate form needed by the source common-end proof: the
first collapsed ordered branch has already been discarded, and the middle old
leg may also have collapsed to its attachment.  The leg-segment rim still has a
nontrivial right endpoint, so the middle-foot collapse is handled as an
endpoint exclusion. -/
theorem firstNilResidualRims_internal_disjoint_last_not_nil
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order r))
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order s)) := by
  have hmiddle_clean :
      forall z : V,
        z ∈ (P.pathSegmentBetween hj hk
          (Nat.le_of_lt hjk_order)).support ->
        z ∈ T.vertexSet ->
          z = T.boundary j ∨ z = T.boundary k := by
    intro z hz hzT
    exact
      P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
        T hij hik hjk hj hk hij_order hjk_order hpath_contacts hz hzT
  have hleft :
      Disjoint
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order 0))
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order 1)) := by
    simpa [Tripod.firstNilResidualRim] using
      T.liftAttachToAttachViaLegSegment_left_rim_internal_disjoint_of_middle_clean_right_non_nil
        hgraph hjk hmiddle_clean
  have hright :
      Disjoint
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order 0))
        (Walk.InternalVertices
          (T.firstNilResidualRim P hgraph hj hk hjk_order 2)) := by
    simpa [Tripod.firstNilResidualRim] using
      T.liftAttachToAttachViaLegSegment_right_rim_internal_disjoint_of_middle_clean_right_non_nil
        hgraph hjk hmiddle_clean
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact hleft
  · exact hright
  · exact hleft.symm
  · exact False.elim (hrs rfl)
  ·
    simpa [Tripod.firstNilResidualRim, Tripod.commonLeftEndpointRim] using
      T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hjk hj hk hjk_order
  · exact hright.symm
  ·
    simpa [Tripod.firstNilResidualRim, Tripod.commonLeftEndpointRim] using
      (T.commonLeftEndpoint_left_right_rims_internal_disjoint
        P hgraph hjk hj hk hjk_order).symm
  · exact False.elim (hrs rfl)

/-- Pairwise disjointness of the residual legs in the first-collapsed ordered
branch, in the subcase where the clean outside tail leaves the old left arm.

This is the leg-disjointness half of the direct source construction for the
paragraph `Q, P_1, P_2, P_3 have a common end`: after the first ordered branch
has collapsed, the forward cut-path tail from the last foot, the old-left-arm
prefix plus clean tail, and the old-right branch followed by the backward
cut-path tail are mutually disjoint. -/
theorem firstNilResidualLeftArmPrefixTail_legs_pairwise_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (q : S.graph.Walk x a)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (T.firstNilResidualLeftArmLeg P hgraph hi hk
            (T.leftArmPrefixTail hgraph hx_arm q) r).support}
        {z : V | z ∈
          (T.firstNilResidualLeftArmLeg P hgraph hi hk
            (T.leftArmPrefixTail hgraph hx_arm q) s).support} := by
  classical
  have hki : k ≠ i := fun h => hik h.symm
  have h0q :
      Disjoint
        {z : V | z ∈ (P.pathTailToEnd hk).support}
        {z : V | z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support} := by
    rw [Set.disjoint_left]
    intro z hz0 hzqLeft
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet hk z hz0
    have hzCases :
        z ∈
            (((T.leftToAttach i).takeUntil x hx_arm).mapLe hgraph).support ∨
          z ∈ q.support := by
      simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
        using hzqLeft
    rcases hzCases with hzPrefixMap | hzq
    · have hzPrefix :
          z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
      exact (hprefix_outside z hzPrefix).2
        (by simpa [GMIX24CutPath.pathSet] using hzPath)
    · exact (hq_outside z hzq).2
        (by simpa [GMIX24CutPath.pathSet] using hzPath)
  have h02 :
      Disjoint
        {z : V | z ∈ (P.pathTailToEnd hk).support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph i
            (P.pathTailToStart hi)).support} := by
    rw [Set.disjoint_left]
    intro z hz0 hz2
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hz2
      with hzArm | hzRest
    · have hzRim : z ∈ (T.rim i).support :=
        T.rightToAttach_support_subset_rim i hzArm
      have hz0_clean :
          z = T.boundary k :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hz0
          (T.rim_mem_vertexSet (i := i) hzRim)
      exact T.boundary_not_mem_rim_of_ne_index hki
        (by simpa [hz0_clean] using hzRim)
    · rcases hzRest with hzLeg | hzTail
      · have hz0_clean :
            z = T.boundary k :=
          P.pathTailToEnd_clean_last_foot_of_path_contacts
            T hij hik hjk hk hij_order hjk_order hpath_contacts hz0
            (T.leg_mem_vertexSet (i := i) hzLeg)
        exact
          T.boundary_not_mem_leg_of_ne (i := i) (j := k) hik
            (by simpa [hz0_clean] using hzLeg)
      · exact
          Set.disjoint_left.mp
            (P.pathTailToStart_support_disjoint_pathTailToEnd
              hi hk (lt_trans hij_order hjk_order)).symm
            hz0 hzTail
  have hq2 :
      Disjoint
        {z : V | z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph i
            (P.pathTailToStart hi)).support} := by
    rw [Set.disjoint_left]
    intro z hzqLeft hz2
    have hzLeftCases :
        z ∈
            (((T.leftToAttach i).takeUntil x hx_arm).mapLe hgraph).support ∨
          z ∈ q.support := by
      simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
        using hzqLeft
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hz2
      with hzArm | hzRest
    · rcases hzLeftCases with hzPrefixMap | hzq
      · have hzPrefix :
            z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support := by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
        exact
          Set.disjoint_left.mp
            (T.leftToAttach_takeUntil_support_disjoint_rightToAttach
              hx_arm hx_ne_attach)
            hzPrefix hzArm
      · have hzRim : z ∈ (T.rim i).support :=
          T.rightToAttach_support_subset_rim i hzArm
        have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := i) hzRim)
        have hx_attach : x = T.attach i :=
          T.leftToAttach_support_inter_rightToAttach_eq_attach i
            hx_arm (by simpa [hzx] using hzArm)
        exact hx_ne_attach hx_attach
    · rcases hzRest with hzLeg | hzTail
      · rcases hzLeftCases with hzPrefixMap | hzq
        · have hzPrefix :
              z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support := by
            simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
          exact
            Set.disjoint_left.mp
              (T.leftToAttach_takeUntil_support_disjoint_leg
                hx_arm hx_ne_attach)
              hzPrefix hzLeg
        · have hzx : z = x :=
            hq_clean z hzq (T.leg_mem_vertexSet (i := i) hzLeg)
          exact hx_not_leg i (by simpa [hzx] using hzLeg)
      · have hzPath : z ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet hi z hzTail
        rcases hzLeftCases with hzPrefixMap | hzq
        · have hzPrefix :
              z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support := by
            simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
          exact (hprefix_outside z hzPrefix).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath)
        · exact (hq_outside z hzq).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h0q
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h02
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h0q.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.firstNilResidualLeftArmLeg] using hq2
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h02.symm
  · simpa [Tripod.firstNilResidualLeftArmLeg] using hq2.symm
  · exact False.elim (hrs rfl)

/-- Pairwise disjointness of the residual legs in the first-collapsed ordered
branch when the clean outside tail starts at the old left common end.

This is the endpoint form of the same source construction as
`firstNilResidualLeftArmPrefixTail_legs_pairwise_disjoint`: the collapsed first
branch contributes no left-arm prefix, so the three legs are the forward cut-path
tail, the clean tail from the common end, and the old-right branch followed by
the backward cut-path tail. -/
theorem firstNilResidualCommonLeftTail_legs_pairwise_disjoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (T.firstNilResidualLeftArmLeg P hgraph hi hk q r).support}
        {z : V | z ∈
          (T.firstNilResidualLeftArmLeg P hgraph hi hk q s).support} := by
  classical
  have hki : k ≠ i := fun h => hik h.symm
  have h0q :
      Disjoint
        {z : V | z ∈ (P.pathTailToEnd hk).support}
        {z : V | z ∈ q.support} := by
    rw [Set.disjoint_left]
    intro z hz0 hzq
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet hk z hz0
    exact (hq_outside z hzq).2
      (by simpa [GMIX24CutPath.pathSet] using hzPath)
  have h02 :
      Disjoint
        {z : V | z ∈ (P.pathTailToEnd hk).support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph i
            (P.pathTailToStart hi)).support} := by
    rw [Set.disjoint_left]
    intro z hz0 hz2
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hz2
      with hzArm | hzRest
    · have hzRim : z ∈ (T.rim i).support :=
        T.rightToAttach_support_subset_rim i hzArm
      have hz0_clean :
          z = T.boundary k :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hz0
          (T.rim_mem_vertexSet (i := i) hzRim)
      exact T.boundary_not_mem_rim_of_ne_index hki
        (by simpa [hz0_clean] using hzRim)
    · rcases hzRest with hzLeg | hzTail
      · have hz0_clean :
            z = T.boundary k :=
          P.pathTailToEnd_clean_last_foot_of_path_contacts
            T hij hik hjk hk hij_order hjk_order hpath_contacts hz0
            (T.leg_mem_vertexSet (i := i) hzLeg)
        exact
          T.boundary_not_mem_leg_of_ne (i := i) (j := k) hik
            (by simpa [hz0_clean] using hzLeg)
      · exact
          Set.disjoint_left.mp
            (P.pathTailToStart_support_disjoint_pathTailToEnd
              hi hk (lt_trans hij_order hjk_order)).symm
            hz0 hzTail
  have hq2 :
      Disjoint
        {z : V | z ∈ q.support}
        {z : V | z ∈
          (T.rightToBoundaryViaLegTail hgraph i
            (P.pathTailToStart hi)).support} := by
    rw [Set.disjoint_left]
    intro z hzq hz2
    rcases
        T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hz2
      with hzArm | hzRest
    · have hzRim : z ∈ (T.rim i).support :=
        T.rightToAttach_support_subset_rim i hzArm
      have hzLeft : z = T.left :=
        hq_clean z hzq (T.rim_mem_vertexSet (i := i) hzRim)
      exact T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzArm)
    · rcases hzRest with hzLeg | hzTail
      · have hzLeft : z = T.left :=
          hq_clean z hzq (T.leg_mem_vertexSet (i := i) hzLeg)
        exact T.left_not_mem_leg i (by simpa [hzLeft] using hzLeg)
      · have hzPath : z ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet hi z hzTail
        exact (hq_outside z hzq).2
          (by simpa [GMIX24CutPath.pathSet] using hzPath)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h0q
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h02
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h0q.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.firstNilResidualLeftArmLeg] using hq2
  · simpa [Tripod.firstNilResidualLeftArmLeg] using h02.symm
  · simpa [Tripod.firstNilResidualLeftArmLeg] using hq2.symm
  · exact False.elim (hrs rfl)

/-- The forward cut-path tail used as leg `0` of the first-collapsed residual
meets each rebuilt rim only at the last ordered old foot. -/
theorem firstNilResidualLeg_zero_meets_rims
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈ (P.pathTailToEnd hk).support ->
        z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
          z = T.firstNilResidualAttach k 0 := by
  intro s z hzLeg hzRim
  have hclean_end :
      forall {w : V}, w ∈ (P.pathTailToEnd hk).support ->
        w ∈ T.vertexSet -> w = T.boundary k := by
    intro w hw hwT
    exact
      P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hw hwT
  fin_cases s
  ·
    have hzRim0 :
        z ∈
          (T.liftAttachToAttachViaLegSegment hgraph j k
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order))).support := by
      simpa [Tripod.firstNilResidualRim] using hzRim
    rcases
        T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
      with hzOldJ | hzRest
    · simpa [Tripod.firstNilResidualAttach] using
        hclean_end hzLeg (T.leg_mem_vertexSet (i := j) hzOldJ)
    · rcases hzRest with hzMid | hzOldK
      · have hzMidSegment :
            z ∈
              (Walk.segmentBetween P.path
                (by simpa [GMIX24CutPath.pathSet] using hj)
                (by simpa [GMIX24CutPath.pathSet] using hk)
                (Nat.le_of_lt hjk_order)).support := by
          simpa [GMIX24CutPath.pathSegmentBetween] using hzMid
        simpa [Tripod.firstNilResidualAttach] using
          P.segmentBetween_support_inter_pathTailToEnd_subset_right
            hj hk (Nat.le_of_lt hjk_order) hzMidSegment hzLeg
      · simpa [Tripod.firstNilResidualAttach] using
          hclean_end hzLeg (T.leg_mem_vertexSet (i := k) hzOldK)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaLeft j k).support := by
      simpa [Tripod.firstNilResidualRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
    · simpa [Tripod.firstNilResidualAttach] using
        hclean_end hzLeg (T.rim_mem_vertexSet (i := j) hzj)
    · simpa [Tripod.firstNilResidualAttach] using
        hclean_end hzLeg (T.rim_mem_vertexSet (i := k) hzk)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaRight j k).support := by
      simpa [Tripod.firstNilResidualRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
    · simpa [Tripod.firstNilResidualAttach] using
        hclean_end hzLeg (T.rim_mem_vertexSet (i := j) hzj)
    · simpa [Tripod.firstNilResidualAttach] using
        hclean_end hzLeg (T.rim_mem_vertexSet (i := k) hzk)

/-- The old-left-arm prefix plus clean outside tail used as leg `1` of the
first-collapsed residual meets each rebuilt rim only at the old left common
end. -/
theorem firstNilResidualLeftArmPrefixTail_meets_rims_only_at_left
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (q : S.graph.Walk x a)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support) :
    forall s : Fin 3, forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
        z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
          z = T.firstNilResidualAttach k 1 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  have hki : k ≠ i := fun h => hik h.symm
  have hx_not_rim_j : x ∉ (T.rim j).support := by
    intro hxj
    rcases T.rim_support_internal_or_endpoint hxj with hxjInt | hxjEnd
    · exact
        Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hx_internal hxjInt
    · rcases hxjEnd with hxLeft | hxRight
      · exact hx_internal.2.1 hxLeft
      · exact hx_internal.2.2 hxRight
  have hx_not_rim_k : x ∉ (T.rim k).support := by
    intro hxk
    rcases T.rim_support_internal_or_endpoint hxk with hxkInt | hxkEnd
    · exact
        Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          hx_internal hxkInt
    · rcases hxkEnd with hxLeft | hxRight
      · exact hx_internal.2.1 hxLeft
      · exact hx_internal.2.2 hxRight
  intro s z hzLeg hzRim
  have hzCases :
      z ∈
          (((T.leftToAttach i).takeUntil x hx_arm).mapLe hgraph).support ∨
        z ∈ q.support := by
    simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
      using hzLeg
  rcases hzCases with hzPrefixMap | hzq
  · have hzPrefix :
        z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
    have hzPrefixRimI : z ∈ (T.rim i).support :=
      T.leftToAttach_support_subset_rim i
        (SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i)
          hx_arm hzPrefix)
    fin_cases s
    ·
      have hzRim0 :
          z ∈
            (T.liftAttachToAttachViaLegSegment hgraph j k
              (P.pathSegmentBetween hj hk
                (Nat.le_of_lt hjk_order))).support := by
        simpa [Tripod.firstNilResidualRim] using hzRim
      rcases
          T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
        with hzOldJ | hzRest
      · have hzAttachJ : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j i z hzOldJ hzPrefixRimI
        exact False.elim
          (T.attach_not_mem_rim_of_ne hji
            (by simpa [hzAttachJ] using hzPrefixRimI))
      · rcases hzRest with hzMid | hzOldK
        · have hzPath : z ∈ P.pathSet :=
            P.pathSegmentBetween_support_subset_pathSet
              hj hk (Nat.le_of_lt hjk_order) z hzMid
          exact False.elim
            ((hprefix_outside z hzPrefix).2
              (by simpa [GMIX24CutPath.pathSet] using hzPath))
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k i z hzOldK hzPrefixRimI
          exact False.elim
            (T.attach_not_mem_rim_of_ne hki
              (by simpa [hzAttachK] using hzPrefixRimI))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaLeft j k).support := by
        simpa [Tripod.firstNilResidualRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
      · simpa [Tripod.firstNilResidualAttach] using
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hij
            hx_arm hzPrefix hzj
      · simpa [Tripod.firstNilResidualAttach] using
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hik
            hx_arm hzPrefix hzk
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaRight j k).support := by
        simpa [Tripod.firstNilResidualRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
      · simpa [Tripod.firstNilResidualAttach] using
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hij
            hx_arm hzPrefix hzj
      · simpa [Tripod.firstNilResidualAttach] using
          T.leftToAttach_takeUntil_support_inter_rim_eq_left hik
            hx_arm hzPrefix hzk
  · fin_cases s
    ·
      have hzRim0 :
          z ∈
            (T.liftAttachToAttachViaLegSegment hgraph j k
              (P.pathSegmentBetween hj hk
                (Nat.le_of_lt hjk_order))).support := by
        simpa [Tripod.firstNilResidualRim] using hzRim
      rcases
          T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
        with hzOldJ | hzRest
      · have hzx : z = x :=
          hq_clean z hzq (T.leg_mem_vertexSet (i := j) hzOldJ)
        exact False.elim (hx_not_leg j (by simpa [hzx] using hzOldJ))
      · rcases hzRest with hzMid | hzOldK
        · have hzPath : z ∈ P.pathSet :=
            P.pathSegmentBetween_support_subset_pathSet
              hj hk (Nat.le_of_lt hjk_order) z hzMid
          exact False.elim
            ((hq_outside z hzq).2
              (by simpa [GMIX24CutPath.pathSet] using hzPath))
        · have hzx : z = x :=
            hq_clean z hzq (T.leg_mem_vertexSet (i := k) hzOldK)
          exact False.elim (hx_not_leg k (by simpa [hzx] using hzOldK))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaLeft j k).support := by
        simpa [Tripod.firstNilResidualRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
        exact False.elim (hx_not_rim_j (by simpa [hzx] using hzj))
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := k) hzk)
        exact False.elim (hx_not_rim_k (by simpa [hzx] using hzk))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaRight j k).support := by
        simpa [Tripod.firstNilResidualRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
        exact False.elim (hx_not_rim_j (by simpa [hzx] using hzj))
      · have hzx : z = x :=
          hq_clean z hzq (T.rim_mem_vertexSet (i := k) hzk)
        exact False.elim (hx_not_rim_k (by simpa [hzx] using hzk))

/-- The old-right branch, followed by the backward cut-path tail from the first
ordered foot, meets each rebuilt first-collapsed residual rim only at the old
right common end. -/
theorem firstNilResidualRightBranch_meets_rims
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈
        (T.rightToBoundaryViaLegTail hgraph i
          (P.pathTailToStart hi)).support ->
      z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
        z = T.firstNilResidualAttach k 2 := by
  classical
  have hji : j ≠ i := fun h => hij h.symm
  have hki : k ≠ i := fun h => hik h.symm
  have hmiddle_clean :
      forall z : V,
        z ∈ (P.pathSegmentBetween hj hk
          (Nat.le_of_lt hjk_order)).support ->
        z ∈ T.vertexSet ->
          z = T.boundary j ∨ z = T.boundary k := by
    intro z hz hzT
    exact
      P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
        T hij hik hjk hj hk hij_order hjk_order hpath_contacts hz hzT
  have htail_clean :
      forall z : V, z ∈ (P.pathTailToStart hi).support ->
        z ∈ T.vertexSet -> z = T.boundary i := by
    intro z hz hzT
    exact
      P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hz hzT
  intro s z hzBranch hzRim
  rcases
      T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzBranch
    with hzArm | hzRest
  · have hzRimI : z ∈ (T.rim i).support :=
      T.rightToAttach_support_subset_rim i hzArm
    fin_cases s
    ·
      have hzRim0 :
          z ∈
            (T.liftAttachToAttachViaLegSegment hgraph j k
              (P.pathSegmentBetween hj hk
                (Nat.le_of_lt hjk_order))).support := by
        simpa [Tripod.firstNilResidualRim] using hzRim
      rcases
          T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
        with hzOldJ | hzRest0
      · have hzAttachJ : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j i z hzOldJ hzRimI
        exact False.elim
          (T.attach_not_mem_rim_of_ne hji
            (by simpa [hzAttachJ] using hzRimI))
      · rcases hzRest0 with hzMid | hzOldK
        · rcases hmiddle_clean z hzMid
              (T.rim_mem_vertexSet (i := i) hzRimI) with hzJ | hzK
          · exact False.elim
              (T.boundary_not_mem_rim_of_ne_index hji
                (by simpa [hzJ] using hzRimI))
          · exact False.elim
              (T.boundary_not_mem_rim_of_ne_index hki
                (by simpa [hzK] using hzRimI))
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k i z hzOldK hzRimI
          exact False.elim
            (T.attach_not_mem_rim_of_ne hki
              (by simpa [hzAttachK] using hzRimI))
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaLeft j k).support := by
        simpa [Tripod.firstNilResidualRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
      · simpa [Tripod.firstNilResidualAttach] using
          T.rightToAttach_support_inter_rim_eq_right hij hzArm hzj
      · simpa [Tripod.firstNilResidualAttach] using
          T.rightToAttach_support_inter_rim_eq_right hik hzArm hzk
    ·
      have hzOld :
          z ∈ (T.attachToAttachViaRight j k).support := by
        simpa [Tripod.firstNilResidualRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
      rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
      · simpa [Tripod.firstNilResidualAttach] using
          T.rightToAttach_support_inter_rim_eq_right hij hzArm hzj
      · simpa [Tripod.firstNilResidualAttach] using
          T.rightToAttach_support_inter_rim_eq_right hik hzArm hzk
  · rcases hzRest with hzLegI | hzTail
    · fin_cases s
      ·
        have hzRim0 :
            z ∈
              (T.liftAttachToAttachViaLegSegment hgraph j k
                (P.pathSegmentBetween hj hk
                  (Nat.le_of_lt hjk_order))).support := by
          simpa [Tripod.firstNilResidualRim] using hzRim
        rcases
            T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
          with hzOldJ | hzRest0
        · exact False.elim
            (Set.disjoint_left.mp
              (T.legs_pairwise_disjoint i j hij) hzLegI hzOldJ)
        · rcases hzRest0 with hzMid | hzOldK
          · rcases hmiddle_clean z hzMid
                (T.leg_mem_vertexSet (i := i) hzLegI) with hzJ | hzK
            · exact False.elim
                (T.boundary_not_mem_leg_of_ne (i := i) (j := j) hij
                  (by simpa [hzJ] using hzLegI))
            · exact False.elim
                (T.boundary_not_mem_leg_of_ne (i := i) (j := k) hik
                  (by simpa [hzK] using hzLegI))
          · exact False.elim
              (Set.disjoint_left.mp
                (T.legs_pairwise_disjoint i k hik) hzLegI hzOldK)
      ·
        have hzOld :
            z ∈ (T.attachToAttachViaLeft j k).support := by
          simpa [Tripod.firstNilResidualRim,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
        rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
        · have hzAttachI : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i j z hzLegI hzj
          exact False.elim
            (T.attach_not_mem_rim_of_ne hij
              (by simpa [hzAttachI] using hzj))
        · have hzAttachI : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i k z hzLegI hzk
          exact False.elim
            (T.attach_not_mem_rim_of_ne hik
              (by simpa [hzAttachI] using hzk))
      ·
        have hzOld :
            z ∈ (T.attachToAttachViaRight j k).support := by
          simpa [Tripod.firstNilResidualRim,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
        rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
        · have hzAttachI : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i j z hzLegI hzj
          exact False.elim
            (T.attach_not_mem_rim_of_ne hij
              (by simpa [hzAttachI] using hzj))
        · have hzAttachI : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i k z hzLegI hzk
          exact False.elim
            (T.attach_not_mem_rim_of_ne hik
              (by simpa [hzAttachI] using hzk))
    · fin_cases s
      ·
        have hzRim0 :
            z ∈
              (T.liftAttachToAttachViaLegSegment hgraph j k
                (P.pathSegmentBetween hj hk
                  (Nat.le_of_lt hjk_order))).support := by
          simpa [Tripod.firstNilResidualRim] using hzRim
        rcases
            T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
          with hzOldJ | hzRest0
        · have hzBoundaryI : z = T.boundary i :=
            htail_clean z hzTail (T.leg_mem_vertexSet (i := j) hzOldJ)
          exact False.elim
            (T.boundary_not_mem_leg_of_ne (i := j) (j := i) hji
              (by simpa [hzBoundaryI] using hzOldJ))
        · rcases hzRest0 with hzMid | hzOldK
          · exact False.elim
              (Set.disjoint_left.mp
                (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
                  hi hj hk hij_order (Nat.le_of_lt hjk_order))
                hzTail
                (by simpa [GMIX24CutPath.pathSegmentBetween] using hzMid))
          · have hzBoundaryI : z = T.boundary i :=
              htail_clean z hzTail (T.leg_mem_vertexSet (i := k) hzOldK)
            exact False.elim
              (T.boundary_not_mem_leg_of_ne (i := k) (j := i) hki
                (by simpa [hzBoundaryI] using hzOldK))
      ·
        have hzOld :
            z ∈ (T.attachToAttachViaLeft j k).support := by
          simpa [Tripod.firstNilResidualRim,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
        rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
        · have hzBoundaryI : z = T.boundary i :=
            htail_clean z hzTail (T.rim_mem_vertexSet (i := j) hzj)
          exact False.elim
            (T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzBoundaryI] using hzj))
        · have hzBoundaryI : z = T.boundary i :=
            htail_clean z hzTail (T.rim_mem_vertexSet (i := k) hzk)
          exact False.elim
            (T.boundary_not_mem_rim_of_ne_index hik
              (by simpa [hzBoundaryI] using hzk))
      ·
        have hzOld :
            z ∈ (T.attachToAttachViaRight j k).support := by
          simpa [Tripod.firstNilResidualRim,
            SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
        rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
        · have hzBoundaryI : z = T.boundary i :=
            htail_clean z hzTail (T.rim_mem_vertexSet (i := j) hzj)
          exact False.elim
            (T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzBoundaryI] using hzj))
        · have hzBoundaryI : z = T.boundary i :=
            htail_clean z hzTail (T.rim_mem_vertexSet (i := k) hzk)
          exact False.elim
            (T.boundary_not_mem_rim_of_ne_index hik
              (by simpa [hzBoundaryI] using hzk))

/-- Aggregate leg/rim contact statement for the first-collapsed residual
constructor with an old-left-arm clean tail. -/
theorem firstNilResidualLeftArmPrefixTail_legs_meet_rims_only_at_attach
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (q : S.graph.Walk x a)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (T.firstNilResidualLeftArmLeg P hgraph hi hk
          (T.leftArmPrefixTail hgraph hx_arm q) r).support ->
      z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
        z = T.firstNilResidualAttach k r := by
  intro r s z hzLeg hzRim
  fin_cases r
  · exact
      T.firstNilResidualLeg_zero_meets_rims
        P hgraph hij hik hjk hj hk hij_order hjk_order hpath_contacts
        s z
        (by simpa [Tripod.firstNilResidualLeftArmLeg] using hzLeg)
        hzRim
  · simpa [Tripod.firstNilResidualLeftArmLeg, Tripod.firstNilResidualAttach] using
      T.firstNilResidualLeftArmPrefixTail_meets_rims_only_at_left
        P hgraph hij hik hj hk hjk_order hx_arm
        hx_internal q hprefix_outside hq_outside hq_clean hx_not_leg s z
        (by simpa [Tripod.firstNilResidualLeftArmLeg] using hzLeg)
        hzRim
  · simpa [Tripod.firstNilResidualLeftArmLeg, Tripod.firstNilResidualAttach] using
      T.firstNilResidualRightBranch_meets_rims
        P hgraph hij hik hjk hi hj hk hij_order hjk_order hpath_contacts
        s z
        (by simpa [Tripod.firstNilResidualLeftArmLeg] using hzLeg)
        hzRim

/-- The clean outside tail from the old left common end meets each rebuilt
first-collapsed residual rim only at that common end. -/
theorem firstNilResidualCommonLeftTail_meets_rims_only_at_left
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {j k : Fin 3}
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left) :
    forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
        z = T.firstNilResidualAttach k 1 := by
  intro s z hzq hzRim
  fin_cases s
  ·
    have hzRim0 :
        z ∈
          (T.liftAttachToAttachViaLegSegment hgraph j k
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order))).support := by
      simpa [Tripod.firstNilResidualRim] using hzRim
    rcases
        T.liftAttachToAttachViaLegSegment_support_cases hgraph hzRim0
      with hzOldJ | hzRest
    · simpa [Tripod.firstNilResidualAttach] using
        hq_clean z hzq (T.leg_mem_vertexSet (i := j) hzOldJ)
    · rcases hzRest with hzMid | hzOldK
      · have hzPath : z ∈ P.pathSet :=
          P.pathSegmentBetween_support_subset_pathSet
            hj hk (Nat.le_of_lt hjk_order) z hzMid
        exact False.elim
          ((hq_outside z hzq).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath))
      · simpa [Tripod.firstNilResidualAttach] using
          hq_clean z hzq (T.leg_mem_vertexSet (i := k) hzOldK)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaLeft j k).support := by
      simpa [Tripod.firstNilResidualRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaLeft_support_cases hzOld with hzj | hzk
    · simpa [Tripod.firstNilResidualAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
    · simpa [Tripod.firstNilResidualAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := k) hzk)
  ·
    have hzOld :
        z ∈ (T.attachToAttachViaRight j k).support := by
      simpa [Tripod.firstNilResidualRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzRim
    rcases T.attachToAttachViaRight_support_cases hzOld with hzj | hzk
    · simpa [Tripod.firstNilResidualAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := j) hzj)
    · simpa [Tripod.firstNilResidualAttach] using
        hq_clean z hzq (T.rim_mem_vertexSet (i := k) hzk)

/-- Aggregate leg/rim contact statement for the first-collapsed residual
constructor with a clean outside tail starting at the old left common end. -/
theorem firstNilResidualCommonLeftTail_legs_meet_rims_only_at_attach
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
    (q : S.graph.Walk T.left a)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (T.firstNilResidualLeftArmLeg P hgraph hi hk q r).support ->
      z ∈ (T.firstNilResidualRim P hgraph hj hk hjk_order s).support ->
        z = T.firstNilResidualAttach k r := by
  intro r s z hzLeg hzRim
  fin_cases r
  · exact
      T.firstNilResidualLeg_zero_meets_rims
        P hgraph hij hik hjk hj hk hij_order hjk_order hpath_contacts
        s z
        (by simpa [Tripod.firstNilResidualLeftArmLeg] using hzLeg)
        hzRim
  · simpa [Tripod.firstNilResidualLeftArmLeg, Tripod.firstNilResidualAttach] using
      T.firstNilResidualCommonLeftTail_meets_rims_only_at_left
        P hgraph hj hk hjk_order q hq_outside hq_clean s z
        (by simpa [Tripod.firstNilResidualLeftArmLeg] using hzLeg)
        hzRim
  · simpa [Tripod.firstNilResidualLeftArmLeg, Tripod.firstNilResidualAttach] using
      T.firstNilResidualRightBranch_meets_rims
        P hgraph hij hik hjk hi hj hk hij_order hjk_order hpath_contacts
        s z
        (by simpa [Tripod.firstNilResidualLeftArmLeg] using hzLeg)
        hzRim

/-- Direct ambient tripod lift for the first ordered collapsed branch when the
clean outside tail starts at the old left common end. -/
theorem liftFirstNilResidualCommonLeftEndpoint
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
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
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod :=
  ⟨T.liftFirstNilResidualLeftArmCore
    P hgraph hij hik hjk hleg_k_not_nil hi hj hk hij_order hjk_order
    ha q hq_path hpath_contacts
    (T.firstNilResidualRims_internal_disjoint
      P hgraph hij hik hjk hj hk hij_order hjk_order hpath_contacts)
    (T.firstNilResidualCommonLeftTail_legs_pairwise_disjoint
      P hgraph hij hik hjk hi hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)
    (T.firstNilResidualCommonLeftTail_legs_meet_rims_only_at_attach
      P hgraph hij hik hjk hi hj hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)⟩

/-- Direct ambient tripod lift for the first ordered collapsed branch when the
residual clean outside tail starts on the old left arm of that branch. -/
theorem liftFirstNilResidualLeftArm
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  refine ⟨T.liftFirstNilResidualLeftArmCore
    P hgraph hij hik hjk hleg_k_not_nil hi hj hk hij_order hjk_order
    ha qLeft hqLeft_path hpath_contacts
    (T.firstNilResidualRims_internal_disjoint
      P hgraph hij hik hjk hj hk hij_order hjk_order hpath_contacts)
    ?_ ?_⟩
  · simpa [qLeft] using
      T.firstNilResidualLeftArmPrefixTail_legs_pairwise_disjoint
        P hgraph hij hik hjk hi hk hij_order hjk_order
        hx_arm hx_ne_attach q hprefix_outside hq_outside hq_clean
        hx_not_leg hpath_contacts
  · simpa [qLeft] using
      T.firstNilResidualLeftArmPrefixTail_legs_meet_rims_only_at_attach
        P hgraph hij hik hjk hi hj hk hij_order hjk_order
        hx_arm hx_internal q hprefix_outside hq_outside
        hq_clean hx_not_leg hpath_contacts

/-- Direct first-collapsed common-left endpoint lift with no nontriviality
assumption on the middle ordered old leg. -/
theorem liftFirstNilResidualCommonLeftEndpoint_last_not_nil
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
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
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod :=
  ⟨T.liftFirstNilResidualLeftArmCore
    P hgraph hij hik hjk hleg_k_not_nil hi hj hk hij_order hjk_order
    ha q hq_path hpath_contacts
    (T.firstNilResidualRims_internal_disjoint_last_not_nil
      P hgraph hij hik hjk hj hk hij_order hjk_order hpath_contacts)
    (T.firstNilResidualCommonLeftTail_legs_pairwise_disjoint
      P hgraph hij hik hjk hi hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)
    (T.firstNilResidualCommonLeftTail_legs_meet_rims_only_at_attach
      P hgraph hij hik hjk hi hj hk hij_order hjk_order q
      hq_outside hq_clean hpath_contacts)⟩

/-- Direct first-collapsed old-left-arm residual lift with no nontriviality
assumption on the middle ordered old leg. -/
theorem liftFirstNilResidualLeftArm_last_not_nil
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
          z ∈ P.outside)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft] using qLeftData.walk_isPath
  refine ⟨T.liftFirstNilResidualLeftArmCore
    P hgraph hij hik hjk hleg_k_not_nil hi hj hk hij_order hjk_order
    ha qLeft hqLeft_path hpath_contacts
    (T.firstNilResidualRims_internal_disjoint_last_not_nil
      P hgraph hij hik hjk hj hk hij_order hjk_order hpath_contacts)
    ?_ ?_⟩
  · simpa [qLeft] using
      T.firstNilResidualLeftArmPrefixTail_legs_pairwise_disjoint
        P hgraph hij hik hjk hi hk hij_order hjk_order
        hx_arm hx_ne_attach q hprefix_outside hq_outside hq_clean
        hx_not_leg hpath_contacts
  · simpa [qLeft] using
      T.firstNilResidualLeftArmPrefixTail_legs_meet_rims_only_at_attach
        P hgraph hij hik hjk hi hj hk hij_order hjk_order
        hx_arm hx_internal q hprefix_outside hq_outside
        hq_clean hx_not_leg hpath_contacts

end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
