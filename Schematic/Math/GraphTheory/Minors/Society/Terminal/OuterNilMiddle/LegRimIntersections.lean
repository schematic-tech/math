import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.RimDisjointness

/-!
Controlled intersections between rebuilt legs and rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- The first cut-path-tail leg meets every rebuilt rim only at its collapsed
old attachment. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
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
    (q : S.graph.Walk T.left a)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
          P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 0).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support ->
      z = GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
        T i j k 0 := by
  intro s z hzLeg hzRim
  have hzTail : z ∈ (P.pathTailToStart hi).support := by
    simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg, SimpleGraph.Walk.support_copy] using hzLeg
  have hclean_start : forall {w : V},
      w ∈ (P.pathTailToStart hi).support -> w ∈ T.vertexSet ->
        w = T.boundary i := by
    intro w hw hwT
    exact P.pathTailToStart_clean_first_foot_of_path_contacts
      T hij hik hjk hi hij_order hjk_order hpath_contacts hw hwT
  have hbi : T.boundary i = T.attach i :=
    (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil
  fin_cases s
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzRim with
      hzArm | hzRest
    · exact (hclean_start hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm))).trans hbi
    · rcases hzRest with hzOldLeg | hzSegment
      · exact (hclean_start hzTail (T.leg_mem_vertexSet hzOldLeg)).trans hbi
      · have hzSegment' : z ∈
            (Walk.segmentBetween P.path
              (by simpa [GMIX24CutPath.pathSet] using hi)
              (by simpa [GMIX24CutPath.pathSet] using hj)
              (Nat.le_of_lt hij_order)).support := by
          simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment
        exact (P.pathTailToStart_support_inter_segmentBetween_subset_left
          hi hj (Nat.le_of_lt hij_order) hzTail hzSegment').trans hbi
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hzRim with
      hzArm | hzRest
    · have hzi := hclean_start hzTail
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.rightToAttach_support_subset_rim j hzArm))
    · rcases hzRest with hzOldLeg | hzNil
      · have hzi := hclean_start hzTail (T.leg_mem_vertexSet hzOldLeg)
        exact False.elim
          (T.boundary_not_mem_leg_of_ne (i := j) (j := i)
            (fun h => hij h.symm) (by simpa [hzi] using hzOldLeg))
      · exact False.elim
          (P.pathTailToStart_not_mem_of_supportIndex_lt hi hij_order (by
            have hzj : z = T.boundary j := by simpa using hzNil
            rw [hzj] at hzTail
            exact hzTail))
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzRim with
      hzArm | hzRest
    · have hzi := hclean_start hzTail
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hzi] using T.rightToAttach_support_subset_rim k hzArm))
    · rcases hzRest with hzOldLeg | hzSegmentRev
      · have hzi := hclean_start hzTail (T.leg_mem_vertexSet hzOldLeg)
        exact False.elim
          (T.boundary_not_mem_leg_of_ne (i := k) (j := i)
            (fun h => hik h.symm) (by simpa [hzi] using hzOldLeg))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact False.elim
          (Set.disjoint_left.mp
            (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
              hi hj hk hij_order (Nat.le_of_lt hjk_order))
            hzTail (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment))

/-- The last cut-path-tail leg meets every rebuilt rim only at its collapsed
old attachment. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
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
    (q : S.graph.Walk T.left a)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
          P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 2).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support ->
      z = GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
        T i j k 2 := by
  intro s z hzLeg hzRim
  have hzTail : z ∈ (P.pathTailToEnd hk).support := by
    simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg, SimpleGraph.Walk.support_copy] using hzLeg
  have hclean_end : forall {w : V},
      w ∈ (P.pathTailToEnd hk).support -> w ∈ T.vertexSet ->
        w = T.boundary k := by
    intro w hw hwT
    exact P.pathTailToEnd_clean_last_foot_of_path_contacts
      T hij hik hjk hk hij_order hjk_order hpath_contacts hw hwT
  have hbk : T.boundary k = T.attach k :=
    (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil
  fin_cases s
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzRim with
      hzArm | hzRest
    · have hzk := hclean_end hzTail
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index (fun h => hik h.symm)
        (by simpa [hzk] using T.rightToAttach_support_subset_rim i hzArm))
    · rcases hzRest with hzOldLeg | hzSegment
      · have hzk := hclean_end hzTail (T.leg_mem_vertexSet hzOldLeg)
        exact False.elim
          (T.boundary_not_mem_leg_of_ne (i := i) (j := k) hik
            (by simpa [hzk] using hzOldLeg))
      · exact False.elim
          (Set.disjoint_left.mp
            (P.segmentBetween_support_disjoint_pathTailToEnd_of_lt
              hi hj hk (Nat.le_of_lt hij_order) hjk_order)
            (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment) hzTail)
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hzRim with
      hzArm | hzRest
    · have hzk := hclean_end hzTail
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index (fun h => hjk h.symm)
        (by simpa [hzk] using T.rightToAttach_support_subset_rim j hzArm))
    · rcases hzRest with hzOldLeg | hzNil
      · have hzk := hclean_end hzTail (T.leg_mem_vertexSet hzOldLeg)
        exact False.elim
          (T.boundary_not_mem_leg_of_ne (i := j) (j := k) hjk
            (by simpa [hzk] using hzOldLeg))
      · exact False.elim
          (P.pathTailToEnd_not_mem_of_supportIndex_lt hk hjk_order (by
            have hzj : z = T.boundary j := by simpa using hzNil
            rw [hzj] at hzTail
            exact hzTail))
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzRim with
      hzArm | hzRest
    · exact (hclean_end hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArm))).trans hbk
    · rcases hzRest with hzOldLeg | hzSegmentRev
      · exact (hclean_end hzTail (T.leg_mem_vertexSet hzOldLeg)).trans hbk
      · have hzSegment : z ∈
            (Walk.segmentBetween P.path
              (by simpa [GMIX24CutPath.pathSet] using hj)
              (by simpa [GMIX24CutPath.pathSet] using hk)
              (Nat.le_of_lt hjk_order)).reverse.support := by
          simpa [GMIX24CutPath.pathSegmentBetween] using hzSegmentRev
        exact (P.segmentBetween_reverse_support_inter_pathTailToEnd_subset_right
          hj hk (Nat.le_of_lt hjk_order) hzSegment hzTail).trans hbk

/-- The middle left-arm/outside-tail leg meets every rebuilt rim only at the
old middle attachment. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_one_meets_rims
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
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
          P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 1).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support ->
      z = GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
        T i j k 1 := by
  intro s z hzLeg hzRim
  rcases
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_one_support_cases
        P T hgraph hleg_i_nil hleg_k_nil hi hk q hzLeg with
    hzArm | hzq
  · have hzRimJ : z ∈ (T.rim j).support :=
      T.leftToAttach_support_subset_rim j hzArm
    fin_cases s
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left (fun h => hij h.symm)
            hzArm (T.rightToAttach_support_subset_rim i hzRightArm)
        exact False.elim
          (T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzSegment
        · have hzAttachI : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i j z hzOldLeg hzRimJ
          exact False.elim
            (T.attach_not_mem_rim_of_ne hij
              (by simpa [hzAttachI] using hzRimJ))
        · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
              T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment
              (T.rim_mem_vertexSet hzRimJ) with hzi | hzj
          · exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzi] using hzRimJ))
          · exact False.elim
              (T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
                (by simpa [hzj] using hzRimJ))
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hzRim with
        hzRightArm | hzRest
      · exact T.leftToAttach_support_inter_rightToAttach_eq_attach j
          hzArm hzRightArm
      · rcases hzRest with hzOldLeg | hzNil
        · exact T.legs_meet_rims_only_at_attach j j z hzOldLeg hzRimJ
        · have hzj : z = T.boundary j := by simpa using hzNil
          exact False.elim
            (T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
              (by simpa [hzj] using hzRimJ))
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left hjk hzArm
            (T.rightToAttach_support_subset_rim k hzRightArm)
        exact False.elim
          (T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzSegmentRev
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k j z hzOldLeg hzRimJ
          exact False.elim
            (T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
              (by simpa [hzAttachK] using hzRimJ))
        · have hzSegment : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
              T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
              (T.rim_mem_vertexSet hzRimJ) with hzj | hzk
          · exact False.elim
              (T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
                (by simpa [hzj] using hzRimJ))
          · exact False.elim
              (T.boundary_not_mem_rim_of_ne_index
                (i := k) (s := j) (fun h => hjk h.symm)
                (by simpa [hzk] using hzRimJ))
  · fin_cases s
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzRightArm))
        exact False.elim
          (T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzSegment
        · have hzLeft : z = T.left := hq_clean z hzq
            (T.leg_mem_vertexSet hzOldLeg)
          exact False.elim (T.left_not_mem_leg i (by simpa [hzLeft] using hzOldLeg))
        · have hzPath : z ∈ P.pathSet :=
            P.pathSegmentBetween_support_subset_pathSet hi hj
              (Nat.le_of_lt hij_order) z hzSegment
          exact False.elim ((hq_outside z hzq).2 hzPath)
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzRightArm))
        exact False.elim
          (T.left_not_mem_rightToAttach j (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzNil
        · have hzLeft : z = T.left := hq_clean z hzq
            (T.leg_mem_vertexSet hzOldLeg)
          exact False.elim (T.left_not_mem_leg j (by simpa [hzLeft] using hzOldLeg))
        · have hzj : z = T.boundary j := by simpa using hzNil
          have hzLeft : z = T.left := hq_clean z hzq
            (by simpa [hzj] using T.leg_mem_vertexSet (T.leg j).end_mem_support)
          exact False.elim (T.left_ne_boundary j (hzLeft.symm.trans hzj))
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzRightArm))
        exact False.elim
          (T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzSegmentRev
        · have hzLeft : z = T.left := hq_clean z hzq
            (T.leg_mem_vertexSet hzOldLeg)
          exact False.elim (T.left_not_mem_leg k (by simpa [hzLeft] using hzOldLeg))
        · have hzSegment : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          have hzPath : z ∈ P.pathSet :=
            P.pathSegmentBetween_support_subset_pathSet hj hk
              (Nat.le_of_lt hjk_order) z hzSegment
          exact False.elim ((hq_outside z hzq).2 hzPath)

/-- Middle-leg incidence from the exact condition that its tail avoids the
rebuilt theta.  The old middle left arm is allowed, and meets the rebuilt
middle rim precisely at `T.attach j`. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_one_meets_rims_of_tail_avoids
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
    (q : S.graph.Walk T.left a)
    (hq_avoids : forall s : Fin 3, forall z : V,
      z ∈ q.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
          P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 1).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support ->
      z = GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
        T i j k 1 := by
  intro s z hzLeg hzRim
  rcases
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_one_support_cases
        P T hgraph hleg_i_nil hleg_k_nil hi hk q hzLeg with
    hzArm | hzq
  · have hzRimJ : z ∈ (T.rim j).support :=
      T.leftToAttach_support_subset_rim j hzArm
    fin_cases s
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left (fun h => hij h.symm)
            hzArm (T.rightToAttach_support_subset_rim i hzRightArm)
        exact False.elim
          (T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzSegment
        · have hzAttachI : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i j z hzOldLeg hzRimJ
          exact False.elim
            (T.attach_not_mem_rim_of_ne hij
              (by simpa [hzAttachI] using hzRimJ))
        · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
              T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment
              (T.rim_mem_vertexSet hzRimJ) with hzi | hzj
          · exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
              (by simpa [hzi] using hzRimJ))
          · exact False.elim
              (T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
                (by simpa [hzj] using hzRimJ))
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hzRim with
        hzRightArm | hzRest
      · exact T.leftToAttach_support_inter_rightToAttach_eq_attach j
          hzArm hzRightArm
      · rcases hzRest with hzOldLeg | hzNil
        · exact T.legs_meet_rims_only_at_attach j j z hzOldLeg hzRimJ
        · have hzj : z = T.boundary j := by simpa using hzNil
          exact False.elim
            (T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
              (by simpa [hzj] using hzRimJ))
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzRim with
        hzRightArm | hzRest
      · have hzLeft : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left hjk hzArm
            (T.rightToAttach_support_subset_rim k hzRightArm)
        exact False.elim
          (T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzRightArm))
      · rcases hzRest with hzOldLeg | hzSegmentRev
        · have hzAttachK : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k j z hzOldLeg hzRimJ
          exact False.elim
            (T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
              (by simpa [hzAttachK] using hzRimJ))
        · have hzSegment : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
              T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
              (T.rim_mem_vertexSet hzRimJ) with hzj | hzk
          · exact False.elim
              (T.boundary_not_mem_own_rim_of_leg_not_nil hleg_j_not_nil
                (by simpa [hzj] using hzRimJ))
          · exact False.elim
              (T.boundary_not_mem_rim_of_ne_index
                (i := k) (s := j) (fun h => hjk h.symm)
                (by simpa [hzk] using hzRimJ))
  · exact False.elim (hq_avoids s z hzq hzRim)

/-- Complete leg/rim incidence for the nontrivial-middle rebuilt tripod. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLegs_meet_rims_only_at_attach
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
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
          P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support ->
      z = GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
        T i j k r := by
  intro r s z hzLeg hzRim
  fin_cases r
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_zero_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts s z hzLeg hzRim
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_one_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
      hi hj hk hij_order hjk_order q hq_outside hq_clean hpath_contacts
      s z hzLeg hzRim
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_two_meets_rims
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hj hk
      hij_order hjk_order q hpath_contacts s z hzLeg hzRim


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
