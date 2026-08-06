import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.LegConstruction

/-!
Internal disjointness of the rebuilt rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Two distinct old right branches (right rim arm followed by its leg) can
meet only at the old common right endpoint. -/
theorem Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right
    [DecidableEq V]
    {H : GeneralSociety V}
    (T : H.Tripod)
    {r s : Fin 3} (hrs : r ≠ s) {z : V}
    (hzr : z ∈ (T.rightToAttach r).support ∨ z ∈ (T.leg r).support)
    (hzs : z ∈ (T.rightToAttach s).support ∨ z ∈ (T.leg s).support) :
    z = T.right := by
  rcases hzr with hzArmR | hzLegR
  · rcases hzs with hzArmS | hzLegS
    · exact T.rightToAttach_support_inter_rim_eq_right hrs hzArmR
        (T.rightToAttach_support_subset_rim s hzArmS)
    · have hzAttachS : z = T.attach s :=
        T.legs_meet_rims_only_at_attach s r z hzLegS
          (T.rightToAttach_support_subset_rim r hzArmR)
      exact False.elim
        (T.attach_not_mem_rim_of_ne (fun h => hrs h.symm)
          (by simpa [hzAttachS] using
            T.rightToAttach_support_subset_rim r hzArmR))
  · rcases hzs with hzArmS | hzLegS
    · have hzAttachR : z = T.attach r :=
        T.legs_meet_rims_only_at_attach r s z hzLegR
          (T.rightToAttach_support_subset_rim s hzArmS)
      exact False.elim
        (T.attach_not_mem_rim_of_ne hrs
          (by simpa [hzAttachR] using
            T.rightToAttach_support_subset_rim s hzArmS))
    · exact False.elim
        (Set.disjoint_left.mp (T.legs_pairwise_disjoint r s hrs)
          hzLegR hzLegS)

/-- Internal disjointness of the first and middle right-based rebuilt rims. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftRim_zero_one_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
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
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 1)) := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hz0.1 with
    hzArm0 | hzRest0
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hz1.1 with
      hzArm1 | hzRest1
    · exact hz0.2.1
        (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hij
          (Or.inl hzArm0) (Or.inl hzArm1))
    · rcases hzRest1 with hzLeg1 | hzNil
      · exact hz0.2.1
          (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hij
            (Or.inl hzArm0) (Or.inr hzLeg1))
      · exact hz0.2.2 (by simpa using hzNil)
  · rcases hzRest0 with hzLeg0 | hzSegment
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hz1.1 with
        hzArm1 | hzRest1
      · exact hz0.2.1
          (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hij
            (Or.inr hzLeg0) (Or.inl hzArm1))
      · rcases hzRest1 with hzLeg1 | hzNil
        · exact hz0.2.1
            (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hij
              (Or.inr hzLeg0) (Or.inr hzLeg1))
        · exact hz0.2.2 (by simpa using hzNil)
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hz1.1 with
        hzArm1 | hzRest1
      · have hzBranch :
            z ∈ (T.rim j).support ∨ z ∈ (T.leg j).support :=
          Or.inl (T.rightToAttach_support_subset_rim j hzArm1)
        have hzT : z ∈ T.vertexSet :=
          T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzArm1)
        rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order hpath_contacts
            hzSegment hzT with hzi | hzj
        · have : i = j :=
            GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
              (by simpa [hzi] using hzBranch)
          exact False.elim (hij this)
        · exact hz0.2.2 hzj
      · rcases hzRest1 with hzLeg1 | hzNil
        · have hzBranch :
              z ∈ (T.rim j).support ∨ z ∈ (T.leg j).support := Or.inr hzLeg1
          have hzT : z ∈ T.vertexSet := T.leg_mem_vertexSet hzLeg1
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
              T hij hik hjk hi hj hij_order hjk_order hpath_contacts
              hzSegment hzT with hzi | hzj
          · have : i = j :=
              GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
                (by simpa [hzi] using hzBranch)
            exact False.elim (hij this)
          · exact hz0.2.2 hzj
        · exact hz0.2.2 (by simpa using hzNil)

/-- Internal disjointness of the middle and last right-based rebuilt rims. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftRim_one_two_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
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
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 1))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 2)) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hz1.1 with
    hzArm1 | hzRest1
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2.1 with
      hzArm2 | hzRest2
    · exact hz1.2.1
        (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hjk
          (Or.inl hzArm1) (Or.inl hzArm2))
    · rcases hzRest2 with hzLeg2 | hzSegmentRev
      · exact hz1.2.1
          (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hjk
            (Or.inl hzArm1) (Or.inr hzLeg2))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        have hzBranch :
            z ∈ (T.rim j).support ∨ z ∈ (T.leg j).support :=
          Or.inl (T.rightToAttach_support_subset_rim j hzArm1)
        rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim j hzArm1)) with hzj | hzk
        · exact hz1.2.2 hzj
        · have : k = j :=
            GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
              (by simpa [hzk] using hzBranch)
          exact False.elim (hjk this.symm)
  · rcases hzRest1 with hzLeg1 | hzNil
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2.1 with
        hzArm2 | hzRest2
      · exact hz1.2.1
          (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hjk
            (Or.inr hzLeg1) (Or.inl hzArm2))
      · rcases hzRest2 with hzLeg2 | hzSegmentRev
        · exact hz1.2.1
            (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hjk
              (Or.inr hzLeg1) (Or.inr hzLeg2))
        · have hzSegment : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          have hzBranch :
              z ∈ (T.rim j).support ∨ z ∈ (T.leg j).support := Or.inr hzLeg1
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
              T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
              (T.leg_mem_vertexSet hzLeg1) with hzj | hzk
          · exact hz1.2.2 hzj
          · have : k = j :=
              GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
                (by simpa [hzk] using hzBranch)
            exact False.elim (hjk this.symm)
    · exact hz1.2.2 (by simpa using hzNil)

/-- Internal disjointness of the two outer right-based rebuilt rims. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
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
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 2)) := by
  rw [Set.disjoint_left]
  intro z hz0 hz2
  rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hz0.1 with
    hzArm0 | hzRest0
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2.1 with
      hzArm2 | hzRest2
    · exact hz0.2.1
        (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hik
          (Or.inl hzArm0) (Or.inl hzArm2))
    · rcases hzRest2 with hzLeg2 | hzSegmentRev
      · exact hz0.2.1
          (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hik
            (Or.inl hzArm0) (Or.inr hzLeg2))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        have hzBranch :
            z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support :=
          Or.inl (T.rightToAttach_support_subset_rim i hzArm0)
        rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim i hzArm0)) with hzj | hzk
        · have : j = i :=
            GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
              (by simpa [hzj] using hzBranch)
          exact False.elim (hij this.symm)
        · have : k = i :=
            GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
              (by simpa [hzk] using hzBranch)
          exact False.elim (hik this.symm)
  · rcases hzRest0 with hzLeg0 | hzSegment0
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2.1 with
        hzArm2 | hzRest2
      · exact hz0.2.1
          (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hik
            (Or.inr hzLeg0) (Or.inl hzArm2))
      · rcases hzRest2 with hzLeg2 | hzSegmentRev
        · exact hz0.2.1
            (GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right T hik
              (Or.inr hzLeg0) (Or.inr hzLeg2))
        · have hzSegment : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          have hzBranch :
              z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support := Or.inr hzLeg0
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
              T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
              (T.leg_mem_vertexSet hzLeg0) with hzj | hzk
          · have : j = i :=
              GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
                (by simpa [hzj] using hzBranch)
            exact False.elim (hij this.symm)
          · have : k = i :=
              GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
                (by simpa [hzk] using hzBranch)
            exact False.elim (hik this.symm)
    · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hz2.1 with
        hzArm2 | hzRest2
      · have hzBranch :
            z ∈ (T.rim k).support ∨ z ∈ (T.leg k).support :=
          Or.inl (T.rightToAttach_support_subset_rim k hzArm2)
        rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment0
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim k hzArm2)) with hzi | hzj
        · have : i = k :=
            GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
              (by simpa [hzi] using hzBranch)
          exact False.elim (hik this)
        · have : j = k :=
            GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
              (by simpa [hzj] using hzBranch)
          exact False.elim (hjk this)
      · rcases hzRest2 with hzLeg2 | hzSegmentRev
        · have hzBranch :
              z ∈ (T.rim k).support ∨ z ∈ (T.leg k).support := Or.inr hzLeg2
          rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
              T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment0
              (T.leg_mem_vertexSet hzLeg2) with hzi | hzj
          · have : i = k :=
              GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
                (by simpa [hzi] using hzBranch)
            exact False.elim (hik this)
          · have : j = k :=
              GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
                (by simpa [hzj] using hzBranch)
            exact False.elim (hjk this)
        · have hzSegment2 : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
          have hzj : z = T.boundary j :=
            Walk.segmentBetween_support_inter_subset_common P.path_isPath
              (by simpa [GMIX24CutPath.pathSet] using hi)
              (by simpa [GMIX24CutPath.pathSet] using hj)
              (by simpa [GMIX24CutPath.pathSet] using hk)
              (Nat.le_of_lt hij_order) (Nat.le_of_lt hjk_order)
              hzSegment0 hzSegment2
          exact hz0.2.2 hzj

/-- Pairwise internal disjointness of all three right-based rebuilt rims. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftRims_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
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
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
            P T hgraph hi hj hk
            hij_order hjk_order r))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
            P T hgraph hi hj hk
            hij_order hjk_order s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts
  · exact (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts).symm
  · exact False.elim (hrs rfl)
  · exact GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts
  · exact (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts).symm
  · exact (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts).symm
  · exact False.elim (hrs rfl)


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
