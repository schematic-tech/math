import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.TripodAssembly

/-!
Avoidance and intersection facts for prefixed outside tails.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- An old outer-left-arm prefix followed by a clean outside tail avoids the
right-based rebuilt theta.  This is the exact geometric fact needed for an
internal collapsed-outer-rim residual. -/
theorem Tripod.leftArmPrefixTail_avoids_outerNilMiddleNonNilCommonLeftRims
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k r : Fin 3}
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
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (q : S.graph.Walk x a)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x)
    (hqLeft_outside :
      forall z : V,
        z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside) :
    forall s : Fin 3, forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False := by
  have hattach_not_prefix :
      T.attach r ∉ ((T.leftToAttach r).takeUntil x hx_arm).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.leftToAttach_isPath r) hx_arm
      (by simpa [ne_eq] using hx_ne_attach.symm)
  have hold_avoid : forall b : Fin 3, forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      (z ∈ (T.rightToAttach b).support ∨ z ∈ (T.leg b).support) -> False := by
    intro b z hzTail hzOld
    have hzCases :
        z ∈ (((T.leftToAttach r).takeUntil x hx_arm).mapLe hgraph).support ∨
          z ∈ q.support := by
      simpa [Tripod.leftArmPrefixTail,
        SimpleGraph.Walk.mem_support_append_iff] using hzTail
    rcases hzCases with hzPrefixMap | hzq
    · have hzPrefix :
          z ∈ ((T.leftToAttach r).takeUntil x hx_arm).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
      have hzArmR : z ∈ (T.leftToAttach r).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach r)
          hx_arm hzPrefix
      have hzRimR : z ∈ (T.rim r).support :=
        T.leftToAttach_support_subset_rim r hzArmR
      rcases hzOld with hzRightArm | hzLeg
      · by_cases hrb : r = b
        · subst b
          have hzAttach : z = T.attach r :=
            T.leftToAttach_support_inter_rightToAttach_eq_attach r
              hzArmR hzRightArm
          exact hattach_not_prefix (by simpa [hzAttach] using hzPrefix)
        · have hzRight : z = T.right :=
            T.rightToAttach_support_inter_rim_eq_right
              (fun h => hrb h.symm) hzRightArm hzRimR
          exact T.right_not_mem_leftToAttach r (by simpa [hzRight] using hzArmR)
      · have hzAttachB : z = T.attach b :=
          T.legs_meet_rims_only_at_attach b r z hzLeg hzRimR
        by_cases hbr : b = r
        · subst b
          exact hattach_not_prefix (by simpa [hzAttachB] using hzPrefix)
        · exact T.attach_not_mem_rim_of_ne hbr
            (by simpa [hzAttachB] using hzRimR)
    · have hzx : z = x := by
        apply hq_clean z hzq
        rcases hzOld with hzRightArm | hzLeg
        · exact T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim b hzRightArm)
        · exact T.leg_mem_vertexSet hzLeg
      rcases hzOld with hzRightArm | hzLeg
      · by_cases hrb : r = b
        · subst b
          have hxAttach : x = T.attach r := by
            apply T.leftToAttach_support_inter_rightToAttach_eq_attach r hx_arm
            simpa [hzx] using hzRightArm
          exact hx_ne_attach hxAttach
        · have hxRight : x = T.right :=
            T.rightToAttach_support_inter_rim_eq_right
              (fun h => hrb h.symm) (by simpa [hzx] using hzRightArm)
              (Walk.internalVertices_subset_support (T.rim r) hx_internal)
          exact hx_internal.2.2 hxRight
      · have hxAttachB : x = T.attach b :=
          T.legs_meet_rims_only_at_attach b r x
            (by simpa [hzx] using hzLeg)
            (Walk.internalVertices_subset_support (T.rim r) hx_internal)
        by_cases hbr : b = r
        · subst b
          exact hx_ne_attach hxAttachB
        · exact T.attach_not_mem_rim_of_ne hbr
            (by simpa [hxAttachB] using
              Walk.internalVertices_subset_support (T.rim r) hx_internal)
  intro s z hzTail hzRim
  fin_cases s
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzRim with
      hzArm | hzRest
    · exact hold_avoid i z hzTail (Or.inl hzArm)
    · rcases hzRest with hzLeg | hzSegment
      · exact hold_avoid i z hzTail (Or.inr hzLeg)
      · exact (hqLeft_outside z hzTail).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment)
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph j hzRim with
      hzArm | hzRest
    · exact hold_avoid j z hzTail (Or.inl hzArm)
    · rcases hzRest with hzLeg | hzNil
      · exact hold_avoid j z hzTail (Or.inr hzLeg)
      · have hzj : z = T.boundary j := by simpa using hzNil
        exact (hqLeft_outside z hzTail).2 (by simpa [hzj] using hj)
  · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzRim with
      hzArm | hzRest
    · exact hold_avoid k z hzTail (Or.inl hzArm)
    · rcases hzRest with hzLeg | hzSegmentRev
      · exact hold_avoid k z hzTail (Or.inr hzLeg)
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact (hqLeft_outside z hzTail).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment)

/-- A prefix on one old left rim arm followed by a clean tail meets a distinct
old left rim arm only at the old common left endpoint. -/
theorem Tripod.leftArmPrefixTail_inter_leftToAttach_eq_left_of_ne
    [DecidableEq V]
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {r j : Fin 3} (hrj : r ≠ j)
    {x a : V}
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (q : S.graph.Walk x a)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support ->
      z ∈ (T.leftToAttach j).support -> z = T.left := by
  intro z hzTail hzArmJ
  exact T.leftArmPrefixTail_inter_distinct_rim_eq_left_of_clean
    hgraph hrj hx_arm hx_internal q hq_clean z hzTail
    (T.leftToAttach_support_subset_rim j hzArmJ)


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
