import Schematic.Math.GraphTheory.Minors.Society.Terminal.CarrierTails
import Schematic.Math.GraphTheory.Minors.Society.Terminal.CleanBridge
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameMiddleTransition

/-!
All-nil transitions among the three cut-path-ordered rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- The source rerouting when the clean carrier transition runs from the
median right arm to the first left arm.  The transition and the two strict arm
prefixes form a structured right-to-left bridge. -/
theorem Tripod.liftAllNilOfMiddleToFirstArmTransition
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
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim j))
    (hright_prefix_outside : forall z : V,
      z ∈ ((T.rightToAttach j).takeUntil u hu).support -> z ∈ P.outside)
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (hleft_prefix_outside : forall z : V,
      z ∈ ((T.leftToAttach i).takeUntil v hv).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  let bridge : S.graph.Walk T.right T.left :=
    GMIX24SourceProof.Tripod.allNilMiddleToFirstBridge
      T hgraph hu hv transition
  have hbridge_cases : forall z : V, z ∈ bridge.support ->
      z ∈ ((T.rightToAttach j).takeUntil u hu).support ∨
        z ∈ transition.support ∨
          z ∈ ((T.leftToAttach i).takeUntil v hv).support := by
    intro z hz
    exact GMIX24SourceProof.Tripod.allNilMiddleToFirstBridge_support_cases
      T hgraph hu hv transition (by simpa [bridge] using hz)
  have hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside := by
    intro z hz
    rcases hbridge_cases z hz with hzRight | hzTransition | hzLeft
    · exact hright_prefix_outside z hzRight
    · exact htransition_outside z hzTransition
    · exact hleft_prefix_outside z hzLeft
  have hbridge_q : forall z : V,
      z ∈ bridge.support -> z ∈ q.support -> z = T.left := by
    intro z hzBridge hzq
    rcases hbridge_cases z hzBridge with hzRight | hzTransition | hzLeft
    · exact hq_clean z hzq
        (T.rim_mem_vertexSet
          (T.rightToAttach_support_subset_rim j
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.rightToAttach j) hu hzRight)))
    · exact False.elim (htransition_q z hzTransition hzq)
    · exact hq_clean z hzq
        (T.rim_mem_vertexSet
          (T.leftToAttach_support_subset_rim i
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.leftToAttach i) hv hzLeft)))
  have hattach_i_not_leftPrefix :
      T.attach i ∉ ((T.leftToAttach i).takeUntil v hv).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.leftToAttach_isPath i) hv
      (by simpa [ne_eq] using hv_ne_attach.symm)
  have hbridge_zero : forall z : V, z ∈ bridge.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 0).support -> z = T.right := by
    intro z hzBridge hzOuter
    rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzOuter with
      hzArm | hzRest
    · rcases hbridge_cases z hzBridge with hzRight | hzTransition | hzLeft
      · exact GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right
          T (fun h => hij h.symm)
          (Or.inl (SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach j) hu hzRight)) (Or.inl hzArm)
      · rcases htransition_clean z hzTransition
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim i hzArm)) with hzu | hzv
        · have huRight : u ∈ (T.rightToAttach i).support := by
            simpa [hzu] using hzArm
          have huEq : u = T.right :=
            T.rightToAttach_support_inter_rim_eq_right
              (fun h => hij h.symm) hu
              (T.rightToAttach_support_subset_rim i huRight)
          exact False.elim (hu_internal.2.2 huEq)
        · have hvRight : v ∈ (T.rightToAttach i).support := by
            simpa [hzv] using hzArm
          exact False.elim (hv_ne_attach
            (T.leftToAttach_support_inter_rightToAttach_eq_attach i hv hvRight))
      · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv hzLeft
        have hzAttach :=
          T.leftToAttach_support_inter_rightToAttach_eq_attach i hzLeftOld hzArm
        exact False.elim (hattach_i_not_leftPrefix (by simpa [hzAttach] using hzLeft))
    · rcases hzRest with hzLeg | hzSegment
      · rcases hbridge_cases z hzBridge with hzRight | hzTransition | hzLeft
        · exact GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right
            T (fun h => hij h.symm)
            (Or.inl (SimpleGraph.Walk.support_takeUntil_subset
              (T.rightToAttach j) hu hzRight)) (Or.inr hzLeg)
        · rcases htransition_clean z hzTransition (T.leg_mem_vertexSet hzLeg) with
            hzu | hzv
          · have hzAttach : z = T.attach i :=
              T.legs_meet_rims_only_at_attach i j z hzLeg
                (by simpa [hzu] using hu_internal.1)
            have hzRimJ : z ∈ (T.rim j).support := by
              simpa [hzu] using hu_internal.1
            exact False.elim (T.attach_not_mem_rim_of_ne hij
              (by simpa [hzAttach] using hzRimJ))
          · have hzRimI : z ∈ (T.rim i).support := by
              simpa [hzv] using hv_internal.1
            have hzAttach : z = T.attach i :=
              T.legs_meet_rims_only_at_attach i i z hzLeg hzRimI
            exact False.elim (hv_ne_attach (hzv.symm.trans hzAttach))
        · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
            SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv hzLeft
          have hzAttach : z = T.attach i :=
            T.legs_meet_rims_only_at_attach i i z hzLeg
              (T.leftToAttach_support_subset_rim i hzLeftOld)
          exact False.elim (hattach_i_not_leftPrefix (by simpa [hzAttach] using hzLeft))
      · exact False.elim ((hbridge_outside z hzBridge).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment))
  have hbridge_two : forall z : V, z ∈ bridge.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 2).support -> z = T.right := by
    intro z hzBridge hzOuter
    rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzOuter with
      hzArm | hzRest
    · rcases hbridge_cases z hzBridge with hzRight | hzTransition | hzLeft
      · exact GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right
          T hjk
          (Or.inl (SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach j) hu hzRight)) (Or.inl hzArm)
      · rcases htransition_clean z hzTransition
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim k hzArm)) with hzu | hzv
        · have huRight : u ∈ (T.rightToAttach k).support := by
            simpa [hzu] using hzArm
          have huEq : u = T.right :=
            T.rightToAttach_support_inter_rim_eq_right hjk hu
              (T.rightToAttach_support_subset_rim k huRight)
          exact False.elim (hu_internal.2.2 huEq)
        · have hvRight : v ∈ (T.rightToAttach k).support := by
            simpa [hzv] using hzArm
          have hvEq : v = T.right :=
            T.rightToAttach_support_inter_rim_eq_right
              (i := k) (j := i) (fun h => hik h.symm) hvRight hv_internal.1
          exact False.elim (hv_internal.2.2 hvEq)
      · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv hzLeft
        have hzLeftEq : z = T.left :=
          T.leftToAttach_support_inter_rim_eq_left hik hzLeftOld
            (T.rightToAttach_support_subset_rim k hzArm)
        exact False.elim (T.left_not_mem_rightToAttach k
          (by simpa [hzLeftEq] using hzArm))
    · rcases hzRest with hzLeg | hzSegmentRev
      · rcases hbridge_cases z hzBridge with hzRight | hzTransition | hzLeft
        · exact GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right
            T hjk
            (Or.inl (SimpleGraph.Walk.support_takeUntil_subset
              (T.rightToAttach j) hu hzRight)) (Or.inr hzLeg)
        · rcases htransition_clean z hzTransition (T.leg_mem_vertexSet hzLeg) with
            hzu | hzv
          · have hzAttach : z = T.attach k :=
              T.legs_meet_rims_only_at_attach k j z hzLeg
                (by simpa [hzu] using hu_internal.1)
            have hzRimJ : z ∈ (T.rim j).support := by
              simpa [hzu] using hu_internal.1
            exact False.elim (T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
              (by simpa [hzAttach] using hzRimJ))
          · have hzAttach : z = T.attach k :=
              T.legs_meet_rims_only_at_attach k i z hzLeg
                (by simpa [hzv] using hv_internal.1)
            have hzRimI : z ∈ (T.rim i).support := by
              simpa [hzv] using hv_internal.1
            exact False.elim (T.attach_not_mem_rim_of_ne (fun h => hik h.symm)
              (by simpa [hzAttach] using hzRimI))
        · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
            SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv hzLeft
          have hzAttach : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k i z hzLeg
              (T.leftToAttach_support_subset_rim i hzLeftOld)
          exact False.elim (T.attach_not_mem_rim_of_ne (fun h => hik h.symm)
            (by simpa [hzAttach] using
              T.leftToAttach_support_subset_rim i hzLeftOld))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact False.elim ((hbridge_outside z hzBridge).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
  refine ⟨{
    left := T.right
    right := T.boundary j
    left_ne_right := T.right_ne_boundary j
    rim := GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
      (hlegs_nil j)
      hi hj hk hij_order hjk_order bridge
    rim_isPath := by
      intro r
      simpa [bridge, Tripod.allNilCleanBridgeRim,
        Tripod.allNilMiddleToFirstTransitionRim,
        Tripod.allNilMiddleToFirstBridge] using
        (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim_isPath
          P T hgraph hij hik hjk (hlegs_nil j)
          hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
          (Or.inl hu_internal) hv hv_internal transition htransition_path
          htransition_clean r)
    attach := GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeAttach_mem_rim P T hgraph
        hij hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order bridge
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
      (hlegs_nil i) (hlegs_nil k) hi hk q
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLeg_isPath P T
        (hlegs_nil i) (hlegs_nil k) hi hk q hq_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeRims_internal_disjoint_of_outer_contacts
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts bridge hbridge_zero hbridge_two
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order q hq_outside
    legs_meet_rims_only_at_attach :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts q hq_outside hq_clean
        bridge hbridge_outside hbridge_q
  }⟩

/-- Cut-path-reversed counterpart of the middle-to-first exchange. -/
theorem Tripod.liftAllNilOfMiddleToLastArmTransition
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
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim j))
    (hright_prefix_outside : forall z : V,
      z ∈ ((T.rightToAttach j).takeUntil u hu).support -> z ∈ P.outside)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (hleft_prefix_outside : forall z : V,
      z ∈ ((T.leftToAttach k).takeUntil v hv).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  apply GMIX24SourceProof.Tripod.liftAllNilOfMiddleToFirstArmTransition
    (i := k) (j := j) (k := i) (a := a) (u := u) (v := v)
    (q := q) (transition := transition)
    P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact
      (GMIX24SourceProof.GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2
        hjk_order
  · exact
      (GMIX24SourceProof.GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2
        hij_order
  · intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hq_path
  · intro z hzq
    simpa using hq_outside z hzq
  · exact hq_clean
  · exact hu_ne_attach
  · exact hu_internal
  · intro z hz
    simpa using hright_prefix_outside z hz
  · exact hv_ne_attach
  · exact hv_internal
  · intro z hz
    simpa using hleft_prefix_outside z hz
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean
  · exact htransition_q


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
