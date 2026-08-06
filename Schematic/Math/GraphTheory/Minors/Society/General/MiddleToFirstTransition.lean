import Schematic.Math.GraphTheory.Minors.Society.General.Foundations

/-! Internal disjointness and lifting for the middle-to-first transition. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- The checked middle-to-first transition rims are internally disjoint under
the exact outside-prefix hypotheses used by the source bridge normalization. -/
theorem Tripod.allNilMiddleToFirstTransitionRims_internal_disjoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach j).support)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hright_prefix_outside : forall z : V,
      z ∈ ((T.rightToAttach j).takeUntil u hu).support -> z ∈ P.outside)
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (hleft_prefix_outside : forall z : V,
      z ∈ ((T.leftToAttach i).takeUntil v hv).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall s t : Fin 3, s ≠ t ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim
            P T hgraph (hlegs_nil j)
            hi hj hk hij_order hjk_order hu hv transition s))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim
            P T hgraph (hlegs_nil j)
            hi hj hk hij_order hjk_order hu hv transition t)) := by
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
          rcases hright_contact with huInternal | huRight
          · exact False.elim (huInternal.2.2 huEq)
          · exact hzu.trans huRight
        · have hvRight : v ∈ (T.rightToAttach i).support := by
            simpa [hzv] using hzArm
          exact False.elim (hv_ne_attach
            (T.leftToAttach_support_inter_rightToAttach_eq_attach i hv hvRight))
      · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv hzLeft
        have hzAttach :=
          T.leftToAttach_support_inter_rightToAttach_eq_attach i hzLeftOld hzArm
        exact False.elim
          (hattach_i_not_leftPrefix (by simpa [hzAttach] using hzLeft))
    · rcases hzRest with hzLeg | hzSegment
      · rcases hbridge_cases z hzBridge with hzRight | hzTransition | hzLeft
        · exact GMIX24SourceProof.Tripod.rightArmOrLeg_inter_rightArmOrLeg_eq_right
            T (fun h => hij h.symm)
            (Or.inl (SimpleGraph.Walk.support_takeUntil_subset
              (T.rightToAttach j) hu hzRight)) (Or.inr hzLeg)
        · rcases htransition_clean z hzTransition (T.leg_mem_vertexSet hzLeg) with
            hzu | hzv
          · rcases hright_contact with huInternal | huRight
            · have hzAttach : z = T.attach i :=
                T.legs_meet_rims_only_at_attach i j z hzLeg
                  (by simpa [hzu] using huInternal.1)
              have hzRimJ : z ∈ (T.rim j).support := by
                simpa [hzu] using huInternal.1
              exact False.elim (T.attach_not_mem_rim_of_ne hij
                (by simpa [hzAttach] using hzRimJ))
            · exact False.elim
                (T.right_not_mem_leg i (by simpa [hzu, huRight] using hzLeg))
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
          exact False.elim
            (hattach_i_not_leftPrefix (by simpa [hzAttach] using hzLeft))
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
          rcases hright_contact with huInternal | huRight
          · exact False.elim (huInternal.2.2 huEq)
          · exact hzu.trans huRight
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
          · rcases hright_contact with huInternal | huRight
            · have hzAttach : z = T.attach k :=
                T.legs_meet_rims_only_at_attach k j z hzLeg
                  (by simpa [hzu] using huInternal.1)
              have hzRimJ : z ∈ (T.rim j).support := by
                simpa [hzu] using huInternal.1
              exact False.elim
                (T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
                  (by simpa [hzAttach] using hzRimJ))
            · exact False.elim
                (T.right_not_mem_leg k (by simpa [hzu, huRight] using hzLeg))
          · have hzAttach : z = T.attach k :=
              T.legs_meet_rims_only_at_attach k i z hzLeg
                (by simpa [hzv] using hv_internal.1)
            have hzRimI : z ∈ (T.rim i).support := by
              simpa [hzv] using hv_internal.1
            exact False.elim
              (T.attach_not_mem_rim_of_ne (fun h => hik h.symm)
                (by simpa [hzAttach] using hzRimI))
        · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
            SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv hzLeft
          have hzAttach : z = T.attach k :=
            T.legs_meet_rims_only_at_attach k i z hzLeg
              (T.leftToAttach_support_subset_rim i hzLeftOld)
          exact False.elim
            (T.attach_not_mem_rim_of_ne (fun h => hik h.symm)
              (by simpa [hzAttach] using
                T.leftToAttach_support_subset_rim i hzLeftOld))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact False.elim ((hbridge_outside z hzBridge).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
  simpa [bridge, Tripod.allNilCleanBridgeRim,
      Tripod.allNilMiddleToFirstTransitionRim,
      Tripod.allNilMiddleToFirstBridge] using
    GMIX24SourceProof.Tripod.allNilCleanBridgeRims_internal_disjoint_of_outer_contacts
      P T hgraph hij hik hjk (hlegs_nil j)
      hi hj hk hij_order hjk_order hpath_contacts bridge hbridge_zero hbridge_two

/-- A median-right to selected-first-left transition with an arbitrary
intersection against the selected prefixed escape.  The escape's last contact
with the checked transition theta becomes the new middle attachment. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToFirstTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
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
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
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
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Nonempty S.Tripod := by
  let escapeData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let escape : S.graph.Walk T.left a := escapeData.walk
  let bridge : S.graph.Walk T.right T.left :=
    GMIX24SourceProof.Tripod.allNilMiddleToFirstBridge
      T hgraph hu hv transition
  let rim : Fin 3 -> S.graph.Walk T.right (T.boundary j) :=
    GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim
      P T hgraph (hlegs_nil j)
      hi hj hk hij_order hjk_order hu hv transition
  have hrj : r ≠ j := by
    rcases hr with rfl | rfl
    · exact hij
    · exact fun h => hjk h.symm
  have hescape_path : escape.IsPath := by
    simpa [escape] using escapeData.walk_isPath
  have hescape_outside : forall z : V,
      z ∈ escape.support -> z ∈ P.outside := by
    simpa [escape] using hq_prefix_outside
  have hescape_right (s : Fin 3) : forall z : V,
      z ∈ escape.support -> z ∈ (T.attachToRight s).support -> False := by
    simpa [escape] using escapeData.disjoint_attachToRight s
  have hescape_outer : forall z : V, z ∈ escape.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False := by
    intro z hzEscape hzOuter
    rcases hzOuter with hzZero | hzTwo
    · have hzOld : z ∈
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
            P T hgraph hi hj hk
            hij_order hjk_order 0).support := by
        simpa [rim, Tripod.allNilMiddleToFirstTransitionRim] using hzZero
      rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i hzOld with
        hzArm | hzLeg | hzPath
      · exact hescape_right i z hzEscape (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzArm)
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp (hlegs_nil i)
        have hzi : z = T.attach i := by simpa [hsupport] using hzLeg
        exact (hescape_outside z hzEscape).2 (by
          rw [hzi, ← (T.leg_nil_iff_boundary_eq_attach i).mp (hlegs_nil i)]
          exact hi)
      · exact (hescape_outside z hzEscape).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzPath)
    · have hzOld : z ∈
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
            P T hgraph hi hj hk
            hij_order hjk_order 2).support := by
        simpa [rim, Tripod.allNilMiddleToFirstTransitionRim] using hzTwo
      rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k hzOld with
        hzArm | hzLeg | hzPathRev
      · exact hescape_right k z hzEscape (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzArm)
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp (hlegs_nil k)
        have hzk : z = T.attach k := by simpa [hsupport] using hzLeg
        exact (hescape_outside z hzEscape).2 (by
          rw [hzk, ← (T.leg_nil_iff_boundary_eq_attach k).mp (hlegs_nil k)]
          exact hk)
      · have hzPath : z ∈
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzPathRev
        exact (hescape_outside z hzEscape).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzPath)
  have hescape_ne_right : forall z : V,
      z ∈ escape.support -> z ≠ T.right := by
    intro z hzEscape hzRight
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp
        (by simpa [escape, Tripod.LeftArmPrefixTailData.walk,
          Tripod.leftArmPrefixTail] using hzEscape) with
      hzPrefix | hzq
    · have hzOld : z ∈ (T.leftToAttach r).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach r) hx_arm (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefix)
      exact T.right_not_mem_leftToAttach r (by simpa [hzRight] using hzOld)
    · have hzx : z = x := hq_clean z hzq (by
          rw [hzRight]
          exact T.right_mem_vertexSet)
      exact hx_internal.2.2 (hzx.symm.trans hzRight)
  have hescape_ne_boundary_j : forall z : V,
      z ∈ escape.support -> z ≠ T.boundary j := by
    intro z hzEscape hzBoundary
    have hzLeft : z = T.left :=
      escapeData.inter_distinct_rim_eq_left hrj z
        (by simpa [escape] using hzEscape)
        (by
          rw [hzBoundary,
            (T.leg_nil_iff_boundary_eq_attach j).mp (hlegs_nil j)]
          exact (T.attach_mem_rim j).1)
    exact T.left_ne_boundary j (hzLeft.symm.trans hzBoundary)
  have hleft_middle : T.left ∈ (rim 1).support := by
    have hleft_internal : T.left ∈ Walk.InternalVertices (rim 1) := by
      simpa [rim, Tripod.allNilMiddleToFirstTransitionAttach,
        Tripod.allNilSameMiddleTransitionAttach] using
          (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionAttach_mem_rim
            P T hgraph hij hjk (hlegs_nil j)
            hi hj hk hij_order hjk_order hu hv transition 1)
    exact hleft_internal.1
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
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hescape_outside T.left escape.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [qnil] using hz
  have hbridge_qnil : forall z : V, z ∈ bridge.support ->
      z ∈ qnil.support -> z = T.left := by
    intro z _hzBridge hzq
    simpa [qnil] using hzq
  have hbase :=
    GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean bridge hbridge_outside hbridge_qnil
  have houter_incidence : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
          (hlegs_nil i) (hlegs_nil k) hi hk escape p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach
        T i k T.left p := by
    intro p s hp z hzLeg hzRim
    fin_cases p
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilCleanBridgeLeg, Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilCleanBridgeAttach, rim, bridge,
        Tripod.allNilCleanBridgeRim,
        Tripod.allNilMiddleToFirstTransitionRim,
        Tripod.allNilMiddleToFirstBridge, qnil] using
        hbase 0 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg, qnil] using hzLeg) (by
              simpa [rim, bridge, Tripod.allNilCleanBridgeRim,
                Tripod.allNilMiddleToFirstTransitionRim,
                Tripod.allNilMiddleToFirstBridge] using hzRim)
    · exact False.elim (hp rfl)
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilCleanBridgeLeg, Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilCleanBridgeAttach, rim, bridge,
        Tripod.allNilCleanBridgeRim,
        Tripod.allNilMiddleToFirstTransitionRim,
        Tripod.allNilMiddleToFirstBridge, qnil] using
        hbase 2 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg, qnil] using hzLeg) (by
              simpa [rim, bridge, Tripod.allNilCleanBridgeRim,
                Tripod.allNilMiddleToFirstTransitionRim,
                Tripod.allNilMiddleToFirstBridge] using hzRim)
  apply GMIX24SourceProof.Tripod.liftCheckedRimsAtLastMiddleContact
    P T (hlegs_nil i) (hlegs_nil k) hi hk hij_order hjk_order
    (T.right_ne_boundary j) rim
  · intro s
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hright_contact hv hv_internal transition htransition_path
        htransition_clean s
  · intro s t hst
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRims_internal_disjoint
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts hu hright_contact hright_prefix_outside
        hv hv_ne_attach hv_internal hleft_prefix_outside transition
        htransition_outside htransition_clean s t hst
  · simpa [rim, Tripod.allNilMiddleToFirstTransitionAttach,
      Tripod.allNilSameMiddleTransitionAttach] using
      GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionAttach_mem_rim
        P T hgraph hij hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hu hv transition 0
  · simpa [rim, Tripod.allNilMiddleToFirstTransitionAttach,
      Tripod.allNilSameMiddleTransitionAttach] using
      GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionAttach_mem_rim
        P T hgraph hij hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hu hv transition 2
  · exact ha
  · exact hescape_path
  · exact hescape_outside
  · exact ⟨T.left, escape.start_mem_support, hleft_middle⟩
  · exact hescape_outer
  · exact hescape_ne_right
  · exact hescape_ne_boundary_j
  · exact houter_incidence

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
