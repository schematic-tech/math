import Schematic.Math.GraphTheory.Minors.Society.General.Foundations

/-! The structured last-to-first source-text exchange. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- The final structured source-text exchange.  The transition runs from the
last right arm to the selected first left arm.  Reverse the cut-path order and
extend the transition along that first-left arm to the old common left end.
The extension is the middle rim of a same-first theta; the selected escape is
then cut after its last middle-rim contact. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndLastToFirstTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach k).support)
    (hu_ne_attach : u ≠ T.attach k)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (hfirst_left_prefix_outside : forall z : V,
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
  let bridge : S.graph.Walk u T.left :=
    GMIX24SourceProof.Tripod.lastToFirstExtendedTransition
      T hgraph hv transition
  let rim : Fin 3 -> S.graph.Walk (T.attach j) u :=
    GMIX24SourceProof.Tripod.allNilSameFirstViaLastTransitionRim
      P.reverse T hgraph (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
      (by simpa using hk) (by simpa using hj) (by simpa using hi)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
      hu hv transition
  have hescape_path : escape.IsPath := by
    simpa [escape] using escapeData.walk_isPath
  have hescape_outside : forall z : V,
      z ∈ escape.support -> z ∈ P.reverse.outside := by
    intro z hz
    simpa using hq_prefix_outside z (by simpa [escape] using hz)
  have hbridge_path : bridge.IsPath := by
    simpa [bridge] using
      (GMIX24SourceProof.Tripod.lastToFirstExtendedTransition_isPath
        (i := k) (k := i) T hgraph (fun h => hik h.symm)
        hu_internal hv transition htransition_path
        htransition_clean)
  have hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.reverse.outside := by
    intro z hz
    have hzOutside :=
      GMIX24SourceProof.Tripod.lastToFirstExtendedTransition_outside
        P T hgraph hv transition htransition_outside
        hfirst_left_prefix_outside z (by simpa [bridge] using hz)
    simpa using hzOutside
  have hcontacts_reverse : forall z : V,
      z ∈ P.reverse.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m := by
    intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  have hrim_path : forall s : Fin 3, (rim s).IsPath := by
    intro s
    simpa [rim] using
      (GMIX24SourceProof.Tripod.allNilSameFirstViaLastTransitionRim_isPath
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hcontacts_reverse hu hu_internal hv transition htransition_path
        htransition_clean s)
  have hrim_disjoint : forall s t : Fin 3, s ≠ t ->
      Disjoint (Walk.InternalVertices (rim s))
        (Walk.InternalVertices (rim t)) := by
    intro s t hst
    simpa [rim] using
      (GMIX24SourceProof.Tripod.allNilSameFirstViaLastTransitionRims_internal_disjoint
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hcontacts_reverse hu hu_ne_attach hu_internal hv hv_ne_attach
        hv_internal transition (by
          intro z hz
          simpa using htransition_outside z hz) htransition_clean s t hst)
  have hescape_right (s : Fin 3) : forall z : V,
      z ∈ escape.support -> z ∈ (T.attachToRight s).support -> False := by
    simpa [escape] using escapeData.disjoint_attachToRight s
  have hescape_outer : forall z : V, z ∈ escape.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False := by
    intro z hzEscape hzOuter
    rcases hzOuter with hzZero | hzTwo
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
          P.reverse T hgraph (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
          (by simpa using hk) (by simpa using hj) (by simpa using hi)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
          hu (T.leftToAttach k).start_mem_support bridge
          (by simpa [rim, bridge,
            Tripod.allNilSameFirstViaLastTransitionRim] using hzZero) with
        hzSegment | hzArm
      · exact (hescape_outside z hzEscape).2
          (P.reverse.pathSegmentBetween_support_subset_pathSet
            (by simpa using hk) (by simpa using hj)
            (Nat.le_of_lt
              ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2
                hjk_order)) z hzSegment)
      · exact hescape_right k z hzEscape
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight k) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArm)
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P.reverse T hgraph (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
          (by simpa using hk) (by simpa using hj) (by simpa using hi)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
          hu (T.leftToAttach k).start_mem_support bridge
          (by simpa [rim, bridge,
            Tripod.allNilSameFirstViaLastTransitionRim] using hzTwo) with
        hzSegment | hzI | hzRight
      · exact (hescape_outside z hzEscape).2
          (P.reverse.pathSegmentBetween_support_subset_pathSet
            (by simpa using hj) (by simpa using hi)
            (Nat.le_of_lt
              ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2
                hij_order)) z hzSegment)
      · exact hescape_right i z hzEscape hzI
      · exact hescape_right k z hzEscape (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using
              (SimpleGraph.Walk.support_takeUntil_subset
                (T.rightToAttach k) hu hzRight))
  have hleft_middle : T.left ∈ (rim 1).support := by
    simp only [rim, Tripod.allNilSameFirstViaLastTransitionRim,
      Tripod.allNilSameFirstTransitionRim,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      exact (T.attachToLeft j).end_mem_support))
  have hescape_ne_leftEnd : forall z : V,
      z ∈ escape.support -> z ≠ T.attach j := by
    intro z hzEscape hzAttach
    have hzLeft : z = T.left :=
      escapeData.inter_distinct_rim_eq_left hij z
        (by simpa [escape] using hzEscape)
        (by simpa [hzAttach] using (T.attach_mem_rim j).1)
    exact (T.attach_mem_rim j).2.1 (hzAttach.symm.trans hzLeft)
  have hescape_ne_rightEnd : forall z : V,
      z ∈ escape.support -> z ≠ u := by
    intro z hzEscape hzu
    have huForward : u ∈ (T.attachToRight k).support := by
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hu
    exact hescape_right k z hzEscape (by simpa [hzu] using huForward)
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.reverse.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hescape_outside T.left escape.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [qnil] using hz
  have hbridge_qnil : forall z : V, z ∈ bridge.support ->
      z ∈ qnil.support -> z = T.left := by
    intro z _hzBridge hzNil
    simpa [qnil] using hzNil
  have hbase :=
    GMIX24SourceProof.Tripod.allNilSameFirstTransitionLegs_meet_rims_only_at_attach
      P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
      (by simpa using hk) (by simpa using hj) (by simpa using hi)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
      hcontacts_reverse qnil hqnil_outside hqnil_clean hu hu_ne_attach
      (T.leftToAttach k).start_mem_support (by
        intro h
        exact T.left_ne_boundary k
          (h.trans ((T.leg_nil_iff_boundary_eq_attach k).mp
            (hlegs_nil k)).symm)) bridge hbridge_outside hbridge_qnil
  have houter_incidence : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P.reverse T
          (hlegs_nil k) (hlegs_nil i) (by simpa using hk) (by simpa using hi)
          escape p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach
        T k i T.left p := by
    intro p s hp z hzLeg hzRim
    fin_cases p
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilCleanBridgeLeg, Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilCleanBridgeAttach, rim, bridge, qnil,
        Tripod.allNilSameFirstViaLastTransitionRim] using
        hbase 0 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg, qnil] using hzLeg) hzRim
    · exact False.elim (hp rfl)
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilCleanBridgeLeg, Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilCleanBridgeAttach, rim, bridge, qnil,
        Tripod.allNilSameFirstViaLastTransitionRim] using
        hbase 2 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg, qnil] using hzLeg) hzRim
  apply GMIX24SourceProof.Tripod.liftCheckedRimsAtLastMiddleContact
    P.reverse T (hlegs_nil k) (hlegs_nil i) (by simpa using hk)
    (by simpa using hi)
    ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
    ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
    (by
      intro hju
      exact T.attach_not_mem_rim_of_ne (i := j) (j := k) hjk
        (by simpa [hju] using hu_internal.1)) rim hrim_path hrim_disjoint
  · simpa [rim, Tripod.allNilSameFirstViaLastTransitionRim,
      Tripod.allNilCleanBridgeAttach] using
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hu hu_ne_attach hu_internal (T.leftToAttach k).start_mem_support
        bridge 0)
  · simpa [rim, Tripod.allNilSameFirstViaLastTransitionRim,
      Tripod.allNilCleanBridgeAttach] using
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hu hu_ne_attach hu_internal (T.leftToAttach k).start_mem_support
        bridge 2)
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hescape_path
  · exact hescape_outside
  · exact ⟨T.left, escape.start_mem_support, hleft_middle⟩
  · exact hescape_outer
  · exact hescape_ne_leftEnd
  · exact hescape_ne_rightEnd
  · exact houter_incidence

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
