import Schematic.Math.GraphTheory.Minors.Society.General.Foundations

/-! Same-end transitions whose selected escape lies on the opposite outer rim. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- A same-first transition theta whose boundary escape is prefixed on the
opposite ordered outer rim.  The escape avoids both outer rebuilt rims, so its
last contact with the middle rim supplies the third boundary leg. -/
theorem Tripod.liftAllNilOfOuterLastLeftArmResidualAndSameFirstTransition
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
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim i) ∨ v = T.left)
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
  let rim : Fin 3 -> S.graph.Walk (T.attach j) u :=
    GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
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
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu hv transition
          (by simpa [rim] using hzZero) with hzSegment | hzArm
      · exact (hescape_outside z hzEscape).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment)
      · exact hescape_right i z hzEscape
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight i) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArm)
    · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
          hi hj hk hij_order hjk_order hu hv transition
          (by simpa [rim] using hzTwo) with hzSegment | hzK | hzRight
      · exact (hescape_outside z hzEscape).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment)
      · exact hescape_right k z hzEscape hzK
      · have hzRightOld : z ∈ (T.rightToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach i) hu hzRight
        exact hescape_right i z hzEscape (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzRightOld)
  have hleft_middle : T.left ∈ (rim 1).support := by
    simp only [rim, Tripod.allNilSameFirstTransitionRim,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      exact (T.attachToLeft j).end_mem_support))
  have hescape_ne_leftEnd : forall z : V,
      z ∈ escape.support -> z ≠ T.attach j := by
    intro z hzEscape hzAttach
    have hzLeft : z = T.left :=
      escapeData.inter_distinct_rim_eq_left (fun h => hjk h.symm) z
        (by simpa [escape] using hzEscape)
        (by simpa [hzAttach] using (T.attach_mem_rim j).1)
    exact (T.attach_mem_rim j).2.1 (hzAttach.symm.trans hzLeft)
  have hescape_ne_rightEnd : forall z : V,
      z ∈ escape.support -> z ≠ u := by
    intro z hzEscape hzu
    have huForward : u ∈ (T.attachToRight i).support := by
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hu
    exact hescape_right i z hzEscape (by simpa [hzu] using huForward)
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
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> z = T.left := by
    intro z _ hz
    simpa [qnil] using hz
  have hbase :=
    GMIX24SourceProof.Tripod.allNilSameFirstTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean hu hu_ne_attach hv hv_ne_attach transition
      htransition_outside htransition_qnil
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
        Tripod.allNilCleanBridgeAttach, rim, qnil] using
        hbase 0 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg, qnil] using hzLeg) hzRim
    · exact False.elim (hp rfl)
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilCleanBridgeLeg, Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilCleanBridgeAttach, rim, qnil] using
        hbase 2 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg, qnil] using hzLeg) hzRim
  apply GMIX24SourceProof.Tripod.liftCheckedRimsAtLastMiddleContact
    P T (hlegs_nil i) (hlegs_nil k) hi hk hij_order hjk_order
    (by
      intro hju
      exact T.attach_not_mem_rim_of_ne (fun h => hij h.symm)
        (by simpa [hju] using hu_internal.1)) rim
  · intro s
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv transition
        htransition_path htransition_clean s
  · intro s t hst
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv hv_ne_attach hleft_contact transition
        htransition_outside htransition_clean s t hst
  · simpa [rim, Tripod.allNilCleanBridgeAttach] using
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal hv transition 0
  · simpa [rim, Tripod.allNilCleanBridgeAttach] using
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal hv transition 2
  · exact ha
  · exact hescape_path
  · exact hescape_outside
  · exact ⟨T.left, escape.start_mem_support, hleft_middle⟩
  · exact hescape_outer
  · exact hescape_ne_leftEnd
  · exact hescape_ne_rightEnd
  · exact houter_incidence

/-- Cut-path-reversed opposite-selected same-first exchange.  In the original
ordering this is a last-rim transition ending either on that same last left arm
or at the old left common end, while the selected escape lies on the first
rim. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameLastTransition
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
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim k) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterLastLeftArmResidualAndSameFirstTransition
      (i := k) (j := j) (k := i) (q := q) (hx_arm := hx_arm)
      (u := u) (v := v) (hu := hu) (hv := hv) (transition := transition)
      P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact (GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order
  · exact (GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order
  · intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  · exact hx_ne_attach
  · exact hx_internal
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hq_path
  · exact hq_clean
  · intro z hz
    simpa using hq_prefix_outside z hz
  · exact hu_ne_attach
  · exact hu_internal
  · exact hv_ne_attach
  · exact hleft_contact
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
