import Schematic.Math.GraphTheory.Minors.Society.Terminal.SplicedTransitions.ResidualCases

/-!
Final transition-versus-escape intersection resolution.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- A normalized right-arm-to-left-arm transition either gives the ambient
tripod through the finite dispatcher, or meets the selected left escape at a
vertex other than their possible common old endpoint. -/
theorem Tripod.liftAllNilOfCleanTransitionOrNonleftIntersection
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
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
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu_contact : u = T.right ∨
      Exists fun r : Fin 3 =>
        u ∈ Walk.InternalVertices (T.rim r) ∧
          u ∈ (T.rightToAttach r).support ∧ u ≠ T.attach r)
    (hv_contact : v = T.left ∨
      Exists fun s : Fin 3 =>
        v ∈ Walk.InternalVertices (T.rim s) ∧
          v ∈ (T.leftToAttach s).support ∧ v ≠ T.attach s)
    (hright_prefix_outside : forall (r : Fin 3) (w : V)
      (hw : w ∈ (T.rightToAttach r).support),
      w ≠ T.attach r -> forall z : V,
        z ∈ ((T.rightToAttach r).takeUntil w hw).support -> z ∈ P.outside)
    (hleft_prefix_outside : forall (r : Fin 3) (w : V)
      (hw : w ∈ (T.leftToAttach r).support),
      w ≠ T.attach r -> forall z : V,
        z ∈ ((T.leftToAttach r).takeUntil w hw).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Nonempty S.Tripod ∨
      Exists fun c : V =>
        c ∈ transition.support ∧ c ∈ q.support ∧ c ≠ T.left := by
  rcases hv_contact with hvLeft | hvStrict
  · subst v
    by_cases htransition_q : forall z : V,
        z ∈ transition.support -> z ∈ q.support -> z = T.left
    · exact Or.inl
        (Tripod.liftAllNilOfCleanTransitionToLeftEndpoint
          P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
          hpath_contacts q ha hq_path hq_outside hq_clean hu_contact
          transition htransition_path htransition_outside htransition_clean
          htransition_q)
    · push Not at htransition_q
      rcases htransition_q with ⟨c, hcTransition, hcQ, hcNe⟩
      exact Or.inr ⟨c, hcTransition, hcQ, hcNe⟩
  · by_cases htransition_q : forall z : V,
        z ∈ transition.support -> z ∈ q.support -> False
    · exact Or.inl
        (Tripod.liftAllNilOfCleanTransitionToStrictLeftArm
          P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
          hpath_contacts q ha hq_path hq_outside hq_clean hu_contact hvStrict
          hright_prefix_outside hleft_prefix_outside transition
          htransition_path htransition_outside htransition_clean htransition_q)
    · push Not at htransition_q
      rcases htransition_q with ⟨c, hcTransition, hcQ, _⟩
      refine Or.inr ⟨c, hcTransition, hcQ, ?_⟩
      intro hcLeft
      have hcT : c ∈ T.vertexSet := by simp [hcLeft]
      rcases htransition_clean c hcTransition hcT with hcu | hcv
      · rcases hu_contact with huRight | ⟨r, huInternal, _huArm, _huNe⟩
        · exact T.left_ne_right (hcLeft.symm.trans (hcu.trans huRight))
        · exact huInternal.2.1 (hcu.symm.trans hcLeft)
      · rcases hvStrict with ⟨s, hvInternal, _hvArm, _hvNe⟩
        exact hvInternal.2.1 (hcv.symm.trans hcLeft)

/-- The non-left intersection alternative from the normalized transition
dichotomy also gives an ambient tripod.  Stop at the first transition contact
with the escape, reverse the escape prefix into the rebuilt rim, and retain
the escape suffix as the new boundary leg. -/
theorem Tripod.liftAllNilOfNonleftTransitionIntersection
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
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
    {a u v d : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu_contact : u = T.right ∨
      Exists fun r : Fin 3 =>
        u ∈ Walk.InternalVertices (T.rim r) ∧
          u ∈ (T.rightToAttach r).support ∧ u ≠ T.attach r)
    (hv_contact : v = T.left ∨
      Exists fun s : Fin 3 =>
        v ∈ Walk.InternalVertices (T.rim s) ∧
          v ∈ (T.leftToAttach s).support ∧ v ≠ T.attach s)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (hd_transition : d ∈ transition.support)
    (hd_q : d ∈ q.support)
    (hd_ne_left : d ≠ T.left) :
    Nonempty S.Tripod := by
  have hu_ne_left : u ≠ T.left := by
    intro huLeft
    rcases hu_contact with huRight | ⟨r, huInternal, _huArm, _huNe⟩
    · exact T.left_ne_right (huLeft.symm.trans huRight)
    · exact huInternal.2.1 huLeft
  have hd_ne_v : d ≠ v := by
    intro hdv
    rcases hv_contact with hvLeft | ⟨s, hvInternal, _hvArm, _hvNe⟩
    · exact hd_ne_left (hdv.trans hvLeft)
    · have hdLeft := hq_clean d hd_q (by
        rw [hdv]
        exact T.rim_mem_vertexSet hvInternal.1)
      exact hd_ne_left hdLeft
  let toD : S.graph.Walk u d := transition.takeUntil d hd_transition
  have htoD_path : toD.IsPath := by
    simpa [toD] using htransition_path.takeUntil hd_transition
  obtain ⟨c, hcToD, hcQ, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) htoD_path {z : V | z ∈ q.support} hd_q
  let transPrefix : S.graph.Walk u c := toD.takeUntil c hcToD
  let qPrefix : S.graph.Walk T.left c := q.takeUntil c hcQ
  let tail : S.graph.Walk c a := q.dropUntil c hcQ
  have hv_not_toD : v ∉ toD.support := by
    simpa [toD] using
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        htransition_path hd_transition hd_ne_v.symm
  have hc_ne_left : c ≠ T.left := by
    intro hcLeft
    have hcTransition : c ∈ transition.support :=
      SimpleGraph.Walk.support_takeUntil_subset transition hd_transition
        (by simpa [toD] using hcToD)
    rcases htransition_clean c hcTransition
        (by simp [hcLeft]) with hcu | hcv
    · exact hu_ne_left (hcu.symm.trans hcLeft)
    · exact hv_not_toD (by simpa [hcv] using hcToD)
  have htransPrefix_path : transPrefix.IsPath := by
    simpa [transPrefix] using htoD_path.takeUntil hcToD
  have hqPrefix_path : qPrefix.IsPath := by
    simpa [qPrefix] using hq_path.takeUntil hcQ
  have htail_path : tail.IsPath := by
    simpa [tail] using hq_path.dropUntil hcQ
  let bridge : S.graph.Walk u T.left := transPrefix.append qPrefix.reverse
  have hbridge_path : bridge.IsPath := by
    dsimp [bridge]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      htransPrefix_path hqPrefix_path.reverse ?_
    intro z hzPrefix hzQPrefixRev
    apply hfirst z
    · simpa [transPrefix] using hzPrefix
    · have hzQPrefix : z ∈ qPrefix.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzQPrefixRev
      exact SimpleGraph.Walk.support_takeUntil_subset q hcQ
        (by simpa [qPrefix] using hzQPrefix)
  have htransPrefix_transition : forall z : V,
      z ∈ transPrefix.support -> z ∈ transition.support := by
    intro z hz
    apply SimpleGraph.Walk.support_takeUntil_subset transition hd_transition
    apply SimpleGraph.Walk.support_takeUntil_subset toD hcToD
    simpa [transPrefix] using hz
  have hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside := by
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with
      hzPrefix | hzQPrefixRev
    · exact htransition_outside z
        (htransPrefix_transition z (by simpa [bridge] using hzPrefix))
    · apply hq_outside z
      exact SimpleGraph.Walk.support_takeUntil_subset q hcQ (by
        simpa [bridge, qPrefix, SimpleGraph.Walk.support_reverse] using hzQPrefixRev)
  have hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = u ∨ z = T.left := by
    intro z hz hzT
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with
      hzPrefix | hzQPrefixRev
    · rcases htransition_clean z
          (htransPrefix_transition z (by simpa [bridge] using hzPrefix)) hzT with
        hzu | hzv
      · exact Or.inl hzu
      · exact False.elim (hv_not_toD (by
          apply SimpleGraph.Walk.support_takeUntil_subset toD hcToD
          simpa [bridge, transPrefix, hzv] using hzPrefix))
    · exact Or.inr (hq_clean z (SimpleGraph.Walk.support_takeUntil_subset q hcQ
        (by simpa [bridge, qPrefix,
          SimpleGraph.Walk.support_reverse] using hzQPrefixRev)) hzT)
  have htail_outside : forall z : V, z ∈ tail.support -> z ∈ P.outside := by
    intro z hz
    exact hq_outside z
      (SimpleGraph.Walk.support_dropUntil_subset q hcQ (by simpa [tail] using hz))
  have hleft_not_tail : T.left ∉ tail.support := by
    simpa [tail] using
      Walk.IsPath.start_not_mem_dropUntil_support_of_ne hq_path hcQ hc_ne_left
  have htail_clean : forall z : V, z ∈ tail.support ->
      z ∈ T.vertexSet -> False := by
    intro z hz hzT
    have hzQ : z ∈ q.support :=
      SimpleGraph.Walk.support_dropUntil_subset q hcQ (by simpa [tail] using hz)
    have hzLeft : z = T.left := hq_clean z hzQ hzT
    exact hleft_not_tail (by simpa [hzLeft] using hz)
  have hc_bridge : c ∈ bridge.support := by
    change c ∈ (transPrefix.append qPrefix.reverse).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (by simp [transPrefix])
  have hbridge_tail : forall z : V, z ∈ bridge.support ->
      z ∈ tail.support -> z = c := by
    intro z hzBridge hzTail
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzBridge with
      hzPrefix | hzQPrefixRev
    · apply hfirst z
      · simpa [bridge, transPrefix] using hzPrefix
      · exact SimpleGraph.Walk.support_dropUntil_subset q hcQ
          (by simpa [tail] using hzTail)
    · exact Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        hq_path hcQ
        (by simpa [bridge, qPrefix,
          SimpleGraph.Walk.support_reverse] using hzQPrefixRev)
        (by simpa [tail] using hzTail)
  rcases hu_contact with huRight | huStrict
  · subst u
    exact Tripod.liftAllNilOfSplicedRightEndpointTransition
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts ha bridge hbridge_path hbridge_outside hbridge_clean
      tail htail_path htail_outside htail_clean hc_bridge hbridge_tail
  · exact Tripod.liftAllNilOfSplicedStrictRightArmTransition
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts ha huStrict bridge hbridge_path hbridge_outside
      hbridge_clean tail htail_path htail_outside htail_clean hc_bridge
      hbridge_tail

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
