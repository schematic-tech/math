import Schematic.Math.GraphTheory.Minors.Society.Terminal.CarrierTails
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SplicedTransitions

/-!
Terminal common-end rerouting and rebuilt-linkage normalization.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

omit [DecidableEq V] in
/-- Source-style terminal common-left rerouting.  An arbitrary simple outside
right-to-left bridge is normalized to consecutive carrier contacts; the
transition is then handled either by the finite exchange dispatcher or by the
first-intersection splice. -/
theorem Tripod.liftAllNilOfOutsideRightToLeftBridge
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
    {a : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hright_prefix_outside : forall (r : Fin 3) (w : V)
      (hw : w ∈ (T.rightToAttach r).support),
      w ≠ T.attach r -> forall z : V,
        z ∈ ((T.rightToAttach r).takeUntil w hw).support -> z ∈ P.outside)
    (hleft_prefix_outside : forall (r : Fin 3) (w : V)
      (hw : w ∈ (T.leftToAttach r).support),
      w ≠ T.attach r -> forall z : V,
        z ∈ ((T.leftToAttach r).takeUntil w hw).support -> z ∈ P.outside)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside) :
    Nonempty S.Tripod := by
  rcases Tripod.exists_clean_rightArm_to_leftArm_transition
      P T hlegs_nil (fun r => by
        rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
        · simpa [hri] using hi
        · rcases hrjk with hrj | hrk
          · simpa [hrj] using hj
          · simpa [hrk] using hk)
      bridge hbridge_path hbridge_outside with
    ⟨u, v, transition, huContact, hvContact, _huv,
      htransitionPath, htransitionOutside, htransitionClean⟩
  rcases Tripod.liftAllNilOfCleanTransitionOrNonleftIntersection
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q ha hq_path hq_outside hq_clean huContact hvContact
      hright_prefix_outside hleft_prefix_outside transition htransitionPath
      htransitionOutside htransitionClean with htripod | hintersection
  · exact htripod
  · rcases hintersection with ⟨d, hdTransition, hdQ, hdNe⟩
    exact Tripod.liftAllNilOfNonleftTransitionIntersection
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q ha hq_path hq_outside hq_clean huContact hvContact
      transition htransitionPath htransitionOutside htransitionClean
      hdTransition hdQ hdNe

omit [DecidableEq V] in
/-- The shared-component branch of the all-collapsed common-end argument.

Two carrier-clean escape paths start at the common ends of the old theta.  If
they meet, stop the right path at its first contact `c` with the left path.
The two prefixes form a fourth `left`--`right` rim, with `c` as its attachment
and the remaining left-path suffix as its boundary leg.  Two old rims retain
the first and last ordered collapsed feet and use the two disjoint tails of
the induced cut path as their ambient boundary legs. -/
theorem Tripod.liftAllNilOfIntersectingCommonEndpointTails
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a b : V}
    (qLeft : S.graph.Walk T.left a)
    (qRight : S.graph.Walk T.right b)
    (ha : a ∈ P.leftBoundaryArc)
    (hqLeft_path : qLeft.IsPath)
    (hqRight_path : qRight.IsPath)
    (hqLeft_outside : forall z : V, z ∈ qLeft.support -> z ∈ P.outside)
    (hqRight_outside : forall z : V, z ∈ qRight.support -> z ∈ P.outside)
    (hqLeft_clean :
      forall z : V, z ∈ qLeft.support -> z ∈ T.vertexSet -> z = T.left)
    (hqRight_clean :
      forall z : V, z ∈ qRight.support -> z ∈ T.vertexSet -> z = T.right)
    (hcontact : Exists fun c : V =>
      c ∈ qLeft.support ∧ c ∈ qRight.support) :
    Nonempty S.Tripod := by
  classical
  obtain ⟨c, hcLeft, rightPrefix, hrightPrefix_path,
      hrightPrefix_subset, hfirst⟩ :=
    exists_first_mutual_contact_prefix qLeft qRight hqRight_path hcontact
  let leftPrefix : S.graph.Walk T.left c := qLeft.takeUntil c hcLeft
  let leftSuffix : S.graph.Walk c a := qLeft.dropUntil c hcLeft
  let externalRim : S.graph.Walk T.left T.right :=
    leftPrefix.append rightPrefix.reverse
  have hcRightPrefix : c ∈ rightPrefix.support :=
    rightPrefix.end_mem_support
  have hcRight : c ∈ qRight.support :=
    hrightPrefix_subset c hcRightPrefix
  have hc_ne_left : c ≠ T.left := by
    intro hc
    have hc_right : c = T.right :=
      hqRight_clean c hcRight (by simp [hc])
    exact T.left_ne_right (hc.symm.trans hc_right)
  have hc_ne_right : c ≠ T.right := by
    intro hc
    have hc_left : c = T.left :=
      hqLeft_clean c hcLeft (by simp [hc])
    exact T.left_ne_right (hc_left.symm.trans hc)
  have hexternal_path : externalRim.IsPath := by
    apply Walk.IsPath.append_of_support_inter_eq_endpoint
      (by simpa [leftPrefix] using hqLeft_path.takeUntil hcLeft)
      hrightPrefix_path.reverse
    intro z hzLeft hzRight
    apply hfirst z
    · simpa [SimpleGraph.Walk.support_reverse] using hzRight
    · exact SimpleGraph.Walk.support_takeUntil_subset qLeft hcLeft
        (by simpa [leftPrefix] using hzLeft)
  have hc_external_internal : c ∈ Walk.InternalVertices externalRim := by
    refine ⟨?_, hc_ne_left, hc_ne_right⟩
    simp only [externalRim, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (by simp [leftPrefix])
  have hexternal_outside :
      forall z : V, z ∈ externalRim.support -> z ∈ P.outside := by
    intro z hz
    simp only [externalRim, SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hzLeft | hzRight
    · exact hqLeft_outside z
        (SimpleGraph.Walk.support_takeUntil_subset qLeft hcLeft
          (by simpa [leftPrefix] using hzLeft))
    · exact hqRight_outside z
        (hrightPrefix_subset z (by
          simpa [SimpleGraph.Walk.support_reverse] using hzRight))
  have hexternal_old_internal_disjoint (r : Fin 3) :
      Disjoint (Walk.InternalVertices externalRim)
        (Walk.InternalVertices ((T.rim r).mapLe hgraph)) := by
    rw [Set.disjoint_left]
    intro z hzExternal hzOld
    have hzOldT : z ∈ T.vertexSet := by
      apply T.rim_mem_vertexSet (i := r)
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzOld.1
    have hzExternalSupport : z ∈ externalRim.support := hzExternal.1
    change z ∈ (leftPrefix.append rightPrefix.reverse).support at hzExternalSupport
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzExternalSupport
    rcases hzExternalSupport with hzLeft | hzRight
    · have hzqLeft : z ∈ qLeft.support :=
        SimpleGraph.Walk.support_takeUntil_subset qLeft hcLeft
          (by simpa [leftPrefix] using hzLeft)
      exact hzExternal.2.1 (hqLeft_clean z hzqLeft hzOldT)
    · have hzqRight : z ∈ qRight.support :=
        hrightPrefix_subset z (by
          simpa [SimpleGraph.Walk.support_reverse] using hzRight)
      exact hzExternal.2.2 (hqRight_clean z hzqRight hzOldT)
  let newRim : Fin 3 -> S.graph.Walk T.left T.right
    | 0 => (T.rim i).mapLe hgraph
    | 1 => externalRim
    | 2 => (T.rim k).mapLe hgraph
  let newAttach : Fin 3 -> V
    | 0 => T.attach i
    | 1 => c
    | 2 => T.attach k
  let newLeg : forall r : Fin 3,
      S.graph.Walk (newAttach r) (P.boundaryTriple a r)
    | 0 =>
        (P.pathTailToStart hi).copy
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl
    | 1 => leftSuffix
    | 2 =>
        (P.pathTailToEnd hk).copy
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl
  have hleft_not_suffix : T.left ∉ leftSuffix.support := by
    simpa [leftSuffix] using
      Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        hqLeft_path hcLeft hc_ne_left
  refine ⟨{
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := newRim
    rim_isPath := ?_
    attach := newAttach
    attach_mem_rim := ?_
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := newLeg
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }⟩
  · intro r
    fin_cases r
    · simpa [newRim] using SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
    · simpa [newRim] using hexternal_path
    · simpa [newRim] using SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath k)
  · intro r
    fin_cases r
    · simpa [newAttach, newRim, Walk.InternalVertices,
        SimpleGraph.Walk.support_mapLe_eq_support] using T.attach_mem_rim i
    · simpa [newAttach, newRim] using hc_external_internal
    · simpa [newAttach, newRim, Walk.InternalVertices,
        SimpleGraph.Walk.support_mapLe_eq_support] using T.attach_mem_rim k
  · intro r
    fin_cases r
    · simpa [newLeg, GMIX24CutPath.boundaryTriple] using
        (SimpleGraph.Walk.isPath_copy
          (P.pathTailToStart hi)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl).mpr
          (P.pathTailToStart_isPath hi)
    · simpa [newLeg, leftSuffix] using hqLeft_path.dropUntil hcLeft
    · simpa [newLeg, GMIX24CutPath.boundaryTriple] using
        (SimpleGraph.Walk.isPath_copy
          (P.pathTailToEnd hk)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
          (P.pathTailToEnd_isPath hk)
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact False.elim (hrs rfl)
    · simpa [newRim] using (hexternal_old_internal_disjoint i).symm
    · simpa [newRim, Walk.InternalVertices,
        SimpleGraph.Walk.support_mapLe_eq_support] using
        T.rim_internals_disjoint i k hik
    · simpa [newRim] using hexternal_old_internal_disjoint i
    · exact False.elim (hrs rfl)
    · simpa [newRim] using hexternal_old_internal_disjoint k
    · simpa [newRim, Walk.InternalVertices,
        SimpleGraph.Walk.support_mapLe_eq_support] using
        (T.rim_internals_disjoint i k hik).symm
    · simpa [newRim] using (hexternal_old_internal_disjoint k).symm
    · exact False.elim (hrs rfl)
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact False.elim (hrs rfl)
    · rw [Set.disjoint_left]
      intro z hzStart hzSuffix
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z (by
          simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzStart)
      exact (hqLeft_outside z
        (SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
          (by simpa [newLeg, leftSuffix] using hzSuffix))).2 hzPath
    · simpa [newLeg, GMIX24CutPath.boundaryTriple] using
        P.pathTailToStart_support_disjoint_pathTailToEnd hi hk
          (lt_trans hij_order hjk_order)
    · rw [Set.disjoint_left]
      intro z hzSuffix hzStart
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z (by
          simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzStart)
      exact (hqLeft_outside z
        (SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
          (by simpa [newLeg, leftSuffix] using hzSuffix))).2 hzPath
    · exact False.elim (hrs rfl)
    · rw [Set.disjoint_left]
      intro z hzSuffix hzEnd
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hk z (by
          simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzEnd)
      exact (hqLeft_outside z
        (SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
          (by simpa [newLeg, leftSuffix] using hzSuffix))).2 hzPath
    · simpa [newLeg, GMIX24CutPath.boundaryTriple] using
        (P.pathTailToStart_support_disjoint_pathTailToEnd hi hk
          (lt_trans hij_order hjk_order)).symm
    · rw [Set.disjoint_left]
      intro z hzEnd hzSuffix
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hk z (by
          simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzEnd)
      exact (hqLeft_outside z
        (SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
          (by simpa [newLeg, leftSuffix] using hzSuffix))).2 hzPath
    · exact False.elim (hrs rfl)
  · intro r s z hzLeg hzRim
    fin_cases r <;> fin_cases s
    · have hzTail : z ∈ (P.pathTailToStart hi).support := by
        simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzLeg
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := i) (by
          simpa [newRim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim)
      simpa [newAttach, (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail hzT
    · have hzTail : z ∈ (P.pathTailToStart hi).support := by
        simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzLeg
      have hzPath := P.pathTailToStart_support_subset_pathSet hi z hzTail
      exact False.elim ((hexternal_outside z (by simpa [newRim] using hzRim)).2 hzPath)
    · have hzTail : z ∈ (P.pathTailToStart hi).support := by
        simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzLeg
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := k) (by
          simpa [newRim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim)
      simpa [newAttach, (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail hzT
    · have hzqLeft : z ∈ qLeft.support :=
        SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
          (by simpa [newLeg, leftSuffix] using hzLeg)
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := i) (by
          simpa [newRim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim)
      exact False.elim (hleft_not_suffix (by
        have hzLeft := hqLeft_clean z hzqLeft hzT
        simpa [hzLeft, newLeg, leftSuffix] using hzLeg))
    · have hzSuffix : z ∈ leftSuffix.support := by
        simpa [newLeg] using hzLeg
      simp only [newRim, externalRim,
        SimpleGraph.Walk.mem_support_append_iff] at hzRim
      rcases hzRim with hzLeftPrefix | hzRightPrefix
      · exact Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          hqLeft_path hcLeft (by simpa [leftPrefix] using hzLeftPrefix)
            (by simpa [leftSuffix] using hzSuffix)
      · apply hfirst z
        · simpa [SimpleGraph.Walk.support_reverse] using hzRightPrefix
        · exact SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
            hzSuffix
    · have hzqLeft : z ∈ qLeft.support :=
        SimpleGraph.Walk.support_dropUntil_subset qLeft hcLeft
          (by simpa [newLeg, leftSuffix] using hzLeg)
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := k) (by
          simpa [newRim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim)
      exact False.elim (hleft_not_suffix (by
        have hzLeft := hqLeft_clean z hzqLeft hzT
        simpa [hzLeft, newLeg, leftSuffix] using hzLeg))
    · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
        simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzLeg
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := i) (by
          simpa [newRim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim)
      simpa [newAttach, (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail hzT
    · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
        simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzLeg
      have hzPath := P.pathTailToEnd_support_subset_pathSet hk z hzTail
      exact False.elim ((hexternal_outside z (by simpa [newRim] using hzRim)).2 hzPath)
    · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
        simpa [newLeg, GMIX24CutPath.boundaryTriple] using hzLeg
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := k) (by
          simpa [newRim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim)
      simpa [newAttach, (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail hzT

omit [DecidableEq V] in
/-- The exact common-end escape configuration is impossible in a society
with neither a cross nor a tripod.

This is the complete final alternative in the printed GM IX `(2.4)`
side-tripod paragraph.  Two carrier-clean paths leave the two common ends of
the old theta.  If they meet, their first common vertex gives the fourth rim
used by `liftAllNilOfIntersectingCommonEndpointTails`; if they do not meet,
the two paths and the two outer tails of the induced cut path give a cross. -/
theorem Tripod.exactCommonEndpointTails_impossible
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a b : V}
    (qLeft : S.graph.Walk T.left a)
    (qRight : S.graph.Walk T.right b)
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hqLeft_path : qLeft.IsPath)
    (hqRight_path : qRight.IsPath)
    (hqLeft_outside : forall z : V, z ∈ qLeft.support -> z ∈ P.outside)
    (hqRight_outside : forall z : V, z ∈ qRight.support -> z ∈ P.outside)
    (hqLeft_clean :
      forall z : V, z ∈ qLeft.support -> z ∈ T.vertexSet -> z = T.left)
    (hqRight_clean :
      forall z : V, z ∈ qRight.support -> z ∈ T.vertexSet -> z = T.right)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod)) :
    False := by
  classical
  by_cases hcontact : Exists fun c : V =>
      c ∈ qLeft.support ∧ c ∈ qRight.support
  · exact hno_tripod
      (Tripod.liftAllNilOfIntersectingCommonEndpointTails
        P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
        hij_order hjk_order hpath_contacts qLeft qRight ha
        hqLeft_path hqRight_path hqLeft_outside hqRight_outside
        hqLeft_clean hqRight_clean hcontact)
  · have hdisjoint :
        Disjoint {z : V | z ∈ qLeft.support}
          {z : V | z ∈ qRight.support} := by
      rw [Set.disjoint_left]
      intro z hzLeft hzRight
      exact hcontact ⟨z, hzLeft, hzRight⟩
    exact hno_cross
      (Tripod.crossOfDisjointCommonEndpointTails
        P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
        hij_order hjk_order hpath_contacts qLeft qRight ha hb
        hqLeft_path hqRight_path hqLeft_outside hqRight_outside
        hqLeft_clean hqRight_clean hdisjoint)

omit [DecidableEq V] in
/-- The distinct-common-end branch after independently normalizing the two
caught-component escapes.

Each normalized source is assumed to be an old theta end.  If the two sources
are distinct, they are the two ends in one order or the other, so the exact
common-end alternative applies directly (with the two tails exchanged in the
second order). -/
theorem Tripod.distinctEndpointResidualTails_impossible
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x y a b : V}
    (qX : S.graph.Walk x a)
    (qY : S.graph.Walk y b)
    (hxEnd : x = T.left ∨ x = T.right)
    (hyEnd : y = T.left ∨ y = T.right)
    (hxy : x ≠ y)
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hqX_path : qX.IsPath)
    (hqY_path : qY.IsPath)
    (hqX_outside : forall z : V, z ∈ qX.support -> z ∈ P.outside)
    (hqY_outside : forall z : V, z ∈ qY.support -> z ∈ P.outside)
    (hqX_clean :
      forall z : V, z ∈ qX.support -> z ∈ T.vertexSet -> z = x)
    (hqY_clean :
      forall z : V, z ∈ qY.support -> z ∈ T.vertexSet -> z = y)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod)) :
    False := by
  rcases hxEnd with hxLeft | hxRight <;>
    rcases hyEnd with hyLeft | hyRight
  · exact False.elim (hxy (hxLeft.trans hyLeft.symm))
  · subst x
    subst y
    exact
      Tripod.exactCommonEndpointTails_impossible
        P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
        hij_order hjk_order hpath_contacts qX qY ha hb
        hqX_path hqY_path hqX_outside hqY_outside
        hqX_clean hqY_clean hno_cross hno_tripod
  · subst x
    subst y
    exact
      Tripod.exactCommonEndpointTails_impossible
        P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
        hij_order hjk_order hpath_contacts qY qX hb ha
        hqY_path hqX_path hqY_outside hqX_outside
        hqY_clean hqX_clean hno_cross hno_tripod
  · exact False.elim (hxy (hxRight.trans hyRight.symm))

omit [DecidableEq V] in
/-- Every vertex of the theta rebuilt in the double-outer-collapsed branch is
either on the induced cut path or already belongs to the old side tripod.

This is the precise carrier comparison needed for the source path `Q`.  It is
strictly weaker than the discarded global path-contact normalization: old rim
vertices are allowed to lie on `P`; the conclusion merely records the two
pieces from which the rebuilt theta was assembled. -/
theorem Tripod.outerNilCommonLeftEndpointRim_mem_pathSet_or_vertexSet
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {z : V} :
    (Exists fun r : Fin 3 =>
      z ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r).support) ->
      z ∈ P.pathSet ∨ z ∈ T.vertexSet := by
  rintro ⟨r, hzr⟩
  fin_cases r
  · left
    apply
      P.pathSegmentBetween_support_subset_pathSet hi hk
        (Nat.le_of_lt (lt_trans hij_order hjk_order)) z
    simpa [Tripod.outerNilCommonLeftEndpointRim] using hzr
  · right
    have hzOld : z ∈ (T.attachToAttachViaLeft i k).support := by
      simpa [Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases T.attachToAttachViaLeft_support_cases hzOld with hzi | hzk
    · exact T.rim_mem_vertexSet (i := i) hzi
    · exact T.rim_mem_vertexSet (i := k) hzk
  · right
    have hzOld : z ∈ (T.attachToAttachViaRight i k).support := by
      simpa [Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases T.attachToAttachViaRight_support_cases hzOld with hzi | hzk
    · exact T.rim_mem_vertexSet (i := i) hzi
    · exact T.rim_mem_vertexSet (i := k) hzk

omit [DecidableEq V] in
/-- The source clean tail in GM IX `(2.4)` is also clean with respect to the
rebuilt theta in the double-outer-collapsed branch.

The cut-path part of the rebuilt carrier is excluded because `Q` lies in
`G - V(P)`.  Its two remaining rims lie in the old tripod carrier, where the
last-contact construction already gives cleanliness. -/
theorem Tripod.outerNilCommonLeftEndpoint_clean_tail
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x a : V} (q : S.graph.Walk x a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    forall z : V,
      z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈
            (T.outerNilCommonLeftEndpointRim P hgraph
              hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r).support) ->
          z = x := by
  intro z hzq hzRebuilt
  rcases
      GMIX24SourceProof.Tripod.outerNilCommonLeftEndpointRim_mem_pathSet_or_vertexSet
        P T hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order hzRebuilt with
    hzPath | hzT
  · exact False.elim ((hq_outside z hzq).2 hzPath)
  · exact hq_clean z hzq hzT

omit [DecidableEq V] in
/-- The common-end/nil-arm residual point used by the source proof lies on
one of the three rebuilt rims.

For a common old theta end this is one of the two old-side rebuilt rims.  An
internal point of either outer old rim lies on one side or the other of its
attachment and hence lies on the corresponding rebuilt old-side rim. -/
theorem Tripod.outerNilCommonLeftEndpoint_residual_mem_carrier
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {x : V}
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    Exists fun r : Fin 3 =>
      x ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r).support := by
  rcases hresidual with hend | hinternal
  · rcases hend with hxLeft | hxRight
    · refine ⟨1, ?_⟩
      simpa [Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support, hxLeft] using
        Walk.internalVertices_subset_support
          (T.attachToAttachViaLeft i k)
          (T.left_mem_internal_attachToAttachViaLeft i k)
    · refine ⟨2, ?_⟩
      simpa [Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support, hxRight] using
        Walk.internalVertices_subset_support
          (T.attachToAttachViaRight i k)
          (T.right_mem_internal_attachToAttachViaRight i k)
  · rcases hinternal with ⟨r, hr, hxr, _hrNil⟩
    have hsplit := Nat.le_total
      (Walk.supportIndex (T.rim r) x)
      (Walk.supportIndex (T.rim r) (T.attach r))
    rcases hsplit with hbefore | hafter
    · have hxArm : x ∈ (T.leftToAttach r).support :=
        T.mem_leftToAttach_of_rim_supportIndex_le_attach hxr.1 hbefore
      rcases hr with hri | hrk
      · subst r
        refine ⟨1, ?_⟩
        have hxVia : x ∈ (T.attachToAttachViaLeft i k).support := by
          rw [Tripod.attachToAttachViaLeft,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hxArm)
        simpa [Tripod.outerNilCommonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hxVia
      · subst r
        refine ⟨1, ?_⟩
        have hxVia : x ∈ (T.attachToAttachViaLeft i k).support := by
          rw [Tripod.attachToAttachViaLeft,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hxArm
        simpa [Tripod.outerNilCommonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hxVia
    · have hxArm : x ∈ (T.attachToRight r).support :=
        T.mem_attachToRight_of_attach_supportIndex_le_rim hxr.1 hafter
      rcases hr with hri | hrk
      · subst r
        refine ⟨2, ?_⟩
        have hxVia : x ∈ (T.attachToAttachViaRight i k).support := by
          rw [Tripod.attachToAttachViaRight,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl hxArm
        simpa [Tripod.outerNilCommonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hxVia
      · subst r
        refine ⟨2, ?_⟩
        have hxVia : x ∈ (T.attachToAttachViaRight i k).support := by
          rw [Tripod.attachToAttachViaRight,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hxArm)
        simpa [Tripod.outerNilCommonLeftEndpointRim,
          SimpleGraph.Walk.support_mapLe_eq_support] using hxVia

/-- Classify an arbitrary clean linkage out of the rebuilt all-collapsed
theta.  If its three sources occupy three distinct rim interiors, the linkage
itself is an ambient tripod.  Under ambient tripod-freeness, a source must
therefore be a rebuilt-theta endpoint or two sources must occupy one rim. -/
theorem Tripod.outerNilRebuiltLinkage_endpoint_or_same_rim_of_no_tripod
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (M : ThreeSetLinkage S.graph
      {z : V | Exists fun r : Fin 3 =>
        z ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r).support}
      S.boundarySet) :
    (Exists fun m : Fin 3 =>
      M.source m = T.attach i ∨ M.source m = T.attach k) ∨
      Exists fun a : Fin 3 =>
        Exists fun b : Fin 3 =>
          Exists fun r : Fin 3 =>
            a ≠ b ∧
              M.source a ∈ Walk.InternalVertices
                (T.outerNilCommonLeftEndpointRim P hgraph
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r) ∧
              M.source b ∈ Walk.InternalVertices
                (T.outerNilCommonLeftEndpointRim P hgraph
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order r) := by
  classical
  let rim : Fin 3 -> S.graph.Walk (T.attach i) (T.attach k) :=
    T.outerNilCommonLeftEndpointRim P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
  let carrier : Set V :=
    {z : V | Exists fun r : Fin 3 => z ∈ (rim r).support}
  have hclassify : forall a : Fin 3,
      (M.source a = T.attach i ∨ M.source a = T.attach k) ∨
        Exists fun r : Fin 3 =>
          M.source a ∈ Walk.InternalVertices (rim r) := by
    intro a
    rcases M.source_mem a with ⟨r, hr⟩
    rcases
        Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support hr with
      hinternal | hend
    · exact Or.inr ⟨r, by simpa [rim] using hinternal⟩
    · exact Or.inl hend
  by_cases hend : Exists fun a : Fin 3 =>
      M.source a = T.attach i ∨ M.source a = T.attach k
  · exact Or.inl hend
  · right
    have hinternal : forall a : Fin 3,
        Exists fun r : Fin 3 =>
          M.source a ∈ Walk.InternalVertices (rim r) := by
      intro a
      rcases hclassify a with ha | ha
      · exact False.elim (hend ⟨a, ha⟩)
      · exact ha
    choose rimIndex hrimIndex using hinternal
    by_cases hinjective : Function.Injective rimIndex
    · let linkage : ThreeVertexLinkage S.graph M.source M.target := {
        targetEquiv := Equiv.refl (Fin 3)
        path := M.path
        isPath := M.isPath
        pairwise_vertex_disjoint := M.pairwise_vertex_disjoint
      }
      have hambient : S.Tripod := by
        apply
          Tripod.ofThreeVertexLinkage
            (T.attach i) (T.attach k) (T.attach_ne_of_ne hik)
            (fun a => rim (rimIndex a))
            (fun a => by
              simpa [rim] using
                T.outerNilCommonLeftEndpointRim_isPath P hgraph hik
                  hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
                  (rimIndex a))
            M.source hrimIndex M.target M.target_mem M.target_injective linkage
        · intro a b hab
          exact
            T.outerNilCommonLeftEndpointRims_internal_disjoint
              P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
              hij_order hjk_order hpath_contacts
              (rimIndex a) (rimIndex b) (fun h => hab (hinjective h))
        · intro a b z hzPath hzRim
          apply M.source_clean a z hzPath
          exact ⟨rimIndex b, by simpa [rim] using hzRim⟩
      exact False.elim (hno_tripod ⟨hambient⟩)
    · rcases Function.not_injective_iff.mp hinjective with
        ⟨a, b, habRim, hab⟩
      exact
        ⟨a, b, rimIndex a, hab,
          by simpa [rim] using hrimIndex a,
          by simpa [rim, habRim] using hrimIndex b⟩

omit [DecidableEq V] in
/-- A retained source and retained target in a completed set-linkage are
either paired by one linkage path, or they belong to two distinct, hence
vertex-disjoint, linkage paths.

GM IX `(2.2)` preserves endpoint sets rather than a prescribed matching.  This
is the exact permutation-invariant split needed when expanding the "it follows
easily" sentence in `(2.4)`: in the rematched branch the two linkage paths are
available as genuinely disjoint rerouting paths. -/
theorem ThreeSetLinkage.selected_source_target_paired_or_disjoint
    {G : SimpleGraph V} {X Y : Set V}
    (M : ThreeSetLinkage G X Y)
    {x b : V}
    (hx : x ∈ Set.range M.source)
    (hb : b ∈ Set.range M.target) :
    (Exists fun m : Fin 3 => M.source m = x ∧ M.target m = b) ∨
      Exists fun m : Fin 3 =>
        Exists fun n : Fin 3 =>
          m ≠ n ∧ M.source m = x ∧ M.target n = b ∧
            Disjoint {z : V | z ∈ (M.path m).support}
              {z : V | z ∈ (M.path n).support} := by
  rcases hx with ⟨m, hm⟩
  rcases hb with ⟨n, hn⟩
  by_cases hmn : m = n
  · subst n
    exact Or.inl ⟨m, hm, hn⟩
  · exact Or.inr ⟨m, n, hmn, hm, hn,
      M.pairwise_vertex_disjoint m n hmn⟩

/-- Apply society three-connectivity directly to the three attachments of the
rebuilt theta in the double-outer-collapsed case.

The resulting ordinary linkage is normalized against the union of the three
rebuilt rims, as required by the GM IX `X -> Ω` convention. If its three
normalized sources lie internally on three distinct rebuilt rims, they give
the forbidden ambient tripod immediately. Thus ambient tripod-freeness leaves
exactly the genuine topological residual: a source at a rebuilt-theta end, or
two sources in the same rebuilt rim. This avoids the obsolete demand that a
preselected rim-deleted graph itself be three-connected. -/
theorem ThreeConnected.exists_outerNilRebuiltLinkage_endpoint_or_same_rim_of_no_tripod
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    let rim : Fin 3 -> S.graph.Walk (T.attach i) (T.attach k) :=
      T.outerNilCommonLeftEndpointRim P hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
    let carrier : Set V :=
      {z : V | Exists fun r : Fin 3 => z ∈ (rim r).support}
    Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
      (Exists fun m : Fin 3 =>
        M.source m = T.attach i ∨ M.source m = T.attach k) ∨
        Exists fun a : Fin 3 =>
          Exists fun b : Fin 3 =>
            Exists fun r : Fin 3 =>
              a ≠ b ∧
                M.source a ∈ Walk.InternalVertices (rim r) ∧
                  M.source b ∈ Walk.InternalVertices (rim r) := by
  classical
  let rim : Fin 3 -> S.graph.Walk (T.attach i) (T.attach k) :=
    T.outerNilCommonLeftEndpointRim P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
  let carrier : Set V :=
    {z : V | Exists fun r : Fin 3 => z ∈ (rim r).support}
  have hleft_injective :
      Function.Injective (T.outerNilCommonLeftEndpointAttach j) :=
    T.outerNilCommonLeftEndpointAttach_injective j
  have hleft_active :
      forall r : Fin 3,
        T.outerNilCommonLeftEndpointAttach j r ∈ S.activeSet :=
    T.outerNilCommonLeftEndpointAttach_mem_activeSet P hgraph hj
  rcases
      hthree.hasThreeVertexLinkageToBoundary hleft_injective hleft_active with
    ⟨target, htarget, ⟨L⟩⟩
  have hleft_carrier :
      forall r : Fin 3,
        T.outerNilCommonLeftEndpointAttach j r ∈ carrier := by
    intro r
    exact ⟨r, Walk.internalVertices_subset_support (rim r)
      (by
        simpa [rim] using
          T.outerNilCommonLeftEndpointAttach_mem_rim P hgraph
            hleg_i_nil hleg_k_nil hi hj hk hij_order hjk_order r)⟩
  let M : ThreeSetLinkage S.graph carrier S.boundarySet :=
    L.toThreeSetLinkage carrier S.boundarySet hleft_carrier htarget
  refine ⟨M, ?_⟩
  simpa [carrier, rim] using
    GMIX24SourceProof.Tripod.outerNilRebuiltLinkage_endpoint_or_same_rim_of_no_tripod
      hno_tripod P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts M

/-- Retain the source proof's clean path `Q` while completing a linkage out of
the rebuilt theta.

The raw end of `Q` is normalized to its first ambient-boundary contact.  Its
source remains the original last carrier contact `x`, because `Q` is clean for
the rebuilt carrier.  GM IX `(2.2)` then extends this selected path to three
clean rebuilt-carrier-to-boundary paths without losing either endpoint. -/
theorem ThreeConnected.exists_outerNilRebuiltLinkage_preserving_clean_tail
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall z : V, z ∈ q.support -> z ∈ P.leftSide)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    let rim : Fin 3 -> S.graph.Walk (T.attach i) (T.attach k) :=
      T.outerNilCommonLeftEndpointRim P hgraph
        hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
    let carrier : Set V :=
      {z : V | Exists fun r : Fin 3 => z ∈ (rim r).support}
    Exists fun b : V =>
      b ∈ P.leftBoundaryArc ∧
        Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
          x ∈ Set.range M.source ∧ b ∈ Set.range M.target := by
  classical
  let rim : Fin 3 -> S.graph.Walk (T.attach i) (T.attach k) :=
    T.outerNilCommonLeftEndpointRim P hgraph
      hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
  let carrier : Set V :=
    {z : V | Exists fun r : Fin 3 => z ∈ (rim r).support}
  have hxCarrier : x ∈ carrier := by
    simpa [carrier, rim] using
      GMIX24SourceProof.Tripod.outerNilCommonLeftEndpoint_residual_mem_carrier
        P T hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
        hresidual
  have hqCarrierClean :
      forall z : V, z ∈ q.support -> z ∈ carrier -> z = x := by
    intro z hzq hzCarrier
    apply
      GMIX24SourceProof.Tripod.outerNilCommonLeftEndpoint_clean_tail
        P T hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
        q hq_outside hq_clean z hzq
    simpa [carrier, rim] using hzCarrier
  rcases
      Walk.IsPath.exists_setToSetPathData hq_path carrier S.boundarySet
        hxCarrier (P.leftBoundaryArc_subset ha) with
    ⟨D⟩
  have hDsource : D.source = x :=
    hqCarrierClean D.source
      (D.support_subset D.path.start_mem_support) D.source_mem
  have hDtargetLeft : D.target ∈ P.leftSide :=
    hq_side D.target (D.support_subset D.path.end_mem_support)
  have hDtargetArc : D.target ∈ P.leftBoundaryArc :=
    P.boundary_mem_leftSide_of_no_cross
      hno_cross D.target_mem hDtargetLeft
  let Lselected : PartialSetLinkage S.graph carrier S.boundarySet 1 :=
    PartialSetLinkage.ofOnePath D.path D.isPath D.source_mem D.target_mem
      D.source_clean D.target_clean
  rcases
      GMIX24SourceProof.ThreeConnected.exists_outerNilRebuiltLinkage_endpoint_or_same_rim_of_no_tripod
        hthree hno_tripod P T hgraph hij hik hjk hi hj hk hleg_i_nil hleg_k_nil
        hij_order hjk_order hpath_contacts with
    ⟨F, _hFresidual⟩
  rcases Lselected.exists_threeSetLinkage_extending (by omega) F with
    ⟨M, hsource, htarget⟩
  refine ⟨D.target, hDtargetArc, M, hsource ?_, htarget ?_⟩
  · exact ⟨0, by simpa [Lselected, PartialSetLinkage.ofOnePath] using hDsource⟩
  · exact ⟨0, rfl⟩

private theorem exists_carrierLinkage_preserving_clean_paths
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {x a e : V} (q : S.graph.Walk x a)
    (hxT : x ∈ T.vertexSet)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall z : V, z ∈ q.support -> z ∈ P.leftSide)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x)
    {r : Fin 3}
    (hr : T.boundary r ∈ P.pathSet)
    (p : S.graph.Walk (T.boundary r) e)
    (he : e ∈ S.boundarySet)
    (hp_path : p.IsPath)
    (hp_pathSet : forall z : V, z ∈ p.support -> z ∈ P.pathSet)
    (hp_source_clean :
      forall z : V, z ∈ p.support -> z ∈ T.vertexSet ->
        z = T.boundary r)
    (hp_target_clean :
      forall z : V, z ∈ p.support -> z ∈ S.boundarySet -> z = e)
    (hleft_ne_e : forall b : V, b ∈ P.leftBoundaryArc -> b ≠ e) :
    let carrier : Set V := T.vertexSet
    Exists fun b : V =>
      b ∈ P.leftBoundaryArc ∧
        Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
          x ∈ Set.range M.source ∧
            T.boundary r ∈ Set.range M.source ∧
              b ∈ Set.range M.target ∧ e ∈ Set.range M.target := by
  classical
  let carrier : Set V := T.vertexSet
  have hxCarrier : x ∈ carrier := by
    simpa [carrier] using hxT
  have hqCarrierClean :
      forall z : V, z ∈ q.support -> z ∈ carrier -> z = x := by
    simpa [carrier] using hq_clean
  rcases
      Walk.IsPath.exists_setToSetPathData hq_path carrier S.boundarySet
        hxCarrier (P.leftBoundaryArc_subset ha) with
    ⟨D⟩
  have hDsource : D.source = x :=
    hqCarrierClean D.source
      (D.support_subset D.path.start_mem_support) D.source_mem
  have hDtargetLeft : D.target ∈ P.leftSide :=
    hq_side D.target (D.support_subset D.path.end_mem_support)
  have hDtargetArc : D.target ∈ P.leftBoundaryArc :=
    P.boundary_mem_leftSide_of_no_cross
      hno_cross D.target_mem hDtargetLeft
  have hrCarrier : T.boundary r ∈ carrier := by
    simpa [carrier] using T.boundary_mem_vertexSet r
  have hpSourceClean :
      forall z : V, z ∈ p.support -> z ∈ carrier ->
        z = T.boundary r := by
    simpa [carrier] using hp_source_clean
  have hsource_ne : D.source ≠ T.boundary r := by
    intro h
    have hDoutside : D.source ∈ P.outside :=
      hq_outside D.source (D.support_subset D.path.start_mem_support)
    exact hDoutside.2 (by simpa [h] using hr)
  have htarget_ne : D.target ≠ e := hleft_ne_e D.target hDtargetArc
  have hdisjoint :
      Disjoint {z : V | z ∈ D.path.support}
        {z : V | z ∈ p.support} := by
    rw [Set.disjoint_left]
    intro z hzD hzp
    have hzOutside : z ∈ P.outside :=
      hq_outside z (D.support_subset hzD)
    exact hzOutside.2 (hp_pathSet z hzp)
  let Lselected : PartialSetLinkage S.graph carrier S.boundarySet 2 :=
    PartialSetLinkage.ofTwoPaths D.path p D.isPath hp_path
      D.source_mem hrCarrier D.target_mem he hsource_ne htarget_ne hdisjoint
      D.source_clean hpSourceClean D.target_clean hp_target_clean
  rcases hthree.hasMappedTripodAttachmentLinkageToBoundary T hgraph with
    ⟨right, hrightBoundary, ⟨Lfull⟩⟩
  let F : ThreeSetLinkage S.graph carrier S.boundarySet :=
    Lfull.toThreeSetLinkage carrier S.boundarySet
      (by
        intro s
        simpa [carrier] using T.attach_mem_vertexSet s)
      hrightBoundary
  rcases Lselected.exists_threeSetLinkage_extending (by omega) F with
    ⟨M, hsource, htarget⟩
  refine ⟨D.target, hDtargetArc, M, hsource ?_, hsource ?_,
    htarget ?_, htarget ?_⟩
  · exact ⟨0, by simpa [Lselected, PartialSetLinkage.ofTwoPaths] using hDsource⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- Complete the source `Q` path and one ordered cut-path tail simultaneously.

This is the order-two GM IX `(2.2)` exchange used in the common-end branch of
the side-tripod paragraph.  The raw `Q` path is first shortened to an
old-carrier-to-ambient-boundary path.  Its support remains outside the induced
cut path, so it is disjoint from the selected tail from the first ordered foot
to `P.s`.  Augmentation to order three then retains both source-target pairs.
-/
theorem ThreeConnected.exists_carrierLinkage_preserving_clean_tail_and_start_tail
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
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
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a : V} (q : S.graph.Walk x a)
    (hxT : x ∈ T.vertexSet)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall z : V, z ∈ q.support -> z ∈ P.leftSide)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    let carrier : Set V := T.vertexSet
    Exists fun b : V =>
      b ∈ P.leftBoundaryArc ∧
        Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
          x ∈ Set.range M.source ∧
            T.boundary i ∈ Set.range M.source ∧
              b ∈ Set.range M.target ∧ P.s ∈ Set.range M.target := by
  let p0 : S.graph.Walk (T.boundary i) P.s := P.pathTailToStart hi
  apply exists_carrierLinkage_preserving_clean_paths
    hthree hno_cross P T hgraph q hxT ha hq_path hq_side hq_outside hq_clean
    hi p0 P.s_mem_boundary
  · exact P.pathTailToStart_isPath hi
  · exact P.pathTailToStart_support_subset_pathSet hi
  · intro z hz hzCarrier
    exact P.pathTailToStart_clean_first_foot_of_path_contacts
      T hij hik hjk hi hij_order hjk_order hpath_contacts hz hzCarrier
  · intro z hz hzBoundary
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet hi z hz
    rcases P.boundary_mem_pathSet_eq_s_or_t hzBoundary hzPath with hzs | hzt
    · exact hzs
    · subst z
      have ht_le_i := P.pathTailToStart_supportIndex_le hi hz
      have hi_lt_t := lt_trans hij_order hjk_order
      have hk_le_t := Walk.IsPath.supportIndex_le_end P.path_isPath
        (by simpa [GMIX24CutPath.pathSet] using hk)
      omega
  · exact fun _ hb => P.leftBoundaryArc_ne_s hb

/-- Complete the source `Q` path and the final ordered cut-path tail
simultaneously.

This is the right-hand counterpart of
`exists_carrierLinkage_preserving_clean_tail_and_start_tail`.  It is stated
directly rather than through `P.reverse`, so the resulting linkage remains on
the original old-tripod carrier and can be compared with the start-tail
exchange in the final common-end argument. -/
theorem ThreeConnected.exists_carrierLinkage_preserving_clean_tail_and_end_tail
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
    {x a : V} (q : S.graph.Walk x a)
    (hxT : x ∈ T.vertexSet)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall z : V, z ∈ q.support -> z ∈ P.leftSide)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    let carrier : Set V := T.vertexSet
    Exists fun b : V =>
      b ∈ P.leftBoundaryArc ∧
        Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
          x ∈ Set.range M.source ∧
            T.boundary k ∈ Set.range M.source ∧
              b ∈ Set.range M.target ∧ P.t ∈ Set.range M.target := by
  let p2 : S.graph.Walk (T.boundary k) P.t := P.pathTailToEnd hk
  apply exists_carrierLinkage_preserving_clean_paths
    hthree hno_cross P T hgraph q hxT ha hq_path hq_side hq_outside hq_clean
    hk p2 P.t_mem_boundary
  · exact P.pathTailToEnd_isPath hk
  · exact P.pathTailToEnd_support_subset_pathSet hk
  · intro z hz hzCarrier
    exact P.pathTailToEnd_clean_last_foot_of_path_contacts
      T hij hik hjk hk hij_order hjk_order hpath_contacts hz hzCarrier
  · intro z hz hzBoundary
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet hk z hz
    rcases P.boundary_mem_pathSet_eq_s_or_t hzBoundary hzPath with hzs | hzt
    · subst z
      have hk_le_s := P.pathTailToEnd_supportIndex_le hk hz
      have hi_lt_k := lt_trans hij_order hjk_order
      have hs_le_i := Walk.supportIndex_start_le
        (p := P.path) (x := T.boundary i)
      omega
    · exact hzt
  · exact fun _ hb => P.leftBoundaryArc_ne_t hb


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
