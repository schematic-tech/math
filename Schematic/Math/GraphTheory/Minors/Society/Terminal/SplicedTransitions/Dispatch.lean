import Schematic.Math.GraphTheory.Minors.Society.Terminal.MiddleSplice
import Schematic.Math.GraphTheory.Minors.Society.Terminal.EndpointTransitions

/-!
Finite dispatch and endpoint splicing for clean all-nil transitions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Finite dispatcher for a clean transition whose left contact is strict.
The two contact indices are classified against the three cut-path-ordered
old rims and sent to the checked diagonal/off-diagonal exchange. -/
theorem Tripod.liftAllNilOfCleanTransitionToStrictLeftArm
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
    (hv_contact : Exists fun s : Fin 3 =>
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
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  rcases hv_contact with ⟨s, hvInternal, hvArm, hvNe⟩
  have hs : s = i ∨ s = j ∨ s = k := by
    rcases fin3_eq_of_pairwise (m := s) hij hik hjk with hsi | hsjk
    · exact Or.inl hsi
    · exact Or.inr hsjk
  rcases hu_contact with huRight | ⟨r, huInternal, huArm, huNe⟩
  · subst u
    rcases hs with hsi | hsj | hsk
    · subst s
      exact Tripod.liftAllNilOfRightEndpointToFirstArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        hvArm hvNe hvInternal transition htransition_path
        htransition_outside htransition_clean htransition_q
    · subst s
      exact Tripod.liftAllNilOfRightEndpointToMiddleArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q ha hq_path hq_outside hq_clean
        hvArm hvNe hvInternal transition htransition_path
        htransition_outside htransition_clean htransition_q
    · subst s
      exact Tripod.liftAllNilOfRightEndpointToLastArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        hvArm hvNe hvInternal transition htransition_path
        htransition_outside htransition_clean htransition_q
  · have hr : r = i ∨ r = j ∨ r = k := by
      rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
      · exact Or.inl hri
      · exact Or.inr hrjk
    rcases hr with hri | hrj | hrk <;>
      rcases hs with hsi | hsj | hsk
    · subst r; subst s
      exact Tripod.liftAllNilOfSameFirstArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huNe huInternal hvArm hvNe (Or.inl hvInternal) transition
        htransition_path htransition_outside htransition_clean
        (fun z hzTransition hzQ => False.elim (htransition_q z hzTransition hzQ))
    · subst r; subst s
      exact Tripod.liftAllNilOfFirstToMiddleArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huNe huInternal hvArm hvNe hvInternal transition
        htransition_path htransition_outside htransition_clean htransition_q
    · subst r; subst s
      exact Tripod.liftAllNilOfFirstToLastArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm (Or.inl huInternal) hvArm hvNe hvInternal transition
        htransition_path htransition_outside htransition_clean htransition_q
    · subst r; subst s
      exact Tripod.liftAllNilOfMiddleToFirstArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huNe huInternal (hright_prefix_outside j u huArm huNe)
        hvArm hvNe hvInternal (hleft_prefix_outside i v hvArm hvNe)
        transition htransition_path htransition_outside htransition_clean
        htransition_q
    · subst r; subst s
      exact Tripod.liftAllNilOfSameMiddleArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q ha hq_path hq_outside hq_clean
        huArm huNe (Or.inl huInternal) hvArm hvNe (Or.inl hvInternal) transition
        htransition_path htransition_outside htransition_clean
        (fun z hzTransition hzQ => False.elim (htransition_q z hzTransition hzQ))
    · subst r; subst s
      exact Tripod.liftAllNilOfMiddleToLastArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huNe huInternal (hright_prefix_outside j u huArm huNe)
        hvArm hvNe hvInternal (hleft_prefix_outside k v hvArm hvNe)
        transition htransition_path htransition_outside htransition_clean
        htransition_q
    · subst r; subst s
      exact Tripod.liftAllNilOfLastToFirstArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huInternal hvArm hvNe hvInternal transition
        htransition_path htransition_outside htransition_clean htransition_q
    · subst r; subst s
      exact Tripod.liftAllNilOfLastToMiddleArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huNe huInternal hvArm hvNe hvInternal transition
        htransition_path htransition_outside htransition_clean htransition_q
    · subst r; subst s
      exact Tripod.liftAllNilOfSameLastArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q ha hq_path hq_outside hq_clean
        huArm huNe huInternal hvArm hvNe (Or.inl hvInternal) transition
        htransition_path htransition_outside htransition_clean
        (fun z hzTransition hzQ => False.elim (htransition_q z hzTransition hzQ))

/-- Finite dispatcher for a carrier-clean transition ending at the old left
common end.  A transition starting at the right common end is the clean bridge
case; the other three cases are the diagonal exchanges on the ordered rims. -/
theorem Tripod.liftAllNilOfCleanTransitionToLeftEndpoint
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
    {a u : V}
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
    (transition : S.graph.Walk u T.left)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = T.left)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = T.left) :
    Nonempty S.Tripod := by
  have hleft_ne_attach (r : Fin 3) : T.left ≠ T.attach r := by
    intro h
    exact T.left_ne_boundary r
      (h.trans ((T.leg_nil_iff_boundary_eq_attach r).mp (hlegs_nil r)).symm)
  rcases hu_contact with huRight | ⟨r, huInternal, huArm, huNe⟩
  · subst u
    exact Tripod.liftAllNilOfCleanRightToLeftBridge
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts q ha hq_path hq_outside hq_clean transition
      htransition_path htransition_outside htransition_clean htransition_q
  · rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
    · subst r
      exact Tripod.liftAllNilOfSameFirstArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts q (Or.inl ha) hq_path hq_outside hq_clean
        huArm huNe huInternal (T.leftToAttach i).start_mem_support
        (hleft_ne_attach i) (Or.inr rfl) transition htransition_path
        htransition_outside htransition_clean htransition_q
    · rcases hrjk with hrj | hrk
      · subst r
        exact Tripod.liftAllNilOfSameMiddleArmTransition
          P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
          hpath_contacts q ha hq_path hq_outside hq_clean
          huArm huNe (Or.inl huInternal) (T.leftToAttach j).start_mem_support
          (hleft_ne_attach j) (Or.inr rfl) transition htransition_path
          htransition_outside htransition_clean htransition_q
      · subst r
        exact Tripod.liftAllNilOfSameLastArmTransition
          P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
          hpath_contacts q ha hq_path hq_outside hq_clean
          huArm huNe huInternal (T.leftToAttach k).start_mem_support
          (hleft_ne_attach k) (Or.inr rfl) transition htransition_path
          htransition_outside htransition_clean htransition_q

/-- Dispatch the first-intersection splice by the strict right-arm contact. -/
theorem Tripod.liftAllNilOfSplicedStrictRightArmTransition
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
    {a u c : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hu_contact : Exists fun r : Fin 3 =>
      u ∈ Walk.InternalVertices (T.rim r) ∧
        u ∈ (T.rightToAttach r).support ∧ u ≠ T.attach r)
    (bridge : S.graph.Walk u T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = u ∨ z = T.left)
    (tail : S.graph.Walk c a)
    (htail_path : tail.IsPath)
    (htail_outside : forall z : V, z ∈ tail.support -> z ∈ P.outside)
    (htail_clean : forall z : V, z ∈ tail.support ->
      z ∈ T.vertexSet -> False)
    (hc_bridge : c ∈ bridge.support)
    (hbridge_tail : forall z : V, z ∈ bridge.support ->
      z ∈ tail.support -> z = c) :
    Nonempty S.Tripod := by
  rcases hu_contact with ⟨r, huInternal, huArm, huNe⟩
  rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
  · subst r
    exact Tripod.liftAllNilOfSplicedSameFirstArmTransition
      P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
      hpath_contacts (Or.inl ha) huArm huNe huInternal bridge hbridge_path
      hbridge_outside hbridge_clean tail htail_path htail_outside htail_clean
      hc_bridge hbridge_tail
  · rcases hrjk with hrj | hrk
    · subst r
      exact Tripod.liftAllNilOfSplicedSameMiddleArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts ha huArm huNe (Or.inl huInternal) bridge hbridge_path
        hbridge_outside hbridge_clean tail htail_path htail_outside htail_clean
        hc_bridge hbridge_tail
    · subst r
      exact Tripod.liftAllNilOfSplicedSameLastArmTransition
        P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
        hpath_contacts ha huArm huNe huInternal bridge hbridge_path
        hbridge_outside hbridge_clean tail htail_path htail_outside htail_clean
        hc_bridge hbridge_tail

/-- First-intersection splice when the normalized transition starts at the old
right common end. -/
theorem Tripod.liftAllNilOfSplicedRightEndpointTransition
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
    {a c : V}
    (ha : a ∈ P.leftBoundaryArc)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hbridge_clean : forall z : V, z ∈ bridge.support ->
      z ∈ T.vertexSet -> z = T.right ∨ z = T.left)
    (tail : S.graph.Walk c a)
    (htail_path : tail.IsPath)
    (htail_outside : forall z : V, z ∈ tail.support -> z ∈ P.outside)
    (htail_clean : forall z : V, z ∈ tail.support ->
      z ∈ T.vertexSet -> False)
    (hc_bridge : c ∈ bridge.support)
    (hbridge_tail : forall z : V, z ∈ bridge.support ->
      z ∈ tail.support -> z = c) :
    Nonempty S.Tripod := by
  have hc_not_T : c ∉ T.vertexSet := by
    intro hcT
    exact htail_clean c tail.start_mem_support hcT
  let q0 : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hq0_outside : forall z : V, z ∈ q0.support -> z ∈ P.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [q0] using hz
    simpa [hzLeft] using hbridge_outside T.left bridge.end_mem_support
  have hq0_clean : forall z : V, z ∈ q0.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [q0] using hz
  have hbridge_q0 : forall z : V, z ∈ bridge.support ->
      z ∈ q0.support -> z = T.left := by
    intro z _hzBridge hzq
    simpa [q0] using hzq
  have houter :=
    GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts q0 hq0_outside hq0_clean
      bridge hbridge_outside hbridge_q0
  refine ⟨{
    left := T.right
    right := T.boundary j
    left_ne_right := T.right_ne_boundary j
    rim := GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
      (hlegs_nil j)
      hi hj hk hij_order hjk_order bridge
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeRim_isPath P T hgraph
        hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts bridge
        hbridge_path hbridge_clean
    attach :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c
    attach_mem_rim := by
      intro r
      fin_cases r
      · simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilCleanBridgeAttach] using
          (GMIX24SourceProof.Tripod.allNilCleanBridgeAttach_mem_rim
            P T hgraph hij hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order bridge 0)
      · change c ∈ Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilCleanBridgeRim P T hgraph
            (hlegs_nil j)
            hi hj hk hij_order hjk_order bridge 1)
        refine ⟨?_, ?_, ?_⟩
        · simp only [Tripod.allNilCleanBridgeRim,
            SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl hc_bridge
        · intro hcRight
          apply hc_not_T
          rw [hcRight]
          exact T.right_mem_vertexSet
        · intro hcBoundary
          apply hc_not_T
          rw [hcBoundary]
          exact T.boundary_mem_vertexSet j
      · simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilCleanBridgeAttach] using
          (GMIX24SourceProof.Tripod.allNilCleanBridgeAttach_mem_rim
            P T hgraph hij hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order bridge 2)
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg
      P T (hlegs_nil i) (hlegs_nil k) hi hk tail
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg_isPath
        P T (hlegs_nil i) (hlegs_nil k) hi hk tail htail_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts bridge
        hbridge_outside hbridge_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order tail htail_outside
    legs_meet_rims_only_at_attach := by
      intro r s z hzLeg hzRim
      fin_cases r
      · have hzOldLeg : z ∈
            (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
              (hlegs_nil i) (hlegs_nil k) hi hk q0 0).support := by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg] using hzLeg
        simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilCleanBridgeAttach] using houter 0 s z hzOldLeg hzRim
      · have hzTail : z ∈ tail.support := by
          simpa [Tripod.allNilSplicedTransitionLeg] using hzLeg
        fin_cases s
        · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
              (by simpa [Tripod.allNilCleanBridgeRim] using hzRim) with
            hzArm | hzOldLeg | hzPath
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm)))
          · exact False.elim (htail_clean z hzTail (T.leg_mem_vertexSet hzOldLeg))
          · exact False.elim ((htail_outside z hzTail).2
              (P.pathSegmentBetween_support_subset_pathSet hi hj
                (Nat.le_of_lt hij_order) z hzPath))
        · rcases GMIX24SourceProof.Tripod.allNilCleanBridgeRim_one_support_cases
              P T hgraph (hlegs_nil j)
              hi hj hk hij_order hjk_order bridge hzRim with hzBridge | hzArm
          · simpa [Tripod.allNilSplicedTransitionAttach] using
              hbridge_tail z hzBridge hzTail
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim j hzArm)))
        · rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
              (by simpa [Tripod.allNilCleanBridgeRim] using hzRim) with
            hzArm | hzOldLeg | hzPathRev
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArm)))
          · exact False.elim (htail_clean z hzTail (T.leg_mem_vertexSet hzOldLeg))
          · have hzPath : z ∈
                (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
              simpa [SimpleGraph.Walk.support_reverse] using hzPathRev
            exact False.elim ((htail_outside z hzTail).2
              (P.pathSegmentBetween_support_subset_pathSet hj hk
                (Nat.le_of_lt hjk_order) z hzPath))
      · have hzOldLeg : z ∈
            (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
              (hlegs_nil i) (hlegs_nil k) hi hk q0 2).support := by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilCleanBridgeLeg] using hzLeg
        simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilCleanBridgeAttach] using houter 2 s z hzOldLeg hzRim
  }⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
