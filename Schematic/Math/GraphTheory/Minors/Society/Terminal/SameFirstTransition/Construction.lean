import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameFirstTransition.Rims

/-!
Ambient tripod constructions for same-first-arm transitions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Ambient tripod produced by a clean transition between the two strict
arms of the first ordered old rim. -/
theorem Tripod.liftAllNilOfSameFirstArmTransition
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
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
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
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = T.left) :
    Nonempty S.Tripod := by
  have hleft_ne_right : T.attach j ≠ u := by
    intro hju
    have hjRimI : T.attach j ∈ (T.rim i).support := by
      simpa [hju] using
        Walk.internalVertices_subset_support (T.rim i) hu_internal
    exact T.attach_not_mem_rim_of_ne
      (i := j) (j := i) (fun h => hij h.symm) hjRimI
  refine ⟨{
    left := T.attach j
    right := u
    left_ne_right := hleft_ne_right
    rim := GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv transition
        htransition_path htransition_clean
    attach := GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal hv transition
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
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv hv_ne_attach hleft_contact transition
        htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilCleanBridgeLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order q hq_outside
    legs_meet_rims_only_at_attach :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionLegs_meet_rims_only_at_attach
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts q hq_outside hq_clean
        hu hu_ne_attach hv hv_ne_attach transition
        htransition_outside htransition_q
  }⟩

/-- First-rim splice at the first intersection of a clean transition with the
selected boundary escape.  The escape suffix becomes the middle leg and the
splice point becomes its attachment. -/
theorem Tripod.liftAllNilOfSplicedSameFirstArmTransition
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
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
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
  have hleft_ne_attach : T.left ≠ T.attach i := by
    intro h
    exact T.left_ne_boundary i
      (h.trans ((T.leg_nil_iff_boundary_eq_attach i).mp (hlegs_nil i)).symm)
  have hc_not_T : c ∉ T.vertexSet := by
    intro hcT
    exact htail_clean c tail.start_mem_support hcT
  have hc_ne_u : c ≠ u := by
    intro h
    exact hc_not_T (by simpa [h] using T.rim_mem_vertexSet hu_internal.1)
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
    GMIX24SourceProof.Tripod.allNilSameFirstTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts q0 hq0_outside hq0_clean
      hu hu_ne_attach (T.leftToAttach i).start_mem_support
      hleft_ne_attach bridge hbridge_outside hbridge_q0
  refine ⟨{
    left := T.attach j
    right := u
    left_ne_right := by
      intro h
      exact T.attach_not_mem_rim_of_ne
        (i := j) (j := i) (fun hji => hij hji.symm)
        (by simpa [h] using hu_internal.1)
    rim := GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu (T.leftToAttach i).start_mem_support bridge
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        (T.leftToAttach i).start_mem_support
        bridge hbridge_path hbridge_clean
    attach :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c
    attach_mem_rim := by
      intro r
      fin_cases r
      · simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilCleanBridgeAttach] using
          (GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
            P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal
            (T.leftToAttach i).start_mem_support bridge 0)
      · change c ∈ Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
            P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu
            (T.leftToAttach i).start_mem_support bridge 1)
        refine ⟨?_, ?_, hc_ne_u⟩
        · rw [Tripod.allNilSameFirstTransitionRim.eq_def,
            SimpleGraph.Walk.mem_support_append_iff]
          right
          simpa [SimpleGraph.Walk.support_reverse] using hc_bridge
        · intro hcAttach
          apply hc_not_T
          rw [hcAttach]
          exact T.attach_mem_vertexSet j
      · simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilCleanBridgeAttach] using
          (GMIX24SourceProof.Tripod.allNilSameFirstTransitionAttach_mem_rim
            P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
            hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal
            (T.leftToAttach i).start_mem_support bridge 2)
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg
      P T (hlegs_nil i) (hlegs_nil k) hi hk tail
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg_isPath
        P T (hlegs_nil i) (hlegs_nil k) hi hk tail htail_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        (T.leftToAttach i).start_mem_support hleft_ne_attach (Or.inr rfl)
        bridge hbridge_outside hbridge_clean
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
        · rcases
              GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
                P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
                hi hj hk hij_order hjk_order hu
                (T.leftToAttach i).start_mem_support bridge hzRim with
            hzPath | hzArm
          · exact False.elim ((htail_outside z hzTail).2
              (P.pathSegmentBetween_support_subset_pathSet hi hj
                (Nat.le_of_lt hij_order) z hzPath))
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet
                (T.attachToRight_support_subset_rim i
                  (SimpleGraph.Walk.support_takeUntil_subset
                    (T.attachToRight i) (by
                      simpa [Tripod.rightToAttach,
                        SimpleGraph.Walk.support_reverse] using hu) hzArm))))
        · rcases
              GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
                P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
                hi hj hk hij_order hjk_order hu
                (T.leftToAttach i).start_mem_support bridge hzRim with
            hzJ | hzI | hzBridge
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzJ)))
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim i
                (SimpleGraph.Walk.support_takeUntil_subset
                  (T.leftToAttach i) (T.leftToAttach i).start_mem_support hzI))))
          · simpa [Tripod.allNilSplicedTransitionAttach] using
              hbridge_tail z hzBridge hzTail
        · rcases
              GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
                P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
                hi hj hk hij_order hjk_order hu
                (T.leftToAttach i).start_mem_support bridge hzRim with
            hzPath | hzK | hzI
          · exact False.elim ((htail_outside z hzTail).2
              (P.pathSegmentBetween_support_subset_pathSet hj hk
                (Nat.le_of_lt hjk_order) z hzPath))
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim k hzK)))
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i
                (SimpleGraph.Walk.support_takeUntil_subset
                  (T.rightToAttach i) hu hzI))))
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
