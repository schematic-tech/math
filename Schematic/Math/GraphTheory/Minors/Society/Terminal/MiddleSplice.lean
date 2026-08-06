import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameFirstTransition
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameMiddleTransition

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Median-rim analogue of the first-intersection splice constructor. -/
theorem Tripod.liftAllNilOfSplicedSameMiddleArmTransition
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
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
  have hleft_ne_attach : T.left ≠ T.attach j := by
    intro h
    exact T.left_ne_boundary j
      (h.trans ((T.leg_nil_iff_boundary_eq_attach j).mp (hlegs_nil j)).symm)
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
    GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts q0 hq0_outside hq0_clean
      hu hu_ne_attach (T.leftToAttach j).start_mem_support hleft_ne_attach
      (Or.inr rfl) bridge hbridge_outside hbridge_clean hbridge_q0
  refine ⟨{
    left := T.right
    right := T.attach j
    left_ne_right := by
      intro h
      exact T.right_ne_boundary j
        (h.trans ((T.leg_nil_iff_boundary_eq_attach j).mp (hlegs_nil j)).symm)
    rim := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
      P T hgraph (hlegs_nil j)
      hi hj hk hij_order hjk_order hu (T.leftToAttach j).start_mem_support bridge
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        (T.leftToAttach j).start_mem_support hleft_ne_attach bridge
        hbridge_path hbridge_clean
    attach :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c
    attach_mem_rim := by
      intro r
      fin_cases r
      · simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilSameMiddleTransitionAttach] using
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach_mem_rim
            P T hgraph hij hjk (hlegs_nil j)
            hi hj hk hij_order hjk_order hu (T.leftToAttach j).start_mem_support
            hleft_ne_attach (Or.inr rfl) bridge 0)
      · change c ∈ Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
            P T hgraph (hlegs_nil j)
            hi hj hk hij_order hjk_order hu
            (T.leftToAttach j).start_mem_support bridge 1)
        refine ⟨?_, ?_, ?_⟩
        · rw [Tripod.allNilSameMiddleTransitionRim.eq_def,
            SimpleGraph.Walk.mem_support_append_iff]
          left
          rw [SimpleGraph.Walk.mem_support_append_iff]
          right
          exact hc_bridge
        · intro hcRight
          apply hc_not_T
          rw [hcRight]
          exact T.right_mem_vertexSet
        · intro hcAttach
          apply hc_not_T
          rw [hcAttach]
          exact T.attach_mem_vertexSet j
      · simpa [Tripod.allNilSplicedTransitionAttach,
          Tripod.allNilSameMiddleTransitionAttach] using
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach_mem_rim
            P T hgraph hij hjk (hlegs_nil j)
            hi hj hk hij_order hjk_order hu (T.leftToAttach j).start_mem_support
            hleft_ne_attach (Or.inr rfl) bridge 2)
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg
      P T (hlegs_nil i) (hlegs_nil k) hi hk tail
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg_isPath
        P T (hlegs_nil i) (hlegs_nil k) hi hk tail htail_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        (T.leftToAttach j).start_mem_support (Or.inr rfl) bridge
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
          Tripod.allNilSameMiddleTransitionAttach] using
            houter 0 s z hzOldLeg hzRim
      · have hzTail : z ∈ tail.support := by
          simpa [Tripod.allNilSplicedTransitionLeg] using hzLeg
        fin_cases s
        · rcases
              GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
                P T hgraph (hlegs_nil j)
                hi hj hk hij_order hjk_order hu
                (T.leftToAttach j).start_mem_support bridge hzRim with
            hzArm | hzOldLeg | hzPath
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm)))
          · exact False.elim (htail_clean z hzTail (T.leg_mem_vertexSet hzOldLeg))
          · exact False.elim ((htail_outside z hzTail).2
              (P.pathSegmentBetween_support_subset_pathSet hi hj
                (Nat.le_of_lt hij_order) z hzPath))
        · rcases
              GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
                P T hgraph (hlegs_nil j)
                hi hj hk hij_order hjk_order hu
                (T.leftToAttach j).start_mem_support bridge hzRim with
            hzRight | hzBridge | hzLeft
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j
                (SimpleGraph.Walk.support_takeUntil_subset
                  (T.rightToAttach j) hu hzRight))))
          · simpa [Tripod.allNilSplicedTransitionAttach] using
              hbridge_tail z hzBridge hzTail
          · exact False.elim (htail_clean z hzTail
              (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim j
                (SimpleGraph.Walk.support_dropUntil_subset
                  (T.leftToAttach j) (T.leftToAttach j).start_mem_support hzLeft))))
        · rcases
              GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
                P T hgraph (hlegs_nil j)
                hi hj hk hij_order hjk_order hu
                (T.leftToAttach j).start_mem_support bridge hzRim with
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
          Tripod.allNilSameMiddleTransitionAttach] using
            houter 2 s z hzOldLeg hzRim
  }⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
