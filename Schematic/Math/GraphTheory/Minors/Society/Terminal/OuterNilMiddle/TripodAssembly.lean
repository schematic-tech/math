import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.LegRimIntersections

/-!
Assembly of the endpoint-starting rebuilt tripods.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Assemble the rebuilt tripod once its leg paths and leg-rim intersections
have been established.  This isolates the common combinatorial assembly from
the two different cleanliness arguments used below and by residual lifts. -/
theorem Tripod.liftOuterNilMiddleNonNilCommonLeftOfLegData
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_path : forall r : Fin 3,
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
        P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).IsPath)
    (hleg_rim : forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
          P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk hij_order hjk_order s).support ->
      z =
        GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
          T i j k r) :
    Nonempty S.Tripod := by
  refine ⟨{
    left := T.right
    right := T.boundary j
    left_ne_right := T.right_ne_boundary j
    rim := GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
      P T hgraph hi hj hk hij_order hjk_order
    rim_isPath := GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
      P T hgraph hij hik hjk hi hj hk
      hij_order hjk_order hpath_contacts
    attach :=
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
        T i j k
    attach_mem_rim := GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttach_mem_rim
      P T hgraph hij hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
      hi hj hk hij_order hjk_order
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
      P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q
    leg_isPath := hleg_path
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRims_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLegs_pairwise_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order q hq_outside hpath_contacts
    legs_meet_rims_only_at_attach := hleg_rim
  }⟩

/-- Direct ambient tripod in the source residual where the two ordered outer
legs have collapsed, the middle leg is nontrivial, and the clean path leaves
the old left common endpoint. -/
theorem Tripod.liftOuterNilMiddleNonNilCommonLeft
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  exact GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilCommonLeftOfLegData
    P T hgraph hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
    hi hj hk hij_order hjk_order ha q hq_outside hpath_contacts
    (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_isPath
      P T hgraph hleg_i_nil hleg_k_nil hi hk q hq_path hq_clean)
    (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk hleg_i_nil hleg_j_not_nil hleg_k_nil
      hi hj hk hij_order hjk_order q hq_outside hq_clean hpath_contacts)

/-- Right-common-end counterpart of
`liftOuterNilMiddleNonNilCommonLeft`, obtained by reversing all old rims. -/
theorem Tripod.liftOuterNilMiddleNonNilCommonRight
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (q : S.graph.Walk T.right a)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.right)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  let Tflip := T.flip
  have hpath_contacts_flip :
      forall z : V, z ∈ P.pathSet -> z ∈ Tflip.vertexSet ->
        Exists fun m : Fin 3 => z = Tflip.boundary m := by
    simpa [Tflip] using T.pathContacts_flip hpath_contacts
  exact GMIX24SourceProof.Tripod.liftOuterNilMiddleNonNilCommonLeft
    P Tflip hgraph hij hik hjk
    (by simpa [Tflip] using hleg_i_nil)
    (by simpa [Tflip] using hleg_j_not_nil)
    (by simpa [Tflip] using hleg_k_nil)
    (by simpa [Tflip] using hi) (by simpa [Tflip] using hj)
    (by simpa [Tflip] using hk)
    (by simpa [Tflip] using hij_order)
    (by simpa [Tflip] using hjk_order)
    ha (by simpa [Tflip] using q) hq_path hq_outside
    (by
      intro z hzq hzT
      exact hq_clean z hzq (by simpa [Tflip] using hzT))
    hpath_contacts_flip


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
