import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.CommonEndpointLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

end GMIX24Split

/-- A point on the right attachment arm becomes a point on the left
attachment arm when all tripod rims are reversed. -/
theorem Tripod.mem_flip_leftToAttach_of_mem_attachToRight
    [DecidableEq V] {S : GeneralSociety V}
    (T : S.Tripod) (i : Fin 3) {x : V}
    (hx : x ∈ (T.attachToRight i).support) :
    x ∈ (T.flip.leftToAttach i).support := by
  have hx_right : x ∈ (T.rightToAttach i).support := by
    simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse] using hx
  have hx_drop :
      x ∈ ((T.rim i).dropUntil (T.attach i) (T.attach_mem_rim i).1).support := by
    simpa [Tripod.rightToAttach, Tripod.attachToRight,
      SimpleGraph.Walk.support_reverse] using hx_right
  have hattach_rev : T.attach i ∈ (T.rim i).reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using (T.attach_mem_rim i).1
  have hx_rev_take :
      x ∈ ((T.rim i).reverse.takeUntil (T.attach i) hattach_rev).support :=
    Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
      (T.rim_isPath i) (T.attach_mem_rim i).1 hattach_rev hx_drop
  simpa [Tripod.leftToAttach, Tripod.flip] using hx_rev_take

namespace GMIX24Split

  /-- Ordered nil-residual lift for the first ordered branch when the clean
  outside tail starts on the old left-to-attachment arm.

  This is the split-level form of the direct GM IX `(2.4)` construction for the
  source subcase in which the first cut-path foot has collapsed to its rim
  attachment.  The rebuilt ambient tripod uses the middle and last old feet as
  its rim ends, the cut-path segment between them as the new central rim, the
  old-left-arm prefix plus `q` as one leg, and the old-right branch plus the
  backward cut-path tail as the opposite leg. -/
  theorem canonicalOfNoCross_left_tripod_lift_nil_first_left_arm_residual_ordered_of_nil
      [DecidableEq V] {S : GeneralSociety V}
      (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_k_not_nil : Not (T.leg k).Nil)
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
      {x a : V}
      (q : S.graph.Walk x a)
      (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
      (hleg_nil : (T.leg i).Nil)
      (hx_arm : x ∈ (T.leftToAttach i).support)
      (hx_ne_attach : x ≠ T.attach i)
      (ha : a ∈ P.leftBoundaryArc)
      (hq_path : q.IsPath)
      (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
      (hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) :
      Nonempty S.Tripod := by
    classical
    let hgraph :=
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
    have hprefix_outside :
        forall z : V,
          z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
            z ∈ P.outside :=
      GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach
    have hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support :=
      GMIX24Split.tripod_leg_nil_residual_not_mem_leg T
        (i := i) (k := k) (x := x)
        ⟨i, Or.inl rfl, hx_internal, hleg_nil, hx_ne_attach⟩
    exact
      T.liftFirstNilResidualLeftArm P hgraph hij hik hjk
        hleg_k_not_nil hi hj hk hij_order hjk_order
        hx_arm hx_ne_attach hx_internal q ha hq_path hprefix_outside
        hq_outside hq_clean_vertex hx_not_leg hpath_contacts

  /-- Ordered nil-first residual lift for the old right arm.  This is the
  left-arm constructor applied after reversing the old side-tripod rims. -/
  theorem canonicalOfNoCross_left_tripod_lift_nil_first_right_arm_residual_ordered_of_nil
      [DecidableEq V] {S : GeneralSociety V}
      (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_k_not_nil : Not (T.leg k).Nil)
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
      {x a : V}
      (q : S.graph.Walk x a)
      (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
      (hleg_nil : (T.leg i).Nil)
      (hx_arm : x ∈ (T.attachToRight i).support)
      (hx_ne_attach : x ≠ T.attach i)
      (ha : a ∈ P.leftBoundaryArc)
      (hq_path : q.IsPath)
      (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
      (hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) :
      Nonempty S.Tripod := by
    let Tflip := T.flip
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_left_arm_residual_ordered_of_nil
        P hno_cross Tflip hij hik hjk
        (by simpa [Tflip] using hleg_k_not_nil)
        (by simpa [Tflip] using hi) (by simpa [Tflip] using hj)
        (by simpa [Tflip] using hk)
        (by simpa [Tflip] using hij_order)
        (by simpa [Tflip] using hjk_order)
        (by
          intro z hzPath hzT
          simpa [Tflip] using hpath_contacts z hzPath (by simpa [Tflip] using hzT))
        q
        (by simpa [Tflip, Tripod.flip, Walk.internalVertices_reverse] using hx_internal)
        (by simpa [Tflip] using hleg_nil)
        (by simpa [Tflip] using T.mem_flip_leftToAttach_of_mem_attachToRight i hx_arm)
        (by simpa [Tflip] using hx_ne_attach)
        ha hq_path hq_outside
        (by
          intro w hw hT
          exact hq_clean w hw (by
            simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hT))

  /-- Ordered nil-first residual lift after the arm normalization step. -/
  theorem canonicalOfNoCross_left_tripod_lift_nil_first_arm_residual_ordered_of_nil
      [DecidableEq V] {S : GeneralSociety V}
      (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_k_not_nil : Not (T.leg k).Nil)
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
      {x a : V}
      (q : S.graph.Walk x a)
      (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
      (hleg_nil : (T.leg i).Nil)
      (harm :
        (x ∈ (T.leftToAttach i).support ∧ x ≠ T.attach i) ∨
          (x ∈ (T.attachToRight i).support ∧ x ≠ T.attach i))
      (ha : a ∈ P.leftBoundaryArc)
      (hq_path : q.IsPath)
      (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
      (hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) :
      Nonempty S.Tripod := by
    rcases harm with harm_left | harm_right
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_left_arm_residual_ordered_of_nil
          P hno_cross T hij hik hjk hleg_k_not_nil
          hi hj hk hij_order hjk_order hpath_contacts q hx_internal
          hleg_nil harm_left.1 harm_left.2 ha hq_path hq_outside hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_right_arm_residual_ordered_of_nil
          P hno_cross T hij hik hjk hleg_k_not_nil
          hi hj hk hij_order hjk_order hpath_contacts q hx_internal
          hleg_nil harm_right.1 harm_right.2 ha hq_path hq_outside hq_clean

/-- Sharper nil-first residual lift for a left-arm hit: the middle ordered old
leg may also be trivial. -/
  theorem canonicalOfNoCross_left_tripod_lift_nil_first_left_arm_residual_ordered_of_nil_last_not_nil
      [DecidableEq V] {S : GeneralSociety V}
      (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_k_not_nil : Not (T.leg k).Nil)
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
      {x a : V}
      (q : S.graph.Walk x a)
      (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
      (hleg_nil : (T.leg i).Nil)
      (hx_arm : x ∈ (T.leftToAttach i).support)
      (hx_ne_attach : x ≠ T.attach i)
      (ha : a ∈ P.leftBoundaryArc)
      (hq_path : q.IsPath)
      (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
      (hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) :
      Nonempty S.Tripod := by
    classical
    let hgraph :=
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
    have hprefix_outside :
        forall z : V,
          z ∈ ((T.leftToAttach i).takeUntil x hx_arm).support ->
            z ∈ P.outside :=
      GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach
    have hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support :=
      GMIX24Split.tripod_leg_nil_residual_not_mem_leg T
        (i := i) (k := k) (x := x)
        ⟨i, Or.inl rfl, hx_internal, hleg_nil, hx_ne_attach⟩
    exact
      T.liftFirstNilResidualLeftArm_last_not_nil P hgraph hij hik hjk
        hleg_k_not_nil hi hj hk hij_order hjk_order
        hx_arm hx_ne_attach hx_internal q ha hq_path hprefix_outside
        hq_outside hq_clean_vertex hx_not_leg hpath_contacts

  /-- Sharper nil-first residual lift for a right-arm hit, obtained by
  flipping the old side-tripod rims. -/
  theorem canonicalOfNoCross_left_tripod_lift_nil_first_right_arm_residual_ordered_of_nil_last_not_nil
      [DecidableEq V] {S : GeneralSociety V}
      (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_k_not_nil : Not (T.leg k).Nil)
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
      {x a : V}
      (q : S.graph.Walk x a)
      (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
      (hleg_nil : (T.leg i).Nil)
      (hx_arm : x ∈ (T.attachToRight i).support)
      (hx_ne_attach : x ≠ T.attach i)
      (ha : a ∈ P.leftBoundaryArc)
      (hq_path : q.IsPath)
      (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
      (hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) :
      Nonempty S.Tripod := by
    let Tflip := T.flip
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_left_arm_residual_ordered_of_nil_last_not_nil
        P hno_cross Tflip hij hik hjk
        (by simpa [Tflip] using hleg_k_not_nil)
        (by simpa [Tflip] using hi) (by simpa [Tflip] using hj)
        (by simpa [Tflip] using hk)
        (by simpa [Tflip] using hij_order)
        (by simpa [Tflip] using hjk_order)
        (by
          intro z hzPath hzT
          simpa [Tflip] using hpath_contacts z hzPath (by simpa [Tflip] using hzT))
        q
        (by simpa [Tflip, Tripod.flip, Walk.internalVertices_reverse] using hx_internal)
        (by simpa [Tflip] using hleg_nil)
        (by simpa [Tflip] using T.mem_flip_leftToAttach_of_mem_attachToRight i hx_arm)
        (by simpa [Tflip] using hx_ne_attach)
        ha hq_path hq_outside
        (by
          intro w hw hT
          exact hq_clean w hw (by
            simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hT))

  /-- Sharper nil-first residual lift after arm normalization: the middle
  ordered old leg may also be trivial. -/
  theorem canonicalOfNoCross_left_tripod_lift_nil_first_arm_residual_ordered_of_nil_last_not_nil
      [DecidableEq V] {S : GeneralSociety V}
      (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_k_not_nil : Not (T.leg k).Nil)
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
      {x a : V}
      (q : S.graph.Walk x a)
      (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
      (hleg_nil : (T.leg i).Nil)
      (harm :
        (x ∈ (T.leftToAttach i).support ∧ x ≠ T.attach i) ∨
          (x ∈ (T.attachToRight i).support ∧ x ≠ T.attach i))
      (ha : a ∈ P.leftBoundaryArc)
      (hq_path : q.IsPath)
      (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
      (hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) :
      Nonempty S.Tripod := by
    rcases harm with harm_left | harm_right
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_left_arm_residual_ordered_of_nil_last_not_nil
          P hno_cross T hij hik hjk hleg_k_not_nil
          hi hj hk hij_order hjk_order hpath_contacts q hx_internal
          hleg_nil harm_left.1 harm_left.2 ha hq_path hq_outside hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_right_arm_residual_ordered_of_nil_last_not_nil
          P hno_cross T hij hik hjk hleg_k_not_nil
          hi hj hk hij_order hjk_order hpath_contacts q hx_internal
          hleg_nil harm_right.1 harm_right.2 ha hq_path hq_outside hq_clean


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
