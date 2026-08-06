import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.FirstResidualLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
  /-- Ordered nil-residual lift for the source side-tripod paragraph: the residual
  hit lies strictly on the old left-to-attachment arm of the last ordered branch.

The new common-left branch is the strict old arm prefix followed by the clean
outside tail.  Only the first ordered old leg has to be nontrivial: the
leg-segment rim may use a collapsed middle foot as an endpoint, so it creates
no internal rim intersection.  The residual branch itself may be nil. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_last_left_arm_residual_ordered
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
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
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x)
    (hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support) :
    Nonempty S.Tripod := by
  classical
  let hgraph :=
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  let qLeftData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean_vertex⟩
  let qLeft : S.graph.Walk T.left a := qLeftData.walk
  have hqLeft_path : qLeft.IsPath := by
    simpa [qLeft, hgraph] using qLeftData.walk_isPath
  have hprefix_outside :
      forall z : V,
        z ∈ ((T.leftToAttach k).takeUntil x hx_arm).support ->
          z ∈ P.outside :=
    GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
      P hno_cross T hpath_contacts hx_arm hx_ne_attach
  refine ⟨T.liftCommonLeftEndpointOrderedCore
    P hgraph hij hik hjk hleg_i_not_nil hi hj hk hij_order hjk_order
    ha qLeft hqLeft_path hpath_contacts
    (T.commonLeftEndpointRims_internal_disjoint_first_not_nil
      P hgraph hij hik hjk hi hj
      hij_order hjk_order hpath_contacts)
    ?_ ?_⟩
  · simpa [qLeft, hgraph] using
      T.commonLeftEndpointLeftArmPrefixTail_legs_pairwise_disjoint
        P hgraph hij hik hjk hi hk hij_order hjk_order
        hx_arm hx_ne_attach q hprefix_outside hq_outside hq_clean_vertex
        hx_not_leg hpath_contacts
  · intro r s z hzLeg hzRim
    fin_cases r
    · exact
        T.commonLeftEndpointLeg_zero_meets_rims
          P hgraph hij hik hjk hi hj hij_order hjk_order hpath_contacts
          s z (by simpa [Tripod.commonLeftEndpointLeg, qLeft] using hzLeg)
          hzRim
    · simpa [Tripod.commonLeftEndpointLeg, Tripod.commonLeftEndpointAttach,
        qLeft, hgraph] using
        T.commonLeftEndpointLeftArmPrefixTail_meets_rims_only_at_left
          P hgraph hik hjk hi hj hij_order hx_arm
          hx_internal q hprefix_outside hq_outside hq_clean_vertex
          hx_not_leg s z
          (by simpa [qLeft, hgraph] using hzLeg) hzRim
    · simpa [Tripod.commonLeftEndpointLeg, Tripod.commonLeftEndpointAttach,
        qLeft, hgraph] using
        T.commonLeftEndpointRightBranch_meets_rims
          P hgraph hij hik hjk hi hj hk hij_order hjk_order
          hpath_contacts s z
          (by simpa [Tripod.commonLeftEndpointLeg, qLeft, hgraph] using hzLeg)
          hzRim

/-- Exact nil-last left-arm residual form of
`canonicalOfNoCross_left_tripod_lift_nil_last_left_arm_residual_ordered`.
The auxiliary fact that the residual hit is on no old leg is derived from the
nil residual itself. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_last_left_arm_residual_ordered_of_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
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
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (hleg_nil : (T.leg k).Nil)
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
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
  have hx_not_leg : forall r : Fin 3, x ∉ (T.leg r).support :=
    GMIX24Split.tripod_leg_nil_residual_not_mem_leg T
      (i := i) (k := k) (x := x)
      ⟨k, Or.inr rfl, hx_internal, hleg_nil, hx_ne_attach⟩
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_last_left_arm_residual_ordered
      P hno_cross T hij hik hjk hleg_i_not_nil
      hi hj hk hij_order hjk_order hpath_contacts q hx_arm hx_ne_attach
      hx_internal ha hq_path hq_outside hq_clean hx_not_leg

/-- Ordered nil-last residual lift for the old right arm.  This is obtained by
flipping the side tripod and applying the checked left-arm constructor. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_last_right_arm_residual_ordered_of_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
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
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (hleg_nil : (T.leg k).Nil)
    (hx_arm : x ∈ (T.attachToRight k).support)
    (hx_ne_attach : x ≠ T.attach k)
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
  let Tflip := T.flip
  have hx_right : x ∈ (T.rightToAttach k).support := by
    simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse] using hx_arm
  have hx_drop : x ∈ ((T.rim k).dropUntil (T.attach k) (T.attach_mem_rim k).1).support := by
    simpa [Tripod.rightToAttach, Tripod.attachToRight,
      SimpleGraph.Walk.support_reverse] using hx_right
  have hattach_rev :
      T.attach k ∈ (T.rim k).reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using (T.attach_mem_rim k).1
  have hx_flip_arm : x ∈ (Tflip.leftToAttach k).support := by
    have hx_rev_take :
        x ∈
          ((T.rim k).reverse.takeUntil (T.attach k) hattach_rev).support :=
      Walk.IsPath.mem_reverse_takeUntil_of_mem_dropUntil
        (T.rim_isPath k) (T.attach_mem_rim k).1 hattach_rev hx_drop
    simpa [Tflip, Tripod.leftToAttach, Tripod.flip] using hx_rev_take
  have hx_flip_internal : x ∈ Walk.InternalVertices (Tflip.rim k) := by
    simpa [Tflip, Tripod.flip, Walk.internalVertices_reverse] using hx_internal
  have hleg_nil_flip : (Tflip.leg k).Nil := by
    simpa [Tflip] using hleg_nil
  have hleg_i_not_nil_flip : Not (Tflip.leg i).Nil := by
    simpa [Tflip] using hleg_i_not_nil
  have hpath_contacts_flip :
      forall z : V, z ∈ P.pathSet -> z ∈ Tflip.vertexSet ->
        Exists fun m : Fin 3 => z = Tflip.boundary m := by
    intro z hzPath hzT
    have hzT_original : z ∈ T.vertexSet := by
      simpa [Tflip] using hzT
    rcases hpath_contacts z hzPath hzT_original with ⟨m, hm⟩
    exact ⟨m, by simpa [Tflip] using hm⟩
  have hq_clean_flip :
      forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (Tflip.rim r).support ∨ w ∈ (Tflip.leg r).support) ->
          w = x := by
    intro w hw hpack
    exact hq_clean w hw (by
      rcases hpack with ⟨r, hrim | hleg⟩
      · exact ⟨r, Or.inl (by
          simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hrim)⟩
      · exact ⟨r, Or.inr (by simpa [Tflip] using hleg)⟩)
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_last_left_arm_residual_ordered_of_nil
      P hno_cross Tflip hij hik hjk hleg_i_not_nil_flip
      (by simpa [Tflip] using hi) (by simpa [Tflip] using hj)
      (by simpa [Tflip] using hk)
      (by simpa [Tflip] using hij_order)
      (by simpa [Tflip] using hjk_order)
      hpath_contacts_flip q hx_flip_internal hleg_nil_flip hx_flip_arm
      (by simpa [Tflip] using hx_ne_attach)
      ha hq_path hq_outside hq_clean_flip

/-- Ordered nil-last residual lift after the arm normalization step.

The source residual classifier only knows that the clean tail starts strictly
on one of the two old rim arms of the last ordered branch.  The two arm
constructors above cover those alternatives uniformly. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_last_arm_residual_ordered_of_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
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
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (hleg_nil : (T.leg k).Nil)
    (harm :
      (x ∈ (T.leftToAttach k).support ∧ x ≠ T.attach k) ∨
        (x ∈ (T.attachToRight k).support ∧ x ≠ T.attach k))
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
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_last_left_arm_residual_ordered_of_nil
        P hno_cross T hij hik hjk hleg_i_not_nil
        hi hj hk hij_order hjk_order hpath_contacts q hx_internal
        hleg_nil harm_left.1 harm_left.2 ha hq_path hq_outside hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_last_right_arm_residual_ordered_of_nil
        P hno_cross T hij hik hjk hleg_i_not_nil
        hi hj hk hij_order hjk_order hpath_contacts q hx_internal
        hleg_nil harm_right.1 harm_right.2 ha hq_path hq_outside hq_clean

private theorem ordered_residual_impossible_of_outer_choice
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (houter : Not (T.leg i).Nil ∨ Not (T.leg k).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    False := by
  classical
  have hi : T.boundary i ∈ P.pathSet := by
    simpa [fin3Order] using hold 0
  have hj : T.boundary j ∈ P.pathSet := by
    simpa [fin3Order] using hold 1
  have hk : T.boundary k ∈ P.pathSet := by
    simpa [fin3Order] using hold 2
  have hall : forall r : Fin 3, T.boundary r ∈ P.pathSet := by
    intro r
    rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
    · simpa [hri] using hi
    · rcases hrjk with hrj | hrk
      · simpa [hrj] using hj
      · simpa [hrk] using hk
  rcases hresidual with hend | hnil_raw
  · rcases hend with hx_left | hx_right
    · rcases houter with hfirst | hlast
      · exact hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered_first_not_nil
            P hno_cross T hij hik hjk hfirst hi hj hk hij_order hjk_order
            hpath_contacts q hx_left ha hq_path hq_outside hq_clean)
      · by_cases hfirst : Not (T.leg i).Nil
        · exact hno_tripod
            (GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered_first_not_nil
              P hno_cross T hij hik hjk hfirst hi hj hk hij_order hjk_order
              hpath_contacts q hx_left ha hq_path hq_outside hq_clean)
        · exact hno_tripod
            (GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_common_left_endpoint_ordered_last_not_nil
              P hno_cross T hij hik hjk hlast hi hj hk hij_order hjk_order
              hpath_contacts q hx_left ha hq_path hq_outside hq_clean)
    · rcases houter with hfirst | hlast
      · exact hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_right_endpoint_ordered_first_not_nil
            P hno_cross T hij hik hjk hfirst hi hj hk hij_order hjk_order
            hpath_contacts q hx_right ha hq_path hq_outside hq_clean)
      · by_cases hfirst : Not (T.leg i).Nil
        · exact hno_tripod
            (GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_right_endpoint_ordered_first_not_nil
              P hno_cross T hij hik hjk hfirst hi hj hk hij_order hjk_order
              hpath_contacts q hx_right ha hq_path hq_outside hq_clean)
        · exact hno_tripod
            (GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_common_right_endpoint_ordered_last_not_nil
              P hno_cross T hij hik hjk hlast hi hj hk hij_order hjk_order
              hpath_contacts q hx_right ha hq_path hq_outside hq_clean)
  · rcases
        GMIX24Split.tripod_leg_nil_residual_arm_of_outside
          P T q hall hq_outside hnil_raw with
      ⟨r, hr, hxrim, hleg_nil, _hx_ne_attach, harm⟩
    rcases hr with hri | hrk
    · subst r
      rcases houter with hfirst | hlast
      · exact hfirst hleg_nil
      · exact hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_arm_residual_ordered_of_nil_last_not_nil
            P hno_cross T hij hik hjk hlast hi hj hk hij_order hjk_order
            hpath_contacts q hxrim hleg_nil harm ha hq_path hq_outside hq_clean)
    · subst r
      rcases houter with hfirst | hlast
      · exact hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_last_arm_residual_ordered_of_nil
            P hno_cross T hij hik hjk hfirst hi hj hk hij_order hjk_order
            hpath_contacts q hxrim hleg_nil harm ha hq_path hq_outside hq_clean)
      · exact hlast hleg_nil

/-- Direct ordered residual elimination when only the last ordered leg is known
to be nontrivial.

This removes the spurious middle-leg hypothesis from the source common-end
paragraph.  If the first ordered leg is nontrivial, the sharpened common-end
lift handles endpoint residuals even when the middle leg has collapsed.  If the
first leg has collapsed, the sharpened first-collapsed constructors use only the
last nontrivial leg.  A last-leg nil residual contradicts `hleg_k_not_nil`. -/
theorem canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_last_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_k_not_nil : Not (T.leg k).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    False :=
  ordered_residual_impossible_of_outer_choice
    P hno_cross hno_tripod T hij hik hjk (Or.inr hleg_k_not_nil)
    q ha hold hq_path hij_order hjk_order hq_outside hpath_contacts
    hq_clean hresidual

/-- Direct ordered residual elimination when only the first ordered leg is
known to be nontrivial.

This is the complementary collapsed-side form of the source common-end
paragraph.  Endpoint residuals use the sharpened common-end lift, which only
needs the first ordered leg.  A first-leg nil residual contradicts that
hypothesis, and a last-leg nil residual is handled by the weakened nil-last arm
constructor above. -/
theorem canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_first_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_not_nil : Not (T.leg i).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    False :=
  ordered_residual_impossible_of_outer_choice
    P hno_cross hno_tripod T hij hik hjk (Or.inl hleg_i_not_nil)
    q ha hold hq_path hij_order hjk_order hq_outside hpath_contacts
    hq_clean hresidual

/-- Direct ordered residual elimination under the exact first/last outer-leg
dichotomy.

This is the consolidated residual form used by the source side-tripod
paragraph: once the feet are ordered on the cut path, either nontrivial outer
leg supplies enough structure to turn the common-end or collapsed-side residual
into the forbidden ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_first_or_last_non_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_or_k_not_nil : Not (T.leg i).Nil ∨ Not (T.leg k).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    False :=
  ordered_residual_impossible_of_outer_choice
    P hno_cross hno_tripod T hij hik hjk hleg_i_or_k_not_nil
    q ha hold hq_path hij_order hjk_order hq_outside hpath_contacts
    hq_clean hresidual

/-- The ordered residual is reduced to the single collapsed-outer case.

The preceding direct constructors prove the source common-end/nil-residual
contradiction as soon as either outer ordered side leg is nontrivial.  Thus the
only residual case left by the side-tripod paragraph is the genuinely hard one:
both outer ordered legs have collapsed to their cut-path feet, and the middle
foot is the only possible non-collapsed attachment. -/
theorem canonicalOfNoCross_left_tripod_ordered_residual_outer_legs_nil_of_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    (T.leg i).Nil ∧ (T.leg k).Nil := by
  classical
  by_cases hleg_i_nil : (T.leg i).Nil
  · by_cases hleg_k_nil : (T.leg k).Nil
    · exact ⟨hleg_i_nil, hleg_k_nil⟩
    · exact False.elim
        (GMIX24Split.canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_first_or_last_non_nil
          P hno_cross hno_tripod T hij hik hjk
          (Or.inr hleg_k_nil) q ha hold hq_path hij_order
          hjk_order hq_outside hpath_contacts hq_clean hresidual)
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_tripod_ordered_residual_impossible_of_first_or_last_non_nil
        P hno_cross hno_tripod T hij hik hjk
        (Or.inl hleg_i_nil) q ha hold hq_path hij_order
        hjk_order hq_outside hpath_contacts hq_clean hresidual)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
