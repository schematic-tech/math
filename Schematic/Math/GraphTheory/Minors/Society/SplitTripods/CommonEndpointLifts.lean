import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.ContactEscapes

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

end GMIX24Split

/-- A path leaving the common left end of a tripod, with no later tripod
contact and with support in a prescribed ambient region. -/
structure Tripod.CleanTailFromLeft {R : GeneralSociety V}
    (T : R.Tripod) (G : SimpleGraph V) (outside : Set V) (a : V) where
  walk : G.Walk T.left a
  isPath : walk.IsPath
  support_subset : forall w : V, w ∈ walk.support -> w ∈ outside
  clean : forall w : V, w ∈ walk.support -> w ∈ T.vertexSet -> w = T.left

/-- Reindex the start of a clean tail to the tripod's left endpoint. -/
def Tripod.CleanTailFromLeft.ofCopy {R : GeneralSociety V}
    (T : R.Tripod) {G : SimpleGraph V} {outside : Set V} {x a : V}
    (q : G.Walk x a)
    (hx : x = T.left)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ outside)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun r : Fin 3 =>
          w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
        w = x) :
    T.CleanTailFromLeft G outside a where
  walk := q.copy hx rfl
  isPath := (SimpleGraph.Walk.isPath_copy q hx rfl).mpr hq_path
  support_subset := by
    intro w hw
    exact hq_outside w (by simpa using hw)
  clean := by
    intro w hw hwT
    have hwx := hq_clean w (by simpa using hw) (by simpa using hwT)
    simpa [hx] using hwx

namespace GMIX24Split

/-- Ordered common-left endpoint lift for a left side-tripod of the canonical
split.  This is the split-level adapter for the source sentence that, when
the clean outside path starts at the old left common end, `Q, P_1, P_2, P_3`
already form an ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_i_not_nil : Not (T.leg i).Nil)
      (hleg_j_not_nil : Not (T.leg j).Nil)
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
    (hx_left : x = T.left)
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
  let tail :=
    Tripod.CleanTailFromLeft.ofCopy T q hx_left hq_path hq_outside hq_clean
  exact
    T.liftCommonLeftEndpointOrdered P
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_i_not_nil hleg_j_not_nil
      hi hj hk hij_order hjk_order ha tail.walk tail.isPath
      tail.support_subset tail.clean hpath_contacts

/-- Sharper ordered common-left endpoint lift: the second ordered old leg may
be trivial. -/
theorem canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered_first_not_nil
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
    (hx_left : x = T.left)
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
  let tail :=
    Tripod.CleanTailFromLeft.ofCopy T q hx_left hq_path hq_outside hq_clean
  exact
    T.liftCommonLeftEndpointOrdered_first_not_nil P
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_i_not_nil
      hi hj hk hij_order hjk_order ha tail.walk tail.isPath
      tail.support_subset tail.clean hpath_contacts

/-- Ordered common-right endpoint lift for a left side-tripod, obtained by
flipping the old rim endpoints and reusing the common-left constructor. -/
theorem canonicalOfNoCross_left_tripod_lift_common_right_endpoint_ordered
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
      (hno_cross : Not (Nonempty S.Cross))
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      {i j k : Fin 3}
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hleg_i_not_nil : Not (T.leg i).Nil)
      (hleg_j_not_nil : Not (T.leg j).Nil)
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
    (hx_right : x = T.right)
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
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered
      P hno_cross Tflip hij hik hjk
      (by simpa [Tflip] using hleg_i_not_nil)
      (by simpa [Tflip] using hleg_j_not_nil)
      (by simpa [Tflip] using hi)
      (by simpa [Tflip] using hj)
      (by simpa [Tflip] using hk)
      (by simpa [Tflip] using hij_order)
      (by simpa [Tflip] using hjk_order)
      (by
        intro z hzPath hzT
        simpa [Tflip] using hpath_contacts z hzPath (by simpa [Tflip] using hzT))
      q (by simpa [Tflip] using hx_right) ha hq_path hq_outside
      (by
        intro w hw hT
        exact hq_clean w hw (by
          simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hT))

/-- Sharper ordered common-right endpoint lift: the second ordered old leg may
be trivial. -/
theorem canonicalOfNoCross_left_tripod_lift_common_right_endpoint_ordered_first_not_nil
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
    (hx_right : x = T.right)
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
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered_first_not_nil
      P hno_cross Tflip hij hik hjk
      (by simpa [Tflip] using hleg_i_not_nil)
      (by simpa [Tflip] using hi)
      (by simpa [Tflip] using hj)
      (by simpa [Tflip] using hk)
      (by simpa [Tflip] using hij_order)
      (by simpa [Tflip] using hjk_order)
      (by
        intro z hzPath hzT
        simpa [Tflip] using hpath_contacts z hzPath (by simpa [Tflip] using hzT))
      q (by simpa [Tflip] using hx_right) ha hq_path hq_outside
      (by
        intro w hw hT
        exact hq_clean w hw (by
          simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hT))

/-- Ordered first-collapsed common-left endpoint lift for a left side-tripod.

This is the split-level source construction for the case where the first ordered
side-tripod leg has collapsed and the clean outside tail starts at the old left
common end.  It rebuilds the ambient tripod from the middle and last ordered
feet, avoiding the nontrivial-first-leg hypothesis required by the ordinary
common-end lift. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_first_common_left_endpoint_ordered
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
    (hx_left : x = T.left)
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
  let tail :=
    Tripod.CleanTailFromLeft.ofCopy T q hx_left hq_path hq_outside hq_clean
  exact
    T.liftFirstNilResidualCommonLeftEndpoint P
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_k_not_nil
      hi hj hk hij_order hjk_order tail.walk ha tail.isPath
      tail.support_subset tail.clean hpath_contacts

/-- Ordered first-collapsed common-right endpoint lift for a left side-tripod,
obtained by flipping the old rim endpoints and reusing the common-left
first-collapsed constructor. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_first_common_right_endpoint_ordered
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
    (hx_right : x = T.right)
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
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_common_left_endpoint_ordered
      P hno_cross Tflip hij hik hjk
      (by simpa [Tflip] using hleg_k_not_nil)
      (by simpa [Tflip] using hi)
      (by simpa [Tflip] using hj)
      (by simpa [Tflip] using hk)
      (by simpa [Tflip] using hij_order)
      (by simpa [Tflip] using hjk_order)
      (by
        intro z hzPath hzT
        simpa [Tflip] using hpath_contacts z hzPath (by simpa [Tflip] using hzT))
      q (by simpa [Tflip] using hx_right) ha hq_path hq_outside
      (by
        intro w hw hT
        exact hq_clean w hw (by
          simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hT))

/-- Sharper first-collapsed common-left endpoint lift: the middle ordered old
leg may also be trivial. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_first_common_left_endpoint_ordered_last_not_nil
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
    (hx_left : x = T.left)
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
  let tail :=
    Tripod.CleanTailFromLeft.ofCopy T q hx_left hq_path hq_outside hq_clean
  exact
    T.liftFirstNilResidualCommonLeftEndpoint_last_not_nil P
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      hij hik hjk hleg_k_not_nil
      hi hj hk hij_order hjk_order tail.walk ha tail.isPath
      tail.support_subset tail.clean hpath_contacts

/-- Sharper first-collapsed common-right endpoint lift: the middle ordered old
leg may also be trivial. -/
theorem canonicalOfNoCross_left_tripod_lift_nil_first_common_right_endpoint_ordered_last_not_nil
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
    (hx_right : x = T.right)
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
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_nil_first_common_left_endpoint_ordered_last_not_nil
      P hno_cross Tflip hij hik hjk
      (by simpa [Tflip] using hleg_k_not_nil)
      (by simpa [Tflip] using hi)
      (by simpa [Tflip] using hj)
      (by simpa [Tflip] using hk)
      (by simpa [Tflip] using hij_order)
      (by simpa [Tflip] using hjk_order)
      (by
        intro z hzPath hzT
        simpa [Tflip] using hpath_contacts z hzPath (by simpa [Tflip] using hzT))
      q (by simpa [Tflip] using hx_right) ha hq_path hq_outside
      (by
        intro w hw hT
        exact hq_clean w hw (by
          simpa [Tflip, Tripod.flip, SimpleGraph.Walk.support_reverse] using hT))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
