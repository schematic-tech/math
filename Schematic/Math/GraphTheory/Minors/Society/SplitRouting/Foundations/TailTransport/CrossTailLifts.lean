import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.TailTransport.InternalBoundary

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint2 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  refine ⟨X.lift_replaceEndpoint2_with_tail
    D.leftSociety_graph_le hx q hendpoint_mem hendpoint_injective
    halternating hq_path hq_boundary hx_not_boundary hq_clean ?_ ?_⟩
  · intro hxS z hz hzB
    exact
      Walk.IsPath.takeUntil_boundary_subset_start_or_cut
        (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
          X.firstPath_isPath)
        hxS S.boundarySet
        (GMIX24Split.canonicalOfNoCross_left_cross_first_internal_boundary_original
          P hno_cross X)
        z hz hzB
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_second_internal_boundary_original
        P hno_cross X

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint0 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  refine ⟨X.lift_replaceEndpoint0_with_tail
    D.leftSociety_graph_le hx q hendpoint_mem hendpoint_injective
    halternating hq_path hq_boundary hx_not_boundary hq_clean ?_ ?_⟩
  · intro hxS z hz hzB
    exact
      Walk.IsPath.dropUntil_boundary_subset_cut_or_end
        (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
          X.firstPath_isPath)
        hxS S.boundarySet
        (GMIX24Split.canonicalOfNoCross_left_cross_first_internal_boundary_original
          P hno_cross X)
        z hz hzB
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_second_internal_boundary_original
        P hno_cross X

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint3 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  refine ⟨X.lift_replaceEndpoint3_with_tail
    D.leftSociety_graph_le hx q hendpoint_mem hendpoint_injective
    halternating hq_path hq_boundary hx_not_boundary hq_clean ?_ ?_⟩
  · intro hxS z hz hzB
    exact
      Walk.IsPath.takeUntil_boundary_subset_start_or_cut
        (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
          X.secondPath_isPath)
        hxS S.boundarySet
        (GMIX24Split.canonicalOfNoCross_left_cross_second_internal_boundary_original
          P hno_cross X)
        z hz hzB
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_first_internal_boundary_original
        P hno_cross X

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint1 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  refine ⟨X.lift_replaceEndpoint1_with_tail
    D.leftSociety_graph_le hx q hendpoint_mem hendpoint_injective
    halternating hq_path hq_boundary hx_not_boundary hq_clean ?_ ?_⟩
  · intro hxS z hz hzB
    exact
      Walk.IsPath.dropUntil_boundary_subset_cut_or_end
        (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
          X.secondPath_isPath)
        hxS S.boundarySet
        (GMIX24Split.canonicalOfNoCross_left_cross_second_internal_boundary_original
          P hno_cross X)
        z hz hzB
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_first_internal_boundary_original
        P hno_cross X

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint2 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q
      (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_mem i)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path hq_boundary hx_not_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint0 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q
      (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_mem i)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path hq_boundary hx_not_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint3 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q
      (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_mem i)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path hq_boundary hx_not_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint1 a i ∈ S.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary : x ∉ S.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q
      (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_mem i)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path hq_boundary hx_not_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

