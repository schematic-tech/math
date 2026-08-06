import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.ReplacementLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P) :
    False := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint2 a) 2
    (by simp [Cross.replaceEndpoint2])
    (by
      intro i hi
      simp [Cross.replaceEndpoint2, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact hmax.not_replaceEndpoint2_with_tail_of_count_lt hx qD
    hendpoint_mem hendpoint_injective halternating hqD_path hqD_boundary
    hx_not_boundary hqD_clean hcount
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P) :
    False := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint0 a) 0
    (by simp [Cross.replaceEndpoint0])
    (by
      intro i hi
      simp [Cross.replaceEndpoint0, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact hmax.not_replaceEndpoint0_with_tail_of_count_lt hx qD
    hendpoint_mem hendpoint_injective halternating hqD_path hqD_boundary
    hx_not_boundary hqD_clean hcount
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P) :
    False := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint3 a) 3
    (by simp [Cross.replaceEndpoint3])
    (by
      intro i hi
      simp [Cross.replaceEndpoint3, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact hmax.not_replaceEndpoint3_with_tail_of_count_lt hx qD
    hendpoint_mem hendpoint_injective halternating hqD_path hqD_boundary
    hx_not_boundary hqD_clean hcount
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P) :
    False := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint1 a) 1
    (by simp [Cross.replaceEndpoint1])
    (by
      intro i hi
      simp [Cross.replaceEndpoint1, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact hmax.not_replaceEndpoint1_with_tail_of_count_lt hx qD
    hendpoint_mem hendpoint_injective halternating hqD_path hqD_boundary
    hx_not_boundary hqD_clean hcount
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
      (by
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross, crossOffPathEndpointCount,
          crossOffPathEndpointFinset, endpointOffPathCount,
          endpointOffPathFinset] using hcount)
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
      (by
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross, crossOffPathEndpointCount,
          crossOffPathEndpointFinset, endpointOffPathCount,
          endpointOffPathFinset] using hcount)
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
      (by
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross, crossOffPathEndpointCount,
          crossOffPathEndpointFinset, endpointOffPathCount,
          endpointOffPathFinset] using hcount)
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
      (by
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross, crossOffPathEndpointCount,
          crossOffPathEndpointFinset, endpointOffPathCount,
          endpointOffPathFinset] using hcount)
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P := by
    simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 2) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P := by
    simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 0) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P := by
    simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 3) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P := by
    simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 1) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P := by
    simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 2) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P := by
    simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 0) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P := by
    simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 3) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P := by
    simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
        P X (k := 1) hall_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    {l : Fin 4}
    (h2l : (2 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P := by
    simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 2) (l := l) h2l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    {l : Fin 4}
    (h0l : (0 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P := by
    simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 0) (l := l) h0l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    {l : Fin 4}
    (h3l : (3 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P := by
    simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 3) (l := l) h3l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    {l : Fin 4}
    (h1l : (1 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P := by
    simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 1) (l := l) h1l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    {l : Fin 4}
    (h2l : (2 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P := by
    simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 2) (l := l) h2l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    {l : Fin 4}
    (h0l : (0 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P := by
    simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 0) (l := l) h0l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    {l : Fin 4}
    (h3l : (3 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P := by
    simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 3) (l := l) h3l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount

theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_single_old_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    {l : Fin 4}
    (h1l : (1 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  have ha_off : a ∉ P.pathSet :=
    (P.rightBoundaryArc_subset_outside ha).2
  have hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P := by
    simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
      crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
        P X (k := 1) (l := l) h1l hl_off hothers_path ha_off
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal
      P hno_cross X hmax hx q ha hendpoint_injective halternating hq_path
      hq_side hq_outside hq_boundary hx_not_boundary hq_clean hcount


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
