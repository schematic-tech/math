import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.MaximalSameSide
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.SideOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint3_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.firstPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  have hx_off_path : x ∉ P.pathSet := by
    exact (hq_outside x q.start_mem_support).2
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hx0 : x ≠ X.endpoints.endpoint 0 := by
    intro hx0
    exact hx_off_path (by
      simpa [hx0] using hothers_path 0 (by decide))
  have hx2 : x ≠ X.endpoints.endpoint 2 := by
    intro hx2
    exact hx_off_path (by
      simpa [hx2] using hothers_path 2 (by decide))
  have hx3 : x ≠ X.endpoints.endpoint 3 := by
    intro hx3
    have hxSecond : x ∈ X.secondPath.support := by
      simp [hx3]
    exact Set.disjoint_left.mp X.paths_disjoint hx hxSecond
  have ha_ne3 : a ≠ X.endpoints.endpoint 3 :=
    X.clean_tail_from_firstPath_hit_ne_endpoint q hq_clean hx3
  have hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
    X.firstPath_nonendpoint_not_boundary hx hx0 hx2
  have hinj0 : Function.Injective (X.replaceEndpoint0 a) := by
    refine X.replaceEndpoint0_injective ?_
    intro i hi hai
    by_cases hi3 : i = 3
    · subst i
      exact ha_ne3 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi3)
  have hinj2 : Function.Injective (X.replaceEndpoint2 a) := by
    refine X.replaceEndpoint2_injective ?_
    intro i hi hai
    by_cases hi3 : i = 3
    · subst i
      exact ha_ne3 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi3)
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_endpoint3_off_path
        P hno_cross X ha h3_off hothers_path ha_ne3 with h0 | h2
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h3_off hothers_path
        hinj0 h0 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h3_off hothers_path
        hinj2 h2 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint3_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.firstPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint3_off_path
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross) q
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h3_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
theorem canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint1_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.firstPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  have hx_off_path : x ∉ P.pathSet := by
    exact (hq_outside x q.start_mem_support).2
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hx0 : x ≠ X.endpoints.endpoint 0 := by
    intro hx0
    exact hx_off_path (by
      simpa [hx0] using hothers_path 0 (by decide))
  have hx2 : x ≠ X.endpoints.endpoint 2 := by
    intro hx2
    exact hx_off_path (by
      simpa [hx2] using hothers_path 2 (by decide))
  have hx1 : x ≠ X.endpoints.endpoint 1 := by
    intro hx1
    have hxSecond : x ∈ X.secondPath.support := by
      simp [hx1]
    exact Set.disjoint_left.mp X.paths_disjoint hx hxSecond
  have ha_ne1 : a ≠ X.endpoints.endpoint 1 :=
    X.clean_tail_from_firstPath_hit_ne_endpoint q hq_clean hx1
  have hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
    X.firstPath_nonendpoint_not_boundary hx hx0 hx2
  have hinj0 : Function.Injective (X.replaceEndpoint0 a) := by
    refine X.replaceEndpoint0_injective ?_
    intro i hi hai
    by_cases hi1 : i = 1
    · subst i
      exact ha_ne1 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi1)
  have hinj2 : Function.Injective (X.replaceEndpoint2 a) := by
    refine X.replaceEndpoint2_injective ?_
    intro i hi hai
    by_cases hi1 : i = 1
    · subst i
      exact ha_ne1 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi1)
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_endpoint1_off_path
        P hno_cross X ha h1_off hothers_path ha_ne1 with h0 | h2
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h1_off hothers_path
        hinj0 h0 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h1_off hothers_path
        hinj2 h2 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint1_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.firstPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint1_off_path
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross) q
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h1_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
theorem canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint0_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.secondPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  have hx_off_path : x ∉ P.pathSet := by
    exact (hq_outside x q.start_mem_support).2
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hx1 : x ≠ X.endpoints.endpoint 1 := by
    intro hx1
    exact hx_off_path (by
      simpa [hx1] using hothers_path 1 (by decide))
  have hx3 : x ≠ X.endpoints.endpoint 3 := by
    intro hx3
    exact hx_off_path (by
      simpa [hx3] using hothers_path 3 (by decide))
  have hx0 : x ≠ X.endpoints.endpoint 0 := by
    intro hx0
    have hxFirst : x ∈ X.firstPath.support := by
      simp [hx0]
    exact Set.disjoint_left.mp X.paths_disjoint hxFirst hx
  have ha_ne0 : a ≠ X.endpoints.endpoint 0 :=
    X.clean_tail_from_secondPath_hit_ne_endpoint q hq_clean hx0
  have hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
    X.secondPath_nonendpoint_not_boundary hx hx1 hx3
  have hinj1 : Function.Injective (X.replaceEndpoint1 a) := by
    refine X.replaceEndpoint1_injective ?_
    intro i hi hai
    by_cases hi0 : i = 0
    · subst i
      exact ha_ne0 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi0)
  have hinj3 : Function.Injective (X.replaceEndpoint3 a) := by
    refine X.replaceEndpoint3_injective ?_
    intro i hi hai
    by_cases hi0 : i = 0
    · subst i
      exact ha_ne0 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi0)
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_endpoint0_off_path
        P hno_cross X ha h0_off hothers_path ha_ne0 with h1 | h3
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h0_off hothers_path
        hinj1 h1 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h0_off hothers_path
        hinj3 h3 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint0_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.secondPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint0_off_path
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross) q
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h0_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
theorem canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint2_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.secondPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  have hx_off_path : x ∉ P.pathSet := by
    exact (hq_outside x q.start_mem_support).2
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  have hx1 : x ≠ X.endpoints.endpoint 1 := by
    intro hx1
    exact hx_off_path (by
      simpa [hx1] using hothers_path 1 (by decide))
  have hx3 : x ≠ X.endpoints.endpoint 3 := by
    intro hx3
    exact hx_off_path (by
      simpa [hx3] using hothers_path 3 (by decide))
  have hx2 : x ≠ X.endpoints.endpoint 2 := by
    intro hx2
    have hxFirst : x ∈ X.firstPath.support := by
      simp [hx2]
    exact Set.disjoint_left.mp X.paths_disjoint hxFirst hx
  have ha_ne2 : a ≠ X.endpoints.endpoint 2 :=
    X.clean_tail_from_secondPath_hit_ne_endpoint q hq_clean hx2
  have hx_not_boundary :
      x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
    X.secondPath_nonendpoint_not_boundary hx hx1 hx3
  have hinj1 : Function.Injective (X.replaceEndpoint1 a) := by
    refine X.replaceEndpoint1_injective ?_
    intro i hi hai
    by_cases hi2 : i = 2
    · subst i
      exact ha_ne2 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi2)
  have hinj3 : Function.Injective (X.replaceEndpoint3 a) := by
    refine X.replaceEndpoint3_injective ?_
    intro i hi hai
    by_cases hi2 : i = 2
    · subst i
      exact ha_ne2 hai
    · exact ha_off (by simpa [hai] using hothers_path i hi2)
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_endpoint2_off_path
        P hno_cross X ha h2_off hothers_path ha_ne2 with h1 | h3
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h2_off hothers_path
        hinj1 h1 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_single_old_off_path
        P hno_cross X hmax hx q ha (by decide) h2_off hothers_path
        hinj3 h3 hq_path hq_side hq_outside hq_boundary
        hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint2_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx : x ∈ X.secondPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint2_off_path
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross) q
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h2_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
theorem canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {l : Fin 4}
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx_first_if_second_endpoint_off :
      (l = 1 ∨ l = 3) -> x ∈ X.firstPath.support)
    (hx_second_if_first_endpoint_off :
      (l = 0 ∨ l = 2) -> x ∈ X.secondPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  fin_cases l
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint0_off_path
        P hno_cross X hmax q
        (hx_second_if_first_endpoint_off (Or.inl rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary
        (by
          intro w hw hwX
          exact hq_clean w hw (by
            rcases hwX with hwFirst | hwSecond
            · exact Or.inl hwFirst
            · exact Or.inr hwSecond)))
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint1_off_path
        P hno_cross X hmax q
        (hx_first_if_second_endpoint_off (Or.inl rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary
        (by
          intro w hw hwX
          exact hq_clean w hw (by
            rcases hwX with hwFirst | hwSecond
            · exact Or.inl hwFirst
            · exact Or.inr hwSecond)))
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint2_off_path
        P hno_cross X hmax q
        (hx_second_if_first_endpoint_off (Or.inr rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary
        (by
          intro w hw hwX
          exact hq_clean w hw (by
            rcases hwX with hwFirst | hwSecond
            · exact Or.inl hwFirst
            · exact Or.inr hwSecond)))
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_endpoint3_off_path
        P hno_cross X hmax q
        (hx_first_if_second_endpoint_off (Or.inr rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary
        (by
          intro w hw hwX
          exact hq_clean w hw (by
            rcases hwX with hwFirst | hwSecond
            · exact Or.inl hwFirst
            · exact Or.inr hwSecond)))

theorem canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {l : Fin 4}
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx_first_if_second_endpoint_off :
      (l = 1 ∨ l = 3) -> x ∈ X.firstPath.support)
    (hx_second_if_first_endpoint_off :
      (l = 0 ∨ l = 2) -> x ∈ X.secondPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  fin_cases l
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint0_off_path
        P hno_cross X hmax q
        (hx_second_if_first_endpoint_off (Or.inl rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary hq_clean)
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint1_off_path
        P hno_cross X hmax q
        (hx_first_if_second_endpoint_off (Or.inl rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary hq_clean)
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint2_off_path
        P hno_cross X hmax q
        (hx_second_if_first_endpoint_off (Or.inr rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary hq_clean)
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_endpoint3_off_path
        P hno_cross X hmax q
        (hx_first_if_second_endpoint_off (Or.inr rfl)) ha hl_off
        hothers_path hq_path hq_side hq_outside hq_boundary hq_clean)

theorem canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hxX : x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  have hx_off_path : x ∉ P.pathSet := by
    exact (hq_outside x q.start_mem_support).2
  have ha_off : a ∉ P.pathSet :=
    (P.leftBoundaryArc_subset_outside ha).2
  rcases hxX with hxFirst | hxSecond
  · have hx0 : x ≠ X.endpoints.endpoint 0 := by
      intro hx0
      exact hx_off_path (by simpa [hx0] using hall_path 0)
    have hx2 : x ≠ X.endpoints.endpoint 2 := by
      intro hx2
      exact hx_off_path (by simpa [hx2] using hall_path 2)
    have hx_not_boundary :
        x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
      X.firstPath_nonendpoint_not_boundary hxFirst hx0 hx2
    have hinj0 : Function.Injective (X.replaceEndpoint0 a) := by
      refine X.replaceEndpoint0_injective ?_
      intro i hi hai
      exact ha_off (by simpa [hai] using hall_path i)
    have hinj2 : Function.Injective (X.replaceEndpoint2 a) := by
      refine X.replaceEndpoint2_injective ?_
      intro i hi hai
      exact ha_off (by simpa [hai] using hall_path i)
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_all_on_path
          P hno_cross X ha hall_path with h0 | h2
    · exact
        GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail_impossible_of_maximal_all_on_path
          P hno_cross X hmax hxFirst q ha hall_path hinj0 h0 hq_path
          hq_side hq_outside hq_boundary hx_not_boundary hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail_impossible_of_maximal_all_on_path
          P hno_cross X hmax hxFirst q ha hall_path hinj2 h2 hq_path
          hq_side hq_outside hq_boundary hx_not_boundary hq_clean
  · have hx1 : x ≠ X.endpoints.endpoint 1 := by
      intro hx1
      exact hx_off_path (by simpa [hx1] using hall_path 1)
    have hx3 : x ≠ X.endpoints.endpoint 3 := by
      intro hx3
      exact hx_off_path (by simpa [hx3] using hall_path 3)
    have hx_not_boundary :
        x ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
      X.secondPath_nonendpoint_not_boundary hxSecond hx1 hx3
    have hinj1 : Function.Injective (X.replaceEndpoint1 a) := by
      refine X.replaceEndpoint1_injective ?_
      intro i hi hai
      exact ha_off (by simpa [hai] using hall_path i)
    have hinj3 : Function.Injective (X.replaceEndpoint3 a) := by
      refine X.replaceEndpoint3_injective ?_
      intro i hi hai
      exact ha_off (by simpa [hai] using hall_path i)
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_all_on_path
          P hno_cross X ha hall_path with h1 | h3
    · exact
        GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail_impossible_of_maximal_all_on_path
          P hno_cross X hmax hxSecond q ha hall_path hinj1 h1 hq_path
          hq_side hq_outside hq_boundary hx_not_boundary hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail_impossible_of_maximal_all_on_path
          P hno_cross X hmax hxSecond q ha hall_path hinj3 h3 hq_path
          hq_side hq_outside hq_boundary hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (q : S.graph.Walk x a)
    (hxX : x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    False := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_all_on_path
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross) q
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hxX)
      (by simpa using ha)
      (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hall_path i)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX))
theorem canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_count_zero
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 0)
    {x a : V}
    (q : S.graph.Walk x a)
    (hxX : x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  have hall_path :
      forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet :=
    (crossOffPathEndpointCount_eq_zero_iff_all_on_path P X).mp hcount
  exact False.elim
    (GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_impossible_of_maximal_all_on_path
      P hno_cross X hmax q hxX ha hall_path hq_path hq_side hq_outside
      hq_boundary hq_clean)

theorem canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_count_zero
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 0)
    {x a : V}
    (q : S.graph.Walk x a)
    (hxX : x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  have hall_path :
      forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet :=
    (crossOffPathEndpointCount_eq_zero_iff_all_on_path P X).mp hcount
  exact False.elim
    (GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_impossible_of_maximal_all_on_path
      P hno_cross X hmax q hxX ha hall_path hq_path hq_side hq_outside
      hq_boundary hq_clean)

theorem canonicalOfNoCross_left_cross_obstruction_of_maximal_count_zero
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 0) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  have hall_path :
      forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet :=
    (crossOffPathEndpointCount_eq_zero_iff_all_on_path P X).mp hcount
  obtain ⟨z, hzX, hzLeft⟩ :=
    GMIX24Split.canonicalOfNoCross_left_cross_with_path_endpoint_meets_leftSide
      P hno_cross X ⟨0, hall_path 0⟩
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_boundary_clean_tail_branch_cases
        P hno_cross X hzX hzLeft with hfirst | hsecond
  · obtain ⟨x, a, q, hx, ha, hq_path, hq_side, hq_outside,
      hq_boundary, hq_clean⟩ := hfirst
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_count_zero
        P hno_cross X hmax hcount q (Or.inl hx) ha hq_path hq_side
        hq_outside hq_boundary hq_clean
  · obtain ⟨x, a, q, hx, ha, hq_path, hq_side, hq_outside,
      hq_boundary, hq_clean⟩ := hsecond
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_count_zero
        P hno_cross X hmax hcount q (Or.inr hx) ha hq_path hq_side
        hq_outside hq_boundary hq_clean

theorem canonicalOfNoCross_right_cross_obstruction_of_maximal_count_zero
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 0) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  have hall_path :
      forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet :=
    (crossOffPathEndpointCount_eq_zero_iff_all_on_path P X).mp hcount
  obtain ⟨z, hzX, hzRight⟩ :=
    GMIX24Split.canonicalOfNoCross_right_cross_with_path_endpoint_meets_rightSide
      P hno_cross X ⟨0, hall_path 0⟩
  rcases
      GMIX24Split.canonicalOfNoCross_right_cross_boundary_clean_tail_branch_cases
        P hno_cross X hzX hzRight with hfirst | hsecond
  · obtain ⟨x, a, q, hx, ha, hq_path, hq_side, hq_outside,
      hq_boundary, hq_clean⟩ := hfirst
    exact
      GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_count_zero
        P hno_cross X hmax hcount q (Or.inl hx) ha hq_path hq_side
        hq_outside hq_boundary hq_clean
  · obtain ⟨x, a, q, hx, ha, hq_path, hq_side, hq_outside,
      hq_boundary, hq_clean⟩ := hsecond
    exact
      GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_count_zero
        P hno_cross X hmax hcount q (Or.inr hx) ha hq_path hq_side
        hq_outside hq_boundary hq_clean

theorem canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_count_one_aligned
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 1)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx_first_if_second_endpoint_off :
      (Exists fun l : Fin 4 =>
        (l = 1 ∨ l = 3) ∧
          X.endpoints.endpoint l ∉ P.pathSet ∧
            forall i : Fin 4, i ≠ l ->
              X.endpoints.endpoint i ∈ P.pathSet) ->
        x ∈ X.firstPath.support)
    (hx_second_if_first_endpoint_off :
      (Exists fun l : Fin 4 =>
        (l = 0 ∨ l = 2) ∧
          X.endpoints.endpoint l ∉ P.pathSet ∧
            forall i : Fin 4, i ≠ l ->
              X.endpoints.endpoint i ∈ P.pathSet) ->
        x ∈ X.secondPath.support)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  obtain ⟨l, hl_off, hothers_path⟩ :=
    (crossOffPathEndpointCount_eq_one_iff_exists_single_old_off_path P X).mp
      hcount
  refine
    GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
      P hno_cross X hmax hl_off hothers_path q ?_ ?_ ha hq_path
      hq_side hq_outside hq_boundary hq_clean
  · intro hl
    exact hx_first_if_second_endpoint_off
      ⟨l, hl, hl_off, hothers_path⟩
  · intro hl
    exact hx_second_if_first_endpoint_off
      ⟨l, hl, hl_off, hothers_path⟩

theorem canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_count_one_aligned
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 1)
    {x a : V}
    (q : S.graph.Walk x a)
    (hx_first_if_second_endpoint_off :
      (Exists fun l : Fin 4 =>
        (l = 1 ∨ l = 3) ∧
          X.endpoints.endpoint l ∉ P.pathSet ∧
            forall i : Fin 4, i ≠ l ->
              X.endpoints.endpoint i ∈ P.pathSet) ->
        x ∈ X.firstPath.support)
    (hx_second_if_first_endpoint_off :
      (Exists fun l : Fin 4 =>
        (l = 0 ∨ l = 2) ∧
          X.endpoints.endpoint l ∉ P.pathSet ∧
            forall i : Fin 4, i ≠ l ->
              X.endpoints.endpoint i ∈ P.pathSet) ->
        x ∈ X.secondPath.support)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  obtain ⟨l, hl_off, hothers_path⟩ :=
    (crossOffPathEndpointCount_eq_one_iff_exists_single_old_off_path P X).mp
      hcount
  refine
    GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
      P hno_cross X hmax hl_off hothers_path q ?_ ?_ ha hq_path
      hq_side hq_outside hq_boundary hq_clean
  · intro hl
    exact hx_first_if_second_endpoint_off
      ⟨l, hl, hl_off, hothers_path⟩
  · intro hl
    exact hx_second_if_first_endpoint_off
      ⟨l, hl, hl_off, hothers_path⟩

theorem canonicalOfNoCross_left_cross_obstruction_of_maximal_count_one_from_opposite_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 1)
    (hopposite_first :
      forall {l : Fin 4},
        l = 1 ∨ l = 3 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {z y a : V} (q : S.graph.Walk z a)
        (hyq : y ∈ q.support),
        z ∈ X.firstPath.support ->
          y ∈ X.secondPath.support ->
            a ∈ P.leftBoundaryArc ->
              q.IsPath ->
                (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ->
                      (forall w : V,
                        w ∈ (q.dropUntil y hyq).support ->
                          (w ∈ X.firstPath.support ∨
                            w ∈ X.secondPath.support) ->
                            w = y) ->
                        Nonempty S.Tripod)
    (hopposite_second :
      forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {z y a : V} (q : S.graph.Walk z a)
        (hyq : y ∈ q.support),
        z ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            a ∈ P.leftBoundaryArc ->
              q.IsPath ->
                (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ->
                      (forall w : V,
                        w ∈ (q.dropUntil y hyq).support ->
                          (w ∈ X.firstPath.support ∨
                            w ∈ X.secondPath.support) ->
                            w = y) ->
                        Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  obtain ⟨l, hl_off, hothers_path⟩ :=
    (crossOffPathEndpointCount_eq_one_iff_exists_single_old_off_path P X).mp
      hcount
  fin_cases l
  · obtain ⟨z, hzSecond, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint1_path
        P hno_cross X (hothers_path 1 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_secondPath_boundary_path_last_contact_cases
          P hno_cross X hzSecond hzLeft with haligned | hopposite
    · obtain ⟨x, a, q, hxSecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by
            intro h
            rcases h with h1 | h3
            · cases h1
            · cases h3)
          (by intro _h; exact hxSecond)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hyFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_second (Or.inl rfl) hl_off hothers_path q hyq
          hzSecond hyFirst ha hq_path hq_side hq_outside hq_boundary
          hq_clean)
  · obtain ⟨z, hzFirst, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint0_path
        P hno_cross X (hothers_path 0 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_firstPath_boundary_path_last_contact_cases
          P hno_cross X hzFirst hzLeft with haligned | hopposite
    · obtain ⟨x, a, q, hxFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by intro _h; exact hxFirst)
          (by
            intro h
            rcases h with h0 | h2
            · cases h0
            · cases h2)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hySecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_first (Or.inl rfl) hl_off hothers_path q hyq
          hzFirst hySecond ha hq_path hq_side hq_outside hq_boundary
          hq_clean)
  · obtain ⟨z, hzSecond, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint1_path
        P hno_cross X (hothers_path 1 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_secondPath_boundary_path_last_contact_cases
          P hno_cross X hzSecond hzLeft with haligned | hopposite
    · obtain ⟨x, a, q, hxSecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by
            intro h
            rcases h with h1 | h3
            · cases h1
            · cases h3)
          (by intro _h; exact hxSecond)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hyFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_second (Or.inr rfl) hl_off hothers_path q hyq
          hzSecond hyFirst ha hq_path hq_side hq_outside hq_boundary
          hq_clean)
  · obtain ⟨z, hzFirst, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint0_path
        P hno_cross X (hothers_path 0 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_firstPath_boundary_path_last_contact_cases
          P hno_cross X hzFirst hzLeft with haligned | hopposite
    · obtain ⟨x, a, q, hxFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by intro _h; exact hxFirst)
          (by
            intro h
            rcases h with h0 | h2
            · cases h0
            · cases h2)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hySecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_first (Or.inr rfl) hl_off hothers_path q hyq
          hzFirst hySecond ha hq_path hq_side hq_outside hq_boundary
          hq_clean)

theorem canonicalOfNoCross_right_cross_obstruction_of_maximal_count_one_from_opposite_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 1)
    (hopposite_first :
      forall {l : Fin 4},
        l = 1 ∨ l = 3 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {z y a : V} (q : S.graph.Walk z a)
        (hyq : y ∈ q.support),
        z ∈ X.firstPath.support ->
          y ∈ X.secondPath.support ->
            a ∈ P.rightBoundaryArc ->
              q.IsPath ->
                (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ->
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ->
                      (forall w : V,
                        w ∈ (q.dropUntil y hyq).support ->
                          (w ∈ X.firstPath.support ∨
                            w ∈ X.secondPath.support) ->
                            w = y) ->
                        Nonempty S.Tripod)
    (hopposite_second :
      forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {z y a : V} (q : S.graph.Walk z a)
        (hyq : y ∈ q.support),
        z ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            a ∈ P.rightBoundaryArc ->
              q.IsPath ->
                (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ->
                  (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
                    Walk.InternalVertices q ∩ S.boundarySet = ∅ ->
                      (forall w : V,
                        w ∈ (q.dropUntil y hyq).support ->
                          (w ∈ X.firstPath.support ∨
                            w ∈ X.secondPath.support) ->
                            w = y) ->
                        Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  obtain ⟨l, hl_off, hothers_path⟩ :=
    (crossOffPathEndpointCount_eq_one_iff_exists_single_old_off_path P X).mp
      hcount
  fin_cases l
  · obtain ⟨z, hzSecond, hzRight⟩ :=
      GMIX24Split.canonicalOfNoCross_right_cross_secondPath_meets_rightSide_of_endpoint1_path
        P hno_cross X (hothers_path 1 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_secondPath_boundary_path_last_contact_cases
          P hno_cross X hzSecond hzRight with haligned | hopposite
    · obtain ⟨x, a, q, hxSecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by
            intro h
            rcases h with h1 | h3
            · cases h1
            · cases h3)
          (by intro _h; exact hxSecond)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hyFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_second (Or.inl rfl) hl_off hothers_path q hyq
          hzSecond hyFirst ha hq_path hq_side hq_outside hq_boundary
          hq_clean)
  · obtain ⟨z, hzFirst, hzRight⟩ :=
      GMIX24Split.canonicalOfNoCross_right_cross_firstPath_meets_rightSide_of_endpoint0_path
        P hno_cross X (hothers_path 0 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_firstPath_boundary_path_last_contact_cases
          P hno_cross X hzFirst hzRight with haligned | hopposite
    · obtain ⟨x, a, q, hxFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by intro _h; exact hxFirst)
          (by
            intro h
            rcases h with h0 | h2
            · cases h0
            · cases h2)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hySecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_first (Or.inl rfl) hl_off hothers_path q hyq
          hzFirst hySecond ha hq_path hq_side hq_outside hq_boundary
          hq_clean)
  · obtain ⟨z, hzSecond, hzRight⟩ :=
      GMIX24Split.canonicalOfNoCross_right_cross_secondPath_meets_rightSide_of_endpoint1_path
        P hno_cross X (hothers_path 1 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_secondPath_boundary_path_last_contact_cases
          P hno_cross X hzSecond hzRight with haligned | hopposite
    · obtain ⟨x, a, q, hxSecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by
            intro h
            rcases h with h1 | h3
            · cases h1
            · cases h3)
          (by intro _h; exact hxSecond)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hyFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_second (Or.inr rfl) hl_off hothers_path q hyq
          hzSecond hyFirst ha hq_path hq_side hq_outside hq_boundary
          hq_clean)
  · obtain ⟨z, hzFirst, hzRight⟩ :=
      GMIX24Split.canonicalOfNoCross_right_cross_firstPath_meets_rightSide_of_endpoint0_path
        P hno_cross X (hothers_path 0 (by decide))
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_firstPath_boundary_path_last_contact_cases
          P hno_cross X hzFirst hzRight with haligned | hopposite
    · obtain ⟨x, a, q, hxFirst, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := haligned
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_clean_tail_obstruction_of_maximal_single_old_off_path_aligned
          P hno_cross X hmax hl_off hothers_path q
          (by intro _h; exact hxFirst)
          (by
            intro h
            rcases h with h0 | h2
            · cases h0
            · cases h2)
          ha hq_path hq_side hq_outside hq_boundary hq_clean
    · obtain ⟨y, a, q, hyq, hySecond, ha, hq_path, hq_side, hq_outside,
        hq_boundary, hq_clean⟩ := hopposite
      exact Or.inr
        (hopposite_first (Or.inr rfl) hl_off hothers_path q hyq
          hzFirst hySecond ha hq_path hq_side hq_outside hq_boundary
          hq_clean)

theorem canonicalOfNoCross_left_cross_obstruction_of_maximal_count_one_from_clean_branch_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 1)
    (htripod_first :
      forall {l : Fin 4},
        l = 1 ∨ l = 3 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.firstPath.support ->
          y ∈ X.secondPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod)
    (htripod_second :
      forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  refine
    GMIX24Split.canonicalOfNoCross_left_cross_obstruction_of_maximal_count_one_from_opposite_contact
      P hno_cross X hmax hcount ?_ ?_
  · intro l hl_second hl_off hothers_path z y a q hyq hzFirst hySecond
      _ha hq_path hq_side hq_outside _hq_boundary _hq_clean
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_first_to_second_inside
          P hno_cross X q hzFirst hyq hySecond hq_path hq_side hq_outside with
      ⟨x, y', r, hx, hy, hr_path, hclean_first, hclean_second,
        _hr_subset, hr_side, hr_outside⟩
    exact htripod_first hl_second hl_off hothers_path r hx hy hr_path
      hclean_first hclean_second hr_side hr_outside
  · intro l hl_first hl_off hothers_path z y a q hyq hzSecond hyFirst
      _ha hq_path hq_side hq_outside _hq_boundary _hq_clean
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_clean_branch_path_second_to_first_inside
          P hno_cross X q hzSecond hyq hyFirst hq_path hq_side hq_outside with
      ⟨x, y', r, hx, hy, hr_path, hclean_second, hclean_first,
        _hr_subset, hr_side, hr_outside⟩
    exact htripod_second hl_first hl_off hothers_path r hx hy hr_path
      hclean_second hclean_first hr_side hr_outside

theorem canonicalOfNoCross_right_cross_obstruction_of_maximal_count_one_from_clean_branch_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (hcount : crossOffPathEndpointCount X P = 1)
    (htripod_first :
      forall {l : Fin 4},
        l = 1 ∨ l = 3 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.firstPath.support ->
          y ∈ X.secondPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod)
    (htripod_second :
      forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  refine
    GMIX24Split.canonicalOfNoCross_right_cross_obstruction_of_maximal_count_one_from_opposite_contact
      P hno_cross X hmax hcount ?_ ?_
  · intro l hl_second hl_off hothers_path z y a q hyq hzFirst hySecond
      _ha hq_path hq_side hq_outside _hq_boundary _hq_clean
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_clean_branch_path_first_to_second_inside
          P hno_cross X q hzFirst hyq hySecond hq_path hq_side hq_outside with
      ⟨x, y', r, hx, hy, hr_path, hclean_first, hclean_second,
        _hr_subset, hr_side, hr_outside⟩
    exact htripod_first hl_second hl_off hothers_path r hx hy hr_path
      hclean_first hclean_second hr_side hr_outside
  · intro l hl_first hl_off hothers_path z y a q hyq hzSecond hyFirst
      _ha hq_path hq_side hq_outside _hq_boundary _hq_clean
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_clean_branch_path_second_to_first_inside
          P hno_cross X q hzSecond hyq hyFirst hq_path hq_side hq_outside with
      ⟨x, y', r, hx, hy, hr_path, hclean_second, hclean_first,
        _hr_subset, hr_side, hr_outside⟩
    exact htripod_second hl_first hl_off hothers_path r hx hy hr_path
      hclean_second hclean_first hr_side hr_outside

theorem canonicalOfNoCross_left_cross_lift_of_count_four
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 4) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_of_all_endpoints_off_path_from_side_order
    P hno_cross X
    ((crossOffPathEndpointCount_eq_four_iff_all_off_path P X).mp hcount)

theorem canonicalOfNoCross_right_cross_lift_of_count_four
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 4) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_of_all_endpoints_off_path_from_side_order
    P hno_cross X
    ((crossOffPathEndpointCount_eq_four_iff_all_off_path P X).mp hcount)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
