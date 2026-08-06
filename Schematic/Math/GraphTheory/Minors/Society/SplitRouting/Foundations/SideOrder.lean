import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.ReplacementLifts
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.BoundaryAlternation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_lift_of_all_endpoints_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoffPath : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet)
    (halternating :
      CrossEndpointAlternating S.boundary X.endpoints.endpoint) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_of_original_alternation
    P hno_cross X
    (fun i =>
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint_mem_original_of_off_path
        P hno_cross X (hoffPath i))
    halternating

theorem canonicalOfNoCross_left_cross_original_alternating_of_all_endpoints_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoffPath : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
  classical
  have harc :
      forall i : Fin 4, X.endpoints.endpoint i ∈ P.leftBoundaryArc := by
    intro i
    exact
      (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
        P hno_cross X i).mp (hoffPath i)
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  dsimp [CrossEndpointAlternating] at hside ⊢
  exact ⟨
    P.leftOrdered_clockwiseOpenBetween_original_of_arc
      (harc 0) (harc 2) (harc 1) hside.1,
    P.leftOrdered_clockwiseOpenBetween_original_of_arc
      (harc 2) (harc 0) (harc 3) hside.2⟩

theorem canonicalOfNoCross_left_cross_lift_of_all_endpoints_off_path_from_side_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoffPath : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_of_all_endpoints_off_path
    P hno_cross X hoffPath
    (GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_all_endpoints_off_path
      P hno_cross X hoffPath)

theorem canonicalOfNoCross_right_cross_lift_of_all_endpoints_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoffPath : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet)
    (halternating :
      CrossEndpointAlternating S.boundary X.endpoints.endpoint) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_of_original_alternation
    P hno_cross X
    (fun i =>
      GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
        P hno_cross X (hoffPath i))
    halternating

theorem canonicalOfNoCross_right_cross_original_alternating_of_all_endpoints_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoffPath : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_all_endpoints_off_path
      P.reverse hno_cross Xrev (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hoffPath i))
theorem canonicalOfNoCross_right_cross_lift_of_all_endpoints_off_path_from_side_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoffPath : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_of_all_endpoints_off_path
    P hno_cross X hoffPath
    (GMIX24Split.canonicalOfNoCross_right_cross_original_alternating_of_all_endpoints_off_path
      P hno_cross X hoffPath)

theorem canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint0 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint2 a) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  have hmem :
      forall i : Fin 4,
        X.endpoints.endpoint i ∈ P.leftOrderedCutBoundary.vertexSet := by
    intro i
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.endpoint_mem i
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have ha_mem : a ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.leftBoundaryArc_subset_leftOrderedCutBoundary ha
  have ha_lt :
      forall i : Fin 4,
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path ha (hall_path i)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  rcases
      crossEndpointAlternating_replaceEndpoint0_or_2_of_before_all
        P.leftOrderedCutBoundary hmem X.endpoints.endpoint_injective
        ha_mem ha_lt hside with h0 | h2
  · left
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint0_eq_replaceEndpointAt]
      using h0
  · right
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint2_eq_replaceEndpointAt]
      using h2

theorem canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint1 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint3 a) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  have hmem :
      forall i : Fin 4,
        X.endpoints.endpoint i ∈ P.leftOrderedCutBoundary.vertexSet := by
    intro i
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.endpoint_mem i
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have ha_mem : a ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.leftBoundaryArc_subset_leftOrderedCutBoundary ha
  have ha_lt :
      forall i : Fin 4,
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path ha (hall_path i)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  rcases
      crossEndpointAlternating_replaceEndpoint1_or_3_of_before_all
        P.leftOrderedCutBoundary hmem X.endpoints.endpoint_injective
        ha_mem ha_lt hside with h1 | h3
  · left
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint1_eq_replaceEndpointAt]
      using h1
  · right
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint3_eq_replaceEndpointAt]
      using h3

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_or_2_alternating_of_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint0 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint2 a) := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_all_on_path
      P.reverse hno_cross Xrev (by simpa using ha) (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hall_path i))
theorem canonicalOfNoCross_right_cross_replaceEndpoint1_or_3_alternating_of_all_on_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint1 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint3 a) := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_all_on_path
      P.reverse hno_cross Xrev (by simpa using ha) (by
        intro i
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hall_path i))
theorem canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_endpoint3_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne3 : a ≠ X.endpoints.endpoint 3) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint0 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint2 a) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  have hmem :
      forall i : Fin 4,
        X.endpoints.endpoint i ∈ P.leftOrderedCutBoundary.vertexSet := by
    intro i
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.endpoint_mem i
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h3_arc : X.endpoints.endpoint 3 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 3).mp h3_off
  have ha_lt :
      forall i : Fin 4, i ≠ 3 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path ha (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  have h3_lt :
      forall i : Fin 4, i ≠ 3 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint 3) <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path h3_arc (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  rcases
      crossEndpointAlternating_replaceEndpoint0_or_2_of_endpoint3_before_path
        P.leftOrderedCutBoundary hmem X.endpoints.endpoint_injective
        ha_lt h3_lt ha_ne3 hside with h0 | h2
  · left
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint0_eq_replaceEndpointAt]
      using h0
  · right
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint2_eq_replaceEndpointAt]
      using h2

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_or_2_alternating_of_endpoint3_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne3 : a ≠ X.endpoints.endpoint 3) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint0 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint2 a) := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_endpoint3_off_path
      P.reverse hno_cross Xrev (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h3_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using ha_ne3))
theorem canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_endpoint1_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne1 : a ≠ X.endpoints.endpoint 1) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint0 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint2 a) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  have hmem :
      forall i : Fin 4,
        X.endpoints.endpoint i ∈ P.leftOrderedCutBoundary.vertexSet := by
    intro i
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.endpoint_mem i
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h1_arc : X.endpoints.endpoint 1 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 1).mp h1_off
  have ha_lt :
      forall i : Fin 4, i ≠ 1 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path ha (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  have h1_lt :
      forall i : Fin 4, i ≠ 1 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint 1) <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path h1_arc (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  rcases
      crossEndpointAlternating_replaceEndpoint0_or_2_of_endpoint1_before_path
        P.leftOrderedCutBoundary hmem X.endpoints.endpoint_injective
        ha_lt h1_lt ha_ne1 hside with h0 | h2
  · left
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint0_eq_replaceEndpointAt]
      using h0
  · right
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint2_eq_replaceEndpointAt]
      using h2

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_or_2_alternating_of_endpoint1_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne1 : a ≠ X.endpoints.endpoint 1) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint0 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint2 a) := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_or_2_alternating_of_endpoint1_off_path
      P.reverse hno_cross Xrev (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h1_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using ha_ne1))
theorem canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_endpoint0_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne0 : a ≠ X.endpoints.endpoint 0) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint1 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint3 a) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h0_arc : X.endpoints.endpoint 0 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp h0_off
  have ha_mem : a ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.leftBoundaryArc_subset_leftOrderedCutBoundary ha
  have ha_lt :
      forall i : Fin 4, i ≠ 0 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path ha (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  have h0_lt :
      forall i : Fin 4, i ≠ 0 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint 0) <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path h0_arc (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  rcases
      crossEndpointAlternating_replaceEndpoint1_or_3_of_endpoint0_before_path
        P.leftOrderedCutBoundary ha_mem ha_lt h0_lt ha_ne0 hside with h1 | h3
  · left
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint1_eq_replaceEndpointAt]
      using h1
  · right
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint3_eq_replaceEndpointAt]
      using h3

theorem canonicalOfNoCross_right_cross_replaceEndpoint1_or_3_alternating_of_endpoint0_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne0 : a ≠ X.endpoints.endpoint 0) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint1 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint3 a) := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_endpoint0_off_path
      P.reverse hno_cross Xrev (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h0_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using ha_ne0))
theorem canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_endpoint2_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne2 : a ≠ X.endpoints.endpoint 2) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint1 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundary
        (X.replaceEndpoint3 a) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary
        X.endpoints.endpoint := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h2_arc : X.endpoints.endpoint 2 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp h2_off
  have ha_mem : a ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.leftBoundaryArc_subset_leftOrderedCutBoundary ha
  have ha_lt :
      forall i : Fin 4, i ≠ 2 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path ha (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  have h2_lt :
      forall i : Fin 4, i ≠ 2 ->
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint 2) <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary (X.endpoints.endpoint i) := by
    intro i hi
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path h2_arc (hothers_path i hi)
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  rcases
      crossEndpointAlternating_replaceEndpoint1_or_3_of_endpoint2_before_path
        P.leftOrderedCutBoundary ha_mem ha_lt h2_lt ha_ne2 hside with h1 | h3
  · left
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint1_eq_replaceEndpointAt]
      using h1
  · right
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical, Cross.replaceEndpoint3_eq_replaceEndpointAt]
      using h3

theorem canonicalOfNoCross_right_cross_replaceEndpoint1_or_3_alternating_of_endpoint2_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_ne2 : a ≠ X.endpoints.endpoint 2) :
    CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint1 a) ∨
      CrossEndpointAlternating
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundary
        (X.replaceEndpoint3 a) := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_or_3_alternating_of_endpoint2_off_path
      P.reverse hno_cross Xrev (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using h2_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hothers_path i hi)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using ha_ne2))
end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
