import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.SideBoundaryFacts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem endpoint_ne_start_of_off_path
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    {i : Fin 4}
    (hoff : X.endpoints.endpoint i ∉ P.pathSet) :
    P.s ≠ X.endpoints.endpoint i := by
  intro h
  exact hoff (by simpa [h] using P.s_mem_pathSet)

theorem endpoint_ne_end_of_off_path
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    {i : Fin 4}
    (hoff : X.endpoints.endpoint i ∉ P.pathSet) :
    P.t ≠ X.endpoints.endpoint i := by
  intro h
  exact hoff (by simpa [h] using P.t_mem_pathSet)

theorem cutPath_start_mem_boundarySet {S : GeneralSociety V}
    (P : GMIX24CutPath S) : P.s ∈ S.boundarySet := by
  simpa [GeneralSociety.boundarySet] using P.s_mem_boundary

theorem cutPath_end_mem_boundarySet {S : GeneralSociety V}
    (P : GMIX24CutPath S) : P.t ∈ S.boundarySet := by
  simpa [GeneralSociety.boundarySet] using P.t_mem_boundary

/-- Replace one of a cross's four boundary endpoints. -/
def replaceCrossEndpointAt {H : GeneralSociety V} (X : H.Cross)
    (k : Fin 4) (a : V) : Fin 4 -> V :=
  fun i => if i = k then a else X.endpoints.endpoint i

/-- Replacing the unique cut-path endpoint of a left-side cross by any
ambient boundary vertex again gives ambient boundary endpoints. -/
theorem canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (k : Fin 4) (a : V) (ha : a ∈ S.boundarySet)
    (hoff : forall i : Fin 4, i ≠ k -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, replaceCrossEndpointAt X k a i ∈ S.boundarySet := by
  intro i
  by_cases hi : i = k
  · subst i
    simpa [replaceCrossEndpointAt] using ha
  · simpa [replaceCrossEndpointAt, hi, GeneralSociety.boundarySet] using
      P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
          P hno_cross X i).mp (hoff i hi))

/-- Right-side counterpart of
`canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path`. -/
theorem canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (k : Fin 4) (a : V) (ha : a ∈ S.boundarySet)
    (hoff : forall i : Fin 4, i ≠ k -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, replaceCrossEndpointAt X k a i ∈ S.boundarySet := by
  intro i
  by_cases hi : i = k
  · subst i
    simpa [replaceCrossEndpointAt] using ha
  · simpa [replaceCrossEndpointAt, hi, GeneralSociety.boundarySet] using
      P.rightBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
          P hno_cross X i).mp (hoff i hi))

theorem canonicalOfNoCross_left_cross_replaceEndpoint2_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint2 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 2 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint2_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint2 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 2 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint2_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint2 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 2 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint2_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint2 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 2 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint0_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint0 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 0 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint0_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint0 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 0 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint0 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 0 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint0 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 0 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint3_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint3 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 3 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint3_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint3 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 3 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint3_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint3 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 3 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint3_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint3 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 3 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint1_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint1 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 1 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint1_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint1 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 1 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint1_mem_original_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint1 P.s i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 1 P.s (cutPath_start_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint1_mem_original_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint1 P.t i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 1 P.t (cutPath_end_mem_boundarySet P) hoff)

theorem canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint0_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hendpoint : X.endpoints.endpoint 0 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.firstPath.support ∧ z ∈ P.leftSide := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.leftGraph_walk_from_path_meets_leftSide
      X.firstPath hendpoint X.firstPath_nontrivial
      (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_support_subset_side_or_path
        P hno_cross X)

theorem canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint2_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hendpoint : X.endpoints.endpoint 2 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.firstPath.support ∧ z ∈ P.leftSide := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.leftGraph_walk_to_path_meets_leftSide
      X.firstPath hendpoint X.firstPath_nontrivial
      (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_support_subset_side_or_path
        P hno_cross X)

theorem canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint1_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hendpoint : X.endpoints.endpoint 1 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.secondPath.support ∧ z ∈ P.leftSide := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.leftGraph_walk_from_path_meets_leftSide
      X.secondPath hendpoint X.secondPath_nontrivial
      (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_support_subset_side_or_path
        P hno_cross X)

theorem canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint3_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hendpoint : X.endpoints.endpoint 3 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.secondPath.support ∧ z ∈ P.leftSide := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.leftGraph_walk_to_path_meets_leftSide
      X.secondPath hendpoint X.secondPath_nontrivial
      (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_support_subset_side_or_path
        P hno_cross X)

theorem canonicalOfNoCross_right_cross_firstPath_meets_rightSide_of_endpoint0_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hendpoint : X.endpoints.endpoint 0 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.firstPath.support ∧ z ∈ P.rightSide := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint0_path
      P.reverse hno_cross Xrev (by simpa [Xrev] using hendpoint))

theorem canonicalOfNoCross_right_cross_firstPath_meets_rightSide_of_endpoint2_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hendpoint : X.endpoints.endpoint 2 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.firstPath.support ∧ z ∈ P.rightSide := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint2_path
      P.reverse hno_cross Xrev (by simpa [Xrev] using hendpoint))

theorem canonicalOfNoCross_right_cross_secondPath_meets_rightSide_of_endpoint1_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hendpoint : X.endpoints.endpoint 1 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.secondPath.support ∧ z ∈ P.rightSide := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint1_path
      P.reverse hno_cross Xrev (by simpa [Xrev] using hendpoint))

theorem canonicalOfNoCross_right_cross_secondPath_meets_rightSide_of_endpoint3_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hendpoint : X.endpoints.endpoint 3 ∈ P.pathSet) :
    Exists fun z : V => z ∈ X.secondPath.support ∧ z ∈ P.rightSide := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint3_path
      P.reverse hno_cross Xrev (by simpa [Xrev] using hendpoint))

theorem canonicalOfNoCross_left_cross_with_path_endpoint_meets_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun z : V =>
      (z ∈ X.firstPath.support ∨ z ∈ X.secondPath.support) ∧
        z ∈ P.leftSide := by
  rcases hpath with ⟨i, hi⟩
  fin_cases i
  · obtain ⟨z, hz, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint0_path
        P hno_cross X hi
    exact ⟨z, Or.inl hz, hzLeft⟩
  · obtain ⟨z, hz, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint1_path
        P hno_cross X hi
    exact ⟨z, Or.inr hz, hzLeft⟩
  · obtain ⟨z, hz, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_firstPath_meets_leftSide_of_endpoint2_path
        P hno_cross X hi
    exact ⟨z, Or.inl hz, hzLeft⟩
  · obtain ⟨z, hz, hzLeft⟩ :=
      GMIX24Split.canonicalOfNoCross_left_cross_secondPath_meets_leftSide_of_endpoint3_path
        P hno_cross X hi
    exact ⟨z, Or.inr hz, hzLeft⟩

theorem canonicalOfNoCross_right_cross_with_path_endpoint_meets_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun z : V =>
      (z ∈ X.firstPath.support ∨ z ∈ X.secondPath.support) ∧
        z ∈ P.rightSide := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_with_path_endpoint_meets_leftSide
      P.reverse hno_cross Xrev (by simpa [Xrev] using hpath))

theorem canonicalOfNoCross_left_cross_path_endpoint_side_to_boundary_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun z : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk z a =>
          (z ∈ X.firstPath.support ∨ z ∈ X.secondPath.support) ∧
            z ∈ P.leftSide ∧ a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                forall w : V, w ∈ q.support -> w ∈ P.outside := by
  obtain ⟨z, hzX, hzLeft⟩ :=
    GMIX24Split.canonicalOfNoCross_left_cross_with_path_endpoint_meets_leftSide
      P hno_cross X hpath
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside hzLeft
  exact ⟨z, a, q, hzX, hzLeft, ha, hqPath, hqLeft, hqOutside⟩

theorem canonicalOfNoCross_right_cross_path_endpoint_side_to_boundary_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun z : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk z a =>
          (z ∈ X.firstPath.support ∨ z ∈ X.secondPath.support) ∧
            z ∈ P.rightSide ∧ a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                forall w : V, w ∈ q.support -> w ∈ P.outside := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_path_endpoint_side_to_boundary_path
      P.reverse hno_cross Xrev (by simpa [Xrev] using hpath))

theorem canonicalOfNoCross_left_cross_path_endpoint_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          (x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support) ∧
            a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  forall w : V,
                    w ∈ q.support ->
                      (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                        w = x := by
  classical
  obtain ⟨z, a, q, hzX, _hzLeft, ha, hqPath, hqLeft, hqOutside⟩ :=
    GMIX24Split.canonicalOfNoCross_left_cross_path_endpoint_side_to_boundary_path
      P hno_cross X hpath
  let A : Set V := {w : V | w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support}
  have hzA : z ∈ A := by
    simpa [A] using hzX
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hzA
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  refine ⟨x, a, tail, ?_, ha, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqLeft w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)

theorem canonicalOfNoCross_right_cross_path_endpoint_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          (x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support) ∧
            a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  forall w : V,
                    w ∈ q.support ->
                      (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                        w = x := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_path_endpoint_clean_tail_to_boundary
      P.reverse hno_cross Xrev (by simpa [Xrev] using hpath))

theorem canonicalOfNoCross_left_cross_path_endpoint_boundary_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          (x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support) ∧
            a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ q.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x := by
  classical
  obtain ⟨z, hzX, hzLeft⟩ :=
    GMIX24Split.canonicalOfNoCross_left_cross_with_path_endpoint_meets_leftSide
      P hno_cross X hpath
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside, hqBoundaryClean⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
      hno_cross hzLeft
  let A : Set V := {w : V | w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support}
  have hzA : z ∈ A := by
    simpa [A] using hzX
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hzA
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  have htail_boundary_clean :
      Walk.InternalVertices tail ∩ S.boundarySet = ∅ := by
    simpa [tail] using
      Walk.IsPath.dropUntil_internalVertices_disjoint_of_internalVertices_disjoint
        hqPath hxq S.boundarySet hqBoundaryClean
  refine ⟨x, a, tail, ?_, ha, ?_, ?_, ?_, htail_boundary_clean, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqLeft w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwA
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwA)

theorem canonicalOfNoCross_right_cross_path_endpoint_boundary_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk x a =>
          (x ∈ X.firstPath.support ∨ x ∈ X.secondPath.support) ∧
            a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ q.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ q.support ->
                        (w ∈ X.firstPath.support ∨
                          w ∈ X.secondPath.support) ->
                          w = x := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_path_endpoint_boundary_clean_tail_to_boundary
      P.reverse hno_cross Xrev (by simpa [Xrev] using hpath))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
