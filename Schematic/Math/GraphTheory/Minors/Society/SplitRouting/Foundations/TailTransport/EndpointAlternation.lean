import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.TailTransport.SinglePathLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_lift_of_original_alternation
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hendpoint_mem :
      forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet)
    (halternating :
      CrossEndpointAlternating S.boundary X.endpoints.endpoint) :
    Nonempty S.Cross :=
  ⟨X.lift_of_le
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    hendpoint_mem halternating
    (GMIX24Split.canonicalOfNoCross_left_cross_first_internal_boundary_original
      P hno_cross X)
    (GMIX24Split.canonicalOfNoCross_left_cross_second_internal_boundary_original
      P hno_cross X)⟩

theorem canonicalOfNoCross_right_cross_lift_of_original_alternation
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hendpoint_mem :
      forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet)
    (halternating :
      CrossEndpointAlternating S.boundary X.endpoints.endpoint) :
    Nonempty S.Cross :=
  ⟨X.lift_of_le
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le
    hendpoint_mem halternating
    (GMIX24Split.canonicalOfNoCross_right_cross_first_internal_boundary_original
      P hno_cross X)
    (GMIX24Split.canonicalOfNoCross_right_cross_second_internal_boundary_original
      P hno_cross X)⟩

theorem canonicalOfNoCross_left_cross_endpoint_mem_original_of_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {i : Fin 4}
    (hoffPath : X.endpoints.endpoint i ∉ P.pathSet) :
    X.endpoints.endpoint i ∈ S.boundary.vertexSet :=
  P.leftBoundaryArc_subset
    ((GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X i).mp hoffPath)

theorem canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {i : Fin 4}
    (hoffPath : X.endpoints.endpoint i ∉ P.pathSet) :
    X.endpoints.endpoint i ∈ S.boundary.vertexSet :=
  P.rightBoundaryArc_subset
    ((GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X i).mp hoffPath)

private theorem canonicalOfNoCross_left_cross_lift_of_only_endpoint_on_path_or_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (k : Fin 4)
    (hoff : forall i : Fin 4, i ≠ k -> X.endpoints.endpoint i ∉ P.pathSet)
    (horiginal_alt :
      X.endpoints.endpoint k ∈ S.boundarySet ->
        CrossEndpointAlternating S.boundary X.endpoints.endpoint)
    (htail_alt :
      X.endpoints.endpoint k ∉ S.boundarySet ->
        CrossEndpointAlternating S.boundary
          (replaceCrossEndpointAt X k P.t))
    (hlift :
      X.endpoints.endpoint k ∉ S.boundarySet ->
        CrossEndpointAlternating S.boundary
          (replaceCrossEndpointAt X k P.t) ->
        Nonempty S.Cross) :
    Nonempty S.Cross := by
  by_cases hb : X.endpoints.endpoint k ∈ S.boundarySet
  · apply canonicalOfNoCross_left_cross_lift_of_original_alternation
      P hno_cross X
    · intro i
      by_cases hi : i = k
      · subst i
        simpa [GeneralSociety.boundarySet] using hb
      · exact canonicalOfNoCross_left_cross_endpoint_mem_original_of_off_path
          P hno_cross X (hoff i hi)
    · exact horiginal_alt hb
  · exact hlift hb (htail_alt hb)

theorem canonicalOfNoCross_left_cross_lift_of_only_endpoint2_on_path_or_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (horiginal_alt :
      X.endpoints.endpoint 2 ∈ S.boundarySet ->
        CrossEndpointAlternating S.boundary X.endpoints.endpoint)
    (htail_alt :
      X.endpoints.endpoint 2 ∉ S.boundarySet ->
        CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.t)) :
    Nonempty S.Cross := by
  apply canonicalOfNoCross_left_cross_lift_of_only_endpoint_on_path_or_to_end
    P hno_cross X 2 hoff horiginal_alt
  · intro hb
    simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using htail_alt hb
  · intro hb halt
    exact canonicalOfNoCross_left_cross_lift_replaceEndpoint2_to_end_of_single_path
      P hno_cross X hpath hoff hb
      (by simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using halt)

theorem canonicalOfNoCross_left_cross_lift_of_only_endpoint0_on_path_or_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 0 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (horiginal_alt :
      X.endpoints.endpoint 0 ∈ S.boundarySet ->
        CrossEndpointAlternating S.boundary X.endpoints.endpoint)
    (htail_alt :
      X.endpoints.endpoint 0 ∉ S.boundarySet ->
        CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.t)) :
    Nonempty S.Cross := by
  apply canonicalOfNoCross_left_cross_lift_of_only_endpoint_on_path_or_to_end
    P hno_cross X 0 hoff horiginal_alt
  · intro hb
    simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using htail_alt hb
  · intro hb halt
    exact canonicalOfNoCross_left_cross_lift_replaceEndpoint0_to_end_of_single_path
      P hno_cross X hpath hoff hb
      (by simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using halt)

theorem canonicalOfNoCross_left_cross_lift_of_only_endpoint3_on_path_or_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (horiginal_alt :
      X.endpoints.endpoint 3 ∈ S.boundarySet ->
        CrossEndpointAlternating S.boundary X.endpoints.endpoint)
    (htail_alt :
      X.endpoints.endpoint 3 ∉ S.boundarySet ->
        CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.t)) :
    Nonempty S.Cross := by
  apply canonicalOfNoCross_left_cross_lift_of_only_endpoint_on_path_or_to_end
    P hno_cross X 3 hoff horiginal_alt
  · intro hb
    simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using htail_alt hb
  · intro hb halt
    exact canonicalOfNoCross_left_cross_lift_replaceEndpoint3_to_end_of_single_path
      P hno_cross X hpath hoff hb
      (by simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using halt)

theorem canonicalOfNoCross_left_cross_lift_of_only_endpoint1_on_path_or_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 1 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (horiginal_alt :
      X.endpoints.endpoint 1 ∈ S.boundarySet ->
        CrossEndpointAlternating S.boundary X.endpoints.endpoint)
    (htail_alt :
      X.endpoints.endpoint 1 ∉ S.boundarySet ->
        CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.t)) :
    Nonempty S.Cross := by
  apply canonicalOfNoCross_left_cross_lift_of_only_endpoint_on_path_or_to_end
    P hno_cross X 1 hoff horiginal_alt
  · intro hb
    simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using htail_alt hb
  · intro hb halt
    exact canonicalOfNoCross_left_cross_lift_replaceEndpoint1_to_end_of_single_path
      P hno_cross X hpath hoff hb
      (by simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using halt)

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
