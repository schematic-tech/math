import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.TailTransport.EndpointAlternation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_firstPath_nonendpoint_not_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x : V}
    (hx : x ∈ X.firstPath.support)
    (hx0 : x ≠ X.endpoints.endpoint 0)
    (hx2 : x ≠ X.endpoints.endpoint 2) :
    x ∉ S.boundarySet := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  exact
    Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
      (p := X.firstPath.mapLe D.leftSociety_graph_le)
      (GMIX24Split.canonicalOfNoCross_left_cross_first_internal_boundary_original
        P hno_cross X)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx)
      hx0 hx2

theorem canonicalOfNoCross_left_cross_secondPath_nonendpoint_not_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x : V}
    (hx : x ∈ X.secondPath.support)
    (hx1 : x ≠ X.endpoints.endpoint 1)
    (hx3 : x ≠ X.endpoints.endpoint 3) :
    x ∉ S.boundarySet := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  exact
    Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
      (p := X.secondPath.mapLe D.leftSociety_graph_le)
      (GMIX24Split.canonicalOfNoCross_left_cross_second_internal_boundary_original
        P hno_cross X)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx)
      hx1 hx3

theorem canonicalOfNoCross_right_cross_firstPath_nonendpoint_not_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x : V}
    (hx : x ∈ X.firstPath.support)
    (hx0 : x ≠ X.endpoints.endpoint 0)
    (hx2 : x ≠ X.endpoints.endpoint 2) :
    x ∉ S.boundarySet := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  exact
    Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
      (p := X.firstPath.mapLe D.rightSociety_graph_le)
      (GMIX24Split.canonicalOfNoCross_right_cross_first_internal_boundary_original
        P hno_cross X)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx)
      hx0 hx2

theorem canonicalOfNoCross_right_cross_secondPath_nonendpoint_not_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x : V}
    (hx : x ∈ X.secondPath.support)
    (hx1 : x ≠ X.endpoints.endpoint 1)
    (hx3 : x ≠ X.endpoints.endpoint 3) :
    x ∉ S.boundarySet := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  exact
    Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
      (p := X.secondPath.mapLe D.rightSociety_graph_le)
      (GMIX24Split.canonicalOfNoCross_right_cross_second_internal_boundary_original
        P hno_cross X)
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx)
      hx1 hx3

theorem canonicalOfNoCross_left_cross_replaceEndpoint2_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint2 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 2 a
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint0_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint0 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 0 a
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint3_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint3 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 3 a
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_left_cross_replaceEndpoint1_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint1 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using
    (canonicalOfNoCross_left_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 1 a
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint2_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint2 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint2, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 2 a
      (by simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint0 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint0, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 0 a
      (by simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint3_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint3 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint3, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 3 a
      (by simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset ha)
      hoff)

theorem canonicalOfNoCross_right_cross_replaceEndpoint1_mem_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {a : V}
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    forall i : Fin 4, X.replaceEndpoint1 a i ∈ S.boundarySet := by
  simpa [Cross.replaceEndpoint1, replaceCrossEndpointAt] using
    (canonicalOfNoCross_right_cross_replaceEndpointAt_mem_original_of_single_path
      P hno_cross X 1 a
      (by simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset ha)
      hoff)



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
