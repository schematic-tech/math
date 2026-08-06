import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.TailTransport.CrossTailLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint2_to_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 2 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.t)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail
    P hno_cross X X.firstPath.end_mem_support (P.pathTailToEnd hpath)
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint2_mem_original_end_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint2_injective
      (fun i hi => endpoint_ne_end_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToEnd_isPath hpath)
    (P.pathTailToEnd_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToEnd hpath) hoff
      (P.pathTailToEnd_support_subset_pathSet hpath))

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint2_to_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 2 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.s)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail
    P hno_cross X X.firstPath.end_mem_support (P.pathTailToStart hpath)
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint2_mem_original_start_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint2_injective
      (fun i hi => endpoint_ne_start_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToStart_isPath hpath)
    (P.pathTailToStart_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToStart hpath) hoff
      (P.pathTailToStart_support_subset_pathSet hpath))

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint0_to_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 0 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 0 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.t)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail
    P hno_cross X X.firstPath.start_mem_support (P.pathTailToEnd hpath)
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_mem_original_end_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint0_injective
      (fun i hi => endpoint_ne_end_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToEnd_isPath hpath)
    (P.pathTailToEnd_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToEnd hpath) hoff
      (P.pathTailToEnd_support_subset_pathSet hpath))

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint0_to_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 0 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 0 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.s)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail
    P hno_cross X X.firstPath.start_mem_support (P.pathTailToStart hpath)
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint0_mem_original_start_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint0_injective
      (fun i hi => endpoint_ne_start_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToStart_isPath hpath)
    (P.pathTailToStart_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToStart hpath) hoff
      (P.pathTailToStart_support_subset_pathSet hpath))

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint3_to_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 3 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.t)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail
    P hno_cross X X.secondPath.end_mem_support (P.pathTailToEnd hpath)
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint3_mem_original_end_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint3_injective
      (fun i hi => endpoint_ne_end_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToEnd_isPath hpath)
    (P.pathTailToEnd_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToEnd hpath) hoff
      (P.pathTailToEnd_support_subset_pathSet hpath))

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint3_to_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 3 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.s)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail
    P hno_cross X X.secondPath.end_mem_support (P.pathTailToStart hpath)
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint3_mem_original_start_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint3_injective
      (fun i hi => endpoint_ne_start_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToStart_isPath hpath)
    (P.pathTailToStart_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToStart hpath) hoff
      (P.pathTailToStart_support_subset_pathSet hpath))

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint1_to_end_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 1 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 1 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.t)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail
    P hno_cross X X.secondPath.start_mem_support (P.pathTailToEnd hpath)
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_mem_original_end_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint1_injective
      (fun i hi => endpoint_ne_end_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToEnd_isPath hpath)
    (P.pathTailToEnd_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToEnd hpath) hoff
      (P.pathTailToEnd_support_subset_pathSet hpath))

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint1_to_start_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 1 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_not_boundary : X.endpoints.endpoint 1 ∉ S.boundarySet)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.s)) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail
    P hno_cross X X.secondPath.start_mem_support (P.pathTailToStart hpath)
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint1_mem_original_start_of_single_path
      P hno_cross X hoff)
    (X.replaceEndpoint1_injective
      (fun i hi => endpoint_ne_start_of_off_path (P := P) (hoff i hi)))
    halternating
    (P.pathTailToStart_isPath hpath)
    (P.pathTailToStart_internal_boundary_empty hpath)
    hx_not_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_pathSet_support_clean_of_single_path_endpoint
      P hno_cross X (P.pathTailToStart hpath) hoff
      (P.pathTailToStart_support_subset_pathSet hpath))

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

