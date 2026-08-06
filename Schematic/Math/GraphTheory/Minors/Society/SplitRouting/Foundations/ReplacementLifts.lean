import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.TailTransport
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.Maximality

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 2 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint2_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint2_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 0 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint0_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 3 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint3_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint3_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 1 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint1_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 2 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint2_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint2_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 0 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint0_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint0_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 3 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint3_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint3_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (ha_ne : forall i : Fin 4, i ≠ 1 -> a ≠ X.endpoints.endpoint i)
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
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail
    P hno_cross X hx q
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoint1_mem_original
      P hno_cross X ha hoff)
    (X.replaceEndpoint1_injective ha_ne) halternating hq_path hq_boundary
    hx_not_boundary hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint2_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 0) (hx_ne 2))
    hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint0_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 0) (hx_ne 2))
    hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint3_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 1) (hx_ne 3))
    hq_clean

theorem canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_replaceEndpoint1_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 1) (hx_ne 3))
    hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_firstPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 0) (hx_ne 2))
    hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_firstPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 0) (hx_ne 2))
    hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_secondPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 1) (hx_ne 3))
    hq_clean

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail_of_internal_contact
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet)
    (hx_ne : forall i : Fin 4, x ≠ X.endpoints.endpoint i)
    (halternating :
      CrossEndpointAlternating S.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail_of_single_path_endpoint
    P hno_cross X hx q ha hoff
    (fun i _hi => X.clean_tail_endpoint_ne_all_of_hit q hq_clean hx_ne i)
    halternating hq_path hq_boundary
    (GMIX24Split.canonicalOfNoCross_right_cross_secondPath_nonendpoint_not_boundary
      P hno_cross X hx (hx_ne 1) (hx_ne 3))
    hq_clean

theorem canonicalOfNoCross_left_cross_sameSide_tail_elim
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (endpoint : Fin 4 -> V)
    (k : Fin 4)
    (hendpoint_at : endpoint k = a)
    (hendpoint_other :
      forall i : Fin 4, i ≠ k -> endpoint i = X.endpoints.endpoint i)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (R : Prop)
    (hreject :
      forall qD :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk x a,
        (forall i : Fin 4,
          endpoint i ∈
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet) ->
        qD.IsPath ->
        Walk.InternalVertices qD ∩
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet =
          ∅ ->
        (forall w : V,
          w ∈ qD.support ->
            (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
              w = x) ->
        R) :
    R := by
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let hp : forall e : Sym2 V, e ∈ q.edges -> e ∈ P.leftGraph.edgeSet :=
    P.leftSide_walk_edges_subset_leftGraph hno_cross q hq_side
  let qLeft : P.leftGraph.Walk x a := q.transfer P.leftGraph hp
  let qD : D.leftSociety.graph.Walk x a := by
    simpa [D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using qLeft
  apply hreject qD
  · intro i
    by_cases hi : i = k
    · subst i
      rw [hendpoint_at]
      change a ∈ D.leftSociety.boundarySet
      change a ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet]
      exact Or.inl ha
    · rw [hendpoint_other i hi]
      simpa [GeneralSociety.boundarySet] using X.endpoints.endpoint_mem i
  · have hqLeft_path : qLeft.IsPath :=
      SimpleGraph.Walk.IsPath.transfer hp hq_path
    simpa [qD, qLeft, D, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using hqLeft_path
  · have hqLeft_boundary :
        Walk.InternalVertices qLeft ∩ P.leftCutBoundarySet = ∅ :=
      P.leftSide_walk_transfer_internal_leftCutBoundary_empty
        hno_cross q hq_side hq_outside hq_boundary
    simpa [qD, qLeft, D,
      GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet] using
      hqLeft_boundary
  · intro w hw hwX
    have hwLeft : w ∈ qLeft.support := by
      simpa [qD, qLeft, D, GMIX24Split.canonicalOfNoCross,
        GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
        GMIX24Split.ofCanonical] using hw
    have hwq : w ∈ q.support := by
      simpa [qLeft, SimpleGraph.Walk.support_transfer] using hwLeft
    exact hq_clean w hwq hwX


theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint2 a) 2
    (by simp [Cross.replaceEndpoint2])
    (by
      intro i hi
      simp [Cross.replaceEndpoint2, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
    (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact ⟨X.replaceEndpoint2_with_tail hx qD hendpoint_mem
    hendpoint_injective halternating hqD_path hqD_boundary hx_not_boundary
    hqD_clean⟩
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint0 a) 0
    (by simp [Cross.replaceEndpoint0])
    (by
      intro i hi
      simp [Cross.replaceEndpoint0, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
    (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact ⟨X.replaceEndpoint0_with_tail hx qD hendpoint_mem
    hendpoint_injective halternating hqD_path hqD_boundary hx_not_boundary
    hqD_clean⟩
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint3 a) 3
    (by simp [Cross.replaceEndpoint3])
    (by
      intro i hi
      simp [Cross.replaceEndpoint3, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
    (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact ⟨X.replaceEndpoint3_with_tail hx qD hendpoint_mem
    hendpoint_injective halternating hqD_path hqD_boundary hx_not_boundary
    hqD_clean⟩
theorem canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross := by
  apply canonicalOfNoCross_left_cross_sameSide_tail_elim
    P hno_cross X q ha (X.replaceEndpoint1 a) 1
    (by simp [Cross.replaceEndpoint1])
    (by
      intro i hi
      simp [Cross.replaceEndpoint1, hi])
    hq_path hq_side hq_outside hq_boundary hq_clean
    (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
  intro qD hendpoint_mem hqD_path hqD_boundary hqD_clean
  exact ⟨X.replaceEndpoint1_with_tail hx qD hendpoint_mem
    hendpoint_injective halternating hqD_path hqD_boundary hx_not_boundary
    hqD_clean⟩
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint2_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint2_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint0_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint0_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint3_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint3_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
theorem canonicalOfNoCross_right_cross_sameSide_replaceEndpoint1_with_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
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
            w = x) :
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross := by
  classical
  let Xrev := GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_sameSide_replaceEndpoint1_with_tail
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx)
      q (by simpa using ha)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hendpoint_injective)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using halternating)
      hq_path (by simpa using hq_side) (by simpa using hq_outside)
      hq_boundary
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hx_not_boundary)
      (by
        intro w hw hwX
        exact hq_clean w hw (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hwX)))
end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
