import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.MixedEdgeElimination

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
@[simp]
theorem canonicalOfNoCross_leftSociety_boundarySet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet =
      P.leftCutBoundarySet := by
  simp [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical, GeneralSociety.boundarySet]

@[simp]
theorem canonicalOfNoCross_rightSociety_boundarySet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet =
      P.rightCutBoundarySet := by
  simp [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical, GeneralSociety.boundarySet]

theorem walk_support_subset_of_graph_support_subset
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (h_nontrivial : p.length ≠ 0) {U : Set V}
    (h_support : G.support ⊆ U) :
    {z : V | z ∈ p.support} ⊆ U := by
  intro z hz
  apply h_support
  apply SimpleGraph.mem_support_of_mem_walk_support p
  · intro hnil
    exact h_nontrivial (SimpleGraph.Walk.nil_iff_length_eq.mp hnil)
  · exact hz

theorem walk_support_eq_endpoint_of_internalVertices_inter_set_eq_empty
    {G : SimpleGraph V} {a b z : V} (p : G.Walk a b) {U : Set V}
    (h_clean : Walk.InternalVertices p ∩ U = ∅)
    (hz_support : z ∈ p.support) (hzU : z ∈ U) :
    z = a ∨ z = b := by
  rcases Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
      (p := p) hz_support with hz_internal | hz_endpoint
  · have : z ∉ Walk.InternalVertices p ∩ U := by
      rw [h_clean]
      simp
    exact False.elim (this ⟨hz_internal, hzU⟩)
  · exact hz_endpoint

theorem canonicalOfNoCross_left_cross_endpoint_arc_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (i : Fin 4) :
    X.endpoints.endpoint i ∈ P.leftBoundaryArc ∨
      X.endpoints.endpoint i ∈ P.pathSet := by
  have hmem :
      X.endpoints.endpoint i ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
    X.endpoints.endpoint_mem i
  simpa [GMIX24CutPath.leftCutBoundarySet] using hmem

theorem canonicalOfNoCross_right_cross_endpoint_arc_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (i : Fin 4) :
    X.endpoints.endpoint i ∈ P.rightBoundaryArc ∨
      X.endpoints.endpoint i ∈ P.pathSet := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint_arc_or_path
      P.reverse hno_cross Xrev i

theorem canonicalOfNoCross_left_tripod_boundary_arc_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3) :
    T.boundary i ∈ P.leftBoundaryArc ∨
      T.boundary i ∈ P.pathSet := by
  have hmem :
      T.boundary i ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
    T.boundary_mem i
  simpa [GMIX24CutPath.leftCutBoundarySet] using hmem

theorem canonicalOfNoCross_right_tripod_boundary_arc_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    T.boundary i ∈ P.rightBoundaryArc ∨
      T.boundary i ∈ P.pathSet := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    GMIX24Split.canonicalOfNoCross_left_tripod_boundary_arc_or_path
      P.reverse hno_cross Trev i

theorem canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (i : Fin 4) :
    X.endpoints.endpoint i ∉ P.pathSet ↔
      X.endpoints.endpoint i ∈ P.leftBoundaryArc := by
  constructor
  · intro hnotPath
    rcases
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint_arc_or_path
        P hno_cross X i with hArc | hPath
    · exact hArc
    · exact False.elim (hnotPath hPath)
  · intro hArc hPath
    exact (P.leftBoundaryArc_subset_outside hArc).2
      (by simpa [GMIX24CutPath.pathSet] using hPath)

theorem canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (i : Fin 4) :
    X.endpoints.endpoint i ∉ P.pathSet ↔
      X.endpoints.endpoint i ∈ P.rightBoundaryArc := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P.reverse hno_cross Xrev i

theorem canonicalOfNoCross_left_cross_side_alternating
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    CrossEndpointAlternating P.leftOrderedCutBoundary X.endpoints.endpoint := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating

theorem canonicalOfNoCross_right_cross_side_alternating
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    CrossEndpointAlternating P.rightOrderedCutBoundary X.endpoints.endpoint := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    GMIX24Split.canonicalOfNoCross_left_cross_side_alternating
      P.reverse hno_cross Xrev

theorem canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3) :
    T.boundary i ∉ P.pathSet ↔ T.boundary i ∈ P.leftBoundaryArc := by
  constructor
  · intro hnotPath
    rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_boundary_arc_or_path
        P hno_cross T i with hArc | hPath
    · exact hArc
    · exact False.elim (hnotPath hPath)
  · intro hArc hPath
    exact (P.leftBoundaryArc_subset_outside hArc).2
      (by simpa [GMIX24CutPath.pathSet] using hPath)

theorem canonicalOfNoCross_right_tripod_boundary_not_path_iff_arc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    T.boundary i ∉ P.pathSet ↔ T.boundary i ∈ P.rightBoundaryArc := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P.reverse hno_cross Trev i

theorem canonicalOfNoCross_left_cross_firstPath_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    {z : V | z ∈ X.firstPath.support} ⊆
      P.leftSide ∪ P.pathSet := by
  exact walk_support_subset_of_graph_support_subset
    X.firstPath X.firstPath_nontrivial
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices

theorem canonicalOfNoCross_left_cross_secondPath_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    {z : V | z ∈ X.secondPath.support} ⊆
      P.leftSide ∪ P.pathSet := by
  exact walk_support_subset_of_graph_support_subset
    X.secondPath X.secondPath_nontrivial
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices

theorem canonicalOfNoCross_right_cross_firstPath_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    {z : V | z ∈ X.firstPath.support} ⊆
      P.rightSide ∪ P.pathSet := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    GMIX24Split.canonicalOfNoCross_left_cross_firstPath_support_subset_side_or_path
      P.reverse hno_cross Xrev

theorem canonicalOfNoCross_right_cross_secondPath_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    {z : V | z ∈ X.secondPath.support} ⊆
      P.rightSide ∪ P.pathSet := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    GMIX24Split.canonicalOfNoCross_left_cross_secondPath_support_subset_side_or_path
      P.reverse hno_cross Xrev

theorem canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z : V}
    (hz : z ∈ X.firstPath.support)
    (hzP : z ∈ P.pathSet) :
    z = X.endpoints.endpoint 0 ∨ z = X.endpoints.endpoint 2 := by
  apply walk_support_eq_endpoint_of_internalVertices_inter_set_eq_empty
    X.firstPath X.first_internal_boundary hz
  rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
  exact Or.inr hzP

theorem canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {z : V}
    (hz : z ∈ X.secondPath.support)
    (hzP : z ∈ P.pathSet) :
    z = X.endpoints.endpoint 1 ∨ z = X.endpoints.endpoint 3 := by
  apply walk_support_eq_endpoint_of_internalVertices_inter_set_eq_empty
    X.secondPath X.second_internal_boundary hz
  rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
  exact Or.inr hzP

theorem canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z : V}
    (hz : z ∈ X.firstPath.support)
    (hzP : z ∈ P.pathSet) :
    z = X.endpoints.endpoint 0 ∨ z = X.endpoints.endpoint 2 := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
      P.reverse hno_cross Xrev (by simpa [Xrev] using hz) (by simpa using hzP))

theorem canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {z : V}
    (hz : z ∈ X.secondPath.support)
    (hzP : z ∈ P.pathSet) :
    z = X.endpoints.endpoint 1 ∨ z = X.endpoints.endpoint 3 := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
      P.reverse hno_cross Xrev (by simpa [Xrev] using hz) (by simpa using hzP))

theorem canonicalOfNoCross_left_cross_pathSet_support_clean_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {u v : V} (q : S.graph.Walk u v)
    {l : Fin 4}
    (hothers_off :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∉ P.pathSet)
    (hq_support : forall w : V, w ∈ q.support -> w ∈ P.pathSet) :
    forall w : V,
      w ∈ q.support ->
        (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
          w = X.endpoints.endpoint l := by
  intro w hw hwX
  have hwP : w ∈ P.pathSet := hq_support w hw
  rcases hwX with hwFirst | hwSecond
  · rcases
        GMIX24Split.canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hwFirst hwP with hw0 | hw2
    · by_cases h0l : (0 : Fin 4) = l
      · simpa [h0l] using hw0
      · exact False.elim (hothers_off 0 h0l (by simpa [← hw0] using hwP))
    · by_cases h2l : (2 : Fin 4) = l
      · simpa [h2l] using hw2
      · exact False.elim (hothers_off 2 h2l (by simpa [← hw2] using hwP))
  · rcases
        GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hwSecond hwP with hw1 | hw3
    · by_cases h1l : (1 : Fin 4) = l
      · simpa [h1l] using hw1
      · exact False.elim (hothers_off 1 h1l (by simpa [← hw1] using hwP))
    · by_cases h3l : (3 : Fin 4) = l
      · simpa [h3l] using hw3
      · exact False.elim (hothers_off 3 h3l (by simpa [← hw3] using hwP))

theorem canonicalOfNoCross_right_cross_pathSet_support_clean_of_single_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {u v : V} (q : S.graph.Walk u v)
    {l : Fin 4}
    (hothers_off :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∉ P.pathSet)
    (hq_support : forall w : V, w ∈ q.support -> w ∈ P.pathSet) :
    forall w : V,
      w ∈ q.support ->
        (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
          w = X.endpoints.endpoint l := by
  let Xrev := GMIX24Split.canonicalOfNoCross.rightCrossOnReverse P hno_cross X
  simpa [Xrev] using
    (GMIX24Split.canonicalOfNoCross_left_cross_pathSet_support_clean_of_single_path_endpoint
      P.reverse hno_cross Xrev q
      (by
        intro i hi
        simpa [Xrev] using hothers_off i hi)
      (by
        intro w hw
        simpa using hq_support w hw))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
