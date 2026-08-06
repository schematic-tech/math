import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.CrossTransport

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

private theorem walk_mapLe_internal_boundary_original
    [DecidableEq V] {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    {side sideArc otherSide otherArc : Set V}
    (hgraph : H.graph ≤ S.graph)
    (hboundary : H.boundarySet = sideArc ∪ P.pathSet)
    (hsides : Disjoint side otherSide)
    (hotherArc_side : otherArc ⊆ otherSide)
    (hotherArc_outside : otherArc ⊆ P.outside)
    (harcs :
      forall {z : V},
        z ∈ S.boundarySet ->
          z ≠ P.s -> z ≠ P.t -> z ∈ sideArc ∨ z ∈ otherArc)
    {u v : V} (p : H.graph.Walk u v)
    (hsupport : {z : V | z ∈ p.support} ⊆ side ∪ P.pathSet)
    (hinternal : Walk.InternalVertices p ∩ H.boundarySet = ∅) :
    Walk.InternalVertices (p.mapLe hgraph) ∩ S.boundarySet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzInternal : z ∈ Walk.InternalVertices p := by
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using hz.1
  have hzSideOrPath : z ∈ side ∪ P.pathSet :=
    hsupport hzInternal.1
  have hnot : z ∉ Walk.InternalVertices p ∩ H.boundarySet := by
    rw [hinternal]
    simp
  by_cases hzs : z = P.s
  · have hzSideBoundary : z ∈ H.boundarySet := by
      rw [hboundary]
      exact Or.inr (by simp [GMIX24CutPath.pathSet, hzs])
    exact hnot ⟨hzInternal, hzSideBoundary⟩
  · by_cases hzt : z = P.t
    · have hzSideBoundary : z ∈ H.boundarySet := by
        rw [hboundary]
        exact Or.inr (by simp [GMIX24CutPath.pathSet, hzt])
      exact hnot ⟨hzInternal, hzSideBoundary⟩
    · rcases harcs hz.2 hzs hzt with hzSideArc | hzOtherArc
      · have hzSideBoundary : z ∈ H.boundarySet := by
          rw [hboundary]
          exact Or.inl hzSideArc
        exact hnot ⟨hzInternal, hzSideBoundary⟩
      · rcases hzSideOrPath with hzSide | hzPath
        · exact Set.disjoint_left.mp hsides hzSide
            (hotherArc_side hzOtherArc)
        · exact (hotherArc_outside hzOtherArc).2
            (by simpa [GMIX24CutPath.pathSet] using hzPath)

theorem canonicalOfNoCross_left_walk_mapLe_internal_boundary_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (p : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Walk u v)
    (hsupport : {z : V | z ∈ p.support} ⊆ P.leftSide ∪ P.pathSet)
    (hinternal :
      Walk.InternalVertices p ∩
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet =
        ∅) :
    Walk.InternalVertices
        (p.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le) ∩
      S.boundarySet = ∅ := by
  apply walk_mapLe_internal_boundary_original P
    (side := P.leftSide) (sideArc := P.leftBoundaryArc)
    (otherSide := P.rightSide) (otherArc := P.rightBoundaryArc)
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (by simp [GMIX24CutPath.leftCutBoundarySet])
    (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
    P.rightBoundaryArc_subset_rightSide P.rightBoundaryArc_subset_outside
    ?_ p hsupport hinternal
  intro z hz hzs hzt
  have hzArc : z ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
    rw [P.leftBoundaryArc_union_right]
    exact ⟨hz, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] using And.intro hzs hzt⟩
  exact hzArc

theorem canonicalOfNoCross_right_walk_mapLe_internal_boundary_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (p : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.Walk u v)
    (hsupport : {z : V | z ∈ p.support} ⊆ P.rightSide ∪ P.pathSet)
    (hinternal :
      Walk.InternalVertices p ∩
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet =
        ∅) :
    Walk.InternalVertices
        (p.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le) ∩
      S.boundarySet = ∅ := by
  apply walk_mapLe_internal_boundary_original P
    (side := P.rightSide) (sideArc := P.rightBoundaryArc)
    (otherSide := P.leftSide) (otherArc := P.leftBoundaryArc)
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le
    (by simp [GMIX24CutPath.rightCutBoundarySet])
    (P.leftSide_disjoint_rightSide_of_no_cross hno_cross).symm
    P.leftBoundaryArc_subset_leftSide P.leftBoundaryArc_subset_outside
    ?_ p hsupport hinternal
  intro z hz hzs hzt
  have hzArc : z ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
    rw [P.leftBoundaryArc_union_right]
    exact ⟨hz, by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] using And.intro hzs hzt⟩
  simpa [or_comm] using hzArc

theorem canonicalOfNoCross_left_cross_first_internal_boundary_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Walk.InternalVertices
        (X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le) ∩
      S.boundarySet = ∅ :=
  GMIX24Split.canonicalOfNoCross_left_walk_mapLe_internal_boundary_original
    P hno_cross X.firstPath
    (GMIX24Split.canonicalOfNoCross_left_cross_firstPath_support_subset_side_or_path
      P hno_cross X)
    X.first_internal_boundary

theorem canonicalOfNoCross_left_cross_second_internal_boundary_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Walk.InternalVertices
        (X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le) ∩
      S.boundarySet = ∅ :=
  GMIX24Split.canonicalOfNoCross_left_walk_mapLe_internal_boundary_original
    P hno_cross X.secondPath
    (GMIX24Split.canonicalOfNoCross_left_cross_secondPath_support_subset_side_or_path
      P hno_cross X)
    X.second_internal_boundary

theorem canonicalOfNoCross_right_cross_first_internal_boundary_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    Walk.InternalVertices
        (X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le) ∩
      S.boundarySet = ∅ :=
  GMIX24Split.canonicalOfNoCross_right_walk_mapLe_internal_boundary_original
    P hno_cross X.firstPath
    (GMIX24Split.canonicalOfNoCross_right_cross_firstPath_support_subset_side_or_path
      P hno_cross X)
    X.first_internal_boundary

theorem canonicalOfNoCross_right_cross_second_internal_boundary_original
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    Walk.InternalVertices
        (X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le) ∩
      S.boundarySet = ∅ :=
  GMIX24Split.canonicalOfNoCross_right_walk_mapLe_internal_boundary_original
    P hno_cross X.secondPath
    (GMIX24Split.canonicalOfNoCross_right_cross_secondPath_support_subset_side_or_path
      P hno_cross X)
    X.second_internal_boundary


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
