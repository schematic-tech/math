import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.SingleOffPathOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_endpoint1_first_rim0_isPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x : V}
    (hx_first : x ∈ X.firstPath.support)
    (hx_not_path : x ∉ P.pathSet) :
    ((((X.firstPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil x
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).reverse).append
        (Walk.segmentBetween P.path
          (by simpa [GMIX24CutPath.pathSet] using hothers_path 0 (by decide))
          (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
          (Nat.le_of_lt
            (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
              P hno_cross X h1_off hothers_path).1))).IsPath := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let F : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.leftSociety_graph_le
  have hxF : x ∈ F.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hx_first
  have h0P : X.endpoints.endpoint 0 ∈ P.pathSet :=
    hothers_path 0 (by decide)
  have h2P : X.endpoints.endpoint 2 ∈ P.pathSet :=
    hothers_path 2 (by decide)
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  have hx_ne_2 : x ≠ X.endpoints.endpoint 2 := by
    intro hx2
    exact hx_not_path (by simpa [hx2] using h2P)
  refine
    Walk.IsPath.append_of_support_inter_eq_endpoint
      ((SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
        X.firstPath_isPath).takeUntil hxF).reverse
      (Walk.segmentBetween_isPath P.path_isPath
        (by simpa [GMIX24CutPath.pathSet] using h0P)
        (by simpa [GMIX24CutPath.pathSet] using h3P)
        (Nat.le_of_lt horder.1))
      ?_
  intro z hzPrefixRev hzSegment
  have hzPrefix : z ∈ (F.takeUntil x hxF).support := by
    rw [SimpleGraph.Walk.support_reverse] at hzPrefixRev
    exact List.mem_reverse.mp hzPrefixRev
  have hzF : z ∈ F.support :=
    SimpleGraph.Walk.support_takeUntil_subset F hxF hzPrefix
  have hzFirst : z ∈ X.firstPath.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
  have hzPath : z ∈ P.pathSet := by
    simpa [GMIX24CutPath.pathSet] using
      Walk.segmentBetween_support_subset
        (p := P.path)
        (by simpa [GMIX24CutPath.pathSet] using h0P)
        (by simpa [GMIX24CutPath.pathSet] using h3P)
        (Nat.le_of_lt horder.1) hzSegment
  have hzBoundary :
      z ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
    rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
    exact Or.inr hzPath
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := X.firstPath) hzFirst with hzInternal | hzEnd
  · have hbad :
        z ∈ Walk.InternalVertices X.firstPath ∩
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
      ⟨hzInternal, hzBoundary⟩
    have hnot :
        z ∉ Walk.InternalVertices X.firstPath ∩
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
      rw [X.first_internal_boundary]
      simp
    exact False.elim (hnot hbad)
  · rcases hzEnd with hz0 | hz2
    · exact hz0
    · have h2_not_prefix : X.endpoints.endpoint 2 ∉ (F.takeUntil x hxF).support := by
          exact
            SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
                X.firstPath_isPath)
              hxF hx_ne_2.symm
      exact False.elim (h2_not_prefix (by simpa [hz2] using hzPrefix))

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim1_isPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x : V}
    (hx_first : x ∈ X.firstPath.support)
    (hx_not_path : x ∉ P.pathSet) :
    (((X.firstPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil x
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).append
        (Walk.segmentBetween P.path
          (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
          (by simpa [GMIX24CutPath.pathSet] using hothers_path 2 (by decide))
          (Nat.le_of_lt
            (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
              P hno_cross X h1_off hothers_path).2)).reverse).IsPath := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let F : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.leftSociety_graph_le
  have hxF : x ∈ F.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hx_first
  have h0P : X.endpoints.endpoint 0 ∈ P.pathSet :=
    hothers_path 0 (by decide)
  have h2P : X.endpoints.endpoint 2 ∈ P.pathSet :=
    hothers_path 2 (by decide)
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  have hx_ne_0 : x ≠ X.endpoints.endpoint 0 := by
    intro hx0
    exact hx_not_path (by simpa [hx0] using h0P)
  refine
    Walk.IsPath.append_of_support_inter_eq_endpoint
      ((SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
        X.firstPath_isPath).dropUntil hxF)
      ((Walk.segmentBetween_isPath P.path_isPath
        (by simpa [GMIX24CutPath.pathSet] using h3P)
        (by simpa [GMIX24CutPath.pathSet] using h2P)
        (Nat.le_of_lt horder.2)).reverse)
      ?_
  intro z hzSuffix hzSegmentRev
  have hzF : z ∈ F.support :=
    SimpleGraph.Walk.support_dropUntil_subset F hxF hzSuffix
  have hzFirst : z ∈ X.firstPath.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
  have hzPath : z ∈ P.pathSet := by
    simpa [GMIX24CutPath.pathSet] using
      Walk.segmentBetween_reverse_support_subset
        (p := P.path)
        (by simpa [GMIX24CutPath.pathSet] using h3P)
        (by simpa [GMIX24CutPath.pathSet] using h2P)
        (Nat.le_of_lt horder.2) hzSegmentRev
  have hzBoundary :
      z ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
    rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
    exact Or.inr hzPath
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := X.firstPath) hzFirst with hzInternal | hzEnd
  · have hbad :
        z ∈ Walk.InternalVertices X.firstPath ∩
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet :=
      ⟨hzInternal, hzBoundary⟩
    have hnot :
        z ∉ Walk.InternalVertices X.firstPath ∩
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
      rw [X.first_internal_boundary]
      simp
    exact False.elim (hnot hbad)
  · rcases hzEnd with hz0 | hz2
    · have h0_not_suffix : X.endpoints.endpoint 0 ∉ (F.dropUntil x hxF).support := by
        exact
          Walk.IsPath.start_not_mem_dropUntil_support_of_ne
            (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
              X.firstPath_isPath)
            hxF hx_ne_0
      exact False.elim (h0_not_suffix (by simpa [hz0] using hzSuffix))
    · exact hz2

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim2_isPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x y : V}
    (r : S.graph.Walk x y)
    (hy_second : y ∈ X.secondPath.support)
    (hr_path : r.IsPath)
    (hclean_second :
      forall w : V, w ∈ r.support ->
        w ∈ X.secondPath.support -> w = y) :
    (r.append
      ((X.secondPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil y
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second))).IsPath := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  refine
    Walk.IsPath.append_of_support_inter_eq_endpoint
      hr_path
      ((SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
        X.secondPath_isPath).dropUntil hyG)
      ?_
  intro z hzr hzGdrop
  have hzG : z ∈ G.support :=
    SimpleGraph.Walk.support_dropUntil_subset G hyG hzGdrop
  have hzSecond : z ∈ X.secondPath.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
  exact hclean_second z hzr hzSecond


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
