import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.SingleOffPathOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_endpoint1_first_rim0_rim1_internals_disjoint
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
    Disjoint
      (Walk.InternalVertices
        ((((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).reverse).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 0 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).1))))
      (Walk.InternalVertices
        (((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 2 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).2)).reverse)) := by
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
  have hx_ne_2 : x ≠ X.endpoints.endpoint 2 := by
    intro hx2
    exact hx_not_path (by simpa [hx2] using h2P)
  rw [Set.disjoint_left]
  intro z hz0 hz1
  have hz0_support := hz0.1
  have hz1_support := hz1.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz0_support
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz1_support
  rcases hz0_support with hz0_prefix_rev | hz0_segment
  · have hz0_prefix : z ∈ (F.takeUntil x hxF).support := by
      rw [SimpleGraph.Walk.support_reverse] at hz0_prefix_rev
      exact List.mem_reverse.mp hz0_prefix_rev
    rcases hz1_support with hz1_suffix | hz1_segment_rev
    · have hzx :
          z = x :=
        Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
            X.firstPath_isPath)
          hxF hz0_prefix hz1_suffix
      exact hz0.2.1 hzx
    · have hzF : z ∈ F.support :=
        SimpleGraph.Walk.support_takeUntil_subset F hxF hz0_prefix
      have hzFirst : z ∈ X.firstPath.support := by
        simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
      have hzPath : z ∈ P.pathSet := by
        simpa [GMIX24CutPath.pathSet] using
          Walk.segmentBetween_reverse_support_subset
            (p := P.path)
            (by simpa [GMIX24CutPath.pathSet] using h3P)
            (by simpa [GMIX24CutPath.pathSet] using h2P)
            (Nat.le_of_lt horder.2) hz1_segment_rev
      rcases
          GMIX24Split.canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
            P hno_cross X hzFirst hzPath with hz_eq0 | hz_eq2
      · exact False.elim
          ((P.not_mem_segmentBetween_reverse_of_supportIndex_lt_left
            h3P h2P (Nat.le_of_lt horder.2) horder.1)
            (by simpa [hz_eq0] using hz1_segment_rev))
      · have h2_not_prefix : X.endpoints.endpoint 2 ∉ (F.takeUntil x hxF).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
              X.firstPath_isPath)
            hxF hx_ne_2.symm
        exact False.elim (h2_not_prefix (by simpa [hz_eq2] using hz0_prefix))
  · rcases hz1_support with hz1_suffix | hz1_segment_rev
    · have hzF : z ∈ F.support :=
        SimpleGraph.Walk.support_dropUntil_subset F hxF hz1_suffix
      have hzFirst : z ∈ X.firstPath.support := by
        simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
      have hzPath : z ∈ P.pathSet := by
        simpa [GMIX24CutPath.pathSet] using
          Walk.segmentBetween_support_subset
            (p := P.path)
            (by simpa [GMIX24CutPath.pathSet] using h0P)
            (by simpa [GMIX24CutPath.pathSet] using h3P)
            (Nat.le_of_lt horder.1) hz0_segment
      rcases
          GMIX24Split.canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
            P hno_cross X hzFirst hzPath with hz_eq0 | hz_eq2
      · have h0_not_suffix : X.endpoints.endpoint 0 ∉ (F.dropUntil x hxF).support :=
          Walk.IsPath.start_not_mem_dropUntil_support_of_ne
            (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
              X.firstPath_isPath)
            hxF hx_ne_0
        exact False.elim (h0_not_suffix (by simpa [hz_eq0] using hz1_suffix))
      · exact False.elim
          ((P.not_mem_segmentBetween_of_right_lt_supportIndex
            h0P h3P (Nat.le_of_lt horder.1) horder.2)
            (by simpa [hz_eq2] using hz0_segment))
    · have hz1_segment : z ∈
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using h3P)
            (by simpa [GMIX24CutPath.pathSet] using h2P)
            (Nat.le_of_lt horder.2)).support := by
        rw [SimpleGraph.Walk.support_reverse] at hz1_segment_rev
        exact List.mem_reverse.mp hz1_segment_rev
      have hz3 :
          z = X.endpoints.endpoint 3 :=
        Walk.segmentBetween_support_inter_subset_common P.path_isPath
          (by simpa [GMIX24CutPath.pathSet] using h0P)
          (by simpa [GMIX24CutPath.pathSet] using h3P)
          (by simpa [GMIX24CutPath.pathSet] using h2P)
          (Nat.le_of_lt horder.1) (Nat.le_of_lt horder.2)
          hz0_segment hz1_segment
      exact hz0.2.2 hz3

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim0_rim2_internals_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V}
    (r : S.graph.Walk x y)
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support)
    (hclean_first :
      forall w : V, w ∈ r.support ->
        w ∈ X.firstPath.support -> w = x)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    Disjoint
      (Walk.InternalVertices
        ((((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).reverse).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 0 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).1))))
      (Walk.InternalVertices
        (r.append
          ((X.secondPath.mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil y
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)))) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let F : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.leftSociety_graph_le
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hxF : x ∈ F.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hx_first
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  have h0P : X.endpoints.endpoint 0 ∈ P.pathSet :=
    hothers_path 0 (by decide)
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  rw [Set.disjoint_left]
  intro z hz0 hz2
  have hz0_support := hz0.1
  have hz2_support := hz2.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz0_support
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz2_support
  rcases hz0_support with hz0_prefix_rev | hz0_segment
  · have hz0_prefix : z ∈ (F.takeUntil x hxF).support := by
      rw [SimpleGraph.Walk.support_reverse] at hz0_prefix_rev
      exact List.mem_reverse.mp hz0_prefix_rev
    have hzF : z ∈ F.support :=
      SimpleGraph.Walk.support_takeUntil_subset F hxF hz0_prefix
    have hzFirst : z ∈ X.firstPath.support := by
      simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
    rcases hz2_support with hz_branch | hz_suffix
    · have hzx : z = x := hclean_first z hz_branch hzFirst
      exact hz0.2.1 hzx
    · have hzG : z ∈ G.support :=
        SimpleGraph.Walk.support_dropUntil_subset G hyG hz_suffix
      have hzSecond : z ∈ X.secondPath.support := by
        simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
      exact False.elim
        (Set.disjoint_left.mp X.paths_disjoint hzFirst hzSecond)
  · have hzPath : z ∈ P.pathSet := by
      simpa [GMIX24CutPath.pathSet] using
        Walk.segmentBetween_support_subset
          (p := P.path)
          (by simpa [GMIX24CutPath.pathSet] using h0P)
          (by simpa [GMIX24CutPath.pathSet] using h3P)
          (Nat.le_of_lt horder.1) hz0_segment
    rcases hz2_support with hz_branch | hz_suffix
    · exact False.elim ((hr_outside z hz_branch).2 (by
        simpa [GMIX24CutPath.pathSet] using hzPath))
    · have hzG : z ∈ G.support :=
        SimpleGraph.Walk.support_dropUntil_subset G hyG hz_suffix
      have hzSecond : z ∈ X.secondPath.support := by
        simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
      rcases
          GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
            P hno_cross X hzSecond hzPath with hz1 | hz3
      · exact False.elim (h1_off (by simpa [hz1] using hzPath))
      · exact hz0.2.2 hz3

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim1_rim2_internals_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V}
    (r : S.graph.Walk x y)
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support)
    (hclean_first :
      forall w : V, w ∈ r.support ->
        w ∈ X.firstPath.support -> w = x)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    Disjoint
      (Walk.InternalVertices
        (((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 2 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).2)).reverse))
      (Walk.InternalVertices
        (r.append
          ((X.secondPath.mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil y
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)))) := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let F : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.leftSociety_graph_le
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hxF : x ∈ F.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hx_first
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  have h2P : X.endpoints.endpoint 2 ∈ P.pathSet :=
    hothers_path 2 (by decide)
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have hz1_support := hz1.1
  have hz2_support := hz2.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz1_support
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz2_support
  rcases hz1_support with hz1_suffix | hz1_segment_rev
  · have hzF : z ∈ F.support :=
      SimpleGraph.Walk.support_dropUntil_subset F hxF hz1_suffix
    have hzFirst : z ∈ X.firstPath.support := by
      simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
    rcases hz2_support with hz_branch | hz_suffix
    · have hzx : z = x := hclean_first z hz_branch hzFirst
      exact hz1.2.1 hzx
    · have hzG : z ∈ G.support :=
        SimpleGraph.Walk.support_dropUntil_subset G hyG hz_suffix
      have hzSecond : z ∈ X.secondPath.support := by
        simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
      exact False.elim
        (Set.disjoint_left.mp X.paths_disjoint hzFirst hzSecond)
  · have hzPath : z ∈ P.pathSet := by
      simpa [GMIX24CutPath.pathSet] using
        Walk.segmentBetween_reverse_support_subset
          (p := P.path)
          (by simpa [GMIX24CutPath.pathSet] using h3P)
          (by simpa [GMIX24CutPath.pathSet] using h2P)
          (Nat.le_of_lt horder.2) hz1_segment_rev
    rcases hz2_support with hz_branch | hz_suffix
    · exact False.elim ((hr_outside z hz_branch).2 (by
        simpa [GMIX24CutPath.pathSet] using hzPath))
    · have hzG : z ∈ G.support :=
        SimpleGraph.Walk.support_dropUntil_subset G hyG hz_suffix
      have hzSecond : z ∈ X.secondPath.support := by
        simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
      rcases
          GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
            P hno_cross X hzSecond hzPath with hz1_endpoint | hz3
      · exact False.elim (h1_off (by simpa [hz1_endpoint] using hzPath))
      · exact hz1.2.2 hz3


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
