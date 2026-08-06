import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.SingleOffPathOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_endpoint1_first_leg2_meets_rim0_only_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y z : V}
    (r : S.graph.Walk x y)
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside)
    (hz_leg :
      z ∈
        (((X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil y
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse).support)
    (hz_rim :
      z ∈
        ((((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).reverse).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 0 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).1))).support) :
    z = y := by
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
  have hy_ne_3 : y ≠ X.endpoints.endpoint 3 := by
    intro hy3
    exact (hr_outside y r.end_mem_support).2 (by simpa [hy3] using h3P)
  have hz_leg_take : z ∈ (G.takeUntil y hyG).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_leg
    exact List.mem_reverse.mp hz_leg
  have hzG : z ∈ G.support :=
    SimpleGraph.Walk.support_takeUntil_subset G hyG hz_leg_take
  have hzSecond : z ∈ X.secondPath.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_rim
  rcases hz_rim with hz_prefix_rev | hz_segment
  · have hz_prefix : z ∈ (F.takeUntil x hxF).support := by
      rw [SimpleGraph.Walk.support_reverse] at hz_prefix_rev
      exact List.mem_reverse.mp hz_prefix_rev
    have hzF : z ∈ F.support :=
      SimpleGraph.Walk.support_takeUntil_subset F hxF hz_prefix
    have hzFirst : z ∈ X.firstPath.support := by
      simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
    exact False.elim
      (Set.disjoint_left.mp X.paths_disjoint hzFirst hzSecond)
  · have hzPath : z ∈ P.pathSet := by
      simpa [GMIX24CutPath.pathSet] using
        Walk.segmentBetween_support_subset
          (p := P.path)
          (by simpa [GMIX24CutPath.pathSet] using h0P)
          (by simpa [GMIX24CutPath.pathSet] using h3P)
          (Nat.le_of_lt horder.1) hz_segment
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hzSecond hzPath with hz1 | hz3
    · exact False.elim (h1_off (by simpa [hz1] using hzPath))
    · have h3_not_leg : X.endpoints.endpoint 3 ∉ (G.takeUntil y hyG).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
            X.secondPath_isPath)
          hyG hy_ne_3.symm
      exact False.elim (h3_not_leg (by simpa [hz3] using hz_leg_take))

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg2_meets_rim1_only_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y z : V}
    (r : S.graph.Walk x y)
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside)
    (hz_leg :
      z ∈
        (((X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil y
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse).support)
    (hz_rim :
      z ∈
        (((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 2 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).2)).reverse).support) :
    z = y := by
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
  have hy_ne_3 : y ≠ X.endpoints.endpoint 3 := by
    intro hy3
    exact (hr_outside y r.end_mem_support).2 (by simpa [hy3] using h3P)
  have hz_leg_take : z ∈ (G.takeUntil y hyG).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_leg
    exact List.mem_reverse.mp hz_leg
  have hzG : z ∈ G.support :=
    SimpleGraph.Walk.support_takeUntil_subset G hyG hz_leg_take
  have hzSecond : z ∈ X.secondPath.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_rim
  rcases hz_rim with hz_suffix | hz_segment_rev
  · have hzF : z ∈ F.support :=
      SimpleGraph.Walk.support_dropUntil_subset F hxF hz_suffix
    have hzFirst : z ∈ X.firstPath.support := by
      simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
    exact False.elim
      (Set.disjoint_left.mp X.paths_disjoint hzFirst hzSecond)
  · have hzPath : z ∈ P.pathSet := by
      simpa [GMIX24CutPath.pathSet] using
        Walk.segmentBetween_reverse_support_subset
          (p := P.path)
          (by simpa [GMIX24CutPath.pathSet] using h3P)
          (by simpa [GMIX24CutPath.pathSet] using h2P)
          (Nat.le_of_lt horder.2) hz_segment_rev
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hzSecond hzPath with hz1 | hz3
    · exact False.elim (h1_off (by simpa [hz1] using hzPath))
    · have h3_not_leg : X.endpoints.endpoint 3 ∉ (G.takeUntil y hyG).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
            X.secondPath_isPath)
          hyG hy_ne_3.symm
      exact False.elim (h3_not_leg (by simpa [hz3] using hz_leg_take))

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg2_meets_rim2_only_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {x y z : V}
    (r : S.graph.Walk x y)
    (hy_second : y ∈ X.secondPath.support)
    (hclean_second :
      forall w : V, w ∈ r.support ->
        w ∈ X.secondPath.support -> w = y)
    (hz_leg :
      z ∈
        (((X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil y
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse).support)
    (hz_rim :
      z ∈
        (r.append
          ((X.secondPath.mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil y
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second))).support) :
    z = y := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  have hz_leg_take : z ∈ (G.takeUntil y hyG).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_leg
    exact List.mem_reverse.mp hz_leg
  have hzG_from_leg : z ∈ G.support :=
    SimpleGraph.Walk.support_takeUntil_subset G hyG hz_leg_take
  have hzSecond : z ∈ X.secondPath.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG_from_leg
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_rim
  rcases hz_rim with hz_branch | hz_suffix
  · exact hclean_second z hz_branch hzSecond
  · exact
      Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
        (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
          X.secondPath_isPath)
        hyG hz_leg_take hz_suffix


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
