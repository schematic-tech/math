import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.SingleOffPathOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_endpoint1_first_leg0_meets_rim0_only_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x z : V}
    (hx_first : x ∈ X.firstPath.support)
    (hz_leg :
      z ∈ (P.pathTailToStart (hothers_path 0 (by decide))).support)
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
    z = X.endpoints.endpoint 0 := by
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
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_rim
  rcases hz_rim with hz_prefix_rev | hz_segment
  · have hz_prefix : z ∈ (F.takeUntil x hxF).support := by
      rw [SimpleGraph.Walk.support_reverse] at hz_prefix_rev
      exact List.mem_reverse.mp hz_prefix_rev
    have hzF : z ∈ F.support :=
      SimpleGraph.Walk.support_takeUntil_subset F hxF hz_prefix
    have hzFirst : z ∈ X.firstPath.support := by
      simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet h0P z hz_leg
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hzFirst hzPath with hz0 | hz2
    · exact hz0
    · exact False.elim
        ((P.pathTailToStart_not_mem_of_supportIndex_lt h0P
          (lt_trans horder.1 horder.2)) (by simpa [hz2] using hz_leg))
  · exact
      P.pathTailToStart_support_inter_segmentBetween_subset_left
        h0P h3P (Nat.le_of_lt horder.1) hz_leg hz_segment

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg0_meets_rim1_only_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x z : V}
    (hx_first : x ∈ X.firstPath.support)
    (hx_not_path : x ∉ P.pathSet)
    (hz_leg :
      z ∈ (P.pathTailToStart (hothers_path 0 (by decide))).support)
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
    z = X.endpoints.endpoint 0 := by
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
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_rim
  rcases hz_rim with hz_suffix | hz_segment_rev
  · have hzF : z ∈ F.support :=
      SimpleGraph.Walk.support_dropUntil_subset F hxF hz_suffix
    have hzFirst : z ∈ X.firstPath.support := by
      simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hzF
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet h0P z hz_leg
    rcases
        GMIX24Split.canonicalOfNoCross_left_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hzFirst hzPath with hz0 | hz2
    · have h0_not_suffix : X.endpoints.endpoint 0 ∉ (F.dropUntil x hxF).support :=
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          (SimpleGraph.Walk.IsPath.mapLe D.leftSociety_graph_le
            X.firstPath_isPath)
          hxF hx_ne_0
      exact False.elim (h0_not_suffix (by simpa [hz0] using hz_suffix))
    · exact False.elim
        ((P.pathTailToStart_not_mem_of_supportIndex_lt h0P
          (lt_trans horder.1 horder.2)) (by simpa [hz2] using hz_leg))
  · exact False.elim
      (Set.disjoint_left.mp
        (P.pathTailToStart_support_disjoint_segmentBetween_reverse_of_lt
          h0P h3P h2P horder.1 (Nat.le_of_lt horder.2))
        hz_leg hz_segment_rev)

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg0_meets_rim2_only_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y z : V}
    (r : S.graph.Walk x y)
    (hy_second : y ∈ X.secondPath.support)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside)
    (hz_leg :
      z ∈ (P.pathTailToStart (hothers_path 0 (by decide))).support)
    (hz_rim :
      z ∈
        (r.append
          ((X.secondPath.mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil y
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second))).support) :
    z = X.endpoints.endpoint 0 := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  have h0P : X.endpoints.endpoint 0 ∈ P.pathSet :=
    hothers_path 0 (by decide)
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  have hzPath : z ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet h0P z hz_leg
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz_rim
  rcases hz_rim with hz_branch | hz_suffix
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
    · exact False.elim
        ((P.pathTailToStart_not_mem_of_supportIndex_lt h0P horder.1)
          (by simpa [hz3] using hz_leg))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
