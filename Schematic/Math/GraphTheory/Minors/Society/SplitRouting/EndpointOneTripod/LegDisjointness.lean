import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.SingleOffPathOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_endpoint1_first_leg2_isPath
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {y : V}
    (hy_second : y ∈ X.secondPath.support) :
    (((X.secondPath.mapLe
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil y
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse).IsPath := by
  classical
  exact
    ((SimpleGraph.Walk.IsPath.mapLe
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      X.secondPath_isPath).takeUntil
      (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg0_leg1_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Disjoint
      {z : V | z ∈ (P.pathTailToStart (hothers_path 0 (by decide))).support}
      {z : V | z ∈ (P.pathTailToEnd (hothers_path 2 (by decide))).support} := by
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  exact
    P.pathTailToStart_support_disjoint_pathTailToEnd
      (hothers_path 0 (by decide))
      (hothers_path 2 (by decide))
      (lt_trans horder.1 horder.2)

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg0_leg2_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {y : V}
    (hy_second : y ∈ X.secondPath.support) :
    Disjoint
      {z : V | z ∈ (P.pathTailToStart (hothers_path 0 (by decide))).support}
      {z : V | z ∈
        (((X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil y
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse).support} := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  rw [Set.disjoint_left]
  intro z hz0 hz2
  have hz2_take : z ∈ (G.takeUntil y hyG).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz2
    exact List.mem_reverse.mp hz2
  have hzG : z ∈ G.support :=
    SimpleGraph.Walk.support_takeUntil_subset G hyG hz2_take
  have hzSecond : z ∈ X.secondPath.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
  have hzPath : z ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet
      (hothers_path 0 (by decide)) z hz0
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
        P hno_cross X hzSecond hzPath with hz1 | hz3
  · exact h1_off (by simpa [hz1] using hzPath)
  · exact
      (P.pathTailToStart_not_mem_of_supportIndex_lt
        (hothers_path 0 (by decide)) horder.1)
        (by simpa [hz3] using hz0)

theorem canonicalOfNoCross_left_cross_endpoint1_first_leg1_leg2_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {y : V}
    (hy_second : y ∈ X.secondPath.support) :
    Disjoint
      {z : V | z ∈ (P.pathTailToEnd (hothers_path 2 (by decide))).support}
      {z : V | z ∈
        (((X.secondPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil y
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second)).reverse).support} := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  have horder :=
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
      P hno_cross X h1_off hothers_path
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have hz2_take : z ∈ (G.takeUntil y hyG).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz2
    exact List.mem_reverse.mp hz2
  have hzG : z ∈ G.support :=
    SimpleGraph.Walk.support_takeUntil_subset G hyG hz2_take
  have hzSecond : z ∈ X.secondPath.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hzG
  have hzPath : z ∈ P.pathSet :=
    P.pathTailToEnd_support_subset_pathSet
      (hothers_path 2 (by decide)) z hz1
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_secondPath_pathSet_eq_endpoint
        P hno_cross X hzSecond hzPath with hz1_endpoint | hz3
  · exact h1_off (by simpa [hz1_endpoint] using hzPath)
  · exact
      (P.pathTailToEnd_not_mem_of_supportIndex_lt
        (hothers_path 2 (by decide)) horder.2)
        (by simpa [hz3] using hz1)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
