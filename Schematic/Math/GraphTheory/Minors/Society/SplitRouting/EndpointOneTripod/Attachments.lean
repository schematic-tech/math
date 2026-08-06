import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.SingleOffPathOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_cross_endpoint1_first_left_ne_right
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x : V}
    (hx_not_path : x ∉ P.pathSet) :
    x ≠ X.endpoints.endpoint 3 := by
  intro hx3
  exact hx_not_path (by
    simpa [hx3] using hothers_path 3 (by decide))

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim0_attach0_internal
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
    X.endpoints.endpoint 0 ∈
      Walk.InternalVertices
        ((((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).reverse).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 0 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).1))) := by
  classical
  have h0P : X.endpoints.endpoint 0 ∈ P.pathSet :=
    hothers_path 0 (by decide)
  have hx_ne_0 : x ≠ X.endpoints.endpoint 0 := by
    intro hx0
    exact hx_not_path (by simpa [hx0] using h0P)
  refine ⟨?_, hx_ne_0.symm, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    exact
      (((X.firstPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).takeUntil x
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).reverse).end_mem_support
  · intro h03
    exact (by decide : (0 : Fin 4) ≠ 3)
      (X.endpoints.endpoint_injective h03)

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim1_attach1_internal
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
    X.endpoints.endpoint 2 ∈
      Walk.InternalVertices
        (((X.firstPath.mapLe
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil x
          (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).append
          (Walk.segmentBetween P.path
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 3 (by decide))
            (by simpa [GMIX24CutPath.pathSet] using hothers_path 2 (by decide))
            (Nat.le_of_lt
              (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
                P hno_cross X h1_off hothers_path).2)).reverse) := by
  classical
  have h2P : X.endpoints.endpoint 2 ∈ P.pathSet :=
    hothers_path 2 (by decide)
  have hx_ne_2 : x ≠ X.endpoints.endpoint 2 := by
    intro hx2
    exact hx_not_path (by simpa [hx2] using h2P)
  refine ⟨?_, hx_ne_2.symm, ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    exact
      ((X.firstPath.mapLe
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil x
        (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hx_first)).end_mem_support
  · intro h23
    exact (by decide : (2 : Fin 4) ≠ 3)
      (X.endpoints.endpoint_injective h23)

theorem canonicalOfNoCross_left_cross_endpoint1_first_rim2_attach2_internal
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V}
    (r : S.graph.Walk x y)
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    y ∈
      Walk.InternalVertices
        (r.append
          ((X.secondPath.mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).dropUntil y
            (by simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hy_second))) := by
  classical
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have hxy : x ≠ y :=
    cross_clean_branch_endpoints_ne (H :=
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety)
      (X := X) hx_first hy_second
  have hy_ne_3 : y ≠ X.endpoints.endpoint 3 := by
    intro hy3
    exact (hr_outside y r.end_mem_support).2 (by simpa [hy3] using h3P)
  refine ⟨?_, hxy.symm, hy_ne_3⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    exact r.end_mem_support

def canonicalOfNoCross_left_cross_endpoint1_first_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Fin 3 -> V :=
  fun i => if i = 0 then P.s
    else if i = 1 then P.t
    else X.endpoints.endpoint 1

theorem canonicalOfNoCross_left_cross_endpoint1_first_boundary_mem
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet) :
    forall i : Fin 3,
      canonicalOfNoCross_left_cross_endpoint1_first_boundary
        P hno_cross X i ∈ S.boundarySet := by
  intro i
  fin_cases i
  · simpa [canonicalOfNoCross_left_cross_endpoint1_first_boundary] using
      P.s_mem_boundary
  · simpa [canonicalOfNoCross_left_cross_endpoint1_first_boundary] using
      P.t_mem_boundary
  · simpa [canonicalOfNoCross_left_cross_endpoint1_first_boundary,
      GeneralSociety.boundarySet] using
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint_mem_original_of_off_path
        P hno_cross X h1_off

theorem canonicalOfNoCross_left_cross_endpoint1_first_boundary_injective
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet) :
    Function.Injective
      (canonicalOfNoCross_left_cross_endpoint1_first_boundary P hno_cross X) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [canonicalOfNoCross_left_cross_endpoint1_first_boundary] at hij ⊢
  · exact False.elim (P.s_ne_t hij)
  · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
      rw [← hij]
      exact P.s_mem_pathSet
    exact False.elim (h1_off hpath)
  · exact False.elim (P.s_ne_t hij.symm)
  · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
      rw [← hij]
      exact P.t_mem_pathSet
    exact False.elim (h1_off hpath)
  · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
      rw [hij]
      exact P.s_mem_pathSet
    exact False.elim (h1_off hpath)
  · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
      rw [hij]
      exact P.t_mem_pathSet
    exact False.elim (h1_off hpath)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
