import Schematic.Math.GraphTheory.Embedding.Wagner.CycleData

/-! Alternating cycle data from a strict cyclic index order. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner

/-- Cut a simple cycle into the four arcs displayed by the strict index order
`x1, y1, x2, y2` after rotating the cycle to start at `x1`.

This is the list-order-to-path part of Coq's `subcycle` argument. -/
noncomputable def alternatingCycleSplitOfRotatedIndexOrder
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 y1 x2 y2 : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hx1 : x1 ∈ C.support)
    (hy1 : y1 ∈ C.support)
    (hx2 : x2 ∈ C.support)
    (hy2 : y2 ∈ C.support)
    (hfirst :
      0 < (C.rotate x1 hx1).support.idxOf y1)
    (h12 :
      (C.rotate x1 hx1).support.idxOf y1 <
        (C.rotate x1 hx1).support.idxOf x2)
    (h2last :
      (C.rotate x1 hx1).support.idxOf x2 <
        (C.rotate x1 hx1).support.idxOf y2) :
    AlternatingCycleSplit C (x1 := x1) (y1 := y1)
      (x2 := x2) (y2 := y2) := by
  classical
  let C' : G.Walk x1 x1 := C.rotate x1 hx1
  have hC' : C'.IsCycle := by
    simpa [C'] using SimpleGraph.Walk.IsCycle.rotate hx1 hC
  have hy1' : y1 ∈ C'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mpr hy1
  have hx2' : x2 ∈ C'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mpr hx2
  have hy2' : y2 ∈ C'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mpr hy2
  have hfirst' : 0 < C'.support.idxOf y1 := by
    simpa [C'] using hfirst
  have h12' : C'.support.idxOf y1 < C'.support.idxOf x2 := by
    simpa [C'] using h12
  have h2last' : C'.support.idxOf x2 < C'.support.idxOf y2 := by
    simpa [C'] using h2last
  have hy1x1 : y1 ≠ x1 := by
    intro h
    subst y1
    rw [Walk.idxOf_start_support] at hfirst'
    omega
  have hx2x1 : x2 ≠ x1 := by
    intro h
    subst x2
    rw [Walk.idxOf_start_support] at h12'
    omega
  have hy2x1 : y2 ≠ x1 := by
    intro h
    subst y2
    rw [Walk.idxOf_start_support] at h2last'
    omega
  have hy1x2 : y1 ≠ x2 := by
    intro h
    subst x2
    omega
  have hx2y2 : x2 ≠ y2 := by
    intro h
    subst y2
    omega
  let T : G.Walk x1 x2 := C'.takeUntil x2 hx2'
  let D : G.Walk x2 x1 := C'.dropUntil x2 hx2'
  have hT : T.IsPath := by
    simpa [T] using hC'.isPath_takeUntil hx2'
  have hD : D.IsPath := by
    have hT_non_nil : ¬ T.Nil := by
      rw [SimpleGraph.Walk.nil_takeUntil]
      exact hx2x1.symm
    have hcycle_append : (T.append D).IsCycle := by
      simpa [T, D] using hC'
    exact hcycle_append.isPath_of_append_right hT_non_nil
  have hy1T : y1 ∈ T.support := by
    exact Walk.mem_support_takeUntil_of_idxOf_le hx2' hy1'
      (Nat.le_of_lt h12')
  have hy2D : y2 ∈ D.support := by
    exact Walk.mem_support_dropUntil_of_idxOf_le hx2' hy2'
      (Nat.le_of_lt h2last')
  have hsplit :
      Disjoint (Walk.InternalVertices T) (Walk.InternalVertices D) := by
    simpa [T, D] using
      Walk.IsCycle.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hC' hx2'
  let pX1X2 : G.Walk x1 x2 := D.reverse
  let pX1Y1 : G.Walk x1 y1 := T.takeUntil y1 hy1T
  let pX2Y1 : G.Walk x2 y1 := (T.dropUntil y1 hy1T).reverse
  have hpX1X2 : pX1X2.IsPath := by
    simpa [pX1X2] using hD.reverse
  have hpX1Y1 : pX1Y1.IsPath := by
    simpa [pX1Y1] using hT.takeUntil hy1T
  have hpX2Y1 : pX2Y1.IsPath := by
    simpa [pX2Y1] using (hT.dropUntil hy1T).reverse
  have hTtake_subset :
      Walk.InternalVertices (T.takeUntil y1 hy1T) ⊆
        Walk.InternalVertices T :=
    Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
      hT hy1T hy1x2
  have hTdrop_subset :
      Walk.InternalVertices (T.dropUntil y1 hy1T) ⊆
        Walk.InternalVertices T :=
    Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
      hT hy1T hy1x1
  refine {
    pX1X2 := pX1X2
    pX1Y1 := pX1Y1
    pX2Y1 := pX2Y1
    pX1X2_isPath := hpX1X2
    pX1Y1_isPath := hpX1Y1
    pX2Y1_isPath := hpX2Y1
    pX1X2_support := ?_
    pX1Y1_support := ?_
    pX2Y1_support := ?_
    y1_not_pX1X2 := ?_
    x2_not_pX1Y1 := ?_
    x1_not_pX2Y1 := ?_
    disjoint_X_X1Y1 := ?_
    disjoint_X_X2Y1 := ?_
    disjoint_X1Y1_X2Y1 := ?_
    y2_internal := ?_
  }
  · intro z hz
    have hzD : z ∈ D.support := by
      rw [SimpleGraph.Walk.support_reverse] at hz
      exact List.mem_reverse.mp (by simpa [pX1X2] using hz)
    have hzC' : z ∈ C'.support :=
      SimpleGraph.Walk.support_dropUntil_subset C' hx2' hzD
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mp hzC'
  · intro z hz
    have hzT : z ∈ T.support :=
      SimpleGraph.Walk.support_takeUntil_subset T hy1T
        (by simpa [pX1Y1] using hz)
    have hzC' : z ∈ C'.support :=
      SimpleGraph.Walk.support_takeUntil_subset C' hx2' hzT
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mp hzC'
  · intro z hz
    have hzDrop : z ∈ (T.dropUntil y1 hy1T).support := by
      have hzRev : z ∈ (T.dropUntil y1 hy1T).reverse.support := by
        simpa [pX2Y1] using hz
      rw [SimpleGraph.Walk.support_reverse] at hzRev
      exact List.mem_reverse.mp hzRev
    have hzT : z ∈ T.support :=
      SimpleGraph.Walk.support_dropUntil_subset T hy1T hzDrop
    have hzC' : z ∈ C'.support :=
      SimpleGraph.Walk.support_takeUntil_subset C' hx2' hzT
    exact (SimpleGraph.Walk.mem_support_rotate_iff C x1 hx1).mp hzC'
  · intro hy1p
    have hy1D : y1 ∈ D.support := by
      have hy1rev : y1 ∈ D.reverse.support := by
        simpa [pX1X2] using hy1p
      rw [SimpleGraph.Walk.support_reverse] at hy1rev
      exact List.mem_reverse.mp hy1rev
    have hy1TInternal : y1 ∈ Walk.InternalVertices T :=
      ⟨hy1T, hy1x1, hy1x2⟩
    have hy1DInternal : y1 ∈ Walk.InternalVertices D :=
      ⟨hy1D, hy1x2, hy1x1⟩
    exact Set.disjoint_left.mp hsplit hy1TInternal hy1DInternal
  · exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      hT hy1T hy1x2.symm
  · intro hx1p
    have hx1Drop : x1 ∈ (T.dropUntil y1 hy1T).support := by
      have hx1rev : x1 ∈ (T.dropUntil y1 hy1T).reverse.support := by
        simpa [pX2Y1] using hx1p
      rw [SimpleGraph.Walk.support_reverse] at hx1rev
      exact List.mem_reverse.mp hx1rev
    exact Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      hT hy1T hy1x1 hx1Drop
  · rw [Set.disjoint_left]
    intro z hzX hz1
    have hzD : z ∈ Walk.InternalVertices D :=
      (Walk.mem_internalVertices_reverse_iff D).mp
        (by simpa [pX1X2] using hzX)
    have hzT : z ∈ Walk.InternalVertices T :=
      hTtake_subset (by simpa [pX1Y1] using hz1)
    exact Set.disjoint_left.mp hsplit hzT hzD
  · rw [Set.disjoint_left]
    intro z hzX hz2
    have hzD : z ∈ Walk.InternalVertices D :=
      (Walk.mem_internalVertices_reverse_iff D).mp
        (by simpa [pX1X2] using hzX)
    have hzDrop : z ∈ Walk.InternalVertices (T.dropUntil y1 hy1T) :=
      (Walk.mem_internalVertices_reverse_iff (T.dropUntil y1 hy1T)).mp
        (by simpa [pX2Y1] using hz2)
    exact Set.disjoint_left.mp hsplit (hTdrop_subset hzDrop) hzD
  · have hinner :=
      Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hT hy1T
    simpa [pX1Y1, pX2Y1, Walk.internalVertices_reverse] using hinner
  · have hy2rev : y2 ∈ pX1X2.support := by
      have : y2 ∈ D.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr hy2D
      simpa [pX1X2] using this
    exact ⟨hy2rev, hy2x1, hx2y2.symm⟩


end Wagner

end FourColor

end Schematic.Math.GraphTheory
