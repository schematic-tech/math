import Schematic.Math.GraphTheory.Embedding.Wagner.CycleData

/-! Alternating cycle data from two internally disjoint paths. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner

/-- Split one of two internally disjoint `x1`--`x2` arcs at `y1`; the other
arc contains `y2`.  This is the path-level form used after the finite
consecutive-gap argument. -/
noncomputable def alternatingCycleSplitOfTwoArcs
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 y1 x2 y2 : V}
    (C : G.Walk r r)
    (p q : G.Walk x1 x2)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hp_support : forall z, z ∈ p.support -> z ∈ C.support)
    (hq_support : forall z, z ∈ q.support -> z ∈ C.support)
    (hy1 : y1 ∈ Walk.InternalVertices p)
    (hy2 : y2 ∈ Walk.InternalVertices q)
    (hd : Disjoint (Walk.InternalVertices p) (Walk.InternalVertices q)) :
    AlternatingCycleSplit C (x1 := x1) (y1 := y1)
      (x2 := x2) (y2 := y2) := by
  classical
  let pX1Y1 : G.Walk x1 y1 := p.takeUntil y1 hy1.1
  let pX2Y1 : G.Walk x2 y1 := (p.dropUntil y1 hy1.1).reverse
  have htake_subset :
      Walk.InternalVertices (p.takeUntil y1 hy1.1) ⊆
        Walk.InternalVertices p :=
    Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
      hp hy1.1 hy1.2.2
  have hdrop_subset :
      Walk.InternalVertices (p.dropUntil y1 hy1.1) ⊆
        Walk.InternalVertices p :=
    Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
      hp hy1.1 hy1.2.1
  refine {
    pX1X2 := q
    pX1Y1 := pX1Y1
    pX2Y1 := pX2Y1
    pX1X2_isPath := hq
    pX1Y1_isPath := by
      simpa [pX1Y1] using hp.takeUntil hy1.1
    pX2Y1_isPath := by
      simpa [pX2Y1] using (hp.dropUntil hy1.1).reverse
    pX1X2_support := hq_support
    pX1Y1_support := ?_
    pX2Y1_support := ?_
    y1_not_pX1X2 := ?_
    x2_not_pX1Y1 := ?_
    x1_not_pX2Y1 := ?_
    disjoint_X_X1Y1 := ?_
    disjoint_X_X2Y1 := ?_
    disjoint_X1Y1_X2Y1 := ?_
    y2_internal := hy2
  }
  · intro z hz
    exact hp_support z
      (SimpleGraph.Walk.support_takeUntil_subset p hy1.1
        (by simpa [pX1Y1] using hz))
  · intro z hz
    have hzDrop : z ∈ (p.dropUntil y1 hy1.1).support := by
      have hzRev : z ∈ (p.dropUntil y1 hy1.1).reverse.support := by
        simpa [pX2Y1] using hz
      rw [SimpleGraph.Walk.support_reverse] at hzRev
      exact List.mem_reverse.mp hzRev
    exact hp_support z
      (SimpleGraph.Walk.support_dropUntil_subset p hy1.1 hzDrop)
  · intro hy1q
    have hy1qInternal : y1 ∈ Walk.InternalVertices q :=
      ⟨hy1q, hy1.2.1, hy1.2.2⟩
    exact Set.disjoint_left.mp hd hy1 hy1qInternal
  · exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      hp hy1.1 hy1.2.2.symm
  · intro hx1
    have hx1Drop : x1 ∈ (p.dropUntil y1 hy1.1).support := by
      have hx1Rev : x1 ∈ (p.dropUntil y1 hy1.1).reverse.support := by
        simpa [pX2Y1] using hx1
      rw [SimpleGraph.Walk.support_reverse] at hx1Rev
      exact List.mem_reverse.mp hx1Rev
    exact Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      hp hy1.1 hy1.2.1 hx1Drop
  · rw [Set.disjoint_left]
    intro z hzq hztake
    exact Set.disjoint_left.mp hd (htake_subset (by
      simpa [pX1Y1] using hztake)) hzq
  · rw [Set.disjoint_left]
    intro z hzq hzdropRev
    have hzdrop : z ∈ Walk.InternalVertices (p.dropUntil y1 hy1.1) :=
      (Walk.mem_internalVertices_reverse_iff (p.dropUntil y1 hy1.1)).mp
        (by simpa [pX2Y1] using hzdropRev)
    exact Set.disjoint_left.mp hd (hdrop_subset hzdrop) hzq
  · have hinner :=
      Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hp hy1.1
    simpa [pX1Y1, pX2Y1, Walk.internalVertices_reverse] using hinner

end Wagner

end FourColor

end Schematic.Math.GraphTheory
