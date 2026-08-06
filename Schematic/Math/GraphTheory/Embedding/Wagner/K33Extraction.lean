import Schematic.Math.GraphTheory.Embedding.Wagner.AlternatingPaths
import Schematic.Math.GraphTheory.Embedding.Wagner.OrderedCycleSplit

/-! Extraction of a strict `K3,3` subdivision from alternating cycle data. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner
theorem containsStrictSubdivision_K33_of_alternating_cycle_split
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x y x1 y1 x2 y2 : V}
    (C : G.Walk r r)
    (S : AlternatingCycleSplit C (x1 := x1) (y1 := y1)
      (x2 := x2) (y2 := y2))
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    ContainsStrictSubdivision K33Graph G := by
  classical
  let p11 : G.Walk x1 y1 := S.pX1Y1
  let p12 : G.Walk y1 x2 := S.pX2Y1.reverse
  let p22 : G.Walk x2 y2 :=
    (S.pX1X2.dropUntil y2 S.y2_internal.1).reverse
  let p21 : G.Walk y2 x1 :=
    (S.pX1X2.takeUntil y2 S.y2_internal.1).reverse
  have hp11 : p11.IsPath := by
    simpa [p11] using S.pX1Y1_isPath
  have hp12 : p12.IsPath := by
    simpa [p12] using S.pX2Y1_isPath.reverse
  have hp22 : p22.IsPath := by
    simpa [p22] using
      (S.pX1X2_isPath.dropUntil S.y2_internal.1).reverse
  have hp21 : p21.IsPath := by
    simpa [p21] using
      (S.pX1X2_isPath.takeUntil S.y2_internal.1).reverse
  have hxx1_ne : x ≠ x1 := by
    intro h
    exact hxC (by simpa [h] using
      S.pX1X2_support x1 S.pX1X2.start_mem_support)
  have hxx2_ne : x ≠ x2 := by
    intro h
    exact hxC (by simpa [h] using
      S.pX1X2_support x2 S.pX1X2.end_mem_support)
  have hxy1_ne : x ≠ y1 := by
    intro h
    exact hxC (by simpa [h] using
      S.pX1Y1_support y1 S.pX1Y1.end_mem_support)
  have hxy2_ne : x ≠ y2 := by
    intro h
    exact hxC (by simpa [h] using
      S.pX1X2_support y2 S.y2_internal.1)
  have hyx1_ne : y ≠ x1 := by
    intro h
    exact hyC (by simpa [h] using
      S.pX1X2_support x1 S.pX1X2.start_mem_support)
  have hyx2_ne : y ≠ x2 := by
    intro h
    exact hyC (by simpa [h] using
      S.pX1X2_support x2 S.pX1X2.end_mem_support)
  have hyy1_ne : y ≠ y1 := by
    intro h
    exact hyC (by simpa [h] using
      S.pX1Y1_support y1 S.pX1Y1.end_mem_support)
  have hyy2_ne : y ≠ y2 := by
    intro h
    exact hyC (by simpa [h] using
      S.pX1X2_support y2 S.y2_internal.1)
  have hx1y1_ne : x1 ≠ y1 := by
    intro h
    exact S.y1_not_pX1X2 (by simpa [h] using
      S.pX1X2.start_mem_support)
  have hx1x2_ne : x1 ≠ x2 :=
    Walk.IsPath.start_ne_end_of_mem_support_ne_start
      S.pX1X2_isPath S.y2_internal.1 S.y2_internal.2.1
  have hx1y2_ne : x1 ≠ y2 := S.y2_internal.2.1.symm
  have hy1x2_ne : y1 ≠ x2 := by
    intro h
    exact S.y1_not_pX1X2 (by simp [h])
  have hy1y2_ne : y1 ≠ y2 := by
    intro h
    exact S.y1_not_pX1X2 (by simpa [h] using S.y2_internal.1)
  have hx2y2_ne : x2 ≠ y2 := S.y2_internal.2.2.symm
  have hbranch :
      Function.Injective (alternatingBranch x y x1 y1 x2 y2) := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp_all [alternatingBranch]
  have htake_subset :
      Walk.InternalVertices
          (S.pX1X2.takeUntil y2 S.y2_internal.1) ⊆
        Walk.InternalVertices S.pX1X2 :=
    Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
      S.pX1X2_isPath S.y2_internal.1 S.y2_internal.2.2
  have hdrop_subset :
      Walk.InternalVertices
          (S.pX1X2.dropUntil y2 S.y2_internal.1) ⊆
        Walk.InternalVertices S.pX1X2 :=
    Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
      S.pX1X2_isPath S.y2_internal.1 S.y2_internal.2.1
  have hno11 : forall {z}, z ∈ Walk.InternalVertices p11 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w := by
    intro z hz w
    have hz' : z ∈ Walk.InternalVertices S.pX1Y1 := by
      simpa [p11] using hz
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using S.pX1Y1_support z hz'.1)
    · exact hz'.2.2
    · intro hzy2
      exact Set.disjoint_left.mp S.disjoint_X_X1Y1
        (by simpa [hzy2] using S.y2_internal) hz'
    · intro hzy
      exact hyC (by simpa [hzy] using S.pX1Y1_support z hz'.1)
    · exact hz'.2.1
    · intro hzx2
      exact S.x2_not_pX1Y1 (by simpa [hzx2] using hz'.1)
  have hno12 : forall {z}, z ∈ Walk.InternalVertices p12 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w := by
    intro z hz w
    have hz' : z ∈ Walk.InternalVertices S.pX2Y1 :=
      (Walk.mem_internalVertices_reverse_iff S.pX2Y1).mp
        (by simpa [p12] using hz)
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using S.pX2Y1_support z hz'.1)
    · exact hz'.2.2
    · intro hzy2
      exact Set.disjoint_left.mp S.disjoint_X_X2Y1
        (by simpa [hzy2] using S.y2_internal) hz'
    · intro hzy
      exact hyC (by simpa [hzy] using S.pX2Y1_support z hz'.1)
    · intro hzx1
      exact S.x1_not_pX2Y1 (by simpa [hzx1] using hz'.1)
    · exact hz'.2.1
  have hno22 : forall {z}, z ∈ Walk.InternalVertices p22 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w := by
    intro z hz w
    have hzDrop : z ∈ Walk.InternalVertices
        (S.pX1X2.dropUntil y2 S.y2_internal.1) :=
      (Walk.mem_internalVertices_reverse_iff
        (S.pX1X2.dropUntil y2 S.y2_internal.1)).mp
        (by simpa [p22] using hz)
    have hzX := hdrop_subset hzDrop
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using S.pX1X2_support z hzX.1)
    · intro hzy1
      exact S.y1_not_pX1X2 (by simpa [hzy1] using hzX.1)
    · exact hzDrop.2.1
    · intro hzy
      exact hyC (by simpa [hzy] using S.pX1X2_support z hzX.1)
    · exact hzX.2.1
    · exact hzDrop.2.2
  have hno21 : forall {z}, z ∈ Walk.InternalVertices p21 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w := by
    intro z hz w
    have hzTake : z ∈ Walk.InternalVertices
        (S.pX1X2.takeUntil y2 S.y2_internal.1) :=
      (Walk.mem_internalVertices_reverse_iff
        (S.pX1X2.takeUntil y2 S.y2_internal.1)).mp
        (by simpa [p21] using hz)
    have hzX := htake_subset hzTake
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using S.pX1X2_support z hzX.1)
    · intro hzy1
      exact S.y1_not_pX1X2 (by simpa [hzy1] using hzX.1)
    · exact hzTake.2.2
    · intro hzy
      exact hyC (by simpa [hzy] using S.pX1X2_support z hzX.1)
    · exact hzTake.2.1
    · exact hzX.2.2
  have hd11_12 :
      Disjoint (Walk.InternalVertices p11) (Walk.InternalVertices p12) := by
    simpa [p11, p12, Walk.internalVertices_reverse] using
      S.disjoint_X1Y1_X2Y1
  have hd11_22 :
      Disjoint (Walk.InternalVertices p11) (Walk.InternalVertices p22) := by
    rw [Set.disjoint_left]
    intro z hz11 hz22
    have hz11' : z ∈ Walk.InternalVertices S.pX1Y1 := by
      simpa [p11] using hz11
    have hzDrop : z ∈ Walk.InternalVertices
        (S.pX1X2.dropUntil y2 S.y2_internal.1) :=
      (Walk.mem_internalVertices_reverse_iff
        (S.pX1X2.dropUntil y2 S.y2_internal.1)).mp
        (by simpa [p22] using hz22)
    exact Set.disjoint_left.mp S.disjoint_X_X1Y1
      (hdrop_subset hzDrop) hz11'
  have hd11_21 :
      Disjoint (Walk.InternalVertices p11) (Walk.InternalVertices p21) := by
    rw [Set.disjoint_left]
    intro z hz11 hz21
    have hz11' : z ∈ Walk.InternalVertices S.pX1Y1 := by
      simpa [p11] using hz11
    have hzTake : z ∈ Walk.InternalVertices
        (S.pX1X2.takeUntil y2 S.y2_internal.1) :=
      (Walk.mem_internalVertices_reverse_iff
        (S.pX1X2.takeUntil y2 S.y2_internal.1)).mp
        (by simpa [p21] using hz21)
    exact Set.disjoint_left.mp S.disjoint_X_X1Y1
      (htake_subset hzTake) hz11'
  have hd12_22 :
      Disjoint (Walk.InternalVertices p12) (Walk.InternalVertices p22) := by
    rw [Set.disjoint_left]
    intro z hz12 hz22
    have hz12' : z ∈ Walk.InternalVertices S.pX2Y1 :=
      (Walk.mem_internalVertices_reverse_iff S.pX2Y1).mp
        (by simpa [p12] using hz12)
    have hzDrop : z ∈ Walk.InternalVertices
        (S.pX1X2.dropUntil y2 S.y2_internal.1) :=
      (Walk.mem_internalVertices_reverse_iff
        (S.pX1X2.dropUntil y2 S.y2_internal.1)).mp
        (by simpa [p22] using hz22)
    exact Set.disjoint_left.mp S.disjoint_X_X2Y1
      (hdrop_subset hzDrop) hz12'
  have hd12_21 :
      Disjoint (Walk.InternalVertices p12) (Walk.InternalVertices p21) := by
    rw [Set.disjoint_left]
    intro z hz12 hz21
    have hz12' : z ∈ Walk.InternalVertices S.pX2Y1 :=
      (Walk.mem_internalVertices_reverse_iff S.pX2Y1).mp
        (by simpa [p12] using hz12)
    have hzTake : z ∈ Walk.InternalVertices
        (S.pX1X2.takeUntil y2 S.y2_internal.1) :=
      (Walk.mem_internalVertices_reverse_iff
        (S.pX1X2.takeUntil y2 S.y2_internal.1)).mp
        (by simpa [p21] using hz21)
    exact Set.disjoint_left.mp S.disjoint_X_X2Y1
      (htake_subset hzTake) hz12'
  have hd22_21 :
      Disjoint (Walk.InternalVertices p22) (Walk.InternalVertices p21) := by
    have hsplit :=
      Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) S.pX1X2_isPath S.y2_internal.1
    simpa [p22, p21, Walk.internalVertices_reverse] using hsplit.symm
  exact containsStrictSubdivision_K33_of_alternating_paths
    p11 p12 p22 p21 hp11 hp12 hp22 hp21
    hxy hxx1 hxx2 hyy1 hyy2 hbranch
    hno11 hno12 hno22 hno21
    hd11_12 hd11_22 hd11_21 hd12_22 hd12_21 hd22_21

theorem containsStrictSubdivision_K33_of_cycle_alternating_index_order
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x y x1 y1 x2 y2 : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hx1 : x1 ∈ C.support)
    (hy1 : y1 ∈ C.support)
    (hx2 : x2 ∈ C.support)
    (hy2 : y2 ∈ C.support)
    (hfirst : 0 < (C.rotate x1 hx1).support.idxOf y1)
    (h12 :
      (C.rotate x1 hx1).support.idxOf y1 <
        (C.rotate x1 hx1).support.idxOf x2)
    (h2last :
      (C.rotate x1 hx1).support.idxOf x2 <
        (C.rotate x1 hx1).support.idxOf y2)
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    ContainsStrictSubdivision K33Graph G :=
  containsStrictSubdivision_K33_of_alternating_cycle_split C
    (alternatingCycleSplitOfRotatedIndexOrder C hC hx1 hy1 hx2 hy2
      hfirst h12 h2last)
    hxy hxx1 hxx2 hyy1 hyy2 hxC hyC

end Wagner

end FourColor

end Schematic.Math.GraphTheory
