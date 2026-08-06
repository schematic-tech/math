import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.PathIntervals.Definitions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

theorem pathTailToStart_supportIndex_le
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x z : V} (hx : x ∈ P.pathSet)
    (hz : z ∈ (P.pathTailToStart hx).support) :
    Walk.supportIndex P.path z <= Walk.supportIndex P.path x := by
  have hx_support : x ∈ P.path.support := by
    simpa [pathSet] using hx
  have hz_take :
      z ∈ (P.path.takeUntil x hx_support).support := by
    have hzrev :
        z ∈ (P.path.takeUntil x hx_support).support.reverse := by
      simpa [pathTailToStart, SimpleGraph.Walk.support_reverse] using hz
    exact List.mem_reverse.mp hzrev
  simpa [Walk.supportIndex] using
    Walk.idxOf_le_of_mem_takeUntil hx_support hz_take

theorem pathTailToEnd_supportIndex_le
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x z : V} (hx : x ∈ P.pathSet)
    (hz : z ∈ (P.pathTailToEnd hx).support) :
    Walk.supportIndex P.path x <= Walk.supportIndex P.path z := by
  have hx_support : x ∈ P.path.support := by
    simpa [pathSet] using hx
  have hz_drop :
      z ∈ (P.path.dropUntil x hx_support).support := by
    simpa [pathTailToEnd] using hz
  simpa [Walk.supportIndex] using
    Walk.idxOf_le_of_mem_dropUntil P.path_isPath hx_support hz_drop

theorem pathTailToStart_support_disjoint_pathTailToEnd
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy :
      Walk.supportIndex P.path x < Walk.supportIndex P.path y) :
    Disjoint
      {z : V | z ∈ (P.pathTailToStart hx).support}
      {z : V | z ∈ (P.pathTailToEnd hy).support} := by
  exact
    Walk.support_disjoint_of_supportIndex_bounds
      (p := P.path) (first := x) (last := y) hxy
      (fun z hz => P.pathTailToStart_supportIndex_le hx hz)
      (fun z hz => P.pathTailToEnd_supportIndex_le hy hz)

/-- The two cut-path tails from the same vertex meet only at that vertex.

This is the equality case complementary to
`pathTailToStart_support_disjoint_pathTailToEnd`: the start tail has support
index at most the chosen vertex, while the end tail has support index at
least it.  Since the cut path is induced as a path, equality of support
indices forces equality of vertices. -/
theorem pathTailToStart_support_inter_pathTailToEnd_eq
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x z : V} (hx : x ∈ P.pathSet)
    (hzStart : z ∈ (P.pathTailToStart hx).support)
    (hzEnd : z ∈ (P.pathTailToEnd hx).support) :
    z = x := by
  have hzPath : z ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet hx z hzStart
  have hzSupport : z ∈ P.path.support := by
    simpa [GMIX24CutPath.pathSet] using hzPath
  have hxSupport : x ∈ P.path.support := by
    simpa [GMIX24CutPath.pathSet] using hx
  have hzx : Walk.supportIndex P.path z <= Walk.supportIndex P.path x :=
    P.pathTailToStart_supportIndex_le hx hzStart
  have hxz : Walk.supportIndex P.path x <= Walk.supportIndex P.path z :=
    P.pathTailToEnd_supportIndex_le hx hzEnd
  exact
    Walk.supportIndex_injective_of_mem hzSupport (le_antisymm hzx hxz)

theorem pathTailToStart_not_mem_of_supportIndex_lt
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet)
    (hxy :
      Walk.supportIndex P.path x < Walk.supportIndex P.path y) :
    y ∉ (P.pathTailToStart hx).support := by
  intro hy
  have hle : Walk.supportIndex P.path y <= Walk.supportIndex P.path x :=
    P.pathTailToStart_supportIndex_le hx hy
  omega

theorem pathTailToEnd_not_mem_of_supportIndex_lt
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hy : y ∈ P.pathSet)
    (hxy :
      Walk.supportIndex P.path x < Walk.supportIndex P.path y) :
    x ∉ (P.pathTailToEnd hy).support := by
  intro hx_tail
  have hle : Walk.supportIndex P.path y <= Walk.supportIndex P.path x :=
    P.pathTailToEnd_supportIndex_le hy hx_tail
  omega

theorem pathTailToStart_support_inter_segmentBetween_subset_left
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hz_tail : z ∈ (P.pathTailToStart hx).support)
    (hz_segment :
      z ∈ (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).support) :
    z = x := by
  exact
    Walk.takeUntil_reverse_support_inter_segmentBetween_subset_left
      P.path_isPath
      (by simpa [pathSet] using hx)
      (by simpa [pathSet] using hy)
      hxy
      (by simpa [pathTailToStart] using hz_tail)
      hz_segment

theorem segmentBetween_support_inter_pathTailToEnd_subset_right
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hz_segment :
      z ∈ (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).support)
    (hz_tail : z ∈ (P.pathTailToEnd hy).support) :
    z = y := by
  exact
    Walk.segmentBetween_support_inter_dropUntil_subset_right
      P.path_isPath
      (by simpa [pathSet] using hx)
      (by simpa [pathSet] using hy)
      hxy hz_segment
      (by simpa [pathTailToEnd] using hz_tail)

theorem segmentBetween_reverse_support_inter_pathTailToEnd_subset_right
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hz_segment :
      z ∈ (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).reverse.support)
    (hz_tail : z ∈ (P.pathTailToEnd hy).support) :
    z = y := by
  have hz_segment' :
      z ∈ (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_segment
    exact List.mem_reverse.mp hz_segment
  exact
    P.segmentBetween_support_inter_pathTailToEnd_subset_right
      hx hy hxy hz_segment' hz_tail

theorem pathTailToStart_support_disjoint_segmentBetween_of_lt
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a b c : V} (ha : a ∈ P.pathSet) (hb : b ∈ P.pathSet)
    (hc : c ∈ P.pathSet)
    (hab : Walk.supportIndex P.path a < Walk.supportIndex P.path b)
    (hbc : Walk.supportIndex P.path b <= Walk.supportIndex P.path c) :
    Disjoint
      {z : V | z ∈ (P.pathTailToStart ha).support}
      {z : V | z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using hb)
          (by simpa [pathSet] using hc) hbc).support} := by
  rw [Set.disjoint_left]
  intro z hz_tail hz_segment
  have hz_le_a : Walk.supportIndex P.path z <= Walk.supportIndex P.path a :=
    P.pathTailToStart_supportIndex_le ha hz_tail
  have hb_le_z : Walk.supportIndex P.path b <= Walk.supportIndex P.path z :=
    Walk.segmentBetween_supportIndex_left_le P.path_isPath
      (by simpa [pathSet] using hb)
      (by simpa [pathSet] using hc)
      hbc hz_segment
  omega

theorem pathTailToStart_support_disjoint_segmentBetween_reverse_of_lt
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a b c : V} (ha : a ∈ P.pathSet) (hb : b ∈ P.pathSet)
    (hc : c ∈ P.pathSet)
    (hab : Walk.supportIndex P.path a < Walk.supportIndex P.path b)
    (hbc : Walk.supportIndex P.path b <= Walk.supportIndex P.path c) :
    Disjoint
      {z : V | z ∈ (P.pathTailToStart ha).support}
      {z : V | z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using hb)
          (by simpa [pathSet] using hc) hbc).reverse.support} := by
  rw [Set.disjoint_left]
  intro z hz_tail hz_segment
  have hz_segment' :
      z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using hb)
          (by simpa [pathSet] using hc) hbc).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_segment
    exact List.mem_reverse.mp hz_segment
  exact
    Set.disjoint_left.mp
      (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
        ha hb hc hab hbc) hz_tail hz_segment'

theorem segmentBetween_support_disjoint_pathTailToEnd_of_lt
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a b c : V} (ha : a ∈ P.pathSet) (hb : b ∈ P.pathSet)
    (hc : c ∈ P.pathSet)
    (hab : Walk.supportIndex P.path a <= Walk.supportIndex P.path b)
    (hbc : Walk.supportIndex P.path b < Walk.supportIndex P.path c) :
    Disjoint
      {z : V | z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using ha)
          (by simpa [pathSet] using hb) hab).support}
      {z : V | z ∈ (P.pathTailToEnd hc).support} := by
  rw [Set.disjoint_left]
  intro z hz_segment hz_tail
  have hz_le_b : Walk.supportIndex P.path z <= Walk.supportIndex P.path b :=
    Walk.segmentBetween_supportIndex_right_le
      (by simpa [pathSet] using ha)
      (by simpa [pathSet] using hb)
      hab hz_segment
  have hc_le_z : Walk.supportIndex P.path c <= Walk.supportIndex P.path z :=
    P.pathTailToEnd_supportIndex_le hc hz_tail
  omega

theorem segmentBetween_reverse_support_disjoint_pathTailToEnd_of_lt
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a b c : V} (ha : a ∈ P.pathSet) (hb : b ∈ P.pathSet)
    (hc : c ∈ P.pathSet)
    (hab : Walk.supportIndex P.path a <= Walk.supportIndex P.path b)
    (hbc : Walk.supportIndex P.path b < Walk.supportIndex P.path c) :
    Disjoint
      {z : V | z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using ha)
          (by simpa [pathSet] using hb) hab).reverse.support}
      {z : V | z ∈ (P.pathTailToEnd hc).support} := by
  rw [Set.disjoint_left]
  intro z hz_segment hz_tail
  have hz_segment' :
      z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using ha)
          (by simpa [pathSet] using hb) hab).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_segment
    exact List.mem_reverse.mp hz_segment
  exact
    Set.disjoint_left.mp
      (P.segmentBetween_support_disjoint_pathTailToEnd_of_lt
        ha hb hc hab hbc) hz_segment' hz_tail

theorem not_mem_segmentBetween_of_supportIndex_lt_left
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hzx : Walk.supportIndex P.path z < Walk.supportIndex P.path x) :
    z ∉
      (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).support := by
  intro hz
  have hx_le_z : Walk.supportIndex P.path x <= Walk.supportIndex P.path z :=
    Walk.segmentBetween_supportIndex_left_le P.path_isPath
      (by simpa [pathSet] using hx)
      (by simpa [pathSet] using hy)
      hxy hz
  omega

theorem not_mem_segmentBetween_reverse_of_supportIndex_lt_left
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hzx : Walk.supportIndex P.path z < Walk.supportIndex P.path x) :
    z ∉
      (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).reverse.support := by
  intro hz
  have hz' :
      z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using hx)
          (by simpa [pathSet] using hy) hxy).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz
    exact List.mem_reverse.mp hz
  exact P.not_mem_segmentBetween_of_supportIndex_lt_left hx hy hxy hzx hz'

theorem not_mem_segmentBetween_of_right_lt_supportIndex
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hyz : Walk.supportIndex P.path y < Walk.supportIndex P.path z) :
    z ∉
      (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).support := by
  intro hz
  have hz_le_y : Walk.supportIndex P.path z <= Walk.supportIndex P.path y :=
    Walk.segmentBetween_supportIndex_right_le
      (by simpa [pathSet] using hx)
      (by simpa [pathSet] using hy)
      hxy hz
  omega

theorem not_mem_segmentBetween_reverse_of_right_lt_supportIndex
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hyz : Walk.supportIndex P.path y < Walk.supportIndex P.path z) :
    z ∉
      (Walk.segmentBetween P.path
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy) hxy).reverse.support := by
  intro hz
  have hz' :
      z ∈
        (Walk.segmentBetween P.path
          (by simpa [pathSet] using hx)
          (by simpa [pathSet] using hy) hxy).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz
    exact List.mem_reverse.mp hz
  exact P.not_mem_segmentBetween_of_right_lt_supportIndex hx hy hxy hyz hz'

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
